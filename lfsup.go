// lfsup.go — Gerenciador LFS (MVP completo em único arquivo)
// Requisitos extras no sistema: curl, tar, xz, zstd, unzip, git, file, strip, ldd, fakeroot (opcional por receita)
// go: go1.20+ ; deps: gopkg.in/yaml.v3, go.etcd.io/bbolt
package main

import (
	"bufio"
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	bolt "go.etcd.io/bbolt"
	"gopkg.in/yaml.v3"
	"io"
	"io/fs"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"sort"
	"strings"
	"time"
)

/* ========= UI ========= */

var enableColor = true

func color(code, s string) string {
	if !enableColor {
		return s
	}
	return "\x1b[" + code + "m" + s + "\x1b[0m"
}
func Red(s string) string   { return color("31", s) }
func Green(s string) string { return color("32", s) }
func Yellow(s string) string { return color("33", s) }
func Bold(s string) string  { return color("1", s) }
func Dim(s string) string   { return color("2", s) }
func Mark(installed bool) string {
	if installed { return "[✓]" }
	return "[ ]"
}

type spinner struct{ label string; stop chan struct{} }
func newSpinner(label string) *spinner {
	s := &spinner{label: label, stop: make(chan struct{})}
	go func() {
		frames := []rune{'⠋','⠙','⠹','⠸','⠼','⠴','⠦','⠧','⠇','⠏'}
		i := 0
		for {
			select { case <-s.stop: return
			default:
				fmt.Printf("\r%s %c %s...", Dim("lfsup"), frames[i], label)
				i=(i+1)%len(frames); time.Sleep(80*time.Millisecond)
			}
		}
	}()
	return s
}
func (s *spinner) Succeed(){ close(s.stop); fmt.Printf("\r%s %s %s\n", Dim("lfsup"), Green("✓"), s.label) }
func (s *spinner) Fail(){ close(s.stop); fmt.Printf("\r%s %s %s\n", Dim("lfsup"), Red("✗"), s.label) }

/* ========= Modelos de Receita ========= */

type Source struct {
	URL      string `yaml:"url,omitempty"`
	Git      string `yaml:"git,omitempty"`
	Tag      string `yaml:"tag,omitempty"`
	Commit   string `yaml:"commit,omitempty"`
	Sha256   string `yaml:"sha256,omitempty"`
	Type     string `yaml:"type,omitempty"` // file/archive/patch
	Filename string `yaml:"filename,omitempty"`
}

type Recipe struct {
	Package    string            `yaml:"package"`
	Version    string            `yaml:"version"`
	Release    int               `yaml:"release"`
	Summary    string            `yaml:"summary"`
	Homepage   string            `yaml:"homepage"`
	License    string            `yaml:"license"`
	Source     []Source          `yaml:"source"`
	Requires   []string          `yaml:"requires"`
	Provides   []string          `yaml:"provides"`
	Options    map[string]any    `yaml:"options"`
	Vars       map[string]string `yaml:"vars"`
	Stages     map[string]string `yaml:"stages"`
	PostRemove string            `yaml:"postremove"`
	_path      string            `yaml:"-"`
}

func loadRecipeFile(path string) (*Recipe, error) {
	b, err := os.ReadFile(path); if err != nil { return nil, err }
	var r Recipe
	if err := yaml.Unmarshal(b, &r); err != nil { return nil, err }
	if r.Package=="" {
		base := filepath.Base(path)
		r.Package = strings.TrimSuffix(base, filepath.Ext(base))
	}
	if r.Release==0 { r.Release=1 }
	if r.Options==nil { r.Options = map[string]any{} }
	if r.Stages==nil { r.Stages = map[string]string{} }
	if r.Vars==nil { r.Vars = map[string]string{} }
	r._path = path
	return &r, nil
}

func loadAllRecipes(repo string) (map[string]*Recipe, error) {
	out := map[string]*Recipe{}
	err := filepath.WalkDir(repo, func(p string, d fs.DirEntry, err error) error {
		if err != nil || d.IsDir() { return nil }
		if strings.HasSuffix(d.Name(), ".yaml") || strings.HasSuffix(d.Name(), ".yml") {
			r, e := loadRecipeFile(p); if e==nil { out[r.Package]=r }
		}
		return nil
	})
	return out, err
}

/* ========= Grafo de dependências ========= */

type Graph map[string][]string

func buildGraph(recipes map[string]*Recipe) Graph {
	g := Graph{}
	for name, r := range recipes {
		g[name] = append([]string{}, r.Requires...)
		for _, dep := range r.Requires {
			if _, ok := g[dep]; !ok { g[dep]=[]string{} }
		}
	}
	return g
}

func topo(g Graph) ([]string, error) {
	indeg := map[string]int{}; for u := range g { indeg[u]=0 }
	for _, vs := range g { for _, v := range vs { indeg[v]++ } }
	q := []string{}; for n,d := range indeg { if d==0 { q=append(q,n) } }
	order := []string{}
	for len(q)>0 {
		n := q[0]; q=q[1:]
		order = append(order, n)
		for _, v := range g[n] {
			indeg[v]--; if indeg[v]==0 { q=append(q,v) }
		}
	}
	if len(order)!=len(indeg) { return nil, fmt.Errorf("ciclo nas dependências") }
	return order, nil
}

func resolveFor(target string, g Graph) ([]string, error) {
	if _, ok := g[target]; !ok { return nil, fmt.Errorf("pacote desconhecido: %s", target) }
	seen := map[string]bool{}; order := []string{}
	var dfs func(string)
	dfs = func(n string){
		if seen[n] { return }
		seen[n]=true
		for _,d := range g[n] { dfs(d) }
		if n!=target { order = append(order, n) }
	}
	dfs(target)
	return order, nil
}

/* ========= Registro (BoltDB) ========= */

type DB struct{ b *bolt.DB }

type Manifest struct {
	Name    string
	Version string
	Release int
	Time    time.Time
	Files   []FileRec
}
type FileRec struct { Path string }

func openDB(path string) (*DB, error) {
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil { return nil, err }
	b, err := bolt.Open(path, 0o644, nil); if err != nil { return nil, err }
	db := &DB{b:b}
	b.Update(func(tx *bolt.Tx) error {
		_,_ = tx.CreateBucketIfNotExists([]byte("packages"))
		_,_ = tx.CreateBucketIfNotExists([]byte("manifests"))
		return nil
	})
	return db, nil
}
func (db *DB) Close() error { return db.b.Close() }

func (db *DB) IsInstalled(name string) bool {
	ok := false
	_ = db.b.View(func(tx *bolt.Tx) error {
		if v := tx.Bucket([]byte("packages")).Get([]byte(name)); v != nil { ok = true }
		return nil
	})
	return ok
}
func (db *DB) Register(name, version string, release int, destdir string) error {
	man := Manifest{Name:name, Version:version, Release:release, Time:time.Now()}
	b, _ := os.ReadFile(filepath.Join(destdir, "manifest.txt"))
	for _, line := range splitLines(string(b)) {
		line = strings.TrimSpace(line); if line=="" { continue }
		man.Files = append(man.Files, FileRec{Path: line})
	}
	data, _ := json.Marshal(man)
	return db.b.Update(func(tx *bolt.Tx) error {
		if err := tx.Bucket([]byte("packages")).Put([]byte(name), []byte(version)); err != nil { return err }
		return tx.Bucket([]byte("manifests")).Put([]byte(name), data)
	})
}
func (db *DB) Unregister(name string) error {
	return db.b.Update(func(tx *bolt.Tx) error {
		_ = tx.Bucket([]byte("packages")).Delete([]byte(name))
		_ = tx.Bucket([]byte("manifests")).Delete([]byte(name))
		return nil
	})
}
func (db *DB) Manifest(name string) (*Manifest, error) {
	var man Manifest
	err := db.b.View(func(tx *bolt.Tx) error {
		if v := tx.Bucket([]byte("manifests")).Get([]byte(name)); v!=nil { return json.Unmarshal(v, &man) }
		return os.ErrNotExist
	})
	if err!=nil { return nil, err }
	return &man, nil
}
func (db *DB) Installed() ([]string, error) {
	var names []string
	err := db.b.View(func(tx *bolt.Tx) error {
		b := tx.Bucket([]byte("packages"))
		return b.ForEach(func(k, v []byte) error {
			names = append(names, string(k)); return nil
		})
	})
	sort.Strings(names)
	return names, err
}

/* ========= Exec/fases ========= */

func defaultEnv(r *Recipe, destdir, srcdir, builddir string) map[string]string {
	env := map[string]string{
		"DESTDIR": destdir,
		"SRC":     srcdir,
		"BUILD":   builddir,
		"NPROC":   fmt.Sprintf("%d", runtime.NumCPU()),
		"PREFIX":  "/usr",
		"CFLAGS":  "-O2 -pipe",
		"LDFLAGS": "-Wl,-O1,--as-needed",
	}
	for k,v := range r.Vars { env[k]=v }
	return env
}
func flattenEnv(m map[string]string) []string {
	out := make([]string,0,len(m))
	for k,v := range m { out = append(out, fmt.Sprintf("%s=%s", k, v)) }
	sort.Strings(out)
	return out
}

func runStage(ctx context.Context, r *Recipe, script, workdir string, env map[string]string, logw io.Writer) error {
	if strings.TrimSpace(script)=="" { return nil }
	sh := exec.CommandContext(ctx, "/bin/sh", "-euo", "pipefail", "-c", script)
	sh.Env = append(os.Environ(), flattenEnv(env)...)
	sh.Dir = workdir
	sh.Stdout, sh.Stderr = logw, logw
	return sh.Run()
}

func installStage(ctx context.Context, r *Recipe, srcdir, destdir string, env map[string]string, logw io.Writer) error {
	script := r.Stages["install"]
	if strings.TrimSpace(script)=="" { return nil }
	if v, ok := r.Options["fakeroot"]; ok {
		if b, ok2 := v.(bool); ok2 && b {
			if _, err := exec.LookPath("fakeroot"); err != nil {
				return fmt.Errorf("receita requer fakeroot, mas não está instalado")
			}
			w := fmt.Sprintf("fakeroot -- /bin/sh -euo pipefail -c %q", script)
			return runStage(ctx, r, w, srcdir, env, logw)
		}
	}
	return runStage(ctx, r, script, srcdir, env, logw)
}

func stripELF(destdir string, logw io.Writer) error {
	cmd := exec.Command("/bin/sh", "-c",
		fmt.Sprintf("find %s -type f -exec sh -c 'file -b \"$1\" | grep -q ELF && strip -s \"$1\" || true' sh {} \\;", shellQuote(destdir)))
	cmd.Stdout, cmd.Stderr = logw, logw
	return cmd.Run()
}

/* ========= Fetch/Extract/Pack ========= */

func fetchSources(r *Recipe, cache string, logw io.Writer) error {
	if err := os.MkdirAll(cache, 0o755); err!=nil { return err }
	for _, s := range r.Source {
		if s.URL != "" {
			fn := s.Filename; if fn=="" {
				parts := strings.Split(s.URL, "/"); fn = parts[len(parts)-1]
			}
			dst := filepath.Join(cache, fn)
			if _, err := os.Stat(dst); err==nil {
				fmt.Fprintln(logw, "cache hit:", dst); continue
			}
			if _, err := exec.LookPath("curl"); err==nil {
				fmt.Fprintln(logw, "baixando (curl):", s.URL)
				cmd := exec.Command("curl", "-L", "-o", dst, s.URL)
				cmd.Stdout, cmd.Stderr = logw, logw
				if err := cmd.Run(); err != nil { return err }
			} else {
				fmt.Fprintln(logw, "baixando (http):", s.URL)
				resp, err := http.Get(s.URL); if err!=nil { return err }
				defer resp.Body.Close()
				f, err := os.Create(dst); if err!=nil { return err }
				if _, err := io.Copy(f, resp.Body); err!=nil { f.Close(); return err }
				f.Close()
			}
		} else if s.Git != "" {
			base := filepath.Join(cache, "git", gitKey(s.Git))
			if _, err := os.Stat(base); err != nil {
				if err := os.MkdirAll(filepath.Dir(base), 0o755); err != nil { return err }
				cmd := exec.Command("git", "clone", "--depth=1", s.Git, base)
				cmd.Stdout, cmd.Stderr = logw, logw
				if err := cmd.Run(); err != nil { return err }
			}
			ref := s.Tag; if ref=="" { ref = s.Commit }
			if ref != "" {
				cmd := exec.Command("git", "-C", base, "checkout", ref)
				cmd.Stdout, cmd.Stderr = logw, logw
				if err := cmd.Run(); err != nil { return err }
			}
			// cria um tar da árvore para simular “arquivo de origem”
			tmpTar := filepath.Join(cache, fmt.Sprintf("%s-%s.tar.zst", r.Package, refOr("HEAD", ref)))
			if _, err := os.Stat(tmpTar); err != nil {
				if err := runLogged(logw, "tar", "-C", base, "-I", "zstd -19 --long=31", "-cf", tmpTar, "."); err != nil { return err }
			}
		}
	}
	return nil
}

func extractAll(r *Recipe, srcCache, buildDir string, logw io.Writer) (string, error) {
	if err := os.MkdirAll(buildDir, 0o755); err!=nil { return "", err }
	var srcdir string
	for _, s := range r.Source {
		if s.URL=="" && s.Git=="" { continue }
		var archive string
		if s.URL!="" {
			fn := s.Filename; if fn=="" { parts:=strings.Split(s.URL,"/"); fn = parts[len(parts)-1] }
			archive = filepath.Join(srcCache, fn)
		} else { // git tar criado em fetch
			ref := s.Tag; if ref=="" { ref = s.Commit }
			archive = filepath.Join(srcCache, "git", "..", fmt.Sprintf("%s-%s.tar.zst", r.Package, refOr("HEAD", ref)))
			archive = filepath.Clean(archive)
			if _, err := os.Stat(archive); err != nil {
				// fallback: extrair diretório git diretamente
				base := filepath.Join(srcCache, "git", gitKey(s.Git))
				if err := runLogged(logw, "tar", "-C", base, "-I", "zstd -19 --long=31", "-cf", filepath.Join(srcCache, fmt.Sprintf("%s-HEAD.tar.zst", r.Package)), "."); err != nil {
					return "", err
				}
				archive = filepath.Join(srcCache, fmt.Sprintf("%s-HEAD.tar.zst", r.Package))
			}
		}
		if err := extractArchive(archive, buildDir, logw); err != nil { return "", err }
	}
	if srcdir=="" {
		entries, _ := os.ReadDir(buildDir)
		for _, e := range entries {
			if e.IsDir() {
				srcdir = filepath.Join(buildDir, e.Name()); break
			}
		}
		if srcdir=="" { srcdir = buildDir }
	}
	return srcdir, nil
}

func extractArchive(archive, dst string, logw io.Writer) error {
	switch {
	case strings.HasSuffix(archive, ".tar.xz"):
		return runLogged(logw, "tar", "-C", dst, "-xJf", archive)
	case strings.HasSuffix(archive, ".tar.gz"), strings.HasSuffix(archive, ".tgz"):
		return runLogged(logw, "tar", "-C", dst, "-xzf", archive)
	case strings.HasSuffix(archive, ".tar.bz2"):
		return runLogged(logw, "tar", "-C", dst, "-xjf", archive)
	case strings.HasSuffix(archive, ".tar.zst"):
		return runLogged(logw, "tar", "-C", dst, "-I", "zstd -d", "-xf", archive)
	case strings.HasSuffix(archive, ".zip"):
		return runLogged(logw, "unzip", "-q", "-d", dst, archive)
	default:
		return fmt.Errorf("formato não suportado: %s", archive)
	}
}

func packDir(destdir, out string, logw io.Writer) error {
	if err := os.MkdirAll(filepath.Dir(out), 0o755); err!=nil { return err }
	manifest := filepath.Join(destdir, "manifest.txt")
	if err := writeManifest(destdir, manifest); err!=nil { return err }
	return runLogged(logw, "tar", "-C", destdir, "-I", "zstd -19 --long=31", "-cf", out, ".")
}

func extractPack(archive, root string, logw io.Writer) error {
	return runLogged(logw, "tar", "-C", root, "-I", "zstd -d", "-xf", archive)
}

func writeManifest(root, path string) error {
	f, err := os.Create(path); if err!=nil { return err }
	defer f.Close()
	return filepath.WalkDir(root, func(p string, d fs.DirEntry, err error) error {
		if err!=nil { return err }
		if d.IsDir() { return nil }
		rel, _ := filepath.Rel(root, p)
		_, _ = fmt.Fprintf(f, "/%s\n", filepath.ToSlash(rel))
		return nil
	})
}

func runLogged(w io.Writer, name string, args ...string) error {
	cmd := exec.Command(name, args...); cmd.Stdout, cmd.Stderr = w, w
	return cmd.Run()
}

/* ========= CLI / Comandos ========= */

type Config struct {
	Repo     string
	SrcDir   string
	BuildDir string
	PkgDir   string
	LogDir   string
	DBDir    string
	DestDir  string
	BinRepo  string
	Strip    bool
	Spinner  bool
	NoColor  bool
}

func defaultsFromEnv() Config {
	get := func(k, d string) string { if v:=os.Getenv(k); v!="" { return v }; return d }
	return Config{
		Repo:     get("LFSUP_REPO", "/opt/lfsup/repo"),
		SrcDir:   get("LFSUP_SRC", "/var/cache/lfsup/src"),
		BuildDir: get("LFSUP_BUILD", "/var/tmp/lfsup/build"),
		PkgDir:   get("LFSUP_PKG", "/var/cache/lfsup/pkg"),
		LogDir:   get("LFSUP_LOG", "/var/log/lfsup"),
		DBDir:    get("LFSUP_DB", "/var/lib/lfsup/db"),
		DestDir:  get("LFSUP_DESTDIR", "/var/tmp/lfsup/destdir"),
		BinRepo:  get("LFSUP_BINREPO", "/opt/lfsup/binrepo"),
		Strip:    false, Spinner: true, NoColor: false,
	}
}

func ensureDirs(cfg Config) error {
	for _, d := range []string{cfg.SrcDir,cfg.BuildDir,cfg.PkgDir,cfg.LogDir,cfg.DBDir,cfg.DestDir,cfg.BinRepo} {
		if err := os.MkdirAll(d, 0o755); err!=nil { return err }
	}
	return nil
}

func usage() {
	fmt.Println(`lfsup — gerenciador LFS em Go (arquivo único)
Comandos:
  search(s), info(i), status(st), graph(g)
  download(dl), extract(x), patch(p), build(b), check(ck),
  destinstall(di), pack(pk), install(in), remove(rm)
  revdep(rd) [--fix], rebuild(rw) [--reverse], upgrade(up [<pkg>|--all])
  sync-binrepo(sb), sync-repo(sr), doctor(dc)
Flags globais: --strip, --no-color, --no-spinner, --repo, --destdir`)
}

func main() {
	if len(os.Args)<2 { usage(); return }
	cfg := defaultsFromEnv()
	if repo := os.Getenv("REPO"); repo!="" { cfg.Repo = repo }

	cmd := os.Args[1]; args := os.Args[2:]

	gf := flag.NewFlagSet("global", flag.ContinueOnError)
	gf.SetOutput(new(bytes.Buffer))
	gStrip := gf.Bool("strip", cfg.Strip, "habilitar strip")
	gNoColor := gf.Bool("no-color", cfg.NoColor, "desabilitar cores")
	gNoSpin := gf.Bool("no-spinner", !cfg.Spinner, "desabilitar spinner")
	gRepo := gf.String("repo", cfg.Repo, "diretório do repo de receitas")
	gDest := gf.String("destdir", cfg.DestDir, "DESTDIR padrão")
	_ = gf.Parse(args)
	cfg.Strip = *gStrip; cfg.NoColor = *gNoColor; cfg.Spinner = !*gNoSpin; cfg.Repo = *gRepo; cfg.DestDir = *gDest
	enableColor = !cfg.NoColor

	if err := ensureDirs(cfg); err!=nil { fmt.Fprintln(os.Stderr, Red("Erro:"), err); os.Exit(1) }

	aliases := map[string]string{
		"s":"search","search":"search",
		"i":"info","info":"info",
		"st":"status","status":"status",
		"g":"graph","graph":"graph",
		"dl":"download","download":"download",
		"x":"extract","extract":"extract",
		"p":"patch","patch":"patch",
		"b":"build","build":"build",
		"ck":"check","check":"check",
		"di":"destinstall","destinstall":"destinstall",
		"pk":"pack","pack":"pack",
		"in":"install","install":"install",
		"rm":"remove","remove":"remove",
		"rd":"revdep","revdep":"revdep",
		"rw":"rebuild","rebuild":"rebuild",
		"up":"upgrade","upgrade":"upgrade",
		"sb":"sync-binrepo","sync-binrepo":"sync-binrepo",
		"sr":"sync-repo","sync-repo":"sync-repo",
		"dc":"doctor","doctor":"doctor",
	}
	resolved := aliases[cmd]; if resolved=="" {
		fmt.Fprintln(os.Stderr, Red("Comando desconhecido:"), cmd); usage(); os.Exit(2)
	}
	if err := dispatch(cfg, resolved, gf.Args()); err!=nil {
		fmt.Fprintln(os.Stderr, Red("Erro:"), err); os.Exit(1)
	}
}

func dispatch(cfg Config, cmd string, args []string) error {
	switch cmd {
	case "doctor": return doctor()
	case "search": return cmdSearch(cfg, strings.Join(args," "))
	case "info":
		if len(args)<1 { return errors.New("uso: lfsup info <pkg>") }
		return cmdInfo(cfg, args[0])
	case "status": return cmdSearch(cfg, "")
	case "graph":
		if len(args)<1 { return errors.New("uso: lfsup graph <pkg>") }
		return cmdGraph(cfg, args[0])
	case "download","extract","patch","build","check","destinstall","pack","install":
		if len(args)<1 { return fmt.Errorf("uso: lfsup %s <pkg>", cmd) }
		return doStages(cfg, cmd, args[0])
	case "remove":
		if len(args)<1 { return fmt.Errorf("uso: lfsup remove <pkg>") }
		return cmdRemove(cfg, args[0])
	case "revdep":
		if len(args)<1 { return fmt.Errorf("uso: lfsup revdep <pkg> [--fix]") }
		fix := false; for _,a := range args[1:] { if a=="--fix" { fix=true } }
		return cmdRevdep(cfg, args[0], fix)
	case "rebuild":
		reverse := false; for _,a := range args { if a=="--reverse" { reverse=true } }
		return cmdRebuildWorld(cfg, reverse)
	case "upgrade":
		if len(args)==0 || args[0]=="--all" { return cmdRebuildWorld(cfg, false) }
		return doStages(cfg, "install", args[0])
	case "sync-binrepo": return cmdSyncBinRepo(cfg)
	case "sync-repo":    return cmdSyncRepo(cfg)
	}
	return nil
}

/* ========= Comandos ========= */

func cmdSearch(cfg Config, term string) error {
	db, err := openDB(filepath.Join(cfg.DBDir, "lfsup.db")); if err!=nil { return err }
	defer db.Close()
	recs, err := loadAllRecipes(cfg.Repo); if err!=nil { return err }
	names := make([]string,0,len(recs))
	termL := strings.ToLower(term)
	for name, r := range recs {
		if term=="" || strings.Contains(strings.ToLower(name), termL) || strings.Contains(strings.ToLower(r.Summary), termL) {
			names = append(names, name)
		}
	}
	sort.Strings(names)
	for _, name := range names {
		r := recs[name]
		fmt.Printf("%s %-22s %-8s %s\n", Mark(db.IsInstalled(name)), name, r.Version, r.Summary)
	}
	return nil
}

func cmdInfo(cfg Config, name string) error {
	recs, err := loadAllRecipes(cfg.Repo); if err!=nil { return err }
	r := recs[name]; if r==nil { return fmt.Errorf("receita não encontrada: %s", name) }
	fmt.Printf("%s %s-%s (release %d)\n", Bold(name), r.Version, Dim(r.License), r.Release)
	fmt.Println("Resumo:", r.Summary)
	fmt.Println("Homepage:", r.Homepage)
	fmt.Println("Requer:", strings.Join(r.Requires, ", "))
	fmt.Println("Fornece:", strings.Join(r.Provides, ", "))
	fmt.Println("Opções:", r.Options)
	fmt.Println("Arquivo:", r._path)
	return nil
}

func cmdGraph(cfg Config, name string) error {
	recs, err := loadAllRecipes(cfg.Repo); if err!=nil { return err }
	g := buildGraph(recs); order, err := topo(g); if err!=nil { return err }
	fmt.Println("Topo-sort do mundo:", strings.Join(order, " -> "))
	fmt.Println("Dependências de", name, ":", strings.Join(g[name], ", "))
	return nil
}

func doStages(cfg Config, upTo string, name string) error {
	recs, err := loadAllRecipes(cfg.Repo); if err!=nil { return err }
	r := recs[name]; if r==nil { return fmt.Errorf("receita não encontrada: %s", name) }
	db, err := openDB(filepath.Join(cfg.DBDir, "lfsup.db")); if err!=nil { return err }
	defer db.Close()

	g := buildGraph(recs)
	order, err := resolveFor(name, g); if err!=nil { return err }
	for _, dep := range order {
		if dep!=name && db.IsInstalled(dep) { continue }
		if err := runPackage(cfg, recs[dep], upTo, db); err!=nil { return err }
	}
	return runPackage(cfg, r, upTo, db)
}

func runPackage(cfg Config, r *Recipe, upTo string, db *DB) error {
	ctx := context.Background()
	wd := filepath.Join(cfg.BuildDir, fmt.Sprintf("%s-%s", r.Package, r.Version))
	_ = os.MkdirAll(wd, 0o755)
	logPath := filepath.Join(cfg.LogDir, fmt.Sprintf("%s-%s.log", r.Package, r.Version))
	logw, err := os.Create(logPath); if err!=nil { return err }
	defer logw.Close()

	env := defaultEnv(r, cfg.DestDir, cfg.SrcDir, cfg.BuildDir)
	dest := filepath.Join(cfg.DestDir, fmt.Sprintf("%s-%s", r.Package, r.Version))
	_ = os.MkdirAll(dest, 0o755)

	step := func(label, script, workdir string) error {
		if strings.TrimSpace(script)=="" { return nil }
		var sp *spinner; if cfg.Spinner { sp = newSpinner(label) }
		err := runStage(ctx, r, script, workdir, env, logw)
		if sp!=nil { if err!=nil { sp.Fail() } else { sp.Succeed() } }
		return err
	}

	if err := fetchSources(r, cfg.SrcDir, logw); err!=nil { return err }
	if upTo=="download" { return nil }

	srcdir, err := extractAll(r, cfg.SrcDir, wd, logw); if err!=nil { return err }
	if upTo=="extract" { return nil }

	if err := step("patch", r.Stages["patch"], srcdir); err!=nil { return err }
	if upTo=="patch" { return nil }
	if err := step("preconfig", r.Stages["preconfig"], srcdir); err!=nil { return err }
	if err := step("prepare", r.Stages["prepare"], srcdir); err!=nil { return err }
	if err := step("build", r.Stages["build"], srcdir); err!=nil { return err }
	if upTo=="build" { return nil }
	if err := step("check", r.Stages["check"], srcdir); err!=nil { return err }
	if upTo=="check" { return nil }

	if upTo=="destinstall" || upTo=="install" || upTo=="pack" {
		if err := installStage(ctx, r, srcdir, dest, env, logw); err!=nil { return err }
	}
	if upTo=="destinstall" { return nil }

	if cfg.Strip {
		if err := stripELF(dest, logw); err!=nil { return err }
	}

	pkgPath := filepath.Join(cfg.PkgDir, fmt.Sprintf("%s-%s-%d.tar.zst", r.Package, r.Version, r.Release))
	if err := packDir(dest, pkgPath, logw); err!=nil { return err }
	if upTo=="pack" { return nil }

	if err := extractPack(pkgPath, "/", logw); err!=nil { return err }
	if err := db.Register(r.Package, r.Version, r.Release, dest); err!=nil { return err }

	if err := step("postinstall", r.Stages["postinstall"], srcdir); err!=nil { return err }
	_ = runTriggers(cfg.Repo)
	return nil
}

func cmdRemove(cfg Config, name string) error {
	db, err := openDB(filepath.Join(cfg.DBDir, "lfsup.db")); if err!=nil { return err }
	defer db.Close()
	man, err := db.Manifest(name); if err!=nil { return err }
	for _, f := range man.Files {
		path := strings.TrimSpace(f.Path)
		if path!="" { _ = os.RemoveAll(path) }
	}
	recs, _ := loadAllRecipes(cfg.Repo)
	if r := recs[name]; r!=nil && strings.TrimSpace(r.PostRemove)!="" {
		ctx := context.Background()
		wd := filepath.Join(cfg.BuildDir, fmt.Sprintf("%s-%s", r.Package, r.Version))
		env := defaultEnv(r, cfg.DestDir, cfg.SrcDir, cfg.BuildDir)
		_ = runStage(ctx, r, r.PostRemove, wd, env, os.Stdout)
	}
	return db.Unregister(name)
}

/* ========= revdep real (ldd) ========= */

func cmdRevdep(cfg Config, name string, fix bool) error {
	db, err := openDB(filepath.Join(cfg.DBDir, "lfsup.db")); if err!=nil { return err }
	defer db.Close()

	// libs oferecidas por <name>
	man, err := db.Manifest(name); if err!=nil { return err }
	libNames := map[string]bool{}
	for _, f := range man.Files {
		p := strings.TrimSpace(f.Path)
		if p=="" { continue }
		if isELFShared(p) {
			base := filepath.Base(p)
			libNames[base]=true
		}
	}

	installed, _ := db.Installed()
	recs, _ := loadAllRecipes(cfg.Repo)
	var dependents []string

	for _, pkg := range installed {
		if pkg==name { continue }
		man2, err := db.Manifest(pkg); if err!=nil { continue }
		pulls := false
		for _, f := range man2.Files {
			p := strings.TrimSpace(f.Path)
			if p=="" { continue }
			if !isELF(p) { continue }
			missing, uses := lddUsesAny(p, libNames)
			if missing || uses { pulls = true; break }
		}
		if pulls { dependents = append(dependents, pkg) }
	}

	if len(dependents)==0 {
		fmt.Println("Sem dependentes detectados.")
		return nil
	}
	fmt.Println("Pacotes que dependem de", Bold(name), ":")
	for _, d := range dependents { fmt.Println(" -", d) }

	if fix {
		fmt.Println(Yellow("Recompilando dependentes..."))
		for _, d := range dependents {
			if err := doStages(cfg, "install", d); err!=nil { return err }
		}
	}
	return nil
}

func isELF(path string) bool {
	out, _ := exec.Command("file", "-b", path).Output()
	return bytes.Contains(out, []byte("ELF"))
}
func isELFShared(path string) bool {
	out, _ := exec.Command("file", "-b", path).Output()
	return bytes.Contains(out, []byte("shared object")) || bytes.Contains(out, []byte("dynamically linked"))
}

func lddUsesAny(path string, names map[string]bool) (missing bool, uses bool) {
	cmd := exec.Command("ldd", path)
	out, err := cmd.Output(); if err!=nil { return false, false }
	sc := bufio.NewScanner(bytes.NewReader(out))
	for sc.Scan() {
		line := sc.Text()
		if strings.Contains(line, "=> not found") { missing = true }
		for name := range names {
			if strings.Contains(line, name) { uses = true }
		}
	}
	return
}

/* ========= rebuild/sync ========= */

func cmdRebuildWorld(cfg Config, reverse bool) error {
	recs, err := loadAllRecipes(cfg.Repo); if err!=nil { return err }
	g := buildGraph(recs); order, err := topo(g); if err!=nil { return err }
	if reverse {
		for i,j:=0,len(order)-1; i<j; i,j = i+1, j-1 { order[i],order[j]=order[j],order[i] }
	}
	for _, p := range order {
		if err := doStages(cfg, "install", p); err!=nil { return err }
	}
	return nil
}

func cmdSyncBinRepo(cfg Config) error {
	files, _ := filepath.Glob(filepath.Join(cfg.PkgDir, "*.tar.zst"))
	type entry struct{ File string }
	var idx []entry
	for _, f := range files {
		dst := filepath.Join(cfg.BinRepo, filepath.Base(f))
		if err := copyFile(f, dst); err==nil { idx = append(idx, entry{File: filepath.Base(f)}) }
	}
	var buf bytes.Buffer
	buf.WriteString("[\n")
	for i, e := range idx {
		fmt.Fprintf(&buf, "  {\"file\": %q}", e.File)
		if i < len(idx)-1 { buf.WriteString(",") }
		buf.WriteString("\n")
	}
	buf.WriteString("]\n")
	if err := os.WriteFile(filepath.Join(cfg.BinRepo, "index.json"), buf.Bytes(), 0o644); err!=nil { return err }
	_ = runQuiet("git", "-C", cfg.BinRepo, "add", "-A")
	_ = runQuiet("git", "-C", cfg.BinRepo, "commit", "-m", "update", "--allow-empty")
	_ = runQuiet("git", "-C", cfg.BinRepo, "push")
	fmt.Println("binrepo sincronizado em", cfg.BinRepo)
	return nil
}

func cmdSyncRepo(cfg Config) error {
	if _, err := os.Stat(filepath.Join(cfg.Repo, ".git")); err!=nil {
		return fmt.Errorf("repo de receitas não é um repositório git: %s", cfg.Repo)
	}
	_ = runQuiet("git", "-C", cfg.Repo, "add", "-A")
	_ = runQuiet("git", "-C", cfg.Repo, "commit", "-m", "update recipes", "--allow-empty")
	_ = runQuiet("git", "-C", cfg.Repo, "push")
	fmt.Println("repo de receitas sincronizado:", cfg.Repo)
	return nil
}

/* ========= Triggers/Doctor/Utils ========= */

func runTriggers(repo string) error {
	// Lugar para “gatilhos” globais simples (atualizar cache ldconfig, etc)
	_ = runQuiet("ldconfig")
	return nil
}

func doctor() error {
	reqs := []string{"curl","tar","xz","zstd","git","unzip","file","strip","ldd"}
	ok := true
	for _, b := range reqs {
		if _, err := exec.LookPath(b); err!=nil { fmt.Println(Red("faltando:"), b); ok=false }
	}
	if _, err := exec.LookPath("fakeroot"); err!=nil {
		fmt.Println(Yellow("opcional: fakeroot ausente (requerido por receitas com options.fakeroot: true)"))
	}
	if ok { fmt.Println(Green("ok:"), "dependências básicas disponíveis") }
	return nil
}

/* ========= Helpers ========= */

func splitLines(s string) []string {
	var out []string; start:=0
	for i, ch := range s {
		if ch=='\n' { out = append(out, s[start:i]); start=i+1 }
	}
	if start<len(s) { out = append(out, s[start:]) }
	return out
}

func copyFile(src, dst string) error {
	in, err := os.Open(src); if err!=nil { return err }
	defer in.Close()
	if err := os.MkdirAll(filepath.Dir(dst), 0o755); err!=nil { return err }
	out, err := os.Create(dst); if err!=nil { return err }
	defer out.Close()
	_, err = io.Copy(out, in); return err
}

func runQuiet(name string, args ...string) error {
	cmd := exec.Command(name, args...); cmd.Stdout = io.Discard; cmd.Stderr = io.Discard
	return cmd.Run()
}

func gitKey(url string) string {
	k := strings.TrimPrefix(url, "https://")
	k = strings.TrimPrefix(k, "http://")
	k = strings.TrimSuffix(k, ".git")
	k = strings.ReplaceAll(k, "/", "_")
	return k
}
func refOr(def, v string) string { if v=="" { return def }; return v }

func shellQuote(s string) string {
	if strings.ContainsAny(s, " '\"\\") {
		return "'" + strings.ReplaceAll(s, "'", "'\\''") + "'"
	}
	return s
}
