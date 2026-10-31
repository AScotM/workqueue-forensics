package main

import (
	"context"
	"crypto/sha256"
	"encoding/csv"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"math"
	"os"
	"os/signal"
	"path/filepath"
	"regexp"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"syscall"
	"time"
)

type Metric struct {
	Name   string  `json:"name"`
	Value  float64 `json:"value"`
	Unit   string  `json:"unit,omitempty"`
	Source string  `json:"source"`
	Scope  string  `json:"scope,omitempty"`
}
type Finding struct {
	Severity string `json:"severity"`
	Code     string `json:"code"`
	Message  string `json:"message"`
	Source   string `json:"source,omitempty"`
}
type Worker struct {
	PID          int    `json:"pid"`
	Name         string `json:"name"`
	State        string `json:"state"`
	PPID         int    `json:"ppid"`
	CPU          int    `json:"cpu"`
	Threads      int    `json:"threads"`
	Voluntary    int64  `json:"voluntary_context_switches"`
	Nonvoluntary int64  `json:"nonvoluntary_context_switches"`
	UTime        uint64 `json:"utime_ticks"`
	STime        uint64 `json:"stime_ticks"`
	StartTime    uint64 `json:"starttime_ticks"`
	Affinity     string `json:"affinity,omitempty"`
	KernelThread bool   `json:"kernel_thread"`
}
type Record struct {
	Path   string `json:"path"`
	Value  string `json:"value"`
	Source string `json:"source"`
	Kind   string `json:"kind"`
}
type Snapshot struct {
	Schema    int       `json:"schema"`
	Timestamp time.Time `json:"timestamp"`
	Host      string    `json:"host"`
	Kernel    string    `json:"kernel"`
	BootID    string    `json:"boot_id"`
	Metrics   []Metric  `json:"metrics"`
	Workers   []Worker  `json:"workers"`
	Records   []Record  `json:"records"`
	Findings  []Finding `json:"findings"`
	Errors    []string  `json:"errors"`
	Digest    string    `json:"digest"`
}
type Delta struct {
	Name     string  `json:"name"`
	Previous float64 `json:"previous"`
	Current  float64 `json:"current"`
	Change   float64 `json:"change"`
	Rate     float64 `json:"rate_per_second,omitempty"`
	Unit     string  `json:"unit"`
	Source   string  `json:"source"`
}
type Comparison struct {
	From        time.Time `json:"from"`
	To          time.Time `json:"to"`
	Seconds     float64   `json:"seconds"`
	Metrics     []Delta   `json:"metrics"`
	NewWorkers  []Worker  `json:"new_workers"`
	GoneWorkers []Worker  `json:"gone_workers"`
	Findings    []Finding `json:"findings"`
}
type Options struct {
	Command      string
	Root         string
	Output       string
	Format       string
	Interval     time.Duration
	Count        int
	Limit        int
	Timeout      time.Duration
	Threshold    float64
	Baseline     string
	Save         string
	Pattern      string
	Strict       bool
	IncludeRaw   bool
	IncludeDebug bool
	IncludeAll   bool
	Sort         string
	Verbose      bool
}

var workerPattern = regexp.MustCompile(`^(kworker(?:/|$)|ksoftirqd/|kthread|rcu[a-z_]*|events(?:/|$))`)
var numberPattern = regexp.MustCompile(`[-+]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][-+]?[0-9]+)?`)

func rootPath(root, path string) string {
	if root == "" || root == "/" {
		return path
	}
	return filepath.Join(root, strings.TrimPrefix(path, "/"))
}
func readText(path string, limit int64) (string, error) {
	f, e := os.Open(path)
	if e != nil {
		return "", e
	}
	defer f.Close()
	b, e := io.ReadAll(io.LimitReader(f, limit))
	return strings.TrimSpace(string(b)), e
}
func readRelative(o Options, path string) (string, error) {
	return readText(rootPath(o.Root, path), 1<<20)
}
func parseFloat(s string) (float64, bool) {
	v, e := strconv.ParseFloat(strings.TrimSpace(s), 64)
	return v, e == nil && !math.IsNaN(v) && !math.IsInf(v, 0)
}
func parseNumber(s string) (float64, bool) { return parseFloat(numberPattern.FindString(s)) }
func appendMetric(s *Snapshot, name string, value float64, unit, source, scope string) {
	if !math.IsNaN(value) && !math.IsInf(value, 0) {
		s.Metrics = append(s.Metrics, Metric{name, value, unit, source, scope})
	}
}
func addError(s *Snapshot, where string, e error) {
	if e != nil {
		s.Errors = append(s.Errors, where+": "+e.Error())
	}
}
func parseKeyValues(s *Snapshot, content, source, prefix, scope string) {
	for _, line := range strings.Split(content, "\n") {
		f := strings.Fields(line)
		if len(f) < 2 {
			continue
		}
		v, ok := parseFloat(f[1])
		if !ok {
			continue
		}
		unit := ""
		if len(f) > 2 {
			unit = f[2]
		}
		appendMetric(s, prefix+"."+f[0], v, unit, source, scope)
	}
}
func inspectPressure(o Options, s *Snapshot) {
	for _, name := range []string{"cpu", "io", "memory"} {
		path := "/proc/pressure/" + name
		v, e := readRelative(o, path)
		if e != nil {
			addError(s, path, e)
			continue
		}
		for _, line := range strings.Split(v, "\n") {
			f := strings.Fields(line)
			if len(f) < 2 {
				continue
			}
			scope := f[0]
			for _, kv := range f[1:] {
				parts := strings.SplitN(kv, "=", 2)
				if len(parts) != 2 {
					continue
				}
				if n, ok := parseFloat(parts[1]); ok {
					unit := "percent"
					if parts[0] == "total" {
						unit = "microseconds"
					}
					appendMetric(s, "psi."+name+"."+scope+"."+parts[0], n, unit, path, scope)
				}
			}
		}
	}
}
func inspectVM(o Options, s *Snapshot) {
	path := "/proc/vmstat"
	v, e := readRelative(o, path)
	if e != nil {
		addError(s, path, e)
		return
	}
	wanted := []string{"allocstall", "compact", "pgscan", "pgsteal", "pgfault", "pgmajfault", "workingset", "oom_kill", "nr_dirty", "nr_writeback", "nr_slab", "nr_kernel_stack", "nr_unstable", "nr_vmscan"}
	for _, line := range strings.Split(v, "\n") {
		f := strings.Fields(line)
		if len(f) != 2 {
			continue
		}
		include := o.IncludeAll
		for _, w := range wanted {
			if strings.HasPrefix(f[0], w) {
				include = true
				break
			}
		}
		if !include {
			continue
		}
		if n, ok := parseFloat(f[1]); ok {
			appendMetric(s, "vm."+f[0], n, "count", path, "")
		}
	}
}
func inspectCPU(o Options, s *Snapshot) {
	path := "/proc/stat"
	v, e := readRelative(o, path)
	if e != nil {
		addError(s, path, e)
		return
	}
	for _, line := range strings.Split(v, "\n") {
		f := strings.Fields(line)
		if len(f) < 2 {
			continue
		}
		if f[0] == "cpu" || o.IncludeAll && strings.HasPrefix(f[0], "cpu") {
			names := []string{"user", "nice", "system", "idle", "iowait", "irq", "softirq", "steal", "guest", "guest_nice"}
			for i, n := range names {
				if i+1 < len(f) {
					if val, ok := parseFloat(f[i+1]); ok {
						appendMetric(s, "cpu."+f[0]+"."+n, val, "ticks", path, f[0])
					}
				}
			}
		} else if f[0] == "ctxt" || f[0] == "processes" || f[0] == "procs_running" || f[0] == "procs_blocked" || f[0] == "intr" || f[0] == "softirq" {
			if n, ok := parseFloat(f[1]); ok {
				appendMetric(s, "cpu."+f[0], n, "count", path, "")
			}
		}
	}
}
func inspectMem(o Options, s *Snapshot) {
	path := "/proc/meminfo"
	v, e := readRelative(o, path)
	if e != nil {
		addError(s, path, e)
		return
	}
	for _, line := range strings.Split(v, "\n") {
		f := strings.Fields(strings.ReplaceAll(line, ":", ""))
		if len(f) < 2 {
			continue
		}
		if n, ok := parseFloat(f[1]); ok {
			unit := ""
			if len(f) > 2 {
				unit = f[2]
			}
			appendMetric(s, "mem."+f[0], n, unit, path, "")
		}
	}
}
func inspectInterrupts(o Options, s *Snapshot) {
	for _, name := range []string{"softirqs", "interrupts"} {
		path := "/proc/" + name
		v, e := readRelative(o, path)
		if e != nil {
			addError(s, path, e)
			continue
		}
		for _, line := range strings.Split(v, "\n") {
			f := strings.Fields(line)
			if len(f) < 2 || !strings.HasSuffix(f[0], ":") {
				continue
			}
			key := strings.TrimSuffix(f[0], ":")
			if name == "interrupts" && !o.IncludeAll && key != "LOC" && key != "RES" && key != "CAL" && key != "TLB" && key != "IWI" && key != "RTR" {
				continue
			}
			total := float64(0)
			for _, x := range f[1:] {
				n, ok := parseFloat(x)
				if !ok {
					break
				}
				total += n
			}
			appendMetric(s, name+"."+key, total, "count", path, "")
		}
	}
}
func inspectLoad(o Options, s *Snapshot) {
	path := "/proc/loadavg"
	v, e := readRelative(o, path)
	if e != nil {
		addError(s, path, e)
		return
	}
	f := strings.Fields(v)
	for i, n := range []string{"one", "five", "fifteen"} {
		if i < len(f) {
			if x, ok := parseFloat(f[i]); ok {
				appendMetric(s, "load."+n, x, "load", path, "")
			}
		}
	}
	if len(f) > 3 {
		p := strings.Split(f[3], "/")
		if len(p) == 2 {
			if n, ok := parseFloat(p[0]); ok {
				appendMetric(s, "load.running", n, "tasks", path, "")
			}
			if n, ok := parseFloat(p[1]); ok {
				appendMetric(s, "load.total", n, "tasks", path, "")
			}
		}
	}
}
func inspectWorkqueue(o Options, s *Snapshot) {
	paths := []string{"/sys/module/workqueue/parameters/power_efficient", "/sys/module/workqueue/parameters/disable_numa", "/sys/module/workqueue/parameters/debug_force_rr_cpu", "/sys/module/workqueue/parameters/default_affinity_scope", "/sys/devices/virtual/workqueue/cpumask", "/sys/devices/virtual/workqueue/cpumask_requested", "/sys/devices/virtual/workqueue/affinity_scope", "/sys/devices/virtual/workqueue/affinity_strict", "/sys/devices/system/cpu/online", "/sys/devices/system/cpu/possible", "/sys/devices/system/cpu/present", "/sys/devices/system/node/online", "/proc/sys/kernel/threads-max", "/proc/sys/kernel/pid_max"}
	for _, path := range paths {
		v, e := readRelative(o, path)
		if e == nil {
			s.Records = append(s.Records, Record{path, v, "sysfs/procfs", "parameter"})
			if n, ok := parseFloat(v); ok {
				appendMetric(s, "parameter."+strings.ReplaceAll(strings.Trim(path, "/"), "/", "."), n, "value", path, "")
			}
		}
	}
	root := rootPath(o.Root, "/sys/devices/virtual/workqueue")
	entries, e := os.ReadDir(root)
	if e != nil {
		addError(s, root, e)
		return
	}
	for _, entry := range entries {
		if !entry.IsDir() {
			continue
		}
		name := entry.Name()
		if o.Pattern != "" && !strings.Contains(name, o.Pattern) {
			continue
		}
		dir := filepath.Join(root, name)
		children, e := os.ReadDir(dir)
		if e != nil {
			continue
		}
		for _, child := range children {
			if child.IsDir() {
				continue
			}
			if len(s.Records) >= o.Limit {
				break
			}
			path := filepath.Join(dir, child.Name())
			v, e := readText(path, 4096)
			if e != nil || v == "" {
				continue
			}
			rel := "/sys/devices/virtual/workqueue/" + name + "/" + child.Name()
			s.Records = append(s.Records, Record{rel, v, "sysfs", "workqueue"})
			if n, ok := parseFloat(v); ok {
				appendMetric(s, "workqueue."+name+"."+child.Name(), n, "value", rel, name)
			}
		}
	}
}
func parseProcStat(raw string) (Worker, error) {
	i := strings.IndexByte(raw, '(')
	j := strings.LastIndexByte(raw, ')')
	if i < 0 || j <= i {
		return Worker{}, errors.New("invalid stat format")
	}
	pid, e := strconv.Atoi(strings.TrimSpace(raw[:i]))
	if e != nil {
		return Worker{}, e
	}
	w := Worker{PID: pid, Name: raw[i+1 : j]}
	f := strings.Fields(raw[j+1:])
	if len(f) < 20 {
		return w, errors.New("truncated stat")
	}
	w.State = f[0]
	w.PPID, _ = strconv.Atoi(f[1])
	w.UTime, _ = strconv.ParseUint(f[11], 10, 64)
	w.STime, _ = strconv.ParseUint(f[12], 10, 64)
	w.Threads, _ = strconv.Atoi(f[17])
	w.StartTime, _ = strconv.ParseUint(f[19], 10, 64)
	if len(f) > 36 {
		w.CPU, _ = strconv.Atoi(f[36])
	}
	return w, nil
}
func inspectWorkers(o Options, s *Snapshot) {
	root := rootPath(o.Root, "/proc")
	entries, e := os.ReadDir(root)
	if e != nil {
		addError(s, root, e)
		return
	}
	for _, entry := range entries {
		pid, e := strconv.Atoi(entry.Name())
		if e != nil || pid < 1 {
			continue
		}
		stat, e := readText(filepath.Join(root, entry.Name(), "stat"), 8192)
		if e != nil {
			continue
		}
		w, e := parseProcStat(stat)
		if e != nil {
			continue
		}
		if !workerPattern.MatchString(w.Name) {
			continue
		}
		if o.Pattern != "" && !strings.Contains(w.Name, o.Pattern) {
			continue
		}
		cmd, _ := readText(filepath.Join(root, entry.Name(), "cmdline"), 4096)
		w.KernelThread = cmd == ""
		status, _ := readText(filepath.Join(root, entry.Name(), "status"), 16384)
		for _, line := range strings.Split(status, "\n") {
			f := strings.Fields(line)
			if len(f) < 2 {
				continue
			}
			switch f[0] {
			case "voluntary_ctxt_switches:":
				w.Voluntary, _ = strconv.ParseInt(f[1], 10, 64)
			case "nonvoluntary_ctxt_switches:":
				w.Nonvoluntary, _ = strconv.ParseInt(f[1], 10, 64)
			case "Cpus_allowed_list:":
				w.Affinity = f[1]
			}
		}
		s.Workers = append(s.Workers, w)
		if len(s.Workers) >= o.Limit {
			break
		}
	}
	sort.Slice(s.Workers, func(i, j int) bool { return s.Workers[i].PID < s.Workers[j].PID })
	appendMetric(s, "workers.observed", float64(len(s.Workers)), "threads", "/proc/*/stat", "")
	byState := map[string]int{}
	byName := map[string]int{}
	for _, w := range s.Workers {
		byState[w.State]++
		if strings.HasPrefix(w.Name, "kworker/") {
			byName["kworker"]++
		} else {
			byName[w.Name]++
		}
	}
	for k, n := range byState {
		appendMetric(s, "workers.state."+k, float64(n), "threads", "/proc/*/stat", k)
	}
	for k, n := range byName {
		appendMetric(s, "workers.group."+k, float64(n), "threads", "/proc/*/stat", k)
	}
}
func inspectDebug(o Options, s *Snapshot) {
	if !o.IncludeDebug {
		return
	}
	paths := []string{"/sys/kernel/debug/workqueue/workqueues", "/sys/kernel/debug/workqueue/pools", "/sys/kernel/debug/workqueue/worker_pools", "/sys/kernel/debug/workqueue/"}
	for _, path := range paths {
		v, e := readRelative(o, path)
		if e == nil && v != "" {
			if len(v) > 65536 {
				v = v[:65536]
			}
			s.Records = append(s.Records, Record{path, v, "debugfs", "diagnostic"})
		}
	}
	root := rootPath(o.Root, "/sys/kernel/debug/workqueue")
	entries, e := os.ReadDir(root)
	if e != nil {
		return
	}
	for _, entry := range entries {
		if entry.IsDir() || len(s.Records) >= o.Limit {
			continue
		}
		path := "/sys/kernel/debug/workqueue/" + entry.Name()
		v, e := readRelative(o, path)
		if e == nil && v != "" {
			if len(v) > 65536 {
				v = v[:65536]
			}
			s.Records = append(s.Records, Record{path, v, "debugfs", "diagnostic"})
		}
	}
}
func inspectKernel(o Options, s *Snapshot) {
	s.Host, _ = os.Hostname()
	s.Kernel, _ = readRelative(o, "/proc/sys/kernel/osrelease")
	s.BootID, _ = readRelative(o, "/proc/sys/kernel/random/boot_id")
	if o.Root != "" && o.Root != "/" {
		s.Host = "offline-root"
	}
	for _, path := range []string{"/proc/version", "/proc/sys/kernel/tainted", "/sys/kernel/security/lockdown"} {
		v, e := readRelative(o, path)
		if e == nil {
			s.Records = append(s.Records, Record{path, v, "kernel", "metadata"})
		}
	}
}
func analyze(s *Snapshot, o Options) {
	get := func(name string) float64 {
		for _, m := range s.Metrics {
			if m.Name == name {
				return m.Value
			}
		}
		return 0
	}
	for _, kind := range []string{"cpu", "io", "memory"} {
		for _, scope := range []string{"some", "full"} {
			n := "psi." + kind + "." + scope + ".avg10"
			v := get(n)
			if v >= o.Threshold {
				s.Findings = append(s.Findings, Finding{"warning", "pressure_high", fmt.Sprintf("%s pressure %.2f%% exceeds %.2f%%", kind+"/"+scope, v, o.Threshold), "/proc/pressure/" + kind})
			}
		}
	}
	if get("cpu.procs_blocked") > float64(runtime.NumCPU()) {
		s.Findings = append(s.Findings, Finding{"warning", "blocked_tasks", "blocked task count exceeds local CPU count", "/proc/stat"})
	}
	if len(s.Workers) == 0 {
		s.Findings = append(s.Findings, Finding{"info", "no_workers", "No matching kernel workers observed; process visibility may be restricted", "/proc"})
	}
	if len(s.Errors) > 0 {
		s.Findings = append(s.Findings, Finding{"info", "partial_visibility", fmt.Sprintf("%d optional or required interfaces unavailable", len(s.Errors)), ""})
	}
}
func collect(o Options) Snapshot {
	s := Snapshot{Schema: 1, Timestamp: time.Now().UTC(), Metrics: []Metric{}, Workers: []Worker{}, Records: []Record{}, Findings: []Finding{}, Errors: []string{}}
	inspectKernel(o, &s)
	inspectWorkqueue(o, &s)
	inspectWorkers(o, &s)
	inspectPressure(o, &s)
	inspectCPU(o, &s)
	inspectVM(o, &s)
	inspectMem(o, &s)
	inspectLoad(o, &s)
	inspectInterrupts(o, &s)
	inspectDebug(o, &s)
	sort.Slice(s.Metrics, func(i, j int) bool { return s.Metrics[i].Name < s.Metrics[j].Name })
	sort.Slice(s.Records, func(i, j int) bool { return s.Records[i].Path < s.Records[j].Path })
	analyze(&s, o)
	b, _ := json.Marshal(struct {
		Metrics []Metric
		Workers []Worker
		Records []Record
	}{s.Metrics, s.Workers, s.Records})
	h := sha256.Sum256(b)
	s.Digest = fmt.Sprintf("%x", h)
	return s
}
func compare(a, b Snapshot) Comparison {
	c := Comparison{From: a.Timestamp, To: b.Timestamp, Seconds: b.Timestamp.Sub(a.Timestamp).Seconds(), Metrics: []Delta{}, NewWorkers: []Worker{}, GoneWorkers: []Worker{}, Findings: []Finding{}}
	prev := map[string]Metric{}
	for _, m := range a.Metrics {
		prev[m.Name] = m
	}
	for _, m := range b.Metrics {
		p, ok := prev[m.Name]
		if !ok {
			continue
		}
		d := m.Value - p.Value
		rate := float64(0)
		if c.Seconds > 0 {
			rate = d / c.Seconds
		}
		c.Metrics = append(c.Metrics, Delta{m.Name, p.Value, m.Value, d, rate, m.Unit, m.Source})
	}
	old := map[string]Worker{}
	newWorkers := map[string]Worker{}
	key := func(w Worker) string { return fmt.Sprintf("%d/%d", w.PID, w.StartTime) }
	for _, w := range a.Workers {
		old[key(w)] = w
	}
	for _, w := range b.Workers {
		newWorkers[key(w)] = w
		if _, ok := old[key(w)]; !ok {
			c.NewWorkers = append(c.NewWorkers, w)
		}
	}
	for _, w := range a.Workers {
		if _, ok := newWorkers[key(w)]; !ok {
			c.GoneWorkers = append(c.GoneWorkers, w)
		}
	}
	if a.BootID != "" && b.BootID != "" && a.BootID != b.BootID {
		c.Findings = append(c.Findings, Finding{"warning", "boot_changed", "Boot ID changed; cumulative counter deltas may not be comparable", "/proc/sys/kernel/random/boot_id"})
	}
	return c
}
func loadSnapshot(path string) (Snapshot, error) {
	var s Snapshot
	b, e := os.ReadFile(path)
	if e != nil {
		return s, e
	}
	e = json.Unmarshal(b, &s)
	if e == nil && s.Schema != 1 {
		return s, fmt.Errorf("unsupported schema %d", s.Schema)
	}
	return s, e
}
func saveJSON(path string, v any) error {
	b, e := json.MarshalIndent(v, "", "  ")
	if e != nil {
		return e
	}
	if path == "-" {
		_, e = os.Stdout.Write(append(b, '\n'))
		return e
	}
	dir := filepath.Dir(path)
	f, e := os.CreateTemp(dir, ".workqueue-forensics-*")
	if e != nil {
		return e
	}
	name := f.Name()
	defer os.Remove(name)
	if _, e = f.Write(append(b, '\n')); e != nil {
		f.Close()
		return e
	}
	if e = f.Sync(); e != nil {
		f.Close()
		return e
	}
	if e = f.Close(); e != nil {
		return e
	}
	return os.Rename(name, path)
}
func output(o Options, v any) error {
	var w io.Writer = os.Stdout
	var f *os.File
	var e error
	if o.Output != "" && o.Output != "-" {
		f, e = os.Create(o.Output)
		if e != nil {
			return e
		}
		defer f.Close()
		w = f
	}
	switch o.Format {
	case "json":
		enc := json.NewEncoder(w)
		enc.SetIndent("", "  ")
		return enc.Encode(v)
	case "jsonl":
		return json.NewEncoder(w).Encode(v)
	case "csv":
		cw := csv.NewWriter(w)
		switch x := v.(type) {
		case Snapshot:
			cw.Write([]string{"name", "value", "unit", "source", "scope"})
			for _, m := range x.Metrics {
				cw.Write([]string{m.Name, strconv.FormatFloat(m.Value, 'f', -1, 64), m.Unit, m.Source, m.Scope})
			}
		case Comparison:
			cw.Write([]string{"name", "previous", "current", "change", "rate", "unit", "source"})
			for _, m := range x.Metrics {
				cw.Write([]string{m.Name, fmt.Sprint(m.Previous), fmt.Sprint(m.Current), fmt.Sprint(m.Change), fmt.Sprint(m.Rate), m.Unit, m.Source})
			}
		default:
			return errors.New("CSV supports snapshots and comparisons")
		}
		cw.Flush()
		return cw.Error()
	case "text":
		switch x := v.(type) {
		case Snapshot:
			fmt.Fprintf(w, "workqueue-forensics host=%s kernel=%s time=%s workers=%d metrics=%d findings=%d errors=%d\n", x.Host, x.Kernel, x.Timestamp.Format(time.RFC3339), len(x.Workers), len(x.Metrics), len(x.Findings), len(x.Errors))
			for _, m := range x.Metrics {
				fmt.Fprintf(w, "%-52s %16.3f %-12s %s\n", m.Name, m.Value, m.Unit, m.Source)
			}
			for _, worker := range x.Workers {
				fmt.Fprintf(w, "WORKER pid=%d name=%s state=%s cpu=%d affinity=%s\n", worker.PID, worker.Name, worker.State, worker.CPU, worker.Affinity)
			}
			for _, finding := range x.Findings {
				fmt.Fprintf(w, "FINDING %s %s %s\n", finding.Severity, finding.Code, finding.Message)
			}
		case Comparison:
			fmt.Fprintf(w, "comparison interval=%.3fs new_workers=%d gone_workers=%d\n", x.Seconds, len(x.NewWorkers), len(x.GoneWorkers))
			for _, d := range x.Metrics {
				fmt.Fprintf(w, "%-52s %14.3f -> %14.3f delta=%14.3f rate=%14.3f/s\n", d.Name, d.Previous, d.Current, d.Change, d.Rate)
			}
		default:
			return json.NewEncoder(w).Encode(v)
		}
		return nil
	default:
		return fmt.Errorf("unknown format %q", o.Format)
	}
}
func usage() {
	fmt.Fprintln(os.Stderr, "workqueue-forensics: snapshot | watch | compare | baseline | workers | pressure | parameters | findings | help")
	flag.PrintDefaults()
}
func run() error {
	o := Options{}
	flag.StringVar(&o.Root, "root", "/", "filesystem root for offline inspection")
	flag.StringVar(&o.Output, "output", "", "output file or stdout")
	flag.StringVar(&o.Format, "format", "text", "text, json, jsonl, csv")
	flag.DurationVar(&o.Interval, "interval", 5*time.Second, "sampling interval")
	flag.IntVar(&o.Count, "count", 1, "number of samples, zero for continuous watch")
	flag.IntVar(&o.Limit, "limit", 20000, "maximum records or workers")
	flag.DurationVar(&o.Timeout, "timeout", 0, "maximum watch duration")
	flag.Float64Var(&o.Threshold, "threshold", 20, "PSI avg10 warning threshold percent")
	flag.StringVar(&o.Baseline, "baseline", "", "existing snapshot path")
	flag.StringVar(&o.Save, "save", "", "save snapshot JSON to path")
	flag.StringVar(&o.Pattern, "pattern", "", "substring filter for workqueues and workers")
	flag.BoolVar(&o.Strict, "strict", false, "return nonzero if errors encountered")
	flag.BoolVar(&o.IncludeRaw, "raw", false, "include raw records in JSON output")
	flag.BoolVar(&o.IncludeDebug, "debugfs", false, "inspect debugfs workqueue interfaces when available")
	flag.BoolVar(&o.IncludeAll, "all", false, "include all procstat CPUs, VM counters, and interrupts")
	flag.StringVar(&o.Sort, "sort", "name", "sort preference reserved for reporting")
	flag.BoolVar(&o.Verbose, "verbose", false, "verbose diagnostics")
	flag.Usage = usage
	flag.Parse()
	if flag.NArg() > 0 {
		o.Command = flag.Arg(0)
	} else {
		o.Command = "snapshot"
	}
	if o.Limit < 1 || o.Interval <= 0 || o.Count < 0 || o.Threshold < 0 {
		return errors.New("invalid limit, interval, count or threshold")
	}
	if o.Command == "help" {
		usage()
		return nil
	}
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	if o.Timeout > 0 {
		var cancel context.CancelFunc
		ctx, cancel = context.WithTimeout(ctx, o.Timeout)
		defer cancel()
	}
	if o.Command == "compare" {
		if o.Baseline == "" || flag.NArg() < 2 {
			return errors.New("compare requires -baseline path and a snapshot filename")
		}
		a, e := loadSnapshot(o.Baseline)
		if e != nil {
			return e
		}
		b, e := loadSnapshot(flag.Arg(1))
		if e != nil {
			return e
		}
		return output(o, compare(a, b))
	}
	if o.Command == "watch" {
		var previous *Snapshot
		var baseline *Snapshot
		if o.Baseline != "" {
			s, e := loadSnapshot(o.Baseline)
			if e != nil {
				return e
			}
			baseline = &s
		}
		for i := 0; o.Count == 0 || i < o.Count; i++ {
			if ctx.Err() != nil {
				return nil
			}
			s := collect(o)
			if o.Save != "" {
				path := o.Save
				if o.Count != 1 {
					path = fmt.Sprintf("%s.%06d.json", o.Save, i)
				}
				if e := saveJSON(path, s); e != nil {
					return e
				}
			}
			if previous != nil {
				if e := output(o, compare(*previous, s)); e != nil {
					return e
				}
			} else if baseline != nil {
				if e := output(o, compare(*baseline, s)); e != nil {
					return e
				}
			} else {
				if e := output(o, s); e != nil {
					return e
				}
			}
			previous = &s
			if o.Strict && len(s.Errors) > 0 {
				return fmt.Errorf("%d inspection errors", len(s.Errors))
			}
			select {
			case <-ctx.Done():
				return nil
			case <-time.After(o.Interval):
			}
		}
		return nil
	}
	s := collect(o)
	if o.Save != "" {
		if e := saveJSON(o.Save, s); e != nil {
			return e
		}
	}
	if o.Baseline != "" {
		a, e := loadSnapshot(o.Baseline)
		if e != nil {
			return e
		}
		return output(o, compare(a, s))
	}
	switch o.Command {
	case "snapshot", "baseline":
	case "workers":
		s.Metrics = nil
		s.Records = nil
	case "pressure":
		var filtered []Metric
		for _, m := range s.Metrics {
			if strings.HasPrefix(m.Name, "psi.") {
				filtered = append(filtered, m)
			}
		}
		s.Metrics = filtered
		s.Workers = nil
		s.Records = nil
	case "parameters":
		s.Metrics = nil
		s.Workers = nil
	case "findings":
		s.Metrics = nil
		s.Workers = nil
		s.Records = nil
	default:
		return fmt.Errorf("unknown command %q", o.Command)
	}
	if !o.IncludeRaw && o.Command != "parameters" {
		s.Records = nil
	}
	if e := output(o, s); e != nil {
		return e
	}
	if o.Strict && len(s.Errors) > 0 {
		return fmt.Errorf("%d inspection errors", len(s.Errors))
	}
	return nil
}
func main() {
	if e := run(); e != nil {
		fmt.Fprintln(os.Stderr, "error:", e)
		os.Exit(1)
	}
}
