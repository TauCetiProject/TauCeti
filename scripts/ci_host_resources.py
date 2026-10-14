#!/usr/bin/env python3
"""Run the unchanged sandbox command and observe resources from the trusted host.

No candidate paths are read. Output is outside the sandbox mounts. Host counters
include other work on the machine; wait4 counters belong to the command tree
(reaped descendants), and max RSS is the largest process, not aggregate memory.
Sampling is bounded to six small proc reads every five seconds, 2880 samples.
Telemetry errors never change the command's exit status. No merge consumer.
"""
import argparse
import ctypes
import datetime as dt
import json
import os
from pathlib import Path
import signal
import subprocess
import threading
import time

INTERVAL = 5
MAX_SAMPLES = 2880
DESCENDANT_GRACE = 1.0
MAX_READ = 65536


def now():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def read(path):
    with open(path) as handle:
        return handle.read(MAX_READ)


def snapshot():
    result, missing = {}, []
    for name in ('stat', 'meminfo', 'diskstats', 'pressure/cpu', 'pressure/memory', 'pressure/io'):
        try:
            value = read('/proc/' + name)
            if len(value) == MAX_READ:
                missing.append(name + '-truncated')
            if name == 'stat':
                ticks = list(map(int, value.splitlines()[0].split()[1:9]))
                result['cpu_total_ticks'] = sum(ticks)  # excludes duplicate guest ticks
                result['cpu_busy_ticks'] = sum(ticks) - ticks[3] - ticks[4]
            elif name == 'meminfo':
                mem = {line.split(':')[0]: int(line.split()[1]) for line in value.splitlines()}
                result['host_used_bytes'] = (mem['MemTotal'] - mem['MemAvailable']) * 1024
            elif name == 'diskstats':
                # Whole devices only (sysfs partition marker); avoid summing partitions twice.
                devices = {}
                for line in value.splitlines():
                    fields = line.split()
                    device = fields[2]
                    if len(fields) >= 14 and not device.startswith(('loop', 'ram')) and not os.path.exists('/sys/class/block/' + device + '/partition'):
                        devices[device] = {'read_bytes': int(fields[5]) * 512,
                                           'write_bytes': int(fields[9]) * 512}
                result['host_devices'] = devices  # stacked devices can still overlap
            else:
                result[name.replace('/', '_') + '_us'] = {
                    fields[0]: int(dict(item.split('=') for item in fields[1:])['total'])
                    for fields in (line.split() for line in value.splitlines())}
        except (OSError, ValueError, KeyError, IndexError):
            missing.append(name)
    result['missing'] = missing
    return result


class Sampler:
    def __init__(self):
        self.first = self.last = None
        self.peak = None
        self.samples = 0
        self.attempts = 0
        self.missing = set()
        self.cpu_s = 0
        self.started = self.ended = None
        self.lock = threading.Lock()
        self.cached = self._summary()

    def sample(self):
        # The completion sample can race a watcher already past its loop guard.
        # Reserve attempts under the same lock as sampling; never wait on a
        # slow optional proc read just to return the command's outcome.
        if not self.lock.acquire(blocking=False):
            return False
        try:
            if self.attempts >= MAX_SAMPLES:
                return False
            start = time.thread_time()
            self.attempts += 1
            try:
                value = snapshot()
                self.started = self.started or time.monotonic()
                self.ended = time.monotonic()
                self.first = self.first or value
                self.last = value
                self.samples += 1
                self.missing.update(value['missing'])
                if 'host_used_bytes' in value:
                    self.peak = max(self.peak or 0, value['host_used_bytes'])
            except Exception:
                self.missing.add('sampler-error')
            finally:
                self.cpu_s += time.thread_time() - start
                self.cached = self._summary()
            return True
        finally:
            self.lock.release()

    def watch(self, done):
        while self.attempts < MAX_SAMPLES and not done.wait(INTERVAL):
            try:
                self.sample()
            except Exception:
                self.missing.add('sampler-error')

    def summary(self):
        if not self.lock.acquire(blocking=False):
            # One immutable completed summary; do not read mutable state while
            # the watcher is publishing its next sample.
            result = dict(self.cached)
            result['missing'] = sorted(set(result['missing']) | {'sample-in-progress-at-finish'})
            result['sample_attempts'] = self.attempts
            result['sample_limit_reached'] = self.attempts >= MAX_SAMPLES
            return result
        try:
            return self._summary()
        finally:
            self.lock.release()

    def _summary(self):
        first, last = self.first or {}, self.last or {}
        def delta(key):
            if key not in first or key not in last:
                return None
            return max(0, last[key] - first[key])
        total, busy = delta('cpu_total_ticks'), delta('cpu_busy_ticks')
        pressure = {}
        for name in ('cpu', 'memory', 'io'):
            key = 'pressure_' + name + '_us'
            pressure[name] = {kind: max(0, value - first[key][kind])
                              for kind, value in last.get(key, {}).items()
                              if kind in first.get(key, {})}
        devices = {name: {kind: max(0, value - first['host_devices'][name][kind])
                          for kind, value in counters.items()}
                   for name, counters in last.get('host_devices', {}).items()
                   if name in first.get('host_devices', {})}
        return {'samples': self.samples, 'sample_attempts': self.attempts, 'interval_s': INTERVAL, 'sample_limit': MAX_SAMPLES,
                'sampler_cpu_s': self.cpu_s,
                'sample_limit_reached': self.attempts >= MAX_SAMPLES,
                'sampled_elapsed_s': self.ended - self.started if self.started is not None else None,
                'missing': sorted(self.missing),
                'host_cpu_busy_fraction': busy / total if total else None,
                'host_used_peak_bytes': self.peak, 'host_pressure_stall_us': pressure,
                'host_device_io_bytes': devices}


def descendant_accounting():
    """Adopt orphaned sandbox init processes so wait4 sees their reaped work.

    With --unshare-pid, bubblewrap reports through an eventfd and exits before
    reaping its PID-namespace init. A direct wait4 therefore misses the sandbox.
    Subreaping affects only this wrapper's descendants, never sandbox arguments.
    """
    try:
        libc = ctypes.CDLL(None, use_errno=True)
        previous = ctypes.c_int()
        if libc.prctl(37, ctypes.byref(previous), 0, 0, 0) != 0:
            raise OSError(ctypes.get_errno(), 'get subreaper')
        if libc.prctl(36, 1, 0, 0, 0) != 0:
            raise OSError(ctypes.get_errno(), 'set subreaper')
        return lambda: libc.prctl(36, previous.value, 0, 0, 0)
    except (AttributeError, OSError):
        return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', required=True)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if not command:
        parser.error('a command is required')
    started, start = now(), time.monotonic()
    sampler, done = Sampler(), threading.Event()
    try:
        sampler.sample()
    except Exception:
        sampler.missing.add('sampler-error')
    thread = threading.Thread(target=sampler.watch, args=(done,), daemon=True)
    restore_subreaper = descendant_accounting()
    if restore_subreaper is None:
        sampler.missing.add('descendant-accounting-unavailable')
    child = subprocess.Popen(command)
    try:
        thread.start()
    except Exception:
        sampler.missing.add('sampler-thread-unavailable')
    cancelled = []
    def forward(signum, _frame):
        cancelled.append(signum)
        try:
            child.send_signal(signum)
        except ProcessLookupError:
            pass
    for sig in (signal.SIGTERM, signal.SIGINT):
        signal.signal(sig, forward)
    totals = {'command_cpu_user_s': 0, 'command_cpu_system_s': 0,
              'command_max_process_rss_bytes': 0, 'command_block_input_ops': 0,
              'command_block_output_ops': 0}
    reaped = 0
    reaped_signals = []
    code = None
    drain_deadline = None
    try:
        while True:
            if code is None and child.returncode is not None:
                code = child.returncode
                sampler.missing.add('primary-resource-accounting-unavailable')
                drain_deadline = time.monotonic() + DESCENDANT_GRACE
            if restore_subreaper and code is not None and (
                    cancelled or time.monotonic() >= drain_deadline):
                sampler.missing.add('descendant-accounting-unfinished')
                break
            try:
                pid, status, usage = os.wait4(-1 if restore_subreaper else child.pid, os.WNOHANG)
            except InterruptedError:
                continue
            except ChildProcessError:
                break
            if pid == 0:
                time.sleep(.02)
                continue
            reaped += 1
            reaped_code = os.waitstatus_to_exitcode(status)
            if reaped_code < 0:
                reaped_signals.append(-reaped_code)
            if pid == child.pid:
                code = reaped_code
                child.returncode = code
                drain_deadline = time.monotonic() + DESCENDANT_GRACE
            totals['command_cpu_user_s'] += usage.ru_utime
            totals['command_cpu_system_s'] += usage.ru_stime
            totals['command_max_process_rss_bytes'] = max(
                totals['command_max_process_rss_bytes'], usage.ru_maxrss * 1024)
            totals['command_block_input_ops'] += usage.ru_inblock
            totals['command_block_output_ops'] += usage.ru_oublock
            if not restore_subreaper:
                break
    finally:
        if restore_subreaper:
            restore_subreaper()
    if code is None and child.returncode is not None:
        # Popen.send_signal polls first: a completion/signal race can reap the
        # primary child before wait4. Preserve its saved status and expose the
        # unavailable primary usage instead of changing the command outcome.
        code = child.returncode
        sampler.missing.add('primary-resource-accounting-unavailable')
    assert code is not None
    interrupted = bool(cancelled or reaped_signals) or code < 0 or 'descendant-accounting-unfinished' in sampler.missing
    if restore_subreaper and interrupted:
        # Killing a PID-namespace init can destroy live children before their
        # resource usage propagates. Preserve these lower bounds as partial.
        sampler.missing.add('descendant-accounting-interrupted')
    child.returncode = code
    done.set()
    if thread.ident is not None:
        thread.join(timeout=1)
    try:
        if sampler.attempts < MAX_SAMPLES:
            sampler.sample()
        record = {'schema': 'tauceti-ci.host-resources/v1', 'trust': 'host',
                  'scope': 'sandbox-command-tree-and-host', 'host_cpu_count': os.cpu_count(),
                  'run_id': os.environ.get('GITHUB_RUN_ID'),
                  'run_attempt': int(os.environ.get('GITHUB_RUN_ATTEMPT', '1')),
                  'workflow_sha': os.environ.get('CI_RESOURCE_WORKFLOW_SHA'),
                  'tested_head_sha': os.environ.get('CI_RESOURCE_TESTED_HEAD'),
                  'tested_base_sha': os.environ.get('CI_RESOURCE_TESTED_BASE'),
                  'dependency_bump': os.environ.get('CI_RESOURCE_DEPENDENCY_BUMP', 'unknown'),
                  'started_at': started, 'completed_at': now(), 'elapsed_s': time.monotonic() - start,
                  'exit_code': code, 'cancel_signals': cancelled,
                  'command_accounting_scope': ('partial-reaped-descendants' if interrupted else 'reaped-descendants')
                      if restore_subreaper else 'direct-child-only',
                  'reaped_processes': reaped, 'reaped_termination_signals': reaped_signals, **totals,
                  'observer_cpu_s': time.process_time(),
                  **sampler.summary()}
        out = Path(args.out)
        temporary = out.with_suffix('.tmp')
        temporary.write_text(json.dumps(record, sort_keys=True) + '\n')
        temporary.replace(out)
    except Exception as error:
        print('::warning::host resource telemetry unavailable: ' + type(error).__name__, flush=True)
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    raise SystemExit(main())
