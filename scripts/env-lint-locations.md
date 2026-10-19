# Environment-linter retry locations

Refs TauCetiProject/TauCeti#17037. Production batch 816 compiled successfully but
failed `simpNF` on `TauCeti.element_annihilator_flat_baseChange`, without a source
diagnostic. The source hint was unavailable to the existing bors log parser.

The compiled driver now collects optional declaration origins and selection ranges
from its existing candidate environment and structured linter results. It does not
elaborate the library again, search sources for declaration names, or substitute
parent ranges for generated declarations. Private/generated declarations, missing
ranges, unsupported modules and unsupported report names remain unknown.

`LINT-ENV-ORIGINS` is internal driver output, before the existing report region.
Only after the existing nonce, report-count, default-linter, baseline and allowlist
validation does `lint-env.sh` join this metadata to its genuine NEW violations.
The optional Python join validates an exact module in the source inventory, a
regular project-local source path without symlink components, and an in-file line
and column. It never searches for a declaration's spelling. Docstring findings
without matching structured metadata are explicitly unknown.

The final log record is one line:

```text
LINT-ENV-LOCATIONS {"version":1,"complete":true,"findings":[{"linter":"simpNF","declaration":"TauCeti.element_annihilator_flat_baseChange","path":"TauCeti/RingTheory/Flat/Annihilator.lean","line":77,"column":9}]}
```

Unknown findings instead contain `linter`, `declaration` and `unknown`, with no
location. Bounds: 128 records, 1 MiB per metadata envelope, 1,024 characters per
declaration/report name, 512 per path, and at most 1 MiB of source characters read
per validated location. A record-limit envelope has `complete:false`. Duplicate,
missing, ambiguous, malformed or truncated origins become unknowns. Optional hint
collection cannot change lint's verdict, the ratchets or its completion nonce.

All candidate text, including valid-looking records, is untrusted. The bors
companion consumes only the final envelope in an authoritative failed job log,
under its existing candidate/generation/base/ordered-head digest/commit and
workflow/run/attempt/job binding. It stores only bounded observations, with
retry-only authority. Unknown findings have empty paths and force the existing
mapper's fallback. A location in an unchanged dependency needs existing complete
import attribution; it does not invent a changed owner. Multiple findings retain
all owners and the existing provider/bundle interaction rules.

A forged valid location may prioritize a retry, exactly like a forged compiler
diagnostic. It cannot identify individual guilt, hold or close PRs, revoke approval,
authorize merging, skip checks or change cache authority. Global interactions
remain possible; both retry groups still need authoritative full CI. Ordinary PR
compiled artifacts remain excluded from trusted shared caches.

## Validation and measurements

The [frozen evidence](env-lint-locations-evidence.json) records candidate 215,
generation 4, all 35 ordered heads, immutable base/tree/digest and the original
run/job. In a detached checkout of exact candidate `f7be37dc…`, building only
`TauCeti.RingTheory.Flat.Annihilator` and importing it with
`Mathlib.Algebra.Module.Torsion.Basic` reproduces the actual `simpNF` explanation:
`Ideal.annihilator_span_singleton_eq_torsionOf` simplifies the left side. The
driver reports the declaration at line 77, column 9. Importing Annihilator alone
passes, demonstrating why this is a global-environment finding rather than proof
of individual guilt. This bounded reproduction does not claim to reconstruct the
entire production import closure.

Appending the locally re-collected final record to the frozen native 7,299,216-byte
production log allows the production pure planner to select `[16385]` and the
remaining 34 members, with every original snapshot retained unchanged. Complete
ownership/dependency replay took 442 ms locally. This is fixture replay only: the
old production job did not emit this record, neither retry was dispatched by the
replay, and no passing remainder or production throughput benefit is claimed.

Five local one-finding replays measured origin collection at 0 ms each at the
driver's millisecond resolution. The Python validation/join averaged 0.109 ms over
100 calls, or 17.195 ms median including Python startup across ten subprocesses.
Whole replay medians were 1,835.770 ms before and 1,729.173 ms after; that difference
is timing noise, not a speedup claim. These are bounded one-finding measurements,
not a full-library performance benchmark. No second import or elaboration is added
to production diagnostics.

Run the safety regressions and a real Lean name/range smoke test:

```sh
python3 scripts/test_lint_env_locations.py
python3 scripts/test_build_lint_driver.py
python3 scripts/test_lint_scope.py
bash scripts/build-lint-driver.sh "$PWD" "$PWD/scripts/LintEnvDriver.lean" /tmp/lint-driver
python3 scripts/test_lint_env_driver.py "$PWD" /tmp/lint-driver/lint-env-driver
```

The smoke test creates a temporary fixture library and checks Unicode/escaped
names, real source positions and a private theorem's explicit unknown. Shell tests
execute the existing audit parser with controlled Lean process output, verifying
unchanged clean/baselined/ratchet/new-failure verdicts and nonce/forged-report
rejections. The bors companion adds actual Python-parser-to-Elixir mapper/planner
tests for immutable retry state, unknown/global findings, unchanged dependencies
and stale candidate/base/head-order/run-attempt bindings.

## Release

These are human-owned script/workflow changes and require human acceptance and
all required CI. After landing, a **new** ordinary production dispatch must pin
the new trusted reporter; a previously dispatched workflow cannot verify it.
The coordinator owns production dispatch and monitoring. Verify real collection
and a diagnostic partition when a natural failure occurs, followed by a fully
passing remainder. Do not manufacture a production failure. Keep #17037 open and
withhold `rollout-verified:` until acceptance and production verification finish.

The companion is backward-compatible with older logs (no locations means the
existing fallback). `BORS_FAILURE_DIAGNOSTICS=off` remains the existing consumer
rollback switch; the optional producer never changes the audit verdict.
