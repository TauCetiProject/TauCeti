# Official dependency warming

`warm-dependencies.yml` runs from immutable main-defined tooling, independently of
TauCeti compilation. A pin-changing PR is read as Git blobs: only ordinary config
files are materialized, the lakefile must equal current main, and the existing
`check-bump.sh` must accept the pins before any Lake/dependency code runs. Candidate
Lean files and scripts are never checked out into the warm project.

The producer installs the pinned official Lean release and downloads Mathlib's
official cache with the validated config. It saves an exact-pin toolchain snapshot
and the existing `mathlib-ltar-v1` compressed-download snapshot. Main CI also saves
Mathlib downloads before TauCeti compiles. Staging restores toolchains only after
attestation/bump validation; it has no snapshot save step. Toolchain provenance
records the main workflow commit, run, pin, file hashes, modes and internal symlinks.
Hashes detect corruption; the isolated official-release producer supplies trust.

GitHub cache snapshots are immutable. Simultaneous writers may race to reserve
one exact key; losing a reservation is harmless. Every consumer restores into its
own ephemeral runner directory. No persistent cache volume is mounted into the
candidate sandbox. Elan/toolchains are read-only there; Mathlib's compressed store
is absent, and only the candidate `.lake` is writable. No R2 publisher credentials
are available to the warmer or candidate. Ordinary PR compiled outputs never enter
these stores. Existing audited-main/batch publication and eligible-parent Lake
restore remain unchanged; the warmer also checks parent availability anonymously.

Toolchain snapshots have no prefix fallback. Missing, failed or corrupt restores
are discarded and replaced with an official release installation. A corrupt
immutable key continues to take the fresh-install path; retire it by changing the
`official-lean-v1` generation in the restore action after human review. Mathlib
keeps its existing `cache get!` refetch fallback. The warmer refuses partial Mathlib
cache availability and publishes no Mathlib snapshot after a failed fetch.

## Verification

To verify a change to workflow-pinned tooling, dispatch new runs on main.
Rerunning an earlier run uses its earlier workflow definition:

```sh
gh workflow run warm-dependencies.yml --repo TauCetiProject/TauCeti --ref main -F cold=true
gh workflow run warm-dependencies.yml --repo TauCetiProject/TauCeti --ref main -F capacity=true
gh workflow run warm-dependencies.yml --repo TauCetiProject/TauCeti --ref main -f pr=VALIDATED_BUMP_PR
gh workflow run pr-build.yml --repo TauCetiProject/TauCeti --ref main -f pr=SOURCE_PR
```

Use run/jobs APIs for exact state and timings. Start one
`gh run watch RUN_ID --repo TauCetiProject/TauCeti --exit-status --interval 120`
monitor per run. Confirm cold then warm restoration, complete official Mathlib
downloads, eligible-parent availability/fallback, and the synthetic sandbox canary.
The probe replicates the read-only elan mount, absent Mathlib store, offline network
and disabled nested user namespaces. It invokes its own bwrap policy rather than
pr-build.yml's actual sandbox command. The
capacity dispatch requests three independent jobs on the existing 8-vCPU/16-GB
Namespace staging shape, records CPU/memory and holds the consumers for 60 seconds
to expose overlapping availability. It tests dependency setup and the synthetic sandbox on
three runners; it does not certify performance of three full-library compilations.
Use their job start/finish intervals and distinct runner IDs to assess capacity.
The normal warm run requests one runner. No speculative bors merges are enabled.

After a fresh source PR build, inspect the toolchain restore/verification and full
build/audit results, including the actual staging sandbox. Dependency priming cannot
remove necessary cold TauCeti source compilation after a Mathlib/toolchain change.
