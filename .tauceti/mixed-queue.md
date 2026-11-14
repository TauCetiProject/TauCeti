# Optional mixed-source candidate CI

`source-candidate.yml` receives only the exact source-candidate event and remains
inert until `TAUCETI_MIXED_QUEUE_CI_ENABLED` is explicitly set to `true`. This does
not change normal PR/Bors CI, the root `tauceti.toml`, worker defaults, queue
admissions, primary authority or the current main mirror.

The caller pins the shared harness and its independent source policy. The
separate `ci-source.toml` selects Forgejo for immutable candidate retention and
GitHub for execution; the ordinary project configuration keeps its existing
GitHub source. Qualified accepted members can originate on either enrolled host.
CI credentials read retained native objects only. Candidate code still executes
under the existing sandbox, audits, scope/dependency gates and cache protocol.

Before enabling, merge the shared Tools prerequisite, deploy the matching queue
and repair runner, verify the repository IDs and immutable pins, configure a
read-only native retention credential as `CI_SOURCE_READ_TOKEN`, and confirm the
existing trusted cache publication secret. Give the queue execution App its
separately scoped GitHub role. Copy the exact source configuration/policy bytes
from the merged caller to enroll the private queue profile. New requests select
the current protected execution main and freeze its caller, policy and
configuration together; normal control updates need no extra caller approval.
Keep native source access configured when pausing new Forgejo intake with
`forgejo_admission_enabled = false`. Run observation first, then explicitly enable hosted CI and
mixed admission for a supervised canary. Queue setup and primary changes are
covered in Worker `docs/queue/mixed-sources.md`.

Ordinary native scoreboards are not trusted admission receipts. Use the current
native publisher protocol; automatic trusted Review publication remains Stage 2.
Native main, source publication, GitHub execution and GitHub follower writes have
separate credentials. Do not grant a candidate or repair sandbox those roles.
