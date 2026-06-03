# Proxima Centauri

Let's do lots of maths.

Humans own the roadmap, which is written mostly in markdown and a small amount of Lean, and changes to the roadmap are made via human-reviewed pull requests.

AIs own the code, initiating pull requests and shepherding these pull requests through an AI-driven review process.

Humans can raise issues against the code, and leave implementation (and review) to AIs.

## Division of labour

| Path | Owner | Contents |
| --- | --- | --- |
| `Centauri/` | **AIs** | All the Lean mathematics. |
| `CentauriRoadmap/` | **humans** | Roadmaps in markdown, and sample Lean files where `sorry` is allowed. |
| `CentauriReview/` | **humans** | Review rubrics and (eventually) review bots. |
| `.github/`, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | **humans** | The rules of the game and the machinery that enforces them. |

This division is managed via the `CODEOWERS` file and branch protection rules.
The `main` branch is always green, and does not allow `sorry` or any axioms (including `native_decide`).

## Mathlib dependency

For now we depend on Mathlib's `master` branch. AIs are encouraged to make PRs that bump the pin to new commits on the `master` branch, and fix any resulting problems in the library.

From Proxima Centauri's point of view, Mathlib is a long way away, so we don't plan around close coordination: if you're missing something in Mathlib that you need, just build it here. (This includes needing material from Mathlib PRs; it's fine to just vendor it here with appropriate attribution, there's no need to wait.)

Conversely, we don't anticipate actively pushing material from Proxima Centauri to Mathlib, even though we aspire to review standards here that are even higher than those at Mathlib. Mathlib contributors are of course welcome to adopt, curate, and modify material from Proxima Centauri, and submit it to Mathlib themselves. Everything here is Apache licensed.

## Building

```bash
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build
```

## Roadmaps

Some initial example roadmaps live under `CentauriRoadmap/`:

1. [Universal covers](CentauriRoadmap/UniversalCovers/README.md)
2. [The Jacobian challenge](CentauriRoadmap/JacobianChallenge/README.md) 
3. [Reductive algebraic groups](CentauriRoadmap/ReductiveGroups/README.md) 
4. [Partial differential equations](CentauriRoadmap/PDE/README.md)
