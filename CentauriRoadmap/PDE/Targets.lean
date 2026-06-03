import Mathlib

/-!
# Partial differential equations — target signatures

The narrative roadmap, the build lanes (A–F), and the acceptance criteria are in
`README.md`. Mathlib already carries a substantial prerequisite stack — distributions and
test functions, the Schwartz space, the Fourier transform, convolution and mollifiers,
the Gagliardo–Nirenberg–Sobolev inequality, the **Bessel-potential** Sobolev scale
(`TemperedDistribution.memSobolev`), the Laplacian and harmonic-function theory,
**Lax–Milgram** (`InnerProductSpace.continuousLinearEquivOfBilin`), the **Fredholm
alternative** for compact operators, and the spectral theorem for symmetric operators.

What is missing is the PDE theory on top: weak-derivative Sobolev spaces `W^{k,p}(Ω)` on
a domain with their embedding/trace/compactness package (Lane A), the harmonic-analysis
estimates (Lane B), maximum principles and potential theory (Lane C), elliptic existence
via the energy method (Lane D), elliptic regularity — Schauder and De Giorgi–Nash–Moser
(Lane E), and parabolic/evolution equations (Lane F). We build these here, in
`Centauri/Analysis/PDE/`, with supporting theories under `Centauri/Analysis/Sobolev/` and
`Centauri/Analysis/HarmonicAnalysis/`.

As each lane makes the next lane's *types* expressible in `Centauri/`, state that lane's
milestones here with `sorry` (human-owned roadmap territory, so `sorry` is allowed) and
hand them to the AIs to discharge. The natural first targets, in order:

* Lane A: `Wkp k p Ω` (weak-derivative Sobolev space) is complete; Meyers–Serrin `H = W`;
  Poincaré on `Wkp0 1 p Ω`; Rellich–Kondrachov compactness `W^{1,p}(Ω) ↪↪ L^p(Ω)`.
* Lane D: existence and uniqueness of the weak solution of `−Δu = f`, `u|∂Ω = 0`, on a
  bounded domain, via `IsCoercive` + `continuousLinearEquivOfBilin` (Lax–Milgram).
* Lane E: De Giorgi–Nash–Moser — a weak `H¹` solution of a divergence-form equation with
  bounded measurable coefficients is locally Hölder continuous.

The first end-to-end milestone (Lane D.17) is the shortest path to a genuine PDE existence
theorem, because Lax–Milgram is already in Mathlib; it only awaits `Wkp0` and Poincaré
from Lane A.
-/

namespace CentauriRoadmap.PDE

-- (no compiled targets yet; see README.md)

end CentauriRoadmap.PDE
