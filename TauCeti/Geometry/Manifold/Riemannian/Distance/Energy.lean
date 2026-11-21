/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.ArcLength
public import TauCeti.Geometry.Manifold.Riemannian.Distance

/-!
# Distance controlled by curve energy

The distance between the endpoints of a `C¹` curve is at most the square root of twice its
energy times the length of the parameter interval. This combines the distance–length comparison
with the Cauchy–Schwarz bound for length and energy, and applies on every compact interval
contained in the curve's smoothness domain.

## Main results

* `TauCeti.IsRiemannianManifold.dist_le_sqrt_two_mul_energy`: the endpoint distance is bounded
  by `√(2 * (b - a) * energy I γ a b)` when `a ≤ b`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §12.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Bundle Set
open scoped Manifold

namespace TauCeti.IsRiemannianManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

/-- The endpoint distance of a `C¹` curve is at most the square root of twice its energy
times the length of the parameter interval. -/
theorem dist_le_sqrt_two_mul_energy {γ : ℝ → M} {s : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ s) :
    dist (γ a) (γ b) ≤ Real.sqrt (2 * (b - a) * Manifold.energy I γ a b) := by
  apply (edist_le_ofReal (Real.sqrt_nonneg _)).mp
  exact (edist_le_pathELength (hγ.mono hsub) hab).trans
    (hγ.pathELength_le_ofReal_sqrt_energy hsub)

end TauCeti.IsRiemannianManifold
