/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.PathELength
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal

/-!
# Path lengths under constant rescaling

Multiplying a Riemannian metric by a positive constant `c` multiplies the extended length of
each path by `√c`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2.
-/

public noncomputable section

open Bundle Manifold MeasureTheory
open scoped ENNReal ContDiff Manifold

namespace Bundle.ContMDiffRiemannianMetric

section Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) {c : ℝ} (hc : 0 < c)

/-- Multiplying a metric by a positive constant `c` multiplies the length of every path by
`√c`. -/
theorem pathELength_rescale_const (γ : ℝ → M) (a b : ℝ) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      pathELength I γ a b) =
      ENNReal.ofReal √c *
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
          pathELength I γ a b) := by
  let g' := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have h := pathELength_eq_lintegral_mfderiv_Icc (I := I) (γ := γ) (a := a) (b := b)
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩
  rw [pathELength_eq_lintegral_mfderiv_Icc, h, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_congr fun t ↦ g.enorm_rescale (fun _ ↦ c) contMDiff_const (fun _ ↦ hc) _ _

end Manifold

end Bundle.ContMDiffRiemannianMetric
