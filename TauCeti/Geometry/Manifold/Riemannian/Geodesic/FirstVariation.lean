/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Basic

/-!
# Geodesics are critical points of the energy

The first variation formula `TauCeti.Manifold.hasDerivAt_energy_of_fixed_endpoints` of
`TauCeti.Geometry.Manifold.Riemannian.FirstVariation` expresses the derivative at `s = 0` of the
energy of a fixed-endpoint variation `F` of `γ = F 0` as `-∫_a^b ⟪V(t), D_t γ'(t)⟫ dt`.  Along a
geodesic the covariant acceleration `D_t γ'` vanishes, so the derivative is zero: geodesics are
critical points of the energy among variations with fixed endpoints.  This is the "geodesic ⇒
critical" half of the variational characterization of geodesics.

## Main results

* `TauCeti.Manifold.IsGeodesicCurveOn.hasDerivAt_energy_zero`: **geodesics are critical
  points of the energy** among variations with fixed endpoints.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 9, §2, Proposition 2.4.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §12.
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

variable [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {F : ℝ → ℝ → M}

/-- **Geodesics are critical points of the energy.** If the central curve `γ = F 0` of a
variation whose curves near `s = 0` have fixed endpoints is a geodesic on an open set containing
`[a, b]`, the derivative at `s = 0` of the energy of `F s` vanishes. -/
theorem IsGeodesicCurveOn.hasDerivAt_energy_zero {a b : ℝ} {s : Set ℝ}
    (h : IsGeodesicCurveOn I (F 0) s) (hs : IsOpen s) (hsub : uIcc a b ⊆ s)
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (ha : ∀ᶠ s in 𝓝 0, F s a = F 0 a) (hb : ∀ᶠ s in 𝓝 0, F s b = F 0 b) :
    HasDerivAt (fun s ↦ energy I (F s) a b) 0 0 := by
  refine (hasDerivAt_energy_of_fixed_endpoints hF ha hb).congr_deriv ?_
  rw [neg_eq_zero]
  refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_).trans
    intervalIntegral.integral_zero
  simp only [((isGeodesicCurveOn_iff_of_isOpen hs).mp h).2 t (hsub ht), inner_zero_right]

end TauCeti.Manifold

end
