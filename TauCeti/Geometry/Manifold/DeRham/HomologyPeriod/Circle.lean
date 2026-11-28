/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.AddCircle
public import TauCeti.Geometry.Manifold.DeRham.HomologyPeriod

/-!
# Periods of closed one-forms on loops of the circle

A continuous loop `g : ℝ / ℤ → M` has the homology class `g_*[S¹] ∈ H₁(M; ℤ)`, the image of the
circuit class `AddCircle.fundamentalClass 1`. When the loop reads `s ↦ c s` on `[0, 1]` for a
`C¹` curve `c`, the period of a closed `C¹` one-form on this class is the line integral of the form
along `c` over one period
(`TauCeti.homologyPeriodHom_singularHomologyMap_fundamentalClass`). Since periods are defined on
homology classes, this is how line integrals of closed forms along freely homotopic loops, such as
the loops of a swept torus, are compared.

## Main results

* `TauCeti.homologyPeriodHom_singularHomologyMap_fundamentalClass`: the period on the class of a
  `C¹` loop of the circle is its line integral.

## References

* M. Farber, *Topology of Closed One-Forms*, Section 1.1 (the homomorphism of periods
  `H₁(M; ℤ) → ℝ`).
-/

public section

noncomputable section

open Set TauCeti.HurewiczOne
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} {M F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] [CompleteSpace F]
  {θ : RoughForm I M F 1}

/-- **The period on the class of a `C¹` loop is its line integral.** Let `g : S¹ → M` be a loop of
the circle `ℝ / ℤ` which reads `s ↦ c s` on `[0, 1]`, for a `C¹` curve `c`. The period of a
closed `C¹` one-form on the class `g_*[S¹]` is the line integral of the form along `c` over one
period. -/
theorem homologyPeriodHom_singularHomologyMap_fundamentalClass (hθ : IsSmoothForm I 1 θ)
    (hclosed : mextDeriv θ = 0) (g : C(UnitAddCircle, M)) {c : ℝ → M}
    (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) (hgc : ∀ s : unitInterval, g (s : ℝ) = c s) :
    homologyPeriodHom θ (ContinuousMap.singularHomologyMap ℤ 1 g (AddCircle.fundamentalClass 1)) =
      pathIntegral θ c 0 1 := by
  rw [AddCircle.fundamentalClass_def, ContinuousMap.singularHomologyMap_loopClass,
    homologyPeriodHom_loopClass]
  refine pathClassIntegral_mk_eq_pathIntegral hθ hclosed hc fun t ↦ ?_
  rw [Path.map_coe, Function.comp_apply, AddCircle.zsmulLoop_apply]
  simp [hgc]

end TauCeti
