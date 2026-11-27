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
circuit class `AddCircle.fundamentalClass 1`. When the loop reads `s ↦ c s` on the real line for a
`C¹` curve `c`, the period of a closed `C¹` one-form on this class is the line integral of the form
along `c` over one period
(`TauCeti.homologyPeriodHom_singularHomologyMap_fundamentalClass`).

For a continuous family of loops `G(·, t)`, `t ∈ [0, 1]`, the loops are freely homotopic through the
family, so they have the same class in `H₁(M; ℤ)`, and a closed form has the same line integral
along all of them (`TauCeti.pathIntegral_eq_pathIntegral_of_loopFamily`). This is how line integrals
of closed forms along the loops of a swept torus are compared.

## Main results

* `TauCeti.homologyPeriodHom_singularHomologyMap_fundamentalClass`: the period on the class of a
  `C¹` loop of the circle is its line integral.
* `TauCeti.pathIntegral_eq_pathIntegral_of_loopFamily`: a closed form has the same line integral
  along all the loops of a continuous family of `C¹` loops.

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
the circle `ℝ / ℤ` which reads `s ↦ c s` on the real line, for a `C¹` curve `c`. The period of a
closed `C¹` one-form on the class `g_*[S¹]` is the line integral of the form along `c` over one
period. -/
theorem homologyPeriodHom_singularHomologyMap_fundamentalClass (hθ : IsSmoothForm I 1 θ)
    (hclosed : mextDeriv θ = 0) (g : C(UnitAddCircle, M)) {c : ℝ → M}
    (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) (hgc : ∀ s : ℝ, g s = c s) :
    homologyPeriodHom θ (ContinuousMap.singularHomologyMap ℤ 1 g (AddCircle.fundamentalClass 1)) =
      pathIntegral θ c 0 1 := by
  rw [AddCircle.fundamentalClass_def, ContinuousMap.singularHomologyMap_loopClass,
    homologyPeriodHom_loopClass]
  refine pathClassIntegral_mk_eq_pathIntegral hθ hclosed hc fun t ↦ ?_
  rw [Path.map_coe, Function.comp_apply, AddCircle.zsmulLoop_apply, one_smul, mul_one,
    QuotientAddGroup.mk_zero, add_zero, hgc]

/-- **A closed form has the same line integral along every loop of a family.** Let
`G : S¹ × [0, 1] → M` be a continuous family of loops `G(·, t)` of the circle `ℝ / ℤ`, which reads
`(s, t) ↦ u(s, t)` on the real line, with `C¹` loops `s ↦ u(s, t)`. The loops are freely homotopic
through the family, so a closed `C¹` one-form has the same line integral over one period along all
of them. -/
theorem pathIntegral_eq_pathIntegral_of_loopFamily (hθ : IsSmoothForm I 1 θ)
    (hclosed : mextDeriv θ = 0) (G : C(UnitAddCircle × unitInterval, M)) {u : ℝ × ℝ → M}
    (hu : ∀ t : unitInterval, ContMDiff 𝓘(ℝ, ℝ) I 1 fun s ↦ u (s, t))
    (hGu : ∀ (s : ℝ) (t : unitInterval), G (s, t) = u (s, t)) (t t' : unitInterval) :
    pathIntegral θ (fun s ↦ u (s, t)) 0 1 = pathIntegral θ (fun s ↦ u (s, t')) 0 1 := by
  -- The loop of the family at the time `r`.
  let g : unitInterval → C(UnitAddCircle, M) := fun r ↦
    G.comp ((ContinuousMap.id _).prodMk (.const _ r))
  -- The loops at the times `t` and `t'` are homotopic along a path from `t` to `t'`.
  have : PathConnectedSpace unitInterval :=
    (projIcc_surjective (zero_le_one : (0 : ℝ) ≤ 1)).pathConnectedSpace continuous_projIcc
  let γ : Path t t' := PathConnectedSpace.somePath t t'
  let K : (g t).Homotopy (g t') :=
    { toFun := fun p ↦ G (p.2, γ p.1)
      continuous_toFun := by fun_prop
      map_zero_left := fun s ↦ by simp [g]
      map_one_left := fun s ↦ by simp [g] }
  rw [← homologyPeriodHom_singularHomologyMap_fundamentalClass hθ hclosed (g t) (hu t)
      fun s ↦ hGu s t,
    ← homologyPeriodHom_singularHomologyMap_fundamentalClass hθ hclosed (g t') (hu t')
      fun s ↦ hGu s t',
    ContinuousMap.singularHomologyMap_eq_of_homotopic ℤ 1 ⟨K⟩]

end TauCeti
