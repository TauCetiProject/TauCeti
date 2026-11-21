/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.Period
public import TauCeti.Geometry.Manifold.DeRham.Circle
public import TauCeti.Geometry.Manifold.Instances.Sphere

import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic
import TauCeti.Geometry.Manifold.DeRham.HomologyPeriod

/-!
# The period of the angular form on the standard loop of the circle

The standard loop `t ↦ exp (2π i t)` of the circle, read as a smooth singular `1`-simplex
(`TauCeti.circleLoopSimplex`), is an integral smooth singular `1`-cycle: its two faces are the same
vertex. Its class `TauCeti.circleLoopClass ∈ H₁^sm(S¹; ℤ)` pairs with the de Rham class of the
angular form `dθ` to `2π`
(`TauCeti.deRhamCohomology.smoothHomologyPeriod_mk_circleAngularClosedForm_circleLoopClass`), so the
pairing `TauCeti.deRhamCohomology.smoothHomologyPeriod` of de Rham cohomology with integral smooth
singular homology is not trivial. Consequently, the inclusion of smooth singular chains into
continuous singular chains induces a nonzero map on `H₁(S¹; ℤ)`
(`TauCeti.homologyMap_smoothSingularSubcomplex_ι_circle_int_ne_zero`).

## Main definitions

* `TauCeti.circleLoopSimplex`, `TauCeti.circleLoopClass`: the standard loop of the circle as a
  smooth singular `1`-simplex and its class in `H₁^sm(S¹; ℤ)`.

## Main results

* `TauCeti.d_ιChainComplex_circleLoopSimplex`: the standard loop is a cycle.
* `TauCeti.deRhamCohomology.smoothHomologyPeriod_mk_circleAngularClosedForm_circleLoopClass`: the
  period of `dθ` on the standard loop of the circle is `2π`.
* `TauCeti.homologyMap_smoothSingularSubcomplex_ι_circle_int_ne_zero`: the inclusion of smooth
  singular chains into continuous singular chains is nonzero on `H₁(S¹; ℤ)`.
-/

public section

noncomputable section

open CategoryTheory
open scoped Manifold ContDiff

namespace TauCeti

/-- The standard loop `t ↦ exp (2π i t)` of the circle, as a smooth singular `1`-simplex. -/
def circleLoopSimplex : SmoothSimplex (𝓡 1) Circle 1 :=
  SmoothSimplex.ofCurve contMDiff_circleExp_two_pi_mul

/-- The standard loop of the circle is the smooth `1`-simplex of the curve `t ↦ exp (2π i t)`. -/
theorem circleLoopSimplex_eq_ofCurve :
    circleLoopSimplex = SmoothSimplex.ofCurve contMDiff_circleExp_two_pi_mul :=
  (rfl)

/-- Read on `Δ¹`, the standard loop of the circle evaluates `t ↦ exp (2π i t)` at the unique
coordinate. -/
@[simp]
theorem toContinuousMap_circleLoopSimplex_apply (x : fullSimplex 1) :
    circleLoopSimplex.toContinuousMap x = Circle.exp (2 * Real.pi * x.val 0) :=
  SmoothSimplex.toContinuousMap_ofCurve_apply _ x

/-- The standard loop of the circle is an integral smooth singular `1`-cycle: its two faces are
the same vertex `1`. -/
theorem d_ιChainComplex_circleLoopSimplex :
    (((smoothSingularSubcomplex (𝓡 1) Circle : SSet).chainComplex (ModuleCat.of ℤ ℤ)).d 1 0).hom
      (((smoothSingularSubcomplex (𝓡 1) Circle : SSet).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) circleLoopSimplex).hom 1) = 0 := by
  rw [← ConcreteCategory.comp_apply, SSet.ιChainComplex_d]
  simp [Fin.sum_univ_two, circleLoopSimplex_eq_ofCurve]

/-- The homology class in `H₁^sm(S¹; ℤ)` of the standard loop `t ↦ exp (2π i t)`. -/
def circleLoopClass :
    ((smoothSingularSubcomplex (𝓡 1) Circle : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homology 1 :=
  (((smoothSingularSubcomplex (𝓡 1) Circle : SSet).chainComplex (ModuleCat.of ℤ ℤ)).homologyπ 1).hom
    (((smoothSingularSubcomplex (𝓡 1) Circle : SSet).chainComplex
      (ModuleCat.of ℤ ℤ)).moduleCatCyclesMk _ 0 (ChainComplex.next_nat_succ 0)
        d_ιChainComplex_circleLoopSimplex)

/-- The class of the standard loop of the circle is the homology class of the cycle
`circleLoopSimplex`. -/
theorem circleLoopClass_eq_homologyπ :
    circleLoopClass =
      (((smoothSingularSubcomplex (𝓡 1) Circle : SSet).chainComplex
        (ModuleCat.of ℤ ℤ)).homologyπ 1).hom
        (((smoothSingularSubcomplex (𝓡 1) Circle : SSet).chainComplex
          (ModuleCat.of ℤ ℤ)).moduleCatCyclesMk _ 0 (ChainComplex.next_nat_succ 0)
            d_ιChainComplex_circleLoopSimplex) :=
  (rfl)

/-- **The period of `dθ` on the standard loop of the circle is `2π`.** In particular the pairing
of de Rham cohomology with integral smooth singular homology is nonzero on the circle. -/
theorem deRhamCohomology.smoothHomologyPeriod_mk_circleAngularClosedForm_circleLoopClass :
    deRhamCohomology.smoothHomologyPeriod (deRhamCohomology.mk (𝓡 1) 1 circleAngularClosedForm)
      circleLoopClass = 2 * Real.pi := by
  -- reparametrising `t ↦ exp (2π i t)` on `[0, 1]` as `Circle.exp` on `[0, 2π]`
  have h := pathIntegral_comp_mul_add (isSmoothForm_circleAngularForm.of_le (by simp))
    (contMDiff_circleExp (m := 1)) (2 * Real.pi) 0 0 1
  rw [circleLoopClass_eq_homologyπ, deRhamCohomology.smoothHomologyPeriod_mk,
    LinearMap.toAddMonoidHom_coe, smoothHomologyPeriodHom_homologyπ
      (circleAngularClosedForm.val.isSmoothForm.of_le (by simp))
      ((mem_closedForms _ _).mp circleAngularClosedForm.property),
    HomologicalComplex.iCycles_moduleCatCyclesMk, integrationCochain_ιChainComplex]
  simpa [circleLoopSimplex_eq_ofCurve, SmoothSimplex.integral_ofCurve,
    pathIntegral_circleAngularForm_circleExp] using h

/-- The integral of `circleAngularForm` along the continuous path of `circleLoopSimplex` is
`2π`. -/
private theorem pathClassIntegral_circleAngularForm_circleLoopSimplex :
    pathClassIntegral circleAngularForm (.mk (TauCeti.TopCat.path₁ circleLoopSimplex.val)) =
      2 * Real.pi := by
  have hclosed : mextDeriv circleAngularForm = 0 := by
    simpa [coe_circleAngularClosedForm] using
      (mem_closedForms (𝓡 1) circleAngularClosedForm.val).mp circleAngularClosedForm.property
  rw [circleLoopSimplex_eq_ofCurve, SmoothSimplex.coe_ofCurve,
    pathClassIntegral_mk_eq_pathIntegral (isSmoothForm_circleAngularForm.of_le (by norm_num))
      hclosed (contMDiff_circleExp_two_pi_mul.of_le (by norm_num))
      (fun t ↦ TauCeti.TopCat.path₁_simplex₁_apply _ t)]
  have hchg := pathIntegral_comp_mul_add (isSmoothForm_circleAngularForm.of_le zero_le)
    (contMDiff_circleExp (m := 1)) (2 * Real.pi) 0 0 1
  simp only [add_zero, mul_zero, mul_one, pathIntegral_circleAngularForm_circleExp, sub_zero]
    at hchg
  exact hchg

/-- On `Circle`, the inclusion of smooth singular chains into continuous singular chains is nonzero
on `H₁(Circle; ℤ)`: the class of `circleLoopSimplex` has period `2π ≠ 0` under
`homologyPeriodHom circleAngularForm`. -/
theorem homologyMap_smoothSingularSubcomplex_ι_circle_int_ne_zero :
    SSet.homologyMap (smoothSingularSubcomplex (𝓡 1) Circle).ι (ModuleCat.of ℤ ℤ) 1 ≠ 0 := by
  intro hzero
  let K := (smoothSingularSubcomplex (𝓡 1) Circle : SSet).chainComplex (ModuleCat.of ℤ ℤ)
  let φ := SSet.chainComplexMap (smoothSingularSubcomplex (𝓡 1) Circle).ι (ModuleCat.of ℤ ℤ)
  let zK : K.cycles 1 := K.moduleCatCyclesMk _ 0 (ChainComplex.next_nat_succ 0)
    d_ιChainComplex_circleLoopSimplex
  let w := HomologicalComplex.cyclesMap φ 1 zK
  have himg := ConcreteCategory.congr_hom hzero (K.homologyπ 1 zK)
  rw [← ModuleCat.comp_apply, SSet.homologyπ_homologyMap, ModuleCat.comp_apply] at himg
  have hper :
      chainsDesc
        (fun s ↦ pathClassIntegral circleAngularForm (.mk (TauCeti.TopCat.path₁ s)))
        ((((singularChains ℤ).obj (.of Circle)).iCycles 1).hom w) = 0 :=
    (homologyPeriodHom_homologyπ (φ := circleAngularForm) w).symm.trans
      ((congrArg (homologyPeriodHom circleAngularForm) himg).trans (map_zero _))
  have hi : (((singularChains ℤ).obj (.of Circle)).iCycles 1).hom w =
      simplexChain circleLoopSimplex.val (1 : ℤ) :=
    (K.moduleCat_iCycles_cyclesMap_apply 1 φ zK).trans
      ((congrArg (φ.f 1) (K.iCycles_moduleCatCyclesMk 1 _ 0 (ChainComplex.next_nat_succ 0)
        d_ιChainComplex_circleLoopSimplex)).trans
        (ConcreteCategory.congr_hom
          (SSet.ι_chainComplexMap_f _ _ (smoothSingularSubcomplex (𝓡 1) Circle).ι
            (ModuleCat.of ℤ ℤ) circleLoopSimplex) (1 : ℤ)))
  rw [hi, chainsDesc_simplexChain_one,
    pathClassIntegral_circleAngularForm_circleLoopSimplex] at hper
  linarith [Real.pi_pos]

end TauCeti
