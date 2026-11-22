/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Sphere
public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.FubiniStudySphere
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Sphere.Hurewicz
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Tangent.Chern
public import TauCeti.Geometry.Symplectic.Floer.Cap.Action
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chern.Hurewicz

/-!
# The period group of the Riemann sphere with its Fubini–Study form

Capped Hamiltonian Floer theory on a symplectic manifold `(M, σ)` takes its coefficients over the
period group `Γ = TauCeti.Floer.SphericalPeriodGroup ω c` of homomorphisms `ω` and `c` on
`H₂(M; ℤ)`, the symplectic area and the first Chern number. This file computes them, and `Γ`,
for the Riemann sphere `OnePoint ℂ` with its Fubini–Study form `ω_FS`
(`OnePoint.fubiniStudyForm`): both homomorphisms come from the actual form, the area from the
integral of `ω_FS` (`TauCeti.homologySphereIntegralHom`) and the first Chern number from the
clutching number of the tangent bundle with an almost complex structure tamed by `ω_FS`
(`TauCeti.SmoothTwoForm.IsNondegenerate.homologyFirstChernHom`). Both are defined on `H₂` because
the Riemann sphere is simply connected.

* **The periods of the standard sphere.** On the Hurewicz class of the standard sphere
  `TauCeti.riemannSphereSquare` the area is `1`
  (`OnePoint.homologySphereIntegralHom_fubiniStudyForm_hurewiczIntHom_riemannSphereSquare`, from
  `OnePoint.sphereIntegral_fubiniStudyForm_riemannSphereSquare`) and the first Chern number is `2`
  (`OnePoint.homologyFirstChernHom_fubiniStudyForm_hurewiczIntHom_riemannSphereSquare`, from
  `OnePoint.firstChernHom_fubiniStudyForm_apply_mk_riemannSphereSquare`).
* **Monotonicity.** The group `H₂(OnePoint ℂ; ℤ)` is cyclic, being the image of the top homology
  of the round sphere under the stereographic homeomorphism (`onePointEquivSphereOfFinrankEq`), and
  two homomorphisms on a cyclic group are proportional. So the two values above give
  `ω_FS(A) = c₁(A) / 2` on every class `A`
  (`OnePoint.homologySphereIntegralHom_fubiniStudyForm_eq_inv_two_mul`): the Riemann sphere with
  `ω_FS` is spherically monotone with monotonicity constant `1/2`. This holds without knowing which
  class generates `H₂`.
* **The period group.** Consequently, on `Γ` both the area and the first Chern number are
  injective (`TauCeti.Floer.SphericalPeriodGroup.area_injective_fubiniStudyForm`,
  `TauCeti.Floer.SphericalPeriodGroup.chern_injective_fubiniStudyForm`), with area half the Chern
  number (`TauCeti.Floer.SphericalPeriodGroup.area_eq_inv_two_mul_chern_fubiniStudyForm`). So
  recapping changes the action by half the change in Chern number, and a recapping is determined
  by either. In particular, for every time-dependent Hamiltonian the capped action is injective on
  the cap classes of every loop with a smooth based cap
  (`TauCeti.Floer.SphericalCapClass.action_injective_fubiniStudyForm`).

These are the coefficient data of capped Floer theory on `CP¹` for the actual symplectic form and
the actual first Chern number. The computations for arbitrary homomorphisms `ω` and `c` on the round
sphere are in `TauCeti.Geometry.Symplectic.Floer.Examples.Sphere`.

## Main results

* `OnePoint.homologySphereIntegralHom_fubiniStudyForm_eq_inv_two_mul`: the area of the Fubini–Study
  form is half the first Chern number on `H₂(OnePoint ℂ; ℤ)`.
* `TauCeti.Floer.SphericalPeriodGroup.area_injective_fubiniStudyForm`,
  `TauCeti.Floer.SphericalPeriodGroup.chern_injective_fubiniStudyForm`: area and first Chern
  number are injective on the period group.
* `TauCeti.Floer.SphericalCapClass.action_injective_fubiniStudyForm`: a cap class is determined by
  its capped action.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Section 11.1 (the Novikov ring and the quantum cohomology of `CP¹`).
-/

public section

noncomputable section

open AlgebraicTopology HomotopyGroup Metric TauCeti
open scoped Manifold Topology Topology.Homotopy TauCeti.ComplexManifold

/-- The integral of the Fubini–Study form on `H₂(OnePoint ℂ; ℤ)`. -/
local notation "ω_FS" =>
  homologySphereIntegralHom OnePoint.isSmoothForm_fubiniStudyForm
    OnePoint.mextDeriv_fubiniStudyForm

/-- The first Chern number of the Fubini–Study form on `H₂(OnePoint ℂ; ℤ)`. -/
local notation "c₁_FS" =>
  OnePoint.isSymplectic_fubiniStudyForm.isNondegenerate.homologyFirstChernHom

namespace OnePoint

/-- The Hurewicz class of the standard sphere `TauCeti.riemannSphereSquare`. -/
local notation "standardSphere" =>
  hurewiczIntHom (OnePoint ℂ) ∞ 1
    (Additive.ofMul (Quotient.mk _ TauCeti.riemannSphereSquare) :
      Additive (π_ 2 (OnePoint ℂ) ∞))

/-- **The Fubini–Study area of the standard sphere is `1`** on `H₂(OnePoint ℂ; ℤ)`. -/
theorem homologySphereIntegralHom_fubiniStudyForm_hurewiczIntHom_riemannSphereSquare :
    ω_FS standardSphere = 1 := by
  rw [homologySphereIntegralHom_hurewiczIntHom, sphereIntegralHom_apply]
  exact sphereIntegral_fubiniStudyForm_riemannSphereSquare

/-- **The first Chern number of the Fubini–Study form on the standard sphere is `2`** on
`H₂(OnePoint ℂ; ℤ)`. -/
theorem homologyFirstChernHom_fubiniStudyForm_hurewiczIntHom_riemannSphereSquare :
    c₁_FS standardSphere = 2 := by
  rw [SmoothTwoForm.IsNondegenerate.homologyFirstChernHom_hurewiczIntHom,
    firstChernHom_fubiniStudyForm_apply_mk_riemannSphereSquare]

/-- **The Riemann sphere is spherically monotone with constant `1/2`.** For the Fubini–Study form,
the symplectic area of every class of `H₂(OnePoint ℂ; ℤ)` is half its first Chern number. -/
theorem homologySphereIntegralHom_fubiniStudyForm_eq_inv_two_mul
    (A : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (OnePoint ℂ))) :
    ω_FS A = 2⁻¹ * c₁_FS A := by
  -- `H₂(OnePoint ℂ; ℤ)` is cyclic: it is the image of the top homology of the round two-sphere,
  -- generated by the Hurewicz class of its tautological loop, under the stereographic
  -- homeomorphism.
  let e := ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).mapIso
    (TopCat.isoOfHomeo (X := TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
      (Y := TopCat.of (OnePoint ℂ)) (onePointEquivSphereOfFinrankEq (V := ℂ)
      (ι := Fin 3) (by simp)).symm)
  set g := e.hom.hom ((GenLoop.hurewicz (ModuleCat.of ℤ ℤ) (sphereGenLoop 2)).hom 1)
  have hg : AddSubgroup.zmultiples g = ⊤ := by
    refine (AddSubgroup.eq_top_iff' _).2 fun b ↦ ?_
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1
      ((AddSubgroup.eq_top_iff' _).1 (zmultiples_hurewicz_sphereGenLoop (n := 1)) (e.inv.hom b))
    refine AddSubgroup.mem_zmultiples_iff.2 ⟨k, ?_⟩
    rw [← map_zsmul, hk, ← ModuleCat.comp_apply, e.inv_hom_id, ModuleCat.id_apply]
  -- Write `A` and the standard sphere as multiples `m • g` and `k • g` of the generator `g`.
  obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 ((AddSubgroup.eq_top_iff' _).1 hg A)
  obtain ⟨k, hk⟩ :=
    AddSubgroup.mem_zmultiples_iff.1 ((AddSubgroup.eq_top_iff' _).1 hg standardSphere)
  have harea := homologySphereIntegralHom_fubiniStudyForm_hurewiczIntHom_riemannSphereSquare
  have hchern : (c₁_FS standardSphere : ℝ) = 2 := by
    exact_mod_cast homologyFirstChernHom_fubiniStudyForm_hurewiczIntHom_riemannSphereSquare
  rw [← hk, map_zsmul, zsmul_eq_mul] at harea hchern
  push_cast at hchern
  rw [map_zsmul, map_zsmul, zsmul_eq_mul, zsmul_eq_mul]
  push_cast
  -- From `k ω(g) = 1` and `k c₁(g) = 2` we get `c₁(g) = 2 ω(g)`.
  have hk0 : (k : ℝ) ≠ 0 := left_ne_zero_of_mul_eq_one harea
  have hg2 : (c₁_FS g : ℝ) = 2 * ω_FS g :=
    mul_left_cancel₀ hk0 (by linear_combination hchern - 2 * harea)
  rw [hg2]
  ring

end OnePoint

namespace TauCeti.Floer

namespace SphericalPeriodGroup

/-- **On the period group of the Riemann sphere, area is half the first Chern number**, for the
Fubini–Study form and its first Chern number. -/
theorem area_eq_inv_two_mul_chern_fubiniStudyForm (γ : SphericalPeriodGroup ω_FS c₁_FS) :
    PeriodGroup.area _ _ γ = 2⁻¹ * PeriodGroup.chern _ _ γ := by
  have h : ∀ s : sphericalClasses (OnePoint ℂ) 1,
      AddMonoidHom.comp ω_FS (sphericalClasses _ 1).subtype s =
        2⁻¹ * (AddMonoidHom.comp c₁_FS (sphericalClasses _ 1).subtype s : ℝ) :=
    fun s ↦ OnePoint.homologySphereIntegralHom_fubiniStudyForm_eq_inv_two_mul s
  exact PeriodGroup.area_eq_mul_chern h γ

/-- **On the period group of the Riemann sphere, the first Chern number is injective**, for the
Fubini–Study form: a class of the period group is determined by its first Chern number. -/
theorem chern_injective_fubiniStudyForm :
    Function.Injective (PeriodGroup.chern _ _ : SphericalPeriodGroup ω_FS c₁_FS →+ ℤ) :=
  fun γ γ' h ↦ PeriodGroup.ext (by
    rw [area_eq_inv_two_mul_chern_fubiniStudyForm, area_eq_inv_two_mul_chern_fubiniStudyForm, h]) h

/-- **On the period group of the Riemann sphere, area is injective**, for the Fubini–Study form: a
class of the period group is determined by its area. -/
theorem area_injective_fubiniStudyForm :
    Function.Injective (PeriodGroup.area _ _ : SphericalPeriodGroup ω_FS c₁_FS →+ ℝ) :=
  fun γ γ' h ↦ chern_injective_fubiniStudyForm <| by
    have := h
    rw [area_eq_inv_two_mul_chern_fubiniStudyForm,
      area_eq_inv_two_mul_chern_fubiniStudyForm] at this
    exact_mod_cast mul_left_cancel₀ (by norm_num) this

end SphericalPeriodGroup

namespace SphericalCapClass

variable {x : OnePoint ℂ} {γ : Ω (OnePoint ℂ) x}

/-- **On the Riemann sphere a cap class is determined by its action.** For the Fubini–Study form,
its first Chern number and any time-dependent Hamiltonian, the capped action is injective on the
cap classes of a loop with a smooth based cap. -/
theorem action_injective_fubiniStudyForm (Ham : ℝ → OnePoint ℂ → ℝ)
    (h : ∃ u, IsSmoothBasedCap 𝓘(ℝ, ℂ) γ u) :
    Function.Injective (action (c := c₁_FS) OnePoint.isSmoothForm_fubiniStudyForm
      OnePoint.mextDeriv_fubiniStudyForm (homologySphereIntegralHom_hurewiczIntHom _ _ x) Ham
      h) :=
  action_injective _ Ham h SphericalPeriodGroup.area_injective_fubiniStudyForm

end SphericalCapClass

end TauCeti.Floer
