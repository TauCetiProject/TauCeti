/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.BasisChange
public import TauCeti.Algebra.Module.ZLattice.Family.HomeomorphProd

/-!
# Change of basis in a torus-family trivialization

The global trivializations of a continuous period family for two integral bases differ by the
fixed torus coordinate change from `Module.Basis.torusBasisChange`: the transition does not
depend on the parameter or on the periods.

The bases may have different finite index types. These are real, not holomorphic, coordinate
changes; no holomorphic isotriviality of the family is asserted.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Chapter 8 (families of complex tori given by period matrices).
-/

public section

open Module Module.Basis

namespace TauCeti

variable {Λ : Type*} [AddCommGroup Λ]
  {ι κ : Type*} [Fintype ι] [Fintype κ]
  {Y : Type*} [TopologicalSpace Y]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ) (hinj : ∀ y, Function.Injective (P y))

omit [TopologicalSpace Y] in
/-- The period coordinate change is the fixed integral change-of-basis matrix, independent of
both the parameter and the periods. -/
theorem torusBasisChangeLinearEquiv_periodBasis (y : Y) (v : E) :
    torusBasisChangeLinearEquiv b c ((periodBasis P b hinj y).equivFun v) =
      (periodBasis P c hinj y).equivFun v := by
  have h : (torusBasisChangeLinearEquiv b c).toLinearMap.comp
      (periodBasis P b hinj y).equivFun.toLinearMap =
        (periodBasis P c hinj y).equivFun.toLinearMap := by
    apply (periodBasis P b hinj y).ext
    intro i
    have hb : (periodBasis P b hinj y).equivFun (P y (b i)) =
        fun j ↦ (b.repr (b i) j : ℝ) := by ext j; simp
    have hc : (periodBasis P c hinj y).equivFun (P y (b i)) =
        fun j ↦ (c.repr (b i) j : ℝ) := by ext j; simp
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, periodBasis_apply, hb, hc] using
      torusBasisChangeLinearEquiv_intCast b c (b i)
  exact congrArg (fun f : E →ₗ[ℝ] (κ → ℝ) ↦ f v) h

/-- The global torus-family trivializations for two integral bases differ by the fixed
integral coordinate change on the standard torus factor. -/
theorem torusFamilyHomeomorphProd_basisChange (hcont : ∀ l, Continuous fun y ↦ P y l)
    (z : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    torusFamilyHomeomorphProd P c hinj hcont z =
      Prod.map id (torusBasisChange b c) (torusFamilyHomeomorphProd P b hinj hcont z) := by
  let _ := periodAddAction P
  induction z using Quotient.inductionOn with | h p =>
    simp only [torusFamilyHomeomorphProd_mk, Prod.map_apply, id_eq, torusBasisChange_mk]
    rw [torusBasisChangeLinearEquiv_periodBasis]

/-- In the two trivializations the transition homeomorphism is the identity on the base and
one fixed integral change of coordinates on the torus. -/
theorem torusFamilyHomeomorphProd_symm_trans (hcont : ∀ l, Continuous fun y ↦ P y l) :
    (torusFamilyHomeomorphProd P b hinj hcont).symm.trans
        (torusFamilyHomeomorphProd P c hinj hcont) =
      (Homeomorph.refl Y).prodCongr (torusBasisChange b c).toHomeomorph := by
  apply Homeomorph.ext
  intro z
  simpa [ContinuousAddEquiv.toHomeomorph_eq_coe, Homeomorph.coe_ofClass] using
    torusFamilyHomeomorphProd_basisChange P b c hinj hcont
    ((torusFamilyHomeomorphProd P b hinj hcont).symm z)

end TauCeti
