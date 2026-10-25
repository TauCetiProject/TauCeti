/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.HomeomorphProd
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.Topology.Homeomorph.Quotient
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Change of basis in a torus-family trivialization

Two integral bases of the same lattice give real coordinate systems related by the integral
change-of-basis matrix. This matrix descends to a homeomorphism of the standard real tori,
with inverse given by the reverse change of basis. The global trivializations of a continuous
period family differ by this fixed homeomorphism on the torus factor: the transition does not
depend on the parameter or on the periods.

The bases may have different finite index types. The coordinate change and its quotient satisfy
identity and composition laws. These are real, not holomorphic, coordinate changes; no
holomorphic isotriviality of the family is asserted.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Chapter 8 (families of complex tori given by period matrices).
-/

public section

open Module Set Submodule
open scoped Matrix

namespace TauCeti

variable {Λ : Type*} [AddCommGroup Λ]
  {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]

/-- The real extension of the integral coordinate change from `b` to `c`. Its matrix has
entries `c.repr (b i) j`, so it depends only on the two integral bases. -/
noncomputable def torusBasisChangeLinearEquiv (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ) :
    (ι → ℝ) ≃ₗ[ℝ] (κ → ℝ) := by
  classical
  exact Matrix.toLin'OfInv
    (M := (b.toMatrix c).map (Int.castRingHom ℝ))
    (M' := (c.toMatrix b).map (Int.castRingHom ℝ))
    (by rw [← Matrix.map_mul]; simp)
    (by rw [← Matrix.map_mul]; simp)

/-- The real coordinate change is multiplication by the integral change-of-basis matrix. -/
theorem torusBasisChangeLinearEquiv_apply (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ) (x : ι → ℝ) :
    torusBasisChangeLinearEquiv b c x = (c.toMatrix b).map (Int.castRingHom ℝ) *ᵥ x := by
  classical
  rfl

/-- On integral coordinates the real extension is the original integral coordinate change. -/
@[simp] theorem torusBasisChangeLinearEquiv_intCast (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ)
    (l : Λ) :
    torusBasisChangeLinearEquiv b c (fun i ↦ (b.repr l i : ℝ)) =
      fun j ↦ (c.repr l j : ℝ) := by
  rw [torusBasisChangeLinearEquiv_apply]
  ext j
  simpa [Function.comp_def] using
    ((Int.castRingHom ℝ).map_mulVec (c.toMatrix b) (b.repr l) j).symm

/-- Reversing the two bases inverts the real coordinate change. -/
@[simp] theorem torusBasisChangeLinearEquiv_symm (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ) :
    (torusBasisChangeLinearEquiv b c).symm = torusBasisChangeLinearEquiv c b := by
  classical
  rfl

/-- Changing from a basis to itself leaves real coordinates unchanged. -/
@[simp] theorem torusBasisChangeLinearEquiv_refl (b : Basis ι ℤ Λ) :
    torusBasisChangeLinearEquiv b b = LinearEquiv.refl ℝ (ι → ℝ) := by
  classical
  ext x i
  simp [torusBasisChangeLinearEquiv_apply]

/-- Successive integral coordinate changes compose. -/
@[simp] theorem torusBasisChangeLinearEquiv_trans (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ)
    (d : Basis η ℤ Λ) :
    (torusBasisChangeLinearEquiv b c).trans (torusBasisChangeLinearEquiv c d) =
      torusBasisChangeLinearEquiv b d := by
  ext x i
  simp only [LinearEquiv.trans_apply, torusBasisChangeLinearEquiv_apply]
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Basis.toMatrix_mul_toMatrix]

/-- Integral changes of coordinates carry the standard lattice into the standard lattice. -/
theorem torusBasisChangeLinearEquiv_mapsTo (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ) :
    MapsTo (torusBasisChangeLinearEquiv b c)
      (span ℤ (range (Pi.basisFun ℝ ι))) (span ℤ (range (Pi.basisFun ℝ κ))) := by
  intro x hx
  have hx' : ∀ i, ∃ z : ℤ, (z : ℝ) = x i := by
    simpa using ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ x).1 hx
  choose z hz using hx'
  have heq : x = fun i ↦ (b.repr (b.equivFun.symm z) i : ℝ) := by
    simp only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    exact funext fun i ↦ (hz i).symm
  rw [heq, torusBasisChangeLinearEquiv_intCast]
  apply ((Pi.basisFun ℝ κ).mem_span_iff_repr_mem ℤ _).2
  intro j
  exact ⟨c.repr (b.equivFun.symm z) j, by simp⟩

/-- Integral changes of coordinates preserve the standard lattice in both directions. -/
@[simp] theorem torusBasisChangeLinearEquiv_mem_span_iff (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ)
    (x : ι → ℝ) :
    torusBasisChangeLinearEquiv b c x ∈ span ℤ (range (Pi.basisFun ℝ κ)) ↔
      x ∈ span ℤ (range (Pi.basisFun ℝ ι)) := by
  constructor
  · intro hx
    have h := torusBasisChangeLinearEquiv_mapsTo c b hx
    rwa [← torusBasisChangeLinearEquiv_symm, LinearEquiv.symm_apply_apply] at h
  · exact fun hx ↦ torusBasisChangeLinearEquiv_mapsTo b c hx

/-- The continuous additive equivalence of standard real tori induced by an integral change
of lattice basis. -/
noncomputable def torusBasisChange (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ) :
    ((ι → ℝ) ⧸ span ℤ (range (Pi.basisFun ℝ ι))) ≃ₜ+
      ((κ → ℝ) ⧸ span ℤ (range (Pi.basisFun ℝ κ))) :=
  ContinuousAddEquiv.mk'
    (Homeomorph.Quotient.congr
      (torusBasisChangeLinearEquiv b c).toContinuousLinearEquiv.toHomeomorph fun x y ↦ by
      simpa only [Submodule.quotientRel_def, ContinuousLinearEquiv.coe_toHomeomorph,
        LinearEquiv.coe_toContinuousLinearEquiv', map_sub] using
        (torusBasisChangeLinearEquiv_mem_span_iff b c (x - y)).symm)
    (fun x y ↦ by
      induction x using Submodule.Quotient.induction_on with | H x =>
        induction y using Submodule.Quotient.induction_on with | H y =>
          -- Quotient congruence computes on representatives, as does quotient addition.
          exact congrArg Submodule.Quotient.mk (map_add (torusBasisChangeLinearEquiv b c) x y))

/-- On representatives the torus coordinate change is the real extension of the integral one. -/
@[simp] theorem torusBasisChange_mk (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ) (x : ι → ℝ) :
    torusBasisChange b c (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (torusBasisChangeLinearEquiv b c x) := (rfl)

/-- The inverse torus coordinate change is obtained by reversing the bases. -/
@[simp] theorem torusBasisChange_symm (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ) :
    (torusBasisChange b c).symm = torusBasisChange c b := by
  ext z
  induction z using Submodule.Quotient.induction_on with | H x =>
    rfl

/-- Changing a basis to itself acts identically on the standard torus. -/
@[simp] theorem torusBasisChange_refl (b : Basis ι ℤ Λ) :
    torusBasisChange b b = ContinuousAddEquiv.refl _ := by
  ext z
  induction z using Submodule.Quotient.induction_on with | H x =>
    simp

/-- Successive changes of basis on standard tori compose. -/
@[simp] theorem torusBasisChange_trans (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ)
    (d : Basis η ℤ Λ) :
    (torusBasisChange b c).trans (torusBasisChange c d) = torusBasisChange b d := by
  ext z
  induction z using Submodule.Quotient.induction_on with | H x =>
    simp only [ContinuousAddEquiv.trans_apply, torusBasisChange_mk]
    exact congrArg Submodule.Quotient.mk
      (congrArg (fun e : (ι → ℝ) ≃ₗ[ℝ] (η → ℝ) ↦ e x)
        (torusBasisChangeLinearEquiv_trans b c d))

variable {Y : Type*} [TopologicalSpace Y]
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
