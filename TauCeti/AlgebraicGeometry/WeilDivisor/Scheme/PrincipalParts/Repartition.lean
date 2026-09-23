/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.FunctionField
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PrincipalParts.Basic
public import TauCeti.FieldTheory.FunctionField.Repartition.Basic

/-!
# Repartitions and scheme-theoretic principal parts

Let `X` be an integral Noetherian separated scheme over a field `k`. Assume that `X → Spec(k)`
satisfies the existence part of the valuative criterion, every point has coheight at most one,
the local rings at codimension-one points are discrete valuation rings, and the resulting
codimension-one points are identified with the normalized places of its function field. A
repartition of `k(X) / k` determines a finitely supported family of principal parts: at a point
`x`, take the class of its entry at the corresponding place in `k(X) / 𝒪_X(D)_x`.

This file constructs that map and proves that it is surjective, with kernel the repartitions
bounded by the function-field divisor corresponding to `D`. Thus global principal parts are the
quotient of the repartition space by one step of its divisor filtration. This is the local
comparison needed to identify first cohomology of `𝒪_X(D)` with a repartition cokernel.

## Main declarations

* `SchemeWeilDivisor.repartitionToPrincipalParts`: the linear map from repartitions to global
  principal parts;
* `SchemeWeilDivisor.ker_repartitionToPrincipalParts`: its kernel is the divisor filtration;
* `SchemeWeilDivisor.repartitionToPrincipalParts_surjective`: every finitely supported family of
  principal parts is represented by a repartition;
* `SchemeWeilDivisor.adeleFiltrationQuotientEquivPrincipalParts`: global principal parts are the
  quotient of the repartition space by the divisor filtration.

## References

* J.-P. Serre, *Algebraic Groups and Class Fields*, Chapter II, Section 5.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.5.
-/

public section

open scoped WithZero

open Order _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

namespace SchemeWeilDivisor

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (.of k))]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]

section

variable [IsLocallyNoetherian X]

/-- Membership in the stalk of `𝒪_X(D)` at `x` is the valuation bound imposed by `D(x)`. -/
theorem mem_stalkSubmodule_iff_valuation_le_exp (D : SchemeWeilDivisor X)
    (x : CodimensionOnePoint X) (f : X.functionField) :
    f ∈ stalkSubmodule D x ↔
      (X.toPlace (k := k) (x : X)).valuation f ≤ WithZero.exp (WeilDivisor.coeff D x) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [mem_stalkSubmodule, or_iff_right hf,
      (X.toPlace (k := k) (x : X)).valuation_eq_exp_neg_ord hf,
      WithZero.exp_le_exp, CodimensionOnePoint.toPlace_ord]
    omega

end

variable [IsNoetherian X] [X.IsSeparated]

variable (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))
  (hdim : ∀ x : X, coheight x ≤ 1)

private def repartitionToPrincipalPartsFamily (D : SchemeWeilDivisor X)
    (a : repartitionSpace k X.functionField) : principalPartsSections D ⊤ := by
  let e := CodimensionOnePoint.equivPlace (k := k) hex hdim
  let q : ∀ x : {x : CodimensionOnePoint X // (x : X) ∈ (⊤ : X.Opens)}, PrincipalPart D x.1 :=
    fun x ↦ Submodule.Quotient.mk ((a : Place k X.functionField → X.functionField) (e x.1))
  have ha : {P : Place k X.functionField |
      ¬ P.valuation ((a : Place k X.functionField → X.functionField) P) ≤ 1}.Finite :=
    mem_repartitionSpace_iff_finite.mp a.property
  have ha' : {x : CodimensionOnePoint X |
      ¬ (e x).valuation ((a : Place k X.functionField → X.functionField) (e x)) ≤ 1}.Finite :=
    ha.preimage e.injective.injOn
  have hq : {x | q x ≠ 0}.Finite := by
    let val : {x : CodimensionOnePoint X // (x : X) ∈ (⊤ : X.Opens)} →
        CodimensionOnePoint X := fun x ↦ x.1
    have hDfinite : (val ⁻¹' (D.support : Set (CodimensionOnePoint X))).Finite :=
      Set.Finite.preimage Subtype.val_injective.injOn D.support.finite_toSet
    have hafinite : (val ⁻¹' {x | ¬ (e x).valuation
        ((a : Place k X.functionField → X.functionField) (e x)) ≤ 1}).Finite :=
      Set.Finite.preimage Subtype.val_injective.injOn ha'
    refine (hDfinite.union hafinite).subset ?_
    intro x hx
    by_contra h
    rw [Set.mem_union, Set.mem_preimage, Finset.mem_coe, Set.mem_preimage, not_or] at h
    have hD : WeilDivisor.coeff D x.1 = 0 := Finsupp.notMem_support_iff.mp h.1
    have ha_integral : (e x.1).valuation
        ((a : Place k X.functionField → X.functionField) (e x.1)) ≤ 1 := by
      simpa only [Set.mem_preimage, Set.mem_ofPred_eq, not_not] using h.2
    apply hx
    simp only [q]
    rw [Submodule.Quotient.mk_eq_zero,
      mem_stalkSubmodule_iff_valuation_le_exp (k := k)]
    rw [← CodimensionOnePoint.equivPlace_apply (X := X) (k := k) hex hdim, hD,
      WithZero.exp_zero]
    exact ha_integral
  classical
  exact dfinsuppOfFiniteSupport q hq

@[simp]
private theorem repartitionToPrincipalPartsFamily_apply (D : SchemeWeilDivisor X)
    (a : repartitionSpace k X.functionField)
    (x : {x : CodimensionOnePoint X // (x : X) ∈ (⊤ : X.Opens)}) :
    repartitionToPrincipalPartsFamily hex hdim D a x =
      Submodule.Quotient.mk ((a : Place k X.functionField → X.functionField)
        (X.toPlace (k := k) (x.1 : X))) := by
  simp only [repartitionToPrincipalPartsFamily, dfinsuppOfFiniteSupport_apply,
    CodimensionOnePoint.equivPlace_apply (X := X) (k := k) hex hdim]

/-- A repartition determines a global family of principal parts by taking, at each
codimension-one point, the class of its entry at the corresponding place. -/
def repartitionToPrincipalParts (D : SchemeWeilDivisor X) :
    repartitionSpace k X.functionField →ₗ[k] Γ(principalParts D, ⊤) where
  toFun a := (principalPartsSectionsEquiv D ⊤).symm
    (repartitionToPrincipalPartsFamily hex hdim D a)
  map_add' a b := by
    apply (principalPartsSectionsEquiv D ⊤).injective
    simp only [map_add, AddEquiv.apply_symm_apply]
    apply DFinsupp.ext
    intro x
    simp only [DFinsupp.add_apply, repartitionToPrincipalPartsFamily_apply]
    exact Submodule.Quotient.mk_add _
  map_smul' c a := by
    apply (principalPartsSectionsEquiv D ⊤).injective
    apply DFinsupp.ext
    intro x
    simp only [AddEquiv.apply_symm_apply, repartitionToPrincipalPartsFamily_apply]
    simp only [RingHom.id_apply, Scheme.Modules.base_smul_globalSections]
    rw [principalPartsSectionsEquiv_smul_apply D ⊤
      (Scheme.Modules.baseRingToGlobalSections k X c)]
    simp only [AddEquiv.apply_symm_apply, repartitionToPrincipalPartsFamily_apply]
    congr 1
    simp only [Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def]
    have hgerm : X.presheaf.germ ⊤ x.1 x.2
        (Scheme.Modules.baseRingToGlobalSections k X c) =
        algebraMap k (X.presheaf.stalk (x.1 : X)) c := by
      rw [Scheme.algebraMap_stalk_eq_baseRingToStalk]
      exact (Scheme.baseRingToStalk_apply k X x.1 c).symm
    rw [hgerm, IsScalarTower.algebraMap_apply k
      (X.presheaf.stalk (x.1 : X)) X.functionField]

/-- The principal part of a repartition at `x` is the class of its entry at the place attached
to `x`. -/
@[simp]
theorem repartitionToPrincipalParts_apply (D : SchemeWeilDivisor X)
    (a : repartitionSpace k X.functionField)
    (x : {x : CodimensionOnePoint X // (x : X) ∈ (⊤ : X.Opens)}) :
    principalPartsSectionsEquiv D ⊤ (repartitionToPrincipalParts hex hdim D a) x =
      Submodule.Quotient.mk ((a : Place k X.functionField → X.functionField)
        (X.toPlace (k := k) (x.1 : X))) := by
  -- Expose the application of the linear-map wrapper so that the public additive equivalence,
  -- rather than the sealed sheaf construction, reduces the section to its family of values.
  change principalPartsSectionsEquiv D ⊤
      ((principalPartsSectionsEquiv D ⊤).symm
        (repartitionToPrincipalPartsFamily hex hdim D a)) x = _
  rw [AddEquiv.apply_symm_apply, repartitionToPrincipalPartsFamily_apply]

/-- The kernel of the repartition-to-principal-parts map is the step of the repartition
filtration bounded by the corresponding function-field divisor. -/
theorem ker_repartitionToPrincipalParts (D : SchemeWeilDivisor X) :
    LinearMap.ker (repartitionToPrincipalParts hex hdim D) =
      (adeleFiltration (equivFunctionFieldDivisor hex hdim D)).submoduleOf
        (repartitionSpace k X.functionField) := by
  ext a
  rw [LinearMap.mem_ker]
  constructor
  · intro ha
    -- Expose membership in `submoduleOf`, whose carrier is the same divisor-filtration bound.
    change (a : Place k X.functionField → X.functionField) ∈
      adeleFiltration (equivFunctionFieldDivisor hex hdim D)
    rw [mem_adeleFiltration_iff]
    intro P
    let x := (CodimensionOnePoint.equivPlace (k := k) hex hdim).symm P
    let xt : {x : CodimensionOnePoint X // (x : X) ∈ (⊤ : X.Opens)} := ⟨x, by simp⟩
    have hx : principalPartsSectionsEquiv D ⊤
        (repartitionToPrincipalParts hex hdim D a) xt = 0 := by
      simp only [ha, map_zero, DFinsupp.zero_apply]
    rw [repartitionToPrincipalParts_apply,
      Submodule.Quotient.mk_eq_zero,
      mem_stalkSubmodule_iff_valuation_le_exp (k := k)] at hx
    dsimp only [xt] at hx
    have he : X.toPlace (k := k) (x : X) = P := by
      rw [← CodimensionOnePoint.equivPlace_apply (X := X) (k := k) hex hdim]
      exact (CodimensionOnePoint.equivPlace hex hdim).apply_symm_apply P
    rw [he] at hx
    rw [coeff_equivFunctionFieldDivisor]
    exact hx
  · intro ha
    apply (principalPartsSectionsEquiv D ⊤).injective
    simp only [map_zero]
    apply DFinsupp.ext
    intro x
    rw [DFinsupp.zero_apply, repartitionToPrincipalParts_apply,
      Submodule.Quotient.mk_eq_zero,
      mem_stalkSubmodule_iff_valuation_le_exp (k := k)]
    have hbound :=
      (mem_adeleFiltration_iff.mp ha (X.toPlace (k := k) (x.1 : X)))
    rw [coeff_equivFunctionFieldDivisor_toPlace] at hbound
    exact hbound

/-- Every global family of principal parts is represented by a repartition. -/
theorem repartitionToPrincipalParts_surjective (D : SchemeWeilDivisor X) :
    Function.Surjective (repartitionToPrincipalParts hex hdim D) := by
  classical
  intro s
  let t := principalPartsSectionsEquiv D ⊤ s
  let e := CodimensionOnePoint.equivPlace (k := k) hex hdim
  let ix : Place k X.functionField →
      {x : CodimensionOnePoint X // (x : X) ∈ (⊤ : X.Opens)} :=
    fun P ↦ ⟨e.symm P, by simp⟩
  have hix : Function.Injective ix := by
    intro P Q h
    apply e.symm.injective
    exact congrArg Subtype.val h
  let representative : ∀ x, X.functionField := fun x ↦
    if hx : t x = 0 then 0 else Classical.choose
      ((Submodule.Quotient.mk_surjective (stalkSubmodule D x.1)) (t x))
  have hrepresentative (x) : Submodule.Quotient.mk (representative x) = t x := by
    dsimp only [representative]
    split_ifs with hx
    · simp [hx]
    · exact Classical.choose_spec
        ((Submodule.Quotient.mk_surjective (stalkSubmodule D x.1)) (t x))
  have hrepresentative_ne (x) (hx : representative x ≠ 0) : t x ≠ 0 := by
    intro htx
    apply hx
    dsimp only [representative]
    simp [htx]
  let b : Place k X.functionField → X.functionField := fun P ↦ representative (ix P)
  have hb_support : {P | b P ≠ 0}.Finite := by
    refine (t.support.finite_toSet.preimage hix.injOn).subset ?_
    intro P hP
    rw [Set.mem_preimage, Finset.mem_coe]
    exact (DFinsupp.mem_support_toFun t (ix P)).mpr (hrepresentative_ne (ix P) hP)
  have hb : b ∈ repartitionSpace k X.functionField := by
    rw [mem_repartitionSpace_iff_finite]
    exact hb_support.subset fun P hP hPb ↦ hP (by simp [hPb])
  let a : repartitionSpace k X.functionField := ⟨b, hb⟩
  refine ⟨a, ?_⟩
  apply (principalPartsSectionsEquiv D ⊤).injective
  apply DFinsupp.ext
  intro x
  rw [repartitionToPrincipalParts_apply]
  have hix_apply : ix (X.toPlace (k := k) (x.1 : X)) = x := by
    apply Subtype.ext
    simp only [ix, e, ← CodimensionOnePoint.equivPlace_apply (X := X) (k := k) hex hdim,
      Equiv.symm_apply_apply]
  have ha_apply : (a : Place k X.functionField → X.functionField)
      (X.toPlace (k := k) (x.1 : X)) = representative x := by
    simp only [a, b, hix_apply]
  rw [ha_apply, hrepresentative]

/-- **Global principal parts as a repartition quotient.** The quotient of the repartition space
by the repartitions bounded by `D` is linearly equivalent to the global principal parts of `D`. -/
def adeleFiltrationQuotientEquivPrincipalParts (D : SchemeWeilDivisor X) :
    (↥(repartitionSpace k X.functionField) ⧸
      (adeleFiltration (equivFunctionFieldDivisor hex hdim D)).submoduleOf
        (repartitionSpace k X.functionField)) ≃ₗ[k] Γ(principalParts D, ⊤) := by
  exact (Submodule.quotEquivOfEq _ _
    (ker_repartitionToPrincipalParts hex hdim D).symm).trans
      ((repartitionToPrincipalParts hex hdim D).quotKerEquivOfSurjective
        (repartitionToPrincipalParts_surjective hex hdim D))

/-- The repartition-quotient equivalence sends the class of a repartition to its family of
principal parts. -/
@[simp]
theorem adeleFiltrationQuotientEquivPrincipalParts_mk (D : SchemeWeilDivisor X)
    (a : repartitionSpace k X.functionField) :
    adeleFiltrationQuotientEquivPrincipalParts hex hdim D (Submodule.Quotient.mk a) =
      repartitionToPrincipalParts hex hdim D a := by
  rw [adeleFiltrationQuotientEquivPrincipalParts, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

end SchemeWeilDivisor

end

end TauCeti.AlgebraicGeometry
