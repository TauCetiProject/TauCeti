/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PrincipalParts.FirstCohomology
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PrincipalParts.Repartition
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.FieldTheory.FunctionField.Repartition.IndexOfSpecialty
public import TauCeti.Topology.KrullDimension

/-!
# First cohomology as a repartition quotient

Let `X` be an integral separated Noetherian curve over a field `k`, with its codimension-one
points identified with the places of `k(X)`. The global principal parts of a divisor `D` are the
quotient of the repartition space `A_{k(X)}` by its divisor filtration `A_{k(X)}(D)`, while first
cohomology is the quotient of those principal parts by global rational functions. This file
combines the two quotient descriptions:

`H¹(X, 𝒪_X(D)) ≃ A_{k(X)} / (A_{k(X)}(D) + k(X))`.

The right-hand side is finite-dimensional for an algebraic function field. Consequently this gives
finite-dimensionality of `H¹(X, 𝒪_X(D))` on the
curves to which the scheme/function-field comparison applies.

## Main declarations

* `SchemeWeilDivisor.diagonalRationalFunctionsToRepartitions` embeds global rational functions
  as diagonal repartitions;
* `SchemeWeilDivisor.repartitionToCohomologyOne` sends a repartition to its first cohomology
  class;
* `SchemeWeilDivisor.repartitionQuotientEquivCohomologyOne` identifies the quotient by the
  divisor filtration and diagonal rational functions with `H¹(X, 𝒪_X(D))`;
* `SchemeWeilDivisor.finiteDimensional_cohomology_one_sheaf_of_isFunctionField` deduces
  finite-dimensionality.

## References

* J.-P. Serre, *Algebraic Groups and Class Fields*, Chapter II, Section 5.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem I.5.4.
-/

public section

open CategoryTheory AlgebraicGeometry Order

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace SchemeWeilDivisor

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsIntegral X]

/-- The top open of an integral scheme is nonempty. -/
local instance nonemptyTopOpensRepartitionCohomology : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Classical.choice inferInstance, trivial⟩⟩

/-- Global rational functions, viewed as diagonal elements of the repartition space. -/
def diagonalRationalFunctionsToRepartitions (hF : IsFunctionField k X.functionField) :
    Γ(Scheme.rationalFunctions X, ⊤) →ₗ[k] repartitionSpace k X.functionField :=
  LinearMap.codRestrict _
    ((Pi.constAlgHom k (Place k X.functionField) X.functionField).toLinearMap.comp
      (Scheme.globalRationalFunctionsEquivFunctionField (k := k) (X := X)).toLinearMap)
    fun f ↦ by
      -- The codomain restriction is the constant family underlying the diagonal map.
      have hconst (x : X.functionField) :
          (Pi.constAlgHom k (Place k X.functionField) X.functionField).toLinearMap x =
            Function.const _ x := by
        funext P
        exact Pi.constAlgHom_apply k (Place k X.functionField) X.functionField x P
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hconst,
        Scheme.globalRationalFunctionsEquivFunctionField_apply] using
        const_mem_repartitionSpace hF (Scheme.rationalFunctionsEquiv ⊤ f)

@[simp]
lemma diagonalRationalFunctionsToRepartitions_apply
    (f : Γ(Scheme.rationalFunctions X, ⊤)) :
    ((diagonalRationalFunctionsToRepartitions (X := X) hF f : repartitionSpace k X.functionField) :
      Place k X.functionField → X.functionField) =
      Function.const _ (Scheme.rationalFunctionsEquiv ⊤ f) :=
  by
    funext P
    simp only [diagonalRationalFunctionsToRepartitions, LinearMap.codRestrict_apply,
      LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      Scheme.globalRationalFunctionsEquivFunctionField_apply,
      AlgHom.toLinearMap_apply, Pi.constAlgHom_apply]

/-- The image of global rational functions is the diagonal inside the repartition space. -/
theorem range_diagonalRationalFunctionsToRepartitions (hF : IsFunctionField k X.functionField) :
    LinearMap.range (diagonalRationalFunctionsToRepartitions (X := X) hF) =
      (diagonalRepartitions k X.functionField).submoduleOf
        (repartitionSpace k X.functionField) := by
  ext a
  -- Unfold range membership and the submodule trace to membership of the underlying family.
  change (∃ f, diagonalRationalFunctionsToRepartitions hF f = a) ↔
    (a : Place k X.functionField → X.functionField) ∈ diagonalRepartitions k X.functionField
  rw [mem_diagonalRepartitions_iff]
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨Scheme.rationalFunctionsEquiv ⊤ f,
      (diagonalRationalFunctionsToRepartitions_apply (hF := hF) f).symm⟩
  · rintro ⟨f, hf⟩
    refine ⟨(Scheme.rationalFunctionsEquiv ⊤).symm f, ?_⟩
    apply Subtype.ext
    simpa only [diagonalRationalFunctionsToRepartitions_apply,
      LinearEquiv.apply_symm_apply] using hf

/-- Global rational functions embed into the repartition space diagonally. -/
theorem diagonalRationalFunctionsToRepartitions_injective
    (hF : IsFunctionField k X.functionField) :
    Function.Injective (diagonalRationalFunctionsToRepartitions (X := X) hF) := by
  intro f g h
  apply (Scheme.rationalFunctionsEquiv ⊤).injective
  let _ : Nonempty (Place k X.functionField) := Place.nonempty hF
  apply Function.const_injective (α := Place k X.functionField)
  simpa only [diagonalRationalFunctionsToRepartitions_apply] using congrArg Subtype.val h

variable [IsNoetherian X] [X.IsSeparated]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]

variable (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))
  (hdim : ∀ x : X, coheight x ≤ 1)

/-- Taking principal parts of the diagonal repartition of a global rational function recovers
the usual global principal-parts map. -/
lemma repartitionToPrincipalParts_diagonalRationalFunctionsToRepartitions
    (D : SchemeWeilDivisor X) (f : Γ(Scheme.rationalFunctions X, ⊤)) :
    repartitionToPrincipalParts hex hdim D
        (diagonalRationalFunctionsToRepartitions hF f) =
      globalToPrincipalPartsBaseLinear k D f := by
  apply (principalPartsSectionsEquiv D ⊤).injective
  apply DFinsupp.ext
  intro x
  rw [repartitionToPrincipalParts_apply, globalToPrincipalPartsBaseLinear_apply,
    toPrincipalParts_app_apply, principalPartAt_eq]
  simp only [diagonalRationalFunctionsToRepartitions_apply, Function.const_apply]


/-- The first cohomology class represented by a repartition. -/
def repartitionToCohomologyOne (D : SchemeWeilDivisor X) :
    repartitionSpace k X.functionField →ₗ[k] Scheme.Modules.Cohomology (sheaf D) 1 :=
  (principalPartsBoundary k
    (fun x ↦ isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one hdim x.property)
    D).comp
    (repartitionToPrincipalParts hex hdim D)

@[simp]
lemma repartitionToCohomologyOne_apply (D : SchemeWeilDivisor X)
    (a : repartitionSpace k X.functionField) :
    repartitionToCohomologyOne hex hdim D a =
      principalPartsBoundary k
        (fun x ↦ isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one hdim x.property) D
        (repartitionToPrincipalParts hex hdim D a) :=
  by
    rw [repartitionToCohomologyOne, LinearMap.comp_apply]

/-- Every first cohomology class is represented by a repartition. -/
theorem repartitionToCohomologyOne_surjective (D : SchemeWeilDivisor X) :
    Function.Surjective (repartitionToCohomologyOne hex hdim D) :=
  (principalPartsBoundary_surjective k
    (fun x ↦ isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one hdim x.property)
    D).comp (repartitionToPrincipalParts_surjective hex hdim D)

/-- The cohomology class of the diagonal repartition of a global rational function vanishes. -/
@[simp]
lemma repartitionToCohomologyOne_diagonalRationalFunctionsToRepartitions
    (D : SchemeWeilDivisor X) (f : Γ(Scheme.rationalFunctions X, ⊤)) :
    principalPartsBoundary k
      (fun x ↦ isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one hdim x.property) D
        (repartitionToPrincipalParts hex hdim D
          (diagonalRationalFunctionsToRepartitions (X := X) hF f)) = 0 := by
  rw [repartitionToPrincipalParts_diagonalRationalFunctionsToRepartitions (X := X) (hF := hF)
      (hex := hex) (hdim := hdim),
    ← LinearMap.mem_ker, ker_principalPartsBoundary]
  exact LinearMap.mem_range_self _ _

/-- The repartitions representing the zero class in `H¹(X, 𝒪_X(D))` are exactly the sums of a
repartition bounded by `D` and a diagonal rational function. -/
theorem ker_repartitionToCohomologyOne (hF : IsFunctionField k X.functionField)
    (D : SchemeWeilDivisor X) :
    LinearMap.ker (repartitionToCohomologyOne hex hdim D) =
      submoduleOfAdeleFiltrationSupDiagonalRepartitions
        (equivFunctionFieldDivisor hex hdim D) := by
  ext a
  rw [LinearMap.mem_ker, repartitionToCohomologyOne_apply,
    principalPartsBoundary_eq_zero_iff]
  constructor
  · rintro ⟨f, hf⟩
    apply mem_submoduleOfAdeleFiltrationSupDiagonalRepartitions_iff.mpr
    let b : repartitionSpace k X.functionField :=
      a - diagonalRationalFunctionsToRepartitions hF f
    have hb : b ∈ (adeleFiltration (equivFunctionFieldDivisor hex hdim D)).submoduleOf
        (repartitionSpace k X.functionField) := by
      rw [← ker_repartitionToPrincipalParts]
      -- The kernel theorem is stated for the filtration embedded in the repartition space.
      change repartitionToPrincipalParts hex hdim D
          (a - diagonalRationalFunctionsToRepartitions hF f) = 0
      rw [map_sub, repartitionToPrincipalParts_diagonalRationalFunctionsToRepartitions
        (X := X) (hF := hF) (hex := hex) (hdim := hdim), hf, sub_self]
    have hdiag : (diagonalRationalFunctionsToRepartitions hF f :
        Place k X.functionField → X.functionField) ∈ diagonalRepartitions k X.functionField := by
      have hr := LinearMap.mem_range_self (diagonalRationalFunctionsToRepartitions hF) f
      rw [range_diagonalRationalFunctionsToRepartitions hF] at hr
      exact hr
    refine Submodule.mem_sup.mpr ⟨b, hb, diagonalRationalFunctionsToRepartitions hF f, hdiag, ?_⟩
    ext P
    simpa only [b, Submodule.coe_sub, Submodule.coe_add, Pi.sub_apply, Pi.add_apply] using
      congrFun (congrArg Subtype.val
        (sub_add_cancel a (diagonalRationalFunctionsToRepartitions hF f))) P
  · intro ha
    have ha' : (a : Place k X.functionField → X.functionField) ∈
        adeleFiltration (equivFunctionFieldDivisor hex hdim D) ⊔
          diagonalRepartitions k X.functionField :=
      (mem_submoduleOfAdeleFiltrationSupDiagonalRepartitions_iff
        (D := equivFunctionFieldDivisor hex hdim D) (a := a)).mp ha
    obtain ⟨b, hb, c, hc, hac⟩ := Submodule.mem_sup.mp ha'
    let b' : repartitionSpace k X.functionField :=
      ⟨b, adeleFiltration_le_repartitionSpace (equivFunctionFieldDivisor hex hdim D) hb⟩
    let c' : repartitionSpace k X.functionField :=
      ⟨c, diagonalRepartitions_le_repartitionSpace hF hc⟩
    obtain ⟨s, hs⟩ : c' ∈ LinearMap.range (diagonalRationalFunctionsToRepartitions hF) :=
      (range_diagonalRationalFunctionsToRepartitions hF).symm ▸ hc
    have hb' : repartitionToPrincipalParts hex hdim D b' = 0 := by
      rw [← LinearMap.mem_ker, ker_repartitionToPrincipalParts]
      exact hb
    have hc' : diagonalRationalFunctionsToRepartitions hF s = c' := hs
    have hac' : a = b' + c' := by
      ext P
      simpa only [b', c', Submodule.coe_add, Pi.add_apply] using congrFun hac.symm P
    refine ⟨s, ?_⟩
    rw [← repartitionToPrincipalParts_diagonalRationalFunctionsToRepartitions
      (X := X) (hF := hF) (hex := hex) (hdim := hdim), hc', hac', map_add, hb', zero_add]

/-- **First cohomology as a repartition quotient.** The quotient of the repartition space by
the divisor filtration and diagonal rational functions is linearly equivalent to
`H¹(X, 𝒪_X(D))`. -/
def repartitionQuotientEquivCohomologyOne (hF : IsFunctionField k X.functionField)
    (D : SchemeWeilDivisor X) :
    (↥(repartitionSpace k X.functionField) ⧸
      submoduleOfAdeleFiltrationSupDiagonalRepartitions
        (equivFunctionFieldDivisor hex hdim D)) ≃ₗ[k]
      Scheme.Modules.Cohomology (sheaf D) 1 :=
  (Submodule.quotEquivOfEq _ _ (ker_repartitionToCohomologyOne hex hdim hF D).symm).trans
    ((repartitionToCohomologyOne hex hdim D).quotKerEquivOfSurjective
      (repartitionToCohomologyOne_surjective hex hdim D))

/-- The repartition-quotient equivalence sends the class of a repartition to its first
cohomology class. -/
@[simp]
lemma repartitionQuotientEquivCohomologyOne_mk
    (hF : IsFunctionField k X.functionField) (D : SchemeWeilDivisor X)
    (a : repartitionSpace k X.functionField) :
    repartitionQuotientEquivCohomologyOne hex hdim hF D (Submodule.Quotient.mk a) =
      repartitionToCohomologyOne hex hdim D a := by
  rw [repartitionQuotientEquivCohomologyOne, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ a

/-- The first cohomology of a divisor sheaf is finite-dimensional. -/
theorem finiteDimensional_cohomology_one_sheaf_of_isFunctionField
    (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))
    (hdim : ∀ x : X, coheight x ≤ 1)
    (hF : IsFunctionField k X.functionField)
    (D : SchemeWeilDivisor X) :
    FiniteDimensional k (Scheme.Modules.Cohomology (sheaf D) 1) := by
  let _ : FiniteDimensional k (↥(repartitionSpace k X.functionField) ⧸
      submoduleOfAdeleFiltrationSupDiagonalRepartitions
        (equivFunctionFieldDivisor hex hdim D)) := by
    rw [submoduleOfAdeleFiltrationSupDiagonalRepartitions_eq_submoduleOf]
    exact finiteDimensional_quotient_repartitionSpace hF
      (equivFunctionFieldDivisor hex hdim D)
  exact Module.Finite.equiv (repartitionQuotientEquivCohomologyOne hex hdim hF D)

end SchemeWeilDivisor

end

end AlgebraicGeometry

end TauCeti
