/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import TauCeti.Algebra.MonoidAlgebra.Grading
public import TauCeti.RingTheory.MvPolynomial.Groebner.Homogeneous
public import TauCeti.RingTheory.MvPolynomial.ToricIdeal.Basic
public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous
import TauCeti.Data.Finsupp.Weight

/-!
# Hilbert functions of semigroup algebras and of their binomial presentations

Let `a : ι → M` be a family in an additive commutative monoid generating the submonoid
`S = AddSubmonoid.closure (Set.range a)`, and let `deg : M →+ D` be a degree. Give the variable
`X i` of `MvPolynomial ι R` the weight `deg (a i)`, so that the monomial `X^u` has weight
`deg (∑ i, u i • a i)`. The map `X i ↦ single (a i) 1` then sends the polynomials of weight `n`
onto the elements of `R[S]` of degree `n`. Consequently the toric ideal is homogeneous for this
weight, and the binomial presentation `MvPolynomial ι R ⧸ toricIdeal R a ≃ R[S]` identifies the
image of the polynomials of weight `n` with the homogeneous component of `R[S]` of degree `n`.

The rank of that component, the Hilbert function of `R[S]` in degree `n`, is the number of
elements of `S` of degree `n` (`AddMonoidAlgebra.finrank_gradeBy`). Over a field it is also the
number of standard monomials of weight `n` of the toric ideal for any monomial order, and the
corresponding rank for its ideal of leading terms. For finitely many generators of positive degree
in `ℕ`, only finitely many elements of `S` have a given degree, so these are finite counts
(`TauCeti.finite_closure_range_deg_eq`).

## Main results

* `TauCeti.aeval_single_mem_gradeBy`: the image of a polynomial of weight `n` has degree `n`.
* `TauCeti.map_aeval_single_weightedHomogeneousSubmodule`: if the `a i` generate `M`, the
  polynomials of weight `n` are mapped onto the homogeneous component of `R[M]` of degree `n`.
* `TauCeti.isHomogeneous_toricIdeal`: the toric ideal is homogeneous for the weights `deg (a i)`.
* `TauCeti.mapWeightedHomogeneousSubmoduleToricIdealEquivGradeBy`: the image of the polynomials of
  weight `n` in the quotient by the toric ideal is the homogeneous component of `R[S]` of
  degree `n`.
* `TauCeti.finrank_map_weightedHomogeneousSubmodule_toricIdeal`: its rank is the number of
  elements of `S` of degree `n`.
* `MonomialOrder.card_standardMonomials_toricIdeal`: over a field, so is the number of standard
  monomials of weight `n` of the toric ideal, for every monomial order.

## References

* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, University Lecture Series 8, AMS, 1996,
  Chapter 4.
-/

public section

open AddMonoidAlgebra MvPolynomial

namespace TauCeti

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {ι M D : Type*} [AddCommMonoid M] [AddCommMonoid D]

section CommSemiring

variable (R : Type*) [CommSemiring R]

variable {R} in
/-- The image under `X i ↦ single (a i) 1` of a polynomial of weight `n`, for the weights
`deg (a i)`, lies in the homogeneous component of `R[M]` of degree `n`. -/
theorem aeval_single_mem_gradeBy {a : ι → M} {deg : M →+ D} {n : D} {p : MvPolynomial ι R}
    (hp : p ∈ weightedHomogeneousSubmodule R (deg ∘ a) n) :
    aeval (fun i ↦ single (a i) (1 : R)) p ∈ gradeBy R deg n :=
  IsWeightedHomogeneous.aeval_mem (𝒜 := gradeBy R deg) hp fun _ ↦ single_mem_gradeBy deg _ _

/-- If the `a i` generate `M`, then `X i ↦ single (a i) 1` maps the polynomials of weight `n`,
for the weights `deg (a i)`, onto the homogeneous component of `R[M]` of degree `n`. -/
theorem map_aeval_single_weightedHomogeneousSubmodule {a : ι → M}
    (ha : AddSubmonoid.closure (Set.range a) = ⊤) (deg : M →+ D) (n : D) :
    (weightedHomogeneousSubmodule R (deg ∘ a) n).map
        (aeval fun i ↦ single (a i) (1 : R)).toLinearMap = gradeBy R deg n := by
  refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun p hp ↦ aeval_single_mem_gradeBy hp) ?_
  rw [gradeBy_eq_supported, supported_eq_span_single, Submodule.span_le]
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨u, rfl⟩ := AddSubmonoid.mem_closure_range_iff.1 (ha ▸ AddSubmonoid.mem_top s)
  refine ⟨monomial u 1, ?_, ?_⟩
  · exact isWeightedHomogeneous_monomial _ _ _
      ((Finsupp.weight_comp_eq_apply_linearCombination deg a u).trans hs)
  · simp [Finsupp.linearCombination_apply]

end CommSemiring

section CommRing

variable (R : Type*) [CommRing R]

/-- The toric ideal of `a` is homogeneous for the grading of `MvPolynomial ι R` by the weights
`deg (a i)`, for every degree `deg : M →+ D`. -/
theorem isHomogeneous_toricIdeal [DecidableEq D] (a : ι → M) (deg : M →+ D) :
    (toricIdeal R a).IsHomogeneous (weightedHomogeneousSubmodule R (deg ∘ a)) := by
  rw [toricIdeal_eq_span]
  refine Ideal.homogeneous_span _ _ ?_
  rintro _ ⟨u, v, h, rfl⟩
  refine ⟨deg (Finsupp.linearCombination ℕ a u), sub_mem ?_ ?_⟩ <;>
    rw [mem_weightedHomogeneousSubmodule] <;> refine isWeightedHomogeneous_monomial _ _ _ ?_
  · exact Finsupp.weight_comp_eq_apply_linearCombination deg a u
  · exact (Finsupp.weight_comp_eq_apply_linearCombination deg a v).trans (congrArg deg h.symm)

/-- The image of `quotientToricIdealAlgEquivClosure` of the polynomials of weight `n`, for the
weights `deg (a i)`, is the homogeneous component of degree `n` of the semigroup algebra of the
submonoid generated by the `a i`. -/
private theorem map_quotientToricIdealAlgEquivClosure (a : ι → M) (deg : M →+ D) (n : D) :
    ((weightedHomogeneousSubmodule R (deg ∘ a) n).map
        (Ideal.Quotient.mkₐ R (toricIdeal R a)).toLinearMap).map
      (quotientToricIdealAlgEquivClosure R a).toLinearMap =
      gradeBy R (deg ∘ Subtype.val : AddSubmonoid.closure (Set.range a) → D) n := by
  have h : (quotientToricIdealAlgEquivClosure R a).toLinearMap ∘ₗ
      (Ideal.Quotient.mkₐ R (toricIdeal R a)).toLinearMap =
      (aeval fun i ↦ single (⟨a i, AddSubmonoid.subset_closure (Set.mem_range_self i)⟩ :
        AddSubmonoid.closure (Set.range a)) (1 : R)).toLinearMap :=
    LinearMap.ext fun p ↦ quotientToricIdealAlgEquivClosure_mk R a p
  rw [← Submodule.map_comp, h]
  simpa [Function.comp_def] using map_aeval_single_weightedHomogeneousSubmodule R
    (closure_range_mk_eq_top a) (deg.comp (AddSubmonoid.closure (Set.range a)).subtype) n

/-- The image in `MvPolynomial ι R ⧸ toricIdeal R a` of the polynomials of weight `n`, for the
weights `deg (a i)`, is identified by the binomial presentation `quotientToricIdealAlgEquivClosure`
with the homogeneous component of degree `n` of the semigroup algebra `R[S]` of the submonoid `S`
generated by the `a i`. -/
noncomputable def mapWeightedHomogeneousSubmoduleToricIdealEquivGradeBy (a : ι → M) (deg : M →+ D)
    (n : D) :
    (weightedHomogeneousSubmodule R (deg ∘ a) n).map
        (Ideal.Quotient.mkₐ R (toricIdeal R a)).toLinearMap ≃ₗ[R]
      gradeBy R (deg ∘ Subtype.val : AddSubmonoid.closure (Set.range a) → D) n :=
  (quotientToricIdealAlgEquivClosure R a).toLinearEquiv.submoduleMap _ ≪≫ₗ
    LinearEquiv.ofEq _ _ (map_quotientToricIdealAlgEquivClosure R a deg n)

/-- The identification `mapWeightedHomogeneousSubmoduleToricIdealEquivGradeBy` is the binomial
presentation `quotientToricIdealAlgEquivClosure`. -/
@[simp]
theorem mapWeightedHomogeneousSubmoduleToricIdealEquivGradeBy_apply_coe (a : ι → M) (deg : M →+ D)
    (n : D) (x) :
    (mapWeightedHomogeneousSubmoduleToricIdealEquivGradeBy R a deg n x :
        AddMonoidAlgebra R (AddSubmonoid.closure (Set.range a))) =
      quotientToricIdealAlgEquivClosure R a x := by
  simp [mapWeightedHomogeneousSubmoduleToricIdealEquivGradeBy]

/-- **The Hilbert function of a binomial presentation.** The rank of the image in
`MvPolynomial ι R ⧸ toricIdeal R a` of the polynomials of weight `n`, for the weights `deg (a i)`,
is the number of elements of degree `n` of the submonoid generated by the `a i`. -/
theorem finrank_map_weightedHomogeneousSubmodule_toricIdeal [Nontrivial R] (a : ι → M)
    (deg : M →+ D) (n : D) :
    Module.finrank R ((weightedHomogeneousSubmodule R (deg ∘ a) n).map
        (Ideal.Quotient.mkₐ R (toricIdeal R a)).toLinearMap) =
      Nat.card {s : AddSubmonoid.closure (Set.range a) // deg s = n} := by
  rw [(mapWeightedHomogeneousSubmoduleToricIdealEquivGradeBy R a deg n).finrank_eq, finrank_gradeBy]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ Set.mem_singleton_iff)

end CommRing

end TauCeti

namespace MonomialOrder

open TauCeti

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {ι M D : Type*} [AddCommMonoid M] [AddCommMonoid D]

section Field

variable {k : Type*} [Field k]

/-- Over a field, for every monomial order, the number of standard monomials of weight `n` of the
toric ideal of `a`, for the weights `deg (a i)`, is the number of elements of degree `n` of the
submonoid generated by the `a i`. -/
theorem card_standardMonomials_toricIdeal (m : MonomialOrder ι) (a : ι → M)
    (deg : M →+ D) (n : D) :
    Nat.card ↥(m.standardMonomials (toricIdeal k a) ∩ {c | Finsupp.weight (deg ∘ a) c = n}) =
      Nat.card {s : AddSubmonoid.closure (Set.range a) // deg s = n} := by
  classical
  rw [← m.finrank_map_weightedHomogeneousSubmodule (isHomogeneous_toricIdeal k a deg) n,
    finrank_map_weightedHomogeneousSubmodule_toricIdeal]

/-- Over a field, for every monomial order, the rank of the image of the polynomials of weight `n`
in the quotient by the ideal of leading terms of the toric ideal of `a`, for the weights
`deg (a i)`, is the number of elements of degree `n` of the submonoid generated by the `a i`. -/
theorem finrank_map_weightedHomogeneousSubmodule_span_leadingTerm_toricIdeal
    (m : MonomialOrder ι) (a : ι → M) (deg : M →+ D) (n : D) :
    Module.finrank k ((weightedHomogeneousSubmodule k (deg ∘ a) n).map
        (Ideal.Quotient.mkₐ k (Ideal.span (m.leadingTerm '' toricIdeal k a))).toLinearMap) =
      Nat.card {s : AddSubmonoid.closure (Set.range a) // deg s = n} := by
  classical
  rw [MonomialOrder.finrank_map_weightedHomogeneousSubmodule_span_leadingTerm
    (isHomogeneous_toricIdeal k a deg), finrank_map_weightedHomogeneousSubmodule_toricIdeal]

end Field

end MonomialOrder
