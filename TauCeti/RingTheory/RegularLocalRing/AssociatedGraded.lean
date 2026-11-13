/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Regular.AssociatedGraded
public import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay

/-!
# The associated graded ring of a regular local ring

Let `(R, 𝔪)` be a regular local ring with residue field `κ = IsLocalRing.ResidueField R`, and let
`x₁, …, x_d` be a regular system of parameters, that is, `d = dim R` elements generating `𝔪`.
The associated graded
ring `gr_𝔪 R = ⨁ ν, 𝔪ᵛ ⧸ 𝔪ᵛ⁺¹` is a `κ`-algebra through its degree-zero part, and sending `Xᵢ` to
the degree-one class of `xᵢ` is a `κ`-algebra isomorphism `κ[X₁, …, X_d] ≃ gr_𝔪 R`. No coefficient
field and no equicharacteristic hypothesis is needed: the parameters form a regular sequence, whose
associated graded ring is a polynomial ring over `κ`.

Consequently `gr_𝔪 R` is a domain, and initial forms multiply: if `x ∈ 𝔪ʳ \ 𝔪ʳ⁺¹` and
`y ∈ 𝔪ˢ \ 𝔪ˢ⁺¹`, then `x * y ∉ 𝔪ʳ⁺ˢ⁺¹`. This is the input for the multiplicativity of the order
function `ord(x) = sup {r : x ∈ 𝔪ʳ}` on a regular local ring.

## Main results

* `TauCeti.IsRegularLocalRing.associatedGradedEquiv`: for a regular system of parameters, the
  isomorphism `κ[X₁, …, X_d] ≃ₐ[κ] gr_𝔪 R`.
* `TauCeti.IsRegularLocalRing.isDomain_associatedGraded`: `gr_𝔪 R` is a domain.
* `TauCeti.IsRegularLocalRing.mul_notMem_maximalIdeal_pow_succ`: initial forms multiply.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 14.4 and Theorem 16.2 (i).
* [The Stacks Project, Lemma 10.106.1](https://stacks.math.columbia.edu/tag/00NO).
-/

public section

namespace IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- The associated graded ring of the maximal ideal is an algebra over the residue field. -/
noncomputable instance : Algebra (ResidueField R) (maximalIdeal R).AssociatedGraded :=
  inferInstanceAs (Algebra (R ⧸ maximalIdeal R) (maximalIdeal R).AssociatedGraded)

/-- Scalars from the local ring act through its residue field on the associated graded ring. -/
instance : IsScalarTower R (ResidueField R) (maximalIdeal R).AssociatedGraded :=
  inferInstanceAs (IsScalarTower R (R ⧸ maximalIdeal R) (maximalIdeal R).AssociatedGraded)

/-- The degree-zero class of a residue is the scalar class of its representative. -/
@[simp]
theorem algebraMap_associatedGraded_residue (r : R) :
    algebraMap (ResidueField R) (maximalIdeal R).AssociatedGraded (residue R r) =
      algebraMap R (maximalIdeal R).AssociatedGraded r :=
  Ideal.AssociatedGraded.algebraMap_quotient_mk r

end IsLocalRing

open _root_.IsLocalRing Ideal RingTheory.Sequence

namespace TauCeti.IsRegularLocalRing

variable {R : Type*} [CommRing R] [IsRegularLocalRing R]

/-- **The associated graded ring of a regular local ring is a polynomial ring.** For a regular
system of parameters `rs`, that is, at most `spanFinrank 𝔪 = dim R` elements generating `𝔪`, the
`κ`-algebra map `κ[X₁, …, X_d] → gr_𝔪 R` sending `Xᵢ` to the degree-one class of the `i`-th
parameter is an isomorphism, where `κ = IsLocalRing.ResidueField R` is the residue field. -/
@[stacks 00NO]
noncomputable def associatedGradedEquiv {rs : List R} (hspan : ofList rs = maximalIdeal R)
    (hlen : rs.length ≤ (maximalIdeal R).spanFinrank) :
    MvPolynomial (Fin rs.length) (ResidueField R) ≃ₐ[ResidueField R]
      (maximalIdeal R).AssociatedGraded :=
  (isRegular_of_ofList_eq_maximalIdeal hspan hlen).toIsWeaklyRegular.associatedGradedEquiv hspan

/-- The regular-local comparison is the comparison for its weakly regular parameter sequence. -/
theorem associatedGradedEquiv_def {rs : List R} (hspan : ofList rs = maximalIdeal R)
    (hlen : rs.length ≤ (maximalIdeal R).spanFinrank) :
    associatedGradedEquiv hspan hlen =
      (isRegular_of_ofList_eq_maximalIdeal hspan hlen).toIsWeaklyRegular.associatedGradedEquiv
        hspan :=
  (rfl)

/-- The parameter comparison evaluates at the degree-one parameter classes. -/
theorem associatedGradedEquiv_apply {rs : List R} (hspan : ofList rs = maximalIdeal R)
    (hlen : rs.length ≤ (maximalIdeal R).spanFinrank)
    (P : MvPolynomial (Fin rs.length) (ResidueField R)) :
    associatedGradedEquiv hspan hlen P = MvPolynomial.aeval
      (fun i : Fin rs.length ↦ AssociatedGraded.mk (maximalIdeal R) 1
        ⟨rs[(i : ℕ)], by rw [pow_one, ← hspan]; exact subset_span (List.getElem_mem _)⟩) P := by
  -- Simplify in the quotient-algebra presentation before transporting to the residue field.
  have h := IsWeaklyRegular.associatedGradedEquiv_apply
    (isRegular_of_ofList_eq_maximalIdeal hspan hlen).toIsWeaklyRegular hspan
    (P : MvPolynomial (Fin rs.length) (R ⧸ maximalIdeal R))
  simp only [AssociatedGraded.mvPolynomialHom_def, Fin.getElem_fin] at h
  rw [associatedGradedEquiv_def]
  exact h

/-- The parameter comparison sends each variable to its degree-one parameter class. -/
@[simp]
theorem associatedGradedEquiv_X {rs : List R} (hspan : ofList rs = maximalIdeal R)
    (hlen : rs.length ≤ (maximalIdeal R).spanFinrank) (i : Fin rs.length) :
    associatedGradedEquiv hspan hlen (MvPolynomial.X i) =
      AssociatedGraded.mk (maximalIdeal R) 1
        ⟨rs[(i : ℕ)], by rw [pow_one, ← hspan]; exact subset_span (List.getElem_mem _)⟩ := by
  rw [associatedGradedEquiv_apply, MvPolynomial.aeval_X]

/-- The parameter comparison sends residue-field coefficients to their degree-zero classes. -/
@[simp]
theorem associatedGradedEquiv_C {rs : List R} (hspan : ofList rs = maximalIdeal R)
    (hlen : rs.length ≤ (maximalIdeal R).spanFinrank) (c : ResidueField R) :
    associatedGradedEquiv hspan hlen (MvPolynomial.C c) =
      algebraMap (ResidueField R) (maximalIdeal R).AssociatedGraded c :=
  (associatedGradedEquiv hspan hlen).commutes c

/-- The parameter comparison sends a reduced homogeneous form to the class of its value. -/
theorem associatedGradedEquiv_map_of_isHomogeneous {rs : List R}
    (hspan : ofList rs = maximalIdeal R) (hlen : rs.length ≤ (maximalIdeal R).spanFinrank)
    {ν : ℕ} {F : MvPolynomial (Fin rs.length) R} (hF : F.IsHomogeneous ν) :
    associatedGradedEquiv hspan hlen (F.map (residue R)) =
      AssociatedGraded.mk (maximalIdeal R) ν
        ⟨F.eval (fun i : Fin rs.length ↦ rs[(i : ℕ)]), hF.eval_mem_pow
          (fun i : Fin rs.length ↦ by rw [← hspan]; exact subset_span (List.getElem_mem _))⟩ := by
  rw [associatedGradedEquiv_def]
  exact IsWeaklyRegular.associatedGradedEquiv_map_of_isHomogeneous _ hspan hF

/-- The parameter comparison preserves homogeneous components. -/
theorem associatedGradedEquiv_homogeneousComponent {rs : List R}
    (hspan : ofList rs = maximalIdeal R) (hlen : rs.length ≤ (maximalIdeal R).spanFinrank)
    (ν : ℕ) (P : MvPolynomial (Fin rs.length) (ResidueField R)) :
    associatedGradedEquiv hspan hlen (MvPolynomial.homogeneousComponent ν P) =
      DirectSum.of (maximalIdeal R).GradedPiece ν (associatedGradedEquiv hspan hlen P ν) := by
  rw [associatedGradedEquiv_def]
  exact IsWeaklyRegular.associatedGradedEquiv_homogeneousComponent _ hspan ν P

/-- The parameter comparison preserves and reflects homogeneity of any specified degree. -/
theorem isHomogeneous_iff_associatedGradedEquiv_mem_range {rs : List R}
    (hspan : ofList rs = maximalIdeal R) (hlen : rs.length ≤ (maximalIdeal R).spanFinrank)
    (ν : ℕ) (P : MvPolynomial (Fin rs.length) (ResidueField R)) :
    P.IsHomogeneous ν ↔ associatedGradedEquiv hspan hlen P ∈
      Set.range (DirectSum.of (maximalIdeal R).GradedPiece ν) := by
  rw [associatedGradedEquiv_def]
  exact IsWeaklyRegular.isHomogeneous_iff_associatedGradedEquiv_mem_range _ hspan ν P

/-- The inverse parameter comparison preserves homogeneous components. -/
@[simp]
theorem homogeneousComponent_associatedGradedEquiv_symm {rs : List R}
    (hspan : ofList rs = maximalIdeal R) (hlen : rs.length ≤ (maximalIdeal R).spanFinrank)
    (ν : ℕ) (g : (maximalIdeal R).AssociatedGraded) :
    MvPolynomial.homogeneousComponent ν ((associatedGradedEquiv hspan hlen).symm g) =
      (associatedGradedEquiv hspan hlen).symm
        (DirectSum.of (maximalIdeal R).GradedPiece ν (g ν)) := by
  rw [associatedGradedEquiv_def]
  exact IsWeaklyRegular.homogeneousComponent_associatedGradedEquiv_symm _ hspan ν g

/-- The inverse parameter comparison sends the degree-`ν` summand to degree-`ν` forms. -/
theorem isHomogeneous_associatedGradedEquiv_symm_of {rs : List R}
    (hspan : ofList rs = maximalIdeal R) (hlen : rs.length ≤ (maximalIdeal R).spanFinrank)
    (ν : ℕ) (q : (maximalIdeal R).GradedPiece ν) :
    ((associatedGradedEquiv hspan hlen).symm
      (DirectSum.of (maximalIdeal R).GradedPiece ν q)).IsHomogeneous ν := by
  rw [associatedGradedEquiv_def]
  exact IsWeaklyRegular.isHomogeneous_associatedGradedEquiv_symm_of _ hspan ν q

/-- The inverse parameter comparison sends a class from `𝔪ᵛ` to a degree-`ν` form. -/
theorem isHomogeneous_associatedGradedEquiv_symm_mk {rs : List R}
    (hspan : ofList rs = maximalIdeal R) (hlen : rs.length ≤ (maximalIdeal R).spanFinrank)
    (ν : ℕ) (x : ↥(maximalIdeal R ^ ν)) :
    ((associatedGradedEquiv hspan hlen).symm
      (AssociatedGraded.mk (maximalIdeal R) ν x)).IsHomogeneous ν := by
  rw [associatedGradedEquiv_def]
  exact IsWeaklyRegular.isHomogeneous_associatedGradedEquiv_symm_mk _ hspan ν x

/-- The inverse parameter comparison sends a parameter class to its variable. -/
@[simp]
theorem associatedGradedEquiv_symm_mk_one {rs : List R}
    (hspan : ofList rs = maximalIdeal R) (hlen : rs.length ≤ (maximalIdeal R).spanFinrank)
    (i : Fin rs.length) :
    (associatedGradedEquiv hspan hlen).symm (AssociatedGraded.mk (maximalIdeal R) 1
      ⟨rs[(i : ℕ)], by rw [pow_one, ← hspan]; exact subset_span (List.getElem_mem _)⟩) =
        MvPolynomial.X i := by
  rw [associatedGradedEquiv_def]
  exact IsWeaklyRegular.associatedGradedEquiv_symm_mk_one _ hspan i

/-- The inverse parameter comparison sends a homogeneous value class to its residue form. -/
@[simp]
theorem associatedGradedEquiv_symm_mk_eval {rs : List R}
    (hspan : ofList rs = maximalIdeal R) (hlen : rs.length ≤ (maximalIdeal R).spanFinrank)
    {ν : ℕ} {F : MvPolynomial (Fin rs.length) R} (hF : F.IsHomogeneous ν) :
    (associatedGradedEquiv hspan hlen).symm (AssociatedGraded.mk (maximalIdeal R) ν
      ⟨F.eval (fun i : Fin rs.length ↦ rs[(i : ℕ)]), hF.eval_mem_pow
        (fun i : Fin rs.length ↦ by rw [← hspan]; exact subset_span (List.getElem_mem _))⟩) =
        F.map (residue R) := by
  rw [associatedGradedEquiv_def]
  exact IsWeaklyRegular.associatedGradedEquiv_symm_mk_eval _ hspan hF

/-- The associated graded ring of the maximal ideal of a regular local ring is a domain. -/
instance isDomain_associatedGraded : IsDomain (maximalIdeal R).AssociatedGraded := by
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (maximalIdeal R).fg_of_isNoetherianRing
  have hofList : ofList s.toList = maximalIdeal R := by simpa [ofList] using hspan
  exact (associatedGradedEquiv hofList (by simp [hcard])).symm.toMulEquiv.isDomain

/-- **Initial forms multiply.** In a regular local ring, if `x ∈ 𝔪ʳ \ 𝔪ʳ⁺¹` and
`y ∈ 𝔪ˢ \ 𝔪ˢ⁺¹`, then `x * y ∉ 𝔪ʳ⁺ˢ⁺¹`: the initial form of `x * y` is the nonzero product of
the initial forms of `x` and `y`. -/
theorem mul_notMem_maximalIdeal_pow_succ {x y : R} {r s : ℕ} (hx : x ∈ maximalIdeal R ^ r)
    (hx' : x ∉ maximalIdeal R ^ (r + 1)) (hy : y ∈ maximalIdeal R ^ s)
    (hy' : y ∉ maximalIdeal R ^ (s + 1)) : x * y ∉ maximalIdeal R ^ (r + s + 1) :=
  AssociatedGraded.mul_notMem_pow_succ hx hx' hy hy'

end TauCeti.IsRegularLocalRing
