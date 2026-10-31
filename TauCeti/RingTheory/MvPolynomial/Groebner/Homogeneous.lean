/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.RingTheory.MvPolynomial.Groebner.Finite
public import TauCeti.RingTheory.MvPolynomial.Groebner.NormalForm
public import TauCeti.RingTheory.MvPolynomial.Groebner.Reduced

/-!
# Gröbner bases of homogeneous ideals

Let `w : σ → M` be a weight with values in an additive commutative monoid, which grades
`MvPolynomial σ R` by `MvPolynomial.weightedHomogeneousSubmodule R w` (for `w = 1` this is the
grading by total degree), and let `m` be any monomial order. The leading monomial of `f` lies in
the weighted homogeneous component of `f` of weight `weight w (m.degree f)`, and that component
has the same leading term as `f`
(`MonomialOrder.leadingTerm_weightedHomogeneousComponent_weight_degree`). So for an ideal `I`
which is homogeneous for this grading, replacing each member of a Gröbner basis by this component
gives a Gröbner basis of `I` consisting of weighted homogeneous polynomials, the reduced monic
Gröbner basis of `I` consists of weighted homogeneous polynomials, and the normal form modulo `I`
preserves weighted homogeneous components.

Consequently the image of each weighted homogeneous piece in the quotient `MvPolynomial σ R ⧸ I`
has a basis of the standard monomials of that weight. Since an ideal and its ideal of leading
terms have the same standard monomials, this piece is linearly isomorphic to the corresponding
piece for the ideal of leading terms: over a field, every graded piece of the quotient has the same
dimension as for the initial monomial ideal. No monomial order is assumed to be compatible with
the weight.

## Main results

* `MonomialOrder.IsGroebnerBasis.image_weightedHomogeneousComponent`: the weighted homogeneous
  components containing the leading monomials of the members of a Gröbner basis of a homogeneous
  ideal form a Gröbner basis of the same ideal.
* `MonomialOrder.isHomogeneous_iff_exists_isGroebnerBasis_isWeightedHomogeneous`: an ideal is
  homogeneous if and only if it has a Gröbner basis of weighted homogeneous polynomials, and
  `MonomialOrder.exists_finset_isGroebnerBasis_isWeightedHomogeneous` provides a finite one over a
  Noetherian ring in finitely many variables.
* `MonomialOrder.IsReducedGroebnerBasis.isWeightedHomogeneous`: the members of the reduced monic
  Gröbner basis of a homogeneous ideal are weighted homogeneous.
* `MonomialOrder.IsGroebnerBasis.normalForm_weightedHomogeneousComponent`: the normal form
  commutes with weighted homogeneous components.
* `MonomialOrder.IsGroebnerBasis.basisMapWeightedHomogeneousSubmodule`: the standard monomials of
  weight `n` give a basis of the image of the weight `n` piece in the quotient.
* `MonomialOrder.IsGroebnerBasis.mapWeightedHomogeneousSubmoduleEquivSpanLeadingTerm` and
  `MonomialOrder.finrank_map_weightedHomogeneousSubmodule_span_leadingTerm`: these pieces are the
  same for `I` and for its ideal of leading terms.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 8, §3, Theorem 2
  (reduced Gröbner bases of homogeneous ideals), and Chapter 9, §3, Proposition 9 (the Hilbert
  function of an ideal and of its ideal of leading terms).
* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, University Lecture Series 8, AMS, 1996,
  Chapter 1.
-/

public section

namespace MonomialOrder

open MvPolynomial Finsupp

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {σ R M : Type*} [AddCommMonoid M] {m : MonomialOrder σ} (w : σ → M)

section CommSemiring

variable [CommSemiring R]

variable [DecidableEq M] {w} {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}

/-- Let `I` be homogeneous for the grading by the weight `w`. Replacing each member `g` of a
Gröbner basis of `I` by its weighted homogeneous component of the weight of its leading monomial
gives a Gröbner basis of `I`. -/
theorem IsGroebnerBasis.image_weightedHomogeneousComponent
    (hI : I.IsHomogeneous (weightedHomogeneousSubmodule R w)) (h : m.IsGroebnerBasis G I) :
    m.IsGroebnerBasis ((fun g ↦ weightedHomogeneousComponent w (weight w (m.degree g)) g) '' G)
      I := by
  refine .mk ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact weightedHomogeneousComponent_mem_of_mem R w hI (h.subset hg) _
  · rw [Set.image_image]
    simpa using h.span_leadingTerm_image

/-- An ideal which is homogeneous for the grading by the weight `w` has a Gröbner basis
consisting of weighted homogeneous polynomials. -/
theorem exists_isGroebnerBasis_isWeightedHomogeneous
    (hI : I.IsHomogeneous (weightedHomogeneousSubmodule R w)) :
    ∃ G, m.IsGroebnerBasis G I ∧ ∀ g ∈ G, IsWeightedHomogeneous w g (weight w (m.degree g)) :=
  ⟨_, (isGroebnerBasis_self I).image_weightedHomogeneousComponent hI, by
    rintro _ ⟨g, -, rfl⟩
    exact m.isWeightedHomogeneous_weightedHomogeneousComponent_weight_degree w g⟩

/-- The ideal of leading terms is homogeneous for the grading by every weight. -/
theorem isHomogeneous_span_leadingTerm (w : σ → M) (I : Ideal (MvPolynomial σ R)) :
    (Ideal.span (m.leadingTerm '' I)).IsHomogeneous (weightedHomogeneousSubmodule R w) :=
  Ideal.homogeneous_span _ _ <| by
    rintro _ ⟨p, -, rfl⟩
    exact ⟨_, isWeightedHomogeneous_monomial w _ _ rfl⟩

end CommSemiring

section CommRing

variable [CommRing R] [DecidableEq M] {w} {G : Set (MvPolynomial σ R)}
  {I : Ideal (MvPolynomial σ R)}

/-- An ideal with a Gröbner basis consisting of weighted homogeneous polynomials is homogeneous. -/
theorem IsGroebnerBasis.isHomogeneous (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, ∃ n, IsWeightedHomogeneous w g n) :
    I.IsHomogeneous (weightedHomogeneousSubmodule R w) := by
  rw [h.ideal_eq_span]
  exact Ideal.homogeneous_span _ _ hG

/-- **Gröbner bases of homogeneous ideals.** An ideal is homogeneous for the grading by the weight
`w` if and only if it has a Gröbner basis consisting of weighted homogeneous polynomials. -/
theorem isHomogeneous_iff_exists_isGroebnerBasis_isWeightedHomogeneous :
    I.IsHomogeneous (weightedHomogeneousSubmodule R w) ↔
      ∃ G, m.IsGroebnerBasis G I ∧ ∀ g ∈ G, IsWeightedHomogeneous w g (weight w (m.degree g)) :=
  ⟨exists_isGroebnerBasis_isWeightedHomogeneous, fun ⟨_, h, hG⟩ ↦
    h.isHomogeneous fun g hg ↦ ⟨_, hG g hg⟩⟩

/-- Over a Noetherian ring in finitely many variables, an ideal which is homogeneous for the
grading by the weight `w` has a finite Gröbner basis consisting of weighted homogeneous
polynomials. -/
theorem exists_finset_isGroebnerBasis_isWeightedHomogeneous [IsNoetherianRing R] [Finite σ]
    (hI : I.IsHomogeneous (weightedHomogeneousSubmodule R w)) :
    ∃ G : Finset (MvPolynomial σ R), m.IsGroebnerBasis G I ∧
      ∀ g ∈ G, IsWeightedHomogeneous w g (weight w (m.degree g)) := by
  classical
  obtain ⟨G, hG⟩ := m.exists_finset_isGroebnerBasis I
  refine ⟨G.image fun g ↦ weightedHomogeneousComponent w (weight w (m.degree g)) g, ?_, ?_⟩
  · rw [Finset.coe_image]
    exact hG.image_weightedHomogeneousComponent hI
  · intro g hg
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hg
    exact m.isWeightedHomogeneous_weightedHomogeneousComponent_weight_degree w g

/-- The members of a reduced monic Gröbner basis of an ideal which is homogeneous for the grading by
the weight `w` are weighted homogeneous. -/
theorem IsReducedGroebnerBasis.isWeightedHomogeneous (hG : m.IsReducedGroebnerBasis G I)
    (hI : I.IsHomogeneous (weightedHomogeneousSubmodule R w)) {g : MvPolynomial σ R}
    (hg : g ∈ G) : IsWeightedHomogeneous w g (weight w (m.degree g)) := by
  set φ := fun g : MvPolynomial σ R ↦ weightedHomogeneousComponent w (weight w (m.degree g)) g
  -- The weighted homogeneous components `φ g` again form a reduced monic Gröbner basis of `I`,
  -- so by uniqueness they are the members of `G`.
  have hφ : m.IsReducedGroebnerBasis (φ '' G) I := by
    refine ⟨hG.isGroebnerBasis.image_weightedHomogeneousComponent hI, ?_, ?_, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      rw [← m.leadingCoeff_ne_zero_iff, leadingCoeff_weightedHomogeneousComponent_weight_degree,
        m.leadingCoeff_ne_zero_iff]
      exact hG.ne_zero g hg
    · rintro _ ⟨g, hg, rfl⟩
      exact (m.leadingCoeff_weightedHomogeneousComponent_weight_degree w g).trans (hG.monic g hg)
    · classical
      rintro _ ⟨g, hg, rfl⟩ c hc _ ⟨h, hh, rfl⟩ hne
      rw [degree_weightedHomogeneousComponent_weight_degree]
      rw [support_weightedHomogeneousComponent] at hc
      exact hG.not_degree_le g hg c (Finset.mem_filter.1 hc).1 h hh (by rintro rfl; exact hne rfl)
  obtain ⟨g, -, rfl⟩ := (hG.eq hφ ▸ hg : g ∈ φ '' G)
  exact m.isWeightedHomogeneous_weightedHomogeneousComponent_weight_degree w g

variable (h : m.IsGroebnerBasis G I) (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
  (hI : I.IsHomogeneous (weightedHomogeneousSubmodule R w))

include h hG hI

/-- For an ideal which is homogeneous for the grading by the weight `w`, the normal form commutes
with taking weighted homogeneous components. -/
theorem IsGroebnerBasis.normalForm_weightedHomogeneousComponent (n : M) (f : MvPolynomial σ R) :
    h.normalForm hG (weightedHomogeneousComponent w n f) =
      weightedHomogeneousComponent w n (h.normalForm hG f) := by
  classical
  refine (h.normalForm_eq_iff hG).2 ⟨?_, ?_⟩
  · have hf := (mem_restrictSupport_iff R).1 (h.normalForm_mem_restrictSupport hG f)
    rw [mem_restrictSupport_iff, support_weightedHomogeneousComponent, Finset.coe_filter]
    exact fun c hc ↦ hf hc.1
  · rw [← map_sub]
    exact weightedHomogeneousComponent_mem_of_mem R w hI (h.sub_normalForm_mem hG f) n

/-- For an ideal which is homogeneous for the grading by the weight `w`, the normal form of a
weighted homogeneous polynomial is weighted homogeneous of the same weight. -/
theorem IsGroebnerBasis.isWeightedHomogeneous_normalForm {n : M} {f : MvPolynomial σ R}
    (hf : IsWeightedHomogeneous w f n) : IsWeightedHomogeneous w (h.normalForm hG f) n := by
  rw [← weightedHomogeneousComponent_eq_self hf, h.normalForm_weightedHomogeneousComponent hG hI]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

/-- For an ideal `I` which is homogeneous for the grading by the weight `w`, the quotient map
restricts to a linear isomorphism from the polynomials supported on the standard monomials of `I`
of weight `n` onto the image in `MvPolynomial σ R ⧸ I` of the weighted homogeneous polynomials of
weight `n`. -/
noncomputable def IsGroebnerBasis.restrictSupportEquivMapWeightedHomogeneousSubmodule (n : M) :
    restrictSupport R (m.standardMonomials I ∩ {c | weight w c = n}) ≃ₗ[R]
      (weightedHomogeneousSubmodule R w n).map (Ideal.Quotient.mkₐ R I).toLinearMap :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict
      ((weightedHomogeneousSubmodule R w n).map (Ideal.Quotient.mkₐ R I).toLinearMap)
      ((Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ Submodule.subtype _)
      fun r ↦ Submodule.mem_map_of_mem <| by
        rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
        exact restrictSupport_mono R Set.inter_subset_right r.2)
    ⟨fun r₁ r₂ hr ↦ Subtype.ext <| eq_of_sub_mem_of_mem_restrictSupport
        (restrictSupport_mono R Set.inter_subset_left r₁.2)
        (restrictSupport_mono R Set.inter_subset_left r₂.2)
        (Ideal.Quotient.eq.1 (congrArg Subtype.val hr)),
      by
        rintro ⟨_, f, hf, rfl⟩
        refine ⟨⟨h.normalForm hG f, ?_⟩, Subtype.ext (h.mk_normalForm hG f)⟩
        have h₁ := (mem_restrictSupport_iff R).1 (h.normalForm_mem_restrictSupport hG f)
        have h₂ :=
          h.isWeightedHomogeneous_normalForm hG hI ((mem_weightedHomogeneousSubmodule ..).1 hf)
        rw [mem_restrictSupport_iff]
        exact fun c hc ↦ ⟨h₁ hc, h₂ (MvPolynomial.mem_support_iff.1 hc)⟩⟩

/-- `MonomialOrder.IsGroebnerBasis.restrictSupportEquivMapWeightedHomogeneousSubmodule` is the
quotient map. -/
@[simp]
theorem IsGroebnerBasis.restrictSupportEquivMapWeightedHomogeneousSubmodule_apply_coe (n : M)
    (r : restrictSupport R (m.standardMonomials I ∩ {c | weight w c = n})) :
    (h.restrictSupportEquivMapWeightedHomogeneousSubmodule hG hI n r : MvPolynomial σ R ⧸ I) =
      Ideal.Quotient.mk I (r : MvPolynomial σ R) :=
  (rfl)

/-- The inverse of
`MonomialOrder.IsGroebnerBasis.restrictSupportEquivMapWeightedHomogeneousSubmodule` sends the
class of `f` to the normal form of `f`. -/
@[simp]
theorem IsGroebnerBasis.coe_restrictSupportEquivMapWeightedHomogeneousSubmodule_symm_mk (n : M)
    {f : MvPolynomial σ R}
    (hf : Ideal.Quotient.mk I f ∈
      (weightedHomogeneousSubmodule R w n).map (Ideal.Quotient.mkₐ R I).toLinearMap) :
    ((h.restrictSupportEquivMapWeightedHomogeneousSubmodule hG hI n).symm
        ⟨Ideal.Quotient.mk I f, hf⟩ : MvPolynomial σ R) = h.normalForm hG f := by
  set r := (h.restrictSupportEquivMapWeightedHomogeneousSubmodule hG hI n).symm
    ⟨Ideal.Quotient.mk I f, hf⟩
  have hr := congrArg Subtype.val
    ((h.restrictSupportEquivMapWeightedHomogeneousSubmodule hG hI n).apply_symm_apply
      ⟨Ideal.Quotient.mk I f, hf⟩)
  rw [restrictSupportEquivMapWeightedHomogeneousSubmodule_apply_coe] at hr
  exact ((h.normalForm_eq_iff hG).2
    ⟨restrictSupport_mono R Set.inter_subset_left r.2, Ideal.Quotient.eq.1 hr.symm⟩).symm

/-- **The graded standard monomial basis.** For an ideal `I` which is homogeneous for the grading
by the weight `w`, the images of the standard monomials of `I` of weight `n` form a basis of the
image in `MvPolynomial σ R ⧸ I` of the weighted homogeneous polynomials of weight `n`. -/
noncomputable def IsGroebnerBasis.basisMapWeightedHomogeneousSubmodule (n : M) :
    Module.Basis ↥(m.standardMonomials I ∩ {c | weight w c = n}) R
      ((weightedHomogeneousSubmodule R w n).map (Ideal.Quotient.mkₐ R I).toLinearMap) :=
  (basisRestrictSupport R _).map (h.restrictSupportEquivMapWeightedHomogeneousSubmodule hG hI n)

/-- The basis vectors of `MonomialOrder.IsGroebnerBasis.basisMapWeightedHomogeneousSubmodule` are
the classes of the standard monomials. -/
@[simp]
theorem IsGroebnerBasis.basisMapWeightedHomogeneousSubmodule_apply_coe (n : M)
    (c : ↥(m.standardMonomials I ∩ {c | weight w c = n})) :
    (h.basisMapWeightedHomogeneousSubmodule hG hI n c : MvPolynomial σ R ⧸ I) =
      Ideal.Quotient.mk I (monomial (c : σ →₀ ℕ) 1) := by
  simp [basisMapWeightedHomogeneousSubmodule]

/-- The coordinates of a class in
`MonomialOrder.IsGroebnerBasis.basisMapWeightedHomogeneousSubmodule` are the coefficients of the
normal form of any representative. -/
@[simp]
theorem IsGroebnerBasis.basisMapWeightedHomogeneousSubmodule_repr_mk (n : M)
    {f : MvPolynomial σ R}
    (hf : Ideal.Quotient.mk I f ∈
      (weightedHomogeneousSubmodule R w n).map (Ideal.Quotient.mkₐ R I).toLinearMap)
    (c : ↥(m.standardMonomials I ∩ {c | weight w c = n})) :
    (h.basisMapWeightedHomogeneousSubmodule hG hI n).repr ⟨Ideal.Quotient.mk I f, hf⟩ c =
      (h.normalForm hG f).coeff c := by
  simp [basisMapWeightedHomogeneousSubmodule]

/-- **The Hilbert function of the ideal of leading terms.** For an ideal `I` which is homogeneous
for the grading by the weight `w`, the images of the weighted homogeneous polynomials of weight `n`
in `MvPolynomial σ R ⧸ I` and in the quotient by the ideal of leading terms of `I` are linearly
isomorphic. -/
noncomputable def IsGroebnerBasis.mapWeightedHomogeneousSubmoduleEquivSpanLeadingTerm (n : M) :
    (weightedHomogeneousSubmodule R w n).map (Ideal.Quotient.mkₐ R I).toLinearMap ≃ₗ[R]
      (weightedHomogeneousSubmodule R w n).map
        (Ideal.Quotient.mkₐ R (Ideal.span (m.leadingTerm '' I))).toLinearMap :=
  (h.restrictSupportEquivMapWeightedHomogeneousSubmodule hG hI n).symm ≪≫ₗ
    LinearEquiv.ofEq _ _ (by rw [standardMonomials_span_leadingTerm]) ≪≫ₗ
    (h.image_leadingTerm hG).restrictSupportEquivMapWeightedHomogeneousSubmodule
      (isUnit_leadingCoeff_of_mem_image_leadingTerm hG) (isHomogeneous_span_leadingTerm w I) n

/-- `MonomialOrder.IsGroebnerBasis.mapWeightedHomogeneousSubmoduleEquivSpanLeadingTerm` sends the
class of `f` modulo `I` to the class of the normal form of `f` modulo the ideal of leading terms. -/
@[simp]
theorem IsGroebnerBasis.mapWeightedHomogeneousSubmoduleEquivSpanLeadingTerm_apply_coe (n : M)
    {f : MvPolynomial σ R}
    (hf : Ideal.Quotient.mk I f ∈
      (weightedHomogeneousSubmodule R w n).map (Ideal.Quotient.mkₐ R I).toLinearMap) :
    (h.mapWeightedHomogeneousSubmoduleEquivSpanLeadingTerm hG hI n ⟨Ideal.Quotient.mk I f, hf⟩ :
        MvPolynomial σ R ⧸ Ideal.span (m.leadingTerm '' (I : Set (MvPolynomial σ R)))) =
      Ideal.Quotient.mk (Ideal.span (m.leadingTerm '' I)) (h.normalForm hG f) := by
  simp [mapWeightedHomogeneousSubmoduleEquivSpanLeadingTerm]

/-- The inverse of
`MonomialOrder.IsGroebnerBasis.mapWeightedHomogeneousSubmoduleEquivSpanLeadingTerm` sends the
class of `f` modulo the ideal of leading terms to the class modulo `I` of the normal form of `f`
for the leading terms of `G`. -/
@[simp]
theorem IsGroebnerBasis.mapWeightedHomogeneousSubmoduleEquivSpanLeadingTerm_symm_apply_coe (n : M)
    {f : MvPolynomial σ R}
    (hf : Ideal.Quotient.mk (Ideal.span (m.leadingTerm '' (I : Set (MvPolynomial σ R)))) f ∈
      (weightedHomogeneousSubmodule R w n).map
        (Ideal.Quotient.mkₐ R (Ideal.span (m.leadingTerm '' I))).toLinearMap) :
    ((h.mapWeightedHomogeneousSubmoduleEquivSpanLeadingTerm hG hI n).symm
        ⟨Ideal.Quotient.mk (Ideal.span (m.leadingTerm '' (I : Set (MvPolynomial σ R)))) f, hf⟩ :
          MvPolynomial σ R ⧸ I) =
      Ideal.Quotient.mk I
        ((h.image_leadingTerm hG).normalForm
          (isUnit_leadingCoeff_of_mem_image_leadingTerm hG) f) := by
  simp [mapWeightedHomogeneousSubmoduleEquivSpanLeadingTerm]

end CommRing

section Field

variable {k : Type*} [Field k] [DecidableEq M] {w} {I : Ideal (MvPolynomial σ k)}

/-- Over a field, for an ideal `I` which is homogeneous for the grading by the weight `w`, the
dimension of the image in `MvPolynomial σ k ⧸ I` of the weighted homogeneous polynomials of weight
`n` is the number of standard monomials of `I` of weight `n`. -/
theorem finrank_map_weightedHomogeneousSubmodule (m : MonomialOrder σ)
    (hI : I.IsHomogeneous (weightedHomogeneousSubmodule k w)) (n : M) :
    Module.finrank k
        ((weightedHomogeneousSubmodule k w n).map (Ideal.Quotient.mkₐ k I).toLinearMap) =
      Nat.card ↥(m.standardMonomials I ∩ {c | weight w c = n}) :=
  Module.finrank_eq_nat_card_basis <| (isGroebnerBasis_self I).basisMapWeightedHomogeneousSubmodule
    (fun _ _ hg ↦ m.isUnit_leadingCoeff.2 hg) hI n

/-- Over a field, an ideal `I` which is homogeneous for the grading by the weight `w` and its ideal
of leading terms have quotients whose weighted homogeneous pieces have the same dimensions. -/
theorem finrank_map_weightedHomogeneousSubmodule_span_leadingTerm
    (hI : I.IsHomogeneous (weightedHomogeneousSubmodule k w)) (n : M) :
    Module.finrank k ((weightedHomogeneousSubmodule k w n).map
        (Ideal.Quotient.mkₐ k (Ideal.span (m.leadingTerm '' I))).toLinearMap) =
      Module.finrank k
        ((weightedHomogeneousSubmodule k w n).map (Ideal.Quotient.mkₐ k I).toLinearMap) :=
  ((isGroebnerBasis_self I).mapWeightedHomogeneousSubmoduleEquivSpanLeadingTerm
    (fun _ _ hg ↦ m.isUnit_leadingCoeff.2 hg) hI n).finrank_eq.symm

end Field

end MonomialOrder
