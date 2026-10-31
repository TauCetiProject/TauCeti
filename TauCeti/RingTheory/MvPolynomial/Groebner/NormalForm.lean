/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Groebner.Basic
public import TauCeti.RingTheory.MvPolynomial.RestrictSupport

/-!
# Standard monomials and normal forms

Let `m` be a monomial order on `σ →₀ ℕ` and `I` an ideal of `MvPolynomial σ R`. The *standard
monomials* of `I` are the exponents that are not divisible by the leading monomial of any nonzero
element of `I`. This file proves that the standard monomials give an `R`-basis of the quotient
`MvPolynomial σ R ⧸ I` as soon as `I` has a Gröbner basis whose nonzero members have unit leading
coefficients, and constructs the corresponding linear normal-form map.

* `MonomialOrder.standardMonomials m I`: the standard monomials of `I`.
* `MonomialOrder.IsGroebnerBasis.restrictSupportEquivQuotient`: the polynomials supported on the
  standard monomials of `I` are linearly isomorphic to `MvPolynomial σ R ⧸ I` through the quotient
  map.
* `MonomialOrder.IsGroebnerBasis.basisQuotient`: the images of the standard monomials form a basis
  of `MvPolynomial σ R ⧸ I`.
* `MonomialOrder.IsGroebnerBasis.normalForm`: the `R`-linear map sending `f` to the unique
  polynomial supported on the standard monomials that is congruent to `f` modulo `I`.

## Main results

* `MonomialOrder.disjoint_restrictSupport_standardMonomials`: no nonzero polynomial supported on
  the standard monomials of `I` lies in `I`. This holds for every ideal, with no Gröbner basis.
* `MonomialOrder.IsGroebnerBasis.normalForm_eq_iff`: `normalForm f` is characterized as the
  polynomial supported on the standard monomials that is congruent to `f` modulo `I`.
* `MonomialOrder.IsGroebnerBasis.isRemainder_iff_eq_normalForm`: the remainders of `f` on division
  by the Gröbner basis are exactly its normal form.
* `MonomialOrder.IsGroebnerBasis.ker_normalForm`, `MonomialOrder.IsGroebnerBasis.range_normalForm`,
  `MonomialOrder.IsGroebnerBasis.normalForm_normalForm` and
  `MonomialOrder.IsGroebnerBasis.normalForm_normalForm_mul`: the normal form is an idempotent
  linear map with kernel `I`, image the polynomials supported on the standard monomials, and
  compatible with multiplication in the quotient.

Over a field every ideal `I` is a Gröbner basis of itself (`MonomialOrder.isGroebnerBasis_self`)
and every nonzero polynomial has a unit leading coefficient (`MonomialOrder.isUnit_leadingCoeff`),
so the results above apply to every ideal.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 2, §6, Proposition 1,
  and Chapter 5, §3, Proposition 1.
-/

public section

namespace MonomialOrder

open MvPolynomial

variable {σ R : Type*} (m : MonomialOrder σ)

section CommSemiring

variable [CommSemiring R]

/-- The standard monomials of the ideal `I` for the monomial order `m`: the exponents that are not
divisible by the leading monomial of any nonzero element of `I`. -/
def standardMonomials (I : Ideal (MvPolynomial σ R)) : Set (σ →₀ ℕ) :=
  {c | ∀ p ∈ I, p ≠ 0 → ¬ m.degree p ≤ c}

variable {m} {I : Ideal (MvPolynomial σ R)} {G : Set (MvPolynomial σ R)} {c : σ →₀ ℕ}
  {f r : MvPolynomial σ R}

/-- An exponent is a standard monomial of `I` when it is not divisible by the leading monomial of
any nonzero element of `I`. -/
@[simp]
theorem mem_standardMonomials_iff :
    c ∈ m.standardMonomials I ↔ ∀ p ∈ I, p ≠ 0 → ¬ m.degree p ≤ c :=
  Iff.rfl

/-- The standard monomials of `I` are the exponents not divisible by the leading monomial of a
nonzero element of a Gröbner basis of `I`. -/
theorem IsGroebnerBasis.mem_standardMonomials_iff (h : m.IsGroebnerBasis G I) :
    c ∈ m.standardMonomials I ↔ ∀ g ∈ G, g ≠ 0 → ¬ m.degree g ≤ c := by
  rw [MonomialOrder.mem_standardMonomials_iff]
  refine ⟨fun hc g hg ↦ hc g (h.subset hg), fun hc p hp hp0 hpc ↦ ?_⟩
  obtain ⟨g, hgG, hg0, hgp⟩ := h.exists_degree_le_degree hp hp0
  exact hc g hgG hg0 (hgp.trans hpc)

/-- A polynomial is its own remainder on division by a Gröbner basis of `I` exactly when it is
supported on the standard monomials of `I`. -/
theorem IsGroebnerBasis.isRemainder_self_iff (h : m.IsGroebnerBasis G I) :
    m.IsRemainder r G r ↔ r ∈ restrictSupport R (m.standardMonomials I) := by
  simp_rw [MonomialOrder.isRemainder_self_iff, mem_restrictSupport_iff, Set.subset_def,
    Finset.mem_coe, h.mem_standardMonomials_iff]

/-- Every remainder on division by a Gröbner basis of `I` is supported on the standard monomials
of `I`. -/
theorem IsGroebnerBasis.mem_restrictSupport_of_isRemainder (h : m.IsGroebnerBasis G I)
    (hr : m.IsRemainder f G r) : r ∈ restrictSupport R (m.standardMonomials I) :=
  h.isRemainder_self_iff.1 <| MonomialOrder.isRemainder_self_iff.2 fun _ hc _ hb hb0 ↦
    hr.not_degree_le hc hb hb0

variable (m I) in
/-- No nonzero polynomial supported on the standard monomials of `I` lies in `I`. -/
theorem disjoint_restrictSupport_standardMonomials :
    Disjoint (restrictSupport R (m.standardMonomials I)) (I.restrictScalars R) := by
  refine Submodule.disjoint_def.2 fun p hp hpI ↦ by_contra fun hp0 ↦ ?_
  exact mem_standardMonomials_iff.1 ((mem_restrictSupport_iff R).1 hp (m.degree_mem_support hp0))
    p ((Submodule.restrictScalars_mem _ _ _).1 hpI) hp0 le_rfl

end CommSemiring

section CommRing

variable [CommRing R] {m} {I : Ideal (MvPolynomial σ R)} {G : Set (MvPolynomial σ R)}
  {f g r r₁ r₂ : MvPolynomial σ R}

/-- Two polynomials supported on the standard monomials of `I` that are congruent modulo `I` are
equal. -/
theorem eq_of_sub_mem_of_mem_restrictSupport
    (hr₁ : r₁ ∈ restrictSupport R (m.standardMonomials I))
    (hr₂ : r₂ ∈ restrictSupport R (m.standardMonomials I)) (hr : r₁ - r₂ ∈ I) : r₁ = r₂ :=
  sub_eq_zero.1 <| Submodule.disjoint_def.1 (disjoint_restrictSupport_standardMonomials m I) _
    (Submodule.sub_mem _ hr₁ hr₂) hr

/-- Given a Gröbner basis of `I` whose nonzero members have unit leading coefficients, every
polynomial is congruent modulo `I` to a polynomial supported on the standard monomials of `I`. -/
theorem IsGroebnerBasis.exists_mem_restrictSupport_sub_mem (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) (f : MvPolynomial σ R) :
    ∃ r ∈ restrictSupport R (m.standardMonomials I), f - r ∈ I := by
  obtain ⟨r, hr⟩ := exists_isRemainder hG f
  exact ⟨r, h.mem_restrictSupport_of_isRemainder hr, Ideal.span_le.2 h.subset hr.sub_mem_span⟩

/-- Given a Gröbner basis of `I` whose nonzero members have unit leading coefficients, the
quotient map restricts to a linear isomorphism from the polynomials supported on the standard
monomials of `I` onto `MvPolynomial σ R ⧸ I`. -/
noncomputable def IsGroebnerBasis.restrictSupportEquivQuotient (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    restrictSupport R (m.standardMonomials I) ≃ₗ[R] MvPolynomial σ R ⧸ I :=
  LinearEquiv.ofBijective
    ((Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ (restrictSupport R (m.standardMonomials I)).subtype)
    ⟨fun r₁ r₂ hr ↦ Subtype.ext <| eq_of_sub_mem_of_mem_restrictSupport r₁.2 r₂.2 <|
        Ideal.Quotient.eq.1 hr,
      fun x ↦ by
        obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
        obtain ⟨r, hr, hfr⟩ := h.exists_mem_restrictSupport_sub_mem hG f
        exact ⟨⟨r, hr⟩, (Ideal.Quotient.eq.2 hfr).symm⟩⟩

/-- `MonomialOrder.IsGroebnerBasis.restrictSupportEquivQuotient` is the quotient map. -/
@[simp]
theorem IsGroebnerBasis.restrictSupportEquivQuotient_apply (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (r : restrictSupport R (m.standardMonomials I)) :
    h.restrictSupportEquivQuotient hG r = Ideal.Quotient.mk I (r : MvPolynomial σ R) :=
  (rfl)

/-- **The standard monomial basis.** Given a Gröbner basis of `I` whose nonzero members have unit
leading coefficients, the images of the standard monomials of `I` form an `R`-basis of
`MvPolynomial σ R ⧸ I`. -/
noncomputable def IsGroebnerBasis.basisQuotient (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    Module.Basis (m.standardMonomials I) R (MvPolynomial σ R ⧸ I) :=
  (basisRestrictSupport R _).map (h.restrictSupportEquivQuotient hG)

@[simp]
theorem IsGroebnerBasis.basisQuotient_apply (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) (c : m.standardMonomials I) :
    h.basisQuotient hG c = Ideal.Quotient.mk I (monomial (c : σ →₀ ℕ) 1) := by
  simp [basisQuotient]

/-- **The normal form** modulo an ideal `I` with a Gröbner basis whose nonzero members have unit
leading coefficients: the `R`-linear map sending `f` to the unique polynomial supported on the
standard monomials of `I` that is congruent to `f` modulo `I`
(`MonomialOrder.IsGroebnerBasis.normalForm_eq_iff`). -/
noncomputable def IsGroebnerBasis.normalForm (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (restrictSupport R (m.standardMonomials I)).subtype ∘ₗ
    (h.restrictSupportEquivQuotient hG).symm.toLinearMap ∘ₗ (Ideal.Quotient.mkₐ R I).toLinearMap

/-- The inverse of `MonomialOrder.IsGroebnerBasis.restrictSupportEquivQuotient` sends the class
of `f` to the normal form of `f`. -/
@[simp]
theorem IsGroebnerBasis.coe_restrictSupportEquivQuotient_symm_mk (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) (f : MvPolynomial σ R) :
    ((h.restrictSupportEquivQuotient hG).symm (Ideal.Quotient.mk I f) : MvPolynomial σ R) =
      h.normalForm hG f :=
  (rfl)

variable (h : m.IsGroebnerBasis G I) (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))

include h hG

/-- The normal form is supported on the standard monomials. -/
@[simp]
theorem IsGroebnerBasis.normalForm_mem_restrictSupport (f : MvPolynomial σ R) :
    h.normalForm hG f ∈ restrictSupport R (m.standardMonomials I) :=
  h.coe_restrictSupportEquivQuotient_symm_mk hG f ▸
    ((h.restrictSupportEquivQuotient hG).symm (Ideal.Quotient.mk I f)).2

/-- A polynomial and its normal form have the same image in the quotient. -/
@[simp]
theorem IsGroebnerBasis.mk_normalForm (f : MvPolynomial σ R) :
    Ideal.Quotient.mk I (h.normalForm hG f) = Ideal.Quotient.mk I f := by
  rw [← h.restrictSupportEquivQuotient_apply hG ⟨_, h.normalForm_mem_restrictSupport hG f⟩]
  exact (h.restrictSupportEquivQuotient hG).apply_symm_apply _

/-- A polynomial is congruent to its normal form modulo `I`. -/
@[simp]
theorem IsGroebnerBasis.sub_normalForm_mem (f : MvPolynomial σ R) : f - h.normalForm hG f ∈ I :=
  Ideal.Quotient.eq.1 (h.mk_normalForm hG f).symm

/-- **Characterization of the normal form.** The normal form of `f` is the unique polynomial
supported on the standard monomials of `I` that is congruent to `f` modulo `I`. -/
theorem IsGroebnerBasis.normalForm_eq_iff :
    h.normalForm hG f = r ↔ r ∈ restrictSupport R (m.standardMonomials I) ∧ f - r ∈ I := by
  refine ⟨fun hr ↦ hr ▸ ⟨h.normalForm_mem_restrictSupport hG f, h.sub_normalForm_mem hG f⟩,
    fun ⟨hr, hfr⟩ ↦ eq_of_sub_mem_of_mem_restrictSupport (h.normalForm_mem_restrictSupport hG f)
      hr ?_⟩
  simpa using I.sub_mem hfr (h.sub_normalForm_mem hG f)

/-- A polynomial supported on the standard monomials is its own normal form. -/
@[simp]
theorem IsGroebnerBasis.normalForm_of_mem_restrictSupport
    (hr : r ∈ restrictSupport R (m.standardMonomials I)) : h.normalForm hG r = r :=
  (h.normalForm_eq_iff hG).2 ⟨hr, by simp⟩

/-- The normal form is idempotent. -/
theorem IsGroebnerBasis.normalForm_normalForm (f : MvPolynomial σ R) :
    h.normalForm hG (h.normalForm hG f) = h.normalForm hG f :=
  h.normalForm_of_mem_restrictSupport hG (h.normalForm_mem_restrictSupport hG f)

/-- Two polynomials have the same normal form if and only if they are congruent modulo `I`. -/
theorem IsGroebnerBasis.normalForm_eq_normalForm_iff :
    h.normalForm hG f = h.normalForm hG g ↔ f - g ∈ I := by
  rw [← Ideal.Quotient.eq, ← h.mk_normalForm hG f, ← h.mk_normalForm hG g]
  refine ⟨fun hfg ↦ hfg ▸ rfl, fun hfg ↦ eq_of_sub_mem_of_mem_restrictSupport
    (h.normalForm_mem_restrictSupport hG f) (h.normalForm_mem_restrictSupport hG g)
    (Ideal.Quotient.eq.1 hfg)⟩

/-- **Ideal membership.** The normal form of `f` vanishes if and only if `f ∈ I`. -/
@[simp]
theorem IsGroebnerBasis.normalForm_eq_zero_iff : h.normalForm hG f = 0 ↔ f ∈ I := by
  simpa using h.normalForm_eq_normalForm_iff hG (g := 0)

/-- The kernel of the normal form is `I`. -/
@[simp]
theorem IsGroebnerBasis.ker_normalForm : LinearMap.ker (h.normalForm hG) = I.restrictScalars R :=
  Submodule.ext fun _ ↦ by
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, h.normalForm_eq_zero_iff hG]

/-- The range of the normal form consists of the polynomials supported on the standard monomials
of `I`. -/
@[simp]
theorem IsGroebnerBasis.range_normalForm :
    LinearMap.range (h.normalForm hG) = restrictSupport R (m.standardMonomials I) :=
  le_antisymm (by rintro _ ⟨f, rfl⟩; exact h.normalForm_mem_restrictSupport hG f)
    fun r hr ↦ ⟨r, h.normalForm_of_mem_restrictSupport hG hr⟩

/-- Reducing the left factor of a product to normal form does not change the normal form of the
product. -/
@[simp]
theorem IsGroebnerBasis.normalForm_normalForm_mul (f g : MvPolynomial σ R) :
    h.normalForm hG (h.normalForm hG f * g) = h.normalForm hG (f * g) :=
  (h.normalForm_eq_normalForm_iff hG).2 <| by
    rw [← sub_mul]
    exact I.mul_mem_right g (by simpa using I.neg_mem (h.sub_normalForm_mem hG f))

/-- Reducing the right factor of a product to normal form does not change the normal form of the
product. -/
@[simp]
theorem IsGroebnerBasis.normalForm_mul_normalForm (f g : MvPolynomial σ R) :
    h.normalForm hG (f * h.normalForm hG g) = h.normalForm hG (f * g) := by
  rw [mul_comm, normalForm_normalForm_mul, mul_comm]

/-- The coordinates of a class in the standard monomial basis are the coefficients of the normal
form of any representative. -/
@[simp]
theorem IsGroebnerBasis.basisQuotient_repr_mk (f : MvPolynomial σ R) (c : m.standardMonomials I) :
    (h.basisQuotient hG).repr (Ideal.Quotient.mk I f) c = (h.normalForm hG f).coeff c := by
  simp [basisQuotient]

/-- The remainders of `f` on division by a Gröbner basis of `I` whose nonzero members have unit
leading coefficients are exactly the normal form of `f`. -/
theorem IsGroebnerBasis.isRemainder_iff_eq_normalForm :
    m.IsRemainder f G r ↔ r = h.normalForm hG f := by
  have key {r : MvPolynomial σ R} (hr : m.IsRemainder f G r) : r = h.normalForm hG f :=
    ((h.normalForm_eq_iff hG).2 ⟨h.mem_restrictSupport_of_isRemainder hr,
      Ideal.span_le.2 h.subset hr.sub_mem_span⟩).symm
  refine ⟨key, ?_⟩
  rintro rfl
  obtain ⟨r, hr⟩ := exists_isRemainder hG f
  rwa [← key hr]

end CommRing

end MonomialOrder
