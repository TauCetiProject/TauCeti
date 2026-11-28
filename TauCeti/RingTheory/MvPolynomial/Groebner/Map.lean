/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Groebner.Buchberger
public import TauCeti.RingTheory.MvPolynomial.Groebner.NormalForm
public import TauCeti.RingTheory.MvPolynomial.Groebner.Reduced

/-!
# Gröbner bases under an injective change of coefficients

Let `m` be a monomial order on `σ →₀ ℕ` and let `φ : R →+* S` be an injective ring homomorphism,
for instance a field extension `k → K`. The coefficient map `MvPolynomial.map φ` does not change
supports, so it preserves leading monomials and commutes with leading coefficients, leading
terms and S-polynomials. It therefore carries remainders to remainders, and, by Buchberger's
criterion, a Gröbner basis `G` of an ideal `I` to a Gröbner basis `map φ '' G` of the extended
ideal `I.map (map φ)`, provided the nonzero members of `G` have unit leading coefficients.

So extending the coefficients changes neither Gröbner bases nor ideals of leading terms: the ideal
of leading terms of the extended ideal is the extension of the ideal of leading terms of `I`, and
the extended ideal contracts back to `I`. Over a field this holds for every ideal, since every
ideal is a Gröbner basis of itself and every nonzero polynomial has a unit leading coefficient.

The same holds for the data computed from a Gröbner basis. The image of a reduced monic Gröbner
basis of `I` is the reduced monic Gröbner basis of the extended ideal, the standard monomials of
`I` and of its extension agree, and the normal form of the image of `f` modulo the extended ideal
is the image of the normal form of `f` modulo `I`. In particular, the quotient map
`R[σ] ⧸ I → S[σ] ⧸ I.map (map φ)` sends the standard-monomial basis to the standard-monomial
basis. For weight-initial ideals, see `Ideal.weightInitialIdeal_map`.

## Main results

* `MonomialOrder.IsRemainder.map`: if `r` is a remainder of `f` on division by `B`, then
  `map φ r` is a remainder of `map φ f` on division by `map φ '' B`.
* `MonomialOrder.IsGroebnerBasis.map`: the image of a Gröbner basis of `I` whose nonzero members
  have unit leading coefficients is a Gröbner basis of `I.map (map φ)`.
* `MonomialOrder.isGroebnerBasis_map_iff`: conversely, a subset `G ⊆ I` whose nonzero members have
  unit leading coefficients is a Gröbner basis of `I` as soon as its image is a Gröbner basis of
  `I.map (map φ)`.
* `MonomialOrder.IsGroebnerBasis.comap_map_eq`: an ideal with such a Gröbner basis is the
  contraction of its extension.
* `MonomialOrder.IsGroebnerBasis.span_leadingTerm_map` and, over a field,
  `MonomialOrder.span_leadingTerm_map`: the ideal of leading terms of the extension of `I` is the
  extension of the ideal of leading terms of `I`.
* `MonomialOrder.IsReducedGroebnerBasis.map` and `MonomialOrder.isReducedGroebnerBasis_map_iff`:
  a subset `G ⊆ I` is a reduced monic Gröbner basis of `I` if and only if its image is a reduced
  monic Gröbner basis of the extended ideal.
* `MonomialOrder.IsGroebnerBasis.standardMonomials_map` and, over a field,
  `MonomialOrder.standardMonomials_map`: the extended ideal has the same standard monomials as
  `I`.
* `MonomialOrder.IsGroebnerBasis.normalForm_map`: normal forms commute with the coefficient map.
* `MonomialOrder.IsGroebnerBasis.quotientMap_basisQuotient`: the induced map of quotients sends
  the standard-monomial basis to the standard-monomial basis.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 2, §6, Theorem 6
  (Buchberger's criterion), which shows that a Gröbner basis computation only involves the field
  of definition of the generators.
-/

public section

namespace MonomialOrder

open MvPolynomial

variable {σ R S : Type*} {m : MonomialOrder σ}

section CommSemiring

variable [CommSemiring R] [CommSemiring S] {φ : R →+* S} {f r : MvPolynomial σ R}
  {B : Set (MvPolynomial σ R)}

/-- An injective coefficient map carries a remainder of `f` on division by `B` to a remainder of
the image of `f` on division by the image of `B`. -/
theorem IsRemainder.map (hφ : Function.Injective φ) (h : m.IsRemainder f B r) :
    m.IsRemainder (MvPolynomial.map φ f) (MvPolynomial.map φ '' B) (MvPolynomial.map φ r) := by
  classical
  obtain ⟨g, hfg, hdeg⟩ := h.exists_linearCombination
  -- The quotient attached to `map φ b` is `map φ` of the quotient attached to `b`.
  let e : B → MvPolynomial.map φ '' B := fun b ↦ ⟨_, Set.mem_image_of_mem _ b.property⟩
  have he : Function.Injective e := fun b c hbc ↦
    Subtype.ext (map_injective φ hφ (congrArg Subtype.val hbc))
  let g' : B →₀ MvPolynomial σ S := g.mapRange (MvPolynomial.map φ) (map_zero _)
  refine isRemainder_iff.2 ⟨⟨g'.mapDomain e, ?_, ?_⟩, ?_⟩
  · rw [Finsupp.linearCombination_mapDomain, hfg, map_add, Finsupp.linearCombination_apply,
      Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp), map_finsuppSum]
    simp [e]
  · rintro ⟨_, b, hb, rfl⟩
    have hgb : g'.mapDomain e ⟨_, Set.mem_image_of_mem _ hb⟩ = MvPolynomial.map φ (g ⟨b, hb⟩) :=
      Finsupp.mapDomain_apply_of_injective he g' ⟨b, hb⟩
    simpa only [hgb, m.withBotDegree_map_of_injective hφ] using hdeg ⟨b, hb⟩
  · rintro c hc _ ⟨b, hb, rfl⟩ hb0
    rw [support_map_of_injective _ hφ] at hc
    rw [m.degree_map_of_injective hφ]
    exact h.not_degree_le hc hb fun h ↦ hb0 (by rw [h, map_zero])

end CommSemiring

section CommRing

variable [CommRing R] [CommRing S] {φ : R →+* S} {G : Set (MvPolynomial σ R)}
  {I : Ideal (MvPolynomial σ R)}

/-- **Extension of coefficients.** An injective coefficient map `φ` carries a Gröbner basis of `I`
whose nonzero members have unit leading coefficients to a Gröbner basis of the extended ideal
`I.map (map φ)`. -/
theorem IsGroebnerBasis.map (hφ : Function.Injective φ) (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis (MvPolynomial.map φ '' G) (I.map (MvPolynomial.map φ)) := by
  rw [h.ideal_eq_span, Ideal.map_span]
  refine isGroebnerBasis_span_of_isRemainder_sPolynomial_zero ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩ hg0
    rw [m.leadingCoeff_map_of_injective hφ]
    exact (hG g hg fun h ↦ hg0 (by rw [h, map_zero])).map φ
  rintro _ ⟨g₁, hg₁, rfl⟩ _ ⟨g₂, hg₂, rfl⟩
  have := (h.isRemainder_sPolynomial_zero hg₁ hg₂).map hφ
  rwa [map_zero, ← m.sPolynomial_map_of_injective hφ] at this

/-- Let `φ` be an injective coefficient map and let `G ⊆ I` have nonzero members with unit leading
coefficients. Then `G` is a Gröbner basis of `I` if and only if `map φ '' G` is a Gröbner basis of
the extended ideal `I.map (map φ)`. -/
theorem isGroebnerBasis_map_iff (hφ : Function.Injective φ)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) (hGI : G ⊆ I) :
    m.IsGroebnerBasis (map φ '' G) (I.map (map φ)) ↔ m.IsGroebnerBasis G I := by
  refine ⟨fun h ↦ (isGroebnerBasis_iff_forall_exists_degree_le_degree hG).2
    ⟨hGI, fun p hp hp0 ↦ ?_⟩, fun h ↦ h.map hφ hG⟩
  obtain ⟨_, ⟨g, hg, rfl⟩, hg0, hle⟩ := h.exists_degree_le_degree (Ideal.mem_map_of_mem _ hp)
    ((map_ne_zero_iff _ (map_injective φ hφ)).2 hp0)
  rw [m.degree_map_of_injective hφ, m.degree_map_of_injective hφ] at hle
  exact ⟨g, hg, fun h ↦ hg0 (by rw [h, map_zero]), hle⟩

/-- **Contraction of an extended ideal.** If `I` has a Gröbner basis whose nonzero members have
unit leading coefficients, then the extension of `I` along an injective coefficient map `φ`
contracts back to `I`: a polynomial over `R` lying in the ideal generated by `I` over `S` already
lies in `I`. -/
theorem IsGroebnerBasis.comap_map_eq (hφ : Function.Injective φ) (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    (I.map (MvPolynomial.map φ)).comap (MvPolynomial.map φ) = I := by
  refine le_antisymm (fun f hf ↦ ?_) Ideal.le_comap_map
  -- The image of a remainder of `f` is a remainder of `map φ f ∈ I.map (map φ)`, hence zero.
  obtain ⟨r, hr⟩ := exists_isRemainder hG f
  have hr0 := ((h.map hφ hG).remainder_eq_zero_iff_mem (hr.map hφ)).2 hf
  rw [map_eq_zero_iff _ (map_injective φ hφ)] at hr0
  exact (h.remainder_eq_zero_iff_mem hr).1 hr0

/-- **Leading terms of an extended ideal.** If `I` has a Gröbner basis whose nonzero members have
unit leading coefficients, then the ideal of leading terms of the extension of `I` along an
injective coefficient map `φ` is the extension of the ideal of leading terms of `I`. -/
theorem IsGroebnerBasis.span_leadingTerm_map (hφ : Function.Injective φ)
    (h : m.IsGroebnerBasis G I) (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    Ideal.span (m.leadingTerm '' (I.map (MvPolynomial.map φ) : Set (MvPolynomial σ S))) =
      (Ideal.span (m.leadingTerm '' I)).map (MvPolynomial.map φ) := by
  rw [(h.map hφ hG).span_leadingTerm_image, h.span_leadingTerm_image, Ideal.map_span,
    Set.image_image, Set.image_image]
  simp_rw [m.leadingTerm_map_of_injective hφ]

/-- **Leading terms under extension of a field of coefficients.** For a field `k` and a ring
homomorphism `φ : k →+* S`, for instance a field extension, the ideal of
leading terms of the extension of an ideal `I` of `k[σ]` is the extension of the ideal of leading
terms of `I`. -/
theorem span_leadingTerm_map {k : Type*} [Field k] (φ : k →+* S)
    (I : Ideal (MvPolynomial σ k)) :
    Ideal.span (m.leadingTerm '' (I.map (map φ) : Set (MvPolynomial σ S))) =
      (Ideal.span (m.leadingTerm '' I)).map (map φ) := by
  rcases subsingleton_or_nontrivial S with _ | _
  · exact Subsingleton.elim _ _
  · exact (isGroebnerBasis_self I).span_leadingTerm_map φ.injective
      fun _ _ ↦ m.isUnit_leadingCoeff.2

variable {H : Set (MvPolynomial σ S)}

/-- **Standard monomials of an extended ideal.** If `I` has a Gröbner basis whose nonzero members
have unit leading coefficients, then the extension of `I` along an injective coefficient map `φ`
has the same standard monomials as `I`. -/
theorem IsGroebnerBasis.standardMonomials_map (hφ : Function.Injective φ)
    (h : m.IsGroebnerBasis G I) (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    m.standardMonomials (I.map (MvPolynomial.map φ)) = m.standardMonomials I := by
  ext c
  rw [(h.map hφ hG).mem_standardMonomials_iff, h.mem_standardMonomials_iff]
  simp only [Set.forall_mem_image, ne_eq, map_eq_zero_iff _ (map_injective φ hφ),
    m.degree_map_of_injective hφ]

/-- **Standard monomials under extension of a field of coefficients.** For a field `k` and a ring
homomorphism `φ : k →+* S` to a nontrivial ring, for instance a field extension, the extension of
an ideal `I` of `k[σ]` has the same standard monomials as `I`. -/
@[simp]
theorem standardMonomials_map {k : Type*} [Field k] [Nontrivial S] (φ : k →+* S)
    (I : Ideal (MvPolynomial σ k)) :
    m.standardMonomials (I.map (map φ)) = m.standardMonomials I :=
  (isGroebnerBasis_self I).standardMonomials_map φ.injective fun _ _ ↦ m.isUnit_leadingCoeff.2

/-- **Normal forms commute with an injective change of coefficients.** Let `G` be a Gröbner basis
of `I` and `H` a Gröbner basis of the extended ideal `I.map (map φ)`, both with nonzero members
having unit leading coefficients. Then the normal form modulo the extended ideal of the image of
`f` is the image of the normal form of `f` modulo `I`.

Over a field `k` and an extension field `K`, this applies to every ideal, with `G = I` and
`H = I.map (map φ)` (`MonomialOrder.isGroebnerBasis_self`). -/
theorem IsGroebnerBasis.normalForm_map (hφ : Function.Injective φ) (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (h' : m.IsGroebnerBasis H (I.map (MvPolynomial.map φ)))
    (hH : ∀ g ∈ H, g ≠ 0 → IsUnit (m.leadingCoeff g)) (f : MvPolynomial σ R) :
    h'.normalForm hH (MvPolynomial.map φ f) = MvPolynomial.map φ (h.normalForm hG f) := by
  refine (h'.normalForm_eq_iff hH).2 ⟨?_, ?_⟩
  · rw [h.standardMonomials_map hφ hG, mem_restrictSupport_iff, support_map_of_injective _ hφ]
    exact (mem_restrictSupport_iff _).1 (h.normalForm_mem_restrictSupport hG f)
  · rw [← map_sub]
    exact Ideal.mem_map_of_mem _ (h.sub_normalForm_mem hG f)

/-- **The standard-monomial basis under an injective change of coefficients.** In the setting of
`MonomialOrder.IsGroebnerBasis.normalForm_map`, the map `R[σ] ⧸ I → S[σ] ⧸ I.map (map φ)` induced
by `φ` sends the basis vector of a standard monomial `c` of `I` to the basis vector of `c`, which
is a standard monomial of the extended ideal
(`MonomialOrder.IsGroebnerBasis.standardMonomials_map`). -/
theorem IsGroebnerBasis.quotientMap_basisQuotient (hφ : Function.Injective φ)
    (h : m.IsGroebnerBasis G I) (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (h' : m.IsGroebnerBasis H (I.map (MvPolynomial.map φ)))
    (hH : ∀ g ∈ H, g ≠ 0 → IsUnit (m.leadingCoeff g)) (c : m.standardMonomials I) :
    Ideal.quotientMap _ (MvPolynomial.map φ) Ideal.le_comap_map (h.basisQuotient hG c) =
      h'.basisQuotient hH ⟨c, by rw [h.standardMonomials_map hφ hG]; exact c.property⟩ := by
  simp

/-- **Reduced Gröbner bases under extension of coefficients.** An injective coefficient map `φ`
carries a reduced monic Gröbner basis of `I` to a reduced monic Gröbner basis of the extended
ideal `I.map (map φ)`. By uniqueness (`MonomialOrder.IsReducedGroebnerBasis.eq`), over a field the
image of the reduced Gröbner basis of `I` is the reduced Gröbner basis of the extended ideal. -/
theorem IsReducedGroebnerBasis.map (hφ : Function.Injective φ)
    (h : m.IsReducedGroebnerBasis G I) :
    m.IsReducedGroebnerBasis (MvPolynomial.map φ '' G) (I.map (MvPolynomial.map φ)) where
  isGroebnerBasis := h.isGroebnerBasis.map hφ fun g hg _ ↦ by
    rw [(h.monic g hg).leadingCoeff_eq_one]
    exact isUnit_one
  ne_zero := by
    rintro _ ⟨g, hg, rfl⟩
    exact (map_ne_zero_iff _ (map_injective φ hφ)).2 (h.ne_zero g hg)
  monic := by
    rintro _ ⟨g, hg, rfl⟩
    rw [Monic, m.leadingCoeff_map_of_injective hφ, (h.monic g hg).leadingCoeff_eq_one, map_one]
  not_degree_le := by
    rintro _ ⟨g, hg, rfl⟩ c hc _ ⟨g', hg', rfl⟩ hne
    rw [support_map_of_injective _ hφ] at hc
    rw [m.degree_map_of_injective hφ]
    exact h.not_degree_le g hg c hc g' hg' fun heq ↦ hne (by rw [heq])

/-- Let `φ` be an injective coefficient map. A subset `G ⊆ I` is a reduced monic Gröbner basis of
`I` if and only if its image is a reduced monic Gröbner basis of the extended ideal
`I.map (map φ)`. -/
theorem isReducedGroebnerBasis_map_iff (hφ : Function.Injective φ) (hGI : G ⊆ I) :
    m.IsReducedGroebnerBasis (MvPolynomial.map φ '' G) (I.map (MvPolynomial.map φ)) ↔
      m.IsReducedGroebnerBasis G I := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map hφ⟩
  have hmonic (g) (hg : g ∈ G) : m.Monic g := by
    apply hφ
    rw [map_one, ← m.leadingCoeff_map_of_injective hφ]
    exact h.monic _ (Set.mem_image_of_mem _ hg)
  refine ⟨(isGroebnerBasis_map_iff hφ (fun g hg _ ↦ ?_) hGI).1 h.isGroebnerBasis,
    fun g hg hg0 ↦ ?_, hmonic, fun g hg c hc g' hg' hne ↦ ?_⟩
  · rw [(hmonic g hg).leadingCoeff_eq_one]
    exact isUnit_one
  · exact h.ne_zero _ (Set.mem_image_of_mem _ hg) (by rw [hg0, map_zero])
  · have := h.not_degree_le _ (Set.mem_image_of_mem _ hg) c
      (by rwa [support_map_of_injective _ hφ]) _ (Set.mem_image_of_mem _ hg')
      ((map_injective φ hφ).ne hne)
    rwa [m.degree_map_of_injective hφ] at this

end CommRing

end MonomialOrder
