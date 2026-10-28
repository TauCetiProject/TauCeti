/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Groebner
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Remainders and Gröbner bases

Let `m` be a monomial order on `σ →₀ ℕ`. This file defines remainders on division by a set of
multivariate polynomials, and Gröbner bases of an ideal, and proves that remainders on division by
a Gröbner basis decide ideal membership.

* `MonomialOrder.IsRemainder m f B r`: `r` is a remainder of `f` on division by `B`, i.e.
  `f = ∑ g_b * b + r` where each product `g_b * b` has degree at most that of `f`, and no monomial
  of `r` is divisible by the leading monomial of a nonzero `b ∈ B`. The degree condition is
  stated with `MonomialOrder.withBotDegree`, so that the zero polynomial has degree `⊥`, and as
  the inequality `deg b + deg g_b ≤ deg f`; the remainder condition only concerns divisibility,
  not a comparison of degrees.
* `MonomialOrder.IsGroebnerBasis m G I`: `G` is a subset of the ideal `I` whose leading terms
  span the same ideal as the leading terms of all elements of `I`.

## Main results

* `MonomialOrder.exists_isRemainder`: remainders exist when every nonzero divisor has a unit
  leading coefficient; this is `MonomialOrder.div_set`.
* `MonomialOrder.IsGroebnerBasis.exists_degree_le_degree`: the leading monomial of every nonzero
  element of `I` is divisible by the leading monomial of a nonzero element of a Gröbner basis.
* `MonomialOrder.isGroebnerBasis_iff_forall_exists_degree_le_degree`: the converse, for a family
  whose nonzero members have unit leading coefficients.
* `MonomialOrder.IsGroebnerBasis.sub_mem_iff`: for remainders `r₁`, `r₂` of `f₁`, `f₂` on division
  by a Gröbner basis of `I`, `f₁ - f₂ ∈ I` if and only if `r₁ = r₂`. In particular remainders on
  division by a Gröbner basis are unique (`MonomialOrder.IsGroebnerBasis.eq_of_isRemainder`) and
  a remainder vanishes exactly on `I` (`MonomialOrder.IsGroebnerBasis.remainder_eq_zero_iff_mem`).
* `MonomialOrder.IsGroebnerBasis.ideal_eq_span`: a Gröbner basis generates its ideal.
* `MonomialOrder.isGroebnerBasis_iff_isRemainder_zero`: `G ⊆ I` is a Gröbner basis of `I` if and
  only if every element of `I` has remainder `0` on division by `G`.

None of these results assume that the coefficients form a field: the statements needing division
assume that the nonzero members of the divisor set have unit leading coefficients, which over a
field is discharged by `MonomialOrder.isUnit_leadingCoeff`.

## References

The definitions `IsRemainder` and `IsGroebnerBasis` are those of Junyu Guo and Hao Shen in
Mathlib pull request 29203, upstreamed from the WuProver Gröbner basis project.

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 2, §§5–6.
-/

public section

namespace MonomialOrder

open MvPolynomial

variable {σ R : Type*} (m : MonomialOrder σ)

section CommSemiring

variable [CommSemiring R]

/-- `r` is a remainder of `f` on division by the set `B` for the monomial order `m`: there is a
finitely supported family `g : B →₀ MvPolynomial σ R` such that

1. `f = ∑ g_b * b + r`;
2. for each `b ∈ B`, `deg b + deg g_b ≤ deg f`, degrees being taken in `WithBot` so that the zero
   polynomial has degree `⊥`;
3. no monomial of `r` is divisible by the leading monomial of a nonzero `b ∈ B`. -/
def IsRemainder (f : MvPolynomial σ R) (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
    Prop :=
  (∃ g : B →₀ MvPolynomial σ R,
    f = Finsupp.linearCombination _ (fun b : B ↦ (b : MvPolynomial σ R)) g + r ∧
    ∀ b : B, m.toWithBotSyn (m.withBotDegree (b : MvPolynomial σ R)) +
      m.toWithBotSyn (m.withBotDegree (g b)) ≤ m.toWithBotSyn (m.withBotDegree f)) ∧
  ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ m.degree b ≤ c

/-- A subset `G` of an ideal `I` is a Gröbner basis of `I` for the monomial order `m` if the
leading terms of the elements of `G` span the same ideal as the leading terms of all elements
of `I`. -/
def IsGroebnerBasis (G : Set (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R)) : Prop :=
  G ⊆ I ∧ Ideal.span (m.leadingTerm '' I) = Ideal.span (m.leadingTerm '' G)

variable {m} {f r : MvPolynomial σ R} {B G G' : Set (MvPolynomial σ R)}
  {I : Ideal (MvPolynomial σ R)}

/-- Unfolding lemma for `MonomialOrder.IsRemainder`. -/
theorem isRemainder_iff : m.IsRemainder f B r ↔
    (∃ g : B →₀ MvPolynomial σ R,
      f = Finsupp.linearCombination _ (fun b : B ↦ (b : MvPolynomial σ R)) g + r ∧
      ∀ b : B, m.toWithBotSyn (m.withBotDegree (b : MvPolynomial σ R)) +
        m.toWithBotSyn (m.withBotDegree (g b)) ≤ m.toWithBotSyn (m.withBotDegree f)) ∧
    ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ m.degree b ≤ c :=
  Iff.rfl

/-- The division representation of a remainder: `f = ∑ g_b * b + r` with
`deg b + deg g_b ≤ deg f` for each `b ∈ B`. -/
theorem IsRemainder.exists_linearCombination (h : m.IsRemainder f B r) :
    ∃ g : B →₀ MvPolynomial σ R,
      f = Finsupp.linearCombination _ (fun b : B ↦ (b : MvPolynomial σ R)) g + r ∧
      ∀ b : B, m.toWithBotSyn (m.withBotDegree (b : MvPolynomial σ R)) +
        m.toWithBotSyn (m.withBotDegree (g b)) ≤ m.toWithBotSyn (m.withBotDegree f) :=
  h.1

/-- No monomial of a remainder is divisible by the leading monomial of a nonzero divisor. -/
theorem IsRemainder.not_degree_le (h : m.IsRemainder f B r) {c : σ →₀ ℕ} (hc : c ∈ r.support)
    {b : MvPolynomial σ R} (hb : b ∈ B) (hb0 : b ≠ 0) : ¬ m.degree b ≤ c :=
  h.2 c hc b hb hb0

/-- Unfolding lemma for `MonomialOrder.IsGroebnerBasis`. -/
theorem isGroebnerBasis_iff : m.IsGroebnerBasis G I ↔
    G ⊆ I ∧ Ideal.span (m.leadingTerm '' I) = Ideal.span (m.leadingTerm '' G) :=
  Iff.rfl

/-- A subset of `I` whose leading terms span the ideal of leading terms of `I` is a Gröbner basis
of `I`. -/
theorem IsGroebnerBasis.mk (hGI : G ⊆ I)
    (hspan : Ideal.span (m.leadingTerm '' I) = Ideal.span (m.leadingTerm '' G)) :
    m.IsGroebnerBasis G I :=
  ⟨hGI, hspan⟩

/-- For nonzero `p`, `q` and `f`, the `WithBot` degree bound `deg p + deg q ≤ deg f` used in
`MonomialOrder.IsRemainder` is the corresponding bound on `MonomialOrder.degree`. -/
theorem toWithBotSyn_withBotDegree_add_le_iff {p q : MvPolynomial σ R} (hp : p ≠ 0) (hq : q ≠ 0)
    (hf : f ≠ 0) :
    m.toWithBotSyn (m.withBotDegree p) + m.toWithBotSyn (m.withBotDegree q) ≤
        m.toWithBotSyn (m.withBotDegree f) ↔
      m.toSyn (m.degree p) + m.toSyn (m.degree q) ≤ m.toSyn (m.degree f) := by
  simp [(m.withBotDegree_eq_coe_degree_iff _).2, toWithBotSyn_apply_coe, ← WithBot.coe_add, *]

/-- The remainders of `0` are exactly `0`. -/
@[simp]
theorem isRemainder_zero_left_iff : m.IsRemainder 0 B r ↔ r = 0 := by
  refine ⟨fun ⟨⟨g, hg, hdeg⟩, _⟩ ↦ ?_, fun hr ↦ ⟨⟨0, by simp [hr], by simp⟩, by simp [hr]⟩⟩
  -- Each product `g b * b` vanishes, since its degree is bounded by the degree `⊥` of `0`.
  have hgb (b : B) : g b • (b : MvPolynomial σ R) = 0 := by
    have := hdeg b
    simp only [withBotDegree_zero, toWithBotSyn_apply_bot, le_bot_iff, WithBot.add_eq_bot,
      toWithBotSyn_apply_eq_bot_iff, withBotDegree_eq_bot_iff] at this
    rcases this with h | h <;> simp [h]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_eq_zero fun b _ ↦ hgb b,
    zero_add] at hg
  exact hg.symm

/-- A polynomial is a remainder of itself on division by `B` exactly when none of its monomials is
divisible by the leading monomial of a nonzero element of `B`. -/
theorem isRemainder_self_iff :
    m.IsRemainder r B r ↔ ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ m.degree b ≤ c :=
  ⟨And.right, fun h ↦ ⟨⟨0, by simp, by simp⟩, h⟩⟩

/-- If `0` is a remainder of a nonzero `f` on division by `B`, then the leading monomial of `f` is
divisible by the leading monomial of a nonzero element of `B`. -/
theorem exists_degree_le_degree_of_isRemainder_zero (h : m.IsRemainder f B 0) (hf : f ≠ 0) :
    ∃ b ∈ B, b ≠ 0 ∧ m.degree b ≤ m.degree f := by
  classical
  obtain ⟨g, hfg, hdeg⟩ := h.exists_linearCombination
  rw [add_zero, Finsupp.linearCombination_apply, Finsupp.sum] at hfg
  have hmem : m.degree f ∈ (∑ b ∈ g.support, g b • (b : MvPolynomial σ R)).support := by
    rw [← hfg]
    exact m.degree_mem_support hf
  obtain ⟨b, -, hb⟩ := Finset.mem_biUnion.1 (support_sum hmem)
  rw [smul_eq_mul] at hb
  have hgb0 : g b ≠ 0 := fun h ↦ by simp [h] at hb
  have hb0 : (b : MvPolynomial σ R) ≠ 0 := fun h ↦ by simp [h] at hb
  -- The degree condition gives `deg b + deg g_b ≤ deg f`, and `deg f` is a monomial of
  -- `g_b * b`, so the two sides are equal.
  have hle := (toWithBotSyn_withBotDegree_add_le_iff hb0 hgb0 hf).1 (hdeg b)
  have hge : m.toSyn (m.degree f) ≤
      m.toSyn (m.degree (b : MvPolynomial σ R)) + m.toSyn (m.degree (g b)) :=
    (m.le_degree hb).trans (m.toSyn_degree_mul_le.trans_eq (add_comm _ _))
  have heq : m.degree f = m.degree (b : MvPolynomial σ R) + m.degree (g b) :=
    m.toSyn.injective (by rw [map_add]; exact le_antisymm hge hle)
  exact ⟨b, b.2, hb0, heq ▸ le_self_add⟩

/-- Every monomial of an element of the ideal spanned by the leading terms of `G` is divisible by
the leading monomial of a nonzero element of `G`. -/
theorem exists_degree_le_of_mem_span_leadingTerm {p : MvPolynomial σ R}
    (hp : p ∈ Ideal.span (m.leadingTerm '' G)) {c : σ →₀ ℕ} (hc : c ∈ p.support) :
    ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ c := by
  have hle : Ideal.span (m.leadingTerm '' G) ≤
      Ideal.span ((fun d ↦ monomial d (1 : R)) '' (m.degree '' (G \ {0}))) := by
    rw [← m.span_leadingTerm_sdiff_singleton_zero, Ideal.span_le, Set.image_subset_iff]
    intro g hg
    rw [Set.mem_preimage, SetLike.mem_coe, ← C_mul_leadingCoeff_monomial_degree]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨m.degree g, ⟨g, hg, rfl⟩, rfl⟩)
  obtain ⟨_, ⟨g, ⟨hgG, hg0⟩, rfl⟩, hgc⟩ := mem_ideal_span_monomial_image.1 (hle hp) c hc
  exact ⟨g, hgG, by simpa using hg0, hgc⟩

/-- A Gröbner basis of `I` is contained in `I`. -/
theorem IsGroebnerBasis.subset (h : m.IsGroebnerBasis G I) : G ⊆ I :=
  h.1

/-- The leading terms of a Gröbner basis of `I` span the ideal of leading terms of `I`. -/
theorem IsGroebnerBasis.span_leadingTerm_image (h : m.IsGroebnerBasis G I) :
    Ideal.span (m.leadingTerm '' I) = Ideal.span (m.leadingTerm '' G) :=
  h.2

/-- An ideal is a Gröbner basis of itself. -/
theorem isGroebnerBasis_self (I : Ideal (MvPolynomial σ R)) : m.IsGroebnerBasis (I : Set _) I :=
  .mk subset_rfl rfl

/-- Adjoining further elements of `I` to a Gröbner basis of `I` gives a Gröbner basis of `I`. -/
theorem IsGroebnerBasis.mono (h : m.IsGroebnerBasis G I) (hGG' : G ⊆ G') (hG'I : G' ⊆ I) :
    m.IsGroebnerBasis G' I :=
  .mk hG'I <| le_antisymm
    (h.span_leadingTerm_image.le.trans (Ideal.span_mono (Set.image_mono hGG')))
    (Ideal.span_mono (Set.image_mono hG'I))

/-- Removing `0` does not change whether a set is a Gröbner basis. -/
@[simp]
theorem isGroebnerBasis_sdiff_singleton_zero :
    m.IsGroebnerBasis (G \ {0}) I ↔ m.IsGroebnerBasis G I := by
  simp only [isGroebnerBasis_iff, m.span_leadingTerm_sdiff_singleton_zero,
    Set.sdiff_singleton_subset_iff, Set.insert_eq_of_mem (show (0 : MvPolynomial σ R) ∈ (I : Set _)
      from I.zero_mem)]

/-- The leading monomial of every nonzero element of `I` is divisible by the leading monomial of a
nonzero element of a Gröbner basis of `I`. -/
theorem IsGroebnerBasis.exists_degree_le_degree (h : m.IsGroebnerBasis G I)
    {p : MvPolynomial σ R} (hp : p ∈ I) (hp0 : p ≠ 0) :
    ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ m.degree p := by
  refine exists_degree_le_of_mem_span_leadingTerm
    (h.span_leadingTerm_image ▸ Ideal.subset_span ⟨p, hp, rfl⟩ : m.leadingTerm p ∈ _) ?_
  rw [m.support_leadingTerm' hp0]
  exact Finset.mem_singleton_self _

/-- A subset `G` of `I` whose nonzero members have unit leading coefficients is a Gröbner basis of
`I` if and only if the leading monomial of every nonzero element of `I` is divisible by the
leading monomial of a nonzero element of `G`. -/
theorem isGroebnerBasis_iff_forall_exists_degree_le_degree
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis G I ↔
      G ⊆ I ∧ ∀ p ∈ I, p ≠ 0 → ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ m.degree p := by
  refine ⟨fun h ↦ ⟨h.subset, fun p hp hp0 ↦ h.exists_degree_le_degree hp hp0⟩,
    fun ⟨hGI, hdeg⟩ ↦ .mk hGI (le_antisymm ?_ (Ideal.span_mono (Set.image_mono hGI)))⟩
  rw [Ideal.span_le, Set.image_subset_iff]
  intro p hp
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  obtain ⟨g, hgG, hg0, hgp⟩ := hdeg p hp hp0
  -- `lt p = (lc p / lc g) X^(deg p - deg g) * lt g`.
  have hu := hG g hgG hg0
  have hlt : m.leadingTerm p = monomial (m.degree p - m.degree g)
      (m.leadingCoeff p * ↑hu.unit⁻¹) * m.leadingTerm g := by
    simp [leadingTerm, monomial_mul_monomial, tsub_add_cancel_of_le hgp, mul_assoc]
  rw [Set.mem_preimage, SetLike.mem_coe, hlt]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g, hgG, rfl⟩)

end CommSemiring

section CommRing

variable [CommRing R] {m} {f f₁ f₂ r r₁ r₂ : MvPolynomial σ R} {B G : Set (MvPolynomial σ R)}
  {I : Ideal (MvPolynomial σ R)}

/-- A polynomial differs from its remainders by an element of the ideal spanned by the divisors. -/
theorem IsRemainder.sub_mem_span (h : m.IsRemainder f B r) : f - r ∈ Ideal.span B := by
  obtain ⟨g, hf, -⟩ := h.exists_linearCombination
  rw [hf, add_sub_cancel_right, Finsupp.linearCombination_apply]
  exact Submodule.sum_mem _ fun b _ ↦ Submodule.smul_mem _ _ (Ideal.subset_span b.2)

/-- **Existence of remainders.** If every nonzero element of `B` has a unit leading coefficient,
then every polynomial has a remainder on division by `B`. -/
theorem exists_isRemainder (hB : ∀ b ∈ B, b ≠ 0 → IsUnit (m.leadingCoeff b))
    (f : MvPolynomial σ R) : ∃ r, m.IsRemainder f B r := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · exact ⟨0, isRemainder_zero_left_iff.2 rfl⟩
  -- Divide by the nonzero elements of `B`, then extend the quotients by `0` to all of `B`.
  obtain ⟨g, r, hfgr, hdeg, hr⟩ := m.div_set (B := B \ {0}) (fun b hb ↦ hB b hb.1 hb.2) f
  refine ⟨r, ⟨g.mapDomain (Set.inclusion Set.sdiff_subset), ?_, fun b ↦ ?_⟩,
    fun c hc b hb hb0 ↦ hr c hc b ⟨hb, hb0⟩⟩
  · rwa [Finsupp.linearCombination_mapDomain]
  by_cases hb0 : (b : MvPolynomial σ R) = 0
  · simp [hb0]
  have hgb : g.mapDomain (Set.inclusion Set.sdiff_subset) b = g ⟨b, b.2, hb0⟩ :=
    Finsupp.mapDomain_apply_of_injective (Set.inclusion_injective _) g ⟨b, b.2, hb0⟩
  rw [hgb, ← map_add, ← withBotDegree_mul_of_left_mem_nonZeroDivisors
    (hB b b.2 hb0).mem_nonZeroDivisors, withBotDegree_le_withBotDegree_iff]
  exact ⟨hdeg ⟨b, b.2, hb0⟩, fun h ↦ absurd h hf⟩

/-- **Remainders modulo a Gröbner basis.** If `r₁` and `r₂` are remainders of `f₁` and `f₂` on
division by a Gröbner basis of `I`, then `f₁ - f₂ ∈ I` if and only if `r₁ = r₂`. -/
theorem IsGroebnerBasis.sub_mem_iff (h : m.IsGroebnerBasis G I) (h₁ : m.IsRemainder f₁ G r₁)
    (h₂ : m.IsRemainder f₂ G r₂) : f₁ - f₂ ∈ I ↔ r₁ = r₂ := by
  classical
  have hdiff : f₁ - f₂ - (r₁ - r₂) ∈ I := by
    have := Ideal.span_le.2 h.subset (Ideal.sub_mem _ h₁.sub_mem_span h₂.sub_mem_span)
    rwa [sub_sub_sub_comm] at this
  rw [← sub_add_cancel (f₁ - f₂) (r₁ - r₂), I.add_mem_iff_right hdiff]
  refine ⟨fun hr ↦ by_contra fun hne ↦ ?_, fun hr ↦ by simp [hr]⟩
  -- The leading monomial of the nonzero `r₁ - r₂ ∈ I` would be a reducible monomial of `r₁`
  -- or `r₂`.
  have hne' : r₁ - r₂ ≠ 0 := sub_ne_zero.2 hne
  obtain ⟨g, hgG, hg0, hgd⟩ := h.exists_degree_le_degree hr hne'
  rcases Finset.mem_union.1 (support_sub σ r₁ r₂ (m.degree_mem_support hne')) with hc | hc
  · exact h₁.not_degree_le hc hgG hg0 hgd
  · exact h₂.not_degree_le hc hgG hg0 hgd

/-- **Uniqueness of remainders.** Remainders on division by a Gröbner basis are unique. -/
theorem IsGroebnerBasis.eq_of_isRemainder (h : m.IsGroebnerBasis G I) (h₁ : m.IsRemainder f G r₁)
    (h₂ : m.IsRemainder f G r₂) : r₁ = r₂ :=
  (h.sub_mem_iff h₁ h₂).1 (by simp)

/-- **Ideal membership.** A remainder on division by a Gröbner basis of `I` vanishes if and only
if the divided polynomial lies in `I`. -/
theorem IsGroebnerBasis.remainder_eq_zero_iff_mem (h : m.IsGroebnerBasis G I)
    (hr : m.IsRemainder f G r) : r = 0 ↔ f ∈ I := by
  simpa using (h.sub_mem_iff hr (isRemainder_zero_left_iff.2 rfl)).symm

/-- For a Gröbner basis of `I` whose nonzero members have unit leading coefficients, `0` is a
remainder of `f` exactly when `f ∈ I`. -/
theorem IsGroebnerBasis.isRemainder_zero_iff_mem (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) : m.IsRemainder f G 0 ↔ f ∈ I := by
  refine ⟨fun hr ↦ (h.remainder_eq_zero_iff_mem hr).1 rfl, fun hf ↦ ?_⟩
  obtain ⟨r, hr⟩ := exists_isRemainder hG f
  rwa [(h.remainder_eq_zero_iff_mem hr).2 hf] at hr

/-- A Gröbner basis of `I` whose nonzero members have unit leading coefficients generates `I`. -/
theorem IsGroebnerBasis.ideal_eq_span (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) : I = Ideal.span G := by
  refine le_antisymm (fun f hf ↦ ?_) (Ideal.span_le.2 h.subset)
  simpa using ((h.isRemainder_zero_iff_mem hG).2 hf).sub_mem_span

/-- Remainders on division by a Gröbner basis whose nonzero members have unit leading
coefficients exist and are unique. -/
theorem IsGroebnerBasis.existsUnique_isRemainder (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) (f : MvPolynomial σ R) :
    ∃! r, m.IsRemainder f G r :=
  (exists_isRemainder hG f).elim fun r hr ↦ ⟨r, hr, fun _ hr' ↦ h.eq_of_isRemainder hr' hr⟩

/-- A subset `G` of `I` whose nonzero members have unit leading coefficients is a Gröbner basis of
`I` if and only if every element of `I` has remainder `0` on division by `G`. -/
theorem isGroebnerBasis_iff_isRemainder_zero (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis G I ↔ G ⊆ I ∧ ∀ f ∈ I, m.IsRemainder f G 0 := by
  refine ⟨fun h ↦ ⟨h.subset, fun f hf ↦ (h.isRemainder_zero_iff_mem hG).2 hf⟩, fun ⟨hGI, h0⟩ ↦ ?_⟩
  exact (isGroebnerBasis_iff_forall_exists_degree_le_degree hG).2
    ⟨hGI, fun p hp hp0 ↦ exists_degree_le_degree_of_isRemainder_zero (h0 p hp) hp0⟩

end CommRing

end MonomialOrder
