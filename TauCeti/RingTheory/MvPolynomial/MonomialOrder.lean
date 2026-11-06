/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-!
# Leading monomials for a monomial order

This file collects facts about leading monomials of multivariate polynomials for a monomial order
`m` on `σ →₀ ℕ`: comparisons of degrees with their `WithBot` forms, the degree of a monomial
multiple, the cancellation of leading terms by an S-polynomial, the behaviour of leading data
under a change of coefficients, leading data of the weighted homogeneous component containing
the leading monomial, the top weighted part of a binomial lifted by terms of lower weight, leading
data of renamed polynomials, elimination orders and the lexicographic ones among them, agreement
of leading exponents under two monomial orders, normalization to leading coefficient one over a
field, leading exponents of substitutions of nonzero families, leading data of substitutions of
monic families, cancellation of substituted monic binomials, and algebraic independence from
leading monomials.

The product `X^a * b`, normalized to leading coefficient one when `b` has a unit leading
coefficient, differs from another such product of the same degree by a monomial multiple of
their S-polynomial. This is the cancellation of leading terms behind Buchberger's criterion.

Let `yᵢ`, `i ∈ σ`, be polynomials in the variables `Xᵢ` over a ring without zero divisors. If the
leading monomial of each `yᵢ` is the variable `Xᵢ`, then the `yᵢ` are algebraically independent:
the image of a monomial `c X^d` under `Xᵢ ↦ yᵢ` has leading monomial `X^d`, so the images of the
distinct monomials of a nonzero polynomial have distinct leading monomials and cannot cancel.

This is the triangularity argument for a family such as `yₙ = cₙ Xₙ + qₙ(X₁, …, Xₙ₋₁)` with
`cₙ ≠ 0`, ordered lexicographically with the variables of larger index more significant, as for
the images of the generators of the Lazard ring in a polynomial ring.

## Main results

* `MonomialOrder.degree_eq_of_forall_lt`, `MonomialOrder.degree_eq_of_forall_mem_lt`: strict
  comparisons preserving the leading exponent, including comparisons on a set containing the
  support and original leading exponent.
* `MonomialOrder.leadingCoeff_eq_of_degree_eq`, `MonomialOrder.leadingTerm_eq_of_degree_eq`,
  `MonomialOrder.sPolynomial_eq_of_degree_eq`: orders agreeing on leading exponents also agree
  on the corresponding leading coefficients, leading terms and S-polynomials.
* `MonomialOrder.toWithBotSyn_withBotDegree_le_toSyn_degree`: the `WithBot` degree of a polynomial
  is at most its degree.
* `MonomialOrder.withBotDegree_sub_lt`: if `q` has degree at most that of `f ≠ 0` and the same
  coefficient of `X^(deg f)`, then `f - q` has smaller degree than `f`.
* `MvPolynomial.monomial_mem_iff_monomial_one_mem`: a set closed under scalar multiplication
  contains `c X^a` for a unit `c` if and only if it contains `X^a`.
* `MonomialOrder.leadingTerm_mem_iff`: a set closed under scalar multiplication contains the
  leading term of a polynomial with unit leading coefficient if and only if it contains its
  leading monomial.
* `MonomialOrder.toSyn_degree_monomial_mul_le`: `c X^a * b` has degree at most `a + deg b`.
* `MonomialOrder.monomial_one_mul_sub_smul_eq_monomial_mul_sPolynomial`: if `b₀` has a unit
  leading coefficient, then `X^a * b` minus `lc b` times the product of `b₀` of the same degree
  normalized to leading coefficient one is a monomial multiple of the S-polynomial
  `m.sPolynomial b b₀`.
* `MonomialOrder.degree_map_of_injective`, `MonomialOrder.leadingCoeff_map_of_injective`,
  `MonomialOrder.leadingTerm_map_of_injective`, `MonomialOrder.sPolynomial_map_of_injective`: an
  injective coefficient map `φ` preserves leading monomials and commutes with leading
  coefficients, leading terms and S-polynomials.
* `MonomialOrder.leadingTerm_weightedHomogeneousComponent_weight_degree`: the weighted
  homogeneous component of `f` containing its leading monomial has the leading term of `f`.
* `MonomialOrder.weightedHomogeneousComponent_monomial_sub_monomial_sub`,
  `MonomialOrder.linearCombination_le_of_mem_support_monomial_sub_monomial_sub`: for weights
  `A w = ∑ i, w i • a i`, if `A u = A v` and all exponents `w` of `Q` satisfy `A w ≺ A u`, then the
  part of `Y^u - Y^v - Q` of weight `A u` is `Y^u - Y^v`, and all its exponents `w` satisfy
  `A w ≼ A u`.
* `MonomialOrder.degree_rename`, `MonomialOrder.leadingCoeff_rename` and
  `MonomialOrder.leadingTerm_rename`: renaming the variables along a relabeling which carries one
  monomial order to another commutes with leading monomials, coefficients and terms; such a
  relabeling is injective by `MonomialOrder.injective_of_forall_toSyn_le_iff`.
* `MonomialOrder.exists_rename_eq_of_coe_support_degree_subset`: for an elimination order, a
  polynomial whose leading monomial only involves the variables `e τ` is a renamed polynomial.
* `MonomialOrder.coe_support_subset_of_lex_le`: monomials supported in an upper set of variables
  form a lower set for the lexicographic order.
* `MonomialOrder.monicNormalize`: over a field, a polynomial divided by its leading coefficient,
  monic with the same leading exponent when the polynomial is nonzero
  (`MonomialOrder.monic_monicNormalize`, `MonomialOrder.degree_monicNormalize`).
* `MonomialOrder.monic_aeval_monomial_one`, `MonomialOrder.degree_aeval_monomial_one`: for a
  family `c` of monic polynomials, `∏ i, c i ^ w i` is monic with leading exponent
  `A w = ∑ i, w i • m.degree (c i)`.
* `MonomialOrder.coeff_aeval_of_forall_le`, `MonomialOrder.degree_aeval_le_of_forall_le`: if all
  exponents `w` of `P` have `A w ≼ e`, then the coefficient of `X^e` in `aeval c P` is the sum of
  the coefficients of `P` at the `w` with `A w = e`, and `aeval c P` has leading exponent at
  most `e`.
* `MonomialOrder.algebraicIndependent_of_degree_eq_single`: polynomials `yᵢ` whose leading
  monomial is `Xᵢ` are algebraically independent.
-/

public section

open MvPolynomial

/-- A set of polynomials closed under scalar multiplication (for example a submodule or a
subalgebra) contains a monomial with unit coefficient if and only if it contains the
corresponding monomial with coefficient one. -/
theorem MvPolynomial.monomial_mem_iff_monomial_one_mem {σ R S : Type*} [CommSemiring R]
    [SetLike S (MvPolynomial σ R)] [SMulMemClass S R (MvPolynomial σ R)]
    {a : σ →₀ ℕ} {c : R} (C : S) (hc : IsUnit c) :
    monomial a c ∈ C ↔ monomial a 1 ∈ C := by
  obtain ⟨u, rfl⟩ := hc
  have h : monomial a (u : R) = (u : R) • monomial a 1 := by simp [smul_monomial]
  rw [h]
  refine ⟨fun hu => ?_, SMulMemClass.smul_mem _⟩
  simpa [smul_smul] using SMulMemClass.smul_mem ((u⁻¹ : Rˣ) : R) hu

namespace MonomialOrder

variable {σ R : Type*} (m : MonomialOrder σ)

/-- Two monomial orders give the same leading exponent of `f` if every other exponent in its
support remains strictly below its original leading exponent. -/
theorem degree_eq_of_forall_lt [CommSemiring R] (n : MonomialOrder σ)
    (f : MvPolynomial σ R)
    (h : ∀ a ∈ f.support, a ≠ m.degree f → a ≺[n] m.degree f) :
    n.degree f = m.degree f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  apply n.toSyn.injective
  refine le_antisymm (n.degree_le_iff.2 fun a ha ↦ ?_)
    (n.le_degree (m.degree_mem_support hf))
  rcases eq_or_ne a (m.degree f) with rfl | hne
  · exact le_rfl
  · exact (h a ha hne).le

/-- Orders preserving strict comparisons on a set containing the support and original leading
exponent of a polynomial give it the same leading exponent. -/
theorem degree_eq_of_forall_mem_lt [CommSemiring R] (n : MonomialOrder σ)
    (f : MvPolynomial σ R) {s : Set (σ →₀ ℕ)}
    (h : ∀ a ∈ s, ∀ b ∈ s, a ≺[m] b → a ≺[n] b)
    (hf : ↑f.support ⊆ s) (hd : m.degree f ∈ s) : n.degree f = m.degree f := by
  apply m.degree_eq_of_forall_lt n f
  intro a ha hne
  exact h a (hf ha) _ hd (lt_of_le_of_ne (m.le_degree ha) (m.toSyn.injective.ne hne))

/-- Orders agreeing on the leading exponent of a polynomial agree on its leading coefficient. -/
theorem leadingCoeff_eq_of_degree_eq [CommSemiring R] (n : MonomialOrder σ)
    {f : MvPolynomial σ R} (h : n.degree f = m.degree f) :
    n.leadingCoeff f = m.leadingCoeff f := by
  simp only [leadingCoeff, h]

/-- Orders agreeing on the leading exponent of a polynomial agree on its leading term. -/
theorem leadingTerm_eq_of_degree_eq [CommSemiring R] (n : MonomialOrder σ)
    {f : MvPolynomial σ R} (h : n.degree f = m.degree f) :
    n.leadingTerm f = m.leadingTerm f := by
  rw [leadingTerm, leadingTerm, h, m.leadingCoeff_eq_of_degree_eq n h]

/-- Orders agreeing on the leading exponents of two polynomials give the same S-polynomial. -/
theorem sPolynomial_eq_of_degree_eq [CommRing R] (n : MonomialOrder σ)
    {f g : MvPolynomial σ R} (hf : n.degree f = m.degree f) (hg : n.degree g = m.degree g) :
    n.sPolynomial f g = m.sPolynomial f g := by
  simp only [sPolynomial, hf, hg, m.leadingCoeff_eq_of_degree_eq n hf,
    m.leadingCoeff_eq_of_degree_eq n hg]

/-- The `WithBot` degree of a polynomial is at most its degree. -/
theorem toWithBotSyn_withBotDegree_le_toSyn_degree [CommSemiring R] (p : MvPolynomial σ R) :
    m.toWithBotSyn (m.withBotDegree p) ≤ m.toSyn (m.degree p) := by
  classical
  rw [withBotDegree_eq]
  split_ifs <;> simp [toWithBotSyn_apply_coe]

/-- If `q` has degree at most that of `f ≠ 0` and the same coefficient of `X^(deg f)`, then
`f - q` has smaller degree than `f`. -/
theorem withBotDegree_sub_lt [CommRing R] {f q : MvPolynomial σ R} (hf : f ≠ 0)
    (hq : m.toWithBotSyn (m.withBotDegree q) ≤ m.toWithBotSyn (m.withBotDegree f))
    (hqf : q.coeff (m.degree f) = m.leadingCoeff f) :
    m.toWithBotSyn (m.withBotDegree (f - q)) < m.toWithBotSyn (m.withBotDegree f) := by
  refine lt_of_le_of_ne ?_ fun heq ↦ ?_
  · simpa [sub_eq_add_neg] using
      (m.withBotDegree_add_le f (-q)).trans (max_le le_rfl (by rwa [withBotDegree_neg]))
  rw [EmbeddingLike.apply_eq_iff_eq, withBotDegree_eq_withBotDegree_iff] at heq
  have := m.degree_mem_support fun h0 ↦ hf (heq.2.1 h0)
  rw [heq.1, mem_support_iff, coeff_sub, hqf, leadingCoeff, sub_self] at this
  exact this rfl

/-- If `q` has degree at most that of `f` and the same coefficient of `X^(deg f)`, then
`f - q` has strictly smaller leading exponent when the difference is nonzero. -/
theorem degree_sub_lt [CommRing R] {f q : MvPolynomial σ R} (hfq : f - q ≠ 0)
    (hq : m.degree q ≼[m] m.degree f) (hqf : q.coeff (m.degree f) = m.leadingCoeff f) :
    m.degree (f - q) ≺[m] m.degree f := by
  refine lt_of_le_of_ne (m.degree_sub_le.trans (max_le le_rfl hq)) ?_
  intro heq
  have hmem := m.degree_mem_support hfq
  rw [m.toSyn.injective heq, mem_support_iff, coeff_sub, hqf, leadingCoeff, sub_self] at hmem
  exact hmem rfl

/-- A monomial multiple `c X^a * b` has degree at most `a + deg b`. -/
theorem toSyn_degree_monomial_mul_le [CommSemiring R] (a : σ →₀ ℕ) (c : R)
    (b : MvPolynomial σ R) : m.toSyn (m.degree (monomial a c * b)) ≤ m.toSyn (a + m.degree b) := by
  rw [map_add]
  exact m.toSyn_degree_mul_le.trans (by gcongr; exact m.degree_monomial_le c)

/-- A set of polynomials closed under scalar multiplication (for example a submodule or a
subalgebra) contains the leading term of a polynomial with unit leading coefficient if and only
if it contains its leading monomial. -/
theorem leadingTerm_mem_iff [CommSemiring R] {S : Type*} [SetLike S (MvPolynomial σ R)]
    [SMulMemClass S R (MvPolynomial σ R)] {f : MvPolynomial σ R} (C : S)
    (hf : IsUnit (m.leadingCoeff f)) :
    m.leadingTerm f ∈ C ↔ monomial (m.degree f) 1 ∈ C := by
  rw [leadingTerm, monomial_mem_iff_monomial_one_mem C hf]

/-- **Cancellation of leading terms by an S-polynomial.** If `b₀` has unit leading coefficient
`u₀` and `deg b₀ ≤ a + deg b`, the difference between `X^a * b` and `lc b` times the normalized
product `X^(a + deg b - deg b₀) * b₀ / lc b₀` is `X^(a + deg b - L) / lc b₀ * S(b, b₀)`, where
`L = deg b ⊔ deg b₀`. -/
theorem monomial_one_mul_sub_smul_eq_monomial_mul_sPolynomial [CommRing R] {a : σ →₀ ℕ}
    {b b₀ : MvPolynomial σ R} (hb₀ : m.degree b₀ ≤ a + m.degree b) (u₀ : Rˣ)
    (hu₀ : (u₀ : R) = m.leadingCoeff b₀) :
    monomial a 1 * b -
        m.leadingCoeff b • (monomial (a + m.degree b - m.degree b₀) ((u₀⁻¹ : Rˣ) : R) * b₀) =
      monomial (a + m.degree b - m.degree b ⊔ m.degree b₀) ((u₀⁻¹ : Rˣ) : R) *
        m.sPolynomial b b₀ := by
  have hL : m.degree b ⊔ m.degree b₀ ≤ a + m.degree b := sup_le le_add_self hb₀
  -- The exponents of the two summands of the right-hand side.
  have e₁ : a + m.degree b - m.degree b ⊔ m.degree b₀ + (m.degree b ⊔ m.degree b₀ - m.degree b) =
      a := by
    rw [tsub_add_tsub_cancel hL le_sup_left, add_tsub_cancel_right]
  have e₂ : a + m.degree b - m.degree b ⊔ m.degree b₀ + (m.degree b ⊔ m.degree b₀ - m.degree b₀) =
      a + m.degree b - m.degree b₀ :=
    tsub_add_tsub_cancel hL le_sup_right
  -- The coefficient of the first summand.
  have hc : ((u₀⁻¹ : Rˣ) : R) * m.leadingCoeff b₀ = 1 := by rw [← hu₀, Units.inv_mul]
  simp only [sPolynomial_def, mul_sub, ← mul_assoc, monomial_mul_monomial, smul_eq_C_mul,
    C_mul_monomial, e₁, e₂, hc, mul_comm (m.leadingCoeff b)]

section Map

variable {S : Type*}

section CommSemiring

variable [CommSemiring R] [CommSemiring S] (φ : R →+* S) {f : MvPolynomial σ R}

/-- A coefficient map that does not kill the leading coefficient preserves the leading monomial. -/
theorem degree_map_of_leadingCoeff_ne_zero (h : φ (m.leadingCoeff f) ≠ 0) :
    m.degree (map φ f) = m.degree f := by
  have hmem : m.degree f ∈ (map φ f).support := by
    rwa [mem_support_iff, coeff_map]
  exact m.toSyn.injective <| le_antisymm
    (m.degree_le_iff.2 fun _ hc ↦ m.le_degree (support_map_subset φ f hc)) (m.le_degree hmem)

/-- A coefficient map that does not kill the leading coefficient maps it to the leading
coefficient of the image. -/
theorem leadingCoeff_map_of_leadingCoeff_ne_zero (h : φ (m.leadingCoeff f) ≠ 0) :
    m.leadingCoeff (map φ f) = φ (m.leadingCoeff f) := by
  rw [leadingCoeff, degree_map_of_leadingCoeff_ne_zero m φ h, coeff_map, leadingCoeff]

variable {φ}

/-- An injective coefficient map preserves the leading monomial. -/
theorem degree_map_of_injective (hφ : Function.Injective φ) (f : MvPolynomial σ R) :
    m.degree (map φ f) = m.degree f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  exact m.degree_map_of_leadingCoeff_ne_zero φ
    ((map_ne_zero_iff φ hφ).2 (m.leadingCoeff_ne_zero_iff.2 hf))

/-- An injective coefficient map preserves the `WithBot` degree. -/
theorem withBotDegree_map_of_injective (hφ : Function.Injective φ) (f : MvPolynomial σ R) :
    m.withBotDegree (map φ f) = m.withBotDegree f := by
  classical
  simp [withBotDegree_eq, m.degree_map_of_injective hφ, map_eq_zero_iff _ (map_injective φ hφ)]

/-- An injective coefficient map sends the leading coefficient to the leading coefficient of the
image. -/
theorem leadingCoeff_map_of_injective (hφ : Function.Injective φ) (f : MvPolynomial σ R) :
    m.leadingCoeff (map φ f) = φ (m.leadingCoeff f) := by
  rw [leadingCoeff, m.degree_map_of_injective hφ, coeff_map, leadingCoeff]

/-- An injective coefficient map sends the leading term to the leading term of the image. -/
theorem leadingTerm_map_of_injective (hφ : Function.Injective φ) (f : MvPolynomial σ R) :
    m.leadingTerm (map φ f) = map φ (m.leadingTerm f) := by
  rw [leadingTerm, leadingTerm, map_monomial, m.degree_map_of_injective hφ,
    m.leadingCoeff_map_of_injective hφ]

end CommSemiring

/-- An injective coefficient map sends the S-polynomial of `f` and `g` to the S-polynomial of
their images. -/
theorem sPolynomial_map_of_injective [CommRing R] [CommRing S] {φ : R →+* S}
    (hφ : Function.Injective φ) (f g : MvPolynomial σ R) :
    m.sPolynomial (map φ f) (map φ g) = map φ (m.sPolynomial f g) := by
  simp only [sPolynomial, map_sub, map_mul, map_monomial, m.degree_map_of_injective hφ,
    m.leadingCoeff_map_of_injective hφ]

end Map

section WeightedHomogeneous

open Finsupp

variable {M : Type*} [AddCommMonoid M] [CommSemiring R] (w : σ → M)

/-- The weighted homogeneous component of `f` whose weight is that of the leading monomial of `f`
has the same leading monomial as `f`. -/
@[simp]
theorem degree_weightedHomogeneousComponent_weight_degree (f : MvPolynomial σ R) :
    m.degree (weightedHomogeneousComponent w (weight w (m.degree f)) f) = m.degree f := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hsupp := support_weightedHomogeneousComponent (w := w) (weight w (m.degree f)) f
  refine m.toSyn.injective (le_antisymm (m.degree_le_iff.2 fun c hc ↦ ?_) (m.le_degree ?_))
  · rw [hsupp] at hc
    exact m.le_degree (Finset.mem_filter.1 hc).1
  · rw [hsupp]
    exact Finset.mem_filter.2 ⟨m.degree_mem_support hf, rfl⟩

/-- The weighted homogeneous component of `f` containing its leading monomial has the same leading
coefficient as `f`. -/
@[simp]
theorem leadingCoeff_weightedHomogeneousComponent_weight_degree (f : MvPolynomial σ R) :
    m.leadingCoeff (weightedHomogeneousComponent w (weight w (m.degree f)) f) =
      m.leadingCoeff f := by
  classical
  simp [leadingCoeff, coeff_weightedHomogeneousComponent]

/-- The weighted homogeneous component of `f` containing its leading monomial has the same leading
term as `f`. -/
@[simp]
theorem leadingTerm_weightedHomogeneousComponent_weight_degree (f : MvPolynomial σ R) :
    m.leadingTerm (weightedHomogeneousComponent w (weight w (m.degree f)) f) =
      m.leadingTerm f := by
  simp [leadingTerm]

/-- The weighted homogeneous component of `f` containing its leading monomial is weighted
homogeneous of the weight of its own leading monomial. -/
theorem isWeightedHomogeneous_weightedHomogeneousComponent_weight_degree (f : MvPolynomial σ R) :
    IsWeightedHomogeneous w (weightedHomogeneousComponent w (weight w (m.degree f)) f)
      (weight w (m.degree (weightedHomogeneousComponent w (weight w (m.degree f)) f))) := by
  rw [degree_weightedHomogeneousComponent_weight_degree]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

end WeightedHomogeneous

section Relation

variable {m} {ι : Type*} [CommRing R] {a : ι → σ →₀ ℕ} {u v : ι →₀ ℕ} {Q : MvPolynomial ι R}

/-- Let `A w = ∑ i, w i • a i`. If `A u = A v` and every exponent `w` of `Q` satisfies
`A w ≺ A u`, then the part of the lifted relation `Y^u - Y^v - Q` of weight `A u` is the binomial
`Y^u - Y^v`. -/
theorem weightedHomogeneousComponent_monomial_sub_monomial_sub
    (huv : Finsupp.linearCombination ℕ a u = Finsupp.linearCombination ℕ a v)
    (hQ : ∀ w ∈ Q.support, Finsupp.linearCombination ℕ a w ≺[m] Finsupp.linearCombination ℕ a u) :
    weightedHomogeneousComponent a (Finsupp.linearCombination ℕ a u)
        (monomial u (1 : R) - monomial v 1 - Q) =
      monomial u 1 - monomial v 1 := by
  have hA (w : ι →₀ ℕ) : Finsupp.weight a w = Finsupp.linearCombination ℕ a w := by
    rw [Finsupp.weight_apply, Finsupp.linearCombination_apply]
  rw [map_sub, weightedHomogeneousComponent_eq_zero' _ _ fun w hw ↦ (hA w).trans_ne
      fun h ↦ (hQ w hw).ne (congrArg m.toSyn h), sub_zero,
    weightedHomogeneousComponent_eq_self ((isWeightedHomogeneous_monomial _ _ _ (hA u)).sub
      (isWeightedHomogeneous_monomial _ _ _ ((hA v).trans huv.symm)))]

/-- Let `A w = ∑ i, w i • a i`. If `A u = A v` and every exponent `w` of `Q` satisfies
`A w ≺ A u`, then every exponent `w` of the lifted relation `Y^u - Y^v - Q` satisfies `A w ≼ A u`:
its part of weight `A u` is its top part. -/
theorem linearCombination_le_of_mem_support_monomial_sub_monomial_sub
    (huv : Finsupp.linearCombination ℕ a u = Finsupp.linearCombination ℕ a v)
    (hQ : ∀ w ∈ Q.support, Finsupp.linearCombination ℕ a w ≺[m] Finsupp.linearCombination ℕ a u)
    {w : ι →₀ ℕ} (hw : w ∈ (monomial u (1 : R) - monomial v 1 - Q).support) :
    Finsupp.linearCombination ℕ a w ≼[m] Finsupp.linearCombination ℕ a u := by
  classical
  rcases Finset.mem_union.1 (support_sub _ _ _ hw) with hw | hw
  · rcases Finset.mem_union.1 (support_sub _ _ _ hw) with hw | hw
    · rw [Finset.mem_singleton.1 (support_monomial_subset hw)]
    · rw [Finset.mem_singleton.1 (support_monomial_subset hw), huv]
  · exact (hQ w hw).le

end Relation

section Rename

variable {τ : Type*} [CommSemiring R] {m} {m' : MonomialOrder τ} {e : τ → σ}

/-- A relabeling of variables which carries the monomial order `m'` to `m` is injective. -/
theorem injective_of_forall_toSyn_le_iff
    (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e) :
    Function.Injective e := by
  intro i j hij
  -- The two variables `X i`, `X j` are renamed to the same variable, so neither exceeds the other.
  have hsingle : m.toSyn ((Finsupp.single i 1).mapDomain e) =
      m.toSyn ((Finsupp.single j 1).mapDomain e) := by
    simp [hij]
  have h := m'.toSyn.injective <| le_antisymm ((hm _ _).2 hsingle.le) ((hm _ _).2 hsingle.ge)
  simpa [Finsupp.single_left_inj] using h

/-- Renaming the variables along a relabeling which carries the monomial order `m'` to `m` renames
the leading monomial. -/
theorem degree_rename (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e)
    (p : MvPolynomial τ R) : m.degree (rename e p) = (m'.degree p).mapDomain e := by
  classical
  have he := injective_of_forall_toSyn_le_iff hm
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  refine m.toSyn.injective (le_antisymm (m.degree_le_iff.2 fun c hc ↦ ?_) (m.le_degree ?_))
  · rw [support_rename_of_injective he, Finset.mem_image] at hc
    obtain ⟨a, ha, rfl⟩ := hc
    exact (hm _ _).1 (m'.le_degree ha)
  · rw [support_rename_of_injective he]
    exact Finset.mem_image_of_mem _ (m'.degree_mem_support hp)

/-- Renaming the variables along a relabeling which carries the monomial order `m'` to `m`
preserves the leading coefficient. -/
theorem leadingCoeff_rename (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e)
    (p : MvPolynomial τ R) : m.leadingCoeff (rename e p) = m'.leadingCoeff p := by
  rw [leadingCoeff, degree_rename hm,
    coeff_rename_mapDomain _ (injective_of_forall_toSyn_le_iff hm), leadingCoeff]

/-- Renaming the variables along a relabeling which carries the monomial order `m'` to `m`
renames the leading term. -/
theorem leadingTerm_rename (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e)
    (p : MvPolynomial τ R) : m.leadingTerm (rename e p) = rename e (m'.leadingTerm p) := by
  rw [leadingTerm, leadingTerm, degree_rename hm, leadingCoeff_rename hm, rename_monomial]

/-- For an elimination order `m` for the variables `e τ`, that is, one in which every monomial
below a monomial in these variables is again a monomial in these variables, a polynomial whose
leading monomial only involves the variables `e τ` is the renaming of a polynomial in the
variables `τ`. -/
theorem exists_rename_eq_of_coe_support_degree_subset
    (helim : ∀ a b : σ →₀ ℕ, a ≼[m] b → ↑b.support ⊆ Set.range e → ↑a.support ⊆ Set.range e)
    (he : Function.Injective e) {g : MvPolynomial σ R}
    (hg : ↑(m.degree g).support ⊆ Set.range e) : ∃ g' : MvPolynomial τ R, rename e g' = g := by
  classical
  refine exists_rename_eq_of_vars_subset_range g e he fun i hi ↦ ?_
  obtain ⟨d, hd, hid⟩ := (mem_vars_iff_mem_support i).1 hi
  exact helim d _ (m.le_degree hd) hg hid

end Rename

section Lex

/-- For the lexicographic order, the monomials supported in an upper set of variables form a
lower set: with the antitone variable convention these are the smallest variables. -/
theorem coe_support_subset_of_lex_le [LinearOrder σ] [WellFoundedGT σ] {s : Set σ}
    (hs : IsUpperSet s) {a b : σ →₀ ℕ} (hab : a ≼[lex] b) (hb : ↑b.support ⊆ s) :
    ↑a.support ⊆ s := by
  intro j hj
  by_contra hjs
  rcases eq_or_ne a b with rfl | hne
  · exact hjs (hb hj)
  -- `a < b` first differs from `b` at some `i` with `0 ≤ a i < b i`, so `i ∈ s`; since `j ∉ s`,
  -- `j < i`, and then `a j = b j = 0`.
  obtain ⟨i, hi, hlt⟩ := Finsupp.Lex.lt_iff.1 <| lex_lt_iff.1 <|
    lt_of_le_of_ne hab (lex.toSyn.injective.ne hne)
  have hbi : i ∈ s := hb (Finsupp.mem_support_iff.2 (Nat.zero_lt_of_lt hlt).ne')
  have hji : j < i := lt_of_not_ge fun hij ↦ hjs (hs hij hbi)
  have hbj : b j = 0 := Finsupp.notMem_support_iff.1 fun h ↦ hjs (hb h)
  exact (Finsupp.mem_support_iff.1 hj) ((hi j hji).trans hbj)

end Lex

section MonicNormalize

variable {k : Type*} [Field k]

/-- The polynomial `f` divided by its leading coefficient for the monomial order `m`. It is monic
when `f ≠ 0` (`MonomialOrder.monic_monicNormalize`), and `0` when `f = 0`. -/
noncomputable def monicNormalize (f : MvPolynomial σ k) : MvPolynomial σ k :=
  C (m.leadingCoeff f)⁻¹ * f

variable {m} {f : MvPolynomial σ k}

theorem monicNormalize_def (f : MvPolynomial σ k) :
    m.monicNormalize f = C (m.leadingCoeff f)⁻¹ * f :=
  (rfl)

@[simp]
theorem monicNormalize_zero : m.monicNormalize (0 : MvPolynomial σ k) = 0 := by
  simp [monicNormalize_def]

@[simp]
theorem monicNormalize_eq_zero_iff : m.monicNormalize f = 0 ↔ f = 0 := by
  simp [monicNormalize_def]

/-- Normalization does not change the leading exponent. -/
@[simp]
theorem degree_monicNormalize (f : MvPolynomial σ k) :
    m.degree (m.monicNormalize f) = m.degree f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rw [monicNormalize_def, m.degree_mul (by simpa using hf) hf, m.degree_C, zero_add]

theorem monic_monicNormalize (hf : f ≠ 0) : m.Monic (m.monicNormalize f) := by
  simp [Monic, monicNormalize_def, m.leadingCoeff_ne_zero_iff.2 hf]

/-- Multiplying the normalization of `f` by the leading coefficient of `f` recovers `f`. -/
@[simp]
theorem C_leadingCoeff_mul_monicNormalize (f : MvPolynomial σ k) :
    C (m.leadingCoeff f) * m.monicNormalize f = f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rw [monicNormalize_def, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (m.leadingCoeff_ne_zero_iff.2 hf),
    C_1, one_mul]

/-- A monic polynomial is its own normalization. -/
theorem Monic.monicNormalize_eq (hf : m.Monic f) : m.monicNormalize f = f := by
  simp [monicNormalize_def, hf.leadingCoeff_eq_one]

/-- The normalization of a nonzero polynomial has leading term `X ^ (m.degree f)`. -/
theorem leadingTerm_monicNormalize_of_ne_zero (hf : f ≠ 0) :
    m.leadingTerm (m.monicNormalize f) = monomial (m.degree f) 1 := by
  rw [leadingTerm, (monic_monicNormalize hf).leadingCoeff_eq_one, degree_monicNormalize]

/-- The leading term of the normalization is the normalization of the leading term. -/
theorem leadingTerm_monicNormalize (f : MvPolynomial σ k) :
    m.leadingTerm (m.monicNormalize f) = m.monicNormalize (m.leadingTerm f) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rw [leadingTerm_monicNormalize_of_ne_zero hf, monicNormalize_def, leadingCoeff_leadingTerm,
    leadingTerm, C_mul_monomial, inv_mul_cancel₀ (m.leadingCoeff_ne_zero_iff.2 hf)]

/-- A set of polynomials closed under multiplication by scalars in `k` (for example a
`k`-subalgebra or a `k`-submodule) contains the normalization of `f` if and only if it
contains `f`. -/
@[simp]
theorem monicNormalize_mem_iff {S : Type*} [SetLike S (MvPolynomial σ k)]
    [SMulMemClass S k (MvPolynomial σ k)] {A : S} : m.monicNormalize f ∈ A ↔ f ∈ A := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← C_leadingCoeff_mul_monicNormalize (m := m) f, ← smul_eq_C_mul]
    exact SMulMemClass.smul_mem _ h
  · rw [monicNormalize_def, ← smul_eq_C_mul]
    exact SMulMemClass.smul_mem _ h

end MonicNormalize

/-- Substituting nonzero polynomials into a coefficient-one monomial adds their leading
exponents, with the multiplicities prescribed by the monomial. -/
theorem degree_aeval_monomial_one_of_ne_zero [CommSemiring R] [NoZeroDivisors R]
    {ι : Type*} {b : ι → MvPolynomial σ R} (hb : ∀ i, b i ≠ 0) (u : ι →₀ ℕ) :
    m.degree (aeval b (monomial u (1 : R))) = Finsupp.linearCombination ℕ (m.degree ∘ b) u := by
  classical
  simp only [aeval_monomial, map_one, one_mul, Finsupp.prod]
  rw [m.degree_prod fun i _ ↦ pow_ne_zero _ (hb i)]
  simp [m.degree_pow, Finsupp.linearCombination_apply, Finsupp.sum]

section Substitution

variable {ι : Type*} [CommSemiring R] {m} {c : ι → MvPolynomial σ R}

/-- The image of the monomial `Y^w` under the substitution of a monic family is monic. -/
theorem monic_aeval_monomial_one (hc : ∀ i, m.Monic (c i)) (w : ι →₀ ℕ) :
    m.Monic (aeval c (monomial w (1 : R))) := by
  rw [aeval_monomial, map_one, one_mul, Finsupp.prod]
  exact Monic.prod fun i _ ↦ (hc i).pow

variable [Nontrivial R]

/-- The image of the monomial `Y^w` under the substitution of a monic family `c` has leading
exponent `∑ i, w i • m.degree (c i)`. -/
theorem degree_aeval_monomial_one (hc : ∀ i, m.Monic (c i)) (w : ι →₀ ℕ) :
    m.degree (aeval c (monomial w (1 : R))) =
      Finsupp.linearCombination ℕ (fun i ↦ m.degree (c i)) w := by
  rw [aeval_monomial, map_one, one_mul, Finsupp.prod,
    m.degree_prod_of_regular fun i _ ↦ by rw [(hc i).pow.leadingCoeff_eq_one]; exact isRegular_one,
    Finsupp.linearCombination_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun i _ ↦
    m.degree_pow_of_pow_leadingCoeff_ne_zero (by simp [(hc i).leadingCoeff_eq_one])

open scoped Classical in
/-- Let `c` be a monic family and write `A w = ∑ i, w i • m.degree (c i)`. If every exponent `w` of
`P` satisfies `A w ≼ e`, then the coefficient of `X^e` in `aeval c P` is the sum of the
coefficients of `P` at the exponents `w` with `A w = e`: the images of the other monomials of `P`
have leading exponent below `e`. -/
theorem coeff_aeval_of_forall_le (hc : ∀ i, m.Monic (c i)) {P : MvPolynomial ι R}
    {e : σ →₀ ℕ}
    (hP : ∀ w ∈ P.support, Finsupp.linearCombination ℕ (fun i ↦ m.degree (c i)) w ≼[m] e) :
    (aeval c P).coeff e = ∑ w ∈ P.support with
      Finsupp.linearCombination ℕ (fun i ↦ m.degree (c i)) w = e, P.coeff w := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum, coeff_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun w hw ↦ ?_
  conv_lhs => rw [← mul_one (P.coeff w), ← C_mul_monomial]
  rw [map_mul, aeval_C, algebraMap_eq, coeff_C_mul]
  split_ifs with h
  · rw [← h, ← degree_aeval_monomial_one hc, (monic_aeval_monomial_one hc w).coeff_degree, mul_one]
  · rw [m.coeff_eq_zero_of_lt, mul_zero]
    rw [degree_aeval_monomial_one hc]
    exact lt_of_le_of_ne (hP w hw) fun h' ↦ h (m.toSyn.injective h')

/-- Let `c` be a monic family and write `A w = ∑ i, w i • m.degree (c i)`. If every exponent `w` of
`P` satisfies `A w ≼ e`, then `aeval c P` has leading exponent at most `e`. -/
theorem degree_aeval_le_of_forall_le (hc : ∀ i, m.Monic (c i)) {P : MvPolynomial ι R}
    {e : σ →₀ ℕ}
    (hP : ∀ w ∈ P.support, Finsupp.linearCombination ℕ (fun i ↦ m.degree (c i)) w ≼[m] e) :
    m.degree (aeval c P) ≼[m] e := by
  classical
  refine m.degree_le_iff.2 fun d hd ↦ le_of_not_gt fun hlt ↦ ?_
  rw [mem_support_iff, coeff_aeval_of_forall_le hc fun w hw ↦ (hP w hw).trans hlt.le] at hd
  refine hd (Finset.sum_eq_zero fun w hw ↦ ?_)
  rw [Finset.mem_filter] at hw
  exact absurd (hP w hw.1) (by rw [hw.2]; exact not_le_of_gt hlt)

end Substitution

variable [CommRing R]

/-- The substituted value of a coefficient-one binomial relation of a monic family vanishes
or has leading exponent strictly below the common exponent of its two terms. -/
theorem aeval_monomial_sub_monomial_eq_zero_or_degree_lt
    {ι : Type*} {b : ι → MvPolynomial σ R} [Nontrivial R]
    (hb : ∀ i, m.Monic (b i)) (u v : ι →₀ ℕ)
    (huv : Finsupp.linearCombination ℕ (m.degree ∘ b) u =
      Finsupp.linearCombination ℕ (m.degree ∘ b) v) :
    aeval b (monomial u (1 : R) - monomial v 1) = 0 ∨
      m.degree (aeval b (monomial u (1 : R) - monomial v 1)) ≺[m]
        Finsupp.linearCombination ℕ (m.degree ∘ b) u := by
  have hu := monic_aeval_monomial_one hb u
  have hv := monic_aeval_monomial_one hb v
  have hdeg : m.degree (aeval b (monomial u (1 : R))) =
      m.degree (aeval b (monomial v (1 : R))) := by
    simpa only [degree_aeval_monomial_one hb, Function.comp_def] using huv
  rcases eq_or_ne (aeval b (monomial u (1 : R) - monomial v 1)) 0 with hz | hn
  · exact Or.inl hz
  · right
    simpa only [← map_sub, degree_aeval_monomial_one hb, Function.comp_def] using
      m.degree_sub_lt (by simpa only [map_sub] using hn)
        (le_of_eq (congrArg m.toSyn hdeg.symm)) (by
          simpa only [leadingCoeff, ← hdeg] using
            hv.leadingCoeff_eq_one.trans hu.leadingCoeff_eq_one.symm)

variable [NoZeroDivisors R]

/-- **Algebraic independence from leading monomials.** Over a ring without zero divisors, a family
`yᵢ` of polynomials in the variables `Xᵢ` whose leading monomial for a monomial order is `Xᵢ` is
algebraically independent. -/
theorem algebraicIndependent_of_degree_eq_single {y : σ → MvPolynomial σ R}
    (hy : ∀ i, m.degree (y i) = Finsupp.single i 1) : AlgebraicIndependent R y := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact algebraicIndependent_iff_injective_aeval.2 fun _ _ _ ↦ Subsingleton.elim _ _
  have hy0 (i : σ) : y i ≠ 0 := fun h ↦ by
    simpa [h] using congrArg (fun d ↦ d i) (hy i)
  have hne (d : σ →₀ ℕ) : (d.prod fun i k ↦ y i ^ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ ↦ pow_ne_zero _ (hy0 i)
  -- The image `c ∏ yᵢ ^ dᵢ` of a monomial `c X^d` with `c ≠ 0` has leading monomial `X^d`.
  have hterm {c : R} (hc : c ≠ 0) (d : σ →₀ ℕ) : m.degree (aeval y (monomial d c)) = d := by
    rw [aeval_monomial, algebraMap_eq, m.degree_mul (C_ne_zero.2 hc) (hne d), m.degree_C,
      zero_add, Finsupp.prod, m.degree_prod fun i _ ↦ pow_ne_zero _ (hy0 i)]
    simp_rw [m.degree_pow, hy, Finsupp.smul_single, smul_eq_mul, mul_one]
    exact d.sum_single
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro p hp
  by_contra hp0
  rw [p.as_sum, map_sum] at hp
  -- The images of the monomials of `p` have pairwise distinct leading monomials, so their sum is
  -- nonzero.
  refine AddMonoidAlgebra.sum_ne_zero_of_injOn_supDegree (D := m.toSyn)
    (support_nonempty.2 hp0) (fun d hd ↦ ?_) (fun d hd e he hde ↦ ?_) hp
  · rw [aeval_monomial, algebraMap_eq]
    exact mul_ne_zero (C_ne_zero.2 (mem_support_iff.1 hd)) (hne d)
  · have key (d : σ →₀ ℕ) (hd : d ∈ p.support) :
        AddMonoidAlgebra.supDegree m.toSyn (aeval y (monomial d (p.coeff d))) = m.toSyn d := by
      -- `m.degree` is defined as the supremum `AddMonoidAlgebra.supDegree m.toSyn`, read back
      -- through `m.toSyn`.
      have h : m.toSyn (m.degree (aeval y (monomial d (p.coeff d)))) =
          AddMonoidAlgebra.supDegree m.toSyn (aeval y (monomial d (p.coeff d))) := by
        rw [degree, AddEquiv.apply_symm_apply]
        rfl
      rw [← h, hterm (mem_support_iff.1 hd)]
    simpa [key d hd, key e he] using hde

end MonomialOrder
