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
under a change of coefficients, leading data of renamed polynomials, elimination orders and the
lexicographic ones among them, and algebraic independence from leading monomials.

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

* `MonomialOrder.toWithBotSyn_withBotDegree_le_toSyn_degree`: the `WithBot` degree of a polynomial
  is at most its degree.
* `MonomialOrder.withBotDegree_sub_lt`: if `q` has degree at most that of `f ≠ 0` and the same
  coefficient of `X^(deg f)`, then `f - q` has smaller degree than `f`.
* `MonomialOrder.toSyn_degree_monomial_mul_le`: `c X^a * b` has degree at most `a + deg b`.
* `MonomialOrder.monomial_one_mul_sub_smul_eq_monomial_mul_sPolynomial`: if `b₀` has a unit
  leading coefficient, then `X^a * b` minus `lc b` times the product of `b₀` of the same degree
  normalized to leading coefficient one is a monomial multiple of the S-polynomial
  `m.sPolynomial b b₀`.
* `MonomialOrder.degree_map_of_injective`, `MonomialOrder.leadingCoeff_map_of_injective`,
  `MonomialOrder.leadingTerm_map_of_injective`, `MonomialOrder.sPolynomial_map_of_injective`: an
  injective coefficient map `φ` preserves leading monomials and commutes with leading
  coefficients, leading terms and S-polynomials.
* `MonomialOrder.degree_rename`, `MonomialOrder.leadingCoeff_rename` and
  `MonomialOrder.leadingTerm_rename`: renaming the variables along a relabeling which carries one
  monomial order to another commutes with leading monomials, coefficients and terms; such a
  relabeling is injective by `MonomialOrder.injective_of_forall_toSyn_le_iff`.
* `MonomialOrder.exists_rename_eq_of_coe_support_degree_subset`: for an elimination order, a
  polynomial whose leading monomial only involves the variables `e τ` is a renamed polynomial.
* `MonomialOrder.coe_support_subset_of_lex_le`: monomials supported in an upper set of variables
  form a lower set for the lexicographic order.
* `MonomialOrder.algebraicIndependent_of_degree_eq_single`: polynomials `yᵢ` whose leading
  monomial is `Xᵢ` are algebraically independent.
-/

public section

open MvPolynomial

namespace MonomialOrder

variable {σ R : Type*} (m : MonomialOrder σ)

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

/-- A monomial multiple `c X^a * b` has degree at most `a + deg b`. -/
theorem toSyn_degree_monomial_mul_le [CommSemiring R] (a : σ →₀ ℕ) (c : R)
    (b : MvPolynomial σ R) : m.toSyn (m.degree (monomial a c * b)) ≤ m.toSyn (a + m.degree b) := by
  rw [map_add]
  exact m.toSyn_degree_mul_le.trans (by gcongr; exact m.degree_monomial_le c)

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

variable [CommRing R] [NoZeroDivisors R]

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
