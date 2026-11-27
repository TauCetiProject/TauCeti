/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-!
# Prescribed leading terms for a monomial order

For a monomial order `m` on `σ →₀ ℕ`, `MonomialOrder.HasLeadingTerm m F γ a` says that no
exponent of `F` exceeds `γ` for `m` and that the coefficient of `X ^ γ` in `F` is `a`, which may
be `0`. Unlike `m.degree` and `m.leadingCoeff`, this is preserved by products, sums with lower
terms and linear combinations without any hypothesis that leading coefficients do not vanish or
multiply to zero, so it computes leading terms over every commutative semiring.

## Main declarations

* `MonomialOrder.HasLeadingTerm`: `F` has leading term `a * X ^ γ` for `m`.
* `MonomialOrder.HasLeadingTerm.mul`, `MonomialOrder.HasLeadingTerm.prod`,
  `MonomialOrder.HasLeadingTerm.sum`, `MonomialOrder.HasLeadingTerm.sum_smul`: leading terms of
  products, sums and linear combinations.
* `MonomialOrder.linearIndependent_of_hasLeadingTerm`: linear independence from leading terms with
  distinct exponents and independent leading coefficients.

## References

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic
PBC), `src/Lib/GLn/SchurModule/MinorBasis.lean` (`New.GL.HasLeadingTerm` and its lemmas,
`New.GL.linearIndependent_of_hasLeadingTerm`), stated there for the colexicographic order only.
-/

public section

open MvPolynomial Finset

namespace MonomialOrder

variable {σ : Type*} (m : MonomialOrder σ)

section CommSemiring

variable {A : Type*} [CommSemiring A]

/-- `F` has leading term `a * X ^ γ` for the monomial order `m`: no exponent of `F` exceeds `γ`,
and the coefficient of `X ^ γ` in `F` is `a` (which may be `0`). -/
def HasLeadingTerm (F : MvPolynomial σ A) (γ : σ →₀ ℕ) (a : A) : Prop :=
  m.degree F ≼[m] γ ∧ F.coeff γ = a

variable {m} {F G : MvPolynomial σ A} {γ δ : σ →₀ ℕ} {a b : A}

theorem hasLeadingTerm_iff : m.HasLeadingTerm F γ a ↔ m.degree F ≼[m] γ ∧ F.coeff γ = a :=
  Iff.rfl

theorem HasLeadingTerm.mk (h_le : m.degree F ≼[m] γ) (h_coeff : F.coeff γ = a) :
    m.HasLeadingTerm F γ a :=
  ⟨h_le, h_coeff⟩

theorem HasLeadingTerm.degree_le (hF : m.HasLeadingTerm F γ a) : m.degree F ≼[m] γ := hF.1

theorem HasLeadingTerm.coeff_eq (hF : m.HasLeadingTerm F γ a) : F.coeff γ = a := hF.2

theorem HasLeadingTerm.coeff_eq_zero_of_lt (hF : m.HasLeadingTerm F γ a) (h : γ ≺[m] δ) :
    F.coeff δ = 0 :=
  m.coeff_eq_zero_of_lt (hF.degree_le.trans_lt h)

/-- A polynomial has its own leading term, `m.leadingCoeff F * X ^ m.degree F`. -/
theorem hasLeadingTerm_degree_leadingCoeff (F : MvPolynomial σ A) :
    m.HasLeadingTerm F (m.degree F) (m.leadingCoeff F) :=
  ⟨le_rfl, rfl⟩

theorem hasLeadingTerm_monomial (γ : σ →₀ ℕ) (a : A) : m.HasLeadingTerm (monomial γ a) γ a :=
  ⟨m.degree_monomial_le a, by classical simp⟩

theorem HasLeadingTerm.mul (hF : m.HasLeadingTerm F γ a) (hG : m.HasLeadingTerm G δ b) :
    m.HasLeadingTerm (F * G) (γ + δ) (a * b) := by
  refine ⟨m.degree_mul_le.trans ?_, ?_⟩
  · rw [map_add, map_add]
    exact add_le_add hF.degree_le hG.degree_le
  · rw [m.coeff_mul_of_add_of_degree_le hF.degree_le hG.degree_le, hF.coeff_eq, hG.coeff_eq]

theorem HasLeadingTerm.prod {ι : Type*} {s : Finset ι} {F : ι → MvPolynomial σ A}
    {γ : ι → σ →₀ ℕ} {a : ι → A} (h : ∀ i ∈ s, m.HasLeadingTerm (F i) (γ i) (a i)) :
    m.HasLeadingTerm (∏ i ∈ s, F i) (∑ i ∈ s, γ i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasLeadingTerm_monomial (m := m) (0 : σ →₀ ℕ) (1 : A)
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi]
    exact (h i (mem_insert_self i s)).mul (ih fun j hj => h j (mem_insert_of_mem hj))

/-- Adding terms below the leading exponent keeps the leading term. -/
theorem HasLeadingTerm.add_of_lt (hF : m.HasLeadingTerm F γ a) (hG : m.degree G ≺[m] γ) :
    m.HasLeadingTerm (F + G) γ a :=
  ⟨m.degree_add_le.trans (sup_le hF.degree_le hG.le), by
    simp [hF.coeff_eq, m.coeff_eq_zero_of_lt hG]⟩

/-- Let each `F i` have leading term `a i * X ^ γ i`. If `γ j` exceeds every other `γ i` with
`i ∈ s`, then the sum of the `F i` over `s` has leading term `a j * X ^ γ j`; the index `j` may lie
outside `s` when `a j = 0`. -/
theorem HasLeadingTerm.sum {ι : Type*} {s : Finset ι} {F : ι → MvPolynomial σ A}
    {γ : ι → σ →₀ ℕ} {a : ι → A} (h : ∀ i, m.HasLeadingTerm (F i) (γ i) (a i)) (j : ι)
    (h_lt : ∀ i ∈ s, i ≠ j → γ i ≺[m] γ j) (h_notMem : j ∉ s → a j = 0) :
    m.HasLeadingTerm (∑ i ∈ s, F i) (γ j) (a j) := by
  classical
  refine ⟨m.degree_sum_le.trans (Finset.sup_le fun i hi => ?_), ?_⟩
  · rcases eq_or_ne i j with rfl | hij
    · exact (h i).degree_le
    · exact ((h i).degree_le.trans_lt (h_lt i hi hij)).le
  · rw [coeff_sum, Finset.sum_eq_single j (fun i hi hij => (h i).coeff_eq_zero_of_lt
      (h_lt i hi hij)) fun hj => (h j).coeff_eq.trans (h_notMem hj), (h j).coeff_eq]

/-- A product of powers of polynomials `u j`, each with leading term the variable `X j`, has as
leading term the monomial of the exponents, with coefficient `1`. -/
theorem hasLeadingTerm_prod_pow [Fintype σ] {u : σ → MvPolynomial σ A}
    (hu : ∀ j, m.HasLeadingTerm (u j) (Finsupp.single j 1) 1) (η : σ →₀ ℕ) :
    m.HasLeadingTerm (∏ j, u j ^ η j) η 1 := by
  classical
  have h_pow (j : σ) : m.HasLeadingTerm (u j ^ η j) (Finsupp.single j (η j)) 1 := by
    simpa [Finset.prod_const, Finset.sum_const] using
      HasLeadingTerm.prod (s := range (η j)) fun _ _ => hu j
  simpa [Finsupp.univ_sum_single] using HasLeadingTerm.prod (s := univ) fun j _ => h_pow j

/-- A linear combination of polynomials with the same leading exponent `γ` has leading term the
same combination of the leading coefficients times `X ^ γ`. -/
theorem HasLeadingTerm.sum_smul {S : Type*} [CommSemiring S] [Algebra S A] {ι : Type*}
    (s : Finset ι) {F : ι → MvPolynomial σ A} {a : ι → A}
    (h : ∀ i ∈ s, m.HasLeadingTerm (F i) γ (a i)) (c : ι → S) :
    m.HasLeadingTerm (∑ i ∈ s, c i • F i) γ (∑ i ∈ s, c i • a i) := by
  refine ⟨m.degree_sum_le.trans (Finset.sup_le fun i hi => ?_), ?_⟩
  · rw [← algebraMap_smul A]
    exact m.degree_smul_le.trans (h i hi).degree_le
  · rw [coeff_sum]
    exact Finset.sum_congr rfl fun i hi => by simp [(h i hi).coeff_eq]

end CommSemiring

variable {m}

/-- **Linear independence by leading terms.** Let `p ⟨k, a⟩` have leading term
`q k a * X ^ e k`, with distinct exponents `e k` for distinct `k`. If for each `k` the leading
coefficients `q k` are linearly independent over `S`, so are the `p`. -/
theorem linearIndependent_of_hasLeadingTerm {A S : Type*} [CommRing A] [CommRing S]
    [Algebra S A] {K : Type*} {ι : K → Type*} [Finite K] [∀ k, Finite (ι k)]
    {p : (Σ k, ι k) → MvPolynomial σ A} {e : K → σ →₀ ℕ} (he : Function.Injective e)
    {q : ∀ k, ι k → A} (h : ∀ i, m.HasLeadingTerm (p i) (e i.1) (q i.1 i.2))
    (hq : ∀ k, LinearIndependent S (q k)) :
    LinearIndependent S p := by
  classical
  have := Fintype.ofFinite K
  have : ∀ k, Fintype (ι k) := fun k => Fintype.ofFinite (ι k)
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra! h_ne
  obtain ⟨i₀, hi₀⟩ := h_ne
  -- Among the indices with a nonzero coefficient take one, `i`, of largest exponent; the
  -- coefficient of `X ^ e i.1` in the relation is a relation among the `q i.1`.
  obtain ⟨i, hi, hmax⟩ := (univ.filter fun i => g i ≠ 0).exists_max_image
    (fun i => m.toSyn (e i.1)) ⟨i₀, by simpa using hi₀⟩
  have h_coeff : ∑ a : ι i.1, g ⟨i.1, a⟩ • q i.1 a = 0 := by
    have h₀ := congrArg (fun P => P.coeff (e i.1)) hg
    simp only [coeff_sum, Fintype.sum_sigma] at h₀
    -- `MvPolynomial.coeff` is `AddMonoidAlgebra.coeff` (Mathlib deprecated the `MvPolynomial`
    -- copies of these lemmas in its favour); `coeff 0` is the zero `Finsupp`.
    simp only [AddMonoidAlgebra.coeff_smul_apply, AddMonoidAlgebra.coeff_zero,
      Finsupp.coe_zero, Pi.zero_apply] at h₀
    rw [← h₀, Finset.sum_eq_single i.1 (fun k _ hk => Finset.sum_eq_zero fun a _ => ?_)
      (by simp)]
    · exact Finset.sum_congr rfl fun a _ => by rw [(h ⟨i.1, a⟩).coeff_eq]
    · by_cases hga : g ⟨k, a⟩ = 0
      · simp [hga]
      have h_lt : e k ≺[m] e i.1 := lt_of_le_of_ne (hmax ⟨k, a⟩ (by simpa using hga))
        fun h' => hk (he (m.toSyn.injective h'))
      rw [(h ⟨k, a⟩).coeff_eq_zero_of_lt h_lt, smul_zero]
  exact (by simpa using hi : g i ≠ 0)
    (Fintype.linearIndependent_iff.mp (hq i.1) (fun a => g ⟨i.1, a⟩) h_coeff i.2)

end MonomialOrder
