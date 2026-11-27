/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.CharP.Algebra
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Polynomial.PowChar
import TauCeti.Data.Finsupp.MapDomain

/-!
# `p`-monomials and `p`-independent families

Let `k` be a field of exponential characteristic `p` and let `k ^ p = (frobenius k p).fieldRange`
be its subfield of `p`-th powers. A family `b : ι → k` is **`p`-independent**
(`TauCeti.IsPIndependent p b`) when its `p`-monomials `∏ i, b i ^ (e i : ℕ)` (`e : ι →₀ Fin p`)
are linearly independent over `k ^ p`.

In the two-element case `![a, b]`, `p`-independence means that the monomials `a ^ i * b ^ j` with
`i, j < p` are linearly independent over `k ^ p`; for instance, independent indeterminates `a` and
`b` over `𝔽_p`.

## Main definitions

* `TauCeti.pMonomial`: the `p`-monomial `∏ i, b i ^ (e i : ℕ)` for `e : ι →₀ Fin p`.
* `TauCeti.IsPIndependent`: linear independence of `pMonomial p b` over
  `(frobenius k p).fieldRange`.

## Main results

* `TauCeti.isPIndependent_iff_finset`: `p`-independence has finite character.
* `TauCeti.isPIndependent_pair_iff_linearIndependent`: `p`-independence of `![a, b]` is linear
  independence of the monomials `a ^ i * b ^ j` over the field range of Frobenius.
* `TauCeti.isPIndependent_pair_iff`: coefficient criterion for `IsPIndependent p ![a, b]`.
* `TauCeti.IsPIndependent.eq_zero_of_sum_pow_mul_C_pair`: a `p`-independent pair stays
  `p`-independent over the `p`-th powers of `k[X]`.
* `TauCeti.notMem_span_pair_of_pow_eq`: `α ∉ k + k β` for `p`-th roots `α` of `a` and `β` of `b`
  in an extension of `k`.

## References

* H. Matsumura, *Commutative Ring Theory*, second edition, Cambridge University Press, 1989, §26.
* S. Lang, *Algebra*, 3rd ed., GTM 211, Springer, 2002, Chapter VIII, Section 4, on separable
  and regular extensions.
-/

public section

namespace TauCeti

section PMonomial

variable (p : ℕ) [NeZero p] {ι ι' M : Type*} [CommMonoid M]

/-- The `p`-monomial `∏ i, b i ^ (e i : ℕ)` attached to a family `b : ι → M` and a finitely
supported exponent function `e : ι →₀ Fin p`. -/
def pMonomial (b : ι → M) (e : ι →₀ Fin p) : M :=
  e.prod fun i n ↦ b i ^ (n : ℕ)

/-- Unfolding `pMonomial` as a `Finsupp.prod`. -/
theorem pMonomial_def (b : ι → M) (e : ι →₀ Fin p) :
    pMonomial p b e = e.prod fun i n ↦ b i ^ (n : ℕ) :=
  (rfl)

/-- The empty exponent gives the unit `p`-monomial `1`. -/
@[simp]
theorem pMonomial_zero (b : ι → M) : pMonomial p b 0 = 1 :=
  Finsupp.prod_zero_index

/-- A single-coordinate exponent gives a single power of the corresponding generator. -/
@[simp]
theorem pMonomial_single (b : ι → M) (i : ι) (n : Fin p) :
    pMonomial p b (Finsupp.single i n) = b i ^ (n : ℕ) :=
  Finsupp.prod_single_index (pow_zero _)

/-- A unit exponent in coordinate `i` recovers `b i`. -/
theorem pMonomial_single_one (hp : 1 < p) (b : ι → M) (i : ι) :
    pMonomial p b (Finsupp.single i 1) = b i := by
  simp [pMonomial_single, Nat.mod_eq_of_lt hp]

/-- On a finite index type, `pMonomial` is the ordinary finite product over all indices. -/
theorem pMonomial_eq_fintype_prod [Fintype ι] (b : ι → M) (e : ι →₀ Fin p) :
    pMonomial p b e = ∏ i, b i ^ (e i : ℕ) :=
  Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _

/-- Reindexing `pMonomial` along `Finsupp.equivFunOnFinite.symm` gives the finite-product family
indexed by `ι → Fin p`. -/
theorem pMonomial_comp_equivFunOnFinite_symm [Fintype ι] (b : ι → M) :
    pMonomial p b ∘ Finsupp.equivFunOnFinite.symm = fun e : ι → Fin p ↦ ∏ i, b i ^ (e i : ℕ) :=
  funext fun e ↦ by
    simpa using pMonomial_eq_fintype_prod p b (Finsupp.equivFunOnFinite.symm e)

/-- Reindexing along an injective map corresponds to `Finsupp.mapDomain` on exponents. -/
theorem pMonomial_comp_of_injective (b : ι → M) {f : ι' → ι} (hf : Function.Injective f)
    (e : ι' →₀ Fin p) : pMonomial p (b ∘ f) e = pMonomial p b (e.mapDomain f) := by
  unfold pMonomial
  convert (Finsupp.prod_mapDomain_index_inj
    (s := e) (h := fun i (n : Fin p) ↦ b i ^ (n : ℕ)) hf).symm using 1
  rfl

/-- Reindexing along `Option.elim' x b` splits off the `none` power from the `some` monomial. -/
theorem pMonomial_option_elim' (x : M) (b : ι → M) (e : Option ι →₀ Fin p) :
    pMonomial p (Option.elim' x b) e = x ^ (e none : ℕ) * pMonomial p b e.some := by
  have he : pMonomial p (Option.elim' x b) e =
      (e.mapRange Fin.val (Fin.val_zero p)).prod fun o n ↦ Option.elim' x b o ^ n := by
    rw [pMonomial_def, Finsupp.prod_mapRange_index (fun _ ↦ pow_zero _)]
  have he_some : pMonomial p b e.some =
      (e.some.mapRange Fin.val (Fin.val_zero p)).prod fun i n ↦ b i ^ n := by
    rw [pMonomial_def, Finsupp.prod_mapRange_index (fun _ ↦ pow_zero _)]
  have hsome : (e.mapRange Fin.val (Fin.val_zero p)).some =
      e.some.mapRange Fin.val (Fin.val_zero p) := by
    ext i
    simp [Finsupp.some_apply, Finsupp.mapRange_apply]
  rw [he, he_some, Finsupp.prod_option_index _ _ (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _),
    Finsupp.mapRange_apply, hsome]
  simp only [Option.elim'_none, Option.elim'_some]

/-- The product of two `p`-monomials differs from the `p`-monomial of their modulo-`p` sum by a
`p`-th power. -/
theorem exists_mul_pMonomial_eq_pow_mul_pMonomial_add (b : ι → M) (e f : ι →₀ Fin p) :
    ∃ c : M, pMonomial p b e * pMonomial p b f = c ^ p * pMonomial p b (e + f) := by
  classical
  let s : Finset ι := e.support ∪ f.support
  refine ⟨∏ i ∈ s, b i ^ (((e i : ℕ) + (f i : ℕ)) / p), ?_⟩
  have he : pMonomial p b e = ∏ i ∈ s, b i ^ (e i : ℕ) :=
    Finsupp.prod_of_support_subset _ Finset.subset_union_left _ fun _ _ ↦ pow_zero _
  have hf : pMonomial p b f = ∏ i ∈ s, b i ^ (f i : ℕ) :=
    Finsupp.prod_of_support_subset _ Finset.subset_union_right _ fun _ _ ↦ pow_zero _
  have hef : pMonomial p b (e + f) = ∏ i ∈ s, b i ^ ((e + f) i : ℕ) :=
    Finsupp.prod_of_support_subset _ Finsupp.support_add _ fun _ _ ↦ pow_zero _
  have hexp : ∀ i, p * (((e i : ℕ) + (f i : ℕ)) / p) + ((e + f) i : ℕ) = (e i : ℕ) + (f i : ℕ) := by
    intro i
    rw [Finsupp.add_apply, Fin.val_add, Nat.div_add_mod]
  rw [he, hf, hef, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← pow_mul, mul_comm _ p, ← pow_add, ← pow_add, hexp i]

/-- Multiplying the decremented `p`-monomial at a nonzero coordinate `j` by `b j` recovers the
original `p`-monomial. -/
theorem mul_pMonomial_sub_single (b : ι → M) (e : ι →₀ Fin p) {j : ι} (hj : e j ≠ 0) :
    b j * pMonomial p b (e - Finsupp.single j 1) = pMonomial p b e := by
  let e' : ι →₀ Fin p := e - Finsupp.single j 1
  have h1 : pMonomial p b e' =
      b j ^ (e' j : ℕ) * (e'.erase j).prod fun i n ↦ b i ^ (n : ℕ) :=
    (Finsupp.mul_prod_erase' e' j (fun i (n : Fin p) ↦ b i ^ (n : ℕ)) fun _ ↦ pow_zero _).symm
  have h2 : pMonomial p b e =
      b j ^ (e j : ℕ) * (e.erase j).prod fun i n ↦ b i ^ (n : ℕ) :=
    (Finsupp.mul_prod_erase' e j (fun i (n : Fin p) ↦ b i ^ (n : ℕ)) fun _ ↦ pow_zero _).symm
  have herase : e'.erase j = e.erase j := by
    ext i
    by_cases hij : i = j
    · simp [hij]
    · simp [e', hij]
  have hj1 : 1 ≤ (e j : ℕ) := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Fin.val_ne_zero_iff.mpr hj))
  have hval : (e' j : ℕ) = (e j : ℕ) - 1 := by
    simpa [e'] using Fin.val_sub_one_of_ne_zero hj
  rw [h1, h2, herase, ← mul_assoc, ← pow_succ', hval, Nat.sub_add_cancel hj1]

end PMonomial

section ExpCharField

variable {p : ℕ} {k : Type*} [Field k] [ExpChar k p] {ι ι' : Type*}

/-- A family `b : ι → k` in a field `k` of exponential characteristic `p` is **`p`-independent**
when its `p`-monomials `∏ i, b i ^ (e i : ℕ)` (`e : ι →₀ Fin p`) are linearly independent over
the subfield `k ^ p` of `p`-th powers. -/
def IsPIndependent (p : ℕ) {k : Type*} [Field k] [ExpChar k p] {ι : Type*} (b : ι → k) : Prop :=
  have : NeZero p := ⟨expChar_ne_zero k p⟩
  LinearIndependent (frobenius k p).fieldRange (pMonomial p b)

/-- Unfolding `IsPIndependent` as linear independence of the `p`-monomials over `k ^ p`. -/
theorem isPIndependent_iff (b : ι → k) :
    IsPIndependent p b ↔
      LinearIndependent (frobenius k p).fieldRange (@pMonomial p ⟨expChar_ne_zero k p⟩ _ _ _ b) :=
  Iff.rfl

/-- Unfold `IsPIndependent` to linear independence of the `p`-monomials over `k ^ p`. -/
theorem IsPIndependent.linearIndependent {b : ι → k} (hb : IsPIndependent p b) :
    LinearIndependent (frobenius k p).fieldRange (@pMonomial p ⟨expChar_ne_zero k p⟩ _ _ _ b) :=
  hb

/-- For a finite index type, `IsPIndependent` is linear independence of `e ↦ ∏ i, b i ^ e i`
indexed by `ι → Fin p`. -/
theorem isPIndependent_iff_fintype [Fintype ι] (b : ι → k) :
    IsPIndependent p b ↔
      LinearIndependent (frobenius k p).fieldRange (fun e : ι → Fin p ↦ ∏ i, b i ^ (e i : ℕ)) := by
  have : NeZero p := ⟨expChar_ne_zero k p⟩
  rw [← pMonomial_comp_equivFunOnFinite_symm, IsPIndependent, linearIndependent_equiv]

/-- Composing a `p`-independent family with an injective map preserves `p`-independence. -/
theorem IsPIndependent.comp {b : ι → k} (hb : IsPIndependent p b) {f : ι' → ι}
    (hf : Function.Injective f) : IsPIndependent p (b ∘ f) := by
  have : NeZero p := ⟨expChar_ne_zero k p⟩
  have hcomp : pMonomial p (b ∘ f) = pMonomial p b ∘ Finsupp.mapDomain f :=
    funext fun e ↦ pMonomial_comp_of_injective p b hf e
  rw [isPIndependent_iff, hcomp]
  exact hb.linearIndependent.comp _ (Finsupp.mapDomain_injective hf)

/-- `p`-independence is invariant under reindexing by an equivalence. -/
theorem isPIndependent_equiv (b : ι → k) (e : ι' ≃ ι) :
    IsPIndependent p (b ∘ e) ↔ IsPIndependent p b :=
  ⟨fun h ↦ by
    have := h.comp e.symm.injective
    rwa [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at this,
    fun h ↦ h.comp e.injective⟩

/-- Any empty family is `p`-independent. -/
theorem isPIndependent_empty [IsEmpty ι] (b : ι → k) : IsPIndependent p b := by
  have : NeZero p := ⟨expChar_ne_zero k p⟩
  rw [IsPIndependent]
  exact LinearIndependent.of_subsingleton 0 (by simp)

/-- `p`-independence has finite character: a family is `p`-independent iff every finite subfamily
is `p`-independent. -/
theorem isPIndependent_iff_finset (b : ι → k) :
    IsPIndependent p b ↔ ∀ s : Finset ι, IsPIndependent p (fun i : s ↦ b i) := by
  have : NeZero p := ⟨expChar_ne_zero k p⟩
  refine ⟨fun hb s ↦ hb.comp Subtype.val_injective, fun h ↦ ?_⟩
  classical
  rw [IsPIndependent, linearIndependent_iff_finset_linearIndependent]
  intro t
  let s : Finset ι := t.biUnion Finsupp.support
  have hs : ∀ f ∈ t, (↑f.support : Set ι) ⊆ (s : Set ι) := fun f hf _ ha ↦
    Finset.mem_biUnion.mpr ⟨f, hf, ha⟩
  let emb : (s →₀ Fin p) → (ι →₀ Fin p) := Finsupp.mapDomain Subtype.val
  let proj : (ι →₀ Fin p) → (s →₀ Fin p) := Finsupp.subtypeDomain (· ∈ s)
  have hsect : ∀ f ∈ t, emb (proj f) = f := fun f hf ↦
    Finsupp.mapDomain_subtypeDomain_subtype (hs f hf)
  have hsub : pMonomial p b ∘ (Subtype.val : t → ι →₀ Fin p) =
      (fun g : s →₀ Fin p ↦ pMonomial p (fun i : s ↦ b i) g) ∘ (fun f : t ↦ proj f) := by
    ext f
    have hpm : pMonomial p (fun i : s ↦ b i) (proj f.val) = pMonomial p b (emb (proj f.val)) :=
      pMonomial_comp_of_injective p b Subtype.val_injective (proj f.val)
    rw [Function.comp_apply, Function.comp_apply, hpm, hsect f.val f.property]
  rw [hsub]
  refine (h s).linearIndependent.comp _ fun f₁ f₂ heq ↦ Subtype.ext ?_
  rw [← hsect f₁.val f₁.property, ← hsect f₂.val f₂.property, heq]

/-- Every element of a `p`-independent family is nonzero. -/
theorem IsPIndependent.ne_zero [Fact p.Prime] {b : ι → k} (hb : IsPIndependent p b) (i : ι) :
    b i ≠ 0 := by
  have h := hb.linearIndependent.ne_zero (Finsupp.single i (1 : Fin p))
  rwa [pMonomial_single_one p (Fact.out : p.Prime).one_lt] at h

/-- A `p`-independent family is injective. -/
theorem IsPIndependent.injective [Fact p.Prime] {b : ι → k} (hb : IsPIndependent p b) :
    Function.Injective b := by
  intro i j hij
  have h1 : pMonomial p b (Finsupp.single i (1 : Fin p)) =
      pMonomial p b (Finsupp.single j (1 : Fin p)) := by
    rw [pMonomial_single_one p (Fact.out : p.Prime).one_lt,
      pMonomial_single_one p (Fact.out : p.Prime).one_lt, hij]
  have hne : (1 : Fin p) ≠ 0 := by
    simp [Fin.ext_iff, Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt]
  exact Finsupp.single_left_injective hne (hb.linearIndependent.injective h1)

end ExpCharField

section Pair

open Finset

variable {k : Type*} [Field k] {p : ℕ} {a b : k}

/-- Two elements `a` and `b` form a `p`-independent family `![a, b]` exactly when the monomials
`a ^ i * b ^ j` with `i, j < p` are linearly independent over the field range `k ^ p` of
Frobenius. -/
theorem isPIndependent_pair_iff_linearIndependent [ExpChar k p] :
    IsPIndependent p ![a, b] ↔ LinearIndependent (frobenius k p).fieldRange
      (fun ij : Fin p × Fin p ↦ a ^ (ij.1 : ℕ) * b ^ (ij.2 : ℕ)) := by
  have heq : (fun ij : Fin p × Fin p ↦ a ^ (ij.1 : ℕ) * b ^ (ij.2 : ℕ)) =
      (fun e : Fin 2 → Fin p ↦ ∏ i, ![a, b] i ^ (e i : ℕ)) ∘ (finTwoArrowEquiv (Fin p)).symm := by
    ext ⟨i, j⟩
    simp [Fin.prod_univ_two, finTwoArrowEquiv]
  rw [isPIndependent_iff_fintype, heq, linearIndependent_equiv]

/-- Unfolding `IsPIndependent p ![a, b]` as the vanishing criterion for `∑ cᵢⱼ ^ p * a ^ i * b ^ j`
with `i, j < p`. -/
theorem isPIndependent_pair_iff [ExpChar k p] :
    IsPIndependent p ![a, b] ↔ ∀ c : ℕ → ℕ → k,
      ∑ i ∈ range p, ∑ j ∈ range p, c i j ^ p * a ^ i * b ^ j = 0 →
        ∀ i < p, ∀ j < p, c i j = 0 := by
  have hp : p ≠ 0 := (expChar_pos k p).ne'
  rw [isPIndependent_pair_iff_linearIndependent, Fintype.linearIndependent_iff]
  constructor
  · intro h c hc i hi j hj
    have := h (fun ij ↦ ⟨c ij.1 ij.2 ^ p, c ij.1 ij.2, frobenius_def ..⟩) ?_ (⟨i, hi⟩, ⟨j, hj⟩)
    · simpa [Subtype.ext_iff, hp] using this
    · rw [Fintype.sum_prod_type]
      simpa [sum_range, Subfield.smul_def, mul_assoc] using hc
  · intro h g hg ij
    choose c hc using fun ij ↦ RingHom.mem_fieldRange.mp (g ij).property
    have := h (fun i j ↦ if h : i < p ∧ j < p then c (⟨i, h.1⟩, ⟨j, h.2⟩) else 0) ?_
      ij.1 ij.1.isLt ij.2 ij.2.isLt
    · rw [Subtype.ext_iff, ← hc]
      simpa using this
    · rw [Fintype.sum_prod_type] at hg
      simpa [sum_range, Subfield.smul_def, ← hc, frobenius_def, mul_assoc] using hg

/-- A vanishing combination `∑ cᵢⱼ ^ p a ^ i b ^ j` of a `p`-independent pair has all its
coefficients `cᵢⱼ` with `i, j < p` equal to zero. -/
theorem IsPIndependent.eq_zero_of_sum_pow_mul_pair [ExpChar k p] (hab : IsPIndependent p ![a, b])
    {c : ℕ → ℕ → k} (h : ∑ i ∈ range p, ∑ j ∈ range p, c i j ^ p * a ^ i * b ^ j = 0)
    {i j : ℕ} (hi : i < p) (hj : j < p) : c i j = 0 :=
  isPIndependent_pair_iff.mp hab c h i hi j hj

open Polynomial in
/-- `p`-independence of `a` and `b` over `k ^ p` gives `p`-independence over `k[X] ^ p`: a
vanishing combination `∑ Pᵢⱼ ^ p a ^ i b ^ j` with polynomial `Pᵢⱼ` has `Pᵢⱼ = 0` for `i, j < p`. -/
theorem IsPIndependent.eq_zero_of_sum_pow_mul_C_pair [ExpChar k p]
    (hab : IsPIndependent p ![a, b]) {P : ℕ → ℕ → k[X]}
    (h : ∑ i ∈ range p, ∑ j ∈ range p, P i j ^ p * C (a ^ i * b ^ j) = 0) {i j : ℕ} (hi : i < p)
    (hj : j < p) : P i j = 0 := by
  ext n
  have hn := congrArg (fun q : k[X] ↦ q.coeff (p * n)) h
  simp only [finsetSum_coeff, coeff_mul_C, coeff_pow_char_mul, coeff_zero] at hn
  exact hab.eq_zero_of_sum_pow_mul_pair (c := fun i j ↦ (P i j).coeff n)
    (by simpa only [mul_assoc] using hn) hi hj

/-- `α ∉ k + k β` when `α` and `β` are `p`-th roots of a `p`-independent pair `a, b`. -/
theorem notMem_span_pair_of_pow_eq [hp : Fact p.Prime] [CharP k p]
    (hab : IsPIndependent p ![a, b]) {K : Type*} [Field K] [Algebra k K] {α β : K}
    (hα : α ^ p = algebraMap k K a) (hβ : β ^ p = algebraMap k K b) :
    α ∉ Submodule.span k {1, β} := by
  have := charP_of_injective_algebraMap (algebraMap k K).injective p
  rw [Submodule.mem_span_pair]
  rintro ⟨c₀, c₂, h⟩
  have hpow := congrArg (· ^ p) h
  simp only [add_pow_char, Algebra.smul_def, mul_pow, mul_one, hα, hβ, ← map_pow,
    ← map_mul, ← map_add] at hpow
  have := hab.eq_zero_of_sum_pow_mul_pair (c := fun i j ↦ if i = 0 ∧ j = 0 then c₀ else
      if i = 1 ∧ j = 0 then -1 else if i = 0 ∧ j = 1 then c₂ else 0) ?_ hp.out.one_lt hp.out.pos
  · simp at this
  · have hpa := (algebraMap k K).injective hpow
    have hp0 : p ≠ 0 := hp.out.ne_zero
    have h0 : 0 ∈ range p := mem_range.mpr hp.out.pos
    have h1 : 1 ∈ range p := mem_range.mpr hp.out.one_lt
    rw [sum_eq_add 0 1 zero_ne_one (fun i _ hi ↦ sum_eq_zero fun j _ ↦ by
        simp [hi.1, hi.2, zero_pow hp0]) (absurd h0) (absurd h1),
      sum_eq_add 0 1 zero_ne_one (fun j _ hj ↦ by simp [hj.1, hj.2, zero_pow hp0])
        (absurd h0) (absurd h1),
      sum_eq_single 0 (fun j _ hj ↦ by simp [hj, zero_pow hp0]) (absurd h0)]
    simp only [and_true, one_ne_zero, zero_ne_one, and_false, ite_true, ite_false, pow_zero,
      pow_one, mul_one, neg_one_pow_char]
    linear_combination hpa

end Pair

end TauCeti
