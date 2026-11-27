/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Oscillator.Highest
import TauCeti.RingTheory.MvPolynomial.DeterminantalIdeal

/-!
# Products of staircase minors are jointly highest vectors

Consider the Fock module `MvPolynomial (I × I') K` of the dual pair of a definite and an
indefinite unitary group (`TauCeti/Algebra/Lie/GeneralLinear/Oscillator/DualPair.lean`): the rows
`I` all have the sign `true`, the columns `I'` have the signs `ε'`. Let `l' : I → ℤ` and
`l : I' → ℤ` be injective. Read the rows in the decreasing order of `l'`, and the columns of each
sign `η` in the decreasing order of `η · l` (decreasing `l` for `η = true`, increasing for
`η = false`).

The **staircase minor** `M_p` (`TauCeti.staircaseMinor`) is the `p × p` minor of the matrix of
variables on the first `p` rows in the decreasing order of `l'` and the first `p` columns `c` with
`ε' c` in the decreasing order of `l`, the `i`-th row paired with the `i`-th column; it is indexed
by the pairs of a row and a column at the same position (`TauCeti.staircasePairs`). The minor
`M_{-,p}` on the first `p` rows in the decreasing order of `-l'` and the first `p` columns of sign
`false` in the decreasing order of `-l` is the same construction for the signs `!ε'` and the keys
`-l'`, `-l`. For exponents `k : Bool → ℕ → ℕ` the **staircase product**
(`TauCeti.staircaseProd`) is

`P = ∏_{p < |I|} M_{+,p} ^ k true p * ∏_{p < |I|} M_{-,p} ^ k false p`.

The main results say that `P` is a joint highest vector of the dual pair:

* `P ≠ 0` (`TauCeti.staircaseProd_ne_zero`);
* `P` is termwise harmonic for the columns when `k true i = 0` or `k false j = 0` for
  `i, j < |I|` with `|I| < i + j` (`TauCeti.isColTermwiseHarmonic_staircaseProd`), while every
  polynomial is termwise harmonic for the rows, which all have one sign
  (`TauCeti.isRowTermwiseHarmonic_const`);
* when `k η p = 0` for `p < |I|` whenever fewer than `p` columns have the sign `η`, `P` is
  `K`-highest for the row action in the order of `l'`, of weight
  `ν₀ + ∑_{q₊(a) < j < |I|} k true j - ∑_{q₋(a) < j < |I|} k false j` at the row `a`, where `ν₀` is
  the weight of the vacuum and `q₊(a)`, `q₋(a)` are the positions of `a` in the decreasing and the
  increasing order of `l'` (`TauCeti.isKHighest_fockRowHom_staircaseProd`);
* `P` is `K`-highest for the column action in the order of `l`, of weight
  `ν'₀(c) + s_c ∑_{o(c) < j < |I|} k (ε' c) j` at the column `c`, where `s_c = ±1` is the sign of
  `c` and `o(c)` is the position of `c` among the columns of its sign in the decreasing order of
  `s_c · l` (`TauCeti.isKHighest_fockColHom_staircaseProd`).

Each minor is killed by the compact raising operators of both actions because its rows and its
columns are initial segments of their orders, and it is a polynomial in variables of one parity;
powers and products keep these properties, and the weights relative to the vacuum add
(`TauCeti/Algebra/Lie/GeneralLinear/Oscillator/Highest.lean`). The rows of the minors of the two
signs are disjoint under the condition on `k`, which gives the termwise harmonicity.

## Conventions

The row action `TauCeti.fockRowHom` is that of the Fock datum with the sign `σ = 1` and the shift
`γ = |I'| / 2`; since the weights are stated relative to the weight of the vacuum, they do not
depend on the shift. The column action `TauCeti.fockColHom` is normalised as
`E c d ↦ ∑ a, R a c L a d + (n / 2) δ c d`, with `n = |I|`. In the convention where the column
action is `E c d ↦ -∑ a, L a c R a d + γ' δ c d`, which is its contragredient `X ↦ -Xᵀ` shifted
by `γ' - n / 2`, a vector `K`-highest of weight `ν'` in the order
of `l` here is `K`-highest of weight `γ' - n / 2 - ν'` in the order of `-l` there, and the weight
of the column `c` reads `ν'₀(c) - s_c ∑_{o(c) < j < |I|} k (ε' c) j` with `ν'₀` the weight of the
vacuum there.

## Main definitions

* `TauCeti.staircasePairs`, `TauCeti.staircaseMinor`: the staircase minor `M_p`.
* `TauCeti.staircaseProd`: the staircase product `P`.

## Main results

* `TauCeti.staircaseMinor_ne_zero`, `TauCeti.staircaseProd_ne_zero`: nonvanishing.
* `TauCeti.isColTermwiseHarmonic_staircaseProd`: termwise harmonicity for the columns.
* `TauCeti.isKHighest_fockRowHom_staircaseProd`, `TauCeti.isKHighest_fockColHom_staircaseProd`:
  the staircase product is `K`-highest for both actions, with its two weights.

## References

* R. Howe, *Transcending classical invariant theory*, J. Amer. Math. Soc. 2 (1989), 535--552.
* M. Kashiwara and M. Vergne, *On the Segal–Shale–Weil representations and harmonic
  polynomials*, Invent. Math. 44 (1978), 1--47.
* The result corresponds to `New.isJointHighest_prod_det_pow_staircaseWeight`, with the minors
  `New.staircaseBlock` and the weights `New.staircaseWeight`, in `src/Lib/Weil/Lift.lean` of
  grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace TauCeti

open MvPolynomial Finset Matrix Function

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Positions in a decreasing order -/

section Position

variable {ι : Type*} {s : Finset ι} {f : ι → ℤ}

/-- An element with a larger key comes earlier in the decreasing order of the keys. -/
private theorem card_filter_lt_lt_of_lt {a b : ι} (hb : b ∈ s) (h : f a < f b) :
    #{c ∈ s | f b < f c} < #{c ∈ s | f a < f c} := by
  refine card_lt_card ((ssubset_iff_of_subset fun c hc ↦ ?_).2 ⟨b, ?_, ?_⟩)
  · simp only [mem_filter] at hc ⊢
    exact ⟨hc.1, h.trans hc.2⟩
  · simp [hb, h]
  · simp

/-- The position of an element of `s` is less than the size of `s`. -/
private theorem card_filter_lt_lt_card {a : ι} (ha : a ∈ s) : #{c ∈ s | f a < f c} < #s :=
  card_lt_card (filter_ssubset.2 ⟨a, ha, lt_irrefl _⟩)

/-- For keys injective on `s`, the positions of the elements of `s` are distinct. -/
private theorem injOn_card_filter_lt (hf : Set.InjOn f s) :
    Set.InjOn (fun a ↦ #{c ∈ s | f a < f c}) s := by
  intro a ha b hb hab
  rcases lt_trichotomy (f a) (f b) with h | h | h
  · exact absurd hab (card_filter_lt_lt_of_lt hb h).ne'
  · exact hf ha hb h
  · exact absurd hab (card_filter_lt_lt_of_lt ha h).ne

/-- For keys injective on `s`, every position below the size of `s` is the position of an element
of `s`. -/
private theorem exists_card_filter_lt_eq (hf : Set.InjOn f s) {j : ℕ} (hj : j < #s) :
    ∃ a ∈ s, #{c ∈ s | f a < f c} = j :=
  surjOn_of_injOn_of_card_le (fun a ↦ #{c ∈ s | f a < f c})
    (fun _ ha ↦ mem_coe.2 (mem_range.2 (card_filter_lt_lt_card ha))) (injOn_card_filter_lt hf)
    (by simp) (mem_coe.2 (mem_range.2 hj))

/-- For injective keys on a finite type, the positions of an element in the decreasing and the
increasing order add up to the number of the other elements. -/
private theorem card_filter_lt_add_card_filter_gt [Fintype ι] (hf : Injective f)
    (a : ι) : #{c | f a < f c} + #{c | f c < f a} + 1 = Fintype.card ι := by
  classical
  have h : ({c | f a < f c} : Finset ι) ∪ ({c | f c < f a} : Finset ι) = univ.erase a := by
    ext c
    simp only [mem_union, mem_filter, mem_univ, true_and, mem_erase, and_true]
    exact ⟨by rintro (h | h) rfl <;> exact lt_irrefl _ h,
      fun hc ↦ lt_or_gt_of_ne fun h ↦ hc (hf h).symm⟩
  rw [← card_union_of_disjoint (disjoint_filter.2 fun c _ h h' ↦ lt_asymm h h'), h,
    card_erase_of_mem (mem_univ a), card_univ, Nat.sub_add_cancel (Fintype.card_pos_iff.2 ⟨a⟩)]

end Position

/-! ### Staircase minors -/

variable {I I' : Type*} [Fintype I] [Fintype I']

section Minor

variable (ε' : I' → Bool) (l' : I → ℤ) (l : I' → ℤ)

/-- The pairs `(a, c)` of a row and a column of the staircase minor `M_p` of
`TauCeti.staircaseMinor`: `c` is among the first `p` columns with `ε' c` in the decreasing order
of `l`, and `a` is the row at the same position in the decreasing order of `l'`. -/
def staircasePairs (p : ℕ) : Finset (I × I') :=
  {x | ε' x.2 ∧ #{d | ε' d ∧ l x.2 < l d} < p ∧ #{b | l' x.1 < l' b} = #{d | ε' d ∧ l x.2 < l d}}

/-- Membership in `TauCeti.staircasePairs`: the column has `ε'`, its position among those columns
in the decreasing order of `l` is less than `p`, and the row has the same position in the
decreasing order of `l'`. -/
@[simp]
theorem mem_staircasePairs {p : ℕ} {x : I × I'} :
    x ∈ staircasePairs ε' l' l p ↔ ε' x.2 ∧ #{d | ε' d ∧ l x.2 < l d} < p ∧
      #{b | l' x.1 < l' b} = #{d | ε' d ∧ l x.2 < l d} := by
  simp [staircasePairs]

variable {ε' l' l} {p : ℕ}

/-- The columns of the staircase minor have `ε'`. -/
private theorem staircasePairs_snd (x : staircasePairs ε' l' l p) : ε' x.val.2 = true :=
  ((mem_staircasePairs ε' l' l).1 x.property).1

/-- The column of a pair of the staircase minor determines it. -/
private theorem injective_staircasePairs_fst (hl : Set.InjOn l {c | ε' c}) :
    Injective fun x : staircasePairs ε' l' l p ↦ x.val.1 := by
  intro x y (hxy : x.val.1 = y.val.1)
  have hx := (mem_staircasePairs ε' l' l).1 x.property
  have hy := (mem_staircasePairs ε' l' l).1 y.property
  have hcol : x.val.2 = y.val.2 := by
    refine injOn_card_filter_lt (s := {d | ε' d}) (f := l) (fun c hc d hd h ↦ ?_)
      (by simpa using hx.1) (by simpa using hy.1) ?_
    · exact hl (by simpa using hc) (by simpa using hd) h
    · simp only [filter_filter]
      rw [← hx.2.2, ← hy.2.2, hxy]
  exact Subtype.ext (Prod.ext hxy hcol)

/-- The row of a pair of the staircase minor determines it. -/
private theorem injective_staircasePairs_snd (hl' : Injective l') :
    Injective fun x : staircasePairs ε' l' l p ↦ x.val.2 := by
  intro x y (hxy : x.val.2 = y.val.2)
  have hx := (mem_staircasePairs ε' l' l).1 x.property
  have hy := (mem_staircasePairs ε' l' l).1 y.property
  have hrow : x.val.1 = y.val.1 :=
    injOn_card_filter_lt (s := univ) (f := l') hl'.injOn (mem_univ _) (mem_univ _)
      (by simp only [hx.2.2, hy.2.2]; rw [hxy])
  exact Subtype.ext (Prod.ext hrow hxy)

/-- The rows of the staircase minor `M_p` are the rows at the positions below `p` and below the
number of columns with `ε'`. -/
private theorem mem_range_staircasePairs_fst (hl : Set.InjOn l {c | ε' c}) {a : I} :
    a ∈ Set.range (fun x : staircasePairs ε' l' l p ↦ x.val.1) ↔
      #{b | l' a < l' b} < p ∧ #{b | l' a < l' b} < #{c | ε' c} := by
  constructor
  · rintro ⟨x, rfl⟩
    have hx := (mem_staircasePairs ε' l' l).1 x.property
    refine ⟨hx.2.2 ▸ hx.2.1, hx.2.2 ▸ ?_⟩
    have h := card_filter_lt_lt_card (s := {d | ε' d}) (f := l) (a := x.val.2)
      (by simpa using hx.1)
    simpa [filter_filter] using h
  · rintro ⟨hp, hc⟩
    obtain ⟨c, hc, hpos⟩ := exists_card_filter_lt_eq (s := {d | ε' d}) (f := l)
      (fun c hc d hd h ↦ hl (by simpa using hc) (by simpa using hd) h) hc
    simp only [filter_filter] at hpos
    refine ⟨⟨(a, c), (mem_staircasePairs ε' l' l).2 ⟨by simpa using hc, ?_, ?_⟩⟩, rfl⟩
    · simpa [hpos] using hp
    · simpa using hpos.symm

/-- The columns of the staircase minor `M_p` are the columns with `ε'` at the positions below `p`
and below the number of rows. -/
private theorem mem_range_staircasePairs_snd (hl' : Injective l') {c : I'} :
    c ∈ Set.range (fun x : staircasePairs ε' l' l p ↦ x.val.2) ↔
      ε' c ∧ #{d | ε' d ∧ l c < l d} < p ∧ #{d | ε' d ∧ l c < l d} < Fintype.card I := by
  constructor
  · rintro ⟨x, rfl⟩
    have hx := (mem_staircasePairs ε' l' l).1 x.property
    refine ⟨hx.1, hx.2.1, hx.2.2 ▸ ?_⟩
    simpa using card_filter_lt_lt_card (s := univ) (f := l') (mem_univ x.val.1)
  · rintro ⟨hc, hp, hn⟩
    obtain ⟨a, -, hpos⟩ := exists_card_filter_lt_eq (s := univ) (f := l') hl'.injOn
      (by simpa using hn)
    exact ⟨⟨(a, c), (mem_staircasePairs ε' l' l).2 ⟨hc, hp, by simpa using hpos⟩⟩, rfl⟩

/-- The rows of the staircase minor `M_p` are at the positions below `p`. -/
private theorem card_lt_of_mem_range_staircasePairs_fst {a : I}
    (ha : a ∈ Set.range (fun x : staircasePairs ε' l' l p ↦ x.val.1)) : #{b | l' a < l' b} < p := by
  obtain ⟨x, rfl⟩ := ha
  have hx := (mem_staircasePairs ε' l' l).1 x.property
  exact hx.2.2 ▸ hx.2.1

variable (ε' l' l) [DecidableEq I] [DecidableEq I'] (K : Type*) [CommRing K]

/-- **The staircase minor** `M_p`: the `p × p` minor of the matrix of variables `(X (a, c))` on
the first `p` rows in the decreasing order of `l'` and the first `p` columns `c` with `ε' c` in
the decreasing order of `l`, the `i`-th row paired with the `i`-th column. It is indexed by the
pairs `TauCeti.staircasePairs` of a row and a column at the same position. If fewer than `p`
columns have `ε'`, or fewer than `p` rows exist, it is the minor on as many rows and columns as
there are. -/
noncomputable def staircaseMinor (p : ℕ) : MvPolynomial (I × I') K :=
  mvPolynomialMinor K (fun x : staircasePairs ε' l' l p ↦ x.val.1) (fun x ↦ x.val.2)

/-- Unfolds `TauCeti.staircaseMinor`. -/
theorem staircaseMinor_def (p : ℕ) :
    staircaseMinor ε' l' l K p =
      mvPolynomialMinor K (fun x : staircasePairs ε' l' l p ↦ x.val.1) (fun x ↦ x.val.2) :=
  (rfl)

/-- **The staircase product** `∏_{p < |I|} M_{+,p} ^ k true p * ∏_{p < |I|} M_{-,p} ^ k false p`,
where `M_{+,p}` is the staircase minor `TauCeti.staircaseMinor` on the first `p` rows in the
decreasing order of `l'` and the first `p` columns of sign `true` in the decreasing order of `l`,
and `M_{-,p}` the one on the first `p` rows in the increasing order of `l'` and the first `p`
columns of sign `false` in the increasing order of `l`. -/
noncomputable def staircaseProd (k : Bool → ℕ → ℕ) : MvPolynomial (I × I') K :=
  (∏ p ∈ range (Fintype.card I), staircaseMinor ε' l' l K p ^ k true p) *
    ∏ p ∈ range (Fintype.card I), staircaseMinor (fun c ↦ !ε' c) (-l') (-l) K p ^ k false p

/-- Unfolds `TauCeti.staircaseProd`. -/
theorem staircaseProd_def (k : Bool → ℕ → ℕ) :
    staircaseProd ε' l' l K k =
      (∏ p ∈ range (Fintype.card I), staircaseMinor ε' l' l K p ^ k true p) *
        ∏ p ∈ range (Fintype.card I), staircaseMinor (fun c ↦ !ε' c) (-l') (-l) K p ^ k false p :=
  (rfl)

variable {l' l} in
/-- **The staircase minor is not zero** for injective keys. -/
theorem staircaseMinor_ne_zero [Nontrivial K] (p : ℕ) (hl' : Injective l') (hl : Injective l) :
    staircaseMinor ε' l' l K p ≠ 0 :=
  mvPolynomialMinor_ne_zero (injective_staircasePairs_fst hl.injOn)
    (injective_staircasePairs_snd hl')

end Minor

/-! ### The staircase product -/

section Product

variable [DecidableEq I] [DecidableEq I'] {ε' : I' → Bool} {l' : I → ℤ} {l : I' → ℤ}

variable (ε' K) in
/-- **The staircase product is not zero** for injective keys. -/
theorem staircaseProd_ne_zero [CommRing K] [IsDomain K] (hl' : Injective l') (hl : Injective l)
    (k : Bool → ℕ → ℕ) : staircaseProd ε' l' l K k ≠ 0 := by
  rw [staircaseProd_def]
  refine mul_ne_zero (prod_ne_zero_iff.2 fun p _ ↦ pow_ne_zero _ ?_)
    (prod_ne_zero_iff.2 fun p _ ↦ pow_ne_zero _ ?_)
  · exact staircaseMinor_ne_zero ε' K p hl' hl
  · exact staircaseMinor_ne_zero _ K p (neg_injective.comp hl') (neg_injective.comp hl)

/-- The staircase minor `M_p` is a polynomial in the variables of its rows, at the positions below
`p`, and its columns, which have `ε'`. -/
private theorem staircaseMinor_mem_supported [CommRing K] (p : ℕ) :
    staircaseMinor ε' l' l K p ∈
      supported K {x | #{b | l' x.1 < l' b} < p ∧ ε' x.2 = true} := by
  refine supported_mono ?_ (mvPolynomialMinor_mem_supported _ _)
  rintro ⟨a, c⟩ ⟨ha, ⟨y, hy⟩⟩
  exact ⟨card_lt_of_mem_range_staircasePairs_fst ha, hy ▸ staircasePairs_snd y⟩

/-- **The staircase product is termwise harmonic for the columns** when `k true i = 0` or
`k false j = 0` for `i, j < |I|` whenever `|I| < i + j`: then the rows of the minors of the two
signs that occur are disjoint, so no row has variables in columns of both signs. -/
theorem isColTermwiseHarmonic_staircaseProd [CommRing K] (hl' : Injective l')
    {k : Bool → ℕ → ℕ} (hk : ∀ i < Fintype.card I, ∀ j < Fintype.card I,
      Fintype.card I < i + j → k true i = 0 ∨ k false j = 0) :
    IsColTermwiseHarmonic ε' (staircaseProd ε' l' l K k) := by
  set n := Fintype.card I
  -- The variables of the minors of sign `true` and of sign `false` that occur in the product.
  set V : Set (I × I') := {x | (∃ i ∈ range n, k true i ≠ 0 ∧ #{b | l' x.1 < l' b} < i) ∧
    ε' x.2 = true} ∪ {x | (∃ j ∈ range n, k false j ≠ 0 ∧ #{b | l' b < l' x.1} < j) ∧
    ε' x.2 = false}
  refine isColTermwiseHarmonic_of_mem_supported (V := V) ?_ ?_
  · rintro a c d (⟨⟨i, hin, hi, hai⟩, hc⟩ | ⟨⟨j, hjn, hj, haj⟩, hc⟩)
      (⟨⟨i', hin', hi', hai'⟩, hd⟩ | ⟨⟨j', hjn', hj', haj'⟩, hd⟩)
    · rw [hc, hd]
    · have h := card_filter_lt_add_card_filter_gt hl' a
      dsimp only at hai haj'
      rcases Nat.lt_or_ge n (i + j') with hn | hn
      · exact absurd ((hk i (mem_range.1 hin) j' (mem_range.1 hjn') hn).resolve_left hi) hj'
      · omega
    · have h := card_filter_lt_add_card_filter_gt hl' a
      dsimp only at hai' haj
      rcases Nat.lt_or_ge n (i' + j) with hn | hn
      · exact absurd ((hk i' (mem_range.1 hin') j (mem_range.1 hjn) hn).resolve_left hi') hj
      · omega
    · rw [hc, hd]
  · rw [staircaseProd_def]
    refine Subalgebra.mul_mem _ (Subalgebra.prod_mem _ fun i hi ↦ ?_)
      (Subalgebra.prod_mem _ fun j hj ↦ ?_)
    · by_cases hki : k true i = 0
      · simp [hki]
      refine Subalgebra.pow_mem _ (supported_mono ?_ (staircaseMinor_mem_supported i)) _
      exact fun x hx ↦ Or.inl ⟨⟨i, hi, hki, hx.1⟩, hx.2⟩
    · by_cases hkj : k false j = 0
      · simp [hkj]
      refine Subalgebra.pow_mem _ (supported_mono ?_ (staircaseMinor_mem_supported j)) _
      refine fun x hx ↦ Or.inr ⟨⟨j, hj, hkj, ?_⟩, ?_⟩
      · simpa using hx.1
      · simpa using hx.2

/-! ### `K`-highest weights -/

/-- A sum over the positions `p < n` of `k p` times the indicator of `q < p` and `q < C`, where
`k p = 0` for the positions `C < p`, is the sum of the `k p` over `q < p < n`. -/
private theorem sum_range_mul_ite_eq_sum_Ioo {K : Type*} [Semiring K] {n q C : ℕ} {k : ℕ → ℕ}
    (hk : ∀ p ∈ range n, C < p → k p = 0) :
    ∑ p ∈ range n, (k p : K) * (if q < p ∧ q < C then 1 else 0) = ∑ p ∈ Ioo q n, (k p : K) := by
  have hIoo : Ioo q n = {p ∈ range n | q < p} := by
    ext p
    simp only [mem_Ioo, mem_filter, mem_range]
    omega
  rw [hIoo, sum_filter]
  refine sum_congr rfl fun p hp ↦ ?_
  by_cases hqp : q < p
  · by_cases hqC : q < C
    · simp [hqp, hqC]
    · simp [hqp, hqC, hk p hp (by omega)]
  · simp [hqp]

/-- The sum of `sum_range_mul_ite_eq_sum_Ioo` with a further condition `P` in the indicator. -/
private theorem sum_range_mul_ite_and_eq {K : Type*} [Semiring K] {n q C : ℕ} {k : ℕ → ℕ}
    (P : Prop) [Decidable P] (hk : ∀ p ∈ range n, C < p → k p = 0) :
    ∑ p ∈ range n, (k p : K) * (if P ∧ q < p ∧ q < C then 1 else 0) =
      if P then ∑ p ∈ Ioo q n, (k p : K) else 0 := by
  by_cases hP : P
  · simpa [hP] using sum_range_mul_ite_eq_sum_Ioo (K := K) hk
  · simp [hP]

variable [Field K] [NeZero (2 : K)]

/-- The staircase minor `M_{+,p}` is `K`-highest for the rows in the order of `l'`, of the weight
of the vacuum plus one on its rows. -/
private theorem isKHighest_fockRowHom_staircaseMinor (hl : Set.InjOn l {c | ε' c}) (p : ℕ) :
    IsKHighest (fockRowHom K (fun _ ↦ true) ε') (fun _ ↦ true) l'
      ((fun a ↦ ((#{c | (fun _ : I ↦ true) a = ε' c} : K) -
        #{c | (fun _ : I ↦ true) a ≠ ε' c}) / 2) +
        (Set.range fun x : staircasePairs ε' l' l p ↦ x.val.1).indicator 1)
      (staircaseMinor ε' l' l K p) := by
  refine isKHighest_fockRowHom_mvPolynomialMinor_of_isEvenPair (isKHighest_fockRowHom_one _ _ l')
    (fun _ y ↦ isEvenPair_iff.2 (staircasePairs_snd y).symm) ?_
  intro a b _ hlt hb
  rw [mem_range_staircasePairs_fst hl] at hb ⊢
  have := card_filter_lt_lt_of_lt (s := univ) (mem_univ a) hlt
  exact ⟨this.trans hb.1, this.trans hb.2⟩

/-- The staircase minor `M_{-,p}` is `K`-highest for the rows in the order of `l'`, of the weight
of the vacuum minus one on its rows. -/
private theorem isKHighest_fockRowHom_staircaseMinor_not (hl : Injective l) (p : ℕ) :
    IsKHighest (fockRowHom K (fun _ ↦ true) ε') (fun _ ↦ true) l'
      ((fun a ↦ ((#{c | (fun _ : I ↦ true) a = ε' c} : K) -
        #{c | (fun _ : I ↦ true) a ≠ ε' c}) / 2) +
        -(Set.range fun x : staircasePairs (fun c ↦ !ε' c) (-l') (-l) p ↦ x.val.1).indicator 1)
      (staircaseMinor (fun c ↦ !ε' c) (-l') (-l) K p) := by
  have hl' : Set.InjOn (-l) {c | (!ε' c) = true} := (neg_injective.comp hl).injOn
  rw [← sub_eq_add_neg]
  refine isKHighest_fockRowHom_mvPolynomialMinor_of_not_isEvenPair
    (isKHighest_fockRowHom_one _ _ l') (fun _ y ↦ ?_) ?_
  · simpa [isEvenPair_iff] using staircasePairs_snd y
  intro a b _ hlt ha
  rw [mem_range_staircasePairs_fst hl'] at ha ⊢
  have := card_filter_lt_lt_of_lt (s := univ) (f := -l') (mem_univ b) (by simpa using hlt)
  exact ⟨this.trans ha.1, this.trans ha.2⟩

/-- **The staircase product is `K`-highest for the rows.** Let `l` be injective, and let
`k η p = 0` for `p < |I|` whenever fewer than `p` columns have the sign `η`. Then the staircase
product is `K`-highest for the row action in the order of `l'`, of weight
`ν₀ + ∑_{q₊(a) < j < |I|} k true j - ∑_{q₋(a) < j < |I|} k false j` at the row `a`, where
`ν₀ = (#{c | ε' c} - #{c | ¬ε' c}) / 2` is the weight of the vacuum and `q₊(a)`, `q₋(a)` are the
positions of `a` in the decreasing and the increasing order of `l'`. -/
theorem isKHighest_fockRowHom_staircaseProd (hl : Injective l) {k : Bool → ℕ → ℕ}
    (hk : ∀ η, ∀ p < Fintype.card I, #{c | ε' c = η} < p → k η p = 0) :
    IsKHighest (fockRowHom K (fun _ ↦ true) ε') (fun _ ↦ true) l'
      (fun a ↦ ((#{c | ε' c = true} : K) - #{c | ε' c = false}) / 2 +
        ∑ j ∈ Ioo #{b | l' a < l' b} (Fintype.card I), (k true j : K) -
        ∑ j ∈ Ioo #{b | l' b < l' a} (Fintype.card I), (k false j : K))
      (staircaseProd ε' l' l K k) := by
  have h₁ := isKHighest_fockRowHom_one (K := K) (fun _ : I ↦ true) ε' l'
  have hplus := isKHighest_fockRowHom_prod h₁ (range (Fintype.card I)) fun p _ ↦
    isKHighest_fockRowHom_pow h₁ (isKHighest_fockRowHom_staircaseMinor hl.injOn p) (k true p)
  have hminus := isKHighest_fockRowHom_prod h₁ (range (Fintype.card I)) fun p _ ↦
    isKHighest_fockRowHom_pow h₁ (isKHighest_fockRowHom_staircaseMinor_not hl p) (k false p)
  have hl' : Set.InjOn (-l) {c | (!ε' c) = true} := (neg_injective.comp hl).injOn
  rw [staircaseProd_def]
  convert isKHighest_fockRowHom_mul h₁ hplus hminus using 1
  funext a
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.neg_apply]
  simp only [nsmul_eq_mul, Set.indicator_apply, Pi.one_apply, mem_range_staircasePairs_fst hl.injOn,
    mem_range_staircasePairs_fst hl', mul_neg, sum_neg_distrib]
  rw [sum_range_mul_ite_eq_sum_Ioo fun p hp ↦ hk true p (mem_range.1 hp),
    sum_range_mul_ite_eq_sum_Ioo fun p hp hlt ↦ hk false p (mem_range.1 hp) (by simpa using hlt)]
  simp [sub_eq_add_neg, add_assoc]

/-- The transpose of the staircase minor `M_{+,p}` is `K`-highest for the rows of the exchanged
pair in the order of `l`, of the weight of the vacuum plus one on the columns of `M_{+,p}`. -/
private theorem isKHighest_rename_swap_staircaseMinor (hl' : Injective l') (p : ℕ) :
    IsKHighest (fockRowHom K ε' (fun _ : I ↦ true)) ε' l
      ((fun c ↦ ((#{a : I | ε' c = (fun _ ↦ true) a} : K) -
        #{a : I | ε' c ≠ (fun _ ↦ true) a}) / 2) +
        (Set.range fun x : staircasePairs ε' l' l p ↦ x.val.2).indicator 1)
      (rename Prod.swap (staircaseMinor ε' l' l K p)) := by
  rw [staircaseMinor_def, rename_swap_mvPolynomialMinor]
  refine isKHighest_fockRowHom_mvPolynomialMinor_of_isEvenPair (isKHighest_fockRowHom_one _ _ l)
    (fun x _ ↦ isEvenPair_iff.2 (staircasePairs_snd x)) ?_
  intro c d hcd hlt hd
  rw [mem_range_staircasePairs_snd hl'] at hd ⊢
  have hc : ε' c = true := hcd.trans hd.1
  have := card_filter_lt_lt_of_lt (s := {e | ε' e}) (f := l) (by simpa using hc) hlt
  simp only [filter_filter] at this
  exact ⟨hc, this.trans hd.2.1, this.trans hd.2.2⟩

/-- The transpose of the staircase minor `M_{-,p}` is `K`-highest for the rows of the exchanged
pair in the order of `l`, of the weight of the vacuum minus one on the columns of `M_{-,p}`. -/
private theorem isKHighest_rename_swap_staircaseMinor_not (hl' : Injective l') (p : ℕ) :
    IsKHighest (fockRowHom K ε' (fun _ : I ↦ true)) ε' l
      ((fun c ↦ ((#{a : I | ε' c = (fun _ ↦ true) a} : K) -
        #{a : I | ε' c ≠ (fun _ ↦ true) a}) / 2) +
        -(Set.range fun x : staircasePairs (fun c ↦ !ε' c) (-l') (-l) p ↦ x.val.2).indicator 1)
      (rename Prod.swap (staircaseMinor (fun c ↦ !ε' c) (-l') (-l) K p)) := by
  have hl'' : Injective (-l') := neg_injective.comp hl'
  rw [← sub_eq_add_neg, staircaseMinor_def, rename_swap_mvPolynomialMinor]
  refine isKHighest_fockRowHom_mvPolynomialMinor_of_not_isEvenPair (isKHighest_fockRowHom_one _ _ l)
    (fun x _ ↦ ?_) ?_
  · simpa [isEvenPair_iff] using staircasePairs_snd x
  intro c d hcd hlt hc
  rw [mem_range_staircasePairs_snd hl''] at hc ⊢
  have hd : (!ε' d) = true := by rw [← hcd]; exact hc.1
  have := card_filter_lt_lt_of_lt (s := {e | (!ε' e) = true}) (f := -l) (by simpa using hd)
    (by simpa using hlt)
  simp only [filter_filter] at this
  exact ⟨hd, this.trans hc.2.1, this.trans hc.2.2⟩

/-- **The staircase product is `K`-highest for the columns.** Let `l'` be injective. Then the
staircase product is `K`-highest for the column action in the order of `l`, of weight
`s_c (|I| / 2 + ∑_{o(c) < j < |I|} k (ε' c) j)` at the column `c`, where `s_c = ±1` is the sign
of `c`, `s_c |I| / 2` is the weight of the vacuum and `o(c)` is the position of `c` among the
columns of its sign in the decreasing order of `s_c · l`. -/
theorem isKHighest_fockColHom_staircaseProd (hl' : Injective l') (k : Bool → ℕ → ℕ) :
    IsKHighest (fockColHom K (fun _ ↦ true) ε') ε' l
      (fun c ↦ if ε' c then
          (Fintype.card I : K) / 2 + ∑ j ∈ Ioo #{d | ε' d ∧ l c < l d} (Fintype.card I),
            (k true j : K)
        else -((Fintype.card I : K) / 2 + ∑ j ∈ Ioo #{d | ε' d = false ∧ l d < l c}
            (Fintype.card I), (k false j : K)))
      (staircaseProd ε' l' l K k) := by
  have h₁ := isKHighest_fockRowHom_one (K := K) ε' (fun _ : I ↦ true) l
  have hplus := isKHighest_fockRowHom_prod h₁ (range (Fintype.card I)) fun p _ ↦
    isKHighest_fockRowHom_pow h₁ (isKHighest_rename_swap_staircaseMinor hl' p) (k true p)
  have hminus := isKHighest_fockRowHom_prod h₁ (range (Fintype.card I)) fun p _ ↦
    isKHighest_fockRowHom_pow h₁ (isKHighest_rename_swap_staircaseMinor_not hl' p) (k false p)
  have hl'' : Injective (-l') := neg_injective.comp hl'
  have hn (p : ℕ) (hp : p ∈ range (Fintype.card I)) (h : Fintype.card I < p) :
      k true p = 0 ∧ k false p = 0 :=
    absurd (mem_range.1 hp) (by omega)
  rw [isKHighest_fockColHom_iff, staircaseProd_def, map_mul, map_prod, map_prod]
  simp only [map_pow]
  convert isKHighest_fockRowHom_mul h₁ hplus hminus using 1
  funext c
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.neg_apply]
  simp only [nsmul_eq_mul, Set.indicator_apply, Pi.one_apply, mem_range_staircasePairs_snd hl',
    mem_range_staircasePairs_snd hl'', mul_neg, sum_neg_distrib]
  rw [sum_range_mul_ite_and_eq _ fun p hp h ↦ (hn p hp h).1,
    sum_range_mul_ite_and_eq _ fun p hp h ↦ (hn p hp h).2]
  cases ε' c
  · simp
    ring
  · simp

end Product

end TauCeti
