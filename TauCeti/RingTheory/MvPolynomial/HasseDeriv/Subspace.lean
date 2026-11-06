/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.ChainRule
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.Grid
public import TauCeti.RingTheory.MvPolynomial.MultiHomogeneous

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Rat.Floor

/-!
# Nonzero Hasse jets on bounded integer grids in linear subspaces

Let `F : MvPolynomial (ι × κ) R` be multihomogeneous of positive multidegree `d : ι → ℕ` over a
domain `R` of characteristic zero, and suppose a Hasse derivative `∂^i F` of bounded weighted order
`∑ h, (∑ l, i (h, l)) / d h < t` restricts non-identically to a product of linear subspaces
`X_{h,l} = ∑ₐ b_{h,a,l} Y_{h,a}` parameterized by `τ`. Combining three ingredients produces a
bounded integer parameter tuple `z : ι → τ → ℤ` whose block combinations `∑ₐ z_{h,a} b_{h,a}` are
all nonzero and at which some Hasse jet `∂^j F` does not vanish:

1. Because `(∂^i F)(bY)` has degree at most `d h` in each parameter `Y_{h,a}`
   (`MvPolynomial.degreeOf_aeval_blockLinearForm_le`), Evertse's rectangular integer-grid lemma
   (`MvPolynomial.exists_int_eval_hasseDeriv_ne_zero`) supplies an integer point `|y_{h,a}| ≤ B`
   and a parameter derivative order `k_{h,a} ≤ d h / B` at which `∂_Y^k ((∂_X^i F)(bY))` is
   nonzero.
2. The block-linear chain rule (`MvPolynomial.exists_eval_hasseDeriv_ne_zero_of_blockLinearForm`)
   lifts this nonzero parameter jet to a nonzero ambient jet `∂^(i + e) F` at `by` whose block
   sums satisfy `∑ₗ e (h, l) = ∑ₐ k (h, a)`, increasing the weighted order by at most
   `card ι * card τ / B` (`MvPolynomial.sum_div_add_lt_of_block_sum_eq`).
3. Since `∂^(i + e) F` remains multihomogeneous (`MvPolynomial.IsMultiHomogeneous.hasseDeriv`), any
   block where the combination `∑ₐ y_{h,a} b_{h,a}` vanishes has residual block degree zero
   (`MvPolynomial.IsWeightedHomogeneous.eq_zero_of_eval₂_ne_zero`) and can be replaced by a single
   nonzero generator `b h a₀` within the same grid bound `B ≥ 1` without changing the value of
   `∂^(i + e) F` (`MvPolynomial.IsMultiHomogeneous.exists_block_ne_zero_and_eval_eq`).

For codimension-one subspaces (`card τ + 1 = card κ`) and grid radius `B = card κ / ε`, the
resulting weighted jet order is strictly below `(2 - 1 / card κ) * card ι * ε` (Evertse, Lemma 26).

## Main results

* `MvPolynomial.sum_div_add_lt_of_block_sum_eq`,
  `MvPolynomial.sum_div_add_lt_two_sub_one_div`: weighted jet-order bounds for `i + e` when
  `∑ₗ e (h, l) = ∑ₐ k (h, a)`, in general and in codimension one.
* `MvPolynomial.IsMultiHomogeneous.exists_block_ne_zero_and_eval_eq`: replacing zero block
  combinations by unit parameter vectors preserves the value of a multihomogeneous polynomial and
  the integer coordinate bound `B ≥ 1`.
* `MvPolynomial.IsMultiHomogeneous.exists_int_eval_hasseDeriv_ne_zero_of_blockLinearForm_le`:
  nonzero Hasse jet on a bounded integer subspace grid of radius `B ≥ 1` for subspaces of arbitrary
  dimension.
* `MvPolynomial.IsMultiHomogeneous.exists_int_eval_hasseDeriv_ne_zero_of_codim_one`: Evertse's
  codimension-one subspace-grid Hasse-jet reduction at radius `card κ / ε` with weighted order
  below `(2 - 1 / card κ) * card ι * ε`.

## References

* J.-H. Evertse, *An improvement of the quantitative subspace theorem*, Compositio Math. 101
  (1996), §7, Lemma 26.
-/

public section

namespace MvPolynomial

open Finset

section WeightBound

/-- **Weighted jet-order increment after a block-linear substitution.** If `i` has weighted block
order `< t`, `e` has the block degrees `∑ₗ e (h, l) = ∑ₐ k (h, a)` of `k`, and each parameter
derivative order satisfies `k (h, a) ≤ d h / B` with `0 < d h`, then `i + e` has weighted block
order strictly less than `t + card ι * card τ / B`. -/
theorem sum_div_add_lt_of_block_sum_eq {ι κ τ S : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    [Semifield S] [LinearOrder S] [IsStrictOrderedRing S]
    {d : ι → ℕ} (hd : ∀ h, 0 < d h) {B t : S}
    {i e : ι × κ →₀ ℕ} {k : ι × τ →₀ ℕ}
    (hi : ∑ h, (∑ l, (i (h, l) : S)) / d h < t)
    (he : ∀ h, ∑ l, e (h, l) = ∑ a, k (h, a))
    (hk : ∀ h a, (k (h, a) : S) ≤ (d h : S) / B) :
    ∑ h, (∑ l, ((i + e) (h, l) : S)) / d h <
      t + (Fintype.card ι : S) * (Fintype.card τ : S) / B := by
  have hsplit : ∑ h, (∑ l, ((i + e) (h, l) : S)) / d h =
      (∑ h, (∑ l, (i (h, l) : S)) / d h) + ∑ h, (∑ l, (e (h, l) : S)) / d h := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun h _ ↦ ?_
    simp [Finsupp.add_apply, Finset.sum_add_distrib, add_div]
  have he_bound (h : ι) : (∑ l, (e (h, l) : S)) / d h ≤ (Fintype.card τ : S) / B := by
    have hdh : (0 : S) < d h := Nat.cast_pos.2 (hd h)
    have hcast : (∑ l, (e (h, l) : S)) = ∑ a, (k (h, a) : S) := by exact_mod_cast he h
    have hsum : (∑ l, (e (h, l) : S)) ≤ (Fintype.card τ : S) * ((d h : S) / B) := by
      rw [hcast]
      calc ∑ a : τ, (k (h, a) : S)
          ≤ ∑ _a : τ, (d h : S) / B := Finset.sum_le_sum fun a _ ↦ hk h a
        _ = (Fintype.card τ : S) * ((d h : S) / B) := by simp
    calc (∑ l, (e (h, l) : S)) / d h
        ≤ ((Fintype.card τ : S) * ((d h : S) / B)) / d h :=
          div_le_div_of_nonneg_right hsum hdh.le
      _ = (Fintype.card τ : S) / B :=
          (div_eq_iff hdh.ne').2 (by simp only [div_eq_mul_inv]; ac_rfl)
  have he_sum : ∑ h, (∑ l, (e (h, l) : S)) / d h ≤
      (Fintype.card ι : S) * (Fintype.card τ : S) / B := by
    calc ∑ h : ι, (∑ l, (e (h, l) : S)) / d h
        ≤ ∑ _h : ι, (Fintype.card τ : S) / B := Finset.sum_le_sum fun h _ ↦ he_bound h
      _ = (Fintype.card ι : S) * ((Fintype.card τ : S) / B) := by simp
      _ = (Fintype.card ι : S) * (Fintype.card τ : S) / B := (mul_div_assoc _ _ _).symm
  rw [hsplit]
  exact add_lt_add_of_lt_of_le hi he_sum

private theorem add_mul_div_div_eq_two_sub_one_div {ι κ τ S : Type*}
    [Fintype ι] [Fintype κ] [Fintype τ] [Field S] [LinearOrder S] [IsStrictOrderedRing S]
    (hcard : Fintype.card τ + 1 = Fintype.card κ) {ε : S} (hε : 0 < ε) :
    (Fintype.card ι : S) * ε +
      (Fintype.card ι : S) * (Fintype.card τ : S) / ((Fintype.card κ : S) / ε) =
      (2 - 1 / (Fintype.card κ : S)) * (Fintype.card ι : S) * ε := by
  have hκ0 : (Fintype.card κ : S) ≠ 0 := (Nat.cast_pos.2 (by omega)).ne'
  have hε0 : ε ≠ 0 := hε.ne'
  have hcardS : (Fintype.card τ : S) = (Fintype.card κ : S) - 1 :=
    eq_sub_of_add_eq (by exact_mod_cast hcard)
  rw [hcardS]
  field_simp
  ring

/-- **Codimension-one weighted jet-order bound** (the weight calculation in Evertse, Lemma 26).
When `card τ + 1 = card κ`, `0 < d h`, and `0 < ε`, combining
`∑ h, (∑ l, i (h, l)) / d h < card ι * ε` with `∑ l, e (h, l) = ∑ a, k (h, a)` and
`k (h, a) ≤ d h * ε / card κ` gives
`∑ h, (∑ l, (i + e) (h, l)) / d h < (2 - 1 / card κ) * card ι * ε`. -/
theorem sum_div_add_lt_two_sub_one_div {ι κ τ S : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    [Field S] [LinearOrder S] [IsStrictOrderedRing S]
    (hcard : Fintype.card τ + 1 = Fintype.card κ)
    {d : ι → ℕ} (hd : ∀ h, 0 < d h) {ε : S} (hε : 0 < ε)
    {i e : ι × κ →₀ ℕ} {k : ι × τ →₀ ℕ}
    (hi : ∑ h, (∑ l, (i (h, l) : S)) / d h < (Fintype.card ι : S) * ε)
    (he : ∀ h, ∑ l, e (h, l) = ∑ a, k (h, a))
    (hk : ∀ h a, (k (h, a) : S) ≤ (d h : S) * ε / Fintype.card κ) :
    ∑ h, (∑ l, ((i + e) (h, l) : S)) / d h <
      (2 - 1 / (Fintype.card κ : S)) * (Fintype.card ι : S) * ε := by
  have hk' (h : ι) (a : τ) : (k (h, a) : S) ≤ (d h : S) / ((Fintype.card κ : S) / ε) := by
    rw [div_div_eq_mul_div]
    exact hk h a
  exact add_mul_div_div_eq_two_sub_one_div (ι := ι) hcard hε ▸
    sum_div_add_lt_of_block_sum_eq hd hi he hk'

/-- When `d * ε / N < 1`, any natural parameter derivative order `k ≤ d * ε / N` vanishes; for
`m = 1`, `N = 2`, `d = 4`, `ε = 1 / 2`, `i = 0`, and `e = k = 1`, the weight `1 / 4` satisfies
`1 / 4 < 3 / 4 < 1`. -/
example : (∀ k : ℕ, (k : ℚ) ≤ 1 / 2 → k = 0) ∧
    ((1 : ℚ) / 4 < (2 - 1 / 2) * 1 * (1 / 2) ∧ (2 - 1 / 2) * 1 * (1 / 2 : ℚ) < 2 * 1 * (1 / 2)) :=
  ⟨fun k hk ↦ by
    have h1 : (k : ℚ) < 1 := hk.trans_lt (by norm_num)
    have h2 : k < 1 := by exact_mod_cast h1
    omega,
   by norm_num⟩

end WeightBound

section BlockReplacement

/-- **Nonzero block-representative replacement** (Evertse, Lemma 26, zero-block elimination).
Suppose `H` is multihomogeneous of multidegree `δ`, every block `h` has at least one nonzero
generator `b h a ≠ 0`, and `H` does not vanish at the block combination
`x_{h,l} = ∑ₐ z_{h,a} b_{h,a,l}` with `(z h a).natAbs ≤ B` and `1 ≤ B`. Then any block where
`x_h = 0` must have `δ h = 0` (`IsWeightedHomogeneous.eq_zero_of_eval₂_ne_zero`), so replacing
`z h` on those blocks by a unit coordinate vector produces `z'` within the same bound
`(z' h a).natAbs ≤ B` whose block combinations `∑ₐ z'_{h,a} b_{h,a}` are all nonzero and at which
`H` takes the exact same value. -/
theorem IsMultiHomogeneous.exists_block_ne_zero_and_eval_eq {R S ι κ τ : Type*}
    [CommRing R] [DecidableEq ι] [Fintype τ]
    [Semiring S] [PartialOrder S] [IsOrderedRing S]
    {δ : ι → ℕ} {H : MvPolynomial (ι × κ) R} (hH : H.IsMultiHomogeneous δ)
    {b : ι → τ → κ → R} (hb : ∀ h, ∃ a, b h a ≠ 0)
    {B : S} (hB : 1 ≤ B) {z : ι → τ → ℤ} (hz : ∀ h a, ((z h a).natAbs : S) ≤ B)
    (heval : eval (fun p : ι × κ ↦ ∑ a, (z p.1 a : R) * b p.1 a p.2) H ≠ 0) :
    ∃ z' : ι → τ → ℤ,
      (∀ h a, ((z' h a).natAbs : S) ≤ B) ∧
      (∀ h, (fun l ↦ ∑ a, (z' h a : R) * b h a l) ≠ 0) ∧
      eval (fun p : ι × κ ↦ ∑ a, (z' p.1 a : R) * b p.1 a p.2) H =
        eval (fun p : ι × κ ↦ ∑ a, (z p.1 a : R) * b p.1 a p.2) H := by
  classical
  let x : ι → κ → R := fun h l ↦ ∑ a, (z h a : R) * b h a l
  let Z : Set ι := {h | x h = 0}
  have hδ0 (h : ι) (hh : h ∈ Z) : δ h = 0 :=
    (hH.isWeightedHomogeneous h).eq_zero_of_eval₂_ne_zero (RingHom.id R) (fun l ↦ congrFun hh l)
      (by simpa only [eval₂_id] using heval)
  let z' : ι → τ → ℤ := fun h ↦ if x h = 0 then Pi.single (hb h).choose 1 else z h
  refine ⟨z', fun h a ↦ ?_, fun h ↦ ?_, ?_⟩
  · dsimp only [z']
    split_ifs with hx0
    · rcases eq_or_ne a (hb h).choose with rfl | ha
      · simpa using hB
      · simpa [Pi.single_eq_of_ne ha] using zero_le_one.trans hB
    · exact hz h a
  · dsimp only [z']
    split_ifs with hx0
    · have hsum :
          (fun l ↦ ∑ a, (((Pi.single (hb h).choose (1 : ℤ) : τ → ℤ) a : R) * b h a l)) =
            b h (hb h).choose := by
        ext l
        simp [Pi.single_apply]
      rw [hsum]
      exact (hb h).choose_spec
    · exact hx0
  · have hZ : ∀ h ∈ Z, H.IsWeightedHomogeneous (fun p : ι × κ ↦ if p.1 = h then 1 else 0) 0 :=
      fun h hh ↦ hδ0 h hh ▸ hH.isWeightedHomogeneous h
    simpa only [eval₂_id] using
      eval₂_congr_of_block_isWeightedHomogeneous_zero hZ (RingHom.id R) fun p hp ↦ by
        have hx0 : x p.1 ≠ 0 := hp
        simp [z', hx0]

/-- Replacing two zero blocks by `(1, 0)` in `H = 1` over `ℚ` preserves the value `1`, and
replacing a zero first block by `(1, 0)` while keeping `(2, 0)` in the second block preserves the
value `4` of `H = X (1, 0) ^ 2`. -/
example :
    eval (![(1 : ℚ), 0] ∘ Prod.snd) (1 : MvPolynomial (Fin 2 × Fin 2) ℚ) = 1 ∧
    eval (fun p : Fin 2 × Fin 2 ↦ if p.1 = 0 then ![1, 0] p.2 else ![2, 0] p.2)
      (X (1, 0) ^ 2 : MvPolynomial (Fin 2 × Fin 2) ℚ) =
      eval (fun p : Fin 2 × Fin 2 ↦ if p.1 = 0 then 0 else ![2, 0] p.2)
        (X (1, 0) ^ 2 : MvPolynomial (Fin 2 × Fin 2) ℚ) ∧
    eval (fun p : Fin 2 × Fin 2 ↦ if p.1 = 0 then 0 else ![2, 0] p.2)
      (X (1, 0) ^ 2 : MvPolynomial (Fin 2 × Fin 2) ℚ) = 4 := by
  refine ⟨by simp, ?_, ?_⟩ <;> norm_num

end BlockReplacement

section SubspaceGrid

/-- **Subspace-grid Hasse-jet nonvanishing at an arbitrary radius `B ≥ 1`.** Over a domain of
characteristic zero, let `F : MvPolynomial (ι × κ) R` be multihomogeneous of positive multidegree
`d`, let each block `h` have generators `b h : τ → κ → R` not all zero, and let `1 ≤ B`. If
`∂^i F` has weighted block order `< t` and its restriction along `blockLinearForm` to the subspace
family `X_{h,l} = ∑ₐ b_{h,a,l} Y_{h,a}` is nonzero, then there exist integer parameters
`z : ι → τ → ℤ` bounded by `B` with all block vectors `∑ₐ z_{h,a} b_{h,a}` nonzero and a jet order
`j` of weighted block order `< t + card ι * card τ / B` such that `(∂^j F)(bz) ≠ 0`. -/
theorem IsMultiHomogeneous.exists_int_eval_hasseDeriv_ne_zero_of_blockLinearForm_le
    {R S ι κ τ : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq ι]
    [Semifield S] [LinearOrder S] [IsStrictOrderedRing S] [FloorSemiring S]
    {d : ι → ℕ} (hd : ∀ h, 0 < d h)
    {F : MvPolynomial (ι × κ) R} (hF : F.IsMultiHomogeneous d)
    {b : ι → τ → κ → R} (hb : ∀ h, ∃ a, b h a ≠ 0)
    {B t : S} (hB : 1 ≤ B)
    {i : ι × κ →₀ ℕ} (hi : ∑ h, (∑ l, (i (h, l) : S)) / d h < t)
    (hn : aeval (blockLinearForm (fun h l a ↦ b h a l)) (MvPolynomial.hasseDeriv i F) ≠ 0) :
    ∃ (z : ι → τ → ℤ) (j : ι × κ →₀ ℕ),
      (∀ h a, ((z h a).natAbs : S) ≤ B) ∧
      (∀ h, (fun l ↦ ∑ a, (z h a : R) * b h a l) ≠ 0) ∧
      ∑ h, (∑ l, (j (h, l) : S)) / d h <
        t + (Fintype.card ι : S) * (Fintype.card τ : S) / B ∧
      eval (fun p : ι × κ ↦ ∑ a, (z p.1 a : R) * b p.1 a p.2)
        (MvPolynomial.hasseDeriv j F) ≠ 0 := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  let A : ι → κ → τ → R := fun h l a ↦ b h a l
  have hdegG (q : ι × τ) :
      (aeval (blockLinearForm A) (MvPolynomial.hasseDeriv i F)).degreeOf q ≤ d q.1 := by
    refine degreeOf_aeval_blockLinearForm_le A (fun μ hμ h ↦ ?_) q
    exact (isMultiHomogeneous_iff.1 (hF.hasseDeriv i) μ (mem_support_iff.1 hμ) h).trans_le
      (Nat.sub_le _ _)
  -- Step 1: pick a nonzero jet of the restricted polynomial on the integer box `[-B, B]`.
  obtain ⟨y, k, hy, hk, hneG⟩ :=
    exists_int_eval_hasseDeriv_ne_zero hn hdegG (fun _ : ι × τ ↦ hB0)
  -- Step 2: lift the parameter jet `k` to an ambient jet `i + e` with matching block sums.
  obtain ⟨e, he, hneF⟩ :=
    exists_eval_hasseDeriv_ne_zero_of_blockLinearForm A F i k (fun q ↦ (y q : R)) hneG
  have hneF' : eval (fun p : ι × κ ↦ ∑ a, (y (p.1, a) : R) * b p.1 a p.2)
      (MvPolynomial.hasseDeriv (i + e) F) ≠ 0 := by
    simpa only [A, mul_comm] using hneF
  have hj := sum_div_add_lt_of_block_sum_eq hd hi he (fun h a ↦ hk (h, a))
  -- Step 3: replace any zero block combinations by nonzero basis vectors without changing the jet.
  obtain ⟨z', hz', hbz', heq⟩ :=
    (hF.hasseDeriv (i + e)).exists_block_ne_zero_and_eval_eq hb hB (fun h a ↦ hy (h, a)) hneF'
  exact ⟨z', i + e, hz', hbz', hj, heq.symm ▸ hneF'⟩

/-- **Subspace-grid Hasse-jet nonvanishing for codimension-one subspaces** (Evertse, Lemma 26).
Over a domain `R` of characteristic zero, suppose `F : MvPolynomial (ι × κ) R` is multihomogeneous
of positive multidegree `d`, each block `h` has generators `b h : τ → κ → R` not all zero with
`card τ + 1 = card κ`, and `0 < ε ≤ card κ`. If `∂^i F` has weighted block order `< card ι * ε`
and its restriction along `blockLinearForm` is nonzero, then there exist `z : ι → τ → ℤ` bounded by
`card κ / ε` with every block vector `∑ₐ z_{h,a} b_{h,a}` nonzero and a jet order `j` of weighted
block order `< (2 - 1 / card κ) * card ι * ε` such that `(∂^j F)(bz) ≠ 0`. -/
theorem IsMultiHomogeneous.exists_int_eval_hasseDeriv_ne_zero_of_codim_one
    {R S ι κ τ : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq ι]
    [Field S] [LinearOrder S] [IsStrictOrderedRing S] [FloorSemiring S]
    (hcard : Fintype.card τ + 1 = Fintype.card κ)
    {d : ι → ℕ} (hd : ∀ h, 0 < d h) {ε : S} (hε : 0 < ε) (hεN : ε ≤ Fintype.card κ)
    {F : MvPolynomial (ι × κ) R} (hF : F.IsMultiHomogeneous d)
    {b : ι → τ → κ → R} (hb : ∀ h, ∃ a, b h a ≠ 0)
    {i : ι × κ →₀ ℕ} (hi : ∑ h, (∑ l, (i (h, l) : S)) / d h < (Fintype.card ι : S) * ε)
    (hn : aeval (blockLinearForm (fun h l a ↦ b h a l)) (MvPolynomial.hasseDeriv i F) ≠ 0) :
    ∃ (z : ι → τ → ℤ) (j : ι × κ →₀ ℕ),
      (∀ h a, ((z h a).natAbs : S) ≤ (Fintype.card κ : S) / ε) ∧
      (∀ h, (fun l ↦ ∑ a, (z h a : R) * b h a l) ≠ 0) ∧
      ∑ h, (∑ l, (j (h, l) : S)) / d h <
        (2 - 1 / (Fintype.card κ : S)) * (Fintype.card ι : S) * ε ∧
      eval (fun p : ι × κ ↦ ∑ a, (z p.1 a : R) * b p.1 a p.2)
        (MvPolynomial.hasseDeriv j F) ≠ 0 := by
  have hB : (1 : S) ≤ (Fintype.card κ : S) / ε := (one_le_div hε).2 hεN
  obtain ⟨z, j, hz, hbz, hj, hne⟩ :=
    hF.exists_int_eval_hasseDeriv_ne_zero_of_blockLinearForm_le hd hb hB hi hn
  exact ⟨z, j, hz, hbz, add_mul_div_div_eq_two_sub_one_div (ι := ι) hcard hε ▸ hj, hne⟩

/-- On `Fin 1 × Fin 2` with `d = ![2]`, `ε = 1 : ℝ`, `F = X (0, 0) ^ 2`, and the hyperplane basis
`b 0 0 = ![1, 0]`, `exists_int_eval_hasseDeriv_ne_zero_of_codim_one` applies directly; for the
concrete witness `z = 1` and `j = 0`, the jet evaluates to `1` with weight `0 < 3 / 2`. -/
example :
    (∃ (z : Fin 1 → Fin (2 - 1) → ℤ) (j : Fin 1 × Fin 2 →₀ ℕ),
      (∀ h a, ((z h a).natAbs : ℝ) ≤ (2 : ℝ) / 1) ∧
      (∀ h, (fun l ↦ ∑ a, (z h a : ℚ) * (![![![(1 : ℚ), 0]]] h a l)) ≠ 0) ∧
      ∑ h : Fin 1, (∑ l : Fin 2, (j (h, l) : ℝ)) / (![2] h) <
        (2 - 1 / (2 : ℝ)) * (1 : ℝ) * 1 ∧
      eval (fun p : Fin 1 × Fin 2 ↦ ∑ a : Fin (2 - 1),
          (z p.1 a : ℚ) * (![![![(1 : ℚ), 0]]] p.1 a p.2))
        (hasseDeriv j (X (0, 0) ^ 2 : MvPolynomial (Fin 1 × Fin 2) ℚ)) ≠ 0) ∧
    eval (fun p : Fin 1 × Fin 2 ↦ (![1, 0] : Fin 2 → ℚ) p.2)
      (hasseDeriv 0 (X (0, 0) ^ 2 : MvPolynomial (Fin 1 × Fin 2) ℚ)) = 1 := by
  refine ⟨?_, by simp⟩
  have hF : IsMultiHomogeneous (![2] : Fin 1 → ℕ)
      (X (0, 0) ^ 2 : MvPolynomial (Fin 1 × Fin 2) ℚ) := by
    convert (isMultiHomogeneous_X (R := ℚ) (0 : Fin 1) (0 : Fin 2)).pow 2
    ext h
    fin_cases h
    simp
  have hb : ∀ h : Fin 1, ∃ a : Fin (2 - 1), ![![![(1 : ℚ), 0]]] h a ≠ 0 :=
    fun h ↦ ⟨0, fun h0 ↦ by fin_cases h; have := congrFun h0 0; norm_num at this⟩
  have hn : aeval (blockLinearForm fun (h : Fin 1) (l : Fin 2) (a : Fin (2 - 1)) ↦
      ![![![(1 : ℚ), 0]]] h a l)
      (hasseDeriv 0 (X (0, 0) ^ 2 : MvPolynomial (Fin 1 × Fin 2) ℚ)) ≠ 0 := by
    intro h0
    have hev := congrArg (eval fun _ ↦ (1 : ℚ)) h0
    simp at hev
  simpa using hF.exists_int_eval_hasseDeriv_ne_zero_of_codim_one
    (ε := (1 : ℝ)) (i := 0) (by simp) (fun h ↦ by fin_cases h; norm_num)
    (by norm_num) (by norm_num) hb (by norm_num) hn

/-- Ambient nonvanishing `F ≠ 0` cannot replace the nonzero-restriction hypothesis `hn`: on
`Fin 1 × Fin 2`, `F = X (0, 1)` is nonzero and multihomogeneous of degree `1`, yet its restriction
to the subspace `Y ↦ (Y, 0)` vanishes identically and every order-zero evaluation along that
subspace is `0`. -/
example :
    (X (0, 1) : MvPolynomial (Fin 1 × Fin 2) ℚ) ≠ 0 ∧
    aeval (blockLinearForm fun (_ : Fin 1) (l : Fin 2) (_ : Fin 1) ↦ (![(1 : ℚ), 0] l))
      (X (0, 1) : MvPolynomial (Fin 1 × Fin 2) ℚ) = 0 := by
  refine ⟨X_ne_zero _, ?_⟩
  simp [blockLinearForm_apply]

end SubspaceGrid

end MvPolynomial
