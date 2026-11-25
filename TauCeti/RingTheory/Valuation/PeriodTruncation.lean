/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.RingTheory.DeltaRing.Basic
public import TauCeti.RingTheory.Valuation.Basic

/-!
# Fontaine's filtered truncation of a valuation ring

Let `E` be a field with a valuation `v`, let `p` be a prime with `0 < v p < 1` (so `E` has
characteristic zero and residue characteristic `p`), and let `r` be a natural number with
`r < p - 1`. When `v` has rank one, write `v₀` for the additive valuation normalised by
`v₀ p = 1`. Fontaine truncates
the ring of integers `𝒪 = v.integer` at the **period ideal**
`𝔟 = {x | v₀ x > r / (p - 1)}`, and equips the quotient `A = 𝒪 ⧸ 𝔟` with the filtration
`Filⁱ A`, the image of `{x | v₀ x ≥ i / p}`, and the **divided Frobenius maps**
`φᵢ : Filⁱ A → A`, `φᵢ [x] = [x ^ p / (-p) ^ i]`. These make `A` a filtered Frobenius module:
`φᵢ` is additive and `p`-semilinear, it vanishes on `Filⁱ⁺¹ A`, `Fil⁰ A = A` and `Filⁱ A = 0` for
`i > r`. Every valuation-compatible field map `E → E'` induces a map of truncations respecting
the filtrations and the divided Frobenius maps.

For an algebraic extension `E` of `K = Frac W(k)`, with `k` perfect of characteristic `p`, the
truncation `A(E)` is the target of Fontaine's period solutions: morphisms of Fontaine–Laffaille
modules killed by `p` into `A(E)` compute the torsion crystalline representation attached to such
a module, and counting them bounds the ramification of its splitting field.

All conditions are stated multiplicatively, so no normalisation of `v` is needed:
`v₀ x > r / (p - 1)` reads `v x ^ (p - 1) < v p ^ r`, and `v₀ x ≥ i / p` reads
`v x ^ p ≤ v p ^ i`. The ideals are defined as spans of these sets, so that the definitions need
no hypothesis; their membership lemmas hold once `p` is prime and `(p : E) ≠ 0`.

## Main definitions

* `Valuation.periodIdeal v p r`: the period ideal `𝔟 = {x | v x ^ (p - 1) < v p ^ r}` of
  `v.integer`.
* `Valuation.PeriodTruncation v p r`: the truncated ring `A = v.integer ⧸ 𝔟`.
* `Valuation.periodFiltrationIdeal v p i`: the ideal `{x | v x ^ p ≤ v p ^ i}` of `v.integer`.
* `Valuation.periodFiltration v p r i`: its image `Filⁱ A` in the truncation.
* `Valuation.periodFrobenius v p r i`: the divided Frobenius `φᵢ : Filⁱ A → A`, bundled as an
  additive map by `Valuation.periodFrobeniusAddHom`.
* `Valuation.PeriodTruncation.map`: the ring map of truncations induced by a field map `E → E'`
  along which the two valuations are equivalent.

## Main results

* `Valuation.mem_periodIdeal`, `Valuation.periodTruncation_mk_eq_mk_iff`: two integral
  representatives have the same class exactly when their difference `d` satisfies
  `v d ^ (p - 1) < v p ^ r`.
* `Valuation.natCast_mem_periodIdeal`, `Valuation.charP_periodTruncation`: `p ∈ 𝔟`, so the
  truncation factors through `𝒪 ⧸ p` and has characteristic `p`.
* `Valuation.mem_periodFiltration`, `Valuation.periodFiltration_zero`,
  `Valuation.periodFiltration_antitone`, `Valuation.periodFiltration_eq_bot`: `Filⁱ A` is the
  image of `{x | v x ^ p ≤ v p ^ i}`, it is decreasing, `Fil⁰ A = A` and `Filⁱ A = 0` for `r < i`.
* `Valuation.periodFrobenius_eq_mk`: on a representative `x` of valuation condition `i` and an
  element `y` with `(-p) ^ i * y = x ^ p`, the divided Frobenius is `φᵢ [x] = [y]`.
* `Valuation.periodFrobenius_add`, `Valuation.periodFrobenius_smul`: `φᵢ` is additive and
  `p`-semilinear over `A`; `Valuation.periodFrobenius_smul_of_isFrobeniusLift` is its
  `σ`-semilinearity over a ring with a Frobenius lift `σ`, such as `W(k)`.
* `Valuation.periodFrobenius_eq_zero_of_mem_succ`: `φᵢ` vanishes on `Filⁱ⁺¹ A`, the relation
  `φᵢ = p φᵢ₊₁` of a filtered Frobenius module in a ring killed by `p`.
* `Valuation.PeriodTruncation.map_id`, `Valuation.PeriodTruncation.map_comp`,
  `Valuation.PeriodTruncation.periodFiltration_le_comap_map`,
  `Valuation.PeriodTruncation.map_periodFrobenius`: the induced maps are functorial and respect
  the filtrations and the divided Frobenius maps.

## References

* J.-M. Fontaine, *Schémas propres et lisses sur Z*, Proceedings of the Indo-French Conference on
  Geometry (Bombay, 1989), Hindustan Book Agency (1993), 43–56; §3.2.
-/

public section

namespace Valuation

variable {E Γ₀ : Type*} [Field E] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation E Γ₀)
  (p r : ℕ)

/-- The **period ideal** `𝔟 = {x | v x ^ (p - 1) < v p ^ r}` of the integers of `v`: for the
additive valuation `v₀` normalised by `v₀ p = 1` it is `{x | v₀ x > r / (p - 1)}`. It is defined
as the ideal spanned by that set, which is the set itself once `p` is prime and `(p : E) ≠ 0`
(`Valuation.mem_periodIdeal`). -/
def periodIdeal : Ideal v.integer :=
  Ideal.span {x | v (x : E) ^ (p - 1) < v (p : E) ^ r}

/-- **Fontaine's truncated valuation ring** `A = 𝒪 ⧸ 𝔟`: the integers of `v` modulo the period
ideal `Valuation.periodIdeal v p r`. -/
abbrev PeriodTruncation : Type _ :=
  v.integer ⧸ v.periodIdeal p r

/-- The ideal `{x | v x ^ p ≤ v p ^ i}` of the integers of `v`: for the additive valuation `v₀`
normalised by `v₀ p = 1` it is `{x | v₀ x ≥ i / p}`. It is defined as the ideal spanned by that
set, which is the set itself once `p` is prime (`Valuation.mem_periodFiltrationIdeal`). -/
def periodFiltrationIdeal (i : ℕ) : Ideal v.integer :=
  Ideal.span {x | v (x : E) ^ p ≤ v (p : E) ^ i}

/-- The filtration `Filⁱ A` of the truncated ring `A = Valuation.PeriodTruncation v p r`: the
image of `Valuation.periodFiltrationIdeal v p i`. -/
def periodFiltration (i : ℕ) : Ideal (v.PeriodTruncation p r) :=
  (v.periodFiltrationIdeal p i).map (Ideal.Quotient.mk _)

variable {v p r}

/-! ### Valuation estimates -/

private lemma valuation_mul_pow_le (a x : v.integer) (n : ℕ) :
    v ((a * x : v.integer) : E) ^ n ≤ v (x : E) ^ n := by
  rw [Subring.coe_mul, map_mul]
  exact pow_le_pow_left₀ zero_le (mul_le_of_le_one_left zero_le a.property) n

private lemma natCast_ne_zero (hp0 : (p : E) ≠ 0) : (p : v.integer) ≠ 0 :=
  fun h => hp0 (by simpa using congrArg (fun x : v.integer => (x : E)) h)

private lemma valuation_natCast_pos (hp0 : (p : E) ≠ 0) : 0 < v (p : E) :=
  pos_iff_ne_zero.2 ((v.ne_zero_iff).2 hp0)

/-! ### The period ideal and the truncation -/

/-- Membership in the period ideal is the valuation condition `v x ^ (p - 1) < v p ^ r`, that is
`v₀ x > r / (p - 1)` for the additive valuation normalised by `v₀ p = 1`. -/
theorem mem_periodIdeal [hp : Fact p.Prime] (hp0 : (p : E) ≠ 0) {x : v.integer} :
    x ∈ v.periodIdeal p r ↔ v (x : E) ^ (p - 1) < v (p : E) ^ r := by
  refine ⟨fun hx => ?_, fun hx => Ideal.subset_span hx⟩
  induction hx using Submodule.span_induction with
  | mem _ hx => exact hx
  | zero =>
    rw [ZeroMemClass.coe_zero, map_zero, zero_pow (by have := hp.out.two_le; omega)]
    exact pow_pos (valuation_natCast_pos hp0) r
  | add x y _ _ hx hy =>
    exact (v.map_add_pow_le_max _ _ _).trans_lt (max_lt hx hy)
  | smul a x _ hx => exact (valuation_mul_pow_le a x _).trans_lt hx

/-- Two integral representatives have the same class in the truncation exactly when their
difference `d` satisfies `v d ^ (p - 1) < v p ^ r`, that is `v₀ d > r / (p - 1)`. -/
theorem periodTruncation_mk_eq_mk_iff [Fact p.Prime] (hp0 : (p : E) ≠ 0) {x y : v.integer} :
    Ideal.Quotient.mk (v.periodIdeal p r) x = Ideal.Quotient.mk _ y ↔
      v ((x : E) - y) ^ (p - 1) < v (p : E) ^ r := by
  rw [Ideal.Quotient.eq, mem_periodIdeal hp0, AddSubgroupClass.coe_sub]

/-- The period ideal contains `p` when `v p < 1` and `r < p - 1`. -/
theorem natCast_mem_periodIdeal (hp0 : (p : E) ≠ 0) (hp1 : v (p : E) < 1)
    (hr : r + 1 < p) : (p : v.integer) ∈ v.periodIdeal p r :=
  Ideal.subset_span (by
    simpa using pow_lt_pow_right_of_lt_one₀ (valuation_natCast_pos hp0) hp1 (by omega))

/-- The period ideal is proper: `1` has valuation `1`, which is not below `v p ^ r ≤ 1`. -/
theorem periodIdeal_ne_top [Fact p.Prime] (hp0 : (p : E) ≠ 0) : v.periodIdeal p r ≠ ⊤ := by
  rw [Ne, Ideal.eq_top_iff_one, mem_periodIdeal hp0]
  simpa using pow_le_one₀ zero_le (v.map_natCast_le_one p)

/-- The truncated ring has characteristic `p`. -/
theorem charP_periodTruncation [hp : Fact p.Prime] (hp0 : (p : E) ≠ 0) (hp1 : v (p : E) < 1)
    (hr : r + 1 < p) : CharP (v.PeriodTruncation p r) p := by
  have := Ideal.Quotient.nontrivial_iff.2 (periodIdeal_ne_top (v := v) (r := r) hp0)
  rw [CharP.charP_iff_prime_eq_zero hp.out, ← map_natCast (Ideal.Quotient.mk (v.periodIdeal p r)),
    Ideal.Quotient.eq_zero_iff_mem]
  exact natCast_mem_periodIdeal hp0 hp1 hr

/-! ### The filtration -/

/-- Membership in `Valuation.periodFiltrationIdeal v p i` is the valuation condition
`v x ^ p ≤ v p ^ i`, that is `v₀ x ≥ i / p` for the additive valuation normalised by
`v₀ p = 1`. -/
theorem mem_periodFiltrationIdeal [hp : Fact p.Prime] {i : ℕ} {x : v.integer} :
    x ∈ v.periodFiltrationIdeal p i ↔ v (x : E) ^ p ≤ v (p : E) ^ i := by
  refine ⟨fun hx => ?_, fun hx => Ideal.subset_span hx⟩
  induction hx using Submodule.span_induction with
  | mem _ hx => exact hx
  | zero => simp [zero_pow hp.out.ne_zero]
  | add x y _ _ hx hy => exact (v.map_add_pow_le_max _ _ _).trans (max_le hx hy)
  | smul a x _ hx => exact (valuation_mul_pow_le a x _).trans hx

/-- An element of the truncation lies in `Filⁱ A` exactly when it is the class of an integer `x`
with `v x ^ p ≤ v p ^ i`. -/
theorem mem_periodFiltration [Fact p.Prime] {i : ℕ} {a : v.PeriodTruncation p r} :
    a ∈ v.periodFiltration p r i ↔
      ∃ x : v.integer, v (x : E) ^ p ≤ v (p : E) ^ i ∧ Ideal.Quotient.mk _ x = a := by
  simp [periodFiltration, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective,
    mem_periodFiltrationIdeal]

/-- `Fil⁰ A = A`. -/
@[simp]
theorem periodFiltration_zero : v.periodFiltration p r 0 = ⊤ := by
  rw [periodFiltration, periodFiltrationIdeal, (Ideal.eq_top_iff_one _).2
    (Ideal.subset_span (by simp)), Ideal.map_top]

/-- The ideals `{x | v x ^ p ≤ v p ^ i}` decrease in `i`. -/
theorem periodFiltrationIdeal_antitone : Antitone (v.periodFiltrationIdeal p) := fun _ _ hij =>
  Ideal.span_mono fun _ hx =>
    Set.mem_ofPred.2 (hx.trans (pow_le_pow_right_of_le_one' (v.map_natCast_le_one p) hij))

/-- The filtration `Filⁱ A` is decreasing in `i`. -/
theorem periodFiltration_antitone : Antitone (v.periodFiltration p r) := fun _ _ hij =>
  Ideal.map_mono (periodFiltrationIdeal_antitone hij)

/-- The period ideal lies in `{x | v x ^ p ≤ v p ^ i}` for `i ≤ r`, as `r / (p - 1) ≥ i / p`. -/
theorem periodIdeal_le_periodFiltrationIdeal [hp : Fact p.Prime] {i : ℕ} (hi : i ≤ r) :
    v.periodIdeal p r ≤ v.periodFiltrationIdeal p i := by
  refine Ideal.span_le.2 fun x (hx : _ < _) => mem_periodFiltrationIdeal.2 ?_
  by_contra! h
  -- Raising `v p ^ i < v x ^ p` to the power `p - 1` and `v x ^ (p - 1) < v p ^ r` to the power
  -- `p` gives `v p ^ (i * (p - 1)) < v p ^ (r * p)`, against `i * (p - 1) ≤ r * p`.
  have h₁ := pow_lt_pow_left₀ h zero_le (n := p - 1) (by have := hp.out.two_le; omega)
  have h₂ := pow_lt_pow_left₀ hx zero_le hp.out.ne_zero
  rw [← pow_mul, ← pow_mul, mul_comm p] at h₁
  rw [← pow_mul, ← pow_mul] at h₂
  exact (h₁.trans h₂).not_ge (pow_le_pow_right_of_le_one' (v.map_natCast_le_one p)
    (by nlinarith [Nat.sub_le p 1]))

/-- The ideal `{x | v x ^ p ≤ v p ^ i}` lies in the period ideal for `r < i`, as
`i / p > r / (p - 1)` when `r < p - 1`. -/
theorem periodFiltrationIdeal_le_periodIdeal [hp : Fact p.Prime] (hp0 : (p : E) ≠ 0)
    (hp1 : v (p : E) < 1) (hr : r + 1 < p) {i : ℕ} (hi : r < i) :
    v.periodFiltrationIdeal p i ≤ v.periodIdeal p r := by
  intro x hx
  rw [mem_periodFiltrationIdeal] at hx
  rw [mem_periodIdeal hp0]
  by_contra! h
  -- Raising `v p ^ r ≤ v x ^ (p - 1)` to the power `p` and `v x ^ p ≤ v p ^ i` to the power
  -- `p - 1` gives `v p ^ (r * p) ≤ v p ^ (i * (p - 1))`, against `r * p < i * (p - 1)`.
  have h₁ := pow_le_pow_left₀ zero_le h p
  have h₂ := pow_le_pow_left₀ zero_le hx (p - 1)
  rw [← pow_mul, ← pow_mul, mul_comm (p - 1)] at h₁
  rw [← pow_mul, ← pow_mul] at h₂
  exact (h₁.trans h₂).not_gt (pow_lt_pow_right_of_lt_one₀ (valuation_natCast_pos hp0) hp1
    (by zify [hp.out.one_le] at hr hi ⊢; nlinarith))

/-- `Filⁱ A = 0` for `r < i`. -/
theorem periodFiltration_eq_bot [Fact p.Prime] (hp0 : (p : E) ≠ 0) (hp1 : v (p : E) < 1)
    (hr : r + 1 < p) {i : ℕ} (hi : r < i) : v.periodFiltration p r i = ⊥ := by
  rw [periodFiltration, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact periodFiltrationIdeal_le_periodIdeal hp0 hp1 hr hi

/-! ### The divided Frobenius -/

private lemma dvd_of_mem_periodFiltrationIdeal [hp : Fact p.Prime] {i k : ℕ} (hk : k ≤ p)
    {x y : v.integer} (hx : x ∈ v.periodFiltrationIdeal p i)
    (hy : y ∈ v.periodFiltrationIdeal p i) :
    (-(p : v.integer)) ^ i ∣ x ^ k * y ^ (p - k) := by
  rw [mem_periodFiltrationIdeal] at hx hy
  -- The `p`-th power of the bound follows from `v x ^ p ≤ v p ^ i` and `v y ^ p ≤ v p ^ i`.
  have key : (v (x : E) ^ k * v (y : E) ^ (p - k)) ^ p ≤ (v (p : E) ^ i) ^ p :=
    calc (v (x : E) ^ k * v (y : E) ^ (p - k)) ^ p
        = (v (x : E) ^ p) ^ k * (v (y : E) ^ p) ^ (p - k) := by
          rw [mul_pow, pow_right_comm _ k, pow_right_comm _ (p - k)]
      _ ≤ (v (p : E) ^ i) ^ k * (v (p : E) ^ i) ^ (p - k) :=
          mul_le_mul' (pow_le_pow_left₀ zero_le hx k) (pow_le_pow_left₀ zero_le hy _)
      _ = (v (p : E) ^ i) ^ p := by rw [← pow_add, Nat.add_sub_cancel' hk]
  refine (integer.integers v).dvd_of_le ?_
  simpa [Algebra.algebraMap_ofSubsemiring_apply] using
    (pow_le_pow_iff_left₀ zero_le zero_le hp.out.ne_zero).1 key

open Classical in
variable (p) in
/-- A chosen `y` with `(-p) ^ i * y = x ^ p`, when one exists. -/
private noncomputable def frobLift (i : ℕ) (x : v.integer) : v.integer :=
  if h : (-(p : v.integer)) ^ i ∣ x ^ p then h.choose else 0

private lemma frobLift_spec [Fact p.Prime] {i : ℕ} {x : v.integer}
    (hx : x ∈ v.periodFiltrationIdeal p i) : (-(p : v.integer)) ^ i * frobLift p i x = x ^ p := by
  have h : (-(p : v.integer)) ^ i ∣ x ^ p := by
    simpa using dvd_of_mem_periodFiltrationIdeal le_rfl hx hx
  simp only [frobLift, h, ↓reduceDIte, ← h.choose_spec]

private lemma frobLift_eq [Fact p.Prime] (hp0 : (p : E) ≠ 0) {i : ℕ} {x y : v.integer}
    (hx : x ∈ v.periodFiltrationIdeal p i) (hy : (-(p : v.integer)) ^ i * y = x ^ p) :
    frobLift p i x = y :=
  mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.2 (natCast_ne_zero hp0)))
    ((frobLift_spec hx).trans hy.symm)

/-- The divided Frobenius is additive modulo `p`: the cross terms of `(x + y) ^ p` are divisible
by `p * (-p) ^ i`. -/
private lemma frobLift_add_sub_mem [Fact p.Prime] (hp0 : (p : E) ≠ 0) (hp1 : v (p : E) < 1)
    (hr : r + 1 < p) {i : ℕ} {x y : v.integer} (hx : x ∈ v.periodFiltrationIdeal p i)
    (hy : y ∈ v.periodFiltrationIdeal p i) :
    frobLift p i (x + y) - frobLift p i x - frobLift p i y ∈ v.periodIdeal p r := by
  obtain ⟨s, hs⟩ : (-(p : v.integer)) ^ i ∣
      ∑ k ∈ Finset.Ioo 0 p, x ^ k * y ^ (p - k) * ((p.choose k / p : ℕ) : v.integer) :=
    Finset.dvd_sum fun k hk => (dvd_of_mem_periodFiltrationIdeal
      (Finset.mem_Ioo.1 hk).2.le hx hy).mul_right _
  have key : (-(p : v.integer)) ^ i *
      (frobLift p i (x + y) - frobLift p i x - frobLift p i y) =
        (-(p : v.integer)) ^ i * (p * s) := by
    rw [mul_sub, mul_sub, frobLift_spec (add_mem hx hy), frobLift_spec hx, frobLift_spec hy,
      add_pow_prime_eq' (Fact.out : p.Prime), hs]
    ring
  rw [mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.2 (natCast_ne_zero hp0))) key]
  exact Ideal.mul_mem_right _ _ (natCast_mem_periodIdeal hp0 hp1 hr)

/-- Changing the representative by an element of the period ideal changes `x ^ p / (-p) ^ i` by
an element of the period ideal, for `i ≤ r`. -/
private lemma frobLift_mem_periodIdeal [hp : Fact p.Prime] (hp0 : (p : E) ≠ 0) {i : ℕ}
    (hi : i ≤ r) {d : v.integer} (hd : d ∈ v.periodIdeal p r) :
    frobLift p i d ∈ v.periodIdeal p r := by
  have hdi := periodIdeal_le_periodFiltrationIdeal hi hd
  rw [mem_periodIdeal hp0] at hd ⊢
  have hval : v (p : E) ^ i * v (frobLift p i d : E) = v (d : E) ^ p := by
    simpa using congrArg (fun z : v.integer => v (z : E)) (frobLift_spec hdi)
  have hpos : 0 < (v (p : E) ^ i) ^ (p - 1) := pow_pos (pow_pos (valuation_natCast_pos hp0) i) _
  -- Multiply the goal by `(v p ^ i) ^ (p - 1)`: the left side becomes `(v d ^ (p - 1)) ^ p`.
  refine (mul_lt_mul_iff_of_pos_left hpos).1 ?_
  calc (v (p : E) ^ i) ^ (p - 1) * v (frobLift p i d : E) ^ (p - 1)
      = (v (d : E) ^ (p - 1)) ^ p := by rw [← mul_pow, hval, ← pow_mul, ← pow_mul, mul_comm]
    _ < (v (p : E) ^ r) ^ p := pow_lt_pow_left₀ hd zero_le hp.out.ne_zero
    _ = v (p : E) ^ r * v (p : E) ^ (r * (p - 1)) := by
        rw [← pow_mul, ← pow_add]; congr 1; have := hp.out.one_le; zify [this]; ring
    _ ≤ v (p : E) ^ r * (v (p : E) ^ i) ^ (p - 1) := by
        rw [← pow_mul]
        exact mul_le_mul_right (pow_le_pow_right_of_le_one' (v.map_natCast_le_one p)
          (Nat.mul_le_mul_right _ hi)) _
    _ = (v (p : E) ^ i) ^ (p - 1) * v (p : E) ^ r := mul_comm _ _

/-- The class of `x ^ p / (-p) ^ i` depends only on the class of `x`, for `i ≤ r`. -/
private lemma frobLift_sub_mem [Fact p.Prime] (hp0 : (p : E) ≠ 0) (hp1 : v (p : E) < 1)
    (hr : r + 1 < p) {i : ℕ} (hi : i ≤ r) {x x' : v.integer}
    (hx : x ∈ v.periodFiltrationIdeal p i) (hx' : x' ∈ v.periodFiltrationIdeal p i)
    (hxx' : x - x' ∈ v.periodIdeal p r) : frobLift p i x - frobLift p i x' ∈ v.periodIdeal p r := by
  have hd : x - x' ∈ v.periodFiltrationIdeal p i := sub_mem hx hx'
  have h := add_mem (frobLift_add_sub_mem hp0 hp1 hr hx' hd) (frobLift_mem_periodIdeal hp0 hi hxx')
  rwa [add_sub_cancel, sub_add_cancel] at h

private lemma exists_mk_eq {i : ℕ} (a : v.periodFiltration p r i) :
    ∃ x ∈ v.periodFiltrationIdeal p i, Ideal.Quotient.mk _ x = (a : v.PeriodTruncation p r) :=
  (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 a.property

variable (v p r) in
/-- **The divided Frobenius** `φᵢ : Filⁱ A → A` of the truncation, `φᵢ [x] = [x ^ p / (-p) ^ i]`
for a representative `x` with `v x ^ p ≤ v p ^ i`, and `φᵢ = 0` for `r < i`, where
`Filⁱ A = 0`. It is well defined once `p` is prime, `0 < v p < 1` and `r < p - 1`
(`Valuation.periodFrobenius_eq_mk`); the sign `(-p) ^ i` is Fontaine's normalisation. -/
noncomputable def periodFrobenius (i : ℕ) (a : v.periodFiltration p r i) :
    v.PeriodTruncation p r :=
  if i ≤ r then Ideal.Quotient.mk _ (frobLift p i (exists_mk_eq a).choose) else 0

/-- The divided Frobenius on a representative: if `v x ^ p ≤ v p ^ i` and
`(-p) ^ i * y = x ^ p`, then `φᵢ [x] = [y]`, for `i ≤ r`. -/
theorem periodFrobenius_eq_mk [Fact p.Prime] (hp0 : (p : E) ≠ 0) (hp1 : v (p : E) < 1)
    (hr : r + 1 < p) {i : ℕ} (hi : i ≤ r) {a : v.periodFiltration p r i} {x y : v.integer}
    (hx : x ∈ v.periodFiltrationIdeal p i)
    (hxa : Ideal.Quotient.mk _ x = (a : v.PeriodTruncation p r))
    (hy : (-(p : v.integer)) ^ i * y = x ^ p) :
    v.periodFrobenius p r i a = Ideal.Quotient.mk _ y := by
  simp only [periodFrobenius, hi, ↓reduceIte]
  rw [← frobLift_eq hp0 hx hy, Ideal.Quotient.eq]
  obtain ⟨hx', hx'a⟩ := (exists_mk_eq a).choose_spec
  exact frobLift_sub_mem hp0 hp1 hr hi hx' hx (Ideal.Quotient.eq.1 (hx'a.trans hxa.symm))

/-- `φᵢ = 0` for `r < i`. -/
theorem periodFrobenius_eq_zero_of_lt {i : ℕ} (hi : r < i) (a : v.periodFiltration p r i) :
    v.periodFrobenius p r i a = 0 := by
  simp [periodFrobenius, hi.not_ge]

/-- The divided Frobenius is additive. -/
theorem periodFrobenius_add [Fact p.Prime] (hp0 : (p : E) ≠ 0) (hp1 : v (p : E) < 1)
    (hr : r + 1 < p) {i : ℕ} (a b : v.periodFiltration p r i) :
    v.periodFrobenius p r i (a + b) = v.periodFrobenius p r i a + v.periodFrobenius p r i b := by
  rcases le_or_gt i r with hi | hi
  · obtain ⟨x, hx, hxa⟩ := exists_mk_eq a
    obtain ⟨y, hy, hyb⟩ := exists_mk_eq b
    rw [periodFrobenius_eq_mk hp0 hp1 hr hi (add_mem hx hy)
        (by rw [map_add, hxa, hyb, Submodule.coe_add]) (frobLift_spec (add_mem hx hy)),
      periodFrobenius_eq_mk hp0 hp1 hr hi hx hxa (frobLift_spec hx),
      periodFrobenius_eq_mk hp0 hp1 hr hi hy hyb (frobLift_spec hy), ← map_add,
      Ideal.Quotient.eq, ← sub_sub]
    exact frobLift_add_sub_mem hp0 hp1 hr hx hy
  · simp [periodFrobenius_eq_zero_of_lt hi]

/-- The divided Frobenius is `p`-semilinear over the truncation: `φᵢ (c • a) = c ^ p * φᵢ a`. -/
theorem periodFrobenius_smul [Fact p.Prime] (hp0 : (p : E) ≠ 0) (hp1 : v (p : E) < 1)
    (hr : r + 1 < p) {i : ℕ} (c : v.PeriodTruncation p r) (a : v.periodFiltration p r i) :
    v.periodFrobenius p r i (c • a) = c ^ p * v.periodFrobenius p r i a := by
  rcases le_or_gt i r with hi | hi
  · obtain ⟨x, hx, hxa⟩ := exists_mk_eq a
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [periodFrobenius_eq_mk hp0 hp1 hr hi (Ideal.mul_mem_left _ c hx)
        (by rw [map_mul, hxa, Submodule.coe_smul, smul_eq_mul])
        (y := c ^ p * frobLift p i x) (by rw [mul_left_comm, frobLift_spec hx, mul_pow]),
      periodFrobenius_eq_mk hp0 hp1 hr hi hx hxa (frobLift_spec hx), map_mul, map_pow]
  · simp [periodFrobenius_eq_zero_of_lt hi]

/-- `φᵢ 0 = 0`: the chosen representative of `0` lies in the period ideal, and so does its
image `x ^ p / (-p) ^ i`. -/
@[simp]
theorem periodFrobenius_zero [Fact p.Prime] (hp0 : (p : E) ≠ 0) {i : ℕ} :
    v.periodFrobenius p r i 0 = 0 := by
  rcases le_or_gt i r with hi | hi
  · obtain ⟨-, hx0⟩ := (exists_mk_eq (0 : v.periodFiltration p r i)).choose_spec
    simp only [periodFrobenius, hi, ↓reduceIte, Ideal.Quotient.eq_zero_iff_mem]
    exact frobLift_mem_periodIdeal hp0 hi (Ideal.Quotient.eq_zero_iff_mem.1 hx0)
  · exact periodFrobenius_eq_zero_of_lt hi 0

variable (v p r) in
/-- The divided Frobenius `φᵢ : Filⁱ A → A` bundled as an additive map. -/
@[expose, simps]
noncomputable def periodFrobeniusAddHom [Fact p.Prime] (hp0 : (p : E) ≠ 0) (hp1 : v (p : E) < 1)
    (hr : r + 1 < p) (i : ℕ) : v.periodFiltration p r i →+ v.PeriodTruncation p r where
  toFun := v.periodFrobenius p r i
  map_zero' := periodFrobenius_zero hp0
  map_add' := periodFrobenius_add hp0 hp1 hr

/-- The divided Frobenius vanishes on `Filⁱ⁺¹ A`: for `[x]` with `v x ^ p ≤ v p ^ (i + 1)`, the
quotient `x ^ p / (-p) ^ i` is divisible by `p`. This is the relation `φᵢ = p φᵢ₊₁` on `Filⁱ⁺¹ A`
of a filtered Frobenius module, in a ring killed by `p`. -/
theorem periodFrobenius_eq_zero_of_mem_succ [Fact p.Prime] (hp0 : (p : E) ≠ 0)
    (hp1 : v (p : E) < 1) (hr : r + 1 < p) {i : ℕ} (a : v.periodFiltration p r i)
    (ha : (a : v.PeriodTruncation p r) ∈ v.periodFiltration p r (i + 1)) :
    v.periodFrobenius p r i a = 0 := by
  rcases le_or_gt i r with hi | hi
  · obtain ⟨x, hx, hxa⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 ha
    rw [periodFrobenius_eq_mk hp0 hp1 hr hi (periodFiltrationIdeal_antitone i.le_succ hx) hxa
      (y := -(p : v.integer) * frobLift p (i + 1) x)
      (by rw [← mul_assoc, ← pow_succ, frobLift_spec hx]), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (neg_mem (natCast_mem_periodIdeal hp0 hp1 hr))
  · exact periodFrobenius_eq_zero_of_lt hi a

/-- The divided Frobenius is `σ`-semilinear over any ring `Λ` with a Frobenius lift `σ`, acting
through a ring map `f : Λ → v.integer`: `φᵢ ([f w] • a) = [f (σ w)] * φᵢ a`. For the Witt vectors
`W(k)` of a perfect field `k` of characteristic `p`, with `σ` the Witt-vector Frobenius
(`WittVector.isFrobeniusLift_frobenius`), this is the `σ`-semilinearity over `W(k)`. -/
theorem periodFrobenius_smul_of_isFrobeniusLift [Fact p.Prime] (hp0 : (p : E) ≠ 0)
    (hp1 : v (p : E) < 1) (hr : r + 1 < p) {Λ : Type*} [CommRing Λ] {σ : Λ →+* Λ}
    (hσ : TauCeti.DeltaRing.IsFrobeniusLift p σ) (f : Λ →+* v.integer) (w : Λ) {i : ℕ}
    (a : v.periodFiltration p r i) :
    v.periodFrobenius p r i (Ideal.Quotient.mk (v.periodIdeal p r) (f w) • a) =
      Ideal.Quotient.mk _ (f (σ w)) * v.periodFrobenius p r i a := by
  rw [periodFrobenius_smul hp0 hp1 hr]
  congr 1
  rw [← map_pow, ← map_pow, Ideal.Quotient.eq]
  obtain ⟨c, hc⟩ := hσ.dvd_sub_pow w
  rw [← neg_sub, ← _root_.map_sub, hc, _root_.map_mul, map_natCast]
  exact neg_mem (Ideal.mul_mem_right _ _ (natCast_mem_periodIdeal hp0 hp1 hr))

/-! ### Functoriality -/

namespace PeriodTruncation

variable {E' E'' Γ₀' Γ₀'' : Type*} [Field E'] [Field E''] [LinearOrderedCommGroupWithZero Γ₀']
  [LinearOrderedCommGroupWithZero Γ₀''] {v' : Valuation E' Γ₀'} {v'' : Valuation E'' Γ₀''}

private lemma map_mem_integer {g : E →+* E'} (hg : (v'.comap g).IsEquiv v) {x : E}
    (hx : x ∈ v.integer) : g x ∈ v'.integer :=
  hg.le_one_iff_le_one.2 hx

private lemma pow_lt_pow_iff_of_isEquiv {g : E →+* E'} (hg : (v'.comap g).IsEquiv v) (x : E)
    (n m : ℕ) : v' (g x) ^ n < v' (p : E') ^ m ↔ v x ^ n < v (p : E) ^ m := by
  simpa using hg.lt_iff_lt (x := x ^ n) (y := (p : E) ^ m)

private lemma pow_le_pow_iff_of_isEquiv {g : E →+* E'} (hg : (v'.comap g).IsEquiv v) (x : E)
    (n m : ℕ) : v' (g x) ^ n ≤ v' (p : E') ^ m ↔ v x ^ n ≤ v (p : E) ^ m := by
  simpa using hg.le_iff_le (x := x ^ n) (y := (p : E) ^ m)

variable (p r) in
/-- The ring map of truncations `A(E) → A(E')` induced by a field map `g : E → E'` along which
the valuations are equivalent, `v' ∘ g ∼ v`; for instance a `K`-embedding of algebraic extensions
of `K` inside an algebraic closure carrying an extended valuation. -/
noncomputable def map (g : E →+* E') (hg : (v'.comap g).IsEquiv v) :
    v.PeriodTruncation p r →+* v'.PeriodTruncation p r :=
  Ideal.quotientMap _ (g.restrict v.integer v'.integer fun _ => map_mem_integer hg) <|
    Ideal.span_le.2 fun _ (hx : _ < _) =>
      Ideal.subset_span ((pow_lt_pow_iff_of_isEquiv hg _ _ _).2 hx)

@[simp]
theorem map_mk {g : E →+* E'} (hg : (v'.comap g).IsEquiv v) (x : v.integer) :
    map p r g hg (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ ⟨g x, hg.le_one_iff_le_one.2 x.property⟩ :=
  Ideal.quotientMap_mk

/-- The identity of `E` induces the identity of the truncation. -/
@[simp]
theorem map_id (hg : (v.comap (RingHom.id E)).IsEquiv v) :
    map p r (RingHom.id E) hg = RingHom.id _ :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => by simp)

/-- The truncation map of a composite is the composite of the truncation maps. -/
theorem map_comp {g : E →+* E'} {g' : E' →+* E''} (hg : (v'.comap g).IsEquiv v)
    (hg' : (v''.comap g').IsEquiv v') (hgg' : (v''.comap (g'.comp g)).IsEquiv v) :
    map p r (g'.comp g) hgg' = (map p r g' hg').comp (map p r g hg) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => by simp)

/-- The truncation map respects the filtrations: it carries `Filⁱ A(E)` into `Filⁱ A(E')`. -/
theorem periodFiltration_le_comap_map {g : E →+* E'} (hg : (v'.comap g).IsEquiv v) (i : ℕ) :
    v.periodFiltration p r i ≤ (v'.periodFiltration p r i).comap (map p r g hg) := by
  rw [periodFiltration, Ideal.map_le_iff_le_comap, Ideal.comap_comap, periodFiltrationIdeal,
    Ideal.span_le]
  intro x (hx : _ ≤ _)
  rw [SetLike.mem_coe, Ideal.mem_comap, RingHom.comp_apply, map_mk]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ((pow_le_pow_iff_of_isEquiv hg _ _ _).2 hx))

/-- The truncation map commutes with the divided Frobenius maps. -/
theorem map_periodFrobenius [Fact p.Prime] (hp0 : (p : E) ≠ 0) (hp1 : v (p : E) < 1)
    (hr : r + 1 < p) {g : E →+* E'} (hg : (v'.comap g).IsEquiv v) {i : ℕ}
    (a : v.periodFiltration p r i) :
    map p r g hg (v.periodFrobenius p r i a) =
      v'.periodFrobenius p r i ⟨map p r g hg a, periodFiltration_le_comap_map hg i a.property⟩ := by
  have hp0' : (p : E') ≠ 0 := by simpa using g.injective.ne hp0
  have hp1' : v' (p : E') < 1 := by simpa using hg.lt_one_iff_lt_one.2 hp1
  rcases le_or_gt i r with hi | hi
  · obtain ⟨x, hx, hxa⟩ := exists_mk_eq a
    have hx' : (⟨g x, map_mem_integer hg x.property⟩ : v'.integer) ∈
        v'.periodFiltrationIdeal p i := by
      rw [mem_periodFiltrationIdeal] at hx ⊢
      exact (pow_le_pow_iff_of_isEquiv hg _ _ _).2 hx
    rw [periodFrobenius_eq_mk hp0 hp1 hr hi hx hxa (frobLift_spec hx), map_mk,
      periodFrobenius_eq_mk hp0' hp1' hr hi hx' (by rw [← map_mk hg, hxa])]
    ext
    simpa using congrArg (fun z : v.integer => g z) (frobLift_spec hx)
  · simp [periodFrobenius_eq_zero_of_lt hi]

end PeriodTruncation

end Valuation
