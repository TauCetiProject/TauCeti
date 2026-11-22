/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Sum.Order
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Countable
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# The continuous-dust limit for cycle-trace generating functions

Splitting residual weight `γ : ℂ` across `N` positive (`b = true`) or negative (`b = false`)
letters of weight `γ / N` produces a factor `(1 ∓ γ * x / N) ^ N / (1 ∓ q ^ 2 * γ * x / N) ^ N`
whose limit as `N → ∞` is `Complex.exp (((q : ℂ) ^ 2 - 1) * γ * x)`.

This module records:
* `TauCeti.TypeAHeckeAlgebra.tendsto_atomicTrace_dust_generating_function`: the pure-dust limit for
  `N` letters of weight `γ / N`.
* `TauCeti.TypeAHeckeAlgebra.tendsto_countableAtomicTrace_add_dust_generating_function`: the mixed
  limit for an arbitrary countable atomic background `ι` augmented by `N` dust letters of weight
  `γ / N`, converging to the background infinite cycle-trace product times
  `Complex.exp (((q : ℂ) ^ 2 - 1) * γ * x)`.

## References

* Yu. A. Neretin, *Some remarks on traces on the infinite-dimensional Iwahori–Hecke algebra*,
  arXiv:2101.02133, §§1.6–1.7 and §3.1, for the continuous-dust term `exp ((Q - 1) * γ * x)`.
-/

public section

open Filter
open scoped Topology

namespace TauCeti.TypeAHeckeAlgebra

private theorem tendsto_dustFactor_pow (b : Bool) (q : ℂˣ) (γ x : ℂ) :
    Tendsto (fun N : ℕ ↦
        (if b then (1 - γ * x / N) / (1 - (q : ℂ) ^ 2 * γ * x / N)
          else (1 + (q : ℂ) ^ 2 * γ * x / N) / (1 + γ * x / N)) ^ N)
      atTop (𝓝 (Complex.exp (((q : ℂ) ^ 2 - 1) * γ * x))) := by
  have hlim (u v : ℂ) : Tendsto (fun N : ℕ ↦ (1 + u / N) ^ N / (1 + v / N) ^ N) atTop
      (𝓝 (Complex.exp (u - v))) := Complex.exp_sub u v ▸
    (Complex.tendsto_one_add_div_pow_exp u).div
      (Complex.tendsto_one_add_div_pow_exp v) (Complex.exp_ne_zero _)
  cases b
  · convert hlim ((q : ℂ) ^ 2 * γ * x) (γ * x) using 1
    · ext N; simp [div_pow]
    · congr 2; ring
  · convert hlim (-(γ * x)) (-((q : ℂ) ^ 2 * γ * x)) using 1
    · ext N; simp [div_pow, sub_eq_add_neg, neg_div]
    · congr 2; ring

/-- **The continuous-dust passage (`exp ((Q - 1) * γ * x)`):** splitting weight `γ` across `N`
positive (`b = true`) or negative (`b = false`) letters of weight `γ / N` converges as `N → ∞` to
`Complex.exp (((q : ℂ) ^ 2 - 1) * γ * x)`. -/
theorem tendsto_atomicTrace_dust_generating_function (b : Bool) (q : ℂˣ) (γ x : ℂ)
    (hx : max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) * ‖γ‖ * ‖x‖ < 1) :
    Tendsto (fun N : ℕ ↦ 1 + ((q : ℂ) ^ 2 - 1) * ∑' m : ℕ,
        atomicTrace (fun _ : Fin N ↦ b = true) q (fun _ ↦ γ / N) (m + 1) (cycleWord q (m + 1)) *
          x ^ (m + 1))
      atTop (𝓝 (Complex.exp (((q : ℂ) ^ 2 - 1) * γ * x))) := by
  refine Tendsto.congr' ?_ (tendsto_dustFactor_pow b q γ x)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hsum_norm : ∑ _a : Fin N, ‖γ / (N : ℂ)‖ = ‖γ‖ := by
    simp [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (by omega) : (N : ℝ) ≠ 0)]
  rw [(atomicTrace_cycleWord_generating_eval (fun _ : Fin N ↦ b = true) q
    (fun _ ↦ γ / N) (by rwa [hsum_norm])).2, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  cases b <;> · simp only [Bool.false_eq_true, ↓reduceIte]; congr 1; congr 1 <;> ring

/-- Sign predicate on the lexicographic sum `ι ⊕ₗ Fin N`, extending `pos : ι → Prop` by `N`
dust letters of sign `b : Bool`. -/
def dustPos {ι : Type*} (pos : ι → Prop) (b : Bool) (N : ℕ) (a : ι ⊕ₗ Fin N) : Prop :=
  match ofLex a with
  | Sum.inl i => pos i
  | Sum.inr _ => b = true

instance {ι : Type*} (pos : ι → Prop) [DecidablePred pos] (b : Bool) (N : ℕ) :
    DecidablePred (dustPos pos b N) :=
  fun a ↦ match ha : ofLex a with
    | Sum.inl i => decidable_of_iff (pos i) (by simp [dustPos, ha])
    | Sum.inr _ => decidable_of_iff (b = true) (by simp [dustPos, ha])

/-- Evaluating `dustPos` on the background summand recovers `pos`. -/
@[simp]
theorem dustPos_inl {ι : Type*} (pos : ι → Prop) (b : Bool) (N : ℕ) (i : ι) :
    dustPos pos b N (Sum.inlₗ i) ↔ pos i := Iff.rfl

/-- Evaluating `dustPos` on the dust summand recovers `b = true`. -/
@[simp]
theorem dustPos_inr {ι : Type*} (pos : ι → Prop) (b : Bool) (N : ℕ) (k : Fin N) :
    dustPos pos b N (Sum.inrₗ k) ↔ b = true := Iff.rfl

/-- Augmenting an absolutely summable weight family `p : ι → ℂ` with `N` dust letters of weight
`γ / N` remains absolutely summable on `ι ⊕ₗ Fin N`. -/
theorem summable_norm_sum_elim_ofLex {ι : Type*} {p : ι → ℂ} (hp : Summable fun a ↦ ‖p a‖)
    (γ : ℂ) (N : ℕ) :
    Summable fun a : ι ⊕ₗ Fin N ↦ ‖Sum.elim p (fun _ ↦ γ / N) (ofLex a)‖ :=
  toLex.symm.summable_iff.mp <| Summable.sum _ hp (hasSum_fintype _).summable

/-- **Mixed atomic-and-dust cycle-trace generating limit.** Augmenting a countable atomic
background `(ι, pos, p)` by `N` dust letters of sign `b` and weight `γ / N` converges as `N → ∞`
to the background infinite cycle-trace product times `Complex.exp (((q : ℂ) ^ 2 - 1) * γ * x)`. -/
theorem tendsto_countableAtomicTrace_add_dust_generating_function {ι : Type*} [LinearOrder ι]
    (pos : ι → Prop) [DecidablePred pos] (b : Bool) (q : ℂˣ) (p : ι → ℂ)
    (hp : Summable fun a ↦ ‖p a‖) (γ x : ℂ)
    (hx : max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) * ((∑' a, ‖p a‖) + ‖γ‖) * ‖x‖ < 1) :
    Tendsto (fun N : ℕ ↦ 1 + ((q : ℂ) ^ 2 - 1) * ∑' m : ℕ,
        countableAtomicTrace (dustPos pos b N) q (fun a ↦ Sum.elim p (fun _ ↦ γ / N) (ofLex a))
          (summable_norm_sum_elim_ofLex hp γ N) (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1))
      atTop
      (𝓝 ((∏' a : ι, if pos a then (1 - p a * x) / (1 - (q : ℂ) ^ 2 * p a * x)
          else (1 + (q : ℂ) ^ 2 * p a * x) / (1 + p a * x)) *
        Complex.exp (((q : ℂ) ^ 2 - 1) * γ * x))) := by
  let f : ι → ℂ := fun a ↦
    if pos a then (1 - p a * x) / (1 - (q : ℂ) ^ 2 * p a * x)
    else (1 + (q : ℂ) ^ 2 * p a * x) / (1 + p a * x)
  have hbg_hx :
      max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) * (∑' a, ‖p a‖) * ‖x‖ < 1 := by
    have : 0 ≤ max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) := by positivity
    calc
      max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) * (∑' a, ‖p a‖) * ‖x‖
        ≤ max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) * ((∑' a, ‖p a‖) + ‖γ‖) * ‖x‖ := by
          gcongr; linarith [norm_nonneg γ]
      _ < 1 := hx
  have hbg := (countableAtomicTrace_cycleWord_hasProd pos q p hp hbg_hx).2
  have hbg_prod : HasProd f (∏' a : ι, f a) := by
    rwa [hbg.tprod_eq]
  refine Tendsto.congr' ?_ (tendsto_const_nhds.mul (tendsto_dustFactor_pow b q γ x))
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsum_norm :
      (∑' a : ι ⊕ₗ Fin N, ‖Sum.elim p (fun _ ↦ γ / N) (ofLex a)‖) = (∑' a, ‖p a‖) + ‖γ‖ := by
    rw [← toLex.tsum_eq]
    simp only [ofLex_toLex]
    rw [hp.tsum_sum (hasSum_fintype _).summable]
    congr 1
    rw [tsum_fintype]
    simp [mul_div_cancel₀ _ hN0]
  have hN_hx :
      max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) *
          (∑' a : ι ⊕ₗ Fin N, ‖Sum.elim p (fun _ ↦ γ / N) (ofLex a)‖) * ‖x‖ < 1 := by
    rwa [hsum_norm]
  have hprodN := (countableAtomicTrace_cycleWord_hasProd (dustPos pos b N) q
    (fun a ↦ Sum.elim p (fun _ ↦ γ / N) (ofLex a))
    (summable_norm_sum_elim_ofLex hp γ N) hN_hx).2
  let d : ℂ :=
    if b then (1 - γ * x / N) / (1 - (q : ℂ) ^ 2 * γ * x / N)
    else (1 + (q : ℂ) ^ 2 * γ * x / N) / (1 + γ * x / N)
  have hd_prod : HasProd (fun _ : Fin N ↦ d) (d ^ N) := by
    simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      hasProd_fintype (fun _ : Fin N ↦ d)
  have hsum_prod : HasProd (fun a : ι ⊕ₗ Fin N ↦
      if dustPos pos b N a then
        (1 - Sum.elim p (fun _ ↦ γ / N) (ofLex a) * x) /
          (1 - (q : ℂ) ^ 2 * Sum.elim p (fun _ ↦ γ / N) (ofLex a) * x)
      else
        (1 + (q : ℂ) ^ 2 * Sum.elim p (fun _ ↦ γ / N) (ofLex a) * x) /
          (1 + Sum.elim p (fun _ ↦ γ / N) (ofLex a) * x))
      ((∏' a : ι, f a) * d ^ N) := by
    refine toLex.hasProd_iff.mp ?_
    refine (HasProd.sum (f := Sum.elim f (fun _ ↦ d)) hbg_prod hd_prod).congr_fun fun s ↦ ?_
    rcases s with i | k
    · change (if dustPos pos b N (Sum.inlₗ i) then _ else _) = f i
      simp [f, Sum.elim_inl]
    · change (if dustPos pos b N (Sum.inrₗ k) then _ else _) = d
      cases b <;> · simp only [d, Sum.elim_inr, dustPos_inr, Bool.false_eq_true, ↓reduceIte,
        ofLex_toLex]; ring_nf
  exact hsum_prod.unique hprodN

end TauCeti.TypeAHeckeAlgebra
