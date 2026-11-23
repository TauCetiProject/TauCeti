/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Countable.CycleWord
public import TauCeti.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# The continuous-dust limit for cycle-trace generating functions

Splitting residual weight `γ` across `N` positive (`b = true`) or negative (`b = false`) letters of
weight `γ / N` contributes `γ` in degree `1` (`m = 0`) and `0` in higher degrees when `Q = 1`
(`TauCeti.TypeAHeckeAlgebra.tendsto_atomicTrace_dust_cycleWord_of_sq_eq_one`), and in general
produces a factor `(1 ∓ γ * x / N) ^ N / (1 ∓ q ^ 2 * γ * x / N) ^ N` whose limit as `N → ∞` is
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

/-- **Pure-dust coefficientwise limit at `Q = 1`:** splitting weight `γ` across `N` letters of
weight `γ / N` contributes `γ` in degree `1` (`m = 0`) and `0` in higher degrees (`m ≥ 1`). -/
theorem tendsto_atomicTrace_dust_cycleWord_of_sq_eq_one {𝕜 : Type*} [RCLike 𝕜]
    (b : Bool) (q : 𝕜ˣ) (hq : (q : 𝕜) ^ 2 = 1) (γ : 𝕜) (m : ℕ) :
    Tendsto (fun N : ℕ ↦
        atomicTrace (fun _ : Fin N ↦ b = true) q (fun _ ↦ γ / N) (m + 1) (cycleWord q (m + 1)))
      atTop (𝓝 (if m = 0 then γ else 0)) := by
  have hrewrite : ∀ᶠ N : ℕ in atTop,
      atomicTrace (fun _ : Fin N ↦ b = true) q (fun _ ↦ γ / N) (m + 1) (cycleWord q (m + 1)) =
        (if m = 0 then γ else
          (if b = true then (1 : 𝕜) else -1) ^ m * γ ^ (m + 1) * ((N : 𝕜)⁻¹) ^ m) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [atomicTrace_cycleWord_of_sq_eq_one _ q hq, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rcases m with _ | m
    · simp [mul_div_cancel₀ _ hN0]
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, div_eq_mul_inv,
        mul_pow, pow_succ' (N : 𝕜)⁻¹ (m + 1)]
      linear_combination (if b = true then (1 : 𝕜) else -1) ^ (m + 1) *
        γ ^ (m + 2) * (N : 𝕜)⁻¹ ^ (m + 1) * mul_inv_cancel₀ hN0
  refine Tendsto.congr' (EventuallyEq.symm hrewrite) ?_
  rcases m with _ | m
  · simp only [↓reduceIte]
    exact tendsto_const_nhds
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    have hinv : Tendsto (fun N : ℕ ↦ ((N : 𝕜)⁻¹)) atTop (𝓝 0) := by
      have hreal : Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      simpa [Function.comp_def, map_inv₀, RCLike.ofReal_natCast] using
        ((RCLike.continuous_ofReal (K := 𝕜)).tendsto 0).comp hreal
    simpa using (hinv.pow (m + 1)).const_mul
      ((if b = true then (1 : 𝕜) else -1) ^ (m + 1) * γ ^ (m + 2))

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

/-- Splitting identity for the countable cycle-word trace of a background augmented by `N` dust
letters at `Q = 1`. -/
private theorem countableAtomicTrace_add_dust_cycleWord_of_sq_eq_one {K ι : Type*}
    [NormedField K] [CompleteSpace K] [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]
    (b : Bool) (q : Kˣ) (hq : (q : K) ^ 2 = 1) (p : ι → K) (hp : Summable fun a ↦ ‖p a‖)
    (γ : K) (N m : ℕ) :
    countableAtomicTrace (dustPos pos b N) q (fun a ↦ Sum.elim p (fun _ ↦ γ / N) (ofLex a))
        (hp.sumLex (hasSum_fintype _).summable) (m + 1) (cycleWord q (m + 1)) =
      (∑' a, (if pos a then (1 : K) else -1) ^ m * p a ^ (m + 1)) +
        atomicTrace (fun _ : Fin N ↦ b = true) q (fun _ ↦ γ / N) (m + 1) (cycleWord q (m + 1)) := by
  rw [countableAtomicTrace_cycleWord_of_sq_eq_one (dustPos pos b N) q hq,
    atomicTrace_cycleWord_of_sq_eq_one (fun _ : Fin N ↦ b = true) q hq]
  let f : ι → K := fun a ↦ (if pos a then (1 : K) else -1) ^ m * p a ^ (m + 1)
  let g : Fin N → K := fun _ ↦ (if b = true then (1 : K) else -1) ^ m * (γ / N) ^ (m + 1)
  have hbg : Summable f := (summable_signed_pow_mul_pow pos hp m).of_norm
  have hsum : HasSum (fun a : ι ⊕ₗ Fin N ↦
      (if dustPos pos b N a then (1 : K) else -1) ^ m *
        Sum.elim p (fun _ ↦ γ / N) (ofLex a) ^ (m + 1))
      ((∑' a, f a) + ∑ k : Fin N, g k) :=
    HasSum.sumLex (hbg.hasSum.congr_fun fun i ↦ by simp [f])
      ((hasSum_fintype g).congr_fun fun k ↦ by simp [g])
  exact hsum.tsum_eq

/-- **Mixed atomic-and-dust coefficientwise limit at `Q = 1`:** augmenting a countable atomic
background `(ι, pos, p)` by `N` dust letters of sign `b` and weight `γ / N` converges as `N → ∞`
in degree `m + 1` to the background signed `(m + 1)`-th power sum plus `γ` when `m = 0` and `0`
otherwise. -/
theorem tendsto_countableAtomicTrace_add_dust_cycleWord_of_sq_eq_one {𝕜 : Type*} [RCLike 𝕜]
    {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos] (b : Bool) (q : 𝕜ˣ)
    (hq : (q : 𝕜) ^ 2 = 1) (p : ι → 𝕜) (hp : Summable fun a ↦ ‖p a‖) (γ : 𝕜) (m : ℕ) :
    Tendsto (fun N : ℕ ↦
        countableAtomicTrace (dustPos pos b N) q (fun a ↦ Sum.elim p (fun _ ↦ γ / N) (ofLex a))
          (hp.sumLex (hasSum_fintype _).summable) (m + 1) (cycleWord q (m + 1)))
      atTop
      (𝓝 ((∑' a, (if pos a then (1 : 𝕜) else -1) ^ m * p a ^ (m + 1)) +
        if m = 0 then γ else 0)) :=
  (tendsto_const_nhds.add (tendsto_atomicTrace_dust_cycleWord_of_sq_eq_one b q hq γ m)).congr
    fun N ↦ (countableAtomicTrace_add_dust_cycleWord_of_sq_eq_one pos b q hq p hp γ N m).symm

private theorem tsum_norm_sum_elim_ofLex {ι : Type*} {p : ι → ℂ}
    (hp : Summable fun a ↦ ‖p a‖) (γ : ℂ) {N : ℕ} (hN : 1 ≤ N) :
    (∑' a : ι ⊕ₗ Fin N, ‖Sum.elim p (fun _ ↦ γ / N) (ofLex a)‖) = (∑' a, ‖p a‖) + ‖γ‖ := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Summable.tsum_sumLex hp (hasSum_fintype _).summable]
  simp [tsum_fintype, mul_div_cancel₀ _ hN0]

private theorem hasProd_add_dust_generating_function {ι : Type*}
    (pos : ι → Prop) [DecidablePred pos] (b : Bool) (q : ℂˣ) (p : ι → ℂ) (γ x : ℂ) (N : ℕ)
    (hbg : HasProd (fun a : ι ↦
      if pos a then (1 - p a * x) / (1 - (q : ℂ) ^ 2 * p a * x)
      else (1 + (q : ℂ) ^ 2 * p a * x) / (1 + p a * x))
      (∏' a : ι, if pos a then (1 - p a * x) / (1 - (q : ℂ) ^ 2 * p a * x)
        else (1 + (q : ℂ) ^ 2 * p a * x) / (1 + p a * x))) :
    HasProd (fun a : ι ⊕ₗ Fin N ↦
      if dustPos pos b N a then
        (1 - Sum.elim p (fun _ ↦ γ / N) (ofLex a) * x) /
          (1 - (q : ℂ) ^ 2 * Sum.elim p (fun _ ↦ γ / N) (ofLex a) * x)
      else
        (1 + (q : ℂ) ^ 2 * Sum.elim p (fun _ ↦ γ / N) (ofLex a) * x) /
          (1 + Sum.elim p (fun _ ↦ γ / N) (ofLex a) * x))
      ((∏' a : ι, if pos a then (1 - p a * x) / (1 - (q : ℂ) ^ 2 * p a * x)
        else (1 + (q : ℂ) ^ 2 * p a * x) / (1 + p a * x)) *
        (if b then (1 - γ * x / N) / (1 - (q : ℂ) ^ 2 * γ * x / N)
          else (1 + (q : ℂ) ^ 2 * γ * x / N) / (1 + γ * x / N)) ^ N) := by
  let d : ℂ :=
    if b then (1 - γ * x / N) / (1 - (q : ℂ) ^ 2 * γ * x / N)
    else (1 + (q : ℂ) ^ 2 * γ * x / N) / (1 + γ * x / N)
  have hd_prod : HasProd (fun _ : Fin N ↦ d) (d ^ N) := by
    simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      hasProd_fintype (fun _ : Fin N ↦ d)
  refine HasProd.sumLex (hbg.congr_fun fun i ↦ by simp) (hd_prod.congr_fun fun k ↦ ?_)
  cases b <;> simp only [dustPos_inr, Bool.false_eq_true, ↓reduceIte, Sum.inrₗ, ofLex_toLex,
    Sum.elim_inr, d] <;> ring_nf

/-- **Mixed atomic-and-dust cycle-trace generating limit.** Augmenting a countable atomic
background `(ι, pos, p)` by `N` dust letters of sign `b` and weight `γ / N` converges as `N → ∞`
to the background infinite cycle-trace product times `Complex.exp (((q : ℂ) ^ 2 - 1) * γ * x)`. -/
theorem tendsto_countableAtomicTrace_add_dust_generating_function {ι : Type*} [LinearOrder ι]
    (pos : ι → Prop) [DecidablePred pos] (b : Bool) (q : ℂˣ) (p : ι → ℂ)
    (hp : Summable fun a ↦ ‖p a‖) (γ x : ℂ)
    (hx : max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) * ((∑' a, ‖p a‖) + ‖γ‖) * ‖x‖ < 1) :
    Tendsto (fun N : ℕ ↦ 1 + ((q : ℂ) ^ 2 - 1) * ∑' m : ℕ,
        countableAtomicTrace (dustPos pos b N) q (fun a ↦ Sum.elim p (fun _ ↦ γ / N) (ofLex a))
          (hp.sumLex (hasSum_fintype _).summable) (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1))
      atTop
      (𝓝 ((∏' a : ι, if pos a then (1 - p a * x) / (1 - (q : ℂ) ^ 2 * p a * x)
          else (1 + (q : ℂ) ^ 2 * p a * x) / (1 + p a * x)) *
        Complex.exp (((q : ℂ) ^ 2 - 1) * γ * x))) := by
  -- 1. Background convergence bound and infinite product over `ι`.
  have hbg_hx :
      max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) * (∑' a, ‖p a‖) * ‖x‖ < 1 := by
    have : 0 ≤ max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) := by positivity
    calc
      max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) * (∑' a, ‖p a‖) * ‖x‖
        ≤ max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) * ((∑' a, ‖p a‖) + ‖γ‖) * ‖x‖ := by
          gcongr; linarith [norm_nonneg γ]
      _ < 1 := hx
  have hbg := (countableAtomicTrace_cycleWord_hasProd pos q p hp hbg_hx).2
  -- 2. Rewrite each `N ≥ 1` generating function as background product times the `N`-dust factor.
  refine Tendsto.congr' ?_ (tendsto_const_nhds.mul (tendsto_dustFactor_pow b q γ x))
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN_hx :
      max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) *
          (∑' a : ι ⊕ₗ Fin N, ‖Sum.elim p (fun _ ↦ γ / N) (ofLex a)‖) * ‖x‖ < 1 := by
    rwa [tsum_norm_sum_elim_ofLex hp γ hN]
  have hprodN := (countableAtomicTrace_cycleWord_hasProd (dustPos pos b N) q
    (fun a ↦ Sum.elim p (fun _ ↦ γ / N) (ofLex a))
    (hp.sumLex (hasSum_fintype _).summable) hN_hx).2
  exact (hasProd_add_dust_generating_function pos b q p γ x N (hbg.tprod_eq ▸ hbg)).unique hprodN

end TauCeti.TypeAHeckeAlgebra
