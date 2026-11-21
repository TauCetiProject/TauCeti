/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.AnnularRing.Gauge
public import TauCeti.NumberTheory.Padics.Basic
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Localization.Away.Basic
import TauCeti.Topology.Algebra.InfiniteSum.Real

/-!
# Annulus evaluations on `ℤ_p⟦T, p/T⟧` and `H[1/T]`

Let `H = TauCeti.AnnularRing p` be the integral annular coefficient ring `ℤ_p⟦T, p/T⟧` and `A` be
any localization of `H` away from `T`. For any complete normed ring `K`, any bounded ring
homomorphism `f : ℤ_[p] →+* K` (satisfying `∃ C, ∀ a, ‖f a‖ ≤ C * ‖a‖`), and any unit `t : Kˣ` in
the open annulus `‖t‖ < 1` and `‖t⁻¹‖ < p`, the two-sided series `∑_{m ∈ ℤ} f(d_m) t ^ m`
converges absolutely in `K` for every `x ∈ H` and defines a ring homomorphism
`TauCeti.AnnularRing.eval₂ : AnnularRing p →+* K` sending `T ↦ t` and `U ↦ p t⁻¹`. Since `t` is a
unit, it extends uniquely to `TauCeti.AnnularRing.localizedEval₂ : A →+* K`. When `K` is
ultrametric, `eval₂` is uniformly bounded by `C` on `H` (`TauCeti.AnnularRing.norm_eval₂_le`).

We specialize this construction in two directions:
* `TauCeti.AnnularRing.eval` and `TauCeti.AnnularRing.localizedEvalAlgHom` as `ℤ_[p]`-algebra
  homomorphisms when `[Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K]`.
* `TauCeti.AnnularRing.evalAt` and `TauCeti.AnnularRing.localizedEvalAt` for any complete normed
  division ring extension `K` of `ℚ_[p]` (such as `ℂ_[p]`) and any `t : K` with `p⁻¹ < ‖t‖ < 1`.

Every annulus evaluation is continuous for the `T`-adic topology on `H[1/T]`
(`TauCeti.AnnularRing.continuous_localizedEval₂`). Nevertheless, for the `T`-adic Tate gauge of
radius `α ∈ (0, 1)`, evaluation at `t` in a complete normed division ring `K / ℚ_[p]` is Lipschitz
(equivalently bounded by a constant multiple of the norm) if and only if `α = ‖t‖`
(`TauCeti.AnnularRing.not_lipschitzWith_localizedEvalAt_of_ne`): for `α < ‖t‖` the powers `T ^ n`
blow up `(‖t‖ / α) ^ n`, while for `‖t‖ < α` the negative powers `T ^ (-n)` blow up
`(α / ‖t‖) ^ n`.

## Main definitions

* `TauCeti.AnnularRing.eval₂`, `TauCeti.AnnularRing.localizedEval₂`: evaluation ring homomorphisms
  on `H` and `H[1/T]` into any complete normed ring `K`.
* `TauCeti.AnnularRing.eval`, `TauCeti.AnnularRing.localizedEvalAlgHom`: `ℤ_[p]`-algebra
  evaluations under `[Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K]`.
* `TauCeti.AnnularRing.evalAt`, `TauCeti.AnnularRing.localizedEvalAt`: evaluations at `t : K` with
  `p⁻¹ < ‖t‖ < 1` in any complete normed division ring `K` over `ℚ_[p]`.

## Main results

* `TauCeti.AnnularRing.summable_norm_eval₂`, `TauCeti.AnnularRing.summable_eval₂`: absolute
  convergence of the bilateral evaluation series on `H`.
* `TauCeti.AnnularRing.hasSum_eval₂`, `TauCeti.AnnularRing.hasSum_localizedEval₂`: bilateral series
  expansions of evaluations on `H` and `H[1/T]`.
* `TauCeti.AnnularRing.eval₂_ofPowerSeriesT`, `TauCeti.AnnularRing.eval₂_ofPowerSeriesU`:
  evaluations of power series in `T` and `U = p / T`.
* `TauCeti.AnnularRing.eval_toRingHom`, `TauCeti.AnnularRing.localizedEvalAlgHom_toRingHom`,
  `TauCeti.AnnularRing.evalAt_eq_eval₂`, `TauCeti.AnnularRing.localizedEvalAt_eq_localizedEval₂`:
  comparison lemmas relating the specialized evaluations to `eval₂` and `localizedEval₂`.
* `TauCeti.AnnularRing.continuous_localizedEval₂`: continuity for the `T`-adic topology on `H[1/T]`.
* `TauCeti.AnnularRing.norm_localizedEvalAt_le_of_eq`,
  `TauCeti.AnnularRing.not_exists_bound_localizedEvalAt_of_ne`,
  `TauCeti.AnnularRing.not_lipschitzWith_localizedEvalAt_of_ne`: exact comparison with the
  `α`-gauge.

## References

* R. Liu, D. Wan and L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J.
  166 (2017), §§2–3.
-/

public noncomputable section

open Filter Topology

namespace TauCeti.AnnularRing

private theorem one_lt_p {p : ℕ} [Fact p.Prime] : (1 : ℝ) < p :=
  mod_cast (Fact.out : p.Prime).one_lt

private theorem p_pos {p : ℕ} [Fact p.Prime] : (0 : ℝ) < p :=
  zero_lt_one.trans one_lt_p

/-! ### General annulus evaluations into complete normed rings -/

section Eval₂

variable {p : ℕ} [Fact p.Prime]

/-- Any constant `C` satisfying `∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖` is nonnegative. -/
private theorem bound_nonneg {K : Type*} [SeminormedRing K] {f : ℤ_[p] →+* K} {C : ℝ}
    (hC : ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖) : 0 ≤ C := by
  have h := hC 1
  simp only [norm_one, mul_one] at h
  exact (norm_nonneg _).trans h

/-- Uniform geometric bound on every term `f(d_m) t ^ m` for `x ∈ H`. -/
private theorem norm_term_le {K : Type*} [SeminormedRing K] {f : ℤ_[p] →+* K} {C : ℝ}
    (hC : ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖) (t : Kˣ) (x : AnnularRing p) (m : ℤ) :
    ‖f (x.coeff m) * ((t ^ m : Kˣ) : K)‖ ≤
      C * (max ‖(t : K)‖ (‖((t⁻¹ : Kˣ) : K)‖ / p)) ^ m.natAbs := by
  have hC0 : 0 ≤ C := bound_nonneg hC
  set ρ := max ‖(t : K)‖ (‖((t⁻¹ : Kˣ) : K)‖ / p)
  rcases lt_trichotomy m 0 with hneg | rfl | hpos
  · have hm_nonneg : 0 ≤ -m := by omega
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hm_nonneg
    have hm_eq : m = -(n : ℤ) := by omega
    have hnpos : 0 < n := by omega
    have habs : m.natAbs = n := by omega
    have hcoeff : ‖x.coeff m‖ ≤ ((p : ℝ)⁻¹) ^ n := by
      have h := x.norm_coeff_le m
      rw [min_eq_right hneg.le, hm_eq, zpow_neg, zpow_natCast, ← inv_pow] at h
      rwa [hm_eq]
    have htpow : ‖((t ^ m : Kˣ) : K)‖ ≤ ‖((t⁻¹ : Kˣ) : K)‖ ^ n := by
      rw [hm_eq, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
      exact norm_pow_le' _ hnpos
    calc ‖f (x.coeff m) * ((t ^ m : Kˣ) : K)‖
        ≤ ‖f (x.coeff m)‖ * ‖((t ^ m : Kˣ) : K)‖ := norm_mul_le _ _
      _ ≤ (C * ‖x.coeff m‖) * ‖((t⁻¹ : Kˣ) : K)‖ ^ n :=
          mul_le_mul (hC _) htpow (norm_nonneg _) (mul_nonneg hC0 (norm_nonneg _))
      _ ≤ (C * ((p : ℝ)⁻¹) ^ n) * ‖((t⁻¹ : Kˣ) : K)‖ ^ n := by gcongr
      _ = C * (‖((t⁻¹ : Kˣ) : K)‖ / p) ^ n := by
          rw [mul_assoc, ← mul_pow, div_eq_inv_mul]
      _ ≤ C * ρ ^ m.natAbs := by rw [habs]; gcongr; exact le_max_right _ _
  · simpa using (hC (x.coeff 0)).trans (mul_le_of_le_one_right hC0 (PadicInt.norm_le_one _))
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hpos.le
    have hnpos : 0 < n := by omega
    have habs : m.natAbs = n := by omega
    have htpow : ‖((t ^ m : Kˣ) : K)‖ ≤ ‖(t : K)‖ ^ n := by
      rw [hn, zpow_natCast, Units.val_pow_eq_pow_val]
      exact norm_pow_le' _ hnpos
    calc ‖f (x.coeff m) * ((t ^ m : Kˣ) : K)‖
        ≤ ‖f (x.coeff m)‖ * ‖((t ^ m : Kˣ) : K)‖ := norm_mul_le _ _
      _ ≤ (C * ‖x.coeff m‖) * ‖(t : K)‖ ^ n :=
          mul_le_mul (hC _) htpow (norm_nonneg _) (mul_nonneg hC0 (norm_nonneg _))
      _ ≤ (C * 1) * ‖(t : K)‖ ^ n := by gcongr; exact PadicInt.norm_le_one _
      _ = C * ‖(t : K)‖ ^ n := by rw [mul_one]
      _ ≤ C * ρ ^ m.natAbs := by rw [habs]; gcongr; exact le_max_left _ _

/-- The norms `‖f(x.coeff m) * t ^ m‖` are summable over `ℤ` whenever `f` is bounded and
`‖t‖ < 1`, `‖t⁻¹‖ < p`. -/
theorem summable_norm_eval₂ {K : Type*} [SeminormedRing K] (f : ℤ_[p] →+* K)
    (hf : ∃ C : ℝ, ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖)
    (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) (x : AnnularRing p) :
    Summable fun m : ℤ ↦ ‖f (x.coeff m) * ((t ^ m : Kˣ) : K)‖ := by
  obtain ⟨C, hC⟩ := hf
  set ρ := max ‖(t : K)‖ (‖((t⁻¹ : Kˣ) : K)‖ / p)
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) (le_max_left _ _)
  have hρ1 : ρ < 1 := max_lt ht ((div_lt_one (p_pos (p := p))).2 htinv)
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_term_le hC t x)
    ((summable_pow_natAbs hρ0 hρ1).mul_left C)

/-- The bilateral series `∑_{m ∈ ℤ} f(x.coeff m) * t ^ m` converges in `K` whenever `‖t‖ < 1` and
`‖t⁻¹‖ < p`. -/
theorem summable_eval₂ {K : Type*} [SeminormedRing K] [CompleteSpace K] (f : ℤ_[p] →+* K)
    (hf : ∃ C : ℝ, ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖)
    (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) (x : AnnularRing p) :
    Summable fun m : ℤ ↦ f (x.coeff m) * ((t ^ m : Kˣ) : K) :=
  (summable_norm_eval₂ f hf t ht htinv x).of_norm

variable {K : Type*} [NormedRing K] [CompleteSpace K]

/-- Multiplicativity of the bilateral evaluation series on `AnnularRing p`. -/
private theorem eval₂_mul (f : ℤ_[p] →+* K) (hf : ∃ C : ℝ, ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖)
    (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) (x y : AnnularRing p) :
    (∑' m : ℤ, f ((x * y).coeff m) * ((t ^ m : Kˣ) : K)) =
      (∑' i : ℤ, f (x.coeff i) * ((t ^ i : Kˣ) : K)) *
        (∑' j : ℤ, f (y.coeff j) * ((t ^ j : Kˣ) : K)) := by
  obtain ⟨C, hC⟩ := hf
  have hfx := summable_norm_eval₂ f ⟨C, hC⟩ t ht htinv x
  have hfy := summable_norm_eval₂ f ⟨C, hC⟩ t ht htinv y
  rw [tsum_mul_tsum_of_summable_norm hfx hfy]
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    (Equiv.prodComm ℤ ℤ).trans (Equiv.prodShear (Equiv.refl ℤ) fun i ↦ (Equiv.addRight i).symm)
  have hprod : Summable fun mi : ℤ × ℤ ↦
      (f (x.coeff mi.2) * ((t ^ mi.2 : Kˣ) : K)) *
        (f (y.coeff (mi.1 - mi.2)) * ((t ^ (mi.1 - mi.2) : Kˣ) : K)) :=
    e.summable_iff.mpr (summable_mul_of_summable_norm hfx hfy)
  rw [← e.tsum_eq]
  simp only [e, Equiv.trans_apply, Equiv.prodComm_apply, Equiv.prodShear_apply, Equiv.refl_apply,
    Equiv.addRight_symm_apply, Prod.fst_swap, Prod.snd_swap, ← sub_eq_add_neg]
  rw [hprod.tsum_prod' (fun m ↦ hprod.comp_injective fun _ _ h ↦ (Prod.mk.inj h).2)]
  refine tsum_congr fun m ↦ ?_
  let g : ℤ_[p] →+ K := (AddMonoidHom.mulRight ((t ^ m : Kˣ) : K)).comp f.toAddMonoidHom
  have hf_cont : Continuous f := AddMonoidHomClass.continuous_of_bound f C hC
  have hg : Continuous g := (continuous_mul_const ((t ^ m : Kˣ) : K)).comp hf_cont
  have hg_apply (a : ℤ_[p]) : g a = f a * ((t ^ m : Kˣ) : K) := by
    simp [g]
  have hsum : HasSum (fun i : ℤ ↦ g (x.coeff i * y.coeff (m - i))) (g ((x * y).coeff m)) :=
    (hasSum_coeff_mul x y m).map g hg
  rw [← hg_apply]
  refine (hsum.congr_fun fun i ↦ ?_).tsum_eq.symm
  rw [hg_apply]
  have ht_add : ((t ^ i : Kˣ) : K) * ((t ^ (m - i) : Kˣ) : K) = ((t ^ m : Kˣ) : K) := by
    rw [← Units.val_mul, ← zpow_add, add_sub_cancel]
  have hcomm : ((t ^ i : Kˣ) : K) * f (y.coeff (m - i)) =
      f (y.coeff (m - i)) * ((t ^ i : Kˣ) : K) :=
    (PadicInt.commute_ringHom_of_continuous hf_cont (y.coeff (m - i)) ((t ^ i : Kˣ) : K)).symm
  rw [map_mul, ← ht_add, mul_assoc, ← mul_assoc ((t ^ i : Kˣ) : K), hcomm, mul_assoc, mul_assoc,
    sub_eq_add_neg]

/-- The evaluation ring homomorphism `H = ℤ_p⟦T, p/T⟧ →+* K` sending `∑ d_m T ^ m` to
`∑ f(d_m) t ^ m`, for any bounded `f : ℤ_[p] →+* K` and any unit `t : Kˣ` with `‖t‖ < 1` and
`‖t⁻¹‖ < p`. -/
def eval₂ (f : ℤ_[p] →+* K) (hf : ∃ C : ℝ, ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖)
    (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) : AnnularRing p →+* K where
  toFun x := ∑' m : ℤ, f (x.coeff m) * ((t ^ m : Kˣ) : K)
  map_zero' := by simp
  map_one' := by
    rw [tsum_eq_single (0 : ℤ) (fun m hm ↦ by simp [coeff_one, hm])]
    simp
  map_add' x y := by
    simp only [coeff_add, map_add, add_mul]
    exact (summable_eval₂ f hf t ht htinv x).tsum_add (summable_eval₂ f hf t ht htinv y)
  map_mul' := eval₂_mul f hf t ht htinv

variable (f : ℤ_[p] →+* K) (hf : ∃ C : ℝ, ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖)
  (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p)

theorem eval₂_apply (x : AnnularRing p) :
    eval₂ f hf t ht htinv x = ∑' m : ℤ, f (x.coeff m) * ((t ^ m : Kˣ) : K) := (rfl)

theorem hasSum_eval₂ (x : AnnularRing p) :
    HasSum (fun m : ℤ ↦ f (x.coeff m) * ((t ^ m : Kˣ) : K)) (eval₂ f hf t ht htinv x) :=
  (summable_eval₂ f hf t ht htinv x).hasSum

@[simp] theorem eval₂_algebraMap (c : ℤ_[p]) :
    eval₂ f hf t ht htinv (algebraMap ℤ_[p] (AnnularRing p) c) = f c := by
  rw [eval₂_apply, tsum_eq_single (0 : ℤ) (fun m hm ↦ by simp [hm])]
  simp

@[simp] theorem eval₂_T : eval₂ f hf t ht htinv T = (t : K) := by
  rw [eval₂_apply, tsum_eq_single (1 : ℤ) (fun m hm ↦ by simp [coeff_T, hm])]
  simp [coeff_T]

@[simp] theorem eval₂_U : eval₂ f hf t ht htinv U = (p : K) * ((t⁻¹ : Kˣ) : K) := by
  rw [eval₂_apply, tsum_eq_single (-1 : ℤ) (fun m hm ↦ by simp [coeff_U, hm])]
  simp [coeff_U]

/-- Evaluating a power series `g(T) ∈ H` gives the convergent power series `∑_{n ≥ 0} f(a_n) t ^ n`
in `K`. -/
theorem eval₂_ofPowerSeriesT (g : PowerSeries ℤ_[p]) :
    eval₂ f hf t ht htinv (ofPowerSeriesT g) =
      ∑' n : ℕ, f (PowerSeries.coeff n g) * (t : K) ^ n := by
  rw [eval₂_apply]
  refine tsum_eq_tsum_of_ne_zero_bij (fun n ↦ (n.val : ℤ))
    (fun _ _ h ↦ Subtype.ext (by dsimp only at h; omega)) (fun m hm ↦ ?_) fun n ↦ ?_
  · by_cases hneg : m < 0
    · exfalso; exact hm (by simp [coeff_ofPowerSeriesT_of_neg g hneg])
    · refine ⟨⟨m.toNat, ?_⟩, by dsimp only; omega⟩
      have hm_eq : (m.toNat : ℤ) = m := by omega
      rw [Function.mem_support, ← hm_eq, coeff_ofPowerSeriesT_natCast, zpow_natCast,
        Units.val_pow_eq_pow_val] at hm
      exact hm
  · simp [coeff_ofPowerSeriesT_natCast]

/-- Evaluating a power series `g(U) ∈ H` gives the convergent power series
`∑_{n ≥ 0} f(b_n) (p t⁻¹) ^ n` in `K`. -/
theorem eval₂_ofPowerSeriesU (g : PowerSeries ℤ_[p]) :
    eval₂ f hf t ht htinv (ofPowerSeriesU g) =
      ∑' n : ℕ, f (PowerSeries.coeff n g) * ((p : K) * ((t⁻¹ : Kˣ) : K)) ^ n := by
  have hmul_pow (n : ℕ) : ((p : K) * ((t⁻¹ : Kˣ) : K)) ^ n =
      (p : K) ^ n * ((t⁻¹ : Kˣ) : K) ^ n :=
    (Nat.cast_commute p ((t⁻¹ : Kˣ) : K)).mul_pow n
  have hterm (n : ℕ) :
      f ((p : ℤ_[p]) ^ n * PowerSeries.coeff n g) * ((t ^ (-(n : ℤ)) : Kˣ) : K) =
        f (PowerSeries.coeff n g) * ((p : K) * ((t⁻¹ : Kˣ) : K)) ^ n := by
    rw [map_mul, map_pow, map_natCast, zpow_neg, zpow_natCast, ← inv_pow,
      Units.val_pow_eq_pow_val, hmul_pow, ← mul_assoc,
      (Nat.cast_commute p (f (PowerSeries.coeff n g))).pow_left n, mul_assoc]
  rw [eval₂_apply]
  refine tsum_eq_tsum_of_ne_zero_bij (fun n ↦ -(n.val : ℤ))
    (fun _ _ h ↦ Subtype.ext (by dsimp only at h; omega))
    (fun m hm ↦ ?_) fun n ↦ ?_
  · by_cases hpos : 0 < m
    · exfalso; exact hm (by simp [coeff_ofPowerSeriesU_of_pos g hpos])
    · refine ⟨⟨(-m).toNat, ?_⟩, by dsimp only; omega⟩
      have hm_eq : -((-m).toNat : ℤ) = m := by omega
      rw [Function.mem_support, ← hm_eq, coeff_ofPowerSeriesU_neg_natCast, hterm] at hm
      exact hm
  · rw [coeff_ofPowerSeriesU_neg_natCast, hterm]

/-- Uniform ultrametric bound on `eval₂` over the integral ring `H`: if `‖f a‖ ≤ C * ‖a‖` for all
`a ∈ ℤ_p`, then `‖eval₂ x‖ ≤ C` for every `x ∈ H`. -/
theorem norm_eval₂_le [IsUltrametricDist K] {C : ℝ} (hC : ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖)
    (x : AnnularRing p) : ‖eval₂ f hf t ht htinv x‖ ≤ C := by
  have hC0 : 0 ≤ C := bound_nonneg hC
  set ρ := max ‖(t : K)‖ (‖((t⁻¹ : Kˣ) : K)‖ / p)
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) (le_max_left _ _)
  have hρ1 : ρ < 1 := max_lt ht ((div_lt_one (p_pos (p := p))).2 htinv)
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC0 fun m ↦ ?_
  exact (norm_term_le hC t x m).trans (mul_le_of_le_one_right hC0 (pow_le_one₀ hρ0 hρ1.le))

/-! ### Extension to `H[1/T]` and `T`-adic continuity -/

section LocalizedEval₂

variable {A : Type*} [CommRing A] [Algebra (AnnularRing p) A]
  [IsLocalization.Away (T : AnnularRing p) A]

/-- The unique extension of `eval₂` to any localization `A = H[1/T]` away from `T`. -/
def localizedEval₂ : A →+* K :=
  IsLocalization.Away.liftNoncomm (T : AnnularRing p) (eval₂ f hf t ht htinv) <| by
    rw [eval₂_T]
    exact t.isUnit

@[simp] theorem localizedEval₂_algebraMap (a : AnnularRing p) :
    localizedEval₂ f hf t ht htinv (algebraMap (AnnularRing p) A a) = eval₂ f hf t ht htinv a :=
  IsLocalization.Away.liftNoncomm_eq (T : AnnularRing p) _ _ a

theorem localizedEval₂_T :
    localizedEval₂ f hf t ht htinv (algebraMap (AnnularRing p) A T) = (t : K) := by
  rw [localizedEval₂_algebraMap, eval₂_T]

theorem localizedEval₂_U :
    localizedEval₂ f hf t ht htinv (algebraMap (AnnularRing p) A U) =
      (p : K) * ((t⁻¹ : Kˣ) : K) := by
  rw [localizedEval₂_algebraMap, eval₂_U]

/-- On integer powers of the unit `T` in `H[1/T]`, `localizedEval₂` evaluates `T ^ k` to `t ^ k`. -/
@[simp] theorem localizedEval₂_T_zpow (k : ℤ) :
    localizedEval₂ f hf t ht htinv
        (((IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit ^ k : Aˣ) : A) =
      ((t ^ k : Kˣ) : K) := by
  have hu : Units.map (localizedEval₂ (A := A) f hf t ht htinv).toMonoidHom
      (IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit = t := by
    ext
    exact localizedEval₂_T f hf t ht htinv
  change (localizedEval₂ (A := A) f hf t ht htinv).toMonoidHom
      (((IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit ^ k : Aˣ) : A) =
    ((t ^ k : Kˣ) : K)
  rw [← Units.coe_map, map_zpow, hu]

/-- For every `x ∈ H[1/T]`, the bilateral series `∑_{m ∈ ℤ} f(localizedCoeff p x m) * t ^ m`
converges to `localizedEval₂ x`. -/
theorem hasSum_localizedEval₂ (x : A) :
    HasSum (fun m : ℤ ↦ f (localizedCoeff p x m) * ((t ^ m : Kˣ) : K))
      (localizedEval₂ f hf t ht htinv x) := by
  obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj (T : AnnularRing p) x
  have hinv : (t ^ (-(k : ℤ)) : Kˣ) = (t ^ k)⁻¹ := by rw [zpow_neg, zpow_natCast]
  have hx : localizedEval₂ f hf t ht htinv x =
      eval₂ f hf t ht htinv a * ((t ^ (-(k : ℤ)) : Kˣ) : K) := by
    have h := congr_arg (localizedEval₂ f hf t ht htinv) ha
    rw [map_mul, map_pow, localizedEval₂_T, localizedEval₂_algebraMap] at h
    rw [← h, ← Units.val_pow_eq_pow_val, hinv, Units.mul_inv_cancel_right]
  have hmul : HasSum
      (fun m : ℤ ↦ (f (a.coeff m) * ((t ^ m : Kˣ) : K)) * ((t ^ (-(k : ℤ)) : Kˣ) : K))
      (localizedEval₂ f hf t ht htinv x) := by
    rw [hx]
    exact (hasSum_eval₂ f hf t ht htinv a).mul_right _
  refine ((Equiv.addRight (k : ℤ)).hasSum_iff.mpr hmul).congr_fun fun m ↦ ?_
  simp only [Function.comp_apply, Equiv.coe_addRight, mul_assoc, ← Units.val_mul, ← zpow_add,
    add_neg_cancel_right]
  rw [localizedCoeff_eq_of_mul_pow ha m]

theorem localizedEval₂_eq_tsum (x : A) :
    localizedEval₂ f hf t ht htinv x =
      ∑' m : ℤ, f (localizedCoeff p x m) * ((t ^ m : Kˣ) : K) :=
  (hasSum_localizedEval₂ f hf t ht htinv x).tsum_eq.symm

/-- On the basic `T`-adic neighbourhood `T ^ N H`, the ultrametric evaluation `localizedEval₂` is
bounded by `C * ‖t‖ ^ N`. -/
theorem norm_localizedEval₂_le_of_mem_awayNhd [IsUltrametricDist K] {C : ℝ}
    (hC : ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖) {N : ℕ} {x : A}
    (hx : x ∈ Huber.awayNhd (T : AnnularRing p) A N) :
    ‖localizedEval₂ f hf t ht htinv x‖ ≤ C * ‖(t : K)‖ ^ N := by
  obtain ⟨a, rfl⟩ := Huber.mem_awayNhd.mp hx
  rcases eq_or_ne N 0 with rfl | hN
  · simpa using norm_eval₂_le f hf t ht htinv hC a
  · rw [localizedEval₂_algebraMap, map_mul, map_pow, eval₂_T]
    calc ‖(t : K) ^ N * eval₂ f hf t ht htinv a‖
        ≤ ‖(t : K) ^ N‖ * ‖eval₂ f hf t ht htinv a‖ := norm_mul_le _ _
      _ ≤ ‖(t : K)‖ ^ N * C :=
          mul_le_mul (norm_pow_le' _ (Nat.pos_of_ne_zero hN)) (norm_eval₂_le f hf t ht htinv hC a)
            (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
      _ = C * ‖(t : K)‖ ^ N := mul_comm _ _

/-- Every annulus evaluation `H[1/T] →+* K` is continuous for any `T`-adic topology on `H[1/T]`
whose neighbourhoods of zero have basis `T ^ n H`. -/
theorem continuous_localizedEval₂ [TopologicalSpace A] [IsTopologicalAddGroup A]
    (hb : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦
      (Huber.awayNhd (T : AnnularRing p) A n : Set A)) :
    Continuous (localizedEval₂ f hf t ht htinv (A := A)) := by
  have ⟨C, hC⟩ := hf
  set ρ := max ‖(t : K)‖ (‖((t⁻¹ : Kˣ) : K)‖ / p)
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) (le_max_left _ _)
  have hρ1 : ρ < 1 := max_lt ht ((div_lt_one (p_pos (p := p))).2 htinv)
  have hgeom := (summable_pow_natAbs hρ0 hρ1).mul_left C
  set M : ℝ := ∑' m : ℤ, C * ρ ^ m.natAbs
  have hbound (a : AnnularRing p) : ‖eval₂ f hf t ht htinv a‖ ≤ M :=
    (norm_tsum_le_tsum_norm (summable_norm_eval₂ f hf t ht htinv a)).trans <|
      (summable_norm_eval₂ f hf t ht htinv a).tsum_le_tsum (norm_term_le hC t a) hgeom
  refine continuous_of_continuousAt_zero (localizedEval₂ f hf t ht htinv).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
  intro ε hε
  have hlim : Tendsto (fun N : ℕ ↦ ‖(t : K)‖ ^ (N + 1) * M) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) ht).comp
        (tendsto_add_atTop_nat 1)).mul_const M
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  filter_upwards [hb.mem_of_mem (i := N + 1) trivial] with x hx
  obtain ⟨a, rfl⟩ := Huber.mem_awayNhd.mp hx
  rw [dist_zero_right, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass,
    localizedEval₂_algebraMap, map_mul, map_pow, eval₂_T]
  calc ‖(t : K) ^ (N + 1) * eval₂ f hf t ht htinv a‖
      ≤ ‖(t : K) ^ (N + 1)‖ * ‖eval₂ f hf t ht htinv a‖ := norm_mul_le _ _
    _ ≤ ‖(t : K)‖ ^ (N + 1) * M :=
        mul_le_mul (norm_pow_le' _ (Nat.succ_pos N)) (hbound a) (norm_nonneg _)
          (pow_nonneg (norm_nonneg _) _)
    _ < ε := hN

/-- Every annulus evaluation `H[1/T] →+* K` is continuous for the `T`-adic Tate gauge of any radius
`α ∈ (0, 1)`. -/
theorem continuous_localizedEval₂_awayNormedCommRing {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    letI := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁
    Continuous (localizedEval₂ f hf t ht htinv (A := A)) := by
  let := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁
  exact continuous_localizedEval₂ f hf t ht htinv
    (Huber.hasBasis_nhds_zero_awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors
      hα₀ hα₁)

end LocalizedEval₂

end Eval₂

/-! ### `ℤ_p`-algebra evaluations under `[IsBoundedSMul ℤ_[p] K]` -/

section EvalAlgHom

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NormedRing K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K]

private theorem exists_norm_algebraMap_le :
    ∃ C : ℝ, ∀ a : ℤ_[p], ‖algebraMap ℤ_[p] K a‖ ≤ C * ‖a‖ :=
  ⟨‖(1 : K)‖, fun a ↦ by
    rw [Algebra.algebraMap_eq_smul_one, mul_comm]
    exact norm_smul_le a 1⟩

variable [CompleteSpace K]

/-- The `ℤ_p`-algebra evaluation `H →ₐ[ℤ_[p]] K` at a unit `t : Kˣ` with `‖t‖ < 1` and
`‖t⁻¹‖ < p`. -/
def eval (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) :
    AnnularRing p →ₐ[ℤ_[p]] K :=
  { eval₂ (algebraMap ℤ_[p] K) exists_norm_algebraMap_le t ht htinv with
    commutes' := eval₂_algebraMap (algebraMap ℤ_[p] K) exists_norm_algebraMap_le t ht htinv }

theorem eval_toRingHom (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p)
    (hf : ∃ C : ℝ, ∀ a : ℤ_[p], ‖algebraMap ℤ_[p] K a‖ ≤ C * ‖a‖) :
    (eval t ht htinv).toRingHom = eval₂ (algebraMap ℤ_[p] K) hf t ht htinv := (rfl)

theorem eval_apply (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p)
    (x : AnnularRing p) :
    eval t ht htinv x = ∑' m : ℤ, algebraMap ℤ_[p] K (x.coeff m) * ((t ^ m : Kˣ) : K) := (rfl)

@[simp] theorem eval_T (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) :
    eval t ht htinv T = (t : K) :=
  eval₂_T (algebraMap ℤ_[p] K) exists_norm_algebraMap_le t ht htinv

@[simp] theorem eval_U (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) :
    eval t ht htinv U = (p : K) * ((t⁻¹ : Kˣ) : K) :=
  eval₂_U (algebraMap ℤ_[p] K) exists_norm_algebraMap_le t ht htinv

/-- The `ℤ_p`-algebra evaluation `H[1/T] →ₐ[ℤ_[p]] K` at a unit `t : Kˣ` with `‖t‖ < 1` and
`‖t⁻¹‖ < p`. -/
def localizedEvalAlgHom {A : Type*} [CommRing A] [Algebra (AnnularRing p) A]
    [IsLocalization.Away (T : AnnularRing p) A] [Algebra ℤ_[p] A]
    (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) : A →ₐ[ℤ_[p]] K :=
  { localizedEval₂ (algebraMap ℤ_[p] K) exists_norm_algebraMap_le t ht htinv with
    commutes' := fun c ↦ by
      have hmap : algebraMap ℤ_[p] A c =
          algebraMap (AnnularRing p) A (algebraMap ℤ_[p] (AnnularRing p) c) :=
        DFunLike.congr_fun (ringHom_padicInt_eq (algebraMap ℤ_[p] A)) c
      rw [RingHom.toFun_eq_coe, hmap, localizedEval₂_algebraMap, eval₂_algebraMap] }

theorem localizedEvalAlgHom_toRingHom {A : Type*} [CommRing A] [Algebra (AnnularRing p) A]
    [IsLocalization.Away (T : AnnularRing p) A] [Algebra ℤ_[p] A]
    (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p)
    (hf : ∃ C : ℝ, ∀ a : ℤ_[p], ‖algebraMap ℤ_[p] K a‖ ≤ C * ‖a‖) :
    (localizedEvalAlgHom (A := A) t ht htinv).toRingHom =
      localizedEval₂ (algebraMap ℤ_[p] K) hf t ht htinv := (rfl)

@[simp] theorem localizedEvalAlgHom_algebraMap {A : Type*} [CommRing A] [Algebra (AnnularRing p) A]
    [IsLocalization.Away (T : AnnularRing p) A] [Algebra ℤ_[p] A]
    (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) (a : AnnularRing p) :
    localizedEvalAlgHom (A := A) t ht htinv (algebraMap (AnnularRing p) A a) =
      eval t ht htinv a :=
  localizedEval₂_algebraMap (algebraMap ℤ_[p] K) exists_norm_algebraMap_le t ht htinv a

theorem localizedEvalAlgHom_T {A : Type*} [CommRing A] [Algebra (AnnularRing p) A]
    [IsLocalization.Away (T : AnnularRing p) A] [Algebra ℤ_[p] A]
    (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) :
    localizedEvalAlgHom (A := A) t ht htinv (algebraMap (AnnularRing p) A T) = (t : K) := by
  rw [localizedEvalAlgHom_algebraMap, eval_T]

theorem localizedEvalAlgHom_U {A : Type*} [CommRing A] [Algebra (AnnularRing p) A]
    [IsLocalization.Away (T : AnnularRing p) A] [Algebra ℤ_[p] A]
    (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) :
    localizedEvalAlgHom (A := A) t ht htinv (algebraMap (AnnularRing p) A U) =
      (p : K) * ((t⁻¹ : Kˣ) : K) := by
  rw [localizedEvalAlgHom_algebraMap, eval_U]

end EvalAlgHom

/-! ### Evaluations into complete normed division rings over `ℚ_p` -/

section EvalAt

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NormedDivisionRing K]

private theorem ne_zero_of_inv_p_lt {t : K} (ht₀ : (p : ℝ)⁻¹ < ‖t‖) : t ≠ 0 :=
  norm_pos_iff.mp ((inv_pos.2 (p_pos (p := p))).trans ht₀)

private theorem norm_mk0_lt_one {t : K} (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) :
    ‖((Units.mk0 t (ne_zero_of_inv_p_lt ht₀) : Kˣ) : K)‖ < 1 := by
  simpa using ht₁

private theorem norm_mk0_inv_lt_p {t : K} (ht₀ : (p : ℝ)⁻¹ < ‖t‖) :
    ‖(((Units.mk0 t (ne_zero_of_inv_p_lt ht₀))⁻¹ : Kˣ) : K)‖ < p := by
  rw [Units.val_inv_eq_inv_val, Units.val_mk0, norm_inv]
  exact inv_lt_of_inv_lt₀ (p_pos (p := p)) ht₀

variable [NormedAlgebra ℚ_[p] K]

private theorem exists_norm_padicIntAlgebraMap_le :
    ∃ C : ℝ, ∀ a : ℤ_[p], ‖padicIntAlgebraMap p K a‖ ≤ C * ‖a‖ :=
  ⟨1, fun a ↦ by rw [one_mul, norm_padicIntAlgebraMap]⟩

variable [CompleteSpace K]

/-- Evaluation `H →+* K` at a point `t` in the open annulus `p⁻¹ < ‖t‖ < 1` of a complete normed
division ring `K` over `ℚ_[p]` (such as `ℂ_[p]`). -/
def evalAt (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) : AnnularRing p →+* K :=
  eval₂ (padicIntAlgebraMap p K) exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) (norm_mk0_lt_one ht₀ ht₁) (norm_mk0_inv_lt_p ht₀)

theorem evalAt_eq_eval₂ (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1)
    (u : Kˣ) (hu : (u : K) = t)
    (hf : ∃ C : ℝ, ∀ a : ℤ_[p], ‖padicIntAlgebraMap p K a‖ ≤ C * ‖a‖)
    (hu₁ : ‖(u : K)‖ < 1) (huinv : ‖((u⁻¹ : Kˣ) : K)‖ < p) :
    evalAt t ht₀ ht₁ = eval₂ (padicIntAlgebraMap p K) hf u hu₁ huinv := by
  obtain rfl : u = Units.mk0 t (ne_zero_of_inv_p_lt ht₀) := Units.ext hu
  rfl

theorem evalAt_apply (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (x : AnnularRing p) :
    evalAt t ht₀ ht₁ x = ∑' m : ℤ, padicIntAlgebraMap p K (x.coeff m) * t ^ m := by
  rw [evalAt, eval₂_apply]
  congr 1 with m
  rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]

theorem hasSum_evalAt (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (x : AnnularRing p) :
    HasSum (fun m : ℤ ↦ padicIntAlgebraMap p K (x.coeff m) * t ^ m) (evalAt t ht₀ ht₁ x) := by
  have h := hasSum_eval₂ (padicIntAlgebraMap p K) exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) (norm_mk0_lt_one ht₀ ht₁) (norm_mk0_inv_lt_p ht₀) x
  exact h.congr_fun fun m ↦ by rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]

@[simp] theorem evalAt_algebraMap (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (c : ℤ_[p]) :
    evalAt t ht₀ ht₁ (algebraMap ℤ_[p] (AnnularRing p) c) = padicIntAlgebraMap p K c :=
  eval₂_algebraMap (padicIntAlgebraMap p K) exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) (norm_mk0_lt_one ht₀ ht₁) (norm_mk0_inv_lt_p ht₀) c

@[simp] theorem evalAt_T (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) :
    evalAt t ht₀ ht₁ T = t :=
  eval₂_T (padicIntAlgebraMap p K) exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) (norm_mk0_lt_one ht₀ ht₁) (norm_mk0_inv_lt_p ht₀)

@[simp] theorem evalAt_U (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) :
    evalAt t ht₀ ht₁ U = (p : K) / t := by
  rw [evalAt, eval₂_U, Units.val_inv_eq_inv_val, Units.val_mk0, div_eq_mul_inv]

/-- Every element of `H` has absolute value at most `1` at every point `t` of the open annulus
`p⁻¹ < ‖t‖ < 1`. -/
theorem norm_evalAt_le_one (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (x : AnnularRing p) :
    ‖evalAt t ht₀ ht₁ x‖ ≤ 1 := by
  have : IsUltrametricDist K := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  exact norm_eval₂_le (padicIntAlgebraMap p K) exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) (norm_mk0_lt_one ht₀ ht₁) (norm_mk0_inv_lt_p ht₀)
    (fun a ↦ by rw [one_mul, norm_padicIntAlgebraMap]) x

section LocalizedEvalAt

variable {A : Type*} [CommRing A] [Algebra (AnnularRing p) A]
  [IsLocalization.Away (T : AnnularRing p) A]

/-- Evaluation `H[1/T] →+* K` at a point `t` in the open annulus `p⁻¹ < ‖t‖ < 1` of a complete
normed division ring `K` over `ℚ_[p]`. -/
def localizedEvalAt (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) : A →+* K :=
  localizedEval₂ (padicIntAlgebraMap p K) exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) (norm_mk0_lt_one ht₀ ht₁) (norm_mk0_inv_lt_p ht₀)

theorem localizedEvalAt_eq_localizedEval₂ (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1)
    (u : Kˣ) (hu : (u : K) = t)
    (hf : ∃ C : ℝ, ∀ a : ℤ_[p], ‖padicIntAlgebraMap p K a‖ ≤ C * ‖a‖)
    (hu₁ : ‖(u : K)‖ < 1) (huinv : ‖((u⁻¹ : Kˣ) : K)‖ < p) :
    localizedEvalAt (A := A) t ht₀ ht₁ =
      localizedEval₂ (padicIntAlgebraMap p K) hf u hu₁ huinv := by
  obtain rfl : u = Units.mk0 t (ne_zero_of_inv_p_lt ht₀) := Units.ext hu
  rfl

@[simp] theorem localizedEvalAt_algebraMap (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1)
    (a : AnnularRing p) :
    localizedEvalAt (A := A) t ht₀ ht₁ (algebraMap (AnnularRing p) A a) = evalAt t ht₀ ht₁ a :=
  localizedEval₂_algebraMap (padicIntAlgebraMap p K) exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) (norm_mk0_lt_one ht₀ ht₁) (norm_mk0_inv_lt_p ht₀) a

theorem localizedEvalAt_T (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) :
    localizedEvalAt (A := A) t ht₀ ht₁ (algebraMap (AnnularRing p) A T) = t := by
  rw [localizedEvalAt_algebraMap, evalAt_T]

theorem localizedEvalAt_U (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) :
    localizedEvalAt (A := A) t ht₀ ht₁ (algebraMap (AnnularRing p) A U) = (p : K) / t := by
  rw [localizedEvalAt_algebraMap, evalAt_U]

@[simp] theorem localizedEvalAt_T_zpow (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (k : ℤ) :
    localizedEvalAt (A := A) t ht₀ ht₁
        (((IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit ^ k : Aˣ) : A) =
      t ^ k := by
  rw [localizedEvalAt, localizedEval₂_T_zpow, Units.val_zpow_eq_zpow_val, Units.val_mk0]

theorem hasSum_localizedEvalAt (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (x : A) :
    HasSum (fun m : ℤ ↦ padicIntAlgebraMap p K (localizedCoeff p x m) * t ^ m)
      (localizedEvalAt t ht₀ ht₁ x) := by
  have h := hasSum_localizedEval₂ (A := A) (padicIntAlgebraMap p K)
    exists_norm_padicIntAlgebraMap_le (Units.mk0 t (ne_zero_of_inv_p_lt ht₀))
    (norm_mk0_lt_one ht₀ ht₁) (norm_mk0_inv_lt_p ht₀) x
  exact h.congr_fun fun m ↦ by rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]

/-- Sharp bound: every element of `T ^ N H` has norm at most `‖t‖ ^ N` under evaluation at `t`. -/
theorem norm_localizedEvalAt_le_pow_of_mem_awayNhd (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1)
    {N : ℕ} {x : A} (hx : x ∈ Huber.awayNhd (T : AnnularRing p) A N) :
    ‖localizedEvalAt t ht₀ ht₁ x‖ ≤ ‖t‖ ^ N := by
  have : IsUltrametricDist K := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  rw [localizedEvalAt]
  exact (norm_localizedEval₂_le_of_mem_awayNhd (padicIntAlgebraMap p K)
    exists_norm_padicIntAlgebraMap_le (Units.mk0 t (ne_zero_of_inv_p_lt ht₀))
    (norm_mk0_lt_one ht₀ ht₁) (norm_mk0_inv_lt_p ht₀)
    (fun a ↦ by rw [one_mul, norm_padicIntAlgebraMap]) hx).trans_eq (by simp)

/-- Evaluation at `t` is continuous for any `T`-adic topology on `H[1/T]`. -/
theorem continuous_localizedEvalAt [TopologicalSpace A] [IsTopologicalAddGroup A]
    (hb : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦
      (Huber.awayNhd (T : AnnularRing p) A n : Set A))
    (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) :
    Continuous (localizedEvalAt (A := A) t ht₀ ht₁) :=
  continuous_localizedEval₂ (padicIntAlgebraMap p K) exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) (norm_mk0_lt_one ht₀ ht₁) (norm_mk0_inv_lt_p ht₀) hb

/-- When the `T`-gauge radius equals `‖t‖`, evaluation at `t` is contractive:
`‖localizedEvalAt t x‖ ≤ ‖x‖`. -/
theorem norm_localizedEvalAt_le_of_eq (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (x : A) :
    letI := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors
      ((inv_pos.2 (Nat.cast_pos.2 (Fact.out : p.Prime).pos)).trans ht₀) ht₁
    ‖localizedEvalAt t ht₀ ht₁ x‖ ≤ ‖x‖ := by
  have htpos : 0 < ‖t‖ := (inv_pos.2 (p_pos (p := p))).trans ht₀
  let := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors htpos ht₁
  rw [Huber.norm_awayNormedCommRing]
  set d := Huber.awayTateNormDatum
    (Huber.hasBasis_nhds_zero_awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors
      htpos ht₁)
    htpos ht₁
  refine le_of_forall_gt fun r hr ↦ ?_
  obtain ⟨n, hmem, hnr⟩ := (Huber.tateNorm_lt_iff d).1 hr
  rw [Huber.awayTateNormDatum_pseudoUniformizer, Huber.awayTateNormDatum_ringOfDefinition] at hmem
  obtain ⟨a, ha⟩ := hmem
  set u : Aˣ := (IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit
  have ha' : (((u ^ n : Aˣ)⁻¹ : Aˣ) : A) * x = algebraMap (AnnularRing p) A a := by
    simpa only [zpow_neg] using ha.symm
  have hx : x = ((u ^ n : Aˣ) : A) * algebraMap (AnnularRing p) A a :=
    (Units.inv_mul_eq_iff_eq_mul (u ^ n)).mp ha'
  have hr' : ‖t‖ ^ n < r := by simpa only [d, Huber.awayTateNormDatum_radius] using hnr
  calc ‖localizedEvalAt t ht₀ ht₁ x‖
      = ‖t ^ n * evalAt t ht₀ ht₁ a‖ := by
        rw [hx, map_mul, localizedEvalAt_T_zpow, localizedEvalAt_algebraMap]
    _ = ‖t‖ ^ n * ‖evalAt t ht₀ ht₁ a‖ := by rw [norm_mul, norm_zpow]
    _ ≤ ‖t‖ ^ n := mul_le_of_le_one_right (zpow_nonneg (norm_nonneg _) _)
        (norm_evalAt_le_one t ht₀ ht₁ a)
    _ < r := hr'

/-- For any `T`-gauge radius `α ∈ (0, 1)` different from `‖t‖`, evaluation at `t` is not bounded
by any constant multiple of the `α`-gauge norm (even though it is continuous for the `T`-adic
topology): positive powers `T ^ n` witness unboundedness when `α < ‖t‖`, and negative powers
`T ^ (-n)` witness it when `‖t‖ < α`. -/
theorem not_exists_bound_localizedEvalAt_of_ne {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (hne : α ≠ ‖t‖) :
    letI := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁
    ¬ ∃ C : ℝ, ∀ x : A, ‖localizedEvalAt t ht₀ ht₁ x‖ ≤ C * ‖x‖ := by
  let := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁
  have : Nontrivial A := (algebraMap_injective (p := p) (A := A)).nontrivial
  have : NormOneClass A :=
    Huber.normOneClass_awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁
  rintro ⟨C, hC⟩
  have htpos : 0 < ‖t‖ := (inv_pos.2 (p_pos (p := p))).trans ht₀
  have hpow (k : ℤ) : ‖t‖ ^ k ≤ C * α ^ k := by
    set u : Aˣ := (IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit
    have hnorm_u : ‖((u ^ k : Aˣ) : A)‖ = α ^ k := by
      have h1 := Huber.norm_pseudoUniformizer_zpow_mul_awayNormedCommRing
        (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁ k 1
      rw [mul_one, norm_one, mul_one] at h1
      exact h1
    have hc := hC ((u ^ k : Aˣ) : A)
    rw [hnorm_u] at hc
    rwa [localizedEvalAt_T_zpow, norm_zpow] at hc
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨n, hn⟩ :=
      ((tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div hα₀).2 hlt)).eventually_gt_atTop C).exists
    have hle : (‖t‖ / α) ^ n ≤ C := by
      rw [div_pow, div_le_iff₀ (pow_pos hα₀ n)]
      simpa only [zpow_natCast] using hpow (n : ℤ)
    exact hn.not_ge hle
  · obtain ⟨n, hn⟩ :=
      ((tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div htpos).2 hgt)).eventually_gt_atTop C).exists
    have h := hpow (-(n : ℤ))
    rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast] at h
    have hle : (α / ‖t‖) ^ n ≤ C := calc
      (α / ‖t‖) ^ n = α ^ n * (‖t‖ ^ n)⁻¹ := by rw [div_pow, div_eq_mul_inv]
      _ ≤ α ^ n * (C * (α ^ n)⁻¹) := mul_le_mul_of_nonneg_left h (pow_nonneg hα₀.le n)
      _ = C := by field_simp
    exact hn.not_ge hle

/-- In particular, evaluation at `t` is not Lipschitz for the `α`-gauge whenever `α ≠ ‖t‖`. -/
theorem not_lipschitzWith_localizedEvalAt_of_ne {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (hne : α ≠ ‖t‖) :
    letI := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁
    ¬ ∃ L : NNReal, LipschitzWith L (localizedEvalAt (A := A) t ht₀ ht₁) := by
  let := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁
  rintro ⟨L, hL⟩
  refine not_exists_bound_localizedEvalAt_of_ne (A := A) hα₀ hα₁ t ht₀ ht₁ hne ⟨(L : ℝ), fun x ↦ ?_⟩
  have := hL.dist_le_mul x 0
  simpa only [map_zero, dist_zero_right] using this

end LocalizedEvalAt

end EvalAt

end TauCeti.AnnularRing
