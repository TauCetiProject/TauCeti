/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.AnnularRing.Localization
public import TauCeti.NumberTheory.Padics.Basic
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import TauCeti.Analysis.Normed.Operator.BoundedLinearMaps
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
`TauCeti.AnnularRing.eval₂ : AnnularRing p →+* K` sending `T ↦ t` and `U ↦ p t⁻¹`. It is the
unique ring homomorphism bounded on `H` extending `f` and sending `T ↦ t`
(`TauCeti.AnnularRing.eq_eval₂_of_bound`). Since `t` is a unit, it extends uniquely to
`TauCeti.AnnularRing.localizedEval₂ : A →+* K`. When `K` is ultrametric, `eval₂` is uniformly
bounded by `C` on `H` (`TauCeti.AnnularRing.norm_eval₂_le`).

We specialize this construction in two directions:
* `TauCeti.AnnularRing.eval` and `TauCeti.AnnularRing.localizedEvalAlgHom` as `ℤ_[p]`-algebra
  homomorphisms when `[Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K]`.
* `TauCeti.AnnularRing.evalAt` and `TauCeti.AnnularRing.localizedEvalAt` for any complete normed
  division ring extension `K` of `ℚ_[p]` (such as `ℂ_[p]`) and any `t : K` with `p⁻¹ < ‖t‖ < 1`.

Every annulus evaluation is continuous for any `T`-adic topology on `H[1/T]` whose neighbourhoods
of zero have basis `T ^ n H` (`TauCeti.AnnularRing.continuous_localizedEval₂`), and is the unique
continuous ring homomorphism extending `f` and sending `T ↦ t`
(`TauCeti.AnnularRing.eq_localizedEval₂_of_continuous`).

## Main definitions

* `TauCeti.AnnularRing.eval₂`, `TauCeti.AnnularRing.localizedEval₂`: evaluation ring homomorphisms
  on `H` and `H[1/T]` into any complete normed ring `K`.
* `TauCeti.AnnularRing.eval`, `TauCeti.AnnularRing.localizedEvalAlgHom`: `ℤ_[p]`-algebra
  evaluations under `[Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K]`.
* `TauCeti.AnnularRing.evalAt`, `TauCeti.AnnularRing.localizedEvalAt`: evaluations at `t : K` with
  `p⁻¹ < ‖t‖ < 1` in any complete normed division ring `K` over `ℚ_[p]`.

## Main results

* `TauCeti.AnnularRing.norm_coeff_mul_le`: uniform geometric term estimate for coefficients in
  `AnnularRing p`.
* `TauCeti.AnnularRing.summable_norm_eval₂`, `TauCeti.AnnularRing.summable_eval₂`,
  `TauCeti.AnnularRing.summable_norm_localizedEval₂`: absolute convergence of the bilateral
  evaluation series on `H` and `H[1/T]`.
* `TauCeti.AnnularRing.hasSum_eval₂`, `TauCeti.AnnularRing.hasSum_localizedEval₂`: bilateral series
  expansions of evaluations on `H` and `H[1/T]`.
* `TauCeti.AnnularRing.eval₂_ofPowerSeriesT`, `TauCeti.AnnularRing.eval₂_ofPowerSeriesU`:
  evaluations of power series in `T` and `U = p / T`.
* `TauCeti.AnnularRing.eq_eval₂_of_bound`, `TauCeti.AnnularRing.eq_localizedEval₂_of_continuous`:
  uniqueness of bounded evaluations on `H` and `T`-adically continuous evaluations on `H[1/T]`.
* `TauCeti.AnnularRing.eval_toRingHom`, `TauCeti.AnnularRing.localizedEvalAlgHom_toRingHom`,
  `TauCeti.AnnularRing.evalAt_eq_eval₂`, `TauCeti.AnnularRing.localizedEvalAt_eq_localizedEval₂`:
  comparison lemmas relating the specialized evaluations to `eval₂` and `localizedEval₂`.
* `TauCeti.AnnularRing.continuous_localizedEval₂`: continuity for the `T`-adic topology on `H[1/T]`.

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

/-- Uniform geometric bound on a term `‖x.coeff m‖ * r ^ |m|` using `r₀` in nonnegative degrees
and `r₁` in negative degrees. -/
theorem norm_coeff_mul_le (x : AnnularRing p) {r₀ r₁ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁)
    (m : ℤ) :
    ‖x.coeff m‖ * (if 0 ≤ m then r₀ else r₁) ^ m.natAbs ≤ (max r₀ (r₁ / p)) ^ m.natAbs := by
  rcases le_or_gt 0 m with hm | hm
  · rw [ite_eq_left hm]
    calc ‖x.coeff m‖ * r₀ ^ m.natAbs
        ≤ 1 * r₀ ^ m.natAbs :=
          mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (pow_nonneg hr₀ _)
      _ = r₀ ^ m.natAbs := one_mul _
      _ ≤ (max r₀ (r₁ / p)) ^ m.natAbs := pow_le_pow_left₀ hr₀ (le_max_left _ _) _
  · rw [ite_eq_right hm.not_ge]
    have hm_eq : m = -(m.natAbs : ℤ) := by omega
    have hcoeff : ‖x.coeff m‖ ≤ ((p : ℝ)⁻¹) ^ m.natAbs := by
      calc ‖x.coeff m‖
          ≤ (p : ℝ) ^ m := by simpa [min_eq_right hm.le] using x.norm_coeff_le m
        _ = ((p : ℝ)⁻¹) ^ m.natAbs := by
            conv_lhs => rw [hm_eq]
            rw [zpow_neg, zpow_natCast, ← inv_pow]
    calc ‖x.coeff m‖ * r₁ ^ m.natAbs
        ≤ ((p : ℝ)⁻¹) ^ m.natAbs * r₁ ^ m.natAbs :=
          mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hr₁ _)
      _ = (r₁ / p) ^ m.natAbs := by rw [← mul_pow, div_eq_inv_mul]
      _ ≤ (max r₀ (r₁ / p)) ^ m.natAbs :=
          pow_le_pow_left₀ (div_nonneg hr₁ (p_pos (p := p)).le) (le_max_right _ _) _

/-- Uniform geometric bound on every term `f(d_m) t ^ m` for `x ∈ H`. -/
private theorem norm_term_le {K : Type*} [SeminormedRing K] {f : ℤ_[p] →+* K} {C : ℝ}
    (hC : ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖) (t : Kˣ) (x : AnnularRing p) (m : ℤ) :
    ‖f (x.coeff m) * ((t ^ m : Kˣ) : K)‖ ≤
      C * (max ‖(t : K)‖ (‖((t⁻¹ : Kˣ) : K)‖ / p)) ^ m.natAbs := by
  have hC0 : 0 ≤ C := bound_nonneg hC
  rcases eq_or_ne m 0 with rfl | hm
  · simpa using (hC (x.coeff 0)).trans (mul_le_of_le_one_right hC0 (PadicInt.norm_le_one _))
  · have htpow :
        ‖((t ^ m : Kˣ) : K)‖ ≤ (if 0 ≤ m then ‖(t : K)‖ else ‖((t⁻¹ : Kˣ) : K)‖) ^ m.natAbs := by
      rcases lt_or_gt_of_ne hm with hneg | hpos
      · rw [ite_eq_right hneg.not_ge]
        have hm_eq : m = -(m.natAbs : ℤ) := by omega
        calc ‖((t ^ m : Kˣ) : K)‖
            = ‖((t⁻¹ : Kˣ) : K) ^ m.natAbs‖ := by
              conv_lhs => rw [hm_eq]
              rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
          _ ≤ ‖((t⁻¹ : Kˣ) : K)‖ ^ m.natAbs := norm_pow_le' _ (Int.natAbs_pos.mpr hm)
      · rw [ite_eq_left hpos.le]
        have hm_eq : m = (m.natAbs : ℤ) := by omega
        calc ‖((t ^ m : Kˣ) : K)‖
            = ‖(t : K) ^ m.natAbs‖ := by
              conv_lhs => rw [hm_eq]
              rw [zpow_natCast, Units.val_pow_eq_pow_val]
          _ ≤ ‖(t : K)‖ ^ m.natAbs := norm_pow_le' _ (Int.natAbs_pos.mpr hm)
    calc ‖f (x.coeff m) * ((t ^ m : Kˣ) : K)‖
        ≤ ‖f (x.coeff m)‖ * ‖((t ^ m : Kˣ) : K)‖ := norm_mul_le _ _
      _ ≤ (C * ‖x.coeff m‖) * (if 0 ≤ m then ‖(t : K)‖ else ‖((t⁻¹ : Kˣ) : K)‖) ^ m.natAbs :=
          mul_le_mul (hC _) htpow (norm_nonneg _) (mul_nonneg hC0 (norm_nonneg _))
      _ = C * (‖x.coeff m‖ * (if 0 ≤ m then ‖(t : K)‖ else ‖((t⁻¹ : Kˣ) : K)‖) ^ m.natAbs) := by
          ring
      _ ≤ C * (max ‖(t : K)‖ (‖((t⁻¹ : Kˣ) : K)‖ / p)) ^ m.natAbs :=
          mul_le_mul_of_nonneg_left (norm_coeff_mul_le x (norm_nonneg _) (norm_nonneg _) m) hC0

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

/-- Uniform geometric-series bound on `eval₂` over `H` without ultrametricity. -/
private theorem exists_norm_eval₂_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : AnnularRing p, ‖eval₂ f hf t ht htinv a‖ ≤ M := by
  obtain ⟨C, hC⟩ := hf
  have hC0 : 0 ≤ C := bound_nonneg hC
  set ρ := max ‖(t : K)‖ (‖((t⁻¹ : Kˣ) : K)‖ / p)
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) (le_max_left _ _)
  have hρ1 : ρ < 1 := max_lt ht ((div_lt_one (p_pos (p := p))).2 htinv)
  have hgeom := (summable_pow_natAbs hρ0 hρ1).mul_left C
  refine ⟨∑' m : ℤ, C * ρ ^ m.natAbs, tsum_nonneg fun m ↦ mul_nonneg hC0 (pow_nonneg hρ0 _),
    fun a ↦ (norm_tsum_le_tsum_norm (summable_norm_eval₂ f ⟨C, hC⟩ t ht htinv a)).trans <|
      (summable_norm_eval₂ f ⟨C, hC⟩ t ht htinv a).tsum_le_tsum (norm_term_le hC t a) hgeom⟩

/-- **Uniqueness on `H`**: any ring homomorphism `φ : AnnularRing p →+* K` bounded on `H` that
agrees with `f` on `ℤ_p` and sends `T` to `t` equals `eval₂ f hf t ht htinv`. -/
theorem eq_eval₂_of_bound (φ : AnnularRing p →+* K) {B : ℝ}
    (hφ_bdd : ∀ x : AnnularRing p, ‖φ x‖ ≤ B)
    (hφ_alg : ∀ c : ℤ_[p], φ (algebraMap ℤ_[p] (AnnularRing p) c) = f c)
    (hφ_T : φ T = (t : K)) :
    φ = eval₂ f hf t ht htinv := by
  have hφ_U : φ U = (p : K) * ((t⁻¹ : Kˣ) : K) := by
    have hTU : φ T * φ U = (p : K) := by
      rw [← map_mul, T_mul_U, map_natCast]
    calc φ U = ((t⁻¹ : Kˣ) : K) * ((t : K) * φ U) := by
          rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      _ = ((t⁻¹ : Kˣ) : K) * (p : K) := by rw [← hφ_T, hTU]
      _ = (p : K) * ((t⁻¹ : Kˣ) : K) := (Nat.cast_commute p _).symm.eq
  obtain ⟨C, hC⟩ := hf
  have hC0 : 0 ≤ C := bound_nonneg hC
  obtain ⟨M, _, hM⟩ := exists_norm_eval₂_le f ⟨C, hC⟩ t ht htinv
  ext x
  have hc (k : ℕ) : ∃ c : ℤ_[p], x.coeff (-k) = (p : ℤ_[p]) ^ k * c := x.pow_dvd_coeff_neg k
  choose c hc_spec using hc
  let coeffHom (m : ℤ) : AnnularRing p →+ ℤ_[p] :=
    { toFun := fun y ↦ y.coeff m
      map_zero' := coeff_zero m
      map_add' := fun y z ↦ coeff_add y z m }
  have happrox (N : ℕ) :
      ‖φ x - eval₂ f ⟨C, hC⟩ t ht htinv x‖ ≤
        (‖(t : K)‖ ^ (N + 1) + C * (‖((t⁻¹ : Kˣ) : K)‖ / p) ^ (N + 1)) * (B + M) := by
    let P : AnnularRing p :=
      (∑ n ∈ Finset.range (N + 1), x.coeff n • (T : AnnularRing p) ^ n) +
        ∑ j ∈ Finset.Icc 1 N, c j • (U : AnnularRing p) ^ j
    let xpos : AnnularRing p :=
      ⟨fun m ↦ if 0 ≤ m then x.coeff (m + (N + 1 : ℕ)) else 0, fun m ↦ by
        split_ifs with hm
        · rw [min_eq_left hm, zpow_zero]
          exact PadicInt.norm_le_one _
        · simp only [norm_zero]; positivity⟩
    let xneg : AnnularRing p :=
      ⟨fun m ↦ if m ≤ 0 then (p : ℤ_[p]) ^ (-m).toNat * c ((-m).toNat + (N + 1)) else 0,
        fun m ↦ by
          split_ifs with hm
          · rw [norm_mul]
            refine (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)).trans_eq ?_
            rw [PadicInt.norm_p_pow]
            congr 1
            omega
          · simp only [norm_zero]; positivity⟩
    have hx_split : x = P + T ^ (N + 1) * xpos + U ^ (N + 1) * xneg := by
      ext m : 2
      have hcoeff_sum (s : Finset ℕ) (g : ℕ → AnnularRing p) :
          (∑ i ∈ s, g i).coeff m = ∑ i ∈ s, (g i).coeff m :=
        map_sum (coeffHom m) g s
      have hU_mul : ((U : AnnularRing p) ^ (N + 1) * xneg).coeff m =
          (p : ℤ_[p]) ^ (N + 1) * xneg.coeff (m + (N + 1 : ℕ)) := by
        rw [coeff_mul_of_coeff_eq_zero (k := -((N + 1 : ℕ) : ℤ))
          (fun i hi ↦ by rw [coeff_U_pow, ite_eq_right hi]), coeff_U_pow, ite_eq_left rfl,
          sub_neg_eq_add]
      have hT_part : (∑ n ∈ Finset.range (N + 1), x.coeff n • (T : AnnularRing p) ^ n).coeff m =
          if 0 ≤ m ∧ m ≤ N then x.coeff m else 0 := by
        rw [hcoeff_sum]
        simp only [coeff_smul, coeff_T_pow]
        split_ifs with hm
        · refine (Finset.sum_eq_single m.toNat (fun n _ hn ↦ ?_) (fun hmem ↦ ?_)).trans ?_
          · rw [ite_eq_right (fun h ↦ hn (by omega)), mul_zero]
          · exfalso; exact hmem (Finset.mem_range.mpr (by omega))
          · have hm_eq : (m.toNat : ℤ) = m := by omega
            simp [hm_eq]
        · refine Finset.sum_eq_zero fun n hn ↦ ?_
          rw [Finset.mem_range] at hn
          rw [ite_eq_right (fun h ↦ hm ⟨by omega, by omega⟩), mul_zero]
      have hU_part : (∑ j ∈ Finset.Icc 1 N, c j • (U : AnnularRing p) ^ j).coeff m =
          if -(N : ℤ) ≤ m ∧ m < 0 then x.coeff m else 0 := by
        rw [hcoeff_sum]
        simp only [coeff_smul, coeff_U_pow]
        split_ifs with hm
        · refine (Finset.sum_eq_single (-m).toNat (fun j _ hj ↦ ?_) (fun hmem ↦ ?_)).trans ?_
          · rw [ite_eq_right (fun h ↦ hj (by omega)), mul_zero]
          · exfalso; exact hmem (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          · have hm_eq : -((-m).toNat : ℤ) = m := by omega
            rw [ite_eq_left hm_eq.symm, mul_comm, ← hc_spec, hm_eq]
        · refine Finset.sum_eq_zero fun j hj ↦ ?_
          rw [Finset.mem_Icc] at hj
          rw [ite_eq_right (fun h ↦ hm ⟨by omega, by omega⟩), mul_zero]
      rw [coeff_add, coeff_add, coeff_add, hT_part, hU_part, coeff_T_pow_mul, hU_mul]
      dsimp only [xpos, xneg]
      by_cases hmN : (N + 1 : ℤ) ≤ m
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
          ite_eq_right (by omega), mul_zero, zero_add, zero_add, add_zero, sub_add_cancel]
      · by_cases hm0 : 0 ≤ m
        · rw [ite_eq_left ⟨hm0, by omega⟩, ite_eq_right (by omega), ite_eq_right (by omega),
            ite_eq_right (by omega)]
          ring
        · by_cases hmneg : -(N : ℤ) ≤ m
          · rw [ite_eq_right (by omega), ite_eq_left ⟨hmneg, by omega⟩, ite_eq_right (by omega),
              ite_eq_right (by omega)]
            ring
          · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
              ite_eq_left (by omega)]
            have hm_eq : -((-m).toNat : ℤ) = m := by omega
            have hpow : (p : ℤ_[p]) ^ (N + 1) * (p : ℤ_[p]) ^ (-(m + (N + 1 : ℕ))).toNat =
                (p : ℤ_[p]) ^ (-m).toNat := by
              rw [← pow_add]
              congr 1
              omega
            have hidx : (-(m + (N + 1 : ℕ))).toNat + (N + 1) = (-m).toNat := by omega
            rw [zero_add, zero_add, zero_add, hidx, ← mul_assoc, hpow, ← hc_spec, hm_eq]
    have hP : φ P = eval₂ f ⟨C, hC⟩ t ht htinv P := by
      simp only [P, map_add, map_sum, Algebra.smul_def, map_mul, map_pow, hφ_alg, hφ_T, hφ_U,
        eval₂_algebraMap, eval₂_T, eval₂_U]
    have hdiff : φ x - eval₂ f ⟨C, hC⟩ t ht htinv x =
        (φ (T ^ (N + 1) * xpos) - eval₂ f ⟨C, hC⟩ t ht htinv (T ^ (N + 1) * xpos)) +
          (φ (U ^ (N + 1) * xneg) - eval₂ f ⟨C, hC⟩ t ht htinv (U ^ (N + 1) * xneg)) := by
      conv_lhs => rw [hx_split]
      simp only [map_add, hP]
      abel
    have hT_norm (ψ : AnnularRing p →+* K) (hψ_T : ψ T = (t : K)) {R : ℝ}
        (hR : ‖ψ xpos‖ ≤ R) : ‖ψ (T ^ (N + 1) * xpos)‖ ≤ ‖(t : K)‖ ^ (N + 1) * R := by
      rw [map_mul, map_pow, hψ_T]
      exact (norm_mul_le _ _).trans
        (mul_le_mul (norm_pow_le' _ (Nat.succ_pos N)) hR (norm_nonneg _)
          (pow_nonneg (norm_nonneg _) _))
    have hU_norm (ψ : AnnularRing p →+* K) (hψ_U : ψ U = (p : K) * ((t⁻¹ : Kˣ) : K))
        {R : ℝ} (hR : ‖ψ xneg‖ ≤ R) :
        ‖ψ (U ^ (N + 1) * xneg)‖ ≤ C * (‖((t⁻¹ : Kˣ) : K)‖ / p) ^ (N + 1) * R := by
      rw [map_mul, map_pow, hψ_U, (Nat.cast_commute p ((t⁻¹ : Kˣ) : K)).mul_pow (N + 1),
        ← map_natCast f p, ← map_pow f (p : ℤ_[p]) (N + 1)]
      have hUpow : ‖f ((p : ℤ_[p]) ^ (N + 1)) * ((t⁻¹ : Kˣ) : K) ^ (N + 1)‖ ≤
          C * (‖((t⁻¹ : Kˣ) : K)‖ / p) ^ (N + 1) := by
        calc ‖f ((p : ℤ_[p]) ^ (N + 1)) * ((t⁻¹ : Kˣ) : K) ^ (N + 1)‖
            ≤ ‖f ((p : ℤ_[p]) ^ (N + 1))‖ * ‖((t⁻¹ : Kˣ) : K) ^ (N + 1)‖ := norm_mul_le _ _
          _ ≤ (C * ‖(p : ℤ_[p]) ^ (N + 1)‖) * ‖((t⁻¹ : Kˣ) : K)‖ ^ (N + 1) :=
              mul_le_mul (hC _) (norm_pow_le' _ (Nat.succ_pos N)) (norm_nonneg _)
                (mul_nonneg hC0 (norm_nonneg _))
          _ = C * (((p : ℝ)⁻¹) ^ (N + 1) * ‖((t⁻¹ : Kˣ) : K)‖ ^ (N + 1)) := by
              rw [PadicInt.norm_p_pow, zpow_neg, zpow_natCast, ← inv_pow, mul_assoc]
          _ = C * (‖((t⁻¹ : Kˣ) : K)‖ / p) ^ (N + 1) := by
              rw [← mul_pow, mul_comm ((p : ℝ)⁻¹), ← div_eq_mul_inv]
      exact (norm_mul_le _ _).trans (mul_le_mul hUpow hR (norm_nonneg _) (by positivity))
    have h1 := (norm_sub_le _ _).trans (add_le_add
      (hT_norm φ hφ_T (hφ_bdd xpos))
      (hT_norm (eval₂ f ⟨C, hC⟩ t ht htinv) (eval₂_T f ⟨C, hC⟩ t ht htinv) (hM xpos)))
    have h2 := (norm_sub_le _ _).trans (add_le_add
      (hU_norm φ hφ_U (hφ_bdd xneg))
      (hU_norm (eval₂ f ⟨C, hC⟩ t ht htinv) (eval₂_U f ⟨C, hC⟩ t ht htinv) (hM xneg)))
    rw [hdiff]
    calc ‖(φ (T ^ (N + 1) * xpos) - eval₂ f ⟨C, hC⟩ t ht htinv (T ^ (N + 1) * xpos)) +
            (φ (U ^ (N + 1) * xneg) - eval₂ f ⟨C, hC⟩ t ht htinv (U ^ (N + 1) * xneg))‖
        ≤ ‖φ (T ^ (N + 1) * xpos) - eval₂ f ⟨C, hC⟩ t ht htinv (T ^ (N + 1) * xpos)‖ +
            ‖φ (U ^ (N + 1) * xneg) - eval₂ f ⟨C, hC⟩ t ht htinv (U ^ (N + 1) * xneg)‖ :=
          norm_add_le _ _
      _ ≤ (‖(t : K)‖ ^ (N + 1) * B + ‖(t : K)‖ ^ (N + 1) * M) +
            (C * (‖((t⁻¹ : Kˣ) : K)‖ / p) ^ (N + 1) * B +
              C * (‖((t⁻¹ : Kˣ) : K)‖ / p) ^ (N + 1) * M) := add_le_add h1 h2
      _ = (‖(t : K)‖ ^ (N + 1) + C * (‖((t⁻¹ : Kˣ) : K)‖ / p) ^ (N + 1)) * (B + M) := by ring
  have ht_lim : Tendsto (fun N : ℕ ↦ ‖(t : K)‖ ^ (N + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) ht).comp (tendsto_add_atTop_nat 1)
  have hu_lim : Tendsto (fun N : ℕ ↦ C * (‖((t⁻¹ : Kˣ) : K)‖ / p) ^ (N + 1)) atTop (𝓝 0) := by
    have hdiv : ‖((t⁻¹ : Kˣ) : K)‖ / p < 1 := (div_lt_one (p_pos (p := p))).2 htinv
    simpa only [Function.comp_apply, mul_zero] using ((tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg (norm_nonneg _) (p_pos (p := p)).le) hdiv).comp
      (tendsto_add_atTop_nat 1)).const_mul C
  have hlim : Tendsto
      (fun N : ℕ ↦ (‖(t : K)‖ ^ (N + 1) + C * (‖((t⁻¹ : Kˣ) : K)‖ / p) ^ (N + 1)) * (B + M))
      atTop (𝓝 0) := by
    simpa only [add_zero, zero_mul] using (ht_lim.add hu_lim).mul_const (B + M)
  have hle0 : ‖φ x - eval₂ f ⟨C, hC⟩ t ht htinv x‖ ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlim happrox
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hle0)

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

/-- On integer powers of the unit `T` in `H[1/T]`, `localizedEval₂` evaluates `T ^ k` to `t ^ k`. -/
@[simp] theorem localizedEval₂_T_zpow (k : ℤ) :
    localizedEval₂ f hf t ht htinv
        (((IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit ^ k : Aˣ) : A) =
      ((t ^ k : Kˣ) : K) := by
  have hu : Units.map (localizedEval₂ (A := A) f hf t ht htinv).toMonoidHom
      (IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit = t := by
    ext
    simp
  have hmap := congr_arg Units.val <|
    (Units.map (localizedEval₂ (A := A) f hf t ht htinv).toMonoidHom).map_zpow
      (IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit k
  rw [hu] at hmap
  simpa only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass] using hmap

omit [CompleteSpace K] in
include hf ht htinv in
/-- For every `x ∈ H[1/T]`, the norms of the terms in the bilateral series
`∑_{m ∈ ℤ} f(localizedCoeff p x m) * t ^ m` are summable over `ℤ`. -/
theorem summable_norm_localizedEval₂ (x : A) :
    Summable fun m : ℤ ↦ ‖f (localizedCoeff p x m) * ((t ^ m : Kˣ) : K)‖ := by
  obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj (T : AnnularRing p) x
  have hshift : Summable fun m : ℤ ↦
      ‖f (a.coeff (m + k)) * ((t ^ (m + k : ℤ) : Kˣ) : K)‖ * ‖((t ^ (-(k : ℤ)) : Kˣ) : K)‖ :=
    ((Equiv.addRight (k : ℤ)).summable_iff.mpr
      (summable_norm_eval₂ f hf t ht htinv a)).mul_right _
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun m ↦ ?_) hshift
  have ht_eq : ((t ^ m : Kˣ) : K) =
      ((t ^ (m + k : ℤ) : Kˣ) : K) * ((t ^ (-(k : ℤ)) : Kˣ) : K) := by
    rw [← Units.val_mul, ← zpow_add, add_neg_cancel_right]
  rw [localizedCoeff_eq_of_mul_pow ha m, ht_eq, ← mul_assoc]
  exact norm_mul_le _ _

/-- For every `x ∈ H[1/T]`, the bilateral series `∑_{m ∈ ℤ} f(localizedCoeff p x m) * t ^ m`
converges to `localizedEval₂ x`. -/
theorem hasSum_localizedEval₂ (x : A) :
    HasSum (fun m : ℤ ↦ f (localizedCoeff p x m) * ((t ^ m : Kˣ) : K))
      (localizedEval₂ f hf t ht htinv x) := by
  obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj (T : AnnularRing p) x
  set u : Aˣ := (IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit
  have hx_eq : x = algebraMap (AnnularRing p) A a * ((u ^ (-(k : ℤ)) : Aˣ) : A) := by
    rw [mul_comm]
    refine (T_zpow_neg_mul_eq_iff (p := p) (-(k : ℤ)) x _).mp ?_
    rw [neg_neg, zpow_natCast, Units.val_pow_eq_pow_val,
      (IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit_spec, mul_comm, ha]
  have hx : localizedEval₂ f hf t ht htinv x =
      eval₂ f hf t ht htinv a * ((t ^ (-(k : ℤ)) : Kˣ) : K) := by
    rw [hx_eq, map_mul, localizedEval₂_algebraMap, localizedEval₂_T_zpow]
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

/-- Shared power-decay estimate on `T ^ N H` from an arbitrary uniform bound on `eval₂` over `H`. -/
private theorem norm_localizedEval₂_le_of_mem_awayNhd_of_bound {M : ℝ}
    (hM : ∀ a : AnnularRing p, ‖eval₂ f hf t ht htinv a‖ ≤ M) {N : ℕ} {x : A}
    (hx : x ∈ Huber.awayNhd (T : AnnularRing p) A N) :
    ‖localizedEval₂ f hf t ht htinv x‖ ≤ M * ‖(t : K)‖ ^ N := by
  obtain ⟨a, rfl⟩ := Huber.mem_awayNhd.mp hx
  rcases eq_or_ne N 0 with rfl | hN
  · simpa using hM a
  · rw [localizedEval₂_algebraMap, map_mul, map_pow, eval₂_T]
    calc ‖(t : K) ^ N * eval₂ f hf t ht htinv a‖
        ≤ ‖(t : K) ^ N‖ * ‖eval₂ f hf t ht htinv a‖ := norm_mul_le _ _
      _ ≤ ‖(t : K)‖ ^ N * M :=
          mul_le_mul (norm_pow_le' _ (Nat.pos_of_ne_zero hN)) (hM a) (norm_nonneg _)
            (pow_nonneg (norm_nonneg _) _)
      _ = M * ‖(t : K)‖ ^ N := mul_comm _ _

/-- On the basic `T`-adic neighbourhood `T ^ N H`, the ultrametric evaluation `localizedEval₂` is
bounded by `C * ‖t‖ ^ N`. -/
theorem norm_localizedEval₂_le_of_mem_awayNhd [IsUltrametricDist K] {C : ℝ}
    (hC : ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖) {N : ℕ} {x : A}
    (hx : x ∈ Huber.awayNhd (T : AnnularRing p) A N) :
    ‖localizedEval₂ f hf t ht htinv x‖ ≤ C * ‖(t : K)‖ ^ N :=
  norm_localizedEval₂_le_of_mem_awayNhd_of_bound f hf t ht htinv
    (norm_eval₂_le f hf t ht htinv hC) hx

/-- Every annulus evaluation `H[1/T] →+* K` is continuous for any `T`-adic topology on `H[1/T]`
whose neighbourhoods of zero have basis `T ^ n H`. -/
theorem continuous_localizedEval₂ [TopologicalSpace A] [IsTopologicalAddGroup A]
    (hb : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦
      (Huber.awayNhd (T : AnnularRing p) A n : Set A)) :
    Continuous (localizedEval₂ f hf t ht htinv (A := A)) := by
  obtain ⟨M, _, hM⟩ := exists_norm_eval₂_le f hf t ht htinv
  refine continuous_of_continuousAt_zero (localizedEval₂ f hf t ht htinv).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
  intro ε hε
  have hlim : Tendsto (fun N : ℕ ↦ M * ‖(t : K)‖ ^ N) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) ht).const_mul M
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  filter_upwards [hb.mem_of_mem (i := N) trivial] with x hx
  rw [dist_zero_right, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
  exact (norm_localizedEval₂_le_of_mem_awayNhd_of_bound f hf t ht htinv hM hx).trans_lt hN

/-- **Uniqueness on `H[1/T]`**: any `T`-adically continuous ring homomorphism `ψ : H[1/T] →+* K`
that agrees with `f` on `ℤ_p` and sends `T` to `t` equals `localizedEval₂ f hf t ht htinv`. -/
theorem eq_localizedEval₂_of_continuous [TopologicalSpace A]
    (hb : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦
      (Huber.awayNhd (T : AnnularRing p) A n : Set A))
    (ψ : A →+* K) (hψ : Continuous ψ)
    (hψ_alg : ∀ c : ℤ_[p],
      ψ (algebraMap (AnnularRing p) A (algebraMap ℤ_[p] (AnnularRing p) c)) = f c)
    (hψ_T : ψ (algebraMap (AnnularRing p) A T) = (t : K)) :
    ψ = localizedEval₂ f hf t ht htinv := by
  have h0 : ContinuousAt ψ 0 := hψ.continuousAt
  rw [ContinuousAt, map_zero] at h0
  obtain ⟨N, -, hN⟩ := hb.mem_iff.mp (h0 (Metric.ball_mem_nhds 0 zero_lt_one))
  have hcomp : ψ.comp (algebraMap (AnnularRing p) A) = eval₂ f hf t ht htinv := by
    refine eq_eval₂_of_bound f hf t ht htinv (ψ.comp (algebraMap (AnnularRing p) A))
      (B := ‖((t ^ (-(N : ℤ)) : Kˣ) : K)‖) (fun a ↦ ?_) hψ_alg hψ_T
    have ha_mem :
        algebraMap (AnnularRing p) A (T ^ N * a) ∈ Huber.awayNhd (T : AnnularRing p) A N :=
      Huber.mem_awayNhd.mpr ⟨a, rfl⟩
    have hball : ‖ψ (algebraMap (AnnularRing p) A (T ^ N * a))‖ < 1 := by
      simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] using hN ha_mem
    have hmul : ψ (algebraMap (AnnularRing p) A a) =
        ((t ^ (-(N : ℤ)) : Kˣ) : K) * ψ (algebraMap (AnnularRing p) A (T ^ N * a)) := by
      rw [map_mul, map_pow, map_mul, map_pow, hψ_T, ← Units.val_pow_eq_pow_val,
        ← mul_assoc, ← Units.val_mul, zpow_neg, zpow_natCast, inv_mul_cancel, Units.val_one,
        one_mul]
    rw [RingHom.comp_apply, hmul]
    exact (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hball.le)
  refine (IsLocalization.Away.liftNoncomm_unique (T : AnnularRing p) _ _ fun a ↦ ?_).symm
  exact DFunLike.congr_fun hcomp a

end LocalizedEval₂

end Eval₂

/-! ### `ℤ_p`-algebra evaluations under `[IsBoundedSMul ℤ_[p] K]` -/

section EvalAlgHom

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NormedRing K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [CompleteSpace K]

/-- The `ℤ_p`-algebra evaluation `H →ₐ[ℤ_[p]] K` at a unit `t : Kˣ` with `‖t‖ < 1` and
`‖t⁻¹‖ < p`. -/
def eval (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) :
    AnnularRing p →ₐ[ℤ_[p]] K :=
  { eval₂ (algebraMap ℤ_[p] K) TauCeti.exists_norm_algebraMap_le_of_isBoundedSMul t ht htinv with
    commutes' :=
      eval₂_algebraMap (algebraMap ℤ_[p] K) TauCeti.exists_norm_algebraMap_le_of_isBoundedSMul t ht
        htinv }

theorem eval_toRingHom (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p)
    (hf : ∃ C : ℝ, ∀ a : ℤ_[p], ‖algebraMap ℤ_[p] K a‖ ≤ C * ‖a‖) :
    (eval t ht htinv).toRingHom = eval₂ (algebraMap ℤ_[p] K) hf t ht htinv := (rfl)

theorem eval_apply (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p)
    (x : AnnularRing p) :
    eval t ht htinv x = ∑' m : ℤ, algebraMap ℤ_[p] K (x.coeff m) * ((t ^ m : Kˣ) : K) := (rfl)

@[simp] theorem eval_T (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) :
    eval t ht htinv T = (t : K) :=
  eval₂_T (algebraMap ℤ_[p] K) TauCeti.exists_norm_algebraMap_le_of_isBoundedSMul t ht htinv

@[simp] theorem eval_U (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) :
    eval t ht htinv U = (p : K) * ((t⁻¹ : Kˣ) : K) :=
  eval₂_U (algebraMap ℤ_[p] K) TauCeti.exists_norm_algebraMap_le_of_isBoundedSMul t ht htinv

/-- The `ℤ_p`-algebra evaluation `H[1/T] →ₐ[ℤ_[p]] K` at a unit `t : Kˣ` with `‖t‖ < 1` and
`‖t⁻¹‖ < p`. -/
def localizedEvalAlgHom {A : Type*} [CommRing A] [Algebra (AnnularRing p) A]
    [IsLocalization.Away (T : AnnularRing p) A] [Algebra ℤ_[p] A]
    (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) : A →ₐ[ℤ_[p]] K :=
  { localizedEval₂ (algebraMap ℤ_[p] K) TauCeti.exists_norm_algebraMap_le_of_isBoundedSMul t ht
      htinv with
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
  localizedEval₂_algebraMap (algebraMap ℤ_[p] K) TauCeti.exists_norm_algebraMap_le_of_isBoundedSMul
    t ht htinv a

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

end LocalizedEvalAt

end EvalAt

end TauCeti.AnnularRing
