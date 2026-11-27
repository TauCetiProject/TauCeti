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
import Mathlib.RingTheory.PowerSeries.Trunc
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
* `TauCeti.AnnularRing.evalAlgHom` and `TauCeti.AnnularRing.localizedEvalAlgHom` as
  `ℤ_[p]`-algebra homomorphisms when `[Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K]`.
* `TauCeti.AnnularRing.eval` and `TauCeti.AnnularRing.localizedEval` for any complete normed
  division ring extension `K` of `ℚ_[p]` (such as `ℂ_[p]`) and any `t : K` with `p⁻¹ < ‖t‖ < 1`,
  while `ℚ_[p]` itself contains no points of the open annulus
  (`TauCeti.AnnularRing.not_exists_padic_annulus`).

Every annulus evaluation is continuous for any `T`-adic topology on `H[1/T]` whose neighbourhoods
of zero have basis `T ^ n H` (`TauCeti.AnnularRing.continuous_localizedEval₂`), and is the unique
continuous ring homomorphism extending `f` and sending `T ↦ t`
(`TauCeti.AnnularRing.eq_localizedEval₂_of_continuous`).

## Main definitions

* `TauCeti.AnnularRing.eval₂`, `TauCeti.AnnularRing.localizedEval₂`: evaluation ring homomorphisms
  on `H` and `H[1/T]` into any complete normed ring `K`.
* `TauCeti.AnnularRing.evalAlgHom`, `TauCeti.AnnularRing.localizedEvalAlgHom`: `ℤ_[p]`-algebra
  evaluations under `[Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K]`.
* `TauCeti.AnnularRing.eval`, `TauCeti.AnnularRing.localizedEval`: evaluations at `t : K` with
  `p⁻¹ < ‖t‖ < 1` in any complete normed division ring `K` over `ℚ_[p]`.

## Main results

* `TauCeti.AnnularRing.summable_norm_eval₂`, `TauCeti.AnnularRing.summable_eval₂`,
  `TauCeti.AnnularRing.summable_norm_localizedEval₂`: absolute convergence of the bilateral
  evaluation series on `H` and `H[1/T]`.
* `TauCeti.AnnularRing.hasSum_eval₂`, `TauCeti.AnnularRing.hasSum_localizedEval₂`: bilateral series
  expansions of evaluations on `H` and `H[1/T]`.
* `TauCeti.AnnularRing.eval₂_ofPowerSeriesT`, `TauCeti.AnnularRing.eval₂_ofPowerSeriesU`:
  evaluations of power series in `T` and `U = p / T`.
* `TauCeti.AnnularRing.eq_eval₂_of_bound`, `TauCeti.AnnularRing.eq_localizedEval₂_of_continuous`:
  uniqueness of bounded evaluations on `H` and `T`-adically continuous evaluations on `H[1/T]`.
* `TauCeti.AnnularRing.evalAlgHom_toRingHom`, `TauCeti.AnnularRing.localizedEvalAlgHom_toRingHom`,
  `TauCeti.AnnularRing.eval_eq_eval₂`, `TauCeti.AnnularRing.localizedEval_eq_localizedEval₂`:
  comparison lemmas relating the specialized evaluations to `eval₂` and `localizedEval₂`.
* `TauCeti.AnnularRing.continuous_localizedEval₂`: continuity for the `T`-adic topology on `H[1/T]`.
* `TauCeti.AnnularRing.not_exists_padic_annulus`: `ℚ_[p]` has no points in the open annulus.

## References

* R. Liu, D. Wan and L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J.
  166 (2017), §§2–3.
-/

public noncomputable section

open Filter Topology

namespace TauCeti.AnnularRing

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
private theorem norm_coeff_mul_le (x : AnnularRing p) {r₀ r₁ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁)
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
          pow_le_pow_left₀ (div_nonneg hr₁ (Nat.cast_pos.mpr (Fact.out : p.Prime).pos).le)
            (le_max_right _ _) _

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

/-- The joint geometric ratio `max ‖t‖ (‖t⁻¹‖ / p)` on the open annulus lies in `[0, 1)`. -/
private theorem annulus_radius_bounds {K : Type*} [SeminormedRing K] {t : Kˣ}
    (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) :
    0 ≤ max ‖(t : K)‖ (‖((t⁻¹ : Kˣ) : K)‖ / p) ∧
      max ‖(t : K)‖ (‖((t⁻¹ : Kˣ) : K)‖ / p) < 1 :=
  ⟨le_trans (norm_nonneg _) (le_max_left _ _),
    max_lt ht ((div_lt_one (Nat.cast_pos.mpr (Fact.out : p.Prime).pos)).2 htinv)⟩

/-- The norms `‖f(x.coeff m) * t ^ m‖` are summable over `ℤ` whenever `f` is bounded and
`‖t‖ < 1`, `‖t⁻¹‖ < p`. -/
theorem summable_norm_eval₂ {K : Type*} [SeminormedRing K] (f : ℤ_[p] →+* K)
    (hf : ∃ C : ℝ, ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖)
    (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) (x : AnnularRing p) :
    Summable fun m : ℤ ↦ ‖f (x.coeff m) * ((t ^ m : Kˣ) : K)‖ := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨hρ0, hρ1⟩ := annulus_radius_bounds (p := p) ht htinv
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
  obtain ⟨hρ0, hρ1⟩ := annulus_radius_bounds (p := p) ht htinv
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC0 fun m ↦ ?_
  exact (norm_term_le hC t x m).trans (mul_le_of_le_one_right hC0 (pow_le_one₀ hρ0 hρ1.le))

/-- Uniform geometric-series bound on `eval₂` over `H` without ultrametricity. -/
private theorem exists_norm_eval₂_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : AnnularRing p, ‖eval₂ f hf t ht htinv a‖ ≤ M := by
  obtain ⟨C, hC⟩ := hf
  have hC0 : 0 ≤ C := bound_nonneg hC
  obtain ⟨hρ0, hρ1⟩ := annulus_radius_bounds (p := p) ht htinv
  have hgeom := (summable_pow_natAbs hρ0 hρ1).mul_left C
  refine ⟨∑' m : ℤ, C * (max ‖(t : K)‖ (‖((t⁻¹ : Kˣ) : K)‖ / p)) ^ m.natAbs,
    tsum_nonneg fun m ↦ mul_nonneg hC0 (pow_nonneg hρ0 _),
    fun a ↦ (norm_tsum_le_tsum_norm (summable_norm_eval₂ f ⟨C, hC⟩ t ht htinv a)).trans <|
      (summable_norm_eval₂ f ⟨C, hC⟩ t ht htinv a).tsum_le_tsum (norm_term_le hC t a) hgeom⟩

omit [CompleteSpace K] in
/-- Any ring homomorphism `φ : H →+* K` sending `T` to `t` sends `U` to `p * t⁻¹`. -/
private theorem map_U_of_map_T {t : Kˣ} (φ : AnnularRing p →+* K) (hφ_T : φ T = (t : K)) :
    φ U = (p : K) * ((t⁻¹ : Kˣ) : K) := by
  have hTU : φ T * φ U = (p : K) := by rw [← map_mul, T_mul_U, map_natCast]
  calc φ U = ((t⁻¹ : Kˣ) : K) * ((t : K) * φ U) := by
        rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    _ = ((t⁻¹ : Kˣ) : K) * (p : K) := by rw [← hφ_T, hTU]
    _ = (p : K) * ((t⁻¹ : Kˣ) : K) := (Nat.cast_commute p _).symm.eq

/-- Degree-`N` polynomial truncation of `x ∈ H` in its normal form `f₀(T) + U g₀(U)`. -/
private def truncPart (x : AnnularRing p) (N : ℕ) : AnnularRing p :=
  ofPowerSeriesT ((normalForm.symm x).1.trunc (N + 1) : PowerSeries ℤ_[p]) +
    U * ofPowerSeriesU ((normalForm.symm x).2.trunc N : PowerSeries ℤ_[p])

/-- Shifted positive-degree tail of `x ∈ H` beyond `T ^ (N + 1)`. -/
private def truncTailPos (x : AnnularRing p) (N : ℕ) : AnnularRing p :=
  ofPowerSeriesT (PowerSeries.mk fun i ↦ PowerSeries.coeff (i + (N + 1)) (normalForm.symm x).1)

/-- Shifted negative-degree tail of `x ∈ H` beyond `U ^ (N + 1)`. -/
private def truncTailNeg (x : AnnularRing p) (N : ℕ) : AnnularRing p :=
  ofPowerSeriesU (PowerSeries.mk fun i ↦ PowerSeries.coeff (i + N) (normalForm.symm x).2)

/-- Truncation decomposition `x = truncPart x N + T ^ (N + 1) * truncTailPos x N +
U ^ (N + 1) * truncTailNeg x N`. -/
private theorem eq_truncPart_add_tail (x : AnnularRing p) (N : ℕ) :
    x = truncPart x N + T ^ (N + 1) * truncTailPos x N + U ^ (N + 1) * truncTailNeg x N := by
  set f₀ := (normalForm.symm x).1
  set g₀ := (normalForm.symm x).2
  have hf_split : ofPowerSeriesT f₀ =
      T ^ (N + 1) * truncTailPos x N + ofPowerSeriesT (f₀.trunc (N + 1) : PowerSeries ℤ_[p]) := by
    conv_lhs => rw [PowerSeries.eq_X_pow_mul_shift_add_trunc (N + 1) f₀]
    simp only [map_add, map_mul, map_pow, ofPowerSeriesT_X, truncTailPos, f₀]
  have hg_split : U * ofPowerSeriesU g₀ =
      U ^ (N + 1) * truncTailNeg x N + U * ofPowerSeriesU (g₀.trunc N : PowerSeries ℤ_[p]) := by
    conv_lhs => rw [PowerSeries.eq_X_pow_mul_shift_add_trunc N g₀]
    simp only [map_add, map_mul, map_pow, ofPowerSeriesU_X, mul_add, ← mul_assoc, ← pow_succ',
      truncTailNeg, g₀]
  calc x = normalForm (f₀, g₀) := (normalForm.apply_symm_apply x).symm
    _ = ofPowerSeriesT f₀ + U * ofPowerSeriesU g₀ := normalForm_apply f₀ g₀
    _ = truncPart x N + T ^ (N + 1) * truncTailPos x N + U ^ (N + 1) * truncTailNeg x N := by
      rw [hf_split, hg_split]
      dsimp only [truncPart, f₀, g₀]
      abel

omit [CompleteSpace K] in
/-- Two ring homomorphisms `H →+* K` that agree on `ℤ_[p]` and on `g X` agree on polynomial
images under an `AlgHom` `g : ℤ_[p]⟦X⟧ →ₐ[ℤ_[p]] H`. -/
private theorem comp_ofPowerSeries_eq {g : PowerSeries ℤ_[p] →ₐ[ℤ_[p]] AnnularRing p}
    (φ ψ : AnnularRing p →+* K)
    (h_alg : ∀ c : ℤ_[p],
      φ (algebraMap ℤ_[p] (AnnularRing p) c) = ψ (algebraMap ℤ_[p] (AnnularRing p) c))
    (h_X : φ (g PowerSeries.X) = ψ (g PowerSeries.X)) :
    φ.comp (g.toRingHom.comp Polynomial.coeToPowerSeries.ringHom) =
      ψ.comp (g.toRingHom.comp Polynomial.coeToPowerSeries.ringHom) := by
  refine Polynomial.ringHom_ext' (RingHom.ext fun c ↦ ?_) ?_
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, PowerSeries.C_eq_algebraMap,
      AlgHom.commutes, h_alg]
  · simp [Polynomial.coeToPowerSeries.ringHom_apply, h_X]

/-- Any ring homomorphism `φ : H →+* K` extending `f` and sending `T ↦ t` agrees with `eval₂` on
every truncation `truncPart x N`. -/
private theorem map_truncPart_eq (φ : AnnularRing p →+* K)
    (hφ_alg : ∀ c : ℤ_[p], φ (algebraMap ℤ_[p] (AnnularRing p) c) = f c)
    (hφ_T : φ T = (t : K)) (hφ_U : φ U = (p : K) * ((t⁻¹ : Kˣ) : K))
    (x : AnnularRing p) (N : ℕ) :
    φ (truncPart x N) = eval₂ f hf t ht htinv (truncPart x N) := by
  have h_alg (c : ℤ_[p]) : φ (algebraMap ℤ_[p] (AnnularRing p) c) =
      eval₂ f hf t ht htinv (algebraMap ℤ_[p] (AnnularRing p) c) := by
    rw [hφ_alg, eval₂_algebraMap]
  have hT := DFunLike.congr_fun
    (comp_ofPowerSeries_eq (g := ofPowerSeriesT) φ (eval₂ f hf t ht htinv) h_alg
      (by rw [ofPowerSeriesT_X, hφ_T, eval₂_T]))
    ((normalForm.symm x).1.trunc (N + 1))
  have hU := DFunLike.congr_fun
    (comp_ofPowerSeries_eq (g := ofPowerSeriesU) φ (eval₂ f hf t ht htinv) h_alg
      (by rw [ofPowerSeriesU_X, hφ_U, eval₂_U]))
    ((normalForm.symm x).2.trunc N)
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Polynomial.coeToPowerSeries.ringHom_apply] at hT hU
  simp only [truncPart, map_add, map_mul, hφ_U, eval₂_U, hT, hU]

omit [CompleteSpace K] in
/-- Power-decay estimate on `T ^ (N + 1) * y` for any ring homomorphism sending `T ↦ t`. -/
private theorem norm_map_T_pow_mul_le {t : Kˣ} (ψ : AnnularRing p →+* K) (hψ_T : ψ T = (t : K))
    (N : ℕ) {y : AnnularRing p} {R : ℝ} (hR : ‖ψ y‖ ≤ R) :
    ‖ψ (T ^ (N + 1) * y)‖ ≤ ‖(t : K)‖ ^ (N + 1) * R := by
  rw [map_mul, map_pow, hψ_T]
  exact (norm_mul_le _ _).trans
    (mul_le_mul (norm_pow_le' _ (Nat.succ_pos N)) hR (norm_nonneg _)
      (pow_nonneg (norm_nonneg _) _))

omit [CompleteSpace K] in
/-- Power-decay estimate on `U ^ (N + 1) * y` for any ring homomorphism sending `U ↦ p * t⁻¹`. -/
private theorem norm_map_U_pow_mul_le {C : ℝ} (hC : ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖) {t : Kˣ}
    (ψ : AnnularRing p →+* K) (hψ_U : ψ U = (p : K) * ((t⁻¹ : Kˣ) : K))
    (N : ℕ) {y : AnnularRing p} {R : ℝ} (hR : ‖ψ y‖ ≤ R) :
    ‖ψ (U ^ (N + 1) * y)‖ ≤ C * (‖((t⁻¹ : Kˣ) : K)‖ / p) ^ (N + 1) * R := by
  have hC0 : 0 ≤ C := bound_nonneg hC
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

/-- Per-degree approximation estimate between `eval₂` and any bounded homomorphism `φ` agreeing
with `f` on `ℤ_[p]` and sending `T ↦ t`. -/
private theorem norm_sub_eval₂_le_of_bound {C B M : ℝ}
    (hC : ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖)
    (φ : AnnularRing p →+* K) (hφ_bdd : ∀ x : AnnularRing p, ‖φ x‖ ≤ B)
    (hM : ∀ x : AnnularRing p, ‖eval₂ f ⟨C, hC⟩ t ht htinv x‖ ≤ M)
    (hφ_alg : ∀ c : ℤ_[p], φ (algebraMap ℤ_[p] (AnnularRing p) c) = f c)
    (hφ_T : φ T = (t : K)) (x : AnnularRing p) (N : ℕ) :
    ‖φ x - eval₂ f ⟨C, hC⟩ t ht htinv x‖ ≤
      (‖(t : K)‖ ^ (N + 1) + C * (‖((t⁻¹ : Kˣ) : K)‖ / p) ^ (N + 1)) * (B + M) := by
  have hφ_U : φ U = (p : K) * ((t⁻¹ : Kˣ) : K) := map_U_of_map_T φ hφ_T
  have hP := map_truncPart_eq f ⟨C, hC⟩ t ht htinv φ hφ_alg hφ_T hφ_U x N
  have hdiff : φ x - eval₂ f ⟨C, hC⟩ t ht htinv x =
      (φ (T ^ (N + 1) * truncTailPos x N) -
          eval₂ f ⟨C, hC⟩ t ht htinv (T ^ (N + 1) * truncTailPos x N)) +
        (φ (U ^ (N + 1) * truncTailNeg x N) -
          eval₂ f ⟨C, hC⟩ t ht htinv (U ^ (N + 1) * truncTailNeg x N)) := by
    conv_lhs => rw [eq_truncPart_add_tail x N]
    simp only [map_add, hP]
    abel
  have h1 := (norm_sub_le _ _).trans (add_le_add
    (norm_map_T_pow_mul_le φ hφ_T N (hφ_bdd (truncTailPos x N)))
    (norm_map_T_pow_mul_le (eval₂ f ⟨C, hC⟩ t ht htinv) (eval₂_T f ⟨C, hC⟩ t ht htinv) N
      (hM (truncTailPos x N))))
  have h2 := (norm_sub_le _ _).trans (add_le_add
    (norm_map_U_pow_mul_le f hC φ hφ_U N (hφ_bdd (truncTailNeg x N)))
    (norm_map_U_pow_mul_le f hC (eval₂ f ⟨C, hC⟩ t ht htinv) (eval₂_U f ⟨C, hC⟩ t ht htinv) N
      (hM (truncTailNeg x N))))
  rw [hdiff]
  calc ‖(φ (T ^ (N + 1) * truncTailPos x N) -
            eval₂ f ⟨C, hC⟩ t ht htinv (T ^ (N + 1) * truncTailPos x N)) +
          (φ (U ^ (N + 1) * truncTailNeg x N) -
            eval₂ f ⟨C, hC⟩ t ht htinv (U ^ (N + 1) * truncTailNeg x N))‖
      ≤ ‖φ (T ^ (N + 1) * truncTailPos x N) -
            eval₂ f ⟨C, hC⟩ t ht htinv (T ^ (N + 1) * truncTailPos x N)‖ +
          ‖φ (U ^ (N + 1) * truncTailNeg x N) -
            eval₂ f ⟨C, hC⟩ t ht htinv (U ^ (N + 1) * truncTailNeg x N)‖ :=
        norm_add_le _ _
    _ ≤ (‖(t : K)‖ ^ (N + 1) * B + ‖(t : K)‖ ^ (N + 1) * M) +
          (C * (‖((t⁻¹ : Kˣ) : K)‖ / p) ^ (N + 1) * B +
            C * (‖((t⁻¹ : Kˣ) : K)‖ / p) ^ (N + 1) * M) := add_le_add h1 h2
    _ = (‖(t : K)‖ ^ (N + 1) + C * (‖((t⁻¹ : Kˣ) : K)‖ / p) ^ (N + 1)) * (B + M) := by ring

/-- **Uniqueness on `H`**: any ring homomorphism `φ : AnnularRing p →+* K` bounded on `H` that
agrees with `f` on `ℤ_p` and sends `T` to `t` equals `eval₂ f hf t ht htinv`. -/
theorem eq_eval₂_of_bound (φ : AnnularRing p →+* K) {B : ℝ}
    (hφ_bdd : ∀ x : AnnularRing p, ‖φ x‖ ≤ B)
    (hφ_alg : ∀ c : ℤ_[p], φ (algebraMap ℤ_[p] (AnnularRing p) c) = f c)
    (hφ_T : φ T = (t : K)) :
    φ = eval₂ f hf t ht htinv := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨M, _, hM⟩ := exists_norm_eval₂_le f ⟨C, hC⟩ t ht htinv
  ext x
  have ht_lim : Tendsto (fun N : ℕ ↦ ‖(t : K)‖ ^ (N + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) ht).comp (tendsto_add_atTop_nat 1)
  have hu_lim : Tendsto (fun N : ℕ ↦ C * (‖((t⁻¹ : Kˣ) : K)‖ / p) ^ (N + 1)) atTop (𝓝 0) := by
    have hdiv : ‖((t⁻¹ : Kˣ) : K)‖ / p < 1 :=
      (div_lt_one (Nat.cast_pos.mpr (Fact.out : p.Prime).pos)).2 htinv
    simpa only [Function.comp_apply, mul_zero] using ((tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg (norm_nonneg _) (Nat.cast_pos.mpr (Fact.out : p.Prime).pos).le) hdiv).comp
      (tendsto_add_atTop_nat 1)).const_mul C
  have hlim : Tendsto
      (fun N : ℕ ↦ (‖(t : K)‖ ^ (N + 1) + C * (‖((t⁻¹ : Kˣ) : K)‖ / p) ^ (N + 1)) * (B + M))
      atTop (𝓝 0) := by
    simpa only [add_zero, zero_mul] using (ht_lim.add hu_lim).mul_const (B + M)
  have hle0 : ‖φ x - eval₂ f ⟨C, hC⟩ t ht htinv x‖ ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
      (norm_sub_eval₂_le_of_bound f t ht htinv hC φ hφ_bdd hM hφ_alg hφ_T x)
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
    refine (Units.inv_mul_eq_iff_eq_mul (u ^ (-(k : ℤ)))).mp ?_
    rw [← zpow_neg, neg_neg, zpow_natCast, Units.val_pow_eq_pow_val,
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
      rw [map_mul, map_pow, map_mul, map_pow, hψ_T, zpow_neg, zpow_natCast,
        ← Units.val_pow_eq_pow_val, Units.inv_mul_cancel_left]
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
def evalAlgHom (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) :
    AnnularRing p →ₐ[ℤ_[p]] K :=
  { eval₂ (algebraMap ℤ_[p] K) TauCeti.exists_norm_algebraMap_le_of_isBoundedSMul t ht htinv with
    commutes' :=
      eval₂_algebraMap (algebraMap ℤ_[p] K) TauCeti.exists_norm_algebraMap_le_of_isBoundedSMul t ht
        htinv }

theorem evalAlgHom_toRingHom (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p)
    (hf : ∃ C : ℝ, ∀ a : ℤ_[p], ‖algebraMap ℤ_[p] K a‖ ≤ C * ‖a‖) :
    (evalAlgHom t ht htinv).toRingHom = eval₂ (algebraMap ℤ_[p] K) hf t ht htinv := (rfl)

theorem evalAlgHom_apply (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p)
    (x : AnnularRing p) :
    evalAlgHom t ht htinv x = ∑' m : ℤ, algebraMap ℤ_[p] K (x.coeff m) * ((t ^ m : Kˣ) : K) :=
  (rfl)

@[simp] theorem evalAlgHom_T (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) :
    evalAlgHom t ht htinv T = (t : K) :=
  eval₂_T (algebraMap ℤ_[p] K) TauCeti.exists_norm_algebraMap_le_of_isBoundedSMul t ht htinv

@[simp] theorem evalAlgHom_U (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p) :
    evalAlgHom t ht htinv U = (p : K) * ((t⁻¹ : Kˣ) : K) :=
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
      evalAlgHom t ht htinv a :=
  localizedEval₂_algebraMap (algebraMap ℤ_[p] K) TauCeti.exists_norm_algebraMap_le_of_isBoundedSMul
    t ht htinv a

end EvalAlgHom

/-! ### Evaluations into complete normed division rings over `ℚ_p` -/

section Eval

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NormedDivisionRing K]

private theorem ne_zero_of_inv_p_lt {t : K} (ht₀ : (p : ℝ)⁻¹ < ‖t‖) : t ≠ 0 :=
  norm_pos_iff.mp ((inv_pos.2 (Nat.cast_pos.mpr (Fact.out : p.Prime).pos)).trans ht₀)

private theorem norm_mk0_inv_lt_p {t : K} (ht₀ : (p : ℝ)⁻¹ < ‖t‖) :
    ‖(((Units.mk0 t (ne_zero_of_inv_p_lt ht₀))⁻¹ : Kˣ) : K)‖ < p := by
  rw [Units.val_inv_eq_inv_val, Units.val_mk0, norm_inv]
  exact inv_lt_of_inv_lt₀ (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) ht₀

variable [NormedAlgebra ℚ_[p] K]

private theorem padicIntAlgebraMap_mul_mk0_zpow (c : ℤ_[p]) {t : K} (ht₀ : (p : ℝ)⁻¹ < ‖t‖)
    (m : ℤ) :
    padicIntAlgebraMap p K c * ((Units.mk0 t (ne_zero_of_inv_p_lt ht₀) ^ m : Kˣ) : K) =
      algebraMap ℚ_[p] K c * t ^ m := by
  rw [padicIntAlgebraMap_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0]

private theorem norm_padicIntAlgebraMap_le_one_mul (a : ℤ_[p]) :
    ‖padicIntAlgebraMap p K a‖ ≤ 1 * ‖a‖ := by
  rw [one_mul, norm_padicIntAlgebraMap]

variable [CompleteSpace K]

/-- **Evaluation on the annulus.** For `t` in a complete normed division ring `K` over `ℚ_p`
(such as `ℂ_[p]`) with `p⁻¹ < ‖t‖ < 1`, the ring homomorphism `∑_m d_m T ^ m ↦ ∑_m d_m t ^ m`
from the annular coefficient ring, sending `T` to `t` and `U` to `p / t`. -/
def eval (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) : AnnularRing p →+* K :=
  eval₂ (padicIntAlgebraMap p K) TauCeti.exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) ht₁ (norm_mk0_inv_lt_p ht₀)

theorem eval_eq_eval₂ (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1)
    (u : Kˣ) (hu : (u : K) = t)
    (hf : ∃ C : ℝ, ∀ a : ℤ_[p], ‖padicIntAlgebraMap p K a‖ ≤ C * ‖a‖)
    (hu₁ : ‖(u : K)‖ < 1) (huinv : ‖((u⁻¹ : Kˣ) : K)‖ < p) :
    eval t ht₀ ht₁ = eval₂ (padicIntAlgebraMap p K) hf u hu₁ huinv := by
  obtain rfl : u = Units.mk0 t (ne_zero_of_inv_p_lt ht₀) := Units.ext hu
  rfl

/-- The value of `x` at `t` is `∑_m d_m t ^ m`. -/
theorem eval_apply {t : K} (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (x : AnnularRing p) :
    eval t ht₀ ht₁ x = ∑' m : ℤ, algebraMap ℚ_[p] K (x.coeff m) * t ^ m := by
  refine (eval₂_apply (padicIntAlgebraMap p K) TauCeti.exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) ht₁ (norm_mk0_inv_lt_p ht₀) x).trans ?_
  congr 1 with m
  exact padicIntAlgebraMap_mul_mk0_zpow (x.coeff m) ht₀ m

/-- The series `∑_m d_m t ^ m` converges to the value of `x` at `t`. -/
theorem hasSum_eval {t : K} (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (x : AnnularRing p) :
    HasSum (fun m : ℤ ↦ algebraMap ℚ_[p] K (x.coeff m) * t ^ m) (eval t ht₀ ht₁ x) := by
  have h := hasSum_eval₂ (padicIntAlgebraMap p K) TauCeti.exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) ht₁ (norm_mk0_inv_lt_p ht₀) x
  exact h.congr_fun fun m ↦ (padicIntAlgebraMap_mul_mk0_zpow (x.coeff m) ht₀ m).symm

/-- Constants evaluate to themselves. -/
@[simp] theorem eval_algebraMap {t : K} (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (c : ℤ_[p]) :
    eval t ht₀ ht₁ (algebraMap ℤ_[p] (AnnularRing p) c) = algebraMap ℚ_[p] K c :=
  (eval₂_algebraMap (padicIntAlgebraMap p K) TauCeti.exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) ht₁ (norm_mk0_inv_lt_p ht₀) c).trans
    (padicIntAlgebraMap_apply c)

/-- The variable `T` evaluates to `t`. -/
@[simp] theorem eval_T {t : K} (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) :
    eval t ht₀ ht₁ T = t :=
  eval₂_T (padicIntAlgebraMap p K) TauCeti.exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) ht₁ (norm_mk0_inv_lt_p ht₀)

/-- The element `U = p / T` evaluates to `p / t`. -/
@[simp] theorem eval_U {t : K} (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) :
    eval t ht₀ ht₁ U = (p : K) / t := by
  refine (eval₂_U (padicIntAlgebraMap p K) TauCeti.exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) ht₁ (norm_mk0_inv_lt_p ht₀)).trans ?_
  rw [Units.val_inv_eq_inv_val, Units.val_mk0, div_eq_mul_inv]

/-- Every element of `H` has absolute value at most `1` at every point `t` of the open annulus
`p⁻¹ < ‖t‖ < 1`. -/
theorem norm_eval_le_one {t : K} (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (x : AnnularRing p) :
    ‖eval t ht₀ ht₁ x‖ ≤ 1 := by
  have : IsUltrametricDist K := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  exact norm_eval₂_le (padicIntAlgebraMap p K) TauCeti.exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) ht₁ (norm_mk0_inv_lt_p ht₀)
    norm_padicIntAlgebraMap_le_one_mul x

section LocalizedEval

variable {A : Type*} [CommRing A] [Algebra (AnnularRing p) A]
  [IsLocalization.Away (T : AnnularRing p) A]

/-- Evaluation `H[1/T] →+* K` at a point `t` in the open annulus `p⁻¹ < ‖t‖ < 1` of a complete
normed division ring `K` over `ℚ_[p]`. -/
def localizedEval (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) : A →+* K :=
  localizedEval₂ (padicIntAlgebraMap p K) TauCeti.exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) ht₁ (norm_mk0_inv_lt_p ht₀)

theorem localizedEval_eq_localizedEval₂ (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1)
    (u : Kˣ) (hu : (u : K) = t)
    (hf : ∃ C : ℝ, ∀ a : ℤ_[p], ‖padicIntAlgebraMap p K a‖ ≤ C * ‖a‖)
    (hu₁ : ‖(u : K)‖ < 1) (huinv : ‖((u⁻¹ : Kˣ) : K)‖ < p) :
    localizedEval (A := A) t ht₀ ht₁ =
      localizedEval₂ (padicIntAlgebraMap p K) hf u hu₁ huinv := by
  obtain rfl : u = Units.mk0 t (ne_zero_of_inv_p_lt ht₀) := Units.ext hu
  rfl

@[simp] theorem localizedEval_algebraMap (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1)
    (a : AnnularRing p) :
    localizedEval (A := A) t ht₀ ht₁ (algebraMap (AnnularRing p) A a) = eval t ht₀ ht₁ a :=
  localizedEval₂_algebraMap (padicIntAlgebraMap p K) TauCeti.exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) ht₁ (norm_mk0_inv_lt_p ht₀) a

@[simp] theorem localizedEval_T_zpow (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (k : ℤ) :
    localizedEval (A := A) t ht₀ ht₁
        (((IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit ^ k : Aˣ) : A) =
      t ^ k := by
  refine (localizedEval₂_T_zpow (A := A) (padicIntAlgebraMap p K)
    TauCeti.exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) ht₁ (norm_mk0_inv_lt_p ht₀) k).trans ?_
  rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]

theorem hasSum_localizedEval (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (x : A) :
    HasSum (fun m : ℤ ↦ algebraMap ℚ_[p] K (localizedCoeff p x m) * t ^ m)
      (localizedEval t ht₀ ht₁ x) := by
  have h := hasSum_localizedEval₂ (A := A) (padicIntAlgebraMap p K)
    TauCeti.exists_norm_padicIntAlgebraMap_le (Units.mk0 t (ne_zero_of_inv_p_lt ht₀))
    ht₁ (norm_mk0_inv_lt_p ht₀) x
  exact h.congr_fun fun m ↦ (padicIntAlgebraMap_mul_mk0_zpow (localizedCoeff p x m) ht₀ m).symm

/-- Sharp bound: every element of `T ^ N H` has norm at most `‖t‖ ^ N` under evaluation at `t`. -/
theorem norm_localizedEval_le_pow_of_mem_awayNhd (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1)
    {N : ℕ} {x : A} (hx : x ∈ Huber.awayNhd (T : AnnularRing p) A N) :
    ‖localizedEval t ht₀ ht₁ x‖ ≤ ‖t‖ ^ N := by
  have : IsUltrametricDist K := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  rw [localizedEval]
  exact (norm_localizedEval₂_le_of_mem_awayNhd (padicIntAlgebraMap p K)
    TauCeti.exists_norm_padicIntAlgebraMap_le (Units.mk0 t (ne_zero_of_inv_p_lt ht₀))
    ht₁ (norm_mk0_inv_lt_p ht₀)
    norm_padicIntAlgebraMap_le_one_mul hx).trans_eq (by simp)

/-- Evaluation at `t` is continuous for any `T`-adic topology on `H[1/T]`. -/
theorem continuous_localizedEval [TopologicalSpace A] [IsTopologicalAddGroup A]
    (hb : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦
      (Huber.awayNhd (T : AnnularRing p) A n : Set A))
    (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) :
    Continuous (localizedEval (A := A) t ht₀ ht₁) :=
  continuous_localizedEval₂ (padicIntAlgebraMap p K) TauCeti.exists_norm_padicIntAlgebraMap_le
    (Units.mk0 t (ne_zero_of_inv_p_lt ht₀)) ht₁ (norm_mk0_inv_lt_p ht₀) hb

end LocalizedEval

end Eval

/-- The open annulus `p⁻¹ < ‖t‖ < 1` has no points in `ℚ_[p]`, because the value group of `ℚ_[p]`
is `p ^ ℤ`. -/
theorem not_exists_padic_annulus (p : ℕ) [Fact (Nat.Prime p)] :
    ¬ ∃ t : ℚ_[p], (p : ℝ)⁻¹ < ‖t‖ ∧ ‖t‖ < 1 := by
  rintro ⟨t, ht₀, ht₁⟩
  rw [← zpow_zero (p : ℝ)] at ht₁
  have hle := (Padic.norm_lt_pow_iff_norm_le_pow_sub_one t 0).mp ht₁
  norm_num at hle
  linarith

end TauCeti.AnnularRing
