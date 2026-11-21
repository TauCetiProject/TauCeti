/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Primitive.Basic
public import TauCeti.RingTheory.PowerSeries.Radius

import TauCeti.Analysis.Normed.Field.NatCast
import TauCeti.RingTheory.MvPowerSeries.Primitive.GaussNorm
import TauCeti.RingTheory.PowerSeries.OpenDisc.Basic

/-!
# Convergence of termwise primitives

Integration divides the coefficient at degree `n` by `n + 1` and shifts it up one degree.
The denominators grow at most polynomially in norm, so they are absorbed by shrinking a
closed disc by any positive amount. Thus the open radius of convergence is unchanged, and
one can integrate both convergent open-disc series and overconvergent series termwise.
Nevertheless, when `0 < ‖(p : K)‖ < 1` for a natural number `p`, the lacunary series
`∑ p^k X^(p^k - 1)` is restricted at radius one but no primitive is restricted there.

See A. Besser, *Heidelberg lectures on Coleman integration*, §1.3.2, and
J. S. Balakrishnan, R. W. Bradshaw and K. S. Kedlaya, *Explicit Coleman integration for
hyperelliptic curves*, §2, Remark 2, for the radius margin in this argument.
-/

public section

open Filter
open scoped ENNReal NNReal Topology

namespace PowerSeries

variable {K : Type*} [NormedField K] [CharZero K]

/-- Termwise integration preserves the radius of convergence, including radius `0` and `∞`. -/
@[simp]
theorem radius_primitive (f : K⟦X⟧) : (primitive f).radius = f.radius := by
  apply le_antisymm <;> refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  · obtain ⟨s, hrs, hsf⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
    have hu : (primitive f).OnOpenDisc (s : ℝ) := by
      refine onOpenDisc_iff.mpr fun t ht hts ↦ ?_
      have he : ‖t‖ₑ < (s : ℝ≥0∞) := by
        rw [Real.eNorm_eq_ofReal ht.le, ← ENNReal.ofReal_coe_nnreal]
        exact (ENNReal.ofReal_lt_ofReal_iff (ht.trans hts)).mpr hts
      exact isRestricted_of_lt_radius (he.trans hsf)
    have hd := hu.derivative.isRestricted (r := (r : ℝ)) (by simpa using hrs)
    simpa using le_radius_of_isRestricted hd
  · obtain ⟨s, hrs, hsf⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
    have hf := isRestricted_of_lt_radius (r := (s : ℝ)) (f := f) (by simpa using hsf)
    have hrs' : (r : ℝ) < (s : ℝ) := by simpa using hrs
    have hEq : MvPowerSeries.primitive () f = primitive f :=
      eq_primitive_iff.mpr ⟨MvPowerSeries.pderiv_primitive () f, by
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_def (s := 0) (by simp)]
        exact MvPowerSeries.coeff_primitive_of_eq_zero () f (by simp)⟩
    have hprim := MvPowerSeries.IsRestricted.primitive (i := ()) (fun _ ↦ r.coe_nonneg)
      (fun _ ↦ hrs'.le) hrs' hf
    rw [hEq] at hprim
    simpa using le_radius_of_isRestricted (r := (r : ℝ)) (f := primitive f) hprim

/-- Gauss norm bound for a primitive on a smaller closed disc. The factor is the supremum of
`r^(n+1) ‖1/(n+1)‖ / ρ^n`, independent of the series being integrated. -/
theorem gaussNorm_primitive_le (f : K⟦X⟧) {r ρ : ℝ≥0} (hr : r < ρ)
    (hf : f.HasGaussNorm norm (ρ : ℝ)) :
    (primitive f).gaussNorm norm (r : ℝ) ≤
      (⨆ n : ℕ, ‖((n : K) + 1)⁻¹‖ * (r : ℝ) ^ (n + 1) / (ρ : ℝ) ^ n) *
        f.gaussNorm norm (ρ : ℝ) := by
  have hρ : 0 < (ρ : ℝ) := r.coe_nonneg.trans_lt (NNReal.coe_lt_coe.mpr hr)
  let b (n : ℕ) := ‖((n : K) + 1)⁻¹‖ * (r : ℝ) ^ (n + 1) / (ρ : ℝ) ^ n
  have hb (n : ℕ) : b n = (ρ : ℝ) * (‖((n + 1 : ℕ) : K)⁻¹‖ * ((r : ℝ) / ρ) ^ (n + 1)) := by
    dsimp [b]
    rw [Nat.cast_succ, div_pow, pow_succ (ρ : ℝ)]
    field_simp
  have hlim : Tendsto b atTop (𝓝 0) := by
    rw [funext hb]
    have ht := NormedField.tendsto_norm_inv_natCast_mul_pow K
      (div_nonneg r.coe_nonneg hρ.le) ((div_lt_one hρ).mpr (NNReal.coe_lt_coe.mpr hr))
    simpa only [Function.comp_def, mul_zero] using
      (ht.comp (tendsto_add_atTop_nat 1)).const_mul (ρ : ℝ)
  have hbd : BddAbove (Set.range b) :=
    (hlim.mono_left Nat.cofinite_eq_atTop.le).bddAbove_range_of_cofinite
  rw [gaussNorm_eq]
  refine ciSup_le fun n ↦ ?_
  cases n with
  | zero =>
    simp only [coeff_zero_primitive, norm_zero, zero_mul]
    exact mul_nonneg ((by positivity : 0 ≤ b 0).trans (le_ciSup hbd 0))
      (gaussNorm_nonneg _ _ _ norm_nonneg)
  | succ n =>
    rw [coeff_succ_primitive, Rat.smul_def, norm_mul]
    push_cast
    calc ‖((n : K) + 1)⁻¹‖ * ‖coeff n f‖ * (r : ℝ) ^ (n + 1) =
        b n * (‖coeff n f‖ * (ρ : ℝ) ^ n) := by
          dsimp [b]
          field_simp
      _ ≤ (⨆ n, b n) * f.gaussNorm norm (ρ : ℝ) :=
        mul_le_mul (le_ciSup hbd n) (le_gaussNorm _ _ _ hf n) (by positivity)
          ((by positivity : 0 ≤ b n).trans (le_ciSup hbd n))

omit [CharZero K] in
/-- The lacunary series `∑ p^k X^(p^k - 1)` is restricted at radius one when `0 < ‖p‖ < 1`.
Every primitive has coefficient one at degree `p^k`, so none is restricted at radius one. -/
theorem exists_isRestricted_not_derivative {p : ℕ} (hp : (p : K) ≠ 0) (hpK : ‖(p : K)‖ < 1) :
    ∃ f : K⟦X⟧, (∀ k : ℕ, coeff (p ^ k - 1) f = (p : K) ^ k) ∧
      (∀ n ∉ Set.range (fun k : ℕ ↦ p ^ k - 1), coeff n f = 0) ∧
      f.IsRestricted 1 ∧ ∀ g : K⟦X⟧, g.IsRestricted 1 → d⁄dX g ≠ f := by
  classical
  have hp₀ : p ≠ 0 := by rintro rfl; simp at hp
  have hp₁ : 1 < p := by
    have hne : p ≠ 1 := by rintro rfl; simp at hpK
    omega
  let e (k : ℕ) := p ^ k - 1
  have hpos (k : ℕ) : 0 < p ^ k := pow_pos (Nat.pos_of_ne_zero hp₀) _
  have he (k : ℕ) : e k + 1 = p ^ k := Nat.sub_add_cancel (hpos k)
  have hinj : Function.Injective e := fun i j hij ↦
    (pow_right_strictMono₀ hp₁).injective (by rw [← he i, ← he j, hij])
  let a := Function.extend e (fun k ↦ (p : K) ^ k) (fun _ ↦ 0)
  have ha (k : ℕ) : a (e k) = (p : K) ^ k := hinj.extend_apply _ _ _
  have ha₀ (n : ℕ) (hn : n ∉ Set.range e) : a n = 0 := Function.extend_apply' _ _ _ hn
  refine ⟨mk a, fun k ↦ (coeff_mk _ _).trans (ha k),
    fun n hn ↦ (coeff_mk _ _).trans (ha₀ n hn), ?_, ?_⟩
  · simp only [isRestricted_iff, coeff_mk, one_pow, mul_one]
    refine tendsto_order.2 ⟨fun x hx ↦ .of_forall fun n ↦ hx.trans_le (norm_nonneg _), ?_⟩
    intro x hx
    have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (p : K)) hpK
    have hfin : {k : ℕ | ¬ ‖(p : K)‖ ^ k < x}.Finite :=
      eventually_cofinite.mp ((hlim.eventually_lt_const hx).filter_mono Nat.cofinite_eq_atTop.le)
    filter_upwards [(hfin.image e).eventually_cofinite_notMem] with n hn
    by_cases hr : ∃ k, e k = n
    · obtain ⟨k, rfl⟩ := hr
      rw [ha, norm_pow]
      by_contra hk
      exact hn ⟨k, hk, rfl⟩
    · simpa [ha₀ n hr] using hx
  · intro g hg hD
    have hc (k : ℕ) : coeff (p ^ k) g = 1 := by
      have h := congrArg (coeff (e k)) hD
      rw [coeff_derivative, coeff_mk, ha] at h
      have hcast : (e k : K) + 1 = (p : K) ^ k := by
        simpa using congrArg (Nat.cast : ℕ → K) (he k)
      rw [he k, hcast] at h
      exact mul_right_cancel₀ (pow_ne_zero k hp)
        (h.trans (one_mul _).symm)
    have hlim := ((isRestricted_iff' 1 g).mp hg).comp
      (pow_right_strictMono₀ hp₁).injective.nat_tendsto_atTop
    simp [Function.comp_def, hc] at hlim

end PowerSeries
