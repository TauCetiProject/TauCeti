/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.SpecificLimits.ProductMajorant
public import TauCeti.RingTheory.PowerSeries.Entire.Basic

/-!
# Majorants of entire power series

This file supplies the two majorants that control Coleman's spectral transform
`D(B, F)` of an entire series `F` with `F(0) = 1` along an entire series `B` with `B(0) = 0`.

**Newton majorants.** A power series `F = ∑ aⱼ Tʲ` over a normed ring with `‖a₀‖ ≤ 1` is entire
exactly when its coefficients are dominated by the partial products of a positive antitone null
sequence `ρ`:

`‖aⱼ‖ ≤ ∏ i < j, ρᵢ` (`PowerSeries.isEntire_iff_exists_newtonMajorant`).

One direction holds since `‖aⱼ‖ |r| ^ j ≤ ∏ i < j, |ρᵢ| |r|` and the factors `|ρᵢ| |r|` tend to
zero (`PowerSeries.isEntire_of_norm_coeff_le_prod`). For the other, the `j`-th roots
`‖aⱼ‖ ^ (1 / j)` of the coefficients of an entire series tend to zero
(`PowerSeries.IsEntire.tendsto_norm_coeff_rpow_inv_natCast`), and `ρᵢ` is the supremum of the
roots of index greater than `i`, plus `2⁻ⁱ` to make it positive. In terms of `v = -log ‖·‖`, the
bound says that the points `(j, v(aⱼ))` lie above the convex polygon with slopes `-log ρᵢ`, whence
the name; no valuation is needed here.

**Coleman majorants.** For a power series `B = ∑ bₘ Tᵐ` and a radius `r`, the Coleman majorant
is the supremum of the weighted coefficients of positive degree,

`β_B(r) = sup_{m ≥ 1} ‖bₘ‖ rᵐ` (`PowerSeries.colemanMajorant`),

that is, for `r ≥ 0`, the Gauss norm of `B - B(0)` at radius `r`.

If `B` is restricted at the radius `r`, the supremum is finite, so every weighted
coefficient `‖bₘ‖ rᵐ` with `m ≥ 1` is bounded by `β_B(r)`
(`PowerSeries.norm_coeff_succ_mul_pow_le_colemanMajorant`). If `B` is restricted at a radius
`s > 0`, then `β_B` is monotone on `[0, s]` and, since the constant term is omitted,
`β_B(r) ≤ (r / s) β_B(s)` for `0 ≤ r ≤ s`; so `β_B(r)` tends to zero with `r`
(`PowerSeries.tendsto_colemanMajorant`). Composed with a Newton majorant `ρ` of
`F`, the products `∏ i < k, β_B(ρᵢ)` therefore again form the coefficient bounds of an entire
series. In Coleman's construction, these products bound the coefficients of the spectral
transform `D(B, F)`, which is therefore entire.

## Main definitions

* `PowerSeries.colemanMajorant`: `β_B(r) = sup_{m ≥ 1} ‖bₘ‖ rᵐ`.

## Main results

* `PowerSeries.IsEntire.tendsto_norm_coeff_rpow_inv_natCast`: the `n`-th roots of the coefficient
  norms of an entire series tend to zero.
* `PowerSeries.IsEntire.exists_newtonMajorant` and `PowerSeries.isEntire_of_norm_coeff_le_prod`:
  the two directions of `PowerSeries.isEntire_iff_exists_newtonMajorant`.
* `PowerSeries.norm_coeff_succ_mul_pow_le_colemanMajorant` and
  `PowerSeries.colemanMajorant_le`: `β_B(r)` is the least upper bound of the weighted
  coefficients of positive degree.
* `PowerSeries.monotoneOn_colemanMajorant` and `PowerSeries.colemanMajorant_le_div_mul`:
  monotonicity, and the linear bound near `0`.
* `PowerSeries.tendsto_colemanMajorant`: `β_B(ρᵢ) → 0` whenever `ρᵢ → 0` with `ρᵢ ≥ 0`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. 127 (1997),
  417–479, Appendix A.
-/

public section

namespace PowerSeries

open Filter Finset Set
open scoped Topology

variable {R : Type*} [NormedRing R] {F B : R⟦X⟧}

section NewtonMajorant

/-- **Cauchy–Hadamard for entire series.** The `n`-th roots `‖aₙ‖ ^ (1 / n)` of the coefficient
norms of an entire series tend to zero. -/
theorem IsEntire.tendsto_norm_coeff_rpow_inv_natCast (hF : F.IsEntire) :
    Tendsto (fun n : ℕ ↦ ‖coeff n F‖ ^ (n⁻¹ : ℝ)) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun b hb ↦ Eventually.of_forall fun n ↦
    hb.trans_le (Real.rpow_nonneg (norm_nonneg _) _), fun ε hε ↦ ?_⟩
  have hδ : 0 < ε / 2 := half_pos hε
  -- at the radius `(ε / 2)⁻¹` the weighted coefficients are eventually below `1`
  have hlim := (isRestricted_iff' _ _).1 (hF.isRestricted (ε / 2)⁻¹)
  filter_upwards [hlim.eventually (gt_mem_nhds one_pos), eventually_ne_atTop 0] with n hn hn0
  have hle : ‖coeff n F‖ ≤ (ε / 2) ^ n := by
    rw [inv_pow, ← div_eq_mul_inv, div_lt_one (by positivity)] at hn
    exact hn.le
  calc ‖coeff n F‖ ^ (n⁻¹ : ℝ) ≤ ((ε / 2) ^ n) ^ (n⁻¹ : ℝ) :=
        Real.rpow_le_rpow (norm_nonneg _) hle (by positivity)
    _ = ε / 2 := Real.pow_rpow_inv_natCast hδ.le hn0
    _ < ε := half_lt_self hε

/-- **Newton majorants of entire series.** The coefficients of an entire series `∑ aⱼ Tʲ` with
`‖a₀‖ ≤ 1`, for instance with `a₀ = 1`, are dominated by the partial products of a positive
antitone sequence tending to zero: `‖aⱼ‖ ≤ ∏ i < j, ρᵢ`. -/
theorem IsEntire.exists_newtonMajorant (hF : F.IsEntire) (hF0 : ‖coeff 0 F‖ ≤ 1) :
    ∃ ρ : ℕ → ℝ, (∀ i, 0 < ρ i) ∧ Antitone ρ ∧ Tendsto ρ atTop (𝓝 0) ∧
      ∀ j, ‖coeff j F‖ ≤ ∏ i ∈ range j, ρ i := by
  set x : ℕ → ℝ := fun n ↦ ‖coeff n F‖ ^ (n⁻¹ : ℝ) with hx_def
  have hx0 (n : ℕ) : 0 ≤ x n := Real.rpow_nonneg (norm_nonneg _) _
  have hx : Tendsto x atTop (𝓝 0) := hF.tendsto_norm_coeff_rpow_inv_natCast
  -- `s i` is the supremum of the roots of index greater than `i`
  set s : ℕ → ℝ := fun i ↦ ⨆ j : ℕ, x (i + j + 1)
  have hbdd (i : ℕ) : BddAbove (Set.range fun j ↦ x (i + j + 1)) :=
    hx.bddAbove_range.mono (Set.range_subset_iff.2 fun j ↦ Set.mem_range_self (i + j + 1))
  have hs0 (i : ℕ) : 0 ≤ s i := Real.iSup_nonneg fun j ↦ hx0 _
  have hxs {i j : ℕ} (hij : i < j) : x j ≤ s i := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
    exact le_ciSup (hbdd i) k
  have hs_anti : Antitone s := antitone_nat_of_succ_le fun i ↦
    ciSup_le fun j ↦ hxs (by omega)
  have hs : Tendsto s atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun b hb ↦ Eventually.of_forall fun i ↦ hb.trans_le (hs0 i),
      fun ε hε ↦ ?_⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hx.eventually (ge_mem_nhds (half_pos hε)))
    filter_upwards [eventually_ge_atTop N] with i hi
    exact (ciSup_le fun j ↦ hN _ (by omega)).trans_lt (half_lt_self hε)
  have hq0 : (0 : ℝ) ≤ 2⁻¹ := by norm_num
  have hq1 : (2⁻¹ : ℝ) < 1 := by norm_num
  refine ⟨fun i ↦ s i + 2⁻¹ ^ i, fun i ↦ by have := hs0 i; positivity,
    hs_anti.add fun i j hij ↦ pow_le_pow_of_le_one hq0 hq1.le hij,
    by simpa using hs.add (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1), fun j ↦ ?_⟩
  rcases eq_or_ne j 0 with rfl | hj
  · simpa using hF0
  calc ‖coeff j F‖ = ∏ _i ∈ range j, x j := by
        rw [prod_const, card_range, hx_def, Real.rpow_inv_natCast_pow (norm_nonneg _) hj]
    _ ≤ ∏ i ∈ range j, (s i + 2⁻¹ ^ i) :=
        prod_le_prod₀ (fun _ _ ↦ hx0 j) fun i hi ↦
          (hxs (mem_range.1 hi)).trans (le_add_of_nonneg_right (by positivity))

/-- A power series whose coefficients are dominated by the partial products of a sequence tending
to zero, `‖aⱼ‖ ≤ ∏ i < j, σᵢ`, is entire. -/
theorem isEntire_of_norm_coeff_le_prod {σ : ℕ → ℝ} (hσ : Tendsto σ atTop (𝓝 0))
    (hF : ∀ j, ‖coeff j F‖ ≤ ∏ i ∈ range j, σ i) : F.IsEntire := by
  refine isEntire_iff.2 fun r ↦ ?_
  rw [← isRestricted_abs_iff, isRestricted_iff']
  have habs : Tendsto (fun i ↦ |σ i|) cofinite (𝓝 0) := by
    simpa [Nat.cofinite_eq_atTop] using hσ.abs
  have h := TauCeti.tendsto_mul_pow_of_forall_prod_le (fun i ↦ abs_nonneg (σ i)) habs
    (x := fun n ↦ ∏ i ∈ range n, |σ i|) (fun n ↦ prod_nonneg fun i _ ↦ abs_nonneg _)
    (fun n c _ hc ↦ hc (range n) (card_range n)) r
  refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) h
  gcongr
  exact (hF n).trans ((le_abs_self _).trans (abs_prod _ _).le)

/-- **Newton majorants characterise entire series.** A power series `∑ aⱼ Tʲ` with `‖a₀‖ ≤ 1` is
entire exactly when `‖aⱼ‖ ≤ ∏ i < j, ρᵢ` for a positive antitone sequence `ρ` tending to zero. -/
theorem isEntire_iff_exists_newtonMajorant (hF0 : ‖coeff 0 F‖ ≤ 1) :
    F.IsEntire ↔ ∃ ρ : ℕ → ℝ, (∀ i, 0 < ρ i) ∧ Antitone ρ ∧ Tendsto ρ atTop (𝓝 0) ∧
      ∀ j, ‖coeff j F‖ ≤ ∏ i ∈ range j, ρ i :=
  ⟨fun hF ↦ hF.exists_newtonMajorant hF0,
    fun ⟨_, _, _, hρ, hF⟩ ↦ isEntire_of_norm_coeff_le_prod hρ hF⟩

end NewtonMajorant

section ColemanMajorant

/-- The **Coleman majorant** `β_B(r) = sup_{m ≥ 1} ‖bₘ‖ rᵐ` of a power series `B = ∑ bₘ Tᵐ` at the
radius `r`. For `r ≥ 0` it is the Gauss norm of `B - B(0)`
(`PowerSeries.colemanMajorant_eq_gaussNorm`). It is a genuine supremum whenever the weighted
coefficients `‖bₘ‖ rᵐ` are bounded above, for instance when `B` is restricted at the radius `r`
(`PowerSeries.norm_coeff_succ_mul_pow_le_colemanMajorant`); only for an unbounded family does it
take the junk value `0` of an unbounded real supremum. -/
noncomputable def colemanMajorant (B : R⟦X⟧) (r : ℝ) : ℝ :=
  ⨆ m : ℕ, ‖coeff (m + 1) B‖ * r ^ (m + 1)

/-- The defining supremum of the Coleman majorant. -/
theorem colemanMajorant_def (B : R⟦X⟧) (r : ℝ) :
    colemanMajorant B r = ⨆ m : ℕ, ‖coeff (m + 1) B‖ * r ^ (m + 1) :=
  (rfl)

/-- The Coleman majorant at a nonnegative radius is nonnegative. -/
theorem colemanMajorant_nonneg (B : R⟦X⟧) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ colemanMajorant B r :=
  Real.iSup_nonneg fun _ ↦ by positivity

/-- At a nonnegative radius, the Coleman majorant of `B` is the Gauss norm of `B - B(0)`. -/
theorem colemanMajorant_eq_gaussNorm {r : ℝ} (hr : 0 ≤ r) :
    colemanMajorant B r = (B - C (coeff 0 B)).gaussNorm norm r := by
  rw [gaussNorm_eq, colemanMajorant_def]
  set f : ℕ → ℝ := fun i ↦ ‖coeff i (B - C (coeff 0 B))‖ * r ^ i
  have hf0 : f 0 = 0 := by simp [f]
  have hf : (fun m ↦ ‖coeff (m + 1) B‖ * r ^ (m + 1)) = fun m ↦ f (m + 1) :=
    funext fun m ↦ by simp [f, coeff_C]
  rw [hf]
  by_cases hb : BddAbove (range f)
  · refine le_antisymm (ciSup_le fun m ↦ le_ciSup hb _) (ciSup_le fun i ↦ ?_)
    cases i with
    | zero => exact hf0.le.trans (Real.iSup_nonneg fun m ↦ by positivity)
    | succ m =>
      exact le_ciSup (f := fun m ↦ f (m + 1))
        (hb.mono (range_subset_iff.2 fun m ↦ mem_range_self _)) m
  · -- both suprema take the junk value `0`
    have hb' : ¬BddAbove (range fun m ↦ f (m + 1)) := fun ⟨M, hM⟩ ↦ hb ⟨max M 0, by
      rintro _ ⟨i, rfl⟩
      cases i with
      | zero => exact hf0.le.trans (le_max_right _ _)
      | succ m => exact (hM ⟨m, rfl⟩).trans (le_max_left _ _)⟩
    rw [Real.iSup_of_not_bddAbove hb, Real.iSup_of_not_bddAbove hb']

/-- The Coleman majorant is at most any bound for the weighted coefficients of positive degree. -/
theorem colemanMajorant_le {r c : ℝ} (h : ∀ m, ‖coeff (m + 1) B‖ * r ^ (m + 1) ≤ c) :
    colemanMajorant B r ≤ c :=
  ciSup_le h

/-- **The Coleman majorant bounds the coefficients.** If `B` is restricted at the radius `r`, every
weighted coefficient `‖bₘ‖ rᵐ` of positive degree is at most `β_B(r)`. -/
theorem norm_coeff_succ_mul_pow_le_colemanMajorant {r : ℝ} (hB : B.IsRestricted r) (m : ℕ) :
    ‖coeff (m + 1) B‖ * r ^ (m + 1) ≤ colemanMajorant B r :=
  le_ciSup (((isRestricted_iff' _ _).1 hB).bddAbove_range.mono
    (Set.range_subset_iff.2 fun m ↦ Set.mem_range_self (m + 1))) m

/-- The Coleman majorant is monotone in the radius below a radius of restrictedness. -/
theorem colemanMajorant_le_colemanMajorant {r s : ℝ} (hB : B.IsRestricted s) (hr : 0 ≤ r)
    (hrs : r ≤ s) : colemanMajorant B r ≤ colemanMajorant B s :=
  colemanMajorant_le fun m ↦ (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrs _)
    (norm_nonneg _)).trans (norm_coeff_succ_mul_pow_le_colemanMajorant hB m)

/-- The Coleman majorant of an entire series is monotone on the nonnegative radii. -/
theorem monotoneOn_colemanMajorant (hB : B.IsEntire) : MonotoneOn (colemanMajorant B) (Ici 0) :=
  fun _ hr _ _ hrs ↦ colemanMajorant_le_colemanMajorant (hB.isRestricted _) hr hrs

/-- **Linear bound near zero.** Since the constant term is omitted, `β_B(r) ≤ (r / s) β_B(s)`
for `0 ≤ r ≤ s` when `B` is restricted at the radius `s > 0`. -/
theorem colemanMajorant_le_div_mul {r s : ℝ} (hB : B.IsRestricted s) (hs : 0 < s) (hr : 0 ≤ r)
    (hrs : r ≤ s) : colemanMajorant B r ≤ r / s * colemanMajorant B s := by
  refine colemanMajorant_le fun m ↦ ?_
  have hpow : r ^ (m + 1) ≤ r / s * s ^ (m + 1) :=
    calc r ^ (m + 1) = r * r ^ m := pow_succ' r m
      _ ≤ r * s ^ m := by gcongr
      _ = r / s * s ^ (m + 1) := by field_simp; ring
  calc ‖coeff (m + 1) B‖ * r ^ (m + 1) ≤ ‖coeff (m + 1) B‖ * (r / s * s ^ (m + 1)) :=
        mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ = r / s * (‖coeff (m + 1) B‖ * s ^ (m + 1)) := by ring
    _ ≤ r / s * colemanMajorant B s :=
        mul_le_mul_of_nonneg_left (norm_coeff_succ_mul_pow_le_colemanMajorant hB m)
          (div_nonneg hr hs.le)

/-- **Decay of the Coleman majorant.** If `B` is restricted at some positive radius, then
`β_B(ρᵢ)` tends to zero along every nonnegative family of radii `ρᵢ` tending to zero. -/
theorem tendsto_colemanMajorant {ι : Type*} {l : Filter ι} {ρ : ι → ℝ} {s : ℝ}
    (hB : B.IsRestricted s) (hs : 0 < s) (hρ0 : ∀ i, 0 ≤ ρ i) (hρ : Tendsto ρ l (𝓝 0)) :
    Tendsto (fun i ↦ colemanMajorant B (ρ i)) l (𝓝 0) := by
  have hlin : Tendsto (fun i ↦ ρ i / s * colemanMajorant B s) l (𝓝 0) := by
    simpa using (hρ.div_const s).mul_const (colemanMajorant B s)
  refine squeeze_zero' (Eventually.of_forall fun i ↦ colemanMajorant_nonneg B (hρ0 i)) ?_ hlin
  filter_upwards [hρ.eventually (ge_mem_nhds hs)] with i hi
  exact colemanMajorant_le_div_mul hB hs (hρ0 i) hi

/-- Truncation does not increase the Coleman majorant at a nonnegative radius. -/
theorem colemanMajorant_trunc_le {r : ℝ} (hB : B.IsRestricted r) (hr : 0 ≤ r) (n : ℕ) :
    colemanMajorant (trunc n B : R⟦X⟧) r ≤ colemanMajorant B r := by
  refine colemanMajorant_le fun m ↦ ?_
  rw [Polynomial.coeff_coe, coeff_trunc]
  split_ifs
  · exact norm_coeff_succ_mul_pow_le_colemanMajorant hB m
  · simpa using colemanMajorant_nonneg B hr

/-- The Coleman majorant ignores the constant term. -/
@[simp]
theorem colemanMajorant_C (a : R) (r : ℝ) : colemanMajorant (C a) r = 0 := by
  simp [colemanMajorant_def]

/-- The Coleman majorant of the zero series vanishes. -/
@[simp]
theorem colemanMajorant_zero (r : ℝ) : colemanMajorant (0 : R⟦X⟧) r = 0 := by
  simpa using colemanMajorant_C (0 : R) r

/-- The Coleman majorant of a monomial `Tᵏ` of positive degree is `rᵏ` at a radius `r ≥ 0`. -/
@[simp]
theorem colemanMajorant_X_pow [NormOneClass R] {k : ℕ} (hk : k ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    colemanMajorant (X ^ k : R⟦X⟧) r = r ^ k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  refine le_antisymm (colemanMajorant_le fun m ↦ ?_) ?_
  · rw [coeff_X_pow]
    split_ifs with h
    · rw [h, norm_one, one_mul]
    · simpa using pow_nonneg hr _
  · simpa using norm_coeff_succ_mul_pow_le_colemanMajorant
      ((isEntire_X (R := R)).pow (k + 1) |>.isRestricted r) k

/-- The Coleman majorant of `T` is the radius `r ≥ 0` itself. -/
@[simp]
theorem colemanMajorant_X [NormOneClass R] {r : ℝ} (hr : 0 ≤ r) :
    colemanMajorant (X : R⟦X⟧) r = r := by
  simpa using colemanMajorant_X_pow (R := R) one_ne_zero hr

end ColemanMajorant

end PowerSeries
