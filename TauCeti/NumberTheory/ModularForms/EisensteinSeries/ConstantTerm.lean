/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Cusps.ConstantTerm
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Character
import Mathlib.Analysis.Normed.Group.Tannery
import TauCeti.Analysis.Complex.UpperHalfPlane.ResToImagAxis
import TauCeti.NumberTheory.ModularForms.QExpansion.BigO

/-!
# Constant terms of Eisenstein series at the cusps

For a weight `W : (Fin 2 → ZMod N) → ℂ` and `k ≥ 3`, the weighted Eisenstein series
`G_W(z) = ∑_{x ∈ ℤ²} W(x mod N) (x₀ z + x₁)^(-k)` tends at `i∞` to the sum of its row `x₀ = 0`,
`∑_{n ∈ ℤ} W(0, n) n^(-k)`: every other summand decays like `(Im z)^(-k)`, and the series is
dominated uniformly on the imaginary axis. Since slashing by `γ ∈ SL₂(ℤ)` changes `W` to
`a ↦ W(a γ⁻¹)`, the constant term of `G_W` at the cusp `γ ∞ = a / c` is the sum over the
multiples of the row `(-c, a)` of `γ⁻¹`:
`∑_{n ∈ ℤ} W(-n c, n a) n^(-k)`.

For the Eisenstein series with character `G_k^{ψ,φ}`, with `ψ` modulo `u` and `φ` modulo `v`,
this sum factors: the constant term at `a / c` vanishes unless `v ∣ c`, and then equals
`ψ(-c / v) φ⁻¹(a) ∑_{n ∈ ℤ} ψ(n) φ⁻¹(n) n^(-k)`. These are the constant-term vectors whose span
is compared with the image of the constant-term map on `M_k(N, χ)` in the cusp–Eisenstein
decomposition `M_k(N, χ) = S_k(N, χ) ⊕ E_k(N, χ)`.

## Main results

* `TauCeti.EisensteinSeries.tendsto_weightedEisensteinSeries_atImInfty`: the limit of `G_W`
  at `i∞`.
* `TauCeti.EisensteinSeries.valueAtInfty_weightedEisensteinSeries_slash`: the value at `i∞` of
  every `SL₂(ℤ)`-translate of `G_W`.
* `TauCeti.EisensteinSeries.constantTermAt_weightedEisensteinSeriesMF`: the constant term of
  `G_W` at every cusp.
* `TauCeti.EisensteinSeries.constantTermAt_charEisensteinSeriesMF`: the constant term of
  `G_k^{ψ,φ}` at every cusp.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.2 and
  §4.5.
-/

public section

noncomputable section

open ModularForm Matrix Matrix.SpecialLinearGroup CongruenceSubgroup Complex Filter
open UpperHalfPlane hiding I
open EisensteinSeries

open scoped MatrixGroups Topology

namespace TauCeti.EisensteinSeries

variable {N : ℕ} (W : (Fin 2 → ZMod N) → ℂ) {k : ℤ}

/-- On the imaginary axis, a summand `(x₀ z + x₁)^(-k)` with `x₀ ≠ 0` tends to `0`, and a
summand with `x₀ = 0` is the constant `x₁^(-k)`. -/
lemma tendsto_eisSummand_ofComplex_I_mul (hk : 0 < k) (x : Fin 2 → ℤ) :
    Tendsto (fun t : ℝ ↦ eisSummand k x (ofComplex (I * t))) atTop
      (𝓝 (if x 0 = 0 then (x 1 : ℂ) ^ (-k) else 0)) := by
  by_cases hx : x 0 = 0
  · simp [eisSummand, hx]
  simp only [hx, ↓reduceIte]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (tendsto_zpow_atTop_zero (neg_neg_of_pos hk))
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hz : ((ofComplex (I * t) : ℍ) : ℂ) = I * t := by
    rw [ofComplex_apply_of_im_pos (by simpa using ht), UpperHalfPlane.coe_mk]
  -- the imaginary part `x₀ t` bounds the linear form from below
  have hle : t ≤ ‖(x 0 : ℂ) * (ofComplex (I * t) : ℍ) + x 1‖ := by
    refine le_trans ?_ (abs_im_le_norm _)
    have h1 : (1 : ℝ) ≤ |(x 0 : ℝ)| := by exact_mod_cast Int.one_le_abs hx
    simpa [hz, abs_mul, abs_of_pos ht] using le_mul_of_one_le_left ht.le h1
  rw [eisSummand, zpow_neg, norm_inv, norm_zpow, zpow_neg]
  exact inv_anti₀ (zpow_pos ht _) (zpow_le_zpow_left₀ hk.le ht.le hle)

variable [NeZero N]

/-- The weighted series tends along the imaginary axis to the sum of its row `x₀ = 0`. -/
private lemma tendsto_weightedEisensteinSeries_ofComplex_I_mul (hk : 3 ≤ k) :
    Tendsto (fun t : ℝ ↦ weightedEisensteinSeries W k (ofComplex (I * t))) atTop
      (𝓝 (∑' n : ℤ, W ((↑) ∘ ![0, n]) * (n : ℂ) ^ (-k))) := by
  have hk' : (2 : ℝ) < k := by exact_mod_cast (by omega : (2 : ℤ) < k)
  have hk0 : 0 < k := by omega
  have hB : (0 : ℝ) < 1 := one_pos
  -- the limit, as a sum over all integer pairs, is supported on the row `x₀ = 0`
  have hrow : ∑' n : ℤ, W ((↑) ∘ ![0, n]) * (n : ℂ) ^ (-k) =
      ∑' x : Fin 2 → ℤ, W ((↑) ∘ x) * (if x 0 = 0 then (x 1 : ℂ) ^ (-k) else 0) := by
    have hinj : Function.Injective fun n : ℤ ↦ ![0, n] := fun m n h ↦ by
      simpa using congrFun h 1
    rw [← hinj.tsum_eq]
    · simp
    · intro x hx
      have hx0 : x 0 = 0 := by
        by_contra h
        simp [h] at hx
      exact ⟨x 1, by ext i; fin_cases i <;> simp [hx0]⟩
  rw [hrow]
  simp_rw [weightedEisensteinSeries_def]
  refine tendsto_tsum_of_dominated_convergence (bound := fun x : Fin 2 → ℤ ↦
      (∑ b, ‖W b‖) * (r ⟨⟨0, 1⟩, hB⟩ ^ (-k : ℝ) * ‖x‖ ^ (-k : ℝ)))
    (((summable_one_div_norm_rpow hk').mul_left _).mul_left _)
    (fun x ↦ (tendsto_eisSummand_ofComplex_I_mul hk0 x).const_mul _) ?_
  filter_upwards [eventually_ge_atTop 1] with t ht x
  have hz : (ofComplex (I * t) : ℍ) ∈ verticalStrip 0 1 := by
    rw [ofComplex_apply_of_im_pos (by simpa using (zero_lt_one.trans_le ht))]
    simpa [verticalStrip] using ht
  rw [norm_mul]
  refine mul_le_mul ?_ ?_ (norm_nonneg _) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  · exact Finset.single_le_sum (f := fun b ↦ ‖W b‖) (fun _ _ ↦ norm_nonneg _)
      (Finset.mem_univ _)
  · simpa only [eisSummand, one_div, ← zpow_neg, norm_zpow, ← Real.rpow_intCast,
      Int.cast_neg] using summand_bound_of_mem_verticalStrip (by positivity) x hB hz

/-- **The limit at `i∞` of a weighted Eisenstein series**: for `k ≥ 3`, the series
`∑_{x ∈ ℤ²} W(x) (x₀ z + x₁)^(-k)` tends to `∑_{n ∈ ℤ} W(0, n) n^(-k)`. -/
theorem tendsto_weightedEisensteinSeries_atImInfty (hk : 3 ≤ k) :
    Tendsto (weightedEisensteinSeries W k) atImInfty
      (𝓝 (∑' n : ℤ, W ((↑) ∘ ![0, n]) * (n : ℂ) ^ (-k))) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hlim := TauCeti.ModularFormClass.tendsto_valueAtInfty
    (weightedEisensteinSeriesMF W hk) hN (by simp)
  rw [coe_weightedEisensteinSeriesMF] at hlim
  -- the limit along `i∞` is also the limit along the imaginary axis
  rw [tendsto_nhds_unique (tendsto_weightedEisensteinSeries_ofComplex_I_mul W hk)
    (hlim.comp tendsto_ofComplex_I_mul_atTop_atImInfty)]
  exact hlim

/-- The value at `i∞` of a weighted Eisenstein series is the sum of its row `x₀ = 0`. -/
theorem valueAtInfty_weightedEisensteinSeries (hk : 3 ≤ k) :
    valueAtInfty (weightedEisensteinSeries W k) =
      ∑' n : ℤ, W ((↑) ∘ ![0, n]) * (n : ℂ) ^ (-k) :=
  (tendsto_weightedEisensteinSeries_atImInfty W hk).limUnder_eq

/-- **The value at `i∞` of a translated weighted Eisenstein series.** For
`γ = !![a, b; c, d] ∈ SL₂(ℤ)`, the value at `i∞` of `G_W ∣[k] γ` is
`∑_{n ∈ ℤ} W(-n c, n a) n^(-k)`: only the multiples of the row `(-c, a)` of `γ⁻¹` contribute,
the pairs whose linear form vanishes at the cusp `a / c`. -/
theorem valueAtInfty_weightedEisensteinSeries_slash (hk : 3 ≤ k) (γ : SL(2, ℤ)) :
    valueAtInfty (weightedEisensteinSeries W k ∣[k] γ) =
      ∑' n : ℤ, W ((↑) ∘ ![-(n * γ 1 0), n * γ 0 0]) * (n : ℂ) ^ (-k) := by
  rw [weightedEisensteinSeries_slash_apply, valueAtInfty_weightedEisensteinSeries _ hk]
  refine tsum_congr fun n ↦ ?_
  congr 2
  ext i
  fin_cases i <;> simp [vecMul, dotProduct, Matrix.adjugate_fin_two]

/-- **The constant term of a weighted Eisenstein series at every cusp.** At the cusp
represented by `γ = !![a, b; c, d] ∈ SL₂(ℤ)`, the constant term of `G_W` is
`∑_{n ∈ ℤ} W(-n c, n a) n^(-k)`. -/
theorem constantTermAt_weightedEisensteinSeriesMF (hk : 3 ≤ k) (γ : SL(2, ℤ)) :
    constantTermAt γ (weightedEisensteinSeriesMF W hk) =
      ∑' n : ℤ, W ((↑) ∘ ![-(n * γ 1 0), n * γ 0 0]) * (n : ℂ) ^ (-k) := by
  have h : weightedEisensteinSeries W k ∣[k] mapGL ℝ γ = weightedEisensteinSeries W k ∣[k] γ :=
    (SL_slash _ γ).symm
  rw [constantTermAt_eq_valueAtInfty, coe_translate, coe_weightedEisensteinSeriesMF, h,
    valueAtInfty_weightedEisensteinSeries_slash W hk]

variable {u v : ℕ} (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v)

/-- The sum of the character weight over the multiples of an integer pair `(-c, a)`: it vanishes
unless `v ∣ c`, and otherwise factors through the series of `ψ φ⁻¹`. -/
private lemma tsum_charWeight_mul_zpow (huv : u * v ∣ N) (c a : ℤ) :
    ∑' n : ℤ, charWeight N ψ φ ((↑) ∘ ![-(n * c), n * a]) * (n : ℂ) ^ (-k) =
      if (v : ℤ) ∣ c then
        ψ ((-(c / v) : ℤ) : ZMod u) * φ⁻¹ (a : ZMod v) *
          ∑' n : ℤ, ψ (n : ZMod u) * φ⁻¹ (n : ZMod v) * (n : ℂ) ^ (-k)
      else 0 := by
  simp only [charWeight_intCast ψ φ huv, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  split_ifs with hc
  · obtain ⟨c, rfl⟩ := hc
    have hv : (v : ℤ) ≠ 0 := by
      have : v ≠ 0 := fun h ↦ NeZero.ne N (Nat.eq_zero_of_zero_dvd (by simpa [h] using huv))
      exact_mod_cast this
    rw [Int.mul_ediv_cancel_left _ hv, ← tsum_mul_left]
    refine tsum_congr fun n ↦ ?_
    have hdvd : (v : ℤ) ∣ -(n * (v * c)) := Dvd.intro (-(n * c)) (by ring)
    have hfactor : -(n * (v * c)) = (v : ℤ) * (n * -c) := by ring
    have hquot : -(n * (v * c)) / (v : ℤ) = n * -c := by
      rw [hfactor, Int.mul_ediv_cancel_left _ hv]
    rw [hquot]
    simp only [hdvd, ↓reduceIte, Int.cast_mul, map_mul]
    ring
  · refine (tsum_congr fun n ↦ ?_).trans tsum_zero
    split_ifs with hn
    · rw [MulChar.map_nonunit φ⁻¹, mul_zero, zero_mul]
      intro hu
      rw [ZMod.coe_int_isUnit_iff_isCoprime] at hu
      exact hc ((hu.of_mul_right_left).dvd_of_dvd_mul_left (by simpa using hn))
    · rw [zero_mul]

/-- **The constant term of the Eisenstein series with character at every cusp.** For `ψ`
modulo `u`, `φ` modulo `v` with `u v ∣ N`, and `γ = !![a, b; c, d] ∈ SL₂(ℤ)`, the constant term
of `G_k^{ψ,φ}` at the cusp `a / c` is
`ψ(-c / v) φ⁻¹(a) ∑_{n ∈ ℤ} ψ(n) φ⁻¹(n) n^(-k)` if `v ∣ c`, and `0` otherwise. -/
theorem constantTermAt_charEisensteinSeriesMF (hk : 3 ≤ k) (huv : u * v ∣ N) (γ : SL(2, ℤ)) :
    constantTermAt γ (charEisensteinSeriesMF ψ φ hk huv) =
      if (v : ℤ) ∣ γ 1 0 then
        ψ ((-(γ 1 0 / v) : ℤ) : ZMod u) * φ⁻¹ (γ 0 0 : ZMod v) *
          ∑' n : ℤ, ψ (n : ZMod u) * φ⁻¹ (n : ZMod v) * (n : ℂ) ^ (-k)
      else 0 := by
  have h : weightedEisensteinSeries (charWeight N ψ φ) k ∣[k] mapGL ℝ γ =
      weightedEisensteinSeries (charWeight N ψ φ) k ∣[k] γ :=
    (SL_slash _ γ).symm
  rw [constantTermAt_eq_valueAtInfty, coe_translate, coe_charEisensteinSeriesMF, h,
    valueAtInfty_weightedEisensteinSeries_slash _ hk, tsum_charWeight_mul_zpow ψ φ huv]

end TauCeti.EisensteinSeries
