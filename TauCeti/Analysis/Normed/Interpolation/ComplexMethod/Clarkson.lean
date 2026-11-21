/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.PiLp
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Symmetry
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Analysis.MeanInequalitiesPow
import TauCeti.Analysis.Normed.Lp.PiLp

/-!
# Boas–Kosaki–McCarthy–Clarkson inequalities via complex interpolation

Whenever one endpoint of `(X₀, X₁)` satisfies `InnerProductSpaceable`, complex interpolation of
`(x, y) ↦ (x + y, x - y)` between `ℓ¹_2 → ℓ^∞_2` (norm `≤ 1`) and `ℓ²_2 → ℓ²_2` (norm `≤ √2`),
conjugated by `CompatibleCouple.piLpComplexMethodEquiv`, gives the Boas–Kosaki–McCarthy and
Clarkson inequalities on `[X₀, X₁]_θ` (`0 < θ < 1`) without completeness, intersection density, or
duality; `ComplexMethodSpace.swap` transfers them to the left Hilbertian endpoint.

## Main results

* `norm_add_rpow_add_norm_sub_rpow_le_right` / `_left`: Boas–Kosaki–McCarthy on `[X₀, X₁]_θ`.
* `norm_add_rpow_add_norm_sub_rpow_le_two_pow_right` / `_left`: Clarkson for `2 < q`.
* `norm_add_rpow_add_norm_sub_rpow_le_two_mul_right` / `_left`: Clarkson for `1 < p < 2`.

## References

* R. P. Boas Jr., Bull. Amer. Math. Soc. **46** (1940), 304–311; C. A. McCarthy, Israel J. Math.
  **5** (1967), 249–271, §2; J. Bergh and J. Löfström, *Interpolation Spaces*, Springer, 1976,
  Exercise 5.7.6; H. Kosaki, J. Funct. Anal. **56** (1984), 29–78, Theorem 5.1.
-/

public noncomputable section

open Set WithLp
open scoped ENNReal

namespace TauCeti.CompatibleCouple.ComplexMethodSpace

/-! ### Exponent arithmetic and compatibility on `CompatibleCouple.piLp` -/

private instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩

private theorem inv_ofReal_two_div_two_sub {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    (ENNReal.ofReal (2 / (2 - θ)))⁻¹ =
      ENNReal.ofReal (1 - θ) * (1 : ℝ≥0∞)⁻¹ + ENNReal.ofReal θ * (2 : ℝ≥0∞)⁻¹ := by
  have hinv : (2 / (2 - θ))⁻¹ = 1 - θ + θ * 2⁻¹ := by rw [inv_div]; ring
  rw [← ENNReal.ofReal_inv_of_pos (div_pos zero_lt_two (by linarith [hθ.2])), hinv,
    ENNReal.ofReal_add (sub_nonneg.2 hθ.2.le) (by linarith [hθ.1]), ENNReal.ofReal_mul hθ.1.le]
  simp [ENNReal.ofReal_inv_of_pos]

private theorem inv_ofReal_two_div {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    (ENNReal.ofReal (2 / θ))⁻¹ =
      ENNReal.ofReal (1 - θ) * (∞ : ℝ≥0∞)⁻¹ + ENNReal.ofReal θ * (2 : ℝ≥0∞)⁻¹ := by
  have hinv : (2 / θ)⁻¹ = θ * 2⁻¹ := by rw [inv_div, div_eq_mul_inv]
  rw [← ENNReal.ofReal_inv_of_pos (div_pos zero_lt_two hθ.1), hinv, ENNReal.ofReal_mul hθ.1.le]
  simp [ENNReal.ofReal_inv_of_pos]

section Couple

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]

private def swapOfSubEq (C : CompatibleCouple ℂ X₀ X₁ V) {θ η : ℝ} (h : 1 - θ = η) :
    C.ComplexMethodSpace θ ≃ₗᵢ[ℂ] C.swap.ComplexMethodSpace η := h ▸ swap C θ

omit [T1Space V] in
private theorem clarksonPair_compat (C : CompatibleCouple ℂ X₀ X₁ V)
    (x : (piLp 1 2 fun _ : Fin 2 ↦ C).inter) :
    (piLp ∞ 2 fun _ : Fin 2 ↦ C).fstToSum
        (PiLp.clarksonPairCLM 1 ∞ ℂ X₀ ((piLp 1 2 fun _ : Fin 2 ↦ C).interFst x)) =
      (piLp ∞ 2 fun _ : Fin 2 ↦ C).sndToSum
        (PiLp.clarksonPairCLM 2 2 ℂ X₁ ((piLp 1 2 fun _ : Fin 2 ↦ C).interSnd x)) := by
  have h (j : Fin 2) : C.embed₀ (x.val.1 j) = C.embed₁ (x.val.2 j) := by
    simpa using congr_fun ((piLp 1 2 fun _ : Fin 2 ↦ C).embed₀_interFst x) j
  refine (piLp ∞ 2 fun _ : Fin 2 ↦ C).sumSpace_ext (funext fun i ↦ ?_)
  simp only [sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, piLp_embed₀_apply, piLp_embed₁_apply,
    PiLp.clarksonPairCLM_apply]
  split_ifs <;> simp [h 0, h 1]

private theorem piLpCoord_map_clarksonPair {θ : ℝ} {C : CompatibleCouple ℂ X₀ X₁ V}
    {w : (piLp 1 2 fun _ : Fin 2 ↦ C).ComplexMethodSpace θ} {u v : C.ComplexMethodSpace θ}
    (hu : piLpCoord θ (fun _ : Fin 2 ↦ C) 0 w = u)
    (hv : piLpCoord θ (fun _ : Fin 2 ↦ C) 1 w = v) (i : Fin 2) :
    piLpCoord θ (fun _ : Fin 2 ↦ C) i
      (map θ (PiLp.clarksonPairCLM 1 ∞ ℂ X₀) (PiLp.clarksonPairCLM 2 2 ℂ X₁)
        (clarksonPair_compat C) w) = if i = 0 then u + v else u - v := by
  obtain ⟨x₀, x₁, hx⟩ := (piLp 1 2 fun _ : Fin 2 ↦ C).exists_fstToSum_add_sndToSum_eq (toSum w)
  have hu' : C.sumSpaceEmbed (toSum u) = C.embed₀ (x₀ 0) + C.embed₁ (x₁ 0) := by
    rw [← hu, sumSpaceEmbed_toSum_piLpCoord θ (fun _ : Fin 2 ↦ C) 0]; simp [← hx]
  have hv' : C.sumSpaceEmbed (toSum v) = C.embed₀ (x₀ 1) + C.embed₁ (x₁ 1) := by
    rw [← hv, sumSpaceEmbed_toSum_piLpCoord θ (fun _ : Fin 2 ↦ C) 1]; simp [← hx]
  refine ComplexMethodSpace.ext <| C.sumSpaceEmbed_injective ?_
  rw [sumSpaceEmbed_toSum_piLpCoord θ (fun _ : Fin 2 ↦ C) i, toSum_map_of_eq_add _ _ _ hx]
  split_ifs with hi <;> simp [hi, PiLp.clarksonPairCLM_apply, hu', hv'] <;> abel

/-! ### Boas–Kosaki–McCarthy–Clarkson inequalities on `[X₀, X₁]_θ` -/

/-- **Boas–Kosaki–McCarthy–Clarkson inequality (right Hilbertian endpoint).**
For `InnerProductSpaceable X₁`, `0 < θ < 1`, and `u, v : [X₀, X₁]_θ`,
`‖u + v‖ ^ (2 / θ) + ‖u - v‖ ^ (2 / θ) ≤`
`  2 * (‖u‖ ^ (2 / (2 - θ)) + ‖v‖ ^ (2 / (2 - θ))) ^ ((2 - θ) / θ)`. -/
theorem norm_add_rpow_add_norm_sub_rpow_le_right [InnerProductSpaceable X₁]
    {C : CompatibleCouple ℂ X₀ X₁ V} {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (u v : C.ComplexMethodSpace θ) :
    ‖u + v‖ ^ (2 / θ) + ‖u - v‖ ^ (2 / θ) ≤
      2 * (‖u‖ ^ (2 / (2 - θ)) + ‖v‖ ^ (2 / (2 - θ))) ^ ((2 - θ) / θ) := by
  set p := 2 / (2 - θ); set q := 2 / θ
  have hp1 : 1 < p := by rw [one_lt_div (by linarith [hθ.2])]; linarith [hθ.1]
  have hq2 : 2 < q := by rw [lt_div_iff₀ hθ.1]; linarith [hθ.2]
  have hp_pos : 0 < p := zero_lt_one.trans hp1; have hq_pos : 0 < q := zero_lt_two.trans hq2
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.2 hp1.le⟩
  have : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.2 (one_lt_two.trans hq2).le⟩
  let eDom := piLpComplexMethodEquiv (q := ENNReal.ofReal p) hθ
    (inv_ofReal_two_div_two_sub hθ) (fun _ : Fin 2 ↦ C)
  let eCod := piLpComplexMethodEquiv (q := ENNReal.ofReal q) hθ
    (inv_ofReal_two_div hθ) (fun _ : Fin 2 ↦ C)
  let pair : PiLp (ENNReal.ofReal p) (fun _ : Fin 2 ↦ C.ComplexMethodSpace θ) :=
    toLp (ENNReal.ofReal p) (fun i : Fin 2 ↦ if i = 0 then u else v)
  let w := eDom.symm pair
  let Tw := map θ (PiLp.clarksonPairCLM 1 ∞ ℂ X₀) (PiLp.clarksonPairCLM 2 2 ℂ X₁)
    (clarksonPair_compat C) w
  have hTw : ‖eCod Tw‖ ≤ (2 : ℝ) ^ (θ / 2) * ‖pair‖ := by
    rw [eCod.norm_map, ← eDom.symm.norm_map pair]
    refine (norm_map_le _ _ _ ⟨hθ.1.le, hθ.2.le⟩ zero_le_one (Real.rpow_nonneg zero_le_two _)
      (fun x ↦ (PiLp.norm_clarksonPairCLM_one_top_le ℂ x).trans_eq (one_mul _).symm)
      (fun x ↦ (PiLp.norm_clarksonPairCLM_two_two_le ℂ x).trans_eq
        (by rw [Real.sqrt_eq_rpow])) w).trans_eq ?_
    rw [Real.one_rpow, one_mul, ← Real.rpow_mul zero_le_two, one_div_mul_eq_div]
  have hcoord (i : Fin 2) : eCod Tw i = if i = 0 then u + v else u - v :=
    (piLpComplexMethodEquiv_apply _ _ _ Tw i).trans <| piLpCoord_map_clarksonPair
      (piLpCoord_piLpComplexMethodEquiv_symm hθ (inv_ofReal_two_div_two_sub hθ) _ pair 0)
      (piLpCoord_piLpComplexMethodEquiv_symm hθ (inv_ofReal_two_div_two_sub hθ) _ pair 1) i
  have hlhs : ‖u + v‖ ^ q + ‖u - v‖ ^ q = ‖eCod Tw‖ ^ q := by
    simpa [ENNReal.toReal_ofReal hq_pos.le, Fin.sum_univ_two, hcoord 0, hcoord 1] using
      (PiLp.norm_rpow_eq_sum (by rwa [ENNReal.toReal_ofReal hq_pos.le]) (eCod Tw)).symm
  have h2θ : 2 - θ ≠ 0 := by linarith [hθ.2]
  have hq_eq : q = p * ((2 - θ) / θ) := (div_mul_div_cancel₀ h2θ).symm
  have hpair : ‖pair‖ ^ q = (‖u‖ ^ p + ‖v‖ ^ p) ^ ((2 - θ) / θ) := by
    rw [hq_eq, Real.rpow_mul (norm_nonneg pair)]
    simpa [ENNReal.toReal_ofReal hp_pos.le, Fin.sum_univ_two, pair] using
      congrArg (· ^ ((2 - θ) / θ))
        (PiLp.norm_rpow_eq_sum (by rwa [ENNReal.toReal_ofReal hp_pos.le]) pair)
  have hθq : θ / 2 * q = 1 := by dsimp [q]; field_simp [hθ.1.ne']
  rw [hlhs]
  refine (Real.rpow_le_rpow (norm_nonneg _) hTw hq_pos.le).trans_eq ?_
  rw [Real.mul_rpow (Real.rpow_nonneg zero_le_two _) (norm_nonneg pair),
    ← Real.rpow_mul zero_le_two, hpair, hθq, Real.rpow_one]

/-- **Boas–Kosaki–McCarthy–Clarkson inequality (left Hilbertian endpoint).** -/
theorem norm_add_rpow_add_norm_sub_rpow_le_left [InnerProductSpaceable X₀]
    {C : CompatibleCouple ℂ X₀ X₁ V} {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (u v : C.ComplexMethodSpace θ) :
    ‖u + v‖ ^ (2 / (1 - θ)) + ‖u - v‖ ^ (2 / (1 - θ)) ≤
      2 * (‖u‖ ^ (2 / (1 + θ)) + ‖v‖ ^ (2 / (1 + θ))) ^ ((1 + θ) / (1 - θ)) := by
  have hsub : 2 - (1 - θ) = 1 + θ := by ring
  have h := norm_add_rpow_add_norm_sub_rpow_le_right
    (sub_mem_Ioo_zero_iff_right.2 hθ) (swap C θ u) (swap C θ v)
  rwa [← map_add, ← map_sub, (swap C θ).norm_map, (swap C θ).norm_map, (swap C θ).norm_map,
    (swap C θ).norm_map, hsub] at h

/-- **Clarkson's inequality on `[X₀, X₁]_{2/q}` for `2 < q` (right Hilbertian endpoint).** -/
theorem norm_add_rpow_add_norm_sub_rpow_le_two_pow_right [InnerProductSpaceable X₁]
    {C : CompatibleCouple ℂ X₀ X₁ V} {q : ℝ} (hq : 2 < q) (u v : C.ComplexMethodSpace (2 / q)) :
    ‖u + v‖ ^ q + ‖u - v‖ ^ q ≤ 2 ^ (q - 1) * (‖u‖ ^ q + ‖v‖ ^ q) := by
  have hq1 : 2 / (2 / q) = q := by field_simp
  have hq2 : 2 / (2 - 2 / q) = q / (q - 1) := by field_simp
  have hq3 : (2 - 2 / q) / (2 / q) = q - 1 := by field_simp
  have hqm1 : q - 1 ≠ 0 := by linarith
  have hb := norm_add_rpow_add_norm_sub_rpow_le_right
    ⟨div_pos zero_lt_two (by linarith), (div_lt_one (by linarith)).2 hq⟩ u v
  rw [hq1, hq2, hq3] at hb
  have hrpow : (‖u‖ ^ (q / (q - 1)) + ‖v‖ ^ (q / (q - 1))) ^ (q - 1) ≤
      2 ^ (q - 1 - 1) * ((‖u‖ ^ (q / (q - 1))) ^ (q - 1) + (‖v‖ ^ (q / (q - 1))) ^ (q - 1)) := by
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
      ⟨‖u‖ ^ (q / (q - 1)), by positivity⟩ ⟨‖v‖ ^ (q / (q - 1)), by positivity⟩ (by linarith)
  refine hb.trans ((mul_le_mul_of_nonneg_left hrpow zero_le_two).trans_eq ?_)
  rw [← Real.rpow_mul (norm_nonneg u), ← Real.rpow_mul (norm_nonneg v),
    div_mul_cancel₀ q hqm1, Real.rpow_sub_one two_ne_zero]; ring

/-- **Clarkson's inequality on `[X₀, X₁]_{1 - 2/q}` for `2 < q` (left Hilbertian endpoint).** -/
theorem norm_add_rpow_add_norm_sub_rpow_le_two_pow_left [InnerProductSpaceable X₀]
    {C : CompatibleCouple ℂ X₀ X₁ V} {q : ℝ} (hq : 2 < q)
    (u v : C.ComplexMethodSpace (1 - 2 / q)) :
    ‖u + v‖ ^ q + ‖u - v‖ ^ q ≤ 2 ^ (q - 1) * (‖u‖ ^ q + ‖v‖ ^ q) := by
  have hθ : 1 - (1 - 2 / q) = 2 / q := by ring
  let e := swapOfSubEq C hθ
  have h := norm_add_rpow_add_norm_sub_rpow_le_two_pow_right hq (e u) (e v)
  rwa [← map_add, ← map_sub, e.norm_map, e.norm_map, e.norm_map, e.norm_map] at h

/-- **Clarkson's inequality on `[X₀, X₁]_{2 - 2/p}` for `1 < p < 2` (right endpoint).** -/
theorem norm_add_rpow_add_norm_sub_rpow_le_two_mul_right [InnerProductSpaceable X₁]
    {C : CompatibleCouple ℂ X₀ X₁ V} {p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2)
    (u v : C.ComplexMethodSpace (2 - 2 / p)) :
    ‖u + v‖ ^ p + ‖u - v‖ ^ p ≤ 2 * (‖u‖ ^ p + ‖v‖ ^ p) := by
  have hp0 : 0 < p := zero_lt_one.trans hp₁; have hp_sub : 0 < p - 1 := sub_pos.2 hp₁
  set r := (p - 1)⁻¹
  have hr_pos : 0 < r := inv_pos.2 hp_sub
  have huv : 0 ≤ ‖u + v‖ ^ p + ‖u - v‖ ^ p := by positivity
  have hp1_exp : 2 / (2 - 2 / p) = p * r := by dsimp [r]; field_simp
  have hp2_exp : 2 / (2 - (2 - 2 / p)) = p := by field_simp; ring
  have hp3_exp : (2 - (2 - 2 / p)) / (2 - 2 / p) = r := by dsimp [r]; field_simp; ring
  have hb := norm_add_rpow_add_norm_sub_rpow_le_right
    ⟨by rw [sub_pos, div_lt_iff₀ hp0]; linarith, by linarith [(one_lt_div hp0).2 hp₂]⟩ u v
  rw [hp1_exp, hp2_exp, hp3_exp] at hb
  have hrpow : (‖u + v‖ ^ p + ‖u - v‖ ^ p) ^ r ≤
      2 ^ (r - 1) * ((‖u + v‖ ^ p) ^ r + (‖u - v‖ ^ p) ^ r) := by
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow ⟨‖u + v‖ ^ p, by positivity⟩
      ⟨‖u - v‖ ^ p, by positivity⟩ ((one_le_inv₀ hp_sub).2 (by linarith))
  have hpow : (‖u + v‖ ^ p + ‖u - v‖ ^ p) ^ r ≤ (2 * (‖u‖ ^ p + ‖v‖ ^ p)) ^ r := by
    refine hrpow.trans ?_
    rw [← Real.rpow_mul (norm_nonneg _), ← Real.rpow_mul (norm_nonneg _)]
    refine (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg zero_le_two _)).trans_eq ?_
    rw [Real.mul_rpow zero_le_two (by positivity), Real.rpow_sub_one two_ne_zero]; ring
  have hinv := Real.rpow_le_rpow (Real.rpow_nonneg huv r) hpow (inv_nonneg.2 hr_pos.le)
  rwa [Real.rpow_rpow_inv huv hr_pos.ne', Real.rpow_rpow_inv (by positivity) hr_pos.ne'] at hinv

/-- **Clarkson's inequality on `[X₀, X₁]_{2/p - 1}` for `1 < p < 2` (left endpoint).** -/
theorem norm_add_rpow_add_norm_sub_rpow_le_two_mul_left [InnerProductSpaceable X₀]
    {C : CompatibleCouple ℂ X₀ X₁ V} {p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2)
    (u v : C.ComplexMethodSpace (2 / p - 1)) :
    ‖u + v‖ ^ p + ‖u - v‖ ^ p ≤ 2 * (‖u‖ ^ p + ‖v‖ ^ p) := by
  have hθ : 1 - (2 / p - 1) = 2 - 2 / p := by ring
  let e := swapOfSubEq C hθ
  have h := norm_add_rpow_add_norm_sub_rpow_le_two_mul_right hp₁ hp₂ (e u) (e v)
  rwa [← map_add, ← map_sub, e.norm_map, e.norm_map, e.norm_map, e.norm_map] at h

end Couple

end TauCeti.CompatibleCouple.ComplexMethodSpace

end
