/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.PiLp
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Symmetry
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Boas–Kosaki–McCarthy–Clarkson inequalities via complex interpolation

Whenever one endpoint of a compatible couple `(X₀, X₁)` of complex normed spaces satisfies the
parallelogram identity (`InnerProductSpaceable`), complex interpolation of the two-point Walsh
operator `(x, y) ↦ (x + y, x - y)` yields the **Boas–Kosaki–McCarthy–Clarkson inequalities** on the
interior complex interpolation spaces `[X₀, X₁]_θ` (`0 < θ < 1`), without completeness, density of
the intersection, or duality.

Concretely, `(x, y) ↦ (x + y, x - y)` has norm at most `1` from `ℓ¹_2(X₀)` to `ℓ^∞_2(X₀)` by the
triangle inequality, and norm `√2` from `ℓ²_2(X₁)` to `ℓ²_2(X₁)` by the parallelogram identity on
`X₁`. Interpolating between `(ℓ¹_2(X₀), ℓ²_2(X₁))` and `(ℓ^∞_2(X₀), ℓ²_2(X₁))` and identifying
both endpoints via `CompatibleCouple.piLpComplexMethodEquiv` gives, for `0 < θ < 1`,
`p = 2 / (2 - θ) ∈ (1, 2)`, and its Hölder conjugate `q = 2 / θ ∈ (2, ∞)`,

`‖u + v‖_θ ^ (2 / θ) + ‖u - v‖_θ ^ (2 / θ) ≤`
`  2 * (‖u‖_θ ^ (2 / (2 - θ)) + ‖v‖_θ ^ (2 / (2 - θ))) ^ ((2 - θ) / θ)`.

Specializing `θ` and applying the two-point power-mean inequality yields both classical Clarkson
regimes on `[X₀, X₁]_θ`, and symmetry (`ComplexMethodSpace.swap`) transfers all three bounds to the
case `[InnerProductSpaceable X₀]`:
* for `2 < q < ∞` (`θ = 2 / q`, e.g. `[S^∞, S²]_{2/q} = S^q`),
  `‖u + v‖ ^ q + ‖u - v‖ ^ q ≤ 2 ^ (q - 1) * (‖u‖ ^ q + ‖v‖ ^ q)`;
* for `1 < p < 2` (`θ = 2 - 2 / p`, e.g. `[S¹, S²]_{2 - 2/p} = S^p`), both McCarthy's `(p, p')`
  inequality and `‖u + v‖ ^ p + ‖u - v‖ ^ p ≤ 2 * (‖u‖ ^ p + ‖v‖ ^ p)`.

## Main results

* `TauCeti.CompatibleCouple.ComplexMethodSpace.norm_add_rpow_add_norm_sub_rpow_le_right` and
  `..._left`: the Boas–Kosaki–McCarthy inequality on `[X₀, X₁]_θ` when `X₁` (resp. `X₀`) satisfies
  the parallelogram identity.
* `TauCeti.CompatibleCouple.ComplexMethodSpace.norm_add_rpow_add_norm_sub_rpow_le_two_pow_right`
  and `..._left`: Clarkson's inequality for `2 < q` at `θ = 2 / q` (resp. `1 - 2 / q`).
* `TauCeti.CompatibleCouple.ComplexMethodSpace.norm_add_rpow_add_norm_sub_rpow_le_two_mul_right`
  and `..._left`: Clarkson's inequality for `1 < p < 2` at `θ = 2 - 2 / p` (resp. `2 / p - 1`).

## References

* R. P. Boas Jr., *Some uniformly convex spaces*, Bull. Amer. Math. Soc. **46** (1940), 304–311.
* C. A. McCarthy, *`c_p`*, Israel J. Math. **5** (1967), 249–271, §2.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223, Springer,
  1976, §5.1, Exercise 5.7.6.
* H. Kosaki, *Applications of the complex interpolation method to a von Neumann algebra:
  non-commutative `L^p`-spaces*, J. Funct. Anal. **56** (1984), 29–78, Theorem 5.1.
-/

public noncomputable section

open Set WithLp
open scoped ENNReal

namespace TauCeti.CompatibleCouple.ComplexMethodSpace

/-! ### The two-point sum-and-difference operator and its endpoint bounds -/

private instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩

private def clarksonPairCLM (p q : ℝ≥0∞) (X : Type*)
    [NormedAddCommGroup X] [NormedSpace ℂ X] :
    PiLp p (fun _ : Fin 2 ↦ X) →L[ℂ] PiLp q (fun _ : Fin 2 ↦ X) :=
  (PiLp.continuousLinearEquiv q ℂ (fun _ : Fin 2 ↦ X)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : Fin 2 ↦
      if i = 0 then PiLp.proj (𝕜 := ℂ) p (fun _ : Fin 2 ↦ X) 0 +
          PiLp.proj (𝕜 := ℂ) p (fun _ : Fin 2 ↦ X) 1
      else PiLp.proj (𝕜 := ℂ) p (fun _ : Fin 2 ↦ X) 0 -
          PiLp.proj (𝕜 := ℂ) p (fun _ : Fin 2 ↦ X) 1)

private theorem clarksonPairCLM_apply_zero (p q : ℝ≥0∞) {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] (x : PiLp p (fun _ : Fin 2 ↦ X)) :
    clarksonPairCLM p q X x 0 = x 0 + x 1 := by
  simp [clarksonPairCLM, PiLp.proj_apply]

private theorem clarksonPairCLM_apply_one (p q : ℝ≥0∞) {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] (x : PiLp p (fun _ : Fin 2 ↦ X)) :
    clarksonPairCLM p q X x 1 = x 0 - x 1 := by
  simp [clarksonPairCLM, PiLp.proj_apply]

private theorem norm_clarksonPairCLM_one_top_le {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] (x : PiLp 1 (fun _ : Fin 2 ↦ X)) :
    ‖clarksonPairCLM 1 ∞ X x‖ ≤ 1 * ‖x‖ := by
  have hx : ‖x‖ = ‖x 0‖ + ‖x 1‖ := by
    simp [PiLp.norm_eq_sum (p := 1) (by simp), Fin.sum_univ_two]
  rw [one_mul, hx, ← toLp_ofLp ∞ (clarksonPairCLM 1 ∞ X x), PiLp.norm_toLp]
  refine (pi_norm_le_iff_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 fun i ↦ ?_
  rcases i with ⟨_ | _ | n, hn⟩
  · exact (clarksonPairCLM_apply_zero 1 ∞ x).symm ▸ norm_add_le (x 0) (x 1)
  · exact (clarksonPairCLM_apply_one 1 ∞ x).symm ▸ norm_sub_le (x 0) (x 1)
  · omega

private theorem norm_clarksonPairCLM_two_two_le {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [InnerProductSpaceable X]
    (x : PiLp 2 (fun _ : Fin 2 ↦ X)) :
    ‖clarksonPairCLM 2 2 X x‖ ≤ (2 : ℝ) ^ ((1 : ℝ) / 2) * ‖x‖ := by
  have hpar : ‖x 0 + x 1‖ ^ (2 : ℝ) + ‖x 0 - x 1‖ ^ (2 : ℝ) =
      2 * (‖x 0‖ ^ (2 : ℝ) + ‖x 1‖ ^ (2 : ℝ)) := by
    simp only [Real.rpow_two, sq]
    exact InnerProductSpaceable.parallelogram_identity (x 0) (x 1)
  rw [PiLp.norm_eq_sum (p := 2) (by simp), PiLp.norm_eq_sum (p := 2) (by simp)]
  simp only [ENNReal.toReal_ofNat, Fin.sum_univ_two, clarksonPairCLM_apply_zero,
    clarksonPairCLM_apply_one]
  rw [hpar, Real.mul_rpow zero_le_two (by positivity)]

/-! ### Exponent arithmetic and compatibility on `CompatibleCouple.piLp` -/

private theorem inv_ofReal_two_div_two_sub {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    (ENNReal.ofReal (2 / (2 - θ)))⁻¹ =
      ENNReal.ofReal (1 - θ) * (1 : ℝ≥0∞)⁻¹ + ENNReal.ofReal θ * (2 : ℝ≥0∞)⁻¹ := by
  have h2 : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos zero_lt_two, ENNReal.ofReal_ofNat]
  rw [← ENNReal.ofReal_inv_of_pos (div_pos zero_lt_two (by linarith [hθ.2])), inv_one, mul_one,
    h2, ← ENNReal.ofReal_mul hθ.1.le,
    ← ENNReal.ofReal_add (sub_nonneg.2 hθ.2.le) (mul_nonneg hθ.1.le (by positivity))]
  congr 1
  rw [inv_div]
  ring

private theorem inv_ofReal_two_div {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    (ENNReal.ofReal (2 / θ))⁻¹ =
      ENNReal.ofReal (1 - θ) * (∞ : ℝ≥0∞)⁻¹ + ENNReal.ofReal θ * (2 : ℝ≥0∞)⁻¹ := by
  have h2 : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos zero_lt_two, ENNReal.ofReal_ofNat]
  rw [← ENNReal.ofReal_inv_of_pos (div_pos zero_lt_two hθ.1), ENNReal.inv_top, mul_zero,
    zero_add, h2, ← ENNReal.ofReal_mul hθ.1.le]
  congr 1; field_simp

private theorem add_rpow_le_two_rpow_mul {r s t : ℝ} (hr : 1 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (s + t) ^ r ≤ 2 ^ (r - 1) * (s ^ r + t ^ r) := by
  lift s to NNReal using hs
  lift t to NNReal using ht
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow s t hr

section Couple

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀]
  [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]

private def swapOfSubEq (C : CompatibleCouple ℂ X₀ X₁ V) {θ η : ℝ} (h : 1 - θ = η) :
    C.ComplexMethodSpace θ ≃ₗᵢ[ℂ] C.swap.ComplexMethodSpace η :=
  h ▸ swap C θ

omit [T1Space V] in
private theorem clarksonPair_compat (C : CompatibleCouple ℂ X₀ X₁ V)
    (x : (piLp 1 2 fun _ : Fin 2 ↦ C).inter) :
    (piLp ∞ 2 fun _ : Fin 2 ↦ C).fstToSum
        (clarksonPairCLM 1 ∞ X₀ ((piLp 1 2 fun _ : Fin 2 ↦ C).interFst x)) =
      (piLp ∞ 2 fun _ : Fin 2 ↦ C).sndToSum
        (clarksonPairCLM 2 2 X₁ ((piLp 1 2 fun _ : Fin 2 ↦ C).interSnd x)) := by
  apply (piLp ∞ 2 fun _ : Fin 2 ↦ C).sumSpace_ext
  have h (j : Fin 2) : C.embed₀ (x.1.1 j) = C.embed₁ (x.1.2 j) := by
    simpa using congr_fun ((piLp 1 2 fun _ : Fin 2 ↦ C).embed₀_interFst x) j
  ext i
  rcases i with ⟨_ | _ | n, hn⟩
  · change (piLp ∞ 2 fun _ : Fin 2 ↦ C).sumSpaceEmbed _ 0 =
      (piLp ∞ 2 fun _ : Fin 2 ↦ C).sumSpaceEmbed _ 0
    simp [clarksonPairCLM_apply_zero, h 0, h 1]
  · change (piLp ∞ 2 fun _ : Fin 2 ↦ C).sumSpaceEmbed _ 1 =
      (piLp ∞ 2 fun _ : Fin 2 ↦ C).sumSpaceEmbed _ 1
    simp [clarksonPairCLM_apply_one, h 0, h 1]
  · omega

private theorem piLpCoord_map_clarksonPair_zero {θ : ℝ} {C : CompatibleCouple ℂ X₀ X₁ V}
    {w : (piLp 1 2 fun _ : Fin 2 ↦ C).ComplexMethodSpace θ} {u v : C.ComplexMethodSpace θ}
    (hu : piLpCoord θ (fun _ : Fin 2 ↦ C) 0 w = u)
    (hv : piLpCoord θ (fun _ : Fin 2 ↦ C) 1 w = v) :
    piLpCoord θ (fun _ : Fin 2 ↦ C) 0
      (map θ (clarksonPairCLM 1 ∞ X₀) (clarksonPairCLM 2 2 X₁) (clarksonPair_compat C) w) =
        u + v := by
  have hu' : (piLp 1 2 fun _ : Fin 2 ↦ C).sumSpaceEmbed (toSum w) 0 =
      C.sumSpaceEmbed (toSum u) := by
    rw [← sumSpaceEmbed_toSum_piLpCoord θ (fun _ : Fin 2 ↦ C) 0, hu]
  have hv' : (piLp 1 2 fun _ : Fin 2 ↦ C).sumSpaceEmbed (toSum w) 1 =
      C.sumSpaceEmbed (toSum v) := by
    rw [← sumSpaceEmbed_toSum_piLpCoord θ (fun _ : Fin 2 ↦ C) 1, hv]
  obtain ⟨x₀, x₁, hx⟩ := (piLp 1 2 fun _ : Fin 2 ↦ C).exists_fstToSum_add_sndToSum_eq (toSum w)
  let T₀ := clarksonPairCLM 1 ∞ X₀
  let T₁ := clarksonPairCLM 2 2 X₁
  let f₀ := (piLp ∞ 2 fun _ : Fin 2 ↦ C).fstToSum.comp T₀
  let f₁ := (piLp ∞ 2 fun _ : Fin 2 ↦ C).sndToSum.comp T₁
  let L := (piLp 1 2 fun _ : Fin 2 ↦ C).sumLift f₀ f₁ (clarksonPair_compat C)
  have hmap : toSum (map θ T₀ T₁ (clarksonPair_compat C) w) = f₀ x₀ + f₁ x₁ :=
    (toSum_map T₀ T₁ (clarksonPair_compat C) w).trans <|
      (congrArg L hx.symm).trans <| (map_add L _ _).trans <|
        congr_arg₂ (· + ·) ((piLp 1 2 fun _ : Fin 2 ↦ C).sumLift_fstToSum f₀ f₁ _ x₀)
          ((piLp 1 2 fun _ : Fin 2 ↦ C).sumLift_sndToSum f₀ f₁ _ x₁)
  apply ComplexMethodSpace.ext
  apply C.sumSpaceEmbed_injective
  rw [sumSpaceEmbed_toSum_piLpCoord θ (fun _ : Fin 2 ↦ C) 0, hmap, map_add, map_add, map_add,
    ← hu', ← hv', ← hx]
  simp [f₀, f₁, T₀, T₁, clarksonPairCLM_apply_zero, add_add_add_comm]

private theorem piLpCoord_map_clarksonPair_one {θ : ℝ} {C : CompatibleCouple ℂ X₀ X₁ V}
    {w : (piLp 1 2 fun _ : Fin 2 ↦ C).ComplexMethodSpace θ} {u v : C.ComplexMethodSpace θ}
    (hu : piLpCoord θ (fun _ : Fin 2 ↦ C) 0 w = u)
    (hv : piLpCoord θ (fun _ : Fin 2 ↦ C) 1 w = v) :
    piLpCoord θ (fun _ : Fin 2 ↦ C) 1
      (map θ (clarksonPairCLM 1 ∞ X₀) (clarksonPairCLM 2 2 X₁) (clarksonPair_compat C) w) =
        u - v := by
  have hu' : (piLp 1 2 fun _ : Fin 2 ↦ C).sumSpaceEmbed (toSum w) 0 =
      C.sumSpaceEmbed (toSum u) := by
    rw [← sumSpaceEmbed_toSum_piLpCoord θ (fun _ : Fin 2 ↦ C) 0, hu]
  have hv' : (piLp 1 2 fun _ : Fin 2 ↦ C).sumSpaceEmbed (toSum w) 1 =
      C.sumSpaceEmbed (toSum v) := by
    rw [← sumSpaceEmbed_toSum_piLpCoord θ (fun _ : Fin 2 ↦ C) 1, hv]
  obtain ⟨x₀, x₁, hx⟩ := (piLp 1 2 fun _ : Fin 2 ↦ C).exists_fstToSum_add_sndToSum_eq (toSum w)
  let T₀ := clarksonPairCLM 1 ∞ X₀
  let T₁ := clarksonPairCLM 2 2 X₁
  let f₀ := (piLp ∞ 2 fun _ : Fin 2 ↦ C).fstToSum.comp T₀
  let f₁ := (piLp ∞ 2 fun _ : Fin 2 ↦ C).sndToSum.comp T₁
  let L := (piLp 1 2 fun _ : Fin 2 ↦ C).sumLift f₀ f₁ (clarksonPair_compat C)
  have hmap : toSum (map θ T₀ T₁ (clarksonPair_compat C) w) = f₀ x₀ + f₁ x₁ :=
    (toSum_map T₀ T₁ (clarksonPair_compat C) w).trans <|
      (congrArg L hx.symm).trans <| (map_add L _ _).trans <|
        congr_arg₂ (· + ·) ((piLp 1 2 fun _ : Fin 2 ↦ C).sumLift_fstToSum f₀ f₁ _ x₀)
          ((piLp 1 2 fun _ : Fin 2 ↦ C).sumLift_sndToSum f₀ f₁ _ x₁)
  apply ComplexMethodSpace.ext
  apply C.sumSpaceEmbed_injective
  rw [sumSpaceEmbed_toSum_piLpCoord θ (fun _ : Fin 2 ↦ C) 1, hmap, map_add, map_sub, map_sub,
    ← hu', ← hv', ← hx]
  simp [f₀, f₁, T₀, T₁, clarksonPairCLM_apply_one, add_sub_add_comm]

/-! ### Boas–Kosaki–McCarthy–Clarkson inequalities on `[X₀, X₁]_θ` -/

/-- **Boas–Kosaki–McCarthy–Clarkson inequality (right Hilbertian endpoint).**
If `X₁` satisfies the parallelogram identity (`InnerProductSpaceable X₁`) and `0 < θ < 1`, then for
every `u, v : [X₀, X₁]_θ`, with `p = 2 / (2 - θ) ∈ (1, 2)` and `q = 2 / θ ∈ (2, ∞)`,
`‖u + v‖ ^ (2 / θ) + ‖u - v‖ ^ (2 / θ) ≤`
`  2 * (‖u‖ ^ (2 / (2 - θ)) + ‖v‖ ^ (2 / (2 - θ))) ^ ((2 - θ) / θ)`. -/
theorem norm_add_rpow_add_norm_sub_rpow_le_right [InnerProductSpaceable X₁]
    {C : CompatibleCouple ℂ X₀ X₁ V} {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (u v : C.ComplexMethodSpace θ) :
    ‖u + v‖ ^ (2 / θ) + ‖u - v‖ ^ (2 / θ) ≤
      2 * (‖u‖ ^ (2 / (2 - θ)) + ‖v‖ ^ (2 / (2 - θ))) ^ ((2 - θ) / θ) := by
  set p := 2 / (2 - θ)
  set q := 2 / θ
  have hp1 : 1 < p := by rw [one_lt_div (by linarith [hθ.2])]; linarith [hθ.1]
  have hq2 : 2 < q := by rw [lt_div_iff₀ hθ.1]; linarith [hθ.2]
  have hp_pos : 0 < p := zero_lt_one.trans hp1
  have hq_pos : 0 < q := zero_lt_two.trans hq2
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.2 hp1.le⟩
  have : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.2 (one_lt_two.trans hq2).le⟩
  let eDom := piLpComplexMethodEquiv (q := ENNReal.ofReal p) hθ
    (inv_ofReal_two_div_two_sub hθ) (fun _ : Fin 2 ↦ C)
  let eCod := piLpComplexMethodEquiv (q := ENNReal.ofReal q) hθ
    (inv_ofReal_two_div hθ) (fun _ : Fin 2 ↦ C)
  let pair : PiLp (ENNReal.ofReal p) (fun _ : Fin 2 ↦ C.ComplexMethodSpace θ) :=
    toLp (ENNReal.ofReal p) (fun i : Fin 2 ↦ if i = 0 then u else v)
  let w := eDom.symm pair
  let Tw := map θ (clarksonPairCLM 1 ∞ X₀) (clarksonPairCLM 2 2 X₁) (clarksonPair_compat C) w
  have hTw : ‖eCod Tw‖ ≤ (2 : ℝ) ^ (θ / 2) * ‖pair‖ := by
    rw [eCod.norm_map, ← eDom.symm.norm_map pair]
    refine (norm_map_le _ _ _ ⟨hθ.1.le, hθ.2.le⟩ zero_le_one (by positivity)
      norm_clarksonPairCLM_one_top_le norm_clarksonPairCLM_two_two_le w).trans_eq ?_
    rw [Real.one_rpow, one_mul, ← Real.rpow_mul zero_le_two, one_div_mul_eq_div]
  have h0 : eCod Tw 0 = u + v := (piLpComplexMethodEquiv_apply _ _ _ Tw 0).trans <|
    piLpCoord_map_clarksonPair_zero
      (piLpCoord_piLpComplexMethodEquiv_symm hθ (inv_ofReal_two_div_two_sub hθ) _ pair 0)
      (piLpCoord_piLpComplexMethodEquiv_symm hθ (inv_ofReal_two_div_two_sub hθ) _ pair 1)
  have h1 : eCod Tw 1 = u - v := (piLpComplexMethodEquiv_apply _ _ _ Tw 1).trans <|
    piLpCoord_map_clarksonPair_one
      (piLpCoord_piLpComplexMethodEquiv_symm hθ (inv_ofReal_two_div_two_sub hθ) _ pair 0)
      (piLpCoord_piLpComplexMethodEquiv_symm hθ (inv_ofReal_two_div_two_sub hθ) _ pair 1)
  have hlhs : ‖u + v‖ ^ q + ‖u - v‖ ^ q = ‖eCod Tw‖ ^ q := by
    have hsum := congrArg (· ^ q) (PiLp.norm_eq_sum
      (p := ENNReal.ofReal q) (by rwa [ENNReal.toReal_ofReal hq_pos.le]) (eCod Tw))
    rw [ENNReal.toReal_ofReal hq_pos.le, one_div, Real.rpow_inv_rpow
      (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) hq_pos.ne',
      Fin.sum_univ_two, h0, h1] at hsum
    exact hsum.symm
  have hpair : ‖pair‖ ^ q = (‖u‖ ^ p + ‖v‖ ^ p) ^ ((2 - θ) / θ) := by
    have hp0 : pair 0 = u := rfl
    have hp1' : pair 1 = v := rfl
    rw [PiLp.norm_eq_sum (p := ENNReal.ofReal p) (by rwa [ENNReal.toReal_ofReal hp_pos.le]),
      ENNReal.toReal_ofReal hp_pos.le, Fin.sum_univ_two, hp0, hp1',
      ← Real.rpow_mul (by positivity), show 1 / p * q = (2 - θ) / θ by dsimp [p, q]; field_simp]
  rw [hlhs]
  refine (Real.rpow_le_rpow (norm_nonneg _) hTw hq_pos.le).trans_eq ?_
  rw [Real.mul_rpow (by positivity) (norm_nonneg _), ← Real.rpow_mul zero_le_two, hpair,
    show θ / 2 * q = 1 by dsimp [q]; field_simp [hθ.1.ne'], Real.rpow_one]

/-- **Boas–Kosaki–McCarthy–Clarkson inequality (left Hilbertian endpoint).**
If `X₀` satisfies the parallelogram identity (`InnerProductSpaceable X₀`) and `0 < θ < 1`, then for
every `u, v : [X₀, X₁]_θ`,
`‖u + v‖ ^ (2 / (1 - θ)) + ‖u - v‖ ^ (2 / (1 - θ)) ≤`
`  2 * (‖u‖ ^ (2 / (1 + θ)) + ‖v‖ ^ (2 / (1 + θ))) ^ ((1 + θ) / (1 - θ))`. -/
theorem norm_add_rpow_add_norm_sub_rpow_le_left [InnerProductSpaceable X₀]
    {C : CompatibleCouple ℂ X₀ X₁ V} {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (u v : C.ComplexMethodSpace θ) :
    ‖u + v‖ ^ (2 / (1 - θ)) + ‖u - v‖ ^ (2 / (1 - θ)) ≤
      2 * (‖u‖ ^ (2 / (1 + θ)) + ‖v‖ ^ (2 / (1 + θ))) ^ ((1 + θ) / (1 - θ)) := by
  have h1θ : 1 - θ ∈ Ioo 0 1 := ⟨sub_pos.2 hθ.2, sub_lt_self 1 hθ.1⟩
  have h := norm_add_rpow_add_norm_sub_rpow_le_right h1θ (swap C θ u) (swap C θ v)
  rw [← map_add, ← map_sub, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at h
  simpa [show 2 - (1 - θ) = 1 + θ by ring] using h

/-- **Clarkson's inequality on `[X₀, X₁]_{2/q}` for `2 < q` (right Hilbertian endpoint).**
When `X₁` satisfies the parallelogram identity and `2 < q`, the complex interpolation space at
`θ = 2 / q` satisfies `‖u + v‖ ^ q + ‖u - v‖ ^ q ≤ 2 ^ (q - 1) * (‖u‖ ^ q + ‖v‖ ^ q)`. -/
theorem norm_add_rpow_add_norm_sub_rpow_le_two_pow_right [InnerProductSpaceable X₁]
    {C : CompatibleCouple ℂ X₀ X₁ V} {q : ℝ} (hq : 2 < q) (u v : C.ComplexMethodSpace (2 / q)) :
    ‖u + v‖ ^ q + ‖u - v‖ ^ q ≤ 2 ^ (q - 1) * (‖u‖ ^ q + ‖v‖ ^ q) := by
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  have hθ : 2 / q ∈ Ioo 0 1 := ⟨div_pos zero_lt_two hq0, (div_lt_one hq0).2 hq⟩
  have hb := norm_add_rpow_add_norm_sub_rpow_le_right hθ u v
  rw [show 2 / (2 / q) = q by field_simp,
    show 2 / (2 - 2 / q) = q / (q - 1) by field_simp,
    show (2 - 2 / q) / (2 / q) = q - 1 by field_simp] at hb
  refine hb.trans ?_
  calc 2 * (‖u‖ ^ (q / (q - 1)) + ‖v‖ ^ (q / (q - 1))) ^ (q - 1)
    _ ≤ 2 * (2 ^ (q - 1 - 1) * ((‖u‖ ^ (q / (q - 1))) ^ (q - 1) +
          (‖v‖ ^ (q / (q - 1))) ^ (q - 1))) := by
        gcongr
        exact add_rpow_le_two_rpow_mul (by linarith) (by positivity) (by positivity)
    _ = 2 ^ (q - 1) * (‖u‖ ^ q + ‖v‖ ^ q) := by
        rw [← Real.rpow_mul (norm_nonneg u), ← Real.rpow_mul (norm_nonneg v),
          div_mul_cancel₀ q hq1.ne', ← mul_assoc,
          show (2 : ℝ) * 2 ^ (q - 1 - 1) = (2 : ℝ) ^ (1 : ℝ) * 2 ^ (q - 1 - 1) by simp,
          ← Real.rpow_add zero_lt_two]
        ring_nf

/-- **Clarkson's inequality on `[X₀, X₁]_{1 - 2/q}` for `2 < q` (left Hilbertian endpoint).** -/
theorem norm_add_rpow_add_norm_sub_rpow_le_two_pow_left [InnerProductSpaceable X₀]
    {C : CompatibleCouple ℂ X₀ X₁ V} {q : ℝ} (hq : 2 < q)
    (u v : C.ComplexMethodSpace (1 - 2 / q)) :
    ‖u + v‖ ^ q + ‖u - v‖ ^ q ≤ 2 ^ (q - 1) * (‖u‖ ^ q + ‖v‖ ^ q) := by
  let e := swapOfSubEq C (by ring : 1 - (1 - 2 / q) = 2 / q)
  have h := norm_add_rpow_add_norm_sub_rpow_le_two_pow_right hq (e u) (e v)
  rwa [← map_add, ← map_sub, e.norm_map, e.norm_map, e.norm_map, e.norm_map] at h

/-- **Clarkson's inequality on `[X₀, X₁]_{2 - 2/p}` for `1 < p < 2` (right Hilbertian endpoint).**
When `X₁` satisfies the parallelogram identity and `1 < p < 2`, the complex interpolation space at
`θ = 2 - 2 / p` satisfies `‖u + v‖ ^ p + ‖u - v‖ ^ p ≤ 2 * (‖u‖ ^ p + ‖v‖ ^ p)`. -/
theorem norm_add_rpow_add_norm_sub_rpow_le_two_mul_right [InnerProductSpaceable X₁]
    {C : CompatibleCouple ℂ X₀ X₁ V} {p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2)
    (u v : C.ComplexMethodSpace (2 - 2 / p)) :
    ‖u + v‖ ^ p + ‖u - v‖ ^ p ≤ 2 * (‖u‖ ^ p + ‖v‖ ^ p) := by
  have hp0 : 0 < p := zero_lt_one.trans hp₁
  have hp_sub : 0 < p - 1 := sub_pos.2 hp₁
  have hθ : 2 - 2 / p ∈ Ioo 0 1 :=
    ⟨by rw [sub_pos, div_lt_iff₀ hp0]; linarith, by linarith [(one_lt_div hp0).2 hp₂]⟩
  set r := (p - 1)⁻¹
  have hr_pos : 0 < r := inv_pos.2 hp_sub
  have hr1 : 1 ≤ r := (one_le_inv₀ hp_sub).2 (by linarith)
  have hb := norm_add_rpow_add_norm_sub_rpow_le_right hθ u v
  rw [show 2 / (2 - 2 / p) = p * r by dsimp [r]; field_simp,
    show 2 / (2 - (2 - 2 / p)) = p by field_simp; ring,
    show (2 - (2 - 2 / p)) / (2 - 2 / p) = r by dsimp [r]; field_simp; ring] at hb
  have hpow : (‖u + v‖ ^ p + ‖u - v‖ ^ p) ^ r ≤ (2 * (‖u‖ ^ p + ‖v‖ ^ p)) ^ r := by
    calc (‖u + v‖ ^ p + ‖u - v‖ ^ p) ^ r
      _ ≤ 2 ^ (r - 1) * ((‖u + v‖ ^ p) ^ r + (‖u - v‖ ^ p) ^ r) :=
          add_rpow_le_two_rpow_mul hr1 (by positivity) (by positivity)
      _ = 2 ^ (r - 1) * (‖u + v‖ ^ (p * r) + ‖u - v‖ ^ (p * r)) := by
          rw [← Real.rpow_mul (norm_nonneg _), ← Real.rpow_mul (norm_nonneg _)]
      _ ≤ 2 ^ (r - 1) * (2 * (‖u‖ ^ p + ‖v‖ ^ p) ^ r) := by gcongr
      _ = (2 * (‖u‖ ^ p + ‖v‖ ^ p)) ^ r := by
          rw [Real.mul_rpow zero_le_two (by positivity), ← mul_assoc,
            show (2 : ℝ) ^ (r - 1) * 2 = 2 ^ (r - 1) * (2 : ℝ) ^ (1 : ℝ) by simp,
            ← Real.rpow_add zero_lt_two, sub_add_cancel]
  have hinv := Real.rpow_le_rpow (by positivity) hpow (inv_nonneg.2 hr_pos.le)
  rwa [Real.rpow_rpow_inv (by positivity) hr_pos.ne',
    Real.rpow_rpow_inv (by positivity) hr_pos.ne'] at hinv

/-- **Clarkson's inequality on `[X₀, X₁]_{2/p - 1}` for `1 < p < 2`** (left Hilbertian
endpoint). -/
theorem norm_add_rpow_add_norm_sub_rpow_le_two_mul_left [InnerProductSpaceable X₀]
    {C : CompatibleCouple ℂ X₀ X₁ V} {p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2)
    (u v : C.ComplexMethodSpace (2 / p - 1)) :
    ‖u + v‖ ^ p + ‖u - v‖ ^ p ≤ 2 * (‖u‖ ^ p + ‖v‖ ^ p) := by
  let e := swapOfSubEq C (by ring : 1 - (2 / p - 1) = 2 - 2 / p)
  have h := norm_add_rpow_add_norm_sub_rpow_le_two_mul_right hp₁ hp₂ (e u) (e v)
  rwa [← map_add, ← map_sub, e.norm_map, e.norm_map, e.norm_map, e.norm_map] at h

end Couple

end TauCeti.CompatibleCouple.ComplexMethodSpace

end
