/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Equality
-- Proof-only: a convex set has positive volume exactly when its interior is nonempty, and
-- containment in an open convex set from directional images.
import TauCeti.Analysis.Convex.Measure
import TauCeti.Analysis.Convex.Separation

/-!
# Equality in Brunn–Minkowski for convex bodies: homothety

Let `K` and `L` be compact convex sets of positive volume in a finite-dimensional Euclidean space
and let `0 < θ < 1`. The multiplicative Brunn–Minkowski inequality
`volume K ^ (1 - θ) * volume L ^ θ ≤ volume ((1 - θ) • K + θ • L)` is an equality exactly when `L`
is a translate of `K`. For `c, d > 0` and `n = finrank ℝ E ≥ 1`, the additive inequality
`c * volume A ^ (1 / n) + d * volume B ^ (1 / n) ≤ volume (c • A + d • B) ^ (1 / n)` is an
equality exactly when `B = v +ᵥ r • A` for a vector `v` and a scalar `r > 0`. Taking `c = 1 - θ`
and `d = θ` gives the weighted form, and `c = d = 1` the unweighted form.

The proof completes the argument of Kneser and Süss. Under multiplicative equality, the height
quantiles of `K` and `L` along each unit vector `u` differ by a constant
(`Convex.exists_quantile_map_inner_cond_eq_add_of_volume_le`). Averaging over the levels identifies
this constant as `⟪u, v⟫`, where `v` is the difference of the centroids of `L` and `K`
(`TauCeti.setIntegral_quantile_map_inner_cond`). Since the quantiles sweep out the heights of
interior points, `interior L` and `v +ᵥ interior K` have the same heights along every unit
vector, so by separation of points from open convex sets they coincide
(`Convex.subset_of_image_inner_subset`). Passing to closures gives
`L = v +ᵥ K`. The additive equality case reduces to the multiplicative one by rescaling `A` and `B`
to unit volume.

The hypothesis of positive volume is equivalent to nonempty interior
(`Convex.addHaar_pos_iff_interior_nonempty`).

## Main results

* `Convex.exists_interior_eq_vadd_interior_of_volume_le`: for bounded Borel convex sets of positive
  volume, multiplicative equality forces the interiors to be translates.
* `Convex.volume_smul_add_smul_eq_iff`: for compact convex sets of positive volume, multiplicative
  equality holds exactly for translates.
* `Convex.volume_real_smul_add_smul_rpow_eq_iff`: for compact convex sets of positive volume,
  additive equality holds exactly for homothetic sets.

## References

* H. Kneser and W. Süss, *Die Volumina in linearen Scharen konvexer Körper*, Mat. Tidsskr. B
  (1932), 19–25.
* R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, 2nd ed., Cambridge University
  Press, 2014, Theorem 7.1.1 and its proof.
-/

public section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal Pointwise RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

variable {K L : Set E}

/-- **Translated interiors under Brunn–Minkowski equality.** Let `K` and `L` be bounded Borel convex
sets of positive volume and `0 < θ < 1`. If the volume of `(1 - θ) • K + θ • L` is at most
`volume K ^ (1 - θ) * volume L ^ θ`, that is, if the multiplicative Brunn–Minkowski inequality is
an equality, then the interior of `L` is a translate of the interior of `K`. -/
theorem _root_.Convex.exists_interior_eq_vadd_interior_of_volume_le (hK : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hKm : MeasurableSet K) (hK0 : volume K ≠ 0)
    (hL : Convex ℝ L) (hLb : Bornology.IsBounded L) (hLm : MeasurableSet L)
    (hL0 : volume L ≠ 0) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hvol : volume ((1 - θ) • K + θ • L) ≤ volume K ^ (1 - θ) * volume L ^ θ) :
    ∃ v : E, interior L = v +ᵥ interior K := by
  set v := ∫ x, x ∂(volume[|L]) - ∫ x, x ∂(volume[|K])
  have hKi := (hK.addHaar_pos_iff_interior_nonempty (μ := volume)).1 (pos_iff_ne_zero.2 hK0)
  have hLi := (hL.addHaar_pos_iff_interior_nonempty (μ := volume)).1 (pos_iff_ne_zero.2 hL0)
  -- Along every unit vector, the heights of the interior points of `L` and of `v +ᵥ interior K`
  -- agree: the height quantiles differ by a constant, which is the difference of the means.
  have himage (u : E) (hu : ‖u‖ = 1) :
      (fun x ↦ ⟪u, x⟫) '' interior L = (fun x ↦ ⟪u, x⟫) '' (v +ᵥ interior K) := by
    obtain ⟨c, hc⟩ := hK.exists_quantile_map_inner_cond_eq_add_of_volume_le hKb hKm hK0 hL hLb
      hLm hL0 hu hθ₀ hθ₁ hvol
    have hcv : c = ⟪u, v⟫ := by
      have h := setIntegral_congr_fun (μ := volume) measurableSet_Ioo hc
      rw [integral_add (integrableOn_quantile_map_inner_cond u hKb hKm hK0)
        (integrable_const c), setIntegral_const, setIntegral_quantile_map_inner_cond u hLb hLm hL0,
        setIntegral_quantile_map_inner_cond u hKb hKm hK0] at h
      simp only [measureReal_def, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one,
        ENNReal.toReal_one, one_smul] at h
      rw [inner_sub_right]
      linarith
    rw [← hL.image_quantile_map_inner_cond_Ioo hu hL0 hLb.measure_lt_top.ne, hc.image_eq,
      ← image_image (· + c), hK.image_quantile_map_inner_cond_Ioo hu hK0 hKb.measure_lt_top.ne,
      ← image_vadd, image_image, image_image]
    simp only [vadd_eq_add, inner_add_right, hcv, add_comm]
  exact ⟨v, Subset.antisymm ((hK.interior.vadd v).subset_of_image_inner_subset
    (isOpen_interior.vadd v) hKi.vadd_set fun u hu ↦ (himage u hu).le)
    (hL.interior.subset_of_image_inner_subset isOpen_interior hLi fun u hu ↦ (himage u hu).ge)⟩

/-- **Brunn–Minkowski equality for convex bodies, multiplicative form.** Let `K` and `L` be compact
convex sets of positive volume and `0 < θ < 1`. If the multiplicative Brunn–Minkowski inequality
`volume K ^ (1 - θ) * volume L ^ θ ≤ volume ((1 - θ) • K + θ • L)` is an equality, then `L` is a
translate of `K`. -/
theorem _root_.Convex.exists_eq_vadd_of_volume_le (hK : Convex ℝ K) (hKc : IsCompact K)
    (hK0 : volume K ≠ 0) (hL : Convex ℝ L) (hLc : IsCompact L) (hL0 : volume L ≠ 0) {θ : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hvol : volume ((1 - θ) • K + θ • L) ≤ volume K ^ (1 - θ) * volume L ^ θ) :
    ∃ v : E, L = v +ᵥ K := by
  obtain ⟨v, hv⟩ := hK.exists_interior_eq_vadd_interior_of_volume_le hKc.isBounded
    hKc.measurableSet hK0 hL hLc.isBounded hLc.measurableSet hL0 hθ₀ hθ₁ hvol
  have hKi := (hK.addHaar_pos_iff_interior_nonempty (μ := volume)).1 (pos_iff_ne_zero.2 hK0)
  have hLi := (hL.addHaar_pos_iff_interior_nonempty (μ := volume)).1 (pos_iff_ne_zero.2 hL0)
  refine ⟨v, ?_⟩
  rw [← hLc.isClosed.closure_eq, ← hL.closure_interior_eq_closure_of_nonempty_interior hLi, hv,
    closure_vadd, hK.closure_interior_eq_closure_of_nonempty_interior hKi,
    hKc.isClosed.closure_eq]

/-- **Equality cases of multiplicative Brunn–Minkowski for convex bodies.** Let `K` and `L` be
compact convex sets of positive volume and `0 < θ < 1`. Then
`volume ((1 - θ) • K + θ • L) = volume K ^ (1 - θ) * volume L ^ θ` exactly when `L` is a translate
of `K`. -/
theorem _root_.Convex.volume_smul_add_smul_eq_iff (hK : Convex ℝ K) (hKc : IsCompact K)
    (hK0 : volume K ≠ 0) (hL : Convex ℝ L) (hLc : IsCompact L) (hL0 : volume L ≠ 0) {θ : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    volume ((1 - θ) • K + θ • L) = volume K ^ (1 - θ) * volume L ^ θ ↔ ∃ v : E, L = v +ᵥ K := by
  refine ⟨fun h ↦ hK.exists_eq_vadd_of_volume_le hKc hK0 hL hLc hL0 hθ₀ hθ₁ h.le, ?_⟩
  rintro ⟨v, rfl⟩
  have hθK : θ • (v +ᵥ K) = θ • v +ᵥ θ • K := by
    simp only [← image_smul, ← image_vadd, image_image, vadd_eq_add, smul_add]
  rw [hθK, add_vadd_comm, ← hK.add_smul (by linarith) hθ₀.le, sub_add_cancel, one_smul,
    measure_vadd, measure_vadd, ← ENNReal.rpow_add _ _ hK0 hKc.measure_lt_top.ne, sub_add_cancel,
    ENNReal.rpow_one]

/-- **Brunn–Minkowski equality for convex bodies, additive form.** Let `A` and `B` be compact convex
sets of positive volume in a space of positive dimension `n`, and let `c, d > 0`. If the
Brunn–Minkowski inequality
`c * volume A ^ (1 / n) + d * volume B ^ (1 / n) ≤ volume (c • A + d • B) ^ (1 / n)` is an
equality, then `B` is homothetic to `A`: `B = v +ᵥ r • A` for some vector `v` and some `r > 0`. -/
theorem _root_.Convex.exists_eq_vadd_smul_of_volume_real_rpow_le
    (hn : Module.finrank ℝ E ≠ 0) {A B : Set E} (hA : Convex ℝ A) (hAc : IsCompact A)
    (hA0 : volume A ≠ 0) (hB : Convex ℝ B) (hBc : IsCompact B) (hB0 : volume B ≠ 0) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d)
    (h : volume.real (c • A + d • B) ^ ((Module.finrank ℝ E : ℝ)⁻¹) ≤
      c * volume.real A ^ ((Module.finrank ℝ E : ℝ)⁻¹) +
        d * volume.real B ^ ((Module.finrank ℝ E : ℝ)⁻¹)) :
    ∃ v : E, ∃ r : ℝ, 0 < r ∧ B = v +ᵥ r • A := by
  set n := Module.finrank ℝ E
  have hVA : 0 < volume.real A := ENNReal.toReal_pos hA0 hAc.measure_lt_top.ne
  have hVB : 0 < volume.real B := ENNReal.toReal_pos hB0 hBc.measure_lt_top.ne
  set a := volume.real A ^ (n : ℝ)⁻¹
  set b := volume.real B ^ (n : ℝ)⁻¹
  have ha : 0 < a := Real.rpow_pos_of_pos hVA _
  have hb : 0 < b := Real.rpow_pos_of_pos hVB _
  set S := c * a + d * b
  have hS : 0 < S := by positivity
  set θ := d * b / S with hθ
  have hθ₀ : 0 < θ := by positivity
  have hθ₁ : θ < 1 := (div_lt_one hS).2 (lt_add_of_pos_left _ (mul_pos hc ha))
  have h1θ : 1 - θ = c * a / S := by
    rw [eq_div_iff hS.ne', sub_mul, one_mul, div_mul_cancel₀ _ hS.ne']
    ring
  -- Rescale `A` and `B` to unit volume.
  have hunit {s : Set E} (hsc : IsCompact s) (hVs : 0 < volume.real s) :
      volume ((volume.real s ^ (n : ℝ)⁻¹)⁻¹ • s) = 1 := by
    rw [addHaar_smul_of_nonneg _ (inv_nonneg.2 (Real.rpow_nonneg hVs.le _)),
      ← ofReal_measureReal hsc.measure_lt_top.ne, ← ENNReal.ofReal_mul (by positivity), inv_pow,
      Real.rpow_inv_natCast_pow hVs.le hn, inv_mul_cancel₀ hVs.ne', ENNReal.ofReal_one]
  have hA1 : volume (a⁻¹ • A) = 1 := hunit hAc hVA
  have hB1 : volume (b⁻¹ • B) = 1 := hunit hBc hVB
  have hset : (1 - θ) • a⁻¹ • A + θ • b⁻¹ • B = S⁻¹ • (c • A + d • B) := by
    rw [smul_add, smul_smul, smul_smul, smul_smul, smul_smul, h1θ]
    congr 2
    · field_simp
    · rw [hθ]
      field_simp
  have hM : volume ((1 - θ) • a⁻¹ • A + θ • b⁻¹ • B) ≤
      volume (a⁻¹ • A) ^ (1 - θ) * volume (b⁻¹ • B) ^ θ := by
    have hMc : IsCompact (c • A + d • B) := (hAc.smul c).add (hBc.smul d)
    have hle : volume.real (c • A + d • B) ≤ S ^ n := by
      calc volume.real (c • A + d • B) = (volume.real (c • A + d • B) ^ (n : ℝ)⁻¹) ^ n :=
            (Real.rpow_inv_natCast_pow measureReal_nonneg hn).symm
        _ ≤ S ^ n := pow_le_pow_left₀ (Real.rpow_nonneg measureReal_nonneg _) h n
    rw [hA1, hB1, ENNReal.one_rpow, ENNReal.one_rpow, one_mul, hset,
      addHaar_smul_of_nonneg _ (inv_nonneg.2 hS.le), ← ofReal_measureReal hMc.measure_lt_top.ne,
      ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_one, inv_pow,
      inv_mul_le_iff₀ (by positivity), mul_one]
    exact hle
  obtain ⟨v, hv⟩ := (hA.smul a⁻¹).exists_eq_vadd_of_volume_le (hAc.smul a⁻¹) (hA1 ▸ one_ne_zero)
    (hB.smul b⁻¹) (hBc.smul b⁻¹) (hB1 ▸ one_ne_zero) hθ₀ hθ₁ hM
  refine ⟨b • v, b / a, div_pos hb ha, ?_⟩
  rw [← smul_inv_smul₀ hb.ne' B, hv]
  simp only [← image_smul, ← image_vadd, image_image, vadd_eq_add, smul_add, smul_smul,
    div_eq_mul_inv]

/-- **Equality cases of Brunn–Minkowski for convex bodies.** Let `A` and `B` be compact convex sets
of positive volume in a space of positive dimension `n`, and let `c, d > 0`. Then
`volume (c • A + d • B) ^ (1 / n) = c * volume A ^ (1 / n) + d * volume B ^ (1 / n)` exactly when
`B` is homothetic to `A`, that is, `B = v +ᵥ r • A` for some vector `v` and some `r > 0`. -/
theorem _root_.Convex.volume_real_smul_add_smul_rpow_eq_iff
    (hn : Module.finrank ℝ E ≠ 0) {A B : Set E} (hA : Convex ℝ A) (hAc : IsCompact A)
    (hA0 : volume A ≠ 0) (hB : Convex ℝ B) (hBc : IsCompact B) (hB0 : volume B ≠ 0) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) :
    volume.real (c • A + d • B) ^ ((Module.finrank ℝ E : ℝ)⁻¹) =
        c * volume.real A ^ ((Module.finrank ℝ E : ℝ)⁻¹) +
          d * volume.real B ^ ((Module.finrank ℝ E : ℝ)⁻¹) ↔
      ∃ v : E, ∃ r : ℝ, 0 < r ∧ B = v +ᵥ r • A := by
  refine ⟨fun h ↦ hA.exists_eq_vadd_smul_of_volume_real_rpow_le hn hAc hA0 hB hBc hB0 hc hd h.le,
    ?_⟩
  rintro ⟨v, r, hr, rfl⟩
  have hscale {k : ℝ} (hk : 0 ≤ k) : volume.real (k • A) ^ ((Module.finrank ℝ E : ℝ)⁻¹) =
      k * volume.real A ^ ((Module.finrank ℝ E : ℝ)⁻¹) := by
    rw [measureReal_def, ENNReal.toReal_rpow, volume_smul_rpow hn, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg k), abs_of_nonneg hk, ← ENNReal.toReal_rpow,
      measureReal_def]
  have hset : c • A + d • (v +ᵥ r • A) = d • v +ᵥ (c + d * r) • A := by
    have hdB : d • (v +ᵥ r • A) = d • v +ᵥ (d * r) • A := by
      simp only [← image_smul, ← image_vadd, image_image, vadd_eq_add, smul_add, smul_smul]
    rw [hdB, add_vadd_comm, hA.add_smul hc.le (by positivity)]
  have hvadd (w : E) (s : Set E) : volume.real (w +ᵥ s) = volume.real s := by
    rw [measureReal_def, measure_vadd, measureReal_def]
  rw [hset, hvadd, hvadd, hscale (by positivity), hscale hr.le]
  ring

end TauCeti
