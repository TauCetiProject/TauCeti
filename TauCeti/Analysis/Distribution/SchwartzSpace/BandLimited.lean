/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SchwartzSpace.WeightedPlancherel
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.SpecificLimits.DyadicSum
import TauCeti.MeasureTheory.Integral.CalderonZygmund.TranslationTail

/-!
# Kernels of band-limited symbols and Hörmander's condition

Let `V` be a finite-dimensional real inner product space of dimension `n`, `b` an orthonormal
basis of `V`, and `2N > n`. Call a Schwartz function `σ` on `V`, with values in a complex Hilbert
space, *adapted to the scale `t > 0` with constant `A`* if it vanishes outside `closedBall 0 t`
and its derivatives of order `k ≤ N` along `b` are bounded by `A t ^ (-k)`. A smooth symbol `m`
satisfying the Mihlin conditions `‖∂^α m(ξ)‖ ≤ A ‖ξ‖ ^ (-|α|)`, cut off by a Littlewood–Paley
partition of unity to the annulus `‖ξ‖ ~ 2 ^ j`, gives such a piece at a scale comparable to
`2 ^ j`, with constant a fixed multiple of `A`.

The estimates of `SchwartzMap.exists_setIntegral_norm_fourierInv_le` and
`SchwartzMap.exists_integral_norm_fourierInv_le` then become scale-invariant bounds on the kernel
`𝓕⁻ σ`, with constants independent of `σ`, `t` and `A`:

* the tail bound `∫_{‖x‖ > R} ‖𝓕⁻ σ x‖ dx ≤ C A (t R) ^ (n/2 - N)`;
* the smoothness bound `∫ ‖𝓕⁻ σ (x + h) - 𝓕⁻ σ x‖ dx ≤ C A t ‖h‖`. Translating the kernel by
  `h` is controlled by the symbol `⟪h, ξ⟫ σ ξ`, whose derivatives the Leibniz rule
  `SchwartzMap.iterate_lineDerivOp_smulLeftCLM_clm` bounds.

For pieces `σ j` adapted to the dyadic scales `2 ^ j`, `j ∈ s`, the smoothness bound is the
better one when `2 ^ j ‖h‖ ≤ 1` and the tail bound when `2 ^ j ‖h‖ > 1`. Summing the better of the
two over `j` (`TauCeti.sum_min_zpow_mul_rpow_neg_le`) gives **Hörmander's condition**

`∫_{‖x‖ > 2 ‖h‖} ‖K (x - h) - K x‖ dx ≤ C A` for `K = 𝓕⁻ (∑ j ∈ s, σ j)`,

with `C` independent of the finite set `s` and of `h`. This is the kernel estimate in the proof
of the Mihlin–Hörmander multiplier theorem: the finite partial sums of the Littlewood–Paley pieces
of a Mihlin symbol have kernels satisfying Hörmander's condition uniformly in the partial sum.

## Main declarations

* `SchwartzMap.norm_toLp_two_le_of_support_subset_closedBall`: the `L²` norm of a bounded
  Schwartz function vanishing outside a ball.
* `SchwartzMap.exists_setIntegral_norm_fourierInv_le_of_support_subset`: the tail bound.
* `SchwartzMap.exists_integral_norm_fourierInv_add_sub_le_of_support_subset`: the smoothness
  bound.
* `SchwartzMap.exists_setIntegral_norm_fourierInv_sub_sub_le_of_support_subset`: Hörmander's
  condition for one band-limited piece, the better of the smoothness and tail bounds.
* `SchwartzMap.exists_setIntegral_norm_fourierInv_sum_sub_sub_le`: Hörmander's condition for
  dyadic sums.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Section 6.2 (proof of Theorem 6.2.7).
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter IV,
  §3.
* L. Hörmander, *Estimates for translation invariant operators in Lᵖ spaces*, Acta Math. **104**
  (1960), 93–140.
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace Real LineDeriv ENNReal
open FourierTransform MeasureTheory Metric Module Function LineDeriv

namespace SchwartzMap

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section Real

variable [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A Schwartz function bounded by `M` and vanishing outside `closedBall 0 t` has `L²` norm at
most `M √|B(0, 1)| t ^ (n/2)`. -/
theorem norm_toLp_two_le_of_support_subset_closedBall (f : 𝓢(V, H)) {t M : ℝ} (ht : 0 ≤ t)
    (hf : support f ⊆ closedBall 0 t) (hfM : ∀ ξ, ‖f ξ‖ ≤ M) :
    ‖f.toLp 2‖ ≤ M * √(volume.real (ball (0 : V) 1)) * t ^ ((finrank ℝ V : ℝ) / 2) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hfM 0)
  have hvol : volume (closedBall (0 : V) t) =
      ENNReal.ofReal (t ^ finrank ℝ V * volume.real (ball (0 : V) 1)) := by
    rw [Measure.addHaar_closedBall _ _ ht, ← ofReal_measureReal,
      ← ENNReal.ofReal_mul (by positivity)]
  have hle := eLpNorm_le_of_ae_bound (p := 2) (μ := volume.restrict (closedBall (0 : V) t))
    f.continuous.aestronglyMeasurable (.of_forall hfM)
  rw [eLpNorm_restrict_eq_of_support_subset f.continuous.aestronglyMeasurable hf,
    Measure.restrict_apply_univ, hvol, ENNReal.toReal_ofNat,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ← ENNReal.ofReal_mul (by positivity)] at hle
  rw [norm_toLp]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (hle.trans_eq ?_)
  congr 1
  rw [Real.mul_rpow (by positivity) measureReal_nonneg, ← Real.rpow_natCast, ← Real.rpow_mul ht,
    Real.sqrt_eq_rpow, one_div, div_eq_mul_inv]
  ring

/-- If the `k`-th derivatives of `f` along an orthonormal basis `b` are bounded by `M` and `f`
vanishes outside `closedBall 0 t`, the root of the sum of their squared `L²` norms is at most
`√#ι M √|B(0, 1)| t ^ (n/2)`. -/
private theorem sqrt_sum_norm_toLp_iterate_lineDerivOp_sq_le {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (f : 𝓢(V, H)) (k : ℕ) {t M : ℝ} (ht : 0 ≤ t) (hM : 0 ≤ M)
    (hf : tsupport f ⊆ closedBall 0 t) (hfM : ∀ i ξ, ‖(∂_{b i})^[k] f ξ‖ ≤ M) :
    √(∑ i, ‖((∂_{b i})^[k] f).toLp 2‖ ^ 2) ≤
      √(Fintype.card ι) * (M * √(volume.real (ball (0 : V) 1)) * t ^ ((finrank ℝ V : ℝ) / 2)) := by
  have hB (i : ι) := norm_toLp_two_le_of_support_subset_closedBall _ ht ((subset_tsupport _).trans
    ((iteratedLineDerivOp_const_eq_iter_lineDerivOp k (b i) f ▸
      tsupport_iteratedLineDerivOp_subset _ f).trans hf)) (hfM i)
  rw [← Real.sqrt_sq (by positivity : 0 ≤ M * √(volume.real (ball (0 : V) 1)) *
    t ^ ((finrank ℝ V : ℝ) / 2)), ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ((Finset.sum_le_sum fun i _ ↦
    pow_le_pow_left₀ (norm_nonneg _) (hB i) 2).trans_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- On a function vanishing outside `closedBall 0 t`, multiplication by a continuous linear
functional `L` costs at most the factor `t ‖L‖`. -/
private theorem norm_clm_smul_le_of_tsupport_subset {g : V → H} {t : ℝ}
    (hg : tsupport g ⊆ closedBall 0 t) (L : V →L[ℝ] ℝ) (ξ : V) :
    ‖L ξ • g ξ‖ ≤ t * ‖L‖ * ‖g ξ‖ := by
  by_cases hξ : ξ ∈ tsupport g
  · rw [norm_smul]
    gcongr
    refine (L.le_opNorm ξ).trans ?_
    rw [mul_comm t]
    gcongr
    simpa using hg hξ
  · simp [image_eq_zero_of_notMem_tsupport hξ]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- For `σ` vanishing outside `closedBall 0 t` and `‖v‖ ≤ 1`, the Leibniz rule bounds the
`(k + 1)`-st derivative of `L σ` along `v` by
`t ‖L‖ ‖∂_v^(k+1) σ‖ + (k + 1) ‖L‖ ‖∂_v^k σ‖`. -/
private theorem norm_iterate_lineDerivOp_smulLeftCLM_clm_le (σ : 𝓢(V, H)) {t : ℝ}
    (hσ : tsupport σ ⊆ closedBall 0 t) {v : V} (hv : ‖v‖ ≤ 1) (L : V →L[ℝ] ℝ) (k : ℕ) (ξ : V) :
    ‖(∂_{v})^[k + 1] (smulLeftCLM H L σ) ξ‖ ≤
      t * ‖L‖ * ‖(∂_{v})^[k + 1] σ ξ‖ + (k + 1) * ‖L‖ * ‖(∂_{v})^[k] σ ξ‖ := by
  rw [iterate_lineDerivOp_smulLeftCLM_clm, add_apply, smul_apply,
    smulLeftCLM_apply_apply L.hasTemperateGrowth]
  refine (norm_add_le _ _).trans (add_le_add (norm_clm_smul_le_of_tsupport_subset
    ((iteratedLineDerivOp_const_eq_iter_lineDerivOp (k + 1) v σ ▸
      tsupport_iteratedLineDerivOp_subset _ σ).trans hσ) L ξ) ?_)
  rw [norm_smul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  gcongr
  exact (L.le_opNorm v).trans (mul_le_of_le_one_right (norm_nonneg _) hv)

/-- If `σ` is bounded by `M` and vanishes outside `closedBall 0 t`, then multiplying it by a
continuous linear functional `L` gives `L²` norm at most `t ‖L‖ M √|B(0, 1)| t ^ (n/2)`. -/
private theorem norm_toLp_smulLeftCLM_clm_le (σ : 𝓢(V, H)) {t M : ℝ} (ht : 0 ≤ t)
    (hσ : tsupport σ ⊆ closedBall 0 t) (hσM : ∀ ξ, ‖σ ξ‖ ≤ M) (L : V →L[ℝ] ℝ) :
    ‖(smulLeftCLM H L σ).toLp 2‖ ≤
      t * ‖L‖ * M * √(volume.real (ball (0 : V) 1)) * t ^ ((finrank ℝ V : ℝ) / 2) := by
  refine norm_toLp_two_le_of_support_subset_closedBall _ ht ((subset_tsupport _).trans
    ((tsupport_smulLeftCLM_subset _ σ).trans (Set.inter_subset_left.trans hσ))) fun ξ ↦ ?_
  rw [smulLeftCLM_apply_apply L.hasTemperateGrowth]
  refine (norm_clm_smul_le_of_tsupport_subset hσ L ξ).trans ?_
  gcongr
  exact hσM ξ

/-- If `σ` vanishes outside `closedBall 0 t` and its derivatives of orders `k` and `k + 1` along
the orthonormal basis `b` are bounded by `A t ^ (-k)` and `A t ^ (-(k + 1))`, then the
`(k + 1)`-st derivatives of `L σ` along `b` have root sum of squared `L²` norms at most
`√#ι (k + 2) ‖L‖ A t ^ (-k) √|B(0, 1)| t ^ (n/2)`. -/
private theorem sqrt_sum_norm_toLp_iterate_lineDerivOp_smulLeftCLM_clm_sq_le {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℝ V) (σ : 𝓢(V, H)) {t A : ℝ} (ht : 0 < t) (hA : 0 ≤ A)
    (hσ : tsupport σ ⊆ closedBall 0 t) (L : V →L[ℝ] ℝ) (k : ℕ)
    (hσk : ∀ i ξ, ‖(∂_{b i})^[k] σ ξ‖ ≤ A / t ^ k)
    (hσk' : ∀ i ξ, ‖(∂_{b i})^[k + 1] σ ξ‖ ≤ A / t ^ (k + 1)) :
    √(∑ i, ‖((∂_{b i})^[k + 1] (smulLeftCLM H L σ)).toLp 2‖ ^ 2) ≤
      √(Fintype.card ι) * ((k + 2) * ‖L‖ * A / t ^ k * √(volume.real (ball (0 : V) 1)) *
        t ^ ((finrank ℝ V : ℝ) / 2)) := by
  refine sqrt_sum_norm_toLp_iterate_lineDerivOp_sq_le b _ (k + 1) ht.le (by positivity)
    ((tsupport_smulLeftCLM_subset _ σ).trans (Set.inter_subset_left.trans hσ)) fun i ξ ↦ ?_
  calc ‖(∂_{b i})^[k + 1] (smulLeftCLM H L σ) ξ‖
      ≤ t * ‖L‖ * ‖(∂_{b i})^[k + 1] σ ξ‖ + (k + 1) * ‖L‖ * ‖(∂_{b i})^[k] σ ξ‖ :=
        norm_iterate_lineDerivOp_smulLeftCLM_clm_le σ hσ (b.orthonormal.1 i).le L k ξ
    _ ≤ t * ‖L‖ * (A / t ^ (k + 1)) + (k + 1) * ‖L‖ * (A / t ^ k) := by
        gcongr
        exacts [hσk' i ξ, hσk i ξ]
    _ = (k + 2) * ‖L‖ * A / t ^ k := by
        rw [pow_succ]
        field_simp
        ring

end Real

section Hilbert

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The tail of the kernel of a band-limited symbol.** Let `b` be an orthonormal basis of the
`n`-dimensional space `V` and `2N > n`. There is a constant `C ≥ 0` such that, whenever a
Schwartz function `σ` vanishes outside `closedBall 0 t` and its `N`-th derivatives along `b` are
bounded by `A t ^ (-N)`,

`∫_{‖x‖ > R} ‖𝓕⁻ σ x‖ dx ≤ C A (t R) ^ (n/2 - N)` for every `R > 0`. -/
theorem exists_setIntegral_norm_fourierInv_le_of_support_subset {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) {N : ℕ} (hN : finrank ℝ V < 2 * N) :
    ∃ C, 0 ≤ C ∧ ∀ (σ : 𝓢(V, H)) {t A : ℝ}, 0 < t → 0 ≤ A → support σ ⊆ closedBall 0 t →
      (∀ i ξ, ‖(∂_{b i})^[N] σ ξ‖ ≤ A / t ^ N) → ∀ R, 0 < R →
        ∫ x in {x | R < ‖x‖}, ‖𝓕⁻ σ x‖ ≤ C * A * (t * R) ^ ((finrank ℝ V : ℝ) / 2 - N) := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_setIntegral_norm_fourierInv_le (H := H) b hN
  refine ⟨C₀ * √(Fintype.card ι) * √(volume.real (ball (0 : V) 1)), by positivity,
    fun σ t A ht hA hσ hσN R hR ↦ ?_⟩
  have hsum := sqrt_sum_norm_toLp_iterate_lineDerivOp_sq_le b σ N ht.le (by positivity)
    (closure_minimal hσ isClosed_closedBall) hσN
  have hte : t ^ ((finrank ℝ V : ℝ) / 2 - N) = t ^ ((finrank ℝ V : ℝ) / 2) / t ^ N := by
    rw [Real.rpow_sub ht, Real.rpow_natCast]
  refine (hC σ R hR).trans ((mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq ?_)
  rw [Real.mul_rpow ht.le hR.le, hte]
  ring

/-- **The smoothness of the kernel of a band-limited symbol.** Let `b` be an orthonormal basis of
the `n`-dimensional space `V` and `2N > n`. There is a constant `C ≥ 0` such that, whenever a
Schwartz function `σ` vanishes outside `closedBall 0 t` and its derivatives of order `k ≤ N` along
`b` are bounded by `A t ^ (-k)`,

`∫ ‖𝓕⁻ σ (x + h) - 𝓕⁻ σ x‖ dx ≤ C A t ‖h‖` for every `h`. -/
theorem exists_integral_norm_fourierInv_add_sub_le_of_support_subset {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) {N : ℕ} (hN : finrank ℝ V < 2 * N) :
    ∃ C, 0 ≤ C ∧ ∀ (σ : 𝓢(V, H)) {t A : ℝ}, 0 < t → 0 ≤ A → support σ ⊆ closedBall 0 t →
      (∀ k ≤ N, ∀ i ξ, ‖(∂_{b i})^[k] σ ξ‖ ≤ A / t ^ k) → ∀ h,
        ∫ x, ‖𝓕⁻ σ (x + h) - 𝓕⁻ σ x‖ ≤ C * A * (t * ‖h‖) := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : N ≠ 0)
  obtain ⟨C₁, hC₁, hC⟩ := exists_integral_norm_fourierInv_le (H := H) b hN
  refine ⟨2 * π * C₁ * √(volume.real (ball (0 : V) 1)) * (1 + √(Fintype.card ι) * (M + 2)),
    by positivity, fun σ t A ht hA hσ hσk h ↦ ?_⟩
  -- Translating the kernel by `h` costs `2π ∫ ‖𝓕⁻ τ‖` with `τ = ⟪·, h⟫ σ`. At `R = t⁻¹`, the
  -- `L¹` bound `exists_integral_norm_fourierInv_le` controls this by `‖τ‖_{L²}` and the `L²` norms
  -- of the `N`-th derivatives of `τ`, which the Leibniz rule bounds through those of `σ`.
  cases isEmpty_or_nonempty ι with
  | inl _ =>
    -- `V` is the zero space, so `h = 0` and the integrand vanishes.
    have : Subsingleton V := Module.finrank_zero_iff.mp (by
      rw [Module.finrank_eq_card_basis b.toBasis, Fintype.card_eq_zero])
    simp only [Subsingleton.elim h 0, add_zero, sub_self, norm_zero, integral_zero]
    positivity
  | inr _ =>
  obtain ⟨i₀⟩ : Nonempty ι := inferInstance
  have hσt : tsupport σ ⊆ closedBall 0 t := closure_minimal hσ isClosed_closedBall
  -- The symbol `τ ξ = ⟪h, ξ⟫ σ ξ` of the derivative of the kernel along `h`.
  have hi : (inner ℝ · h : V → ℝ) = ⇑(innerSL ℝ h) := funext fun _ ↦ real_inner_comm _ _
  set τ : 𝓢(V, H) := smulLeftCLM H (innerSL ℝ h) σ
  -- `τ` is bounded by `A t ‖h‖`, and its `(M + 1)`-st derivatives by `(M + 2) A t ^ (-M) ‖h‖`.
  have hτ := norm_toLp_smulLeftCLM_clm_le σ ht.le hσt (M := A)
    (fun ξ ↦ by simpa using hσk 0 (Nat.zero_le _) i₀ ξ) (innerSL ℝ h)
  have hsum := sqrt_sum_norm_toLp_iterate_lineDerivOp_smulLeftCLM_clm_sq_le b σ ht hA hσt
    (innerSL ℝ h) M (hσk M (by omega)) (hσk (M + 1) le_rfl)
  rw [innerSL_apply_norm] at hτ hsum
  have ha : 0 < t ^ ((finrank ℝ V : ℝ) / 2) := by positivity
  have h₁ : t⁻¹ ^ ((finrank ℝ V : ℝ) / 2) = (t ^ ((finrank ℝ V : ℝ) / 2))⁻¹ :=
    Real.inv_rpow ht.le _
  have h₂ : t⁻¹ ^ ((finrank ℝ V : ℝ) / 2 - (M + 1 : ℕ)) =
      t ^ (M + 1) / t ^ ((finrank ℝ V : ℝ) / 2) := by
    rw [Real.inv_rpow ht.le, Real.rpow_sub ht, Real.rpow_natCast, inv_div]
  refine (hi ▸ integral_norm_fourierInv_add_sub_le σ h).trans ?_
  grw [hC τ t⁻¹ (inv_pos.2 ht), h₁, h₂, hτ, hsum]
  refine le_of_eq ?_
  field_simp
  ring

/-- **Hörmander's condition for the kernel of a band-limited symbol.** Let `b` be an orthonormal
basis of the `n`-dimensional space `V` and `2N > n`. There is a constant `C ≥ 0` such that, whenever
a Schwartz function `σ` vanishes outside `closedBall 0 t` and its derivatives of order `k ≤ N`
along `b` are bounded by `A t ^ (-k)`,

`∫_{‖x‖ > 2 ‖h‖} ‖𝓕⁻ σ (x - h) - 𝓕⁻ σ x‖ dx ≤ C A min (t ‖h‖, (t ‖h‖) ^ (n/2 - N))`

for every `h ≠ 0`: the smoothness bound is the better one when `t ‖h‖ ≤ 1`, the tail bound when
`t ‖h‖ > 1`. -/
theorem exists_setIntegral_norm_fourierInv_sub_sub_le_of_support_subset {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) {N : ℕ} (hN : finrank ℝ V < 2 * N) :
    ∃ C, 0 ≤ C ∧ ∀ (σ : 𝓢(V, H)) {t A : ℝ}, 0 < t → 0 ≤ A → support σ ⊆ closedBall 0 t →
      (∀ k ≤ N, ∀ i ξ, ‖(∂_{b i})^[k] σ ξ‖ ≤ A / t ^ k) → ∀ h, h ≠ 0 →
        ∫ x in {x | 2 * ‖h‖ < ‖x‖}, ‖𝓕⁻ σ (x - h) - 𝓕⁻ σ x‖ ≤
          C * A * min (t * ‖h‖) ((t * ‖h‖) ^ ((finrank ℝ V : ℝ) / 2 - N)) := by
  obtain ⟨C₁, hC₁, hC₁'⟩ := exists_setIntegral_norm_fourierInv_le_of_support_subset (H := H) b hN
  obtain ⟨C₂, hC₂, hC₂'⟩ :=
    exists_integral_norm_fourierInv_add_sub_le_of_support_subset (H := H) b hN
  refine ⟨max (2 * C₁) C₂, hC₂.trans (le_max_right _ _), fun σ t A ht hA hσ hσk h hh ↦ ?_⟩
  have hK := (𝓕⁻ σ).integrable (μ := volume)
  rw [mul_min_of_nonneg _ _ (mul_nonneg (hC₂.trans (le_max_right _ _)) hA)]
  refine le_min ?_ ?_
  · -- the smoothness of the kernel
    refine (setIntegral_le_integral ((hK.comp_sub_right h).sub hK).norm
      (.of_forall fun _ ↦ norm_nonneg _)).trans ?_
    have := hC₂' σ ht hA hσ hσk (-h)
    simp only [← sub_eq_add_neg, norm_neg] at this
    refine this.trans ?_
    gcongr
    exact le_max_right _ _
  · -- the tail of the kernel
    calc ∫ x in {x | 2 * ‖h‖ < ‖x‖}, ‖𝓕⁻ σ (x - h) - 𝓕⁻ σ x‖
        ≤ 2 * ∫ x in {x | ‖h‖ < ‖x‖}, ‖𝓕⁻ σ x‖ := hK.setIntegral_norm_comp_sub_sub_le h
      _ ≤ 2 * (C₁ * A * (t * ‖h‖) ^ ((finrank ℝ V : ℝ) / 2 - N)) := by
          gcongr
          exact hC₁' σ ht hA hσ (hσk N le_rfl) ‖h‖ (norm_pos_iff.2 hh)
      _ ≤ max (2 * C₁) C₂ * A * (t * ‖h‖) ^ ((finrank ℝ V : ℝ) / 2 - N) := by
          rw [← mul_assoc, ← mul_assoc]
          gcongr
          exact le_max_left _ _

/-- **Hörmander's condition for dyadic sums of band-limited symbols.** Let `b` be an orthonormal
basis of the `n`-dimensional space `V` and `2N > n`. There is a constant `C ≥ 0` with the following
property. Let `σ j` be Schwartz functions, for `j` in a finite set `s ⊆ ℤ`, such that `σ j`
vanishes outside `closedBall 0 (2 ^ j)` and its derivatives of order `k ≤ N` along `b` are bounded
by `A 2 ^ (-j k)`. Then the kernel `K = 𝓕⁻ (∑ j ∈ s, σ j)` satisfies

`∫_{‖x‖ > 2 ‖h‖} ‖K (x - h) - K x‖ dx ≤ C A` for every `h`. -/
theorem exists_setIntegral_norm_fourierInv_sum_sub_sub_le {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) {N : ℕ} (hN : finrank ℝ V < 2 * N) :
    ∃ C, 0 ≤ C ∧ ∀ (σ : ℤ → 𝓢(V, H)) (s : Finset ℤ) {A : ℝ}, 0 ≤ A →
      (∀ j ∈ s, support (σ j) ⊆ closedBall 0 (2 ^ j)) →
      (∀ j ∈ s, ∀ k ≤ N, ∀ i ξ, ‖(∂_{b i})^[k] (σ j) ξ‖ ≤ A / (2 ^ j) ^ k) → ∀ h,
        ∫ x in {x | 2 * ‖h‖ < ‖x‖}, ‖𝓕⁻ (∑ j ∈ s, σ j) (x - h) - 𝓕⁻ (∑ j ∈ s, σ j) x‖ ≤
          C * A := by
  obtain ⟨D, hD, hD'⟩ :=
    exists_setIntegral_norm_fourierInv_sub_sub_le_of_support_subset (H := H) b hN
  set δ : ℝ := N - (finrank ℝ V : ℝ) / 2
  have hδ : 0 < δ := by
    have : (finrank ℝ V : ℝ) < 2 * N := by exact_mod_cast hN
    simp only [δ]
    linarith
  have hq : (2 : ℝ) ^ (-δ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  refine ⟨D * (2 + (1 - (2 : ℝ) ^ (-δ))⁻¹), mul_nonneg hD (by
    have := inv_pos.2 (sub_pos.2 hq); positivity), fun σ s A hA hσ hσk h ↦ ?_⟩
  rcases eq_or_ne h 0 with rfl | hh
  · simp only [sub_zero, sub_self, norm_zero, integral_zero]
    exact mul_nonneg (mul_nonneg hD (by have := inv_pos.2 (sub_pos.2 hq); positivity)) hA
  have he : (finrank ℝ V : ℝ) / 2 - N = -δ := by simp only [δ, neg_sub]
  set S : Set V := {x | 2 * ‖h‖ < ‖x‖}
  -- Each dyadic piece contributes at most `D A min (2 ^ j ‖h‖, (2 ^ j ‖h‖) ^ (-δ))`.
  have hterm (j : ℤ) (hj : j ∈ s) : ∫ x in S, ‖𝓕⁻ (σ j) (x - h) - 𝓕⁻ (σ j) x‖ ≤
      D * A * min (2 ^ j * ‖h‖) ((2 ^ j * ‖h‖) ^ (-δ)) :=
    he ▸ hD' (σ j) (zpow_pos two_pos j) hA (hσ j hj) (hσk j hj) h hh
  have hint : ∀ j ∈ s, Integrable (fun x ↦ ‖𝓕⁻ (σ j) (x - h) - 𝓕⁻ (σ j) x‖) (volume.restrict S) :=
    fun j _ ↦ (((𝓕⁻ (σ j)).integrable.comp_sub_right h).sub (𝓕⁻ (σ j)).integrable).norm.restrict
  have hK := (𝓕⁻ (∑ j ∈ s, σ j)).integrable (μ := volume)
  calc ∫ x in S, ‖𝓕⁻ (∑ j ∈ s, σ j) (x - h) - 𝓕⁻ (∑ j ∈ s, σ j) x‖
      ≤ ∫ x in S, ∑ j ∈ s, ‖𝓕⁻ (σ j) (x - h) - 𝓕⁻ (σ j) x‖ := by
        refine setIntegral_mono ((hK.comp_sub_right h).sub hK).norm.integrableOn
          (integrable_finsetSum _ hint) fun x ↦ ?_
        simp only [fourierInv_sum, sum_apply, ← Finset.sum_sub_distrib]
        exact norm_sum_le _ _
    _ = ∑ j ∈ s, ∫ x in S, ‖𝓕⁻ (σ j) (x - h) - 𝓕⁻ (σ j) x‖ := integral_finsetSum _ hint
    _ ≤ ∑ j ∈ s, D * A * min (2 ^ j * ‖h‖) ((2 ^ j * ‖h‖) ^ (-δ)) := Finset.sum_le_sum hterm
    _ = D * A * ∑ j ∈ s, min (2 ^ j * ‖h‖) ((2 ^ j * ‖h‖) ^ (-δ)) := by rw [Finset.mul_sum]
    _ ≤ D * A * (2 + (1 - (2 : ℝ) ^ (-δ))⁻¹) := by
        gcongr
        exact TauCeti.sum_min_zpow_mul_rpow_neg_le hδ (norm_pos_iff.2 hh) s
    _ = D * (2 + (1 - (2 : ℝ) ^ (-δ))⁻¹) * A := by ring

end Hilbert

end SchwartzMap
