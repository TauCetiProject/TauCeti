/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace
public import TauCeti.Analysis.Holder.Normed
public import TauCeti.MeasureTheory.Function.Lp.BoundedContinuous
import TauCeti.Analysis.Convolution.Holder
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.LittlewoodPaley
import TauCeti.Analysis.Distribution.TemperedDistribution.Convolution
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Hölder functions in the Hölder–Zygmund scale

The Hölder–Zygmund space `𝒞^α = B^α_{∞,∞}` consists of the tempered distributions `u` whose
Littlewood–Paley blocks satisfy `‖Δⱼ u‖_∞ ≤ C 2^{-jα}`. This file proves that every bounded
continuous `α`-Hölder function lies in it, with

`supⱼ 2^{jα} ‖Δⱼ f‖_∞ ≤ C (‖f‖_∞ + [f]_α)`,

where `[f]_α` is the Hölder constant and `C` depends only on `α` and the bump function `φ` of the
partition. This is the inclusion `C^{0,α} ⊆ 𝒞^α` of the identification of the Hölder–Zygmund scale
with the classical Hölder spaces.

For `j ≥ 1` the block `Δⱼ f` is the convolution of `f` with the kernel `Kⱼ = 𝓕⁻ ψⱼ`, which has
integral `ψⱼ 0 = 0`. Hence `Δⱼ f (x) = ∫ Kⱼ y (f (x - y) - f x) dy` is bounded by `[f]_α` times
the moment `∫ ‖y‖^α ‖Kⱼ y‖ dy`, and this moment is `2^{-(j-1)α}` times that of `K₁`, since `Kⱼ` is
an `L¹`-normalised dilate of `K₁`. The low-frequency block satisfies `‖Δ₀ f‖_∞ ≤ C_φ ‖f‖_∞`,
with `C_φ` depending only on `φ`.

## Main declarations

* `TemperedDistribution.exists_littlewoodPaleyBlock_eq_and_rpow_mul_norm_le_of_holderWith`: the
  blockwise estimate `2^{jα} ‖Δⱼ f‖_∞ ≤ C (‖f‖_∞ + H)` for an `α`-Hölder function with constant
  `H`, with `C` independent of `f`, `H` and `j`.
* `TemperedDistribution.memBesov_of_holderWith`: a bounded continuous `α`-Hölder function lies in
  `B^α_{∞,∞}`.
* `TauCeti.HolderSpace.toBesovSpace`: the inclusion `C^{0,α} → B^α_{∞,∞}`, as a continuous linear
  map from the Hölder space with norm `‖f‖_∞ + [f]_α`.

## References

* H. Triebel, *Theory of Function Spaces*, Section 2.5.7.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Section 2.7.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, Lecture I, (3.32)–(3.34).
-/

public section

noncomputable section

open MeasureTheory FourierTransform BoundedContinuousFunction
open scoped ENNReal NNReal SchwartzMap Convolution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TemperedDistribution

/-- **Hölder functions have geometrically decaying Littlewood–Paley blocks.** For every
`α ≥ 0` there is `C`, depending only on `α` and `φ`, such that for every bounded continuous
function `f` that is `α`-Hölder with constant `H`, each block `Δⱼ f` is an `L^∞` function `g`
with `2^{jα} ‖g‖_∞ ≤ C (‖f‖_∞ + H)`. -/
theorem exists_littlewoodPaleyBlock_eq_and_rpow_mul_norm_le_of_holderWith
    (φ : ContDiffBump (0 : E)) (α : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : E →ᵇ F) {H : ℝ≥0}, HolderWith H α f → ∀ j : ℕ,
      ∃ g : Lp F ∞ (volume : Measure E),
        littlewoodPaleyBlock F φ j (toLpTop volume ℂ f : 𝓢'(E, F)) = g ∧
          2 ^ ((α : ℝ) * j) * ‖g‖ ≤ C * (‖f‖ + H) := by
  obtain ⟨C₀, hC₀⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  set M := ∫ y, ‖y‖ ^ (α : ℝ) * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) y‖
  refine ⟨|C₀| + 2 ^ (α : ℝ) * M, by positivity, fun f H hf j ↦ ?_⟩
  have hfH : ‖f‖ ≤ ‖f‖ + H := le_add_of_nonneg_right H.coe_nonneg
  have hHf : (H : ℝ) ≤ ‖f‖ + H := le_add_of_nonneg_left (norm_nonneg f)
  rcases j with _ | j
  · -- The low-frequency block satisfies `‖Δ₀ f‖_∞ ≤ C₀ ‖f‖_∞`, with `C₀` depending on `φ`.
    obtain ⟨g, hg, hgf⟩ := hC₀ 0 (toLpTop volume ℂ f)
    refine ⟨g, hg, ?_⟩
    rw [Nat.cast_zero, mul_zero, Real.rpow_zero, one_mul]
    calc ‖g‖ ≤ C₀ * ‖toLpTop volume ℂ f‖ := hgf
      _ ≤ |C₀| * ‖f‖ := by
          gcongr
          · exact le_abs_self C₀
          · exact norm_toLpTop_le volume f
      _ ≤ |C₀| * (‖f‖ + H) := by gcongr
      _ ≤ (|C₀| + 2 ^ (α : ℝ) * M) * (‖f‖ + H) := by
          gcongr
          exact le_add_of_nonneg_right (by positivity)
  · -- The dyadic block is the convolution with the kernel `Kⱼ = 𝓕⁻ ψⱼ` of integral zero.
    set σ := φ.inhomogeneousLittlewoodPaleySchwartz (j + 1)
    set K : E → ℂ := 𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley (j + 1) ξ : ℂ))
    have hσK : 𝓕⁻ (σ : E → ℂ) = K := by
      rw [φ.coe_inhomogeneousLittlewoodPaleySchwartz]
    obtain ⟨g, hg, hgae, -⟩ := exists_fourierMultiplierCLM_toTemperedDistribution_eq σ
      (toLpTop volume ℂ f) (q := ∞) le_rfl (by simp)
    rw [hσK, convolution_congr (ContinuousLinearMap.lsmul ℂ ℂ) (ae_eq_refl K)
      (coeFn_toLpTop (𝕜 := ℂ) volume f)] at hgae
    rw [φ.coe_inhomogeneousLittlewoodPaleySchwartz, ← littlewoodPaleyBlock_apply] at hg
    refine ⟨g, hg, ?_⟩
    have hK : Integrable K := by
      rw [← hσK, ← SchwartzMap.fourierInv_coe]
      exact (𝓕⁻ σ).integrable
    have hKα : Integrable (fun y ↦ ‖y‖ ^ (α : ℝ) * ‖K y‖) := by
      rw [← hσK, ← SchwartzMap.fourierInv_coe]
      exact (𝓕⁻ σ).integrable_rpow_mul_norm α.coe_nonneg
    -- Pointwise, `‖Kⱼ ⋆ f‖ ≤ H ∫ ‖y‖ ^ α ‖Kⱼ y‖ = H 2^{-jα} M`.
    have hbound : ∀ x, ‖(K ⋆[ContinuousLinearMap.lsmul ℂ ℂ] (f : E → F)) x‖ ≤
        H * ((2 ^ ((α : ℝ) * j))⁻¹ * M) := fun x ↦ by
      rw [convolution_lsmul,
        ← φ.integral_rpow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_succ]
      exact TauCeti.norm_integral_kernel_smul_sub_le_of_integral_eq_zero hK
        (φ.integral_fourierInv_inhomogeneousLittlewoodPaley_succ j)
        hKα hf f.continuous x
    have hgn : ‖g‖ ≤ H * ((2 ^ ((α : ℝ) * j))⁻¹ * M) :=
      Lp.norm_top_le_of_ae_bound (by positivity) (by
        filter_upwards [hgae] with x hx
        rw [hx]
        exact hbound x)
    have h2 : (2 : ℝ) ^ ((α : ℝ) * ↑(j + 1)) = 2 ^ (α : ℝ) * 2 ^ ((α : ℝ) * j) := by
      rw [← Real.rpow_add two_pos]
      push_cast
      ring_nf
    calc 2 ^ ((α : ℝ) * ↑(j + 1)) * ‖g‖
        ≤ 2 ^ ((α : ℝ) * ↑(j + 1)) * (H * ((2 ^ ((α : ℝ) * j))⁻¹ * M)) := by gcongr
      _ = 2 ^ (α : ℝ) * M * H := by
          rw [h2]
          field_simp
      _ ≤ (|C₀| + 2 ^ (α : ℝ) * M) * (‖f‖ + H) := by
          gcongr
          exact le_add_of_nonneg_left (abs_nonneg C₀)

/-- **Bounded Hölder functions are Hölder–Zygmund.** A bounded continuous function that is
`α`-Hölder lies in the Besov space `B^α_{∞,∞}`. -/
theorem memBesov_of_holderWith (φ : ContDiffBump (0 : E)) {α H : ℝ≥0} {f : E →ᵇ F}
    (hf : HolderWith H α f) : (toLpTop volume ℂ f : 𝓢'(E, F)).MemBesov φ α ∞ ∞ := by
  obtain ⟨C, -, hC⟩ :=
    exists_littlewoodPaleyBlock_eq_and_rpow_mul_norm_le_of_holderWith (F := F) φ α
  choose g hg hgle using hC f hf
  refine memBesov_iff.2 ⟨g, hg, memℓp_infty_iff.2 ⟨C * (‖f‖ + H), ?_⟩⟩
  rintro _ ⟨j, rfl⟩
  dsimp only
  rw [Real.norm_of_nonneg (by positivity)]
  exact hgle j

end TemperedDistribution

namespace TauCeti.HolderSpace

open TemperedDistribution

variable (φ : ContDiffBump (0 : E)) {α : ℝ≥0}

/-- **The inclusion `C^{0,α} ⊆ 𝒞^α`**: a bounded continuous `α`-Hölder function, as an element of
the Hölder–Zygmund space `B^α_{∞,∞}`. It is bounded for the Hölder norm `‖f‖_∞ + [f]_α`. -/
def toBesovSpace : HolderSpace α E F →L[ℝ] BesovSpace F φ α ∞ ∞ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun f ↦ (memBesov_of_holderWith φ f.memHolder.holderWith).toBesovSpace
      map_add' := fun f g ↦ BesovSpace.ext <| by
        simp only [MemBesov.toDistr_toBesovSpace, BesovSpace.toDistr_add,
          toBoundedContinuousFunction_add, map_add, Lp.toTemperedDistribution_add]
      map_smul' := fun c f ↦ BesovSpace.ext <| by
        simp only [MemBesov.toDistr_toBesovSpace, toBoundedContinuousFunction_smul,
          RingHom.id_apply]
        rw [← Complex.coe_smul c (_ : BesovSpace F φ α ∞ ∞), BesovSpace.toDistr_smul,
          MemBesov.toDistr_toBesovSpace, ← Lp.toTemperedDistribution_smul,
          ← map_smul, Complex.coe_smul] } <| by
    obtain ⟨C, hC0, hC⟩ :=
      exists_littlewoodPaleyBlock_eq_and_rpow_mul_norm_le_of_holderWith (F := F) φ α
    refine ⟨C * 2, fun f ↦ ?_⟩
    have hf := hC f.toBoundedContinuousFunction
      (by simpa only [coe_toBoundedContinuousFunction] using f.holderWith_nnnorm)
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [BesovSpace.norm_eq_ciSup]
    refine ciSup_le fun j ↦ ?_
    obtain ⟨g, hg, hgle⟩ := hf j
    have hblock : (memBesov_of_holderWith φ f.memHolder.holderWith).toBesovSpace.block j = g :=
      LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
        simp [BesovSpace.coe_block, hg]
    rw [hblock]
    calc 2 ^ ((α : ℝ) * j) * ‖g‖ ≤ C * (‖f.toBoundedContinuousFunction‖ + ‖f‖₊) := hgle
      _ ≤ C * 2 * ‖f‖ := by
        rw [coe_nnNorm, mul_assoc, two_mul]
        gcongr
        exact f.norm_toBoundedContinuousFunction_le

/-- The tempered distribution of `toBesovSpace φ f` is that of the bounded function `f`. -/
@[simp]
theorem toDistr_toBesovSpace (f : HolderSpace α E F) :
    (toBesovSpace φ f).toDistr = (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)) := by
  simp [toBesovSpace]

end TauCeti.HolderSpace
