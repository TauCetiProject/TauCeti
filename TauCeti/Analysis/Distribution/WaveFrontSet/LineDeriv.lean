/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.Distribution.TestFunction.FourierAtom
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity

/-!
# The wave front set under differentiation and differential operators

This file proves that the wave front set of a complex distribution does not grow under
differentiation: `WF(∂_v T) ⊆ WF(T)`, and hence `WF(∂^m T) ⊆ WF(T)` for iterated derivatives.

Combining this with the sum rule `Distribution.waveFrontSet_add_subset` and the smooth
multiplication rule `Distribution.waveFrontSet_smulLeftCLM_subset`, a differential operator
`P = ∑ c_α a_α ∂^α` with smooth real coefficients `a_α` and complex constants `c_α`, which covers
every operator with smooth complex coefficients, satisfies `WF(P T) ⊆ WF(T)`
(`Distribution.waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset`). This is the
microlocality of differential operators, the first case of that of pseudodifferential
operators.

The proof goes through the localized Fourier transform `η ↦ T (φ e_η)`, where
`e_η x = 𝐞 (-⟪x, η⟫)`. The product rule `TestFunction.lineDerivOp_bilinLeftCLM_fourierAtom` gives

`(∂_v T) (φ e_η) = 2πi ⟪v, η⟫ T (φ e_η) - T ((∂_v φ) e_η)`

(`Distribution.localFourier_lineDerivOp`), and the polynomial factor `⟪v, η⟫` is absorbed by
rapid decay of every order.

## Main results

* `Distribution.localFourier_lineDerivOp`: the localized Fourier transform of a derivative.
* `Distribution.IsMicrolocallySmoothAt.lineDerivOp`, `Distribution.waveFrontSet_lineDerivOp_subset`,
  `Distribution.waveFrontSet_iteratedLineDerivOp_subset`: the wave front set of a derivative.
* `Distribution.waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset`: differential
  operators with smooth coefficients do not enlarge the wave front set.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, Lecture I, §7.
-/

public section

noncomputable section

open Complex Filter LineDeriv Metric Real Set TopologicalSpace TestFunction
open scoped Distributions Topology RealInnerProductSpace ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Opens E}

/-- **The localized Fourier transform of a derivative.** By the product rule
`∂_v (φ e_η) = (∂_v φ) e_η - 2πi ⟪v, η⟫ φ e_η`,

`(∂_v T) (φ e_η) = 2πi ⟪v, η⟫ T (φ e_η) - T ((∂_v φ) e_η)`. -/
@[simp]
theorem localFourier_lineDerivOp (T : 𝓓'(Ω, ℂ)) (v : E) (φ : 𝓓(Ω, ℂ)) (η : E) :
    (∂_{v} T).localFourier φ η =
      2 * π * I * ⟪v, η⟫ * T.localFourier φ η - T.localFourier (∂_{v} φ) η := by
  rw [localFourier_def, localFourier_def, localFourier_def, complexPairing_lineDerivOp,
    lineDerivOp_bilinLeftCLM_fourierAtom, map_sub, map_smul, smul_eq_mul]
  ring

section FiniteDimensional

variable [FiniteDimensional ℝ E] {T : 𝓓'(Ω, ℂ)} {x ξ : E}

/-! ### Differentiation -/

/-- A derivative `∂_v T` of a distribution microlocally smooth at `(x, ξ)` is microlocally smooth
there. -/
theorem IsMicrolocallySmoothAt.lineDerivOp (hT : T.IsMicrolocallySmoothAt x ξ) (v : E) :
    (∂_{v} T).IsMicrolocallySmoothAt x ξ := by
  have hx : x ∈ Ω := by
    obtain ⟨φ, hφ, -⟩ := isMicrolocallySmoothAt_iff.1 hT
    exact φ.tsupport_subset (subset_tsupport _ hφ)
  obtain ⟨U, hU, Γ, hΓ, hξ, hcone, hdecay⟩ := hT.exists_nhds_cone
  obtain ⟨φ, hφU, hφx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem hU (Ω.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
  have hφU' : tsupport φ ⊆ U := hφU.trans inter_subset_left
  refine isMicrolocallySmoothAt_iff.2 ⟨φ, by simp [hφx], Γ, hΓ, hξ, hcone, fun N ↦ ?_⟩
  -- Both terms of `localFourier_lineDerivOp` decay; the factor `⟪v, η⟫` costs one order.
  obtain ⟨C₁, hC₁⟩ := hdecay φ hφU' (N + 1)
  obtain ⟨C₂, hC₂⟩ := hdecay (∂_{v} φ) ((tsupport_fderiv_apply_subset ℝ v).trans hφU') N
  refine ⟨2 * π * ‖v‖ * C₁ + C₂, fun η hη ↦ ?_⟩
  have hinner : ‖(2 * π * I * ⟪v, η⟫ : ℂ)‖ ≤ 2 * π * ‖v‖ * (1 + ‖η‖) := by
    calc ‖(2 * π * I * ⟪v, η⟫ : ℂ)‖ = 2 * π * ‖⟪v, η⟫‖ := by
          rw [norm_mul, norm_mul, norm_mul, norm_I, Complex.norm_real, Complex.norm_real,
            Complex.norm_two, Real.norm_of_nonneg Real.pi_pos.le, mul_one]
      _ ≤ 2 * π * (‖v‖ * (1 + ‖η‖)) := by
          gcongr
          exact (norm_inner_le_norm (𝕜 := ℝ) v η).trans
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (norm_nonneg v))
      _ = 2 * π * ‖v‖ * (1 + ‖η‖) := by ring
  have h1 : 0 ≤ (1 + ‖η‖) ^ N := by positivity
  rw [localFourier_lineDerivOp]
  calc (1 + ‖η‖) ^ N *
        ‖2 * π * I * ⟪v, η⟫ * T.localFourier φ η - T.localFourier (∂_{v} φ) η‖
      ≤ (1 + ‖η‖) ^ N * (2 * π * ‖v‖ * (1 + ‖η‖) * ‖T.localFourier φ η‖) +
          (1 + ‖η‖) ^ N * ‖T.localFourier (∂_{v} φ) η‖ := by
        rw [← mul_add]
        refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) h1
        rw [norm_mul]
        gcongr
    _ = 2 * π * ‖v‖ * ((1 + ‖η‖) ^ (N + 1) * ‖T.localFourier φ η‖) +
          (1 + ‖η‖) ^ N * ‖T.localFourier (∂_{v} φ) η‖ := by ring
    _ ≤ 2 * π * ‖v‖ * C₁ + C₂ := by
        gcongr
        exacts [hC₁ η hη, hC₂ η hη]

/-- **The wave front set of a derivative** lies in the wave front set of the distribution. -/
theorem waveFrontSet_lineDerivOp_subset (T : 𝓓'(Ω, ℂ)) (v : E) :
    (∂_{v} T).waveFrontSet ⊆ T.waveFrontSet := by
  rintro ⟨x, ξ⟩ hp
  obtain ⟨hx, hξ, hvT⟩ := mem_waveFrontSet_iff.1 hp
  exact mem_waveFrontSet_iff.2 ⟨hx, hξ, fun hT ↦ hvT (hT.lineDerivOp v)⟩

/-- The wave front set of an iterated derivative `∂^m T` lies in the wave front set of `T`. -/
theorem waveFrontSet_iteratedLineDerivOp_subset (T : 𝓓'(Ω, ℂ)) {n : ℕ} (m : Fin n → E) :
    (∂^{m} T).waveFrontSet ⊆ T.waveFrontSet := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left]
    exact (waveFrontSet_lineDerivOp_subset _ _).trans (ih _)

/-- **Differential operators do not enlarge the wave front set** (Hörmander I, §8.1). For
finitely many smooth real coefficients `a i`, complex constants `c i` and iterated directions
`m i`, the operator `P T = ∑ i ∈ s, c i • a i ∂^(m i) T` satisfies `WF(P T) ⊆ WF(T)`. Writing a
smooth complex coefficient as `u + i v`, this covers every linear differential operator with
smooth complex coefficients. -/
theorem waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) {a : ι → E → ℝ} (ha : ∀ i, ContDiff ℝ ∞ (a i)) {k : ι → ℕ}
    (m : ∀ i, Fin (k i) → E) (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ s, c i • smulLeftCLM (ha i) (∂^{m i} T)).waveFrontSet ⊆ T.waveFrontSet :=
  (waveFrontSet_sum_subset s _).trans <| iUnion₂_subset fun i _ ↦
    (waveFrontSet_smul_subset _ _).trans <| (waveFrontSet_smulLeftCLM_subset _ _).trans <|
      inter_subset_left.trans (waveFrontSet_iteratedLineDerivOp_subset T (m i))

end FiniteDimensional

end Distribution
