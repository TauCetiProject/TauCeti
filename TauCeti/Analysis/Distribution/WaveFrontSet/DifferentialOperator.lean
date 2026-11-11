/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SmulLeft
public import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv

/-!
# Differential operators do not enlarge the wave front set

Let `T` be a complex distribution on an open subset `Ω` of a finite-dimensional real inner product
space `E`. This file shows that directional differentiation does not enlarge the wave front set of
`T`. Together with the corresponding statement for multiplication by a smooth function
(`Distribution.waveFrontSet_smulLeftCLM_subset`), a linear differential operator
`P = ∑ᵢ cᵢ gᵢ ∂^{mᵢ}` with coefficients smooth on all of `E` satisfies `WF(P T) ⊆ WF(T)`:
differential operators are *microlocal*.

The statement for derivatives is read off the localized Fourier transform `η ↦ T (φ e_η)` of
`Distribution.localFourier`, where `e_η x = 𝐞 (-⟪x, η⟫)`. For a direction `v`, differentiating
`φ e_η` gives the identity
`(∂_v T)^(φ, η) = 2πi ⟪v, η⟫ T^(φ, η) - T^(∂_v φ, η)`
(`Distribution.localFourier_lineDerivOp`). Both cutoffs on the right are supported in the support
of `φ`. By the independence of the cutoff (`Distribution.IsMicrolocallySmoothAt.exists_nhds_cone`),
rapid decay of the transforms of `T` in a cone for every cutoff supported near `x` gives rapid
decay of the transforms of `∂_v T` in the same cone; the factor `⟪v, η⟫` costs one power of
`1 + ‖η‖`.

Unlike multiplication by a smooth function that does not vanish, differentiation has no converse:
on `ℝ²` the distribution of the function `(x, y) ↦ H(x)`, with `H` the Heaviside function, is
singular along `x = 0`, while its derivative in `y` vanishes.

## Main results

* `Distribution.localFourier_lineDerivOp`: the localized Fourier transform of a derivative.
* `Distribution.waveFrontSet_lineDerivOp_subset`,
  `Distribution.waveFrontSet_iteratedLineDerivOp_subset`: `WF(∂_v T) ⊆ WF(T)`, and the same for
  iterated derivatives.
* `Distribution.waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset`: `WF(P T) ⊆ WF(T)`
  for every linear differential operator `P` with coefficients smooth on all of `E`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.1, (8.1.11) and Lemma 8.1.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, Lecture I, §7.
-/

public section

noncomputable section

open Complex Filter Set TopologicalSpace TestFunction LineDeriv
open scoped Distributions Topology FourierTransform RealInnerProductSpace ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Opens E}
  {T : 𝓓'(Ω, ℂ)} {x ξ : E}

/-! ### Directional derivatives -/

/-- The derivative of the modulated cutoff `φ e_η` in the direction `v` is
`(∂_v φ) e_η - 2πi ⟪v, η⟫ φ e_η`. -/
private theorem lineDerivOp_bilinLeftCLM_fourierAtom (φ : 𝓓(Ω, ℂ)) (v η : E) :
    ∂_{v} (bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) φ) =
      bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) (∂_{v} φ) -
        (2 * Real.pi * I * ⟪v, η⟫) •
          bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) φ := by
  ext y
  have he := TauCeti.hasFDerivAt_fourierAtom η y
  have hφ : HasFDerivAt (φ : E → ℂ) (fderiv ℝ φ y) y :=
    (φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hχ (ψ : 𝓓(Ω, ℂ)) :
      ⇑(bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) ψ) =
        fun z ↦ ψ z * TauCeti.fourierAtom η z :=
    funext fun z ↦ by rw [bilinLeftCLM_fourierAtom_apply, TauCeti.fourierAtom_eq_fourierChar]
  simp only [TestFunction.lineDerivOp_eq_lineDerivCLM ℝ, coe_lineDerivCLM, hχ]
  rw [((hφ.fun_mul he).hasLineDerivAt v).lineDeriv]
  have hin : innerSL ℝ η v = ⟪v, η⟫ := by rw [innerSL_apply_apply, real_inner_comm]
  simp [hχ, (hφ.hasLineDerivAt v).lineDeriv, hin]
  ring

/-- **The localized Fourier transform of a derivative.** For a direction `v`,
`(∂_v T)^(φ, η) = 2πi ⟪v, η⟫ T^(φ, η) - T^(∂_v φ, η)`. -/
theorem localFourier_lineDerivOp (T : 𝓓'(Ω, ℂ)) (v : E) (φ : 𝓓(Ω, ℂ)) (η : E) :
    (∂_{v} T).localFourier φ η =
      2 * Real.pi * I * ⟪v, η⟫ * T.localFourier φ η - T.localFourier (∂_{v} φ) η := by
  rw [localFourier_eq _ φ (bilinLeftCLM_fourierAtom_apply φ η), complexPairing_lineDerivOp,
    lineDerivOp_bilinLeftCLM_fourierAtom, map_sub, map_smul, smul_eq_mul,
    ← localFourier_eq T φ (bilinLeftCLM_fourierAtom_apply φ η),
    ← localFourier_eq T (∂_{v} φ) (bilinLeftCLM_fourierAtom_apply (∂_{v} φ) η)]
  ring

variable [FiniteDimensional ℝ E]

/-- A derivative of a distribution microlocally smooth at `(x, ξ)` is microlocally smooth
there. -/
theorem IsMicrolocallySmoothAt.lineDerivOp (h : T.IsMicrolocallySmoothAt x ξ) (v : E) :
    (∂_{v} T).IsMicrolocallySmoothAt x ξ := by
  obtain ⟨ψ, hψx, Γ, hΓ, hξ, hcone, hdecay⟩ := h.exists_cutoff_cone
  refine isMicrolocallySmoothAt_iff.2 ⟨ψ, by simp [hψx], Γ, hΓ, hξ, hcone, fun N ↦ ?_⟩
  obtain ⟨C₁, hC₁⟩ := hdecay ψ subset_rfl (N + 1)
  obtain ⟨C₂, hC₂⟩ := hdecay (∂_{v} ψ) (TestFunction.tsupport_lineDerivOp_subset ψ v) N
  refine ⟨2 * Real.pi * ‖v‖ * C₁ + C₂, fun η hη ↦ ?_⟩
  have h₁ := hC₁ η hη
  have h₂ := hC₂ η hη
  have hη₁ : ‖η‖ ≤ 1 + ‖η‖ := le_add_of_nonneg_left zero_le_one
  have hinner : ‖(2 * Real.pi * I * ⟪v, η⟫ : ℂ)‖ ≤ 2 * Real.pi * ‖v‖ * (1 + ‖η‖) := by
    calc ‖(2 * Real.pi * I * ⟪v, η⟫ : ℂ)‖ = 2 * Real.pi * |⟪v, η⟫| := by simp
      _ ≤ 2 * Real.pi * (‖v‖ * (1 + ‖η‖)) := by
        gcongr
        exact (abs_real_inner_le_norm v η).trans (by gcongr)
      _ = 2 * Real.pi * ‖v‖ * (1 + ‖η‖) := by ring
  rw [localFourier_lineDerivOp]
  calc (1 + ‖η‖) ^ N *
        ‖2 * Real.pi * I * ⟪v, η⟫ * T.localFourier ψ η - T.localFourier (∂_{v} ψ) η‖
      ≤ (1 + ‖η‖) ^ N * (2 * Real.pi * ‖v‖ * (1 + ‖η‖) * ‖T.localFourier ψ η‖ +
          ‖T.localFourier (∂_{v} ψ) η‖) := by
        gcongr
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul]
        gcongr
    _ = 2 * Real.pi * ‖v‖ * ((1 + ‖η‖) ^ (N + 1) * ‖T.localFourier ψ η‖) +
          (1 + ‖η‖) ^ N * ‖T.localFourier (∂_{v} ψ) η‖ := by ring
    _ ≤ 2 * Real.pi * ‖v‖ * C₁ + C₂ := by gcongr

/-- **Differentiation does not enlarge the wave front set.** -/
theorem waveFrontSet_lineDerivOp_subset (T : 𝓓'(Ω, ℂ)) (v : E) :
    (∂_{v} T).waveFrontSet ⊆ T.waveFrontSet := by
  rintro ⟨y, η⟩ hp
  obtain ⟨hy, hη, hT⟩ := mem_waveFrontSet_iff.1 hp
  exact mem_waveFrontSet_iff.2 ⟨hy, hη, fun h ↦ hT (h.lineDerivOp v)⟩

/-- Iterated differentiation does not enlarge the wave front set. -/
theorem waveFrontSet_iteratedLineDerivOp_subset {k : ℕ} (m : Fin k → E) (T : 𝓓'(Ω, ℂ)) :
    (∂^{m} T).waveFrontSet ⊆ T.waveFrontSet := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedLineDerivOp_succ_left]
    exact (waveFrontSet_lineDerivOp_subset _ _).trans (ih _)

/-- **Differential operators do not enlarge the wave front set.** A linear differential operator
`P = ∑ᵢ cᵢ gᵢ ∂^{mᵢ}` with complex constants `cᵢ`, real functions `gᵢ` smooth on all of `E` and
iterated directional derivatives `∂^{mᵢ}` satisfies `WF(P T) ⊆ WF(T)`. Every differential operator
whose complex coefficients are smooth on all of `E` has this form, by splitting each coefficient
into its real and imaginary parts. Coefficients smooth only on `Ω` are not covered by this
statement. -/
theorem waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) {g : ι → E → ℝ} (hg : ∀ i, ContDiff ℝ ∞ (g i)) {k : ι → ℕ}
    (m : (i : ι) → Fin (k i) → E) (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ s, c i • smulLeftCLM (hg i) (∂^{m i} T)).waveFrontSet ⊆ T.waveFrontSet :=
  (waveFrontSet_sum_subset _ _).trans <| iUnion₂_subset fun _ _ ↦
    (waveFrontSet_smul_subset _ _).trans <| (waveFrontSet_smulLeftCLM_subset _ _).trans <|
      inter_subset_left.trans (waveFrontSet_iteratedLineDerivOp_subset _ _)

end Distribution
