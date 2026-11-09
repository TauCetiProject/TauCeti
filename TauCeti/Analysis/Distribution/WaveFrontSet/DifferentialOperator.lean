/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SmulLeft
public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.PositiveDefinite.FourierAtom

/-!
# Wave front sets under differential operators

A differential operator with smooth coefficients does not create singularities: if `P` is such an
operator, then `WF(P T) ⊆ WF(T)` for every distribution `T`. This file proves this for the two
operations from which these operators are built, multiplication by a smooth function and
directional differentiation.

Both statements are read off the localized Fourier transform `η ↦ T (φ e_η)` of
`Distribution.localFourier`. Multiplying `T` by `g` replaces the cutoff `φ` by `g φ`
(`Distribution.localFourier_smulLeftCLM`), and differentiating `T` in the direction `v` gives

`(∂_v T) (φ e_η) = 2πi ⟪v, η⟫ T (φ e_η) - T ((∂_v φ) e_η)`

(`Distribution.localFourier_lineDerivOp`). The cutoffs `g φ` and `∂_v φ` are supported in the
support of `φ`, and on a small enough support every cutoff gives rapid decay in a fixed cone
(`Distribution.IsMicrolocallySmoothAt.exists_nhds_cone`). The polynomial factor `⟪v, η⟫` is
absorbed by rapid decay.

Near a point where `g` does not vanish, `T` is `g⁻¹ (g T)`, so multiplication by `g` does not
change the wave front set there.

## Main results

* `Distribution.waveFrontSet_smulLeftCLM_subset`: `WF(g T) ⊆ WF(T)` for smooth `g`, with equality
  over the points where `g ≠ 0` (`Distribution.mem_waveFrontSet_smulLeftCLM_iff`).
* `Distribution.waveFrontSet_lineDerivOp_subset`: `WF(∂_v T) ⊆ WF(T)`, and
  `Distribution.waveFrontSet_iteratedLineDerivOp_subset` for iterated derivatives.
* `Distribution.waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset`: for a differential
  operator `P T = ∑ᵢ cᵢ gᵢ ∂^{mᵢ} T` with smooth coefficients, `WF(P T) ⊆ WF(T)`. Since a smooth
  complex coefficient is `g₁ + i g₂` with `g₁`, `g₂` smooth and real, this covers every linear
  differential operator with smooth complex coefficients.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.1: the inclusion `WF(P u) ⊆ WF(u)` for differential operators `P` with
  smooth coefficients.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, Lecture I, §7.
-/

public section

noncomputable section

open Complex Filter Function Real Set TopologicalSpace LineDeriv
open scoped Distributions Topology FourierTransform RealInnerProductSpace ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Opens E} {g : E → ℝ}

/-! ### The localized Fourier transform -/

/-- The modulated test function `x ↦ φ x * 𝐞 (-⟪x, η⟫)` paired with `T` in the localized Fourier
transform. -/
private abbrev charMul (η : E) (φ : 𝓓(Ω, ℂ)) : 𝓓(Ω, ℂ) :=
  TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) φ

private theorem coe_charMul (η : E) (φ : 𝓓(Ω, ℂ)) :
    ⇑(charMul η φ) = fun x ↦ φ x * TauCeti.fourierAtom η x := by
  ext x
  simp [charMul, TestFunction.bilinLeftCLM_apply, -TauCeti.fourierAtom_apply]

private theorem localFourier_eq_complexPairing_charMul (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) (η : E) :
    T.localFourier φ η = T.complexPairing (charMul η φ) :=
  localFourier_eq T φ fun x ↦ by
    simp [TauCeti.fourierAtom_eq_fourierChar, real_inner_comm,
      -TauCeti.fourierAtom_apply]

/-- The localized Fourier transform of `g T` with cutoff `φ` is that of `T` with cutoff `g φ`. -/
theorem localFourier_smulLeftCLM (hg : ContDiff ℝ ∞ g) (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) (η : E) :
    (smulLeftCLM hg T).localFourier φ η = T.localFourier (TestFunction.smulLeftCLM hg φ) η := by
  rw [localFourier_eq_complexPairing_charMul, localFourier_eq_complexPairing_charMul,
    complexPairing_smulLeftCLM]
  congr 1
  ext x
  simp only [TestFunction.smulLeftCLM_apply, coe_charMul, real_smul]
  ring

/-- The directional derivative of a modulated test function:
`∂_v (φ e_η) = (∂_v φ) e_η - 2πi ⟪v, η⟫ φ e_η`. -/
private theorem lineDerivOp_charMul (φ : 𝓓(Ω, ℂ)) (v η : E) :
    ∂_{v} (charMul η φ) =
      charMul η (∂_{v} φ) - (2 * π * I * ((⟪v, η⟫ : ℝ) : ℂ)) • charMul η φ := by
  ext x
  have hE : (TauCeti.fourierAtom η : E → ℂ) = fun y ↦ (𝐞 (-(innerSL ℝ) y η) : ℂ) := by
    ext y
    simp [TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply]
  have he : HasFDerivAt (TauCeti.fourierAtom η)
      ((-2 * π * I * TauCeti.fourierAtom η x) • (ofRealCLM ∘L ((innerSL ℝ).flip η))) x := by
    rw [hE]
    exact Real.hasFDerivAt_fourierChar_neg_bilinear_left (innerSL ℝ) x η
  have hφ : HasFDerivAt (φ : E → ℂ) (fderiv ℝ φ x) x :=
    (φ.contDiff.differentiable (by simp) x).hasFDerivAt
  rw [TestFunction.lineDerivOp_apply, coe_charMul, ((hφ.fun_mul he).hasLineDerivAt v).lineDeriv]
  simp only [hφ.differentiableAt.lineDeriv_eq_fderiv, coe_charMul, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, innerSL_apply_apply,
    ofRealCLM_apply, smul_eq_mul, sub_apply, TestFunction.lineDerivOp_apply, real_inner_comm η v]
  ring

/-- The localized Fourier transform of a directional derivative:
`(∂_v T) (φ e_η) = 2πi ⟪v, η⟫ T (φ e_η) - T ((∂_v φ) e_η)`. -/
theorem localFourier_lineDerivOp (T : 𝓓'(Ω, ℂ)) (v : E) (φ : 𝓓(Ω, ℂ)) (η : E) :
    (∂_{v} T).localFourier φ η =
      2 * π * I * ((⟪v, η⟫ : ℝ) : ℂ) * T.localFourier φ η - T.localFourier (∂_{v} φ) η := by
  simp only [localFourier_eq_complexPairing_charMul, complexPairing_lineDerivOp,
    lineDerivOp_charMul, map_sub, map_smul, smul_eq_mul]
  ring

/-! ### Multiplication by a smooth function -/

variable [FiniteDimensional ℝ E] {T : 𝓓'(Ω, ℂ)} {x ξ : E}

/-- A smooth multiple of `T` is microlocally smooth wherever `T` is. -/
theorem IsMicrolocallySmoothAt.smulLeftCLM (h : T.IsMicrolocallySmoothAt x ξ)
    (hg : ContDiff ℝ ∞ g) : (smulLeftCLM hg T).IsMicrolocallySmoothAt x ξ := by
  obtain ⟨U, hU, Γ, hΓ, hξ, hcone, hd⟩ := h.exists_nhds_cone
  obtain ⟨ψ, hψ, hψx⟩ := TestFunction.exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem hU (Ω.isOpen.mem_nhds h.mem)) inter_subset_right (1 : ℂ)
  refine isMicrolocallySmoothAt_iff.2 ⟨ψ, by simp [hψx], Γ, hΓ, hξ, hcone, fun N ↦ ?_⟩
  simp_rw [localFourier_smulLeftCLM]
  exact hd _ ((TestFunction.tsupport_smulLeftCLM_subset hg ψ).trans
    (inter_subset_right.trans (hψ.trans inter_subset_left))) N

/-- Near a point where `g` does not vanish, `T` is microlocally smooth wherever `g T` is. -/
theorem IsMicrolocallySmoothAt.of_smulLeftCLM (hg : ContDiff ℝ ∞ g) (hgx : g x ≠ 0)
    (h : (Distribution.smulLeftCLM hg T).IsMicrolocallySmoothAt x ξ) :
    T.IsMicrolocallySmoothAt x ξ := by
  obtain ⟨U, hU, Γ, hΓ, hξ, hcone, hd⟩ := h.exists_nhds_cone
  -- A cutoff `χ` equal to one near `x`, supported where `g ≠ 0`, and the smooth function `χ / g`.
  obtain ⟨χ, hχ, -, hχ1, -, hχs⟩ := (isCompact_singleton (x := x)).exists_contDiff_cutoff
    (isOpen_ne_fun hg.continuous continuous_const) (singleton_subset_iff.2 hgx)
  let θ : E → ℝ := fun y ↦ χ y • (g y)⁻¹
  have hθ : ContDiff ℝ ∞ θ := (hg.contDiffOn.inv fun _ hy ↦ hy).contDiff_smul_of_tsupport_subset
    (isOpen_ne_fun hg.continuous continuous_const) hχ.contDiffOn hχs
  obtain ⟨ψ, hψ, hψx⟩ := TestFunction.exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem (inter_mem hU (isOpen_interior.mem_nhds (hχ1 rfl))) (Ω.isOpen.mem_nhds h.mem))
    inter_subset_right (1 : ℂ)
  refine isMicrolocallySmoothAt_iff.2 ⟨ψ, by simp [hψx], Γ, hΓ, hξ, hcone, fun N ↦ ?_⟩
  -- On the support of `ψ`, `χ = 1`, so `ψ = g (θ ψ)`.
  have hψ' : TestFunction.smulLeftCLM (hg.mul hθ) ψ = ψ := by
    ext y
    by_cases hψy : ψ y = 0
    · simp [hψy]
    · have hχy : χ y = 1 :=
        interior_subset ((hψ.trans (inter_subset_left.trans inter_subset_right))
          (subset_tsupport _ hψy))
      have hgy : g y ≠ 0 := hχs (subset_tsupport _ (by simp [hχy]))
      simp [θ, hχy, hgy]
  have hloc (η : E) : T.localFourier ψ η =
      (Distribution.smulLeftCLM hg T).localFourier (TestFunction.smulLeftCLM hθ ψ) η := by
    rw [localFourier_smulLeftCLM, TestFunction.smulLeftCLM_smulLeftCLM, hψ']
  simp_rw [hloc]
  exact hd _ ((TestFunction.tsupport_smulLeftCLM_subset hθ ψ).trans
    (inter_subset_right.trans (hψ.trans (inter_subset_left.trans inter_subset_left)))) N

/-- Near a point where `g` does not vanish, `g T` and `T` are microlocally smooth in the same
directions. -/
theorem isMicrolocallySmoothAt_smulLeftCLM_iff (hg : ContDiff ℝ ∞ g) (hgx : g x ≠ 0) :
    (smulLeftCLM hg T).IsMicrolocallySmoothAt x ξ ↔ T.IsMicrolocallySmoothAt x ξ :=
  ⟨IsMicrolocallySmoothAt.of_smulLeftCLM hg hgx, fun h ↦ h.smulLeftCLM hg⟩

/-- **Smooth multiplication.** The wave front set of `g T` lies in that of `T`. -/
theorem waveFrontSet_smulLeftCLM_subset (hg : ContDiff ℝ ∞ g) (T : 𝓓'(Ω, ℂ)) :
    (smulLeftCLM hg T).waveFrontSet ⊆ T.waveFrontSet := by
  rintro ⟨y, ζ⟩ hp
  rw [mem_waveFrontSet_iff] at hp ⊢
  exact ⟨hp.1, hp.2.1, fun h ↦ hp.2.2 (h.smulLeftCLM hg)⟩

/-- Over a point where `g` does not vanish, `g T` and `T` have the same wave front set. -/
theorem mem_waveFrontSet_smulLeftCLM_iff (hg : ContDiff ℝ ∞ g) (hgx : g x ≠ 0) :
    (x, ξ) ∈ (smulLeftCLM hg T).waveFrontSet ↔ (x, ξ) ∈ T.waveFrontSet := by
  simp [isMicrolocallySmoothAt_smulLeftCLM_iff hg hgx]

/-! ### Differentiation -/

/-- A directional derivative of `T` is microlocally smooth wherever `T` is. -/
theorem IsMicrolocallySmoothAt.lineDerivOp (h : T.IsMicrolocallySmoothAt x ξ) (v : E) :
    (∂_{v} T).IsMicrolocallySmoothAt x ξ := by
  obtain ⟨U, hU, Γ, hΓ, hξ, hcone, hd⟩ := h.exists_nhds_cone
  obtain ⟨ψ, hψ, hψx⟩ := TestFunction.exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem hU (Ω.isOpen.mem_nhds h.mem)) inter_subset_right (1 : ℂ)
  have hψU : tsupport ψ ⊆ U := hψ.trans inter_subset_left
  refine isMicrolocallySmoothAt_iff.2 ⟨ψ, by simp [hψx], Γ, hΓ, hξ, hcone, fun N ↦ ?_⟩
  -- The factor `⟪v, η⟫` costs one order of decay of `T (ψ e_η)`.
  obtain ⟨C, hC⟩ := hd ψ hψU (N + 1)
  obtain ⟨C', hC'⟩ := hd _ ((TestFunction.tsupport_lineDerivOp_subset v ψ).trans hψU) N
  refine ⟨2 * π * ‖v‖ * C + C', fun η hη ↦ ?_⟩
  rw [localFourier_lineDerivOp]
  have hinner : ‖2 * π * I * ((⟪v, η⟫ : ℝ) : ℂ)‖ ≤ 2 * π * ‖v‖ * (1 + ‖η‖) := by
    rw [norm_mul, norm_mul, norm_mul, norm_I, Complex.norm_real, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_of_nonneg pi_pos.le, mul_one, mul_assoc (2 * π)]
    gcongr
    exact (norm_inner_le_norm v η).trans (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg v))
  calc (1 + ‖η‖) ^ N * ‖2 * π * I * ((⟪v, η⟫ : ℝ) : ℂ) * T.localFourier ψ η -
        T.localFourier (∂_{v} ψ) η‖
      ≤ (1 + ‖η‖) ^ N * (‖2 * π * I * ((⟪v, η⟫ : ℝ) : ℂ)‖ * ‖T.localFourier ψ η‖) +
          (1 + ‖η‖) ^ N * ‖T.localFourier (∂_{v} ψ) η‖ := by
        rw [← mul_add, ← norm_mul]
        gcongr
        exact norm_sub_le _ _
    _ ≤ (1 + ‖η‖) ^ N * (2 * π * ‖v‖ * (1 + ‖η‖) * ‖T.localFourier ψ η‖) +
          (1 + ‖η‖) ^ N * ‖T.localFourier (∂_{v} ψ) η‖ := by
        gcongr
    _ = 2 * π * ‖v‖ * ((1 + ‖η‖) ^ (N + 1) * ‖T.localFourier ψ η‖) +
          (1 + ‖η‖) ^ N * ‖T.localFourier (∂_{v} ψ) η‖ := by
        ring
    _ ≤ 2 * π * ‖v‖ * C + C' := by
        gcongr
        · exact hC η hη
        · exact hC' η hη

/-- **Differentiation.** The wave front set of `∂_v T` lies in that of `T`. -/
theorem waveFrontSet_lineDerivOp_subset (v : E) (T : 𝓓'(Ω, ℂ)) :
    (∂_{v} T).waveFrontSet ⊆ T.waveFrontSet := by
  rintro ⟨y, ζ⟩ hp
  rw [mem_waveFrontSet_iff] at hp ⊢
  exact ⟨hp.1, hp.2.1, fun h ↦ hp.2.2 (h.lineDerivOp v)⟩

/-- The wave front set of an iterated directional derivative `∂^{m} T` lies in that of `T`. -/
theorem waveFrontSet_iteratedLineDerivOp_subset {k : ℕ} (m : Fin k → E) (T : 𝓓'(Ω, ℂ)) :
    (∂^{m} T).waveFrontSet ⊆ T.waveFrontSet := by
  induction k with
  | zero => simp [iteratedLineDerivOp_fin_zero]
  | succ k ih =>
    rw [iteratedLineDerivOp_succ_left]
    exact (waveFrontSet_lineDerivOp_subset _ _).trans (ih _)

/-- **Differential operators do not enlarge the wave front set.** For a linear differential
operator `P T = ∑ᵢ cᵢ gᵢ ∂^{mᵢ} T` with complex constants `cᵢ` and smooth real coefficients `gᵢ`,
`WF(P T) ⊆ WF(T)`. -/
theorem waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) {g : ι → E → ℝ} (hg : ∀ i, ContDiff ℝ ∞ (g i)) {k : ι → ℕ}
    (m : ∀ i, Fin (k i) → E) (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ s, c i • smulLeftCLM (hg i) (∂^{m i} T)).waveFrontSet ⊆ T.waveFrontSet := by
  refine (waveFrontSet_sum_subset s _).trans (iUnion₂_subset fun i _ ↦ ?_)
  exact (waveFrontSet_smul_subset _ _).trans ((waveFrontSet_smulLeftCLM_subset _ _).trans
    (waveFrontSet_iteratedLineDerivOp_subset _ _))

end Distribution
