/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SmulLeft
public import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.PositiveDefinite.FourierAtom

/-!
# Differential operators do not enlarge the wave front set

Let `T` be a complex distribution on an open subset `Ω` of a finite-dimensional real inner product
space `E`. This file shows that multiplication by a smooth function and directional
differentiation do not enlarge the wave front set of `T`. Consequently a linear differential
operator `P = ∑ᵢ cᵢ gᵢ ∂^{mᵢ}` with smooth coefficients satisfies `WF(P T) ⊆ WF(T)`: differential
operators are *microlocal*.

Both statements are read off the localized Fourier transform `η ↦ T (φ e_η)` of
`Distribution.localFourier`, where `e_η x = 𝐞 (-⟪x, η⟫)`:

* for a smooth function `g`, the transform of `g T` with cutoff `φ` is the transform of `T` with
  cutoff `g φ` (`Distribution.localFourier_smulLeftCLM`);
* for a direction `v`, differentiating `φ e_η` gives the identity
  `(∂_v T)^(φ, η) = 2πi ⟪v, η⟫ T^(φ, η) - T^(∂_v φ, η)`
  (`Distribution.localFourier_lineDerivOp`).

In both cases the cutoffs on the right are supported in the support of `φ`. By the independence of
the cutoff (`Distribution.IsMicrolocallySmoothAt.exists_nhds_cone`), rapid decay of the transforms
of `T` in a cone for every cutoff supported near `x` gives rapid decay of the transforms of `g T`
and `∂_v T` in the same cone; the factor `⟪v, η⟫` costs one power of `1 + ‖η‖`.

Multiplication by `g` is microlocally invertible where `g` does not vanish, so there the wave front
sets of `T` and `g T` agree. No such converse holds for derivatives: on `ℝ²` the distribution of the
function `(x, y) ↦ H(x)`, with `H` the Heaviside function, is singular along `x = 0`, while its
derivative in `y` vanishes.

## Main results

* `Distribution.waveFrontSet_smulLeftCLM_subset`: `WF(g T) ⊆ WF(T) ∩ (supp g × E)`.
* `Distribution.isMicrolocallySmoothAt_smulLeftCLM_iff`,
  `Distribution.waveFrontSet_inter_subset_waveFrontSet_smulLeftCLM`: over the points where
  `g ≠ 0`, the wave front sets of `g T` and `T` agree.
* `Distribution.waveFrontSet_lineDerivOp_subset`,
  `Distribution.waveFrontSet_iteratedLineDerivOp_subset`: `WF(∂_v T) ⊆ WF(T)`, and the same for
  iterated derivatives.
* `Distribution.waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset`: `WF(P T) ⊆ WF(T)`
  for every linear differential operator `P` with smooth coefficients.

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
  {T : 𝓓'(Ω, ℂ)} {x ξ : E} {g : E → ℝ}

/-- The modulated cutoff `φ e_η` paired with `T` in `Distribution.localFourier T φ η`. -/
private theorem bilinLeftCLM_fourierAtom_apply (φ : 𝓓(Ω, ℂ)) (η y : E) :
    bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) φ y =
      φ y * 𝐞 (-⟪y, η⟫) := by
  simp [bilinLeftCLM_apply, TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply]

/-! ### Multiplication by a smooth function -/

/-- The localized Fourier transform of a smooth multiple `g T` with cutoff `φ` is that of `T` with
cutoff `g φ`. -/
@[simp]
theorem localFourier_smulLeftCLM (hg : ContDiff ℝ ∞ g) (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) (η : E) :
    (smulLeftCLM hg T).localFourier φ η = T.localFourier (TestFunction.smulLeftCLM hg φ) η := by
  rw [localFourier_eq _ φ (bilinLeftCLM_fourierAtom_apply φ η), complexPairing_smulLeftCLM,
    localFourier_eq T _ fun y ↦ ?_]
  simp [bilinLeftCLM_fourierAtom_apply, mul_assoc]

/-- If `g T` is microlocally smooth at `(x, ξ)` and `g x ≠ 0`, then so is `T`: the cutoff `g φ`
does not vanish at `x`. -/
theorem IsMicrolocallySmoothAt.of_smulLeftCLM (hg : ContDiff ℝ ∞ g) (hgx : g x ≠ 0)
    (h : (smulLeftCLM hg T).IsMicrolocallySmoothAt x ξ) : T.IsMicrolocallySmoothAt x ξ := by
  obtain ⟨φ, hφ, Γ, hΓ, hξ, hcone, hdecay⟩ := isMicrolocallySmoothAt_iff.1 h
  refine isMicrolocallySmoothAt_iff.2
    ⟨TestFunction.smulLeftCLM hg φ, ?_, Γ, hΓ, hξ, hcone, fun N ↦ ?_⟩
  · simpa [smulLeftCLM_apply] using smul_ne_zero hgx hφ
  · simpa only [localFourier_smulLeftCLM] using hdecay N

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- **Transfer of decay to nearby cutoffs.** If `T` is microlocally smooth at `(x, ξ)`, there are
an open cone `Γ` containing `ξ` and a cutoff `ψ` with `ψ x = 1` such that the localized Fourier
transform of `T` decays rapidly on `Γ` for every cutoff supported in the support of `ψ`. -/
private theorem IsMicrolocallySmoothAt.exists_cutoff_cone (h : T.IsMicrolocallySmoothAt x ξ) :
    ∃ ψ : 𝓓(Ω, ℂ), ψ x = 1 ∧ ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧
      (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ tsupport ψ →
        ∀ N : ℕ, ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ N * ‖T.localFourier φ η‖ ≤ C := by
  have hx : x ∈ Ω := by
    obtain ⟨φ, hφ, -⟩ := isMicrolocallySmoothAt_iff.1 h
    exact φ.tsupport_subset (subset_tsupport _ hφ)
  obtain ⟨U, hU, Γ, hΓ, hξ, hcone, hdecay⟩ := h.exists_nhds_cone
  obtain ⟨ψ, hψ, hψx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem hU (Ω.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
  exact ⟨ψ, hψx, Γ, hΓ, hξ, hcone, fun φ hφ ↦ hdecay φ (hφ.trans (hψ.trans inter_subset_left))⟩

/-- A smooth multiple of a distribution microlocally smooth at `(x, ξ)` is microlocally smooth
there. -/
theorem IsMicrolocallySmoothAt.smulLeftCLM (h : T.IsMicrolocallySmoothAt x ξ)
    (hg : ContDiff ℝ ∞ g) : (smulLeftCLM hg T).IsMicrolocallySmoothAt x ξ := by
  obtain ⟨ψ, hψx, Γ, hΓ, hξ, hcone, hdecay⟩ := h.exists_cutoff_cone
  refine isMicrolocallySmoothAt_iff.2 ⟨ψ, by simp [hψx], Γ, hΓ, hξ, hcone, fun N ↦ ?_⟩
  simpa only [localFourier_smulLeftCLM] using
    hdecay _ ((TestFunction.tsupport_smulLeftCLM_subset hg ψ).trans inter_subset_right) N

/-- Where `g` does not vanish, `g T` is microlocally smooth exactly where `T` is. -/
theorem isMicrolocallySmoothAt_smulLeftCLM_iff (hg : ContDiff ℝ ∞ g) (hgx : g x ≠ 0) :
    (smulLeftCLM hg T).IsMicrolocallySmoothAt x ξ ↔ T.IsMicrolocallySmoothAt x ξ :=
  ⟨.of_smulLeftCLM hg hgx, fun h ↦ h.smulLeftCLM hg⟩

/-- **Multiplication by a smooth function does not enlarge the wave front set**, and the wave
front set of `g T` lies over the support of `g`. -/
theorem waveFrontSet_smulLeftCLM_subset (hg : ContDiff ℝ ∞ g) (T : 𝓓'(Ω, ℂ)) :
    (smulLeftCLM hg T).waveFrontSet ⊆ T.waveFrontSet ∩ tsupport g ×ˢ univ := by
  rintro ⟨y, η⟩ hp
  obtain ⟨hy, hη, hT⟩ := mem_waveFrontSet_iff.1 hp
  exact ⟨mem_waveFrontSet_iff.2 ⟨hy, hη, fun h ↦ hT (h.smulLeftCLM hg)⟩,
    ((dsupport_smulLeftCLM_subset_inter hg T) (waveFrontSet_subset_dsupport _ hp).1).1, trivial⟩

omit [FiniteDimensional ℝ E] in
/-- Over the points where `g` does not vanish, the wave front set of `T` lies in that of `g T`.
With `Distribution.waveFrontSet_smulLeftCLM_subset`, the two wave front sets agree there. -/
theorem waveFrontSet_inter_subset_waveFrontSet_smulLeftCLM (hg : ContDiff ℝ ∞ g)
    (T : 𝓓'(Ω, ℂ)) :
    T.waveFrontSet ∩ {y | g y ≠ 0} ×ˢ univ ⊆ (smulLeftCLM hg T).waveFrontSet := by
  rintro ⟨y, η⟩ ⟨hp, hgy, -⟩
  obtain ⟨hy, hη, hT⟩ := mem_waveFrontSet_iff.1 hp
  exact mem_waveFrontSet_iff.2 ⟨hy, hη, fun h ↦ hT (h.of_smulLeftCLM hg hgy)⟩

end FiniteDimensional

/-! ### Directional derivatives -/

/-- The derivative of the modulated cutoff `φ e_η` in the direction `v` is
`(∂_v φ) e_η - 2πi ⟪v, η⟫ φ e_η`. -/
private theorem lineDerivOp_bilinLeftCLM_fourierAtom (φ : 𝓓(Ω, ℂ)) (v η : E) :
    ∂_{v} (bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) φ) =
      bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) (∂_{v} φ) -
        (2 * Real.pi * I * ⟪v, η⟫) •
          bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) φ := by
  ext y
  have he : HasFDerivAt (TauCeti.fourierAtom η)
      ((-2 * Real.pi * I * TauCeti.fourierAtom η y) • (ofRealCLM ∘L (innerSL ℝ).flip η)) y := by
    have h := Real.hasFDerivAt_fourierChar_neg_bilinear_left (innerSL ℝ) y η
    rw [show (fun z : E ↦ ((𝐞 (-(innerSL ℝ z) η) : Circle) : ℂ)) = TauCeti.fourierAtom η from
      funext fun z ↦ (TauCeti.fourierAtom_eq_fourierChar η z).symm] at h
    convert h using 4
    exact TauCeti.fourierAtom_eq_fourierChar η y
  have hφ : HasFDerivAt (φ : E → ℂ) (fderiv ℝ φ y) y :=
    (φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hχ (ψ : 𝓓(Ω, ℂ)) :
      ⇑(bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) ψ) =
        fun z ↦ ψ z * TauCeti.fourierAtom η z :=
    funext fun z ↦ by simp [bilinLeftCLM_apply, mul_comm]
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
  have hdψ : tsupport ⇑(∂_{v} ψ : 𝓓(Ω, ℂ)) ⊆ tsupport ψ := by
    rw [TestFunction.lineDerivOp_eq_lineDerivCLM ℝ, coe_lineDerivCLM]
    refine (tsupport_fderiv_apply_subset ℝ v).trans_eq' (congrArg tsupport (funext fun y ↦ ?_))
    exact ((ψ.contDiff.differentiable (by simp)).differentiableAt).lineDeriv_eq_fderiv.symm
  obtain ⟨C₁, hC₁⟩ := hdecay ψ subset_rfl (N + 1)
  obtain ⟨C₂, hC₂⟩ := hdecay (∂_{v} ψ) hdψ N
  refine ⟨2 * Real.pi * ‖v‖ * C₁ + C₂, fun η hη ↦ ?_⟩
  have h₁ := hC₁ η hη
  have h₂ := hC₂ η hη
  have hη₁ : ‖η‖ ≤ 1 + ‖η‖ := le_add_of_nonneg_left zero_le_one
  have hinner : ‖(2 * Real.pi * I * ⟪v, η⟫ : ℂ)‖ ≤ 2 * Real.pi * ‖v‖ * (1 + ‖η‖) := by
    rw [norm_mul, norm_mul, norm_mul, norm_I, mul_one, Complex.norm_real, Complex.norm_two,
      Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, mul_assoc (2 * Real.pi)]
    gcongr
    exact (norm_inner_le_norm v η).trans (by gcongr)
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
`P = ∑ᵢ cᵢ gᵢ ∂^{mᵢ}` with complex constants `cᵢ`, smooth real functions `gᵢ` and iterated
directional derivatives `∂^{mᵢ}` satisfies `WF(P T) ⊆ WF(T)`. Every differential operator with
smooth complex coefficients has this form, by splitting each coefficient into its real and
imaginary parts. -/
theorem waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) {g : ι → E → ℝ} (hg : ∀ i, ContDiff ℝ ∞ (g i)) {k : ι → ℕ}
    (m : (i : ι) → Fin (k i) → E) (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ s, c i • smulLeftCLM (hg i) (∂^{m i} T)).waveFrontSet ⊆ T.waveFrontSet :=
  (waveFrontSet_sum_subset _ _).trans <| iUnion₂_subset fun _ _ ↦
    (waveFrontSet_smul_subset _ _).trans <| (waveFrontSet_smulLeftCLM_subset _ _).trans <|
      inter_subset_left.trans (waveFrontSet_iteratedLineDerivOp_subset _ _)

end Distribution
