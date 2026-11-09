/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SmulLeft
public import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.PositiveDefinite.FourierAtom

/-!
# The wave front set of a smooth multiple

Multiplying a complex distribution `T` by a smooth complex function `g` cannot create
singularities: `WF(g T) ⊆ WF(T)`, and the wave front set of `g T` lies over the closed support of
`g`. Where `g` does not vanish nothing is lost either, since `T = g⁻¹ (g T)` near such a point.
So the wave front set of `g T` agrees with that of `T` over `{g ≠ 0}`, and `WF(g T) = WF(T)` for
a multiplier with no zeros in `Ω` (Hörmander I, §8.1).

The localized Fourier transform of `g T` with cutoff `φ` is that of `T` with cutoff `g φ`
(`Distribution.localFourier_smulLeftCLM`). By the independence of the cutoff
(`Distribution.IsMicrolocallySmoothAt.exists_nhds_cone`), rapid decay in a cone holds for every
cutoff supported in a neighbourhood of the base point, in particular for `g φ`; conversely, near a
point where `g ≠ 0`, every cutoff `ψ` is `g (g⁻¹ ψ)`.

## Main results

* `Distribution.localFourier_smulLeftCLM`: the localized Fourier transform of `g T`.
* `Distribution.IsMicrolocallySmoothAt.smulLeftCLM`: `g T` is microlocally smooth wherever `T`
  is, and `Distribution.isMicrolocallySmoothAt_smulLeftCLM_of_notMem_tsupport`: everywhere outside
  the closed support of `g`.
* `Distribution.isMicrolocallySmoothAt_smulLeftCLM_iff`: at a point where `g ≠ 0`, `g T` and `T`
  are microlocally smooth in the same directions.
* `Distribution.waveFrontSet_smulLeftCLM_subset`: `WF(g T) ⊆ WF(T) ∩ (tsupport g × E)`.
* `Distribution.mem_waveFrontSet_smulLeftCLM_iff`, `Distribution.waveFrontSet_smulLeftCLM`: over
  the points where `g ≠ 0` the two wave front sets agree; they are equal if `g` has no zeros in
  `Ω`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.1.
-/

public section

noncomputable section

open Complex Filter Function Set TopologicalSpace TestFunction
open scoped Distributions Topology ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Opens E}
  {g : E → ℂ}

/-- The localized Fourier transform of `g T` with cutoff `φ` is the localized Fourier transform of
`T` with cutoff `g φ`. -/
@[simp]
theorem localFourier_smulLeftCLM (hg : ContDiff ℝ ∞ g) (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) (η : E) :
    (smulLeftCLM hg T).localFourier φ η =
      T.localFourier (bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) hg φ) η := by
  rw [localFourier_eq _ φ (ψ := bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ)
    (TauCeti.contDiff_fourierAtom η) φ) fun x ↦ ?_, complexPairing_smulLeftCLM]
  · refine (localFourier_eq T _ fun x ↦ ?_).symm
    simp [bilinLeftCLM_apply, TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply]
    ring
  · simp [bilinLeftCLM_apply, TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply]

variable [FiniteDimensional ℝ E]

/-- **Smooth multiplication does not create singularities.** If `T` is microlocally smooth at
`(x, ξ)`, so is `g T` for every smooth `g`. -/
theorem IsMicrolocallySmoothAt.smulLeftCLM {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (h : T.IsMicrolocallySmoothAt x ξ) (hg : ContDiff ℝ ∞ g) :
    (smulLeftCLM hg T).IsMicrolocallySmoothAt x ξ := by
  obtain ⟨U, hU, Γ, hΓ, hξ, hcone, hdecay⟩ := h.exists_nhds_cone
  -- A cutoff supported in `U`; the cutoff `g ψ` is then supported in `U` as well.
  obtain ⟨ψ, hψ, hψx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem hU (Ω.isOpen.mem_nhds h.mem)) inter_subset_right (1 : ℂ)
  refine isMicrolocallySmoothAt_iff.2 ⟨ψ, by simp [hψx], Γ, hΓ, hξ, hcone, fun N ↦ ?_⟩
  simp_rw [localFourier_smulLeftCLM]
  refine hdecay _ (Subset.trans ?_ (hψ.trans inter_subset_left)) N
  simpa [bilinLeftCLM_apply] using tsupport_mul_subset_left (f := ⇑ψ) (g := g)

/-- **No wave front set off the support of the multiplier.** At a point `x ∈ Ω` outside the
closed support of `g`, the product `g T` is microlocally smooth in every direction. -/
theorem isMicrolocallySmoothAt_smulLeftCLM_of_notMem_tsupport (hg : ContDiff ℝ ∞ g)
    (T : 𝓓'(Ω, ℂ)) {x : E} (hx : x ∈ Ω) (hgx : x ∉ tsupport g) (ξ : E) :
    (smulLeftCLM hg T).IsMicrolocallySmoothAt x ξ := by
  -- A cutoff supported off `tsupport g`; the cutoff `g ψ` then vanishes.
  obtain ⟨ψ, hψ, hψx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem ((isClosed_tsupport g).isOpen_compl.mem_nhds hgx) (Ω.isOpen.mem_nhds hx))
    inter_subset_right (1 : ℂ)
  have hgψ : bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) hg ψ = 0 := by
    ext y
    by_cases hy : ψ y = 0
    · simp [bilinLeftCLM_apply, hy]
    · simp [bilinLeftCLM_apply,
        image_eq_zero_of_notMem_tsupport (inter_subset_left (hψ (subset_tsupport _ hy)))]
  exact isMicrolocallySmoothAt_of_forall_decay (φ := ψ) (by simp [hψx])
    (fun N ↦ ⟨0, fun η ↦ by simp [hgψ]⟩) ξ

/-- **Microlocal smoothness where the multiplier does not vanish.** If `g x ≠ 0`, then `g T` is
microlocally smooth at `(x, ξ)` exactly when `T` is. -/
theorem isMicrolocallySmoothAt_smulLeftCLM_iff (hg : ContDiff ℝ ∞ g) {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (hgx : g x ≠ 0) :
    (smulLeftCLM hg T).IsMicrolocallySmoothAt x ξ ↔ T.IsMicrolocallySmoothAt x ξ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.smulLeftCLM hg⟩
  obtain ⟨U, hU, Γ, hΓ, hξ, hcone, hdecay⟩ := h.exists_nhds_cone
  -- A cutoff `ψ` supported in `U` where `g ≠ 0`, written as `g θ` with `θ = g⁻¹ ψ`.
  obtain ⟨ψ, hψ, hψx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem (inter_mem hU ((isOpen_ne_fun hg.continuous continuous_const).mem_nhds hgx))
      (Ω.isOpen.mem_nhds h.mem)) inter_subset_right (1 : ℂ)
  have hψg {y : E} (hy : y ∈ tsupport ψ) : g y ≠ 0 := (inter_subset_left (hψ hy)).2
  have hθ : ContDiff ℝ ∞ fun y ↦ (g y)⁻¹ * ψ y :=
    (ContinuousLinearMap.mul ℝ ℂ).contDiff_of_tsupport_subset_right
      (hg.contDiffOn.inv fun _ hy ↦ hy) ψ.contDiff.contDiffOn
      (isOpen_ne_fun hg.continuous continuous_const) fun _ hy ↦ hψg hy
  have hθs : tsupport (fun y ↦ (g y)⁻¹ * ψ y) ⊆ tsupport ψ := tsupport_mul_subset_right
  let θ : 𝓓(Ω, ℂ) := ⟨fun y ↦ (g y)⁻¹ * ψ y, hθ,
    ψ.hasCompactSupport.mono' ((subset_tsupport _).trans hθs), hθs.trans ψ.tsupport_subset⟩
  have hgθ : bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) hg θ = ψ := by
    ext y
    by_cases hy : y ∈ tsupport ψ
    · simp [bilinLeftCLM_apply, θ, mul_comm _ (g y), mul_inv_cancel_left₀ (hψg hy)]
    · simp [bilinLeftCLM_apply, θ, image_eq_zero_of_notMem_tsupport hy]
  refine isMicrolocallySmoothAt_iff.2 ⟨ψ, by simp [hψx], Γ, hΓ, hξ, hcone, fun N ↦ ?_⟩
  simp_rw [← hgθ, ← localFourier_smulLeftCLM]
  exact hdecay θ (hθs.trans (hψ.trans (inter_subset_left.trans inter_subset_left))) N

/-- **The wave front set of a smooth multiple.** `WF(g T)` lies in `WF(T)`, over the closed
support of `g`. -/
theorem waveFrontSet_smulLeftCLM_subset (hg : ContDiff ℝ ∞ g) (T : 𝓓'(Ω, ℂ)) :
    (smulLeftCLM hg T).waveFrontSet ⊆ T.waveFrontSet ∩ Prod.fst ⁻¹' tsupport g := by
  rintro ⟨x, ξ⟩ hp
  obtain ⟨hx, hξ, h⟩ := mem_waveFrontSet_iff.1 hp
  refine ⟨mem_waveFrontSet_iff.2 ⟨hx, hξ, fun hT ↦ h (hT.smulLeftCLM hg)⟩, ?_⟩
  by_contra hgx
  exact h (isMicrolocallySmoothAt_smulLeftCLM_of_notMem_tsupport hg T hx hgx ξ)

/-- Over a point where `g ≠ 0`, the wave front sets of `g T` and `T` agree. -/
theorem mem_waveFrontSet_smulLeftCLM_iff (hg : ContDiff ℝ ∞ g) {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (hgx : g x ≠ 0) : (x, ξ) ∈ (smulLeftCLM hg T).waveFrontSet ↔ (x, ξ) ∈ T.waveFrontSet := by
  simp only [mem_waveFrontSet_iff, isMicrolocallySmoothAt_smulLeftCLM_iff hg hgx]

/-- Multiplication by a smooth function with no zeros in `Ω` preserves the wave front set. -/
theorem waveFrontSet_smulLeftCLM (hg : ContDiff ℝ ∞ g) (hg₀ : ∀ x ∈ Ω, g x ≠ 0)
    (T : 𝓓'(Ω, ℂ)) : (smulLeftCLM hg T).waveFrontSet = T.waveFrontSet := by
  ext ⟨x, ξ⟩
  by_cases hx : x ∈ Ω
  · exact mem_waveFrontSet_smulLeftCLM_iff hg (hg₀ x hx)
  · simp [mem_waveFrontSet_iff, hx]

end Distribution
