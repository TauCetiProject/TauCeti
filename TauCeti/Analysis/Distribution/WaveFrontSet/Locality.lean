/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SmulLeft
public import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.PositiveDefinite.FourierAtom

/-!
# The wave front set under restriction and smooth multiplication

The wave front set of a distribution is a local object. This file proves the two basic
statements expressing this.

* **Restriction.** For an open set `Ω' ⊆ Ω`, the wave front set of the restriction `T|Ω'` is the
  part of the wave front set of `T` lying over `Ω'`.
* **Smooth multiplication.** For a smooth real function `g`, the wave front set of `g T` lies in
  that of `T`, over the support of `g`, and the two agree over every point where `g` does not
  vanish (Hörmander I, §8.1). The multiplier is real; a complex multiplier `a + i b` acts as
  `a T + i (b T)`, to which `Distribution.waveFrontSet_add_subset` and
  `Distribution.waveFrontSet_smul_subset` apply.

Both follow from the independence of the cutoff
(`Distribution.IsMicrolocallySmoothAt.exists_nhds_cone`): near a point of microlocal smoothness,
every cutoff supported close enough to the point gives rapid decay on a fixed cone. The localized
Fourier transform of `T|Ω'` with cutoff `φ` is that of `T` with `φ` extended by zero, and the
one of `g T` with cutoff `φ` is that of `T` with cutoff `g φ`.

## Main results

* `Distribution.localFourier_restrictCLM`, `Distribution.localFourier_smulLeftCLM`: the
  localized Fourier transforms of `T|Ω'` and of `g T`.
* `Distribution.isMicrolocallySmoothAt_restrictCLM_iff`, `Distribution.waveFrontSet_restrictCLM`:
  `WF(T|Ω') = WF(T) ∩ (Ω' × E)`.
* `Distribution.IsMicrolocallySmoothAt.smulLeftCLM`,
  `Distribution.waveFrontSet_smulLeftCLM_subset`: `WF(g T) ⊆ WF(T) ∩ (tsupport g × E)`.
* `Distribution.isMicrolocallySmoothAt_smulLeftCLM_iff`,
  `Distribution.mem_waveFrontSet_smulLeftCLM_iff`: at a point `x` with `g x ≠ 0`, the
  distributions `g T` and `T` have the same wave front set, and
  `Distribution.waveFrontSet_smulLeftCLM_of_ne_zero` when `g` vanishes nowhere on `Ω`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.1.
-/

public section

noncomputable section

open Filter Set TopologicalSpace TestFunction
open scoped Distributions Topology ContDiff RealInnerProductSpace FourierTransform

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω Ω' : Opens E} {g : E → ℝ} {x ξ : E}

omit [FiniteDimensional ℝ E] in
/-- The modulated cutoff `y ↦ φ y e_η y` paired with a distribution in `Distribution.localFourier`,
evaluated pointwise. -/
private theorem bilinLeftCLM_mul_fourierAtom_apply {Ω : Opens E} (φ : 𝓓(Ω, ℂ)) (η y : E) :
    bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) φ y =
      φ y * 𝐞 (-⟪y, η⟫) := by
  simp [TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply]

/-! ### Restriction to an open subset -/

section Restriction

omit [FiniteDimensional ℝ E] in
/-- The localized Fourier transform of the restriction `T|Ω'` with cutoff `φ` is that of `T` with
`φ` extended by zero to `Ω`. -/
theorem localFourier_restrictCLM (h : Ω' ≤ Ω) (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω', ℂ)) (η : E) :
    (restrictCLM Ω' T).localFourier φ η = T.localFourier (monoCLM ℝ φ) η := by
  have hmod := bilinLeftCLM_mul_fourierAtom_apply φ η
  rw [localFourier_eq _ φ hmod, complexPairing_restrictCLM h]
  exact (localFourier_eq T _ fun y ↦ by simp [h, hmod]).symm

/-- The restriction of a distribution to an open set `Ω'` containing `x` is microlocally smooth at
`(x, ξ)` if the distribution is. -/
theorem IsMicrolocallySmoothAt.restrictCLM (h : Ω' ≤ Ω) (hx : x ∈ Ω') {T : 𝓓'(Ω, ℂ)}
    (hT : T.IsMicrolocallySmoothAt x ξ) : (restrictCLM Ω' T).IsMicrolocallySmoothAt x ξ := by
  obtain ⟨U, hU, Γ, hΓ, hξ, hcone, hdecay⟩ := hT.exists_nhds_cone
  -- A cutoff on `Ω'` supported in `U` serves for the restriction, on the same cone.
  obtain ⟨ψ, hψ, hψx⟩ := exists_tsupport_subset_apply_eq (Ω := Ω') (n := ⊤)
    (inter_mem hU (Ω'.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
  have hψU : tsupport (monoCLM ℝ ψ : 𝓓(Ω, ℂ)) ⊆ U := by
    simpa [h] using hψ.trans inter_subset_left
  refine isMicrolocallySmoothAt_iff.2 ⟨ψ, by simp [hψx], Γ, hΓ, hξ, hcone, fun N ↦ ?_⟩
  simpa only [localFourier_restrictCLM h] using hdecay (monoCLM ℝ ψ) hψU N

omit [FiniteDimensional ℝ E] in
/-- A distribution is microlocally smooth at `(x, ξ)` if its restriction to some open subset is. -/
theorem IsMicrolocallySmoothAt.of_restrictCLM (h : Ω' ≤ Ω) {T : 𝓓'(Ω, ℂ)}
    (hT : (Distribution.restrictCLM Ω' T).IsMicrolocallySmoothAt x ξ) :
    T.IsMicrolocallySmoothAt x ξ := by
  obtain ⟨φ, hφx, Γ, hΓ, hξ, hcone, hdecay⟩ := isMicrolocallySmoothAt_iff.1 hT
  refine isMicrolocallySmoothAt_iff.2
    ⟨monoCLM ℝ φ, by simpa [h] using hφx, Γ, hΓ, hξ, hcone, fun N ↦ ?_⟩
  simpa only [localFourier_restrictCLM h] using hdecay N

/-- Over a point `x` of an open subset `Ω'`, a distribution and its restriction to `Ω'` are
microlocally smooth in the same directions. -/
theorem isMicrolocallySmoothAt_restrictCLM_iff (h : Ω' ≤ Ω) (hx : x ∈ Ω') {T : 𝓓'(Ω, ℂ)} :
    (restrictCLM Ω' T).IsMicrolocallySmoothAt x ξ ↔ T.IsMicrolocallySmoothAt x ξ :=
  ⟨.of_restrictCLM h, .restrictCLM h hx⟩

/-- The wave front set of the restriction of `T` to an open subset `Ω'` is the part of the wave
front set of `T` lying over `Ω'`. -/
theorem waveFrontSet_restrictCLM (h : Ω' ≤ Ω) (T : 𝓓'(Ω, ℂ)) :
    (restrictCLM Ω' T).waveFrontSet = T.waveFrontSet ∩ (Ω' : Set E) ×ˢ univ := by
  ext ⟨x, ξ⟩
  simp only [mem_waveFrontSet_iff, mem_inter_iff, mem_prod, mem_univ, and_true,
    SetLike.mem_coe]
  constructor
  · rintro ⟨hx, hξ, hT⟩
    exact ⟨⟨h hx, hξ, fun hT' ↦ hT (hT'.restrictCLM h hx)⟩, hx⟩
  · rintro ⟨⟨-, hξ, hT⟩, hx⟩
    exact ⟨hx, hξ, fun hT' ↦ hT (hT'.of_restrictCLM h)⟩

end Restriction

/-! ### Multiplication by a smooth function -/

section SmoothMultiplication

omit [FiniteDimensional ℝ E] in
/-- The localized Fourier transform of `g T` with cutoff `φ` is that of `T` with cutoff `g φ`. -/
theorem localFourier_smulLeftCLM (hg : ContDiff ℝ ∞ g) (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) (η : E) :
    (smulLeftCLM hg T).localFourier φ η = T.localFourier (TestFunction.smulLeftCLM hg φ) η := by
  have hmod := bilinLeftCLM_mul_fourierAtom_apply φ η
  rw [localFourier_eq _ φ hmod, complexPairing_smulLeftCLM]
  exact (localFourier_eq T _ fun y ↦ by simp [hmod, mul_assoc]).symm

/-- If `T` is microlocally smooth at `(x, ξ)`, so is its product `g T` with a smooth function. -/
theorem IsMicrolocallySmoothAt.smulLeftCLM (hg : ContDiff ℝ ∞ g) {T : 𝓓'(Ω, ℂ)}
    (hT : T.IsMicrolocallySmoothAt x ξ) : (smulLeftCLM hg T).IsMicrolocallySmoothAt x ξ := by
  have hx : x ∈ Ω := by
    obtain ⟨φ, hφ, -⟩ := isMicrolocallySmoothAt_iff.1 hT
    exact φ.tsupport_subset (subset_tsupport _ hφ)
  obtain ⟨U, hU, Γ, hΓ, hξ, hcone, hdecay⟩ := hT.exists_nhds_cone
  -- For a cutoff `ψ` supported in `U`, the cutoff `g ψ` of `T` is supported in `U` as well.
  obtain ⟨ψ, hψ, hψx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem hU (Ω.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
  refine isMicrolocallySmoothAt_iff.2 ⟨ψ, by simp [hψx], Γ, hΓ, hξ, hcone, fun N ↦ ?_⟩
  simpa only [localFourier_smulLeftCLM] using hdecay (TestFunction.smulLeftCLM hg ψ)
    (((tsupport_smulLeftCLM_subset hg ψ).trans inter_subset_right).trans
      (hψ.trans inter_subset_left)) N

omit [FiniteDimensional ℝ E] in
/-- If `g T` is microlocally smooth at `(x, ξ)` and `g x ≠ 0`, then `T` is microlocally smooth
at `(x, ξ)`. -/
theorem IsMicrolocallySmoothAt.of_smulLeftCLM (hg : ContDiff ℝ ∞ g) (hgx : g x ≠ 0)
    {T : 𝓓'(Ω, ℂ)} (hT : (Distribution.smulLeftCLM hg T).IsMicrolocallySmoothAt x ξ) :
    T.IsMicrolocallySmoothAt x ξ := by
  obtain ⟨φ, hφx, Γ, hΓ, hξ, hcone, hdecay⟩ := isMicrolocallySmoothAt_iff.1 hT
  refine isMicrolocallySmoothAt_iff.2 ⟨TestFunction.smulLeftCLM hg φ, by simp [hgx, hφx], Γ, hΓ,
    hξ, hcone, fun N ↦ ?_⟩
  simpa only [localFourier_smulLeftCLM] using hdecay N

/-- At a point where the smooth function `g` does not vanish, `g T` and `T` are microlocally smooth
in the same directions. -/
theorem isMicrolocallySmoothAt_smulLeftCLM_iff (hg : ContDiff ℝ ∞ g) (hgx : g x ≠ 0)
    {T : 𝓓'(Ω, ℂ)} :
    (smulLeftCLM hg T).IsMicrolocallySmoothAt x ξ ↔ T.IsMicrolocallySmoothAt x ξ :=
  ⟨.of_smulLeftCLM hg hgx, .smulLeftCLM hg⟩

/-- The wave front set of `g T` lies in the wave front set of `T`, over the support of `g`. -/
theorem waveFrontSet_smulLeftCLM_subset (hg : ContDiff ℝ ∞ g) (T : 𝓓'(Ω, ℂ)) :
    (smulLeftCLM hg T).waveFrontSet ⊆ T.waveFrontSet ∩ tsupport g ×ˢ univ := by
  rintro ⟨x, ξ⟩ hp
  obtain ⟨hx, hξ, hgT⟩ := mem_waveFrontSet_iff.1 hp
  refine ⟨mem_waveFrontSet_iff.2 ⟨hx, hξ, fun hT ↦ hgT (hT.smulLeftCLM hg)⟩, ?_, mem_univ ξ⟩
  exact (dsupport_smulLeftCLM_subset_inter hg T (waveFrontSet_subset_dsupport _ hp).1).1

/-- Over a point where the smooth function `g` does not vanish, `g T` and `T` have the same wave
front set. -/
theorem mem_waveFrontSet_smulLeftCLM_iff (hg : ContDiff ℝ ∞ g) (hgx : g x ≠ 0)
    {T : 𝓓'(Ω, ℂ)} : (x, ξ) ∈ (smulLeftCLM hg T).waveFrontSet ↔ (x, ξ) ∈ T.waveFrontSet := by
  simp only [mem_waveFrontSet_iff, isMicrolocallySmoothAt_smulLeftCLM_iff hg hgx]

/-- Multiplying by a smooth function that vanishes nowhere on `Ω` does not change the wave front
set. -/
theorem waveFrontSet_smulLeftCLM_of_ne_zero (hg : ContDiff ℝ ∞ g) (hg0 : ∀ x ∈ Ω, g x ≠ 0)
    (T : 𝓓'(Ω, ℂ)) : (smulLeftCLM hg T).waveFrontSet = T.waveFrontSet := by
  ext ⟨x, ξ⟩
  by_cases hx : x ∈ Ω
  · exact mem_waveFrontSet_smulLeftCLM_iff hg (hg0 x hx)
  · simp [hx]

end SmoothMultiplication

end Distribution
