/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Prod
public import TauCeti.Analysis.Fredholm.Spectral.Flow
public import TauCeti.Analysis.InnerProductSpace.Spectral.BlockSum
import TauCeti.Topology.Algebra.Indicator

/-!
# The spectral flow of a direct sum

For paths `A₁` of operators on a Hilbert space `H₁` and `A₂` on `H₂`, the block-sum path
`t ↦ A₁ t ⊕ A₂ t` acts on the Hilbert direct sum `WithLp 2 (H₁ × H₂)`
(`ContinuousLinearMap.withLpProdMap`). This file proves that Phillips' spectral flow
(`TauCeti.spectralFlow`) is additive under this direct sum: for continuous paths of self-adjoint
Fredholm operators, the spectral flow of `t ↦ A₁ t ⊕ A₂ t` is the spectral flow of `A₁` plus that
of `A₂`.

The continuous functional calculus of a block sum acts block by block
(`ContinuousLinearMap.cfc_withLpProdMap`), so the spectral projections of `A₁ t ⊕ A₂ t` are the
block sums of those of `A₁ t` and `A₂ t`, and their ranks add
(`TauCeti.spectralCount_withLpProdMap`). Since the spectrum of a block sum is the union of the
spectra, a number `c` is a spectral cut of the direct sum exactly when it is a spectral cut of both
summands (`TauCeti.isSpectralCutOn_withLpProdMap_iff`). Hence the sum of spectral flow potentials of
`A₁` and `A₂` is a spectral flow potential of `A₁ ⊕ A₂`, which gives additivity
(`TauCeti.spectralFlow_withLpProdMap`).

## Main declarations

* `TauCeti.spectralCount_withLpProdMap`: eigenvalue counts add under direct sums.
* `TauCeti.isSpectralCutOn_withLpProdMap_iff`: spectral cuts of a direct sum.
* `TauCeti.spectralFlow_withLpProdMap`: the spectral flow is additive under direct sums.

## References

* J. Phillips, *Self-adjoint Fredholm operators and spectral flow*, Canad. Math. Bull. **39**
  (1996), 460--467.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33.
-/

public section

open Set

variable {𝕜 H₁ H₂ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]

namespace TauCeti

open ContinuousLinearMap

variable [CompleteSpace H₁] [CompleteSpace H₂]
  [NormedAlgebra ℝ (H₁ →L[𝕜] H₁)] [IsScalarTower ℝ 𝕜 (H₁ →L[𝕜] H₁)]
  [IsometricContinuousFunctionalCalculus ℝ (H₁ →L[𝕜] H₁) IsSelfAdjoint]
  [NormedAlgebra ℝ (H₂ →L[𝕜] H₂)] [IsScalarTower ℝ 𝕜 (H₂ →L[𝕜] H₂)]
  [IsometricContinuousFunctionalCalculus ℝ (H₂ →L[𝕜] H₂) IsSelfAdjoint]
  [NormedAlgebra ℝ (WithLp 2 (H₁ × H₂) →L[𝕜] WithLp 2 (H₁ × H₂))]
  [IsScalarTower ℝ 𝕜 (WithLp 2 (H₁ × H₂) →L[𝕜] WithLp 2 (H₁ × H₂))]
  [IsometricContinuousFunctionalCalculus ℝ (WithLp 2 (H₁ × H₂) →L[𝕜] WithLp 2 (H₁ × H₂))
    IsSelfAdjoint]

/-- **Eigenvalue counts add under direct sums.** If the indicator of `[0, c]` is continuous on the
spectra of the self-adjoint operators `T₁` and `T₂` and their spectral projections for `[0, c]` have
finite rank, then `T₁ ⊕ T₂` has as many eigenvalues in `[0, c]` as `T₁` and `T₂` together. -/
theorem spectralCount_withLpProdMap {c : ℝ} {T₁ : H₁ →L[𝕜] H₁} {T₂ : H₂ →L[𝕜] H₂}
    (h₁ : IsSelfAdjoint T₁) (h₂ : IsSelfAdjoint T₂)
    (hc : ContinuousOn ((Icc 0 c).indicator (1 : ℝ → ℝ)) (spectrum ℝ T₁ ∪ spectrum ℝ T₂))
    [FiniteDimensional 𝕜 (cfc ((Icc 0 c).indicator (1 : ℝ → ℝ)) T₁).range]
    [FiniteDimensional 𝕜 (cfc ((Icc 0 c).indicator (1 : ℝ → ℝ)) T₂).range] :
    spectralCount c (T₁.withLpProdMap 2 T₂) = spectralCount c T₁ + spectralCount c T₂ := by
  rw [spectralCount_def, spectralCount_def, spectralCount_def, cfc_withLpProdMap _ _ _ h₁ h₂ hc,
    finrank_range_withLpProdMap]

variable {A₁ : ℝ → H₁ →L[𝕜] H₁} {A₂ : ℝ → H₂ →L[𝕜] H₂} {c : ℝ} {s : Set ℝ}

/-- **Spectral cuts of a direct sum.** For two paths of self-adjoint operators, `c` is a spectral
cut of the direct sum `t ↦ A₁ t ⊕ A₂ t` exactly when it is a spectral cut of both: the spectrum of
the direct sum is the union of the spectra, and its spectral projection for `[-c, c]` is the direct
sum of theirs. -/
theorem isSpectralCutOn_withLpProdMap_iff (hsa₁ : ∀ u ∈ s, IsSelfAdjoint (A₁ u))
    (hsa₂ : ∀ u ∈ s, IsSelfAdjoint (A₂ u)) :
    IsSpectralCutOn (fun u ↦ (A₁ u).withLpProdMap 2 (A₂ u)) c s ↔
      IsSpectralCutOn A₁ c s ∧ IsSpectralCutOn A₂ c s := by
  -- Away from `±c`, the spectral projection of the direct sum is the direct sum of projections.
  have key (hc : 0 < c) (u : ℝ) (hu : u ∈ s)
      (hn : -c ∉ spectrum ℝ (A₁ u) ∧ -c ∉ spectrum ℝ (A₂ u))
      (hp : c ∉ spectrum ℝ (A₁ u) ∧ c ∉ spectrum ℝ (A₂ u)) :
      FiniteDimensional 𝕜
          (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) ((A₁ u).withLpProdMap 2 (A₂ u))).range ↔
        FiniteDimensional 𝕜 (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A₁ u)).range ∧
          FiniteDimensional 𝕜 (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A₂ u)).range := by
    have hcont : ContinuousOn ((Icc (-c) c).indicator (1 : ℝ → ℝ))
        (spectrum ℝ (A₁ u) ∪ spectrum ℝ (A₂ u)) := by
      refine continuousOn_const.continuousOn_indicator_of_disjoint_frontier ?_
      rw [frontier_Icc (by linarith), disjoint_left]
      rintro x (rfl | rfl) (hx | hx)
      exacts [hn.1 hx, hn.2 hx, hp.1 hx, hp.2 hx]
    rw [cfc_withLpProdMap (A₁ u) (A₂ u) _ (hsa₁ u hu) (hsa₂ u hu) hcont,
      finiteDimensional_range_withLpProdMap_iff]
  constructor
  · intro h
    have hn (u : ℝ) (hu : u ∈ s) : -c ∉ spectrum ℝ (A₁ u) ∧ -c ∉ spectrum ℝ (A₂ u) := by
      simpa [not_or] using h.neg_notMem_spectrum hu
    have hp (u : ℝ) (hu : u ∈ s) : c ∉ spectrum ℝ (A₁ u) ∧ c ∉ spectrum ℝ (A₂ u) := by
      simpa [not_or] using h.notMem_spectrum hu
    have hfd (u : ℝ) (hu : u ∈ s) :=
      (key h.pos u hu (hn u hu) (hp u hu)).1 (h.finiteDimensional_range_cfc_indicator_Icc hu)
    exact ⟨isSpectralCutOn_iff.2 ⟨h.pos, fun u hu ↦ ⟨(hn u hu).1, (hp u hu).1, (hfd u hu).1⟩⟩,
      isSpectralCutOn_iff.2 ⟨h.pos, fun u hu ↦ ⟨(hn u hu).2, (hp u hu).2, (hfd u hu).2⟩⟩⟩
  · rintro ⟨h₁, h₂⟩
    refine isSpectralCutOn_iff.2 ⟨h₁.pos, fun u hu ↦ ?_⟩
    have hn := And.intro (h₁.neg_notMem_spectrum hu) (h₂.neg_notMem_spectrum hu)
    have hp := And.intro (h₁.notMem_spectrum hu) (h₂.notMem_spectrum hu)
    simp only [spectrum_withLpProdMap, mem_union, not_or]
    exact ⟨hn, hp, (key h₁.pos u hu hn hp).2 ⟨h₁.finiteDimensional_range_cfc_indicator_Icc hu,
      h₂.finiteDimensional_range_cfc_indicator_Icc hu⟩⟩

/-- **The spectral flow is additive under direct sums.** For continuous paths `A₁` and `A₂` of
self-adjoint Fredholm operators on `[a, b]`, the spectral flow of the block-diagonal path
`t ↦ A₁ t ⊕ A₂ t` on the Hilbert direct sum is the spectral flow of `A₁` plus that of `A₂`. -/
theorem spectralFlow_withLpProdMap {a b : ℝ} (hab : a ≤ b) (hA₁ : ContinuousOn A₁ (Icc a b))
    (hA₂ : ContinuousOn A₂ (Icc a b)) (hsa₁ : ∀ t ∈ Icc a b, IsSelfAdjoint (A₁ t))
    (hsa₂ : ∀ t ∈ Icc a b, IsSelfAdjoint (A₂ t)) (hF₁ : ∀ t ∈ Icc a b, (A₁ t).IsFredholm)
    (hF₂ : ∀ t ∈ Icc a b, (A₂ t).IsFredholm) :
    spectralFlow (fun t ↦ (A₁ t).withLpProdMap 2 (A₂ t)) a b =
      spectralFlow A₁ a b + spectralFlow A₂ a b := by
  obtain ⟨F₁, hF₁p⟩ := exists_isSpectralFlowPotential hA₁ hsa₁ hF₁
  obtain ⟨F₂, hF₂p⟩ := exists_isSpectralFlowPotential hA₂ hsa₂ hF₂
  have hsa : ∀ t ∈ Icc a b, IsSelfAdjoint ((A₁ t).withLpProdMap 2 (A₂ t)) := fun t ht ↦
    (isSelfAdjoint_withLpProdMap_iff _ _).2 ⟨hsa₁ t ht, hsa₂ t ht⟩
  have hF : ∀ t ∈ Icc a b, ((A₁ t).withLpProdMap 2 (A₂ t)).IsFredholm := fun t ht ↦
    isFredholm_withLpProdMap_iff.2 ⟨hF₁ t ht, hF₂ t ht⟩
  -- The sum of potentials of `A₁` and `A₂` is a potential of their direct sum.
  have hFp : IsSpectralFlowPotential (fun t ↦ (A₁ t).withLpProdMap 2 (A₂ t)) a b (F₁ + F₂) := by
    refine isSpectralFlowPotential_iff.2 fun x y d hax hxy hyb hd ↦ ?_
    have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hax hyb
    obtain ⟨hd₁, hd₂⟩ := (isSpectralCutOn_withLpProdMap_iff (fun u hu ↦ hsa₁ u (hsub hu))
      fun u hu ↦ hsa₂ u (hsub hu)).1 hd
    have hcount (u : ℝ) (hu : u ∈ Icc x y) :
        spectralCount d ((A₁ u).withLpProdMap 2 (A₂ u)) =
          spectralCount d (A₁ u) + spectralCount d (A₂ u) := by
      have := hd₁.finiteDimensional_range_cfc_indicator_Icc_zero hu (hsa₁ u (hsub hu))
      have := hd₂.finiteDimensional_range_cfc_indicator_Icc_zero hu (hsa₂ u (hsub hu))
      refine spectralCount_withLpProdMap (hsa₁ u (hsub hu)) (hsa₂ u (hsub hu)) ?_
      rw [← spectrum_withLpProdMap (p := 2)]
      exact hd.continuousOn_indicator_Icc_zero hu (hsa u (hsub hu))
    rw [Pi.add_apply, Pi.add_apply, hcount x ⟨le_rfl, hxy⟩, hcount y ⟨hxy, le_rfl⟩]
    push_cast
    linarith [hF₁p.sub_eq hax hxy hyb hd₁, hF₂p.sub_eq hax hxy hyb hd₂]
  rw [spectralFlow_eq_sub hab (hA₁.withLpProdMap hA₂) hsa hF hFp,
    spectralFlow_eq_sub hab hA₁ hsa₁ hF₁ hF₁p, spectralFlow_eq_sub hab hA₂ hsa₂ hF₂ hF₂p,
    Pi.add_apply, Pi.add_apply]
  ring

end TauCeti
