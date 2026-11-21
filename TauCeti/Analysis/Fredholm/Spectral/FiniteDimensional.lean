/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.Flow
public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus
public import TauCeti.Analysis.InnerProductSpace.FunctionalCalculusComparison
public import TauCeti.Analysis.InnerProductSpace.Symmetric.Signature
public import TauCeti.Analysis.Matrix.HermitianSignature.RegularCrossings
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap

/-!
# The spectral flow in finite dimensions

On a finite-dimensional real or complex inner product space `H`, every self-adjoint operator is
Fredholm, and the spectral flow `TauCeti.spectralFlow A a b` of a continuous path `A` of
self-adjoint operators over `[a, b]` can be computed from its endpoints alone: it is the number of
negative eigenvalues of `A a` minus that of `A b`, counted with multiplicity,

`SF(A; a, b) = n⁻(A a) - n⁻(A b)`

(`TauCeti.spectralFlow_eq_finrank_pointSpectralSubspace_sub_finrank`). Here `n⁻(T)` is the
dimension of the sum of the eigenspaces of `T` at negative eigenvalues. No invertibility of the
endpoints is needed, because Phillips' counts place the eigenvalue `0` with the nonnegative ones.
The proof uses a single global spectral cut: any `c` larger than the norms `‖A t‖` on `[a, b]` is a
spectral cut of `A` on all of `[a, b]` (`TauCeti.isSpectralCutOn_of_forall_norm_lt`), and the count
of eigenvalues of `A t` in `[0, c]` is then the number `dim H - n⁻(A t)` of its nonnegative
eigenvalues (`TauCeti.spectralCount_eq_finrank_pointSpectralSubspace`).

Two consequences are recorded.

* **Negation.** When the endpoints are invertible, the spectral flow of `-A` is minus that of `A`
  (`TauCeti.spectralFlow_neg`): the negative eigenvalues of `-T` are the positive eigenvalues of
  `T`, and `n⁺(T) + n⁻(T) = dim H` for invertible `T`.
* **The regular-crossing formula.** On a real space, if the endpoints are invertible and every
  crossing `t`, a time at which `A t` is not injective, is regular, that is, `A` has a derivative
  `A' t` there and the crossing form `v ↦ ⟪A' t v, v⟫` on the kernel of `A t` is nondegenerate,
  then the spectral flow is the sum over the crossings of the signatures of the crossing forms
  (`TauCeti.spectralFlow_eq_finsum_sigPos_sub_sigNeg_crossingForm`). Positive crossings count
  positively. This is Robbin and Salamon's formula, and it rests on the drop of the negative index
  along a path of symmetric bilinear forms with regular crossings
  (`ContinuousLinearMap.sigNeg_sub_sigNeg_eq_finsum_sigPos_sub_sigNeg_crossingForm`).

These are the finite-dimensional forms of the statements that the spectral flow of `A` is the
index of the trajectory operator `d/ds + A` and minus that of `d/ds - A`; see
`TauCeti.WeakDerivStep.eventually_index_trajectoryOperator_eq_spectralFlow`.

## Main results

* `TauCeti.isSpectralCutOn_iff_of_finiteDimensional`: in finite dimensions a spectral cut is a
  positive `c` with `±c` outside the spectra.
* `TauCeti.isSpectralCutOn_of_forall_norm_lt`: a bound on the norms gives a spectral cut.
* `TauCeti.spectralCount_eq_finrank_pointSpectralSubspace_Icc`: the local count is the number of
  eigenvalues in `[0, c]`.
* `TauCeti.spectralCount_eq_finrank_pointSpectralSubspace`: above the norm, the local count is the
  number of nonnegative eigenvalues.
* `TauCeti.spectralFlow_eq_finrank_pointSpectralSubspace_sub_finrank`: the spectral flow is
  `n⁻(A a) - n⁻(A b)`.
* `TauCeti.spectralFlow_neg`: negating a path with invertible endpoints negates its spectral flow.
* `TauCeti.spectralFlow_eq_finsum_sigPos_sub_sigNeg_crossingForm`: the regular-crossing formula.

## References

* J. Phillips, *Self-adjoint Fredholm operators and spectral flow*, Canad. Math. Bull. **39**
  (1996), 460--467.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, Section 4 (the spectral flow as a sum of crossing signatures).
-/

public section

open Set

namespace TauCeti

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [FiniteDimensional 𝕜 H] [CompleteSpace H] [NormedAlgebra ℝ (H →L[𝕜] H)]
  [IsometricContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]
  {A : ℝ → H →L[𝕜] H} {c : ℝ} {s : Set ℝ}

/-! ### Spectral cuts and counts in finite dimensions -/

/-- In finite dimensions, `c` is a spectral cut of `A` on `s` exactly when `c > 0` and neither
`-c` nor `c` is in the spectrum of any `A u` with `u ∈ s`: every spectral projection has finite
rank. -/
theorem isSpectralCutOn_iff_of_finiteDimensional : IsSpectralCutOn A c s ↔
    0 < c ∧ ∀ u ∈ s, -c ∉ spectrum ℝ (A u) ∧ c ∉ spectrum ℝ (A u) := by
  rw [isSpectralCutOn_iff]
  exact and_congr_right fun _ ↦ forall₂_congr fun _ _ ↦
    and_congr_right fun _ ↦ and_iff_left inferInstance

/-- In finite dimensions, a positive `c` larger than the norms of all `A u`, `u ∈ s`, is a
spectral cut of `A` on `s`, since the spectrum of an operator lies in the closed ball of radius
its norm. -/
theorem isSpectralCutOn_of_forall_norm_lt (hc : 0 < c) (h : ∀ u ∈ s, ‖A u‖ < c) :
    IsSpectralCutOn A c s := by
  refine isSpectralCutOn_iff_of_finiteDimensional.2 ⟨hc, fun u hu ↦ ?_⟩
  have hspec {r : ℝ} (hr : r ∈ spectrum ℝ (A u)) : |r| < c := by
    have h₁ := spectrum.norm_le_norm_of_mem hr
    rw [Real.norm_eq_abs] at h₁
    nlinarith [norm_nonneg (A u), h u hu]
  exact ⟨fun hr ↦ by simpa [abs_of_pos hc] using hspec hr,
    fun hr ↦ by simpa [abs_of_pos hc] using hspec hr⟩

variable [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]

/-- In finite dimensions, the count `TauCeti.spectralCount c T` of the eigenvalues of a
self-adjoint `T` in `[0, c]` is the dimension of the sum of the eigenspaces of `T` at the
eigenvalues in `[0, c]`. -/
theorem spectralCount_eq_finrank_pointSpectralSubspace_Icc (c : ℝ) {T : H →L[𝕜] H}
    (hT : IsSelfAdjoint T) :
    spectralCount c T =
      Module.finrank 𝕜 (Module.End.pointSpectralSubspace (T : H →ₗ[𝕜] H) (Icc 0 c)) := by
  rw [spectralCount_def, ContinuousLinearMap.cfc_indicator_eq_starProjection _ hT,
    Submodule.range_starProjection]

/-- In finite dimensions, for `c > ‖T‖` the count `TauCeti.spectralCount c T` of the eigenvalues
of a self-adjoint `T` in `[0, c]` is the number of nonnegative eigenvalues of `T`, counted with
multiplicity. -/
theorem spectralCount_eq_finrank_pointSpectralSubspace {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (hc : ‖T‖ < c) :
    spectralCount c T =
      Module.finrank 𝕜 (Module.End.pointSpectralSubspace (T : H →ₗ[𝕜] H) (Ici 0)) := by
  -- Every eigenvalue of `T` is at most `‖T‖ < c` in absolute value, so selecting those in
  -- `[0, c]` or in `[0, ∞)` gives the same subspace.
  have hΩ : Icc 0 c ∩ Metric.closedBall 0 ‖T‖ = Ici 0 ∩ Metric.closedBall 0 ‖T‖ := by
    ext x
    simp only [mem_inter_iff, mem_Icc, mem_Ici, mem_closedBall_zero_iff, Real.norm_eq_abs]
    exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, (le_abs_self x).trans (h.2.trans hc.le)⟩, h.2⟩⟩
  rw [spectralCount_eq_finrank_pointSpectralSubspace_Icc c hT,
    ← T.pointSpectralSubspace_inter_closedBall_norm, hΩ,
    T.pointSpectralSubspace_inter_closedBall_norm]

/-! ### The spectral flow from the endpoints -/

/-- **The spectral flow in finite dimensions.** For a continuous path `A` of self-adjoint
operators on a finite-dimensional space over `[a, b]`, the spectral flow is the number of negative
eigenvalues of `A a` minus the number of negative eigenvalues of `A b`, counted with multiplicity.
The endpoints need not be invertible. -/
theorem spectralFlow_eq_finrank_pointSpectralSubspace_sub_finrank {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t)) :
    spectralFlow A a b =
      (Module.finrank 𝕜 (Module.End.pointSpectralSubspace (A a : H →ₗ[𝕜] H) (Iio 0)) : ℤ) -
        Module.finrank 𝕜 (Module.End.pointSpectralSubspace (A b : H →ₗ[𝕜] H) (Iio 0)) := by
  -- A bound on `‖A t‖` over `[a, b]` gives one spectral cut for the whole interval.
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC a ha)
  have hlt (t : ℝ) (ht : t ∈ Icc a b) : ‖A t‖ < C + 1 := by linarith [hC t ht]
  rw [spectralFlow_eq_of_isSpectralCutOn hab hA hsa
      (isSpectralCutOn_of_forall_norm_lt (by linarith) hlt),
    spectralCount_eq_finrank_pointSpectralSubspace (hsa b hb) (hlt b hb),
    spectralCount_eq_finrank_pointSpectralSubspace (hsa a ha) (hlt a ha)]
  -- The nonnegative and the negative eigenvalues of `A t` together have the dimension of `H`.
  have hAa := (hsa a ha).isSymmetric
  have hAb := (hsa b hb).isSymmetric
  have h₁ := hAa.finrank_pointSpectralSubspace_add_finrank_pointSpectralSubspace_compl (Iio 0)
  have h₂ := hAb.finrank_pointSpectralSubspace_add_finrank_pointSpectralSubspace_compl (Iio 0)
  rw [compl_Iio] at h₁ h₂
  omega

/-- **Negation.** On a finite-dimensional space, negating a continuous path of self-adjoint
operators with invertible endpoints negates its spectral flow. -/
theorem spectralFlow_neg {a b : ℝ} (hab : a ≤ b) (hA : ContinuousOn A (Icc a b))
    (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t)) (ha : LinearMap.ker (A a : H →ₗ[𝕜] H) = ⊥)
    (hb : LinearMap.ker (A b : H →ₗ[𝕜] H) = ⊥) :
    spectralFlow (fun t ↦ -A t) a b = -spectralFlow A a b := by
  have ha' : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb' : b ∈ Icc a b := ⟨hab, le_rfl⟩
  rw [spectralFlow_eq_finrank_pointSpectralSubspace_sub_finrank (A := fun t ↦ -A t) hab hA.neg
      fun t ht ↦ (hsa t ht).neg,
    spectralFlow_eq_finrank_pointSpectralSubspace_sub_finrank hab hA hsa]
  -- The negative eigenvalues of `-T` are the positive ones of `T`, and for invertible `T` the
  -- positive and the negative eigenvalues together have the dimension of `H`.
  rw [ContinuousLinearMap.toLinearMap_neg, ContinuousLinearMap.toLinearMap_neg,
    Module.End.pointSpectralSubspace_neg, Module.End.pointSpectralSubspace_neg, neg_Iio, neg_zero]
  have hAa := (hsa a ha').isSymmetric
  have hAb := (hsa b hb').isSymmetric
  have h₁ :=
    hAa.finrank_pointSpectralSubspace_Iio_zero_add_finrank_pointSpectralSubspace_Ioi_zero ha
  have h₂ :=
    hAb.finrank_pointSpectralSubspace_Iio_zero_add_finrank_pointSpectralSubspace_Ioi_zero hb
  omega

end TauCeti

/-! ### The regular-crossing formula -/

namespace TauCeti

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A A' : ℝ → E →L[ℝ] E}

/-- **The regular-crossing formula for the spectral flow.** Let `A` be a continuous path of
self-adjoint operators on a finite-dimensional real inner product space over `[a, b]`, with
invertible endpoints. Suppose that every crossing `t ∈ (a, b)`, where `A t` is not injective, is
regular: `A` has derivative `A' t` at `t`, and the crossing form `Γₜ : v ↦ ⟪A' t v, v⟫` on the
kernel of `A t` is nondegenerate. Then the spectral flow of `A` is the sum over the crossings of
the signatures `sigPos Γₜ - sigNeg Γₜ`. Times at which `A t` is invertible contribute zero to the
sum. That the crossings are finite in number is a separate fact,
`ContinuousLinearMap.finite_setOf_not_nondegenerate_toBilinForm`. -/
theorem spectralFlow_eq_finsum_sigPos_sub_sigNeg_crossingForm {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t))
    (ha : LinearMap.ker (A a : E →ₗ[ℝ] E) = ⊥) (hb : LinearMap.ker (A b : E →ₗ[ℝ] E) = ⊥)
    (hderiv : ∀ t ∈ Ioo a b, LinearMap.ker (A t : E →ₗ[ℝ] E) ≠ ⊥ → HasDerivAt A (A' t) t)
    (hreg : ∀ t ∈ Ioo a b, LinearMap.ker (A t : E →ₗ[ℝ] E) ≠ ⊥ →
      (crossingForm ((innerSL ℝ).comp (A t)) ((innerSL ℝ).comp (A' t))).Nondegenerate) :
    spectralFlow A a b = ∑ᶠ t ∈ Ioo a b,
      ((sigPos (crossingForm ((innerSL ℝ).comp (A t)) ((innerSL ℝ).comp (A' t))) : ℤ) -
        sigNeg (crossingForm ((innerSL ℝ).comp (A t)) ((innerSL ℝ).comp (A' t)))) := by
  have ha' : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb' : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hflow := spectralFlow_eq_finrank_pointSpectralSubspace_sub_finrank hab hA hsa
  have hcross := sigNeg_sub_sigNeg_eq_finsum_sigPos_sub_sigNeg_crossingForm hab
    (continuousOn_const.clm_comp hA)
    (fun t ht ↦ (hsa t ht).isSymmetric.isSymm_toBilinForm_innerSL_comp)
    (nondegenerate_toBilinForm_innerSL_comp_iff.2 ha)
    (nondegenerate_toBilinForm_innerSL_comp_iff.2 hb)
    (fun t ht hnd ↦
      (hderiv t ht (mt nondegenerate_toBilinForm_innerSL_comp_iff.2 hnd)).const_clm_comp _)
    (fun t ht hnd ↦ hreg t ht (mt nondegenerate_toBilinForm_innerSL_comp_iff.2 hnd))
  rw [(hsa a ha').isSymmetric.sigNeg_toBilinForm_innerSL_comp,
    (hsa b hb').isSymmetric.sigNeg_toBilinForm_innerSL_comp] at hcross
  rw [hflow, hcross]

end TauCeti
