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

On a finite-dimensional real or complex inner product space `H`, the spectral flow of a continuous
path `A` of self-adjoint operators on `[a, b]` (`TauCeti.spectralFlow`) is the number of negative
eigenvalues of `A a` minus that of `A b`, counted with multiplicity
(`TauCeti.spectralFlow_eq_finrank_sub_finrank`):

`SF(A; a, b) = n⁻(A a) - n⁻(A b)`,

where `n⁻(T)` is the dimension of the sum of the eigenspaces of `T` at negative eigenvalues,
`Module.End.pointSpectralSubspace T (Iio 0)`. So in finite dimensions the spectral flow depends
only on the endpoints, and it is the net number of eigenvalues that pass from negative to
nonnegative.

In finite dimensions the spectral projection `cfc ((Icc 0 c).indicator 1) T` is the orthogonal
projection onto the sum of the eigenspaces of `T` at eigenvalues in `[0, c]`
(`ContinuousLinearMap.cfc_indicator_eq_starProjection`), so the local count
`TauCeti.spectralCount c T` is the number of eigenvalues of `T` in `[0, c]`
(`TauCeti.spectralCount_eq_finrank_pointSpectralSubspace`). Once `c > ‖T‖`, every eigenvalue
lies in `(-c, c)`, so the eigenvalues in `[0, c]` are exactly the nonnegative ones and
`spectralCount c T + n⁻(T) = dim H`
(`TauCeti.spectralCount_add_finrank_pointSpectralSubspace`).
A continuous path is bounded on the compact interval `[a, b]`, so any `c` above that bound is a
single spectral cut along the whole interval, and Phillips' formula with this one cut gives the
spectral flow.

Over `ℝ`, this gives the **regular-crossing formula** of Robbin and Salamon for the spectral flow
(`TauCeti.spectralFlow_eq_finsum_sigPos_sub_sigNeg_crossingForm`). A *crossing* of `A` is a time
`t` at which `A t` is not invertible, and its *crossing form* is the quadratic form
`v ↦ ⟪A' t v, v⟫` on the kernel of `A t`. If the endpoints are invertible and every crossing in
`(a, b)` is regular, that is its crossing form is nondegenerate, then the spectral flow is the sum
over the crossings of the signatures of the crossing forms, so that positive crossings count
positively. This is the formula for the drop of the negative index along a path of symmetric
bilinear forms (`ContinuousLinearMap.sigNeg_sub_sigNeg_eq_finsum_sigPos_sub_sigNeg_crossingForm`)
applied to `⟪A t ·, ·⟫`, whose negative index is `n⁻(A t)`.

## Main results

* `TauCeti.spectralCount_eq_finrank_pointSpectralSubspace`: the local count is the number of
  eigenvalues in `[0, c]`.
* `TauCeti.spectralCount_add_finrank_pointSpectralSubspace`: for `c > ‖T‖`, the local count and
  the number of negative eigenvalues add up to the dimension.
* `TauCeti.spectralFlow_eq_finrank_sub_finrank`: the spectral flow of a path in finite dimensions
  is the drop of the number of negative eigenvalues.
* `TauCeti.spectralFlow_eq_finsum_sigPos_sub_sigNeg_crossingForm`: the regular-crossing formula.

## References

* J. Phillips, *Self-adjoint Fredholm operators and spectral flow*, Canad. Math. Bull. **39**
  (1996), 460--467.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33.
-/

public section

open Module Set

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [FiniteDimensional 𝕜 H] [CompleteSpace H] [NormedAlgebra ℝ (H →L[𝕜] H)]
  [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
  [IsometricContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]

namespace TauCeti

/-- In finite dimensions, the local count of a self-adjoint operator `T` for `c` is the number of
eigenvalues of `T` in `[0, c]`, counted with multiplicity: the dimension of the sum of the
eigenspaces of `T` at those eigenvalues. -/
theorem spectralCount_eq_finrank_pointSpectralSubspace (c : ℝ) {T : H →L[𝕜] H}
    (hT : IsSelfAdjoint T) :
    spectralCount c T =
      finrank 𝕜 (Module.End.pointSpectralSubspace (T : H →ₗ[𝕜] H) (Icc 0 c)) := by
  rw [spectralCount_def, ContinuousLinearMap.cfc_indicator_eq_starProjection _ hT,
    Submodule.range_starProjection]

/-- In finite dimensions, if `‖T‖ < c`, then the local count of a self-adjoint operator `T` for
`c` and the number of negative eigenvalues of `T` add up to the dimension: every eigenvalue lies in
`(-c, c)`, so the eigenvalues in `[0, c]` are exactly the nonnegative ones. -/
theorem spectralCount_add_finrank_pointSpectralSubspace {c : ℝ} {T : H →L[𝕜] H}
    (hT : IsSelfAdjoint T) (hc : ‖T‖ < c) :
    spectralCount c T +
        finrank 𝕜 (Module.End.pointSpectralSubspace (T : H →ₗ[𝕜] H) (Iio 0)) =
      finrank 𝕜 H := by
  have hs : (T : H →ₗ[𝕜] H).IsSymmetric := T.isSelfAdjoint_iff_isSymmetric.mp hT
  -- Every eigenvalue of `T` lies below `c`.
  have hle (i : Fin (finrank 𝕜 H)) : hs.eigenvalues rfl i < c := by
    have hmem :
        hs.eigenvalues rfl i ∈ Module.End.restrictedPointSpectrum (T : H →ₗ[𝕜] H) ⊤ :=
      Module.End.mem_restrictedPointSpectrum Submodule.mem_top
        ((hs.eigenvectorBasis rfl).orthonormal.ne_zero i) (hs.apply_eigenvectorBasis rfl i)
    exact (le_abs_self _).trans_lt
      ((ContinuousLinearMap.abs_le_norm_of_mem_restrictedPointSpectrum hmem).trans_lt hc)
  have hcompl :
      {i | hs.eigenvalues rfl i ∈ Icc 0 c} = {i | hs.eigenvalues rfl i ∈ Iio 0}ᶜ := by
    ext i
    simp [(hle i).le]
  rw [spectralCount_eq_finrank_pointSpectralSubspace c hT, hs.finrank_pointSpectralSubspace rfl,
    hs.finrank_pointSpectralSubspace rfl, hcompl, add_comm, ncard_add_ncard_compl,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **The spectral flow in finite dimensions.** For a continuous path `A` of self-adjoint operators
on `[a, b]` in a finite-dimensional space, the spectral flow from `a` to `b` is the number of
negative eigenvalues of `A a` minus that of `A b`, counted with multiplicity. -/
theorem spectralFlow_eq_finrank_sub_finrank {A : ℝ → H →L[𝕜] H} {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t)) :
    spectralFlow A a b =
      (finrank 𝕜 (Module.End.pointSpectralSubspace (A a : H →ₗ[𝕜] H) (Iio 0)) : ℤ) -
        finrank 𝕜 (Module.End.pointSpectralSubspace (A b : H →ₗ[𝕜] H) (Iio 0)) := by
  -- A bound `C` for the path on the compact interval gives one spectral cut `c = C + 1`.
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  have hlt {t : ℝ} (ht : t ∈ Icc a b) : ‖A t‖ < C + 1 := (hC t ht).trans_lt (lt_add_one C)
  have hnotMem {t r : ℝ} (ht : t ∈ Icc a b) (hr : C + 1 ≤ |r|) :
      r ∉ spectrum ℝ (A t) := by
    intro hr'
    rcases subsingleton_or_nontrivial H with _ | _
    · rw [spectrum.of_subsingleton] at hr'
      exact hr'
    · have := spectrum.norm_le_norm_of_mem hr'
      rw [Real.norm_eq_abs] at this
      linarith [hlt ht]
  have hcut : IsSpectralCutOn A (C + 1) (Icc a b) := by
    refine isSpectralCutOn_iff.2 ⟨(norm_nonneg _).trans_lt (hlt ⟨le_rfl, hab⟩),
      fun u hu ↦ ⟨hnotMem hu ?_, hnotMem hu ?_, inferInstance⟩⟩
    · rw [abs_neg, abs_of_pos ((norm_nonneg _).trans_lt (hlt hu))]
    · rw [abs_of_pos ((norm_nonneg _).trans_lt (hlt hu))]
  have ha := spectralCount_add_finrank_pointSpectralSubspace (hsa a ⟨le_rfl, hab⟩)
    (hlt ⟨le_rfl, hab⟩)
  have hb := spectralCount_add_finrank_pointSpectralSubspace (hsa b ⟨hab, le_rfl⟩)
    (hlt ⟨hab, le_rfl⟩)
  rw [spectralFlow_eq_of_isSpectralCutOn hab hA hsa hcut]
  omega

section Crossing

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The regular-crossing formula for the spectral flow.** Let `A` be a continuous path of
symmetric operators on `[a, b]` in a finite-dimensional real inner product space, invertible at
both endpoints. Suppose that at every crossing `t ∈ (a, b)`, where `A t` is not injective, `A` has
derivative `A' t` and the crossing form `v ↦ ⟪A' t v, v⟫` on the kernel of `A t` is
nondegenerate. Then the spectral flow of `A` from `a` to `b` is the sum over the (finitely many)
crossings of the signatures of the crossing forms. Times at which `A t` is injective contribute
zero to the sum. -/
theorem spectralFlow_eq_finsum_sigPos_sub_sigNeg_crossingForm {A A' : ℝ → E →L[ℝ] E} {a b : ℝ}
    (hab : a ≤ b) (hA : ContinuousOn A (Icc a b))
    (hsym : ∀ t ∈ Icc a b, (A t : E →ₗ[ℝ] E).IsSymmetric)
    (ha : LinearMap.ker (A a : E →ₗ[ℝ] E) = ⊥) (hb : LinearMap.ker (A b : E →ₗ[ℝ] E) = ⊥)
    (hderiv : ∀ t ∈ Ioo a b, LinearMap.ker (A t : E →ₗ[ℝ] E) ≠ ⊥ → HasDerivAt A (A' t) t)
    (hreg : ∀ t ∈ Ioo a b, LinearMap.ker (A t : E →ₗ[ℝ] E) ≠ ⊥ →
      (crossingForm ((innerSL ℝ).comp (A t)) ((innerSL ℝ).comp (A' t))).Nondegenerate) :
    spectralFlow A a b = ∑ᶠ t ∈ Ioo a b,
      ((sigPos (crossingForm ((innerSL ℝ).comp (A t)) ((innerSL ℝ).comp (A' t))) : ℤ) -
        sigNeg (crossingForm ((innerSL ℝ).comp (A t)) ((innerSL ℝ).comp (A' t)))) := by
  have hker {t : ℝ} (h : ¬((innerSL ℝ).comp (A t)).toBilinForm.Nondegenerate) :
      LinearMap.ker (A t : E →ₗ[ℝ] E) ≠ ⊥ :=
    fun hk ↦ h (nondegenerate_toBilinForm_innerSL_comp_iff.2 hk)
  rw [spectralFlow_eq_finrank_sub_finrank hab hA
      fun t ht ↦ isSelfAdjoint_iff_isSymmetric.2 (hsym t ht),
    ← (hsym a ⟨le_rfl, hab⟩).sigNeg_toBilinForm_innerSL_comp,
    ← (hsym b ⟨hab, le_rfl⟩).sigNeg_toBilinForm_innerSL_comp]
  have h := sigNeg_sub_sigNeg_eq_finsum_sigPos_sub_sigNeg_crossingForm
    (V' := fun t ↦ (innerSL ℝ).comp (A' t)) hab (continuousOn_const.clm_comp hA)
    (fun t ht ↦ (hsym t ht).isSymm_toBilinForm_innerSL_comp)
    (nondegenerate_toBilinForm_innerSL_comp_iff.2 ha)
    (nondegenerate_toBilinForm_innerSL_comp_iff.2 hb)
    (fun t ht h ↦ (hderiv t ht (hker h)).const_clm_comp _) fun t ht h ↦ hreg t ht (hker h)
  -- The formula is stated for the path `fun t ↦ ⟪A t ·, ·⟫`; matching the goal against its
  -- unreduced applications to `t` is slow, so reduce them first.
  beta_reduce at h
  exact h

end Crossing

end TauCeti
