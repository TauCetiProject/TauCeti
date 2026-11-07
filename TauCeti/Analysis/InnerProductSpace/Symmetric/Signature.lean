/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import TauCeti.Analysis.InnerProductSpace.Symmetric.Basic
public import TauCeti.Analysis.Matrix.HermitianSignature.Continuity
public import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# The signature of the quadratic form of a symmetric operator

Let `T` be a symmetric operator on a finite-dimensional real inner product space `E`, and `Q` the
quadratic form `x ↦ ⟪T x, x⟫`. In an orthonormal eigenbasis of `T`, the form `Q` is the weighted
sum of squares whose weights are the eigenvalues of `T`. By Sylvester's law of inertia, the
negative index `sigNeg Q` of `Q` is therefore the number of negative eigenvalues of `T`, counted
with multiplicity, which is the dimension of the point-spectral subspace of `T` for `(-∞, 0)`;
likewise the positive index `sigPos Q` is the dimension of the point-spectral subspace for
`(0, ∞)`.

This identifies the two descriptions of a Morse index used side by side in the theory of the
trajectory operator `d/ds + A(s)`: as the negative index of a symmetric bilinear form, the form in
which crossing forms and their signatures are stated, and as the number of negative eigenvalues of
a symmetric operator, the form in which the Fredholm index is computed.

The form `Q` is passed together with the identity `Q x = ⟪T x, x⟫`, so the results apply to any
presentation of it, such as a Hessian quadratic form or the diagonal of a continuous bilinear form.

## Main results

In the namespace `LinearMap.IsSymmetric`:

* `equivalent_weightedSumSquares_eigenvalues`: `Q` is equivalent to the weighted sum of squares
  with the eigenvalues of `T` as weights.
* `sigNeg_eq_ncard_eigenvalues_neg`, `sigPos_eq_ncard_eigenvalues_pos`: the negative and positive
  indices of `Q` count the negative and positive eigenvalues of `T`.
* `sigNeg_eq_finrank_pointSpectralSubspace`: the negative index of `Q` is the dimension of the
  negative point-spectral subspace of `T`.
* `sigPos_eq_finrank_pointSpectralSubspace`: the positive index of `Q` is the dimension of the
  positive point-spectral subspace of `T`.
* `isSymm_toBilinForm_innerSL_comp`, `sigNeg_toBilinForm_innerSL_comp`,
  `sigPos_toBilinForm_innerSL_comp`: the continuous bilinear form `⟪T ·, ·⟫` is symmetric, and its
  negative and positive indices count the negative and positive eigenvalues of `T`.

In the namespace `ContinuousLinearMap`:

* `nondegenerate_toBilinForm_innerSL_comp_iff`: the form `⟪T ·, ·⟫` of an operator `T` is
  nondegenerate exactly when `T` is injective.

In the namespace `TauCeti`, for families of symmetric operators:

* `eventually_ker_eq_bot_and_sigNeg_eq_of_tendsto`: along a family tending to an injective limit
  `L`, the operators are eventually injective, and the negative index of their forms is eventually
  the number of negative eigenvalues of `L`.
* `exists_le_forall_ker_eq_bot_and_sigNeg_eq_of_tendsto`: a family on `ℝ` with injective limits at
  `±∞` is injective outside a compact interval `[a, b]`, and the negative indices of its forms at
  `a` and `b` count the negative eigenvalues of the limits.
-/

public section

open Set Filter
open scoped InnerProductSpace Topology

namespace LinearMap.IsSymmetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {T : E →ₗ[ℝ] E} {Q : QuadraticForm ℝ E}

/-- The quadratic form `x ↦ ⟪T x, x⟫` of a symmetric operator `T` is equivalent to the weighted
sum of squares whose weights are the eigenvalues of `T`: an orthonormal eigenbasis diagonalizes
it. -/
theorem equivalent_weightedSumSquares_eigenvalues (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (hQ : ∀ x, Q x = ⟪T x, x⟫_ℝ) :
    QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares ℝ (hT.eigenvalues hn)) := by
  subst hn
  let b := hT.eigenvectorBasis rfl
  -- The polar form of `Q` is `⟪T x, y⟫`, because `T` is symmetric.
  have hassoc (x y : E) : QuadraticMap.associated Q x y = ⟪T x, y⟫_ℝ := by
    rw [QuadraticMap.associated_apply, hQ, hQ, hQ, map_add, inner_add_left, inner_add_right,
      inner_add_right, hT y x, real_inner_comm (T x) y]
    simp [invOf_eq_inv]
    ring
  have hb (i : Fin (Module.finrank ℝ E)) : T (b i) = hT.eigenvalues rfl i • b i :=
    hT.apply_eigenvectorBasis rfl i
  have horth : (QuadraticMap.associated Q).IsOrthoᵢ b := by
    rw [LinearMap.isOrthoᵢ_def]
    intro i j hij
    rw [hassoc, hb, real_inner_smul_left, orthonormal_iff_ite.mp b.orthonormal i j]
    simp [hij]
  have hweights : (fun i ↦ Q (b i)) = hT.eigenvalues rfl := by
    funext i
    rw [hQ, hb, real_inner_smul_left, real_inner_self_eq_norm_sq, b.orthonormal.1 i, one_pow,
      mul_one]
  rw [← hweights]
  exact ⟨QuadraticForm.isometryEquivWeightedSumSquares Q b.toBasis horth⟩

/-- The negative index of the quadratic form `x ↦ ⟪T x, x⟫` of a symmetric operator `T` is the
number of negative eigenvalues of `T`, counted with multiplicity. -/
theorem sigNeg_eq_ncard_eigenvalues_neg (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (hQ : ∀ x, Q x = ⟪T x, x⟫_ℝ) :
    sigNeg Q = {i | hT.eigenvalues hn i < 0}.ncard :=
  QuadraticForm.sigNeg_of_equiv_weightedSumSquares
    (hT.equivalent_weightedSumSquares_eigenvalues hn hQ)

/-- The positive index of the quadratic form `x ↦ ⟪T x, x⟫` of a symmetric operator `T` is the
number of positive eigenvalues of `T`, counted with multiplicity. -/
theorem sigPos_eq_ncard_eigenvalues_pos (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (hQ : ∀ x, Q x = ⟪T x, x⟫_ℝ) :
    sigPos Q = {i | 0 < hT.eigenvalues hn i}.ncard :=
  QuadraticForm.sigPos_of_equiv_weightedSumSquares
    (hT.equivalent_weightedSumSquares_eigenvalues hn hQ)

/-- **The negative index of the form of a symmetric operator.** The negative index of the
quadratic form `x ↦ ⟪T x, x⟫` of a symmetric operator `T` is the dimension of the sum of the
eigenspaces of `T` at negative eigenvalues. -/
theorem sigNeg_eq_finrank_pointSpectralSubspace (hT : T.IsSymmetric)
    (hQ : ∀ x, Q x = ⟪T x, x⟫_ℝ) :
    sigNeg Q = Module.finrank ℝ (Module.End.pointSpectralSubspace T (Iio 0)) := by
  rw [hT.finrank_pointSpectralSubspace rfl, hT.sigNeg_eq_ncard_eigenvalues_neg rfl hQ]
  rfl

/-- **The positive index of the form of a symmetric operator.** The positive index of the
quadratic form `x ↦ ⟪T x, x⟫` of a symmetric operator `T` is the dimension of the sum of the
eigenspaces of `T` at positive eigenvalues. -/
theorem sigPos_eq_finrank_pointSpectralSubspace (hT : T.IsSymmetric)
    (hQ : ∀ x, Q x = ⟪T x, x⟫_ℝ) :
    sigPos Q = Module.finrank ℝ (Module.End.pointSpectralSubspace T (Ioi 0)) := by
  rw [hT.finrank_pointSpectralSubspace rfl, hT.sigPos_eq_ncard_eigenvalues_pos rfl hQ]
  rfl

/-! ### The bilinear form of an operator -/

omit [FiniteDimensional ℝ E] in
/-- The continuous bilinear form `⟪T ·, ·⟫` of a symmetric operator `T` is symmetric. -/
theorem isSymm_toBilinForm_innerSL_comp {T : E →L[ℝ] E} (hT : (T : E →ₗ[ℝ] E).IsSymmetric) :
    ((innerSL ℝ).comp T).toBilinForm.IsSymm :=
  ContinuousLinearMap.isSymm_toBilinForm_iff.2 fun u v ↦ by
    simpa [real_inner_comm u] using hT u v

/-- The negative index of the continuous bilinear form `⟪T ·, ·⟫` of a symmetric operator `T` is
the dimension of the sum of the eigenspaces of `T` at negative eigenvalues. -/
theorem sigNeg_toBilinForm_innerSL_comp {T : E →L[ℝ] E} (hT : (T : E →ₗ[ℝ] E).IsSymmetric) :
    sigNeg ((innerSL ℝ).comp T).toBilinForm.toQuadraticMap =
      Module.finrank ℝ (Module.End.pointSpectralSubspace (T : E →ₗ[ℝ] E) (Iio 0)) :=
  hT.sigNeg_eq_finrank_pointSpectralSubspace fun x ↦ by simp

/-- The positive index of the continuous bilinear form `⟪T ·, ·⟫` of a symmetric operator `T` is
the dimension of the sum of the eigenspaces of `T` at positive eigenvalues. -/
theorem sigPos_toBilinForm_innerSL_comp {T : E →L[ℝ] E} (hT : (T : E →ₗ[ℝ] E).IsSymmetric) :
    sigPos ((innerSL ℝ).comp T).toBilinForm.toQuadraticMap =
      Module.finrank ℝ (Module.End.pointSpectralSubspace (T : E →ₗ[ℝ] E) (Ioi 0)) :=
  hT.sigPos_eq_finrank_pointSpectralSubspace fun x ↦ by simp

end LinearMap.IsSymmetric

/-- On a finite-dimensional real inner product space, the continuous bilinear form `⟪T ·, ·⟫` of an
operator `T` is nondegenerate exactly when `T` is injective. -/
theorem ContinuousLinearMap.nondegenerate_toBilinForm_innerSL_comp_iff {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {T : E →L[ℝ] E} :
    ((innerSL ℝ).comp T).toBilinForm.Nondegenerate ↔ LinearMap.ker (T : E →ₗ[ℝ] E) = ⊥ := by
  rw [nondegenerate_toBilinForm_iff_injective, LinearMap.ker_eq_bot, coe_coe,
    injective_iff_map_eq_zero, injective_iff_map_eq_zero]
  refine forall_congr' fun u ↦ imp_congr_left ?_
  rw [comp_apply, ← norm_eq_zero, innerSL_apply_norm, norm_eq_zero]

/-! ### Families of symmetric operators near an injective limit -/

namespace TauCeti

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Along a family of symmetric operators tending to an injective limit `L`, the operators are
eventually injective, and the negative index of their bilinear forms `⟪A s ·, ·⟫` is eventually
the number of negative eigenvalues of `L`. -/
theorem eventually_ker_eq_bot_and_sigNeg_eq_of_tendsto {ι : Type*} {A : ι → E →L[ℝ] E}
    {l : Filter ι} [l.NeBot] (hsym : ∀ s, (A s : E →ₗ[ℝ] E).IsSymmetric) {L : E →L[ℝ] E}
    (hLker : LinearMap.ker (L : E →ₗ[ℝ] E) = ⊥) (hlim : Tendsto A l (𝓝 L)) :
    ∀ᶠ s in l, LinearMap.ker (A s : E →ₗ[ℝ] E) = ⊥ ∧
      sigNeg ((innerSL ℝ).comp (A s)).toBilinForm.toQuadraticMap =
        Module.finrank ℝ (Module.End.pointSpectralSubspace (L : E →ₗ[ℝ] E) (Iio 0)) := by
  have hLsym : (L : E →ₗ[ℝ] E).IsSymmetric :=
    isClosed_setOf_isSymmetric.mem_of_tendsto hlim (.of_forall hsym)
  have hLnd := nondegenerate_toBilinForm_innerSL_comp_iff.2 hLker
  -- The negative index is locally constant on the space of symmetric operators at `L`.
  let S := {B : E →L[ℝ] E // (B : E →ₗ[ℝ] E).IsSymmetric}
  have hV : Continuous fun B : S ↦ (innerSL ℝ).comp (B : E →L[ℝ] E) :=
    continuous_const.clm_comp continuous_subtype_val
  have hconst := eventually_sigNeg_toBilinForm_eq_of_continuousAt (x := (⟨L, hLsym⟩ : S))
    (.of_forall fun B ↦ B.2.isSymm_toBilinForm_innerSL_comp) hV.continuousAt hLnd
  have hlimS : Tendsto (fun s ↦ (⟨A s, hsym s⟩ : S)) l (𝓝 ⟨L, hLsym⟩) :=
    tendsto_subtype_rng.2 hlim
  filter_upwards [hlimS hconst, hlimS (hV.continuousAt.eventually_toBilinForm_nondegenerate hLnd)]
    with s hs hnd
  exact ⟨nondegenerate_toBilinForm_innerSL_comp_iff.1 hnd,
    hs.trans hLsym.sigNeg_toBilinForm_innerSL_comp⟩

/-- A family of symmetric operators on `ℝ` with injective limits `A±` at `±∞` is injective outside
a compact interval `[a, b]`, and the negative indices of its bilinear forms `⟪A s ·, ·⟫` at `a` and
`b` are the numbers of negative eigenvalues of `A⁻` and `A⁺`. -/
theorem exists_le_forall_ker_eq_bot_and_sigNeg_eq_of_tendsto {A : ℝ → E →L[ℝ] E}
    (hsym : ∀ s, (A s : E →ₗ[ℝ] E).IsSymmetric) {Aminus Aplus : E →L[ℝ] E}
    (hminus : LinearMap.ker (Aminus : E →ₗ[ℝ] E) = ⊥)
    (hplus : LinearMap.ker (Aplus : E →ₗ[ℝ] E) = ⊥)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus)) :
    ∃ a b, a ≤ b ∧ (∀ s ∉ Ioo a b, LinearMap.ker (A s : E →ₗ[ℝ] E) = ⊥) ∧
      sigNeg ((innerSL ℝ).comp (A a)).toBilinForm.toQuadraticMap =
        Module.finrank ℝ (Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio 0)) ∧
      sigNeg ((innerSL ℝ).comp (A b)).toBilinForm.toQuadraticMap =
        Module.finrank ℝ (Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Iio 0)) := by
  obtain ⟨a, ha⟩ :=
    eventually_atBot.1 (eventually_ker_eq_bot_and_sigNeg_eq_of_tendsto hsym hminus hbot)
  obtain ⟨b, hb⟩ :=
    eventually_atTop.1 (eventually_ker_eq_bot_and_sigNeg_eq_of_tendsto hsym hplus htop)
  refine ⟨min a b, max a b, min_le_max, fun s hs ↦ ?_, (ha _ (min_le_left a b)).2,
    (hb _ (le_max_right a b)).2⟩
  rcases not_and_or.1 hs with hs | hs
  · exact (ha s ((not_lt.1 hs).trans (min_le_left a b))).1
  · exact (hb s ((le_max_right a b).trans (not_lt.1 hs))).1

end TauCeti
