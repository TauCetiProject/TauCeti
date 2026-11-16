/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Basic
public import TauCeti.Analysis.InnerProductSpace.Trace.Basic

/-!
# The Hilbert–Schmidt inner product on operators from a finite-dimensional source

For bounded linear operators `S, T : E →L[𝕜] F` from a finite-dimensional inner product space `E`
into an arbitrary inner product space `F`, the **Hilbert–Schmidt inner product** (or Frobenius
inner product) is

`⟪S, T⟫_HS = ∑ i, ⟪S (b i), T (b i)⟫_𝕜`,

where `(bᵢ)` is any orthonormal basis of `E`. Expanding `(bᵢ)` in the standard orthonormal basis and
applying Parseval's identity shows that this sum is independent of the choice of orthonormal basis,
with neither completeness nor finite-dimensionality needed on the target `F`.

Because `E →L[𝕜] F` already carries the operator norm in Mathlib, installing a global
`InnerProductSpace` instance on `E →L[𝕜] F` would create competing norms. Instead, following
`InnerProductSpace.tensorDualMetric` and `TauCeti.bilinFormTrace`, this file bundles the pairing as
a sesquilinear form `ContinuousLinearMap.hilbertSchmidtInner : (E →L[𝕜] F) →ₗ⋆[𝕜] (E →L[𝕜] F) →ₗ[𝕜]
𝕜` and relates its diagonal directly to `ContinuousLinearMap.hilbertSchmidtNorm`.

## Main definitions

* `ContinuousLinearMap.hilbertSchmidtInner`: the Hilbert–Schmidt sesquilinear form on `E →L[𝕜] F`
  for finite-dimensional `E`.

## Main results

* `ContinuousLinearMap.hilbertSchmidtInner_eq_sum`:
  `hilbertSchmidtInner S T = ∑ i, ⟪S (b i), T (b i)⟫` in every orthonormal basis `b` of `E`.
* `ContinuousLinearMap.hilbertSchmidtInner_conj_symm` and
  `ContinuousLinearMap.hilbertSchmidtInner_comm`: conjugate symmetry over `𝕜` and symmetry over `ℝ`.
* `ContinuousLinearMap.hilbertSchmidtInner_self_eq_hilbertSchmidtNorm_sq`:
  `hilbertSchmidtInner T T = (T.hilbertSchmidtNorm ^ 2 : 𝕜)`.
* `ContinuousLinearMap.hilbertSchmidtInner_self_eq_zero` and
  `ContinuousLinearMap.hilbertSchmidtNorm_eq_zero`: definiteness of the Hilbert–Schmidt pairing and
  norm on a finite-dimensional source.
* `ContinuousLinearMap.norm_hilbertSchmidtInner_le`: the Cauchy–Schwarz inequality
  `‖hilbertSchmidtInner S T‖ ≤ S.hilbertSchmidtNorm * T.hilbertSchmidtNorm`.
* `ContinuousLinearMap.hilbertSchmidtInner_rankOne_left` and
  `ContinuousLinearMap.hilbertSchmidtInner_rankOne_right`: pairing against rank-one operators
  evaluates `⟪y, T x⟫` and `⟪S x, y⟫`.
* `ContinuousLinearMap.hilbertSchmidtInner_eq_trace_adjoint_comp`: when `F` is also
  finite-dimensional, `hilbertSchmidtInner S T = tr (S† T)`.
* `ContinuousLinearMap.hilbertSchmidtInner_eq_bilinFormTrace` and
  `ContinuousLinearMap.hilbertSchmidtInner_eq_sum_inv_gram`: over `ℝ`, identification with the
  metric trace and the `gⁱʲ ⟪S bᵢ, T bⱼ⟫` formula in an arbitrary basis `b`.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, revised
  edition, Academic Press, 1980, Section VI.6.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (fiber inner products on bundle homomorphisms).
-/

public section

open scoped InnerProductSpace ComplexOrder

namespace ContinuousLinearMap

section RCLike

variable {𝕜 E E' F G ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-- The **Hilbert–Schmidt inner product** `⟪S, T⟫_HS = ∑ i, ⟪S (b i), T (b i)⟫_𝕜` on bounded
linear operators out of a finite-dimensional inner product space `E`, bundled as a sesquilinear
form so as not to conflict with the operator norm on `E →L[𝕜] F`. By `hilbertSchmidtInner_eq_sum`,
any orthonormal basis of `E` computes the same pairing; the target `F` need not be complete or
finite-dimensional. -/
noncomputable def hilbertSchmidtInner : (E →L[𝕜] F) →ₗ⋆[𝕜] (E →L[𝕜] F) →ₗ[𝕜] 𝕜 where
  toFun S :=
    { toFun T := ∑ i, ⟪S (stdOrthonormalBasis 𝕜 E i), T (stdOrthonormalBasis 𝕜 E i)⟫_𝕜
      map_add' T₁ T₂ := by simp [inner_add_right, Finset.sum_add_distrib]
      map_smul' c T := by simp [inner_smul_right, Finset.mul_sum] }
  map_add' S₁ S₂ := by ext T; simp [inner_add_left, Finset.sum_add_distrib]
  map_smul' c S := by ext T; simp [inner_smul_left, Finset.mul_sum]

/-- **Basis independence of the Hilbert–Schmidt inner product.** In any orthonormal basis `b` of
`E`, `hilbertSchmidtInner S T = ∑ i, ⟪S (b i), T (b i)⟫_𝕜`. -/
theorem hilbertSchmidtInner_eq_sum [Fintype ι] (S T : E →L[𝕜] F) (b : OrthonormalBasis ι 𝕜 E) :
    hilbertSchmidtInner S T = ∑ i, ⟪S (b i), T (b i)⟫_𝕜 := by
  let e := stdOrthonormalBasis 𝕜 E
  -- Expand each `b i` in `e` and sum over `i` first via Parseval (`b.sum_inner_mul_inner`).
  have hexp (i : ι) :
      ⟪S (b i), T (b i)⟫_𝕜 =
        ∑ j, ∑ k, (⟪e k, b i⟫_𝕜 * ⟪b i, e j⟫_𝕜) * ⟪S (e j), T (e k)⟫_𝕜 := by
    conv_lhs => rw [← e.sum_repr' (b i)]
    rw [map_sum, map_sum, sum_inner]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [map_smul, inner_smul_left, inner_smul_right, inner_conj_symm]
    ring
  calc hilbertSchmidtInner S T
      = ∑ j, ∑ k, ⟪e k, e j⟫_𝕜 * ⟪S (e j), T (e k)⟫_𝕜 := by
        simp only [hilbertSchmidtInner, LinearMap.coe_mk, AddHom.coe_mk,
          orthonormal_iff_ite.1 e.orthonormal, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
          Finset.mem_univ, ↓reduceIte, e]
    _ = ∑ j, ∑ k, (∑ i, ⟪e k, b i⟫_𝕜 * ⟪b i, e j⟫_𝕜) * ⟪S (e j), T (e k)⟫_𝕜 := by
        simp_rw [b.sum_inner_mul_inner]
    _ = ∑ i, ∑ j, ∑ k, (⟪e k, b i⟫_𝕜 * ⟪b i, e j⟫_𝕜) * ⟪S (e j), T (e k)⟫_𝕜 := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_congr rfl fun j _ ↦ Finset.sum_comm, Finset.sum_comm]
    _ = ∑ i, ⟪S (b i), T (b i)⟫_𝕜 := by simp_rw [← hexp]

/-- Conjugate symmetry of the Hilbert–Schmidt inner product. -/
theorem hilbertSchmidtInner_conj_symm (S T : E →L[𝕜] F) :
    starRingEnd 𝕜 (hilbertSchmidtInner T S) = hilbertSchmidtInner S T := by
  let e := stdOrthonormalBasis 𝕜 E
  rw [hilbertSchmidtInner_eq_sum T S e, hilbertSchmidtInner_eq_sum S T e, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ inner_conj_symm (S (e i)) (T (e i))

/-- The Hilbert–Schmidt inner product is a Hermitian sesquilinear form. -/
theorem isSymm_hilbertSchmidtInner :
    (hilbertSchmidtInner (𝕜 := 𝕜) (E := E) (F := F)).IsSymm :=
  ⟨fun S T ↦ hilbertSchmidtInner_conj_symm T S⟩

/-- On the diagonal, the Hilbert–Schmidt inner product is `∑ i, ((‖T (b i)‖ ^ 2 : ℝ) : 𝕜)`. -/
theorem hilbertSchmidtInner_self_eq_sum [Fintype ι] (T : E →L[𝕜] F)
    (b : OrthonormalBasis ι 𝕜 E) :
    hilbertSchmidtInner T T = ∑ i, ((‖T (b i)‖ ^ 2 : ℝ) : 𝕜) := by
  rw [hilbertSchmidtInner_eq_sum T T b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_pow]

/-- On a finite-dimensional source, the diagonal of `hilbertSchmidtInner` is the square of
`hilbertSchmidtNorm`. -/
theorem hilbertSchmidtInner_self_eq_hilbertSchmidtNorm_sq [CompleteSpace E] (T : E →L[𝕜] F) :
    hilbertSchmidtInner T T = ((T.hilbertSchmidtNorm ^ 2 : ℝ) : 𝕜) := by
  let e := stdOrthonormalBasis 𝕜 E
  rw [hilbertSchmidtInner_self_eq_sum T e, T.sq_hilbertSchmidtNorm e.toHilbertBasis,
    hilbertSchmidtEnergy_def, tsum_fintype]
  simp only [e.coe_toHilbertBasis, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ sq_nonneg _,
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _), RCLike.ofReal_sum]

/-- The real part of `hilbertSchmidtInner T T` is nonnegative. -/
theorem re_hilbertSchmidtInner_self_nonneg (T : E →L[𝕜] F) :
    0 ≤ RCLike.re (hilbertSchmidtInner T T) := by
  rw [hilbertSchmidtInner_self_eq_sum T (stdOrthonormalBasis 𝕜 E), ← RCLike.ofReal_sum,
    RCLike.ofReal_re]
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The imaginary part of `hilbertSchmidtInner T T` vanishes. -/
@[simp]
theorem im_hilbertSchmidtInner_self (T : E →L[𝕜] F) :
    RCLike.im (hilbertSchmidtInner T T) = 0 := by
  rw [hilbertSchmidtInner_self_eq_sum T (stdOrthonormalBasis 𝕜 E), ← RCLike.ofReal_sum,
    RCLike.ofReal_im]

/-- **Definiteness of the Hilbert–Schmidt inner product.** `hilbertSchmidtInner T T = 0` if and only
if `T = 0`. -/
@[simp]
theorem hilbertSchmidtInner_self_eq_zero {T : E →L[𝕜] F} :
    hilbertSchmidtInner T T = 0 ↔ T = 0 := by
  let e := stdOrthonormalBasis 𝕜 E
  rw [hilbertSchmidtInner_self_eq_sum T e, ← RCLike.ofReal_sum, RCLike.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _]
  refine ⟨fun h ↦ ?_, fun h i _ ↦ by simp [h]⟩
  ext x
  rw [← e.sum_repr' x, map_sum]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  have hTi : T (e i) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp (h i hi))
  simp [hTi]

/-- **Definiteness of the Hilbert–Schmidt norm** on a finite-dimensional source. -/
@[simp]
theorem hilbertSchmidtNorm_eq_zero [CompleteSpace E] {T : E →L[𝕜] F} :
    T.hilbertSchmidtNorm = 0 ↔ T = 0 := by
  rw [← sq_eq_zero_iff, ← RCLike.ofReal_eq_zero (K := 𝕜),
    ← hilbertSchmidtInner_self_eq_hilbertSchmidtNorm_sq T, hilbertSchmidtInner_self_eq_zero]

/-- The Hilbert–Schmidt inner product is Hermitian and positive semidefinite. -/
theorem isPosSemidef_hilbertSchmidtInner :
    (hilbertSchmidtInner (𝕜 := 𝕜) (E := E) (F := F)).IsPosSemidef where
  eq := isSymm_hilbertSchmidtInner.eq
  nonneg T := RCLike.nonneg_iff.2 ⟨re_hilbertSchmidtInner_self_nonneg T,
    im_hilbertSchmidtInner_self T⟩

/-- **Cauchy–Schwarz inequality for the Hilbert–Schmidt inner product.** -/
theorem norm_hilbertSchmidtInner_le [CompleteSpace E] (S T : E →L[𝕜] F) :
    ‖hilbertSchmidtInner S T‖ ≤ S.hilbertSchmidtNorm * T.hilbertSchmidtNorm := by
  let e := stdOrthonormalBasis 𝕜 E
  -- Identify `(S (e i))ᵢ` and `(T (e i))ᵢ` with vectors in `PiLp 2` and apply Cauchy–Schwarz there.
  let u : PiLp 2 (fun _ : Fin (Module.finrank 𝕜 E) ↦ F) := WithLp.toLp 2 fun i ↦ S (e i)
  let v : PiLp 2 (fun _ : Fin (Module.finrank 𝕜 E) ↦ F) := WithLp.toLp 2 fun i ↦ T (e i)
  have hinner : hilbertSchmidtInner S T = ⟪u, v⟫_𝕜 := by
    rw [hilbertSchmidtInner_eq_sum S T e, PiLp.inner_apply]
  have hu : ‖u‖ = S.hilbertSchmidtNorm := by
    rw [← sq_eq_sq₀ (norm_nonneg u) S.hilbertSchmidtNorm_nonneg, PiLp.norm_sq_eq_of_L2]
    have hS := congrArg RCLike.re (hilbertSchmidtInner_self_eq_hilbertSchmidtNorm_sq S)
    rw [hilbertSchmidtInner_self_eq_sum S e, ← RCLike.ofReal_sum, RCLike.ofReal_re,
      RCLike.ofReal_re] at hS
    exact hS
  have hv : ‖v‖ = T.hilbertSchmidtNorm := by
    rw [← sq_eq_sq₀ (norm_nonneg v) T.hilbertSchmidtNorm_nonneg, PiLp.norm_sq_eq_of_L2]
    have hT := congrArg RCLike.re (hilbertSchmidtInner_self_eq_hilbertSchmidtNorm_sq T)
    rw [hilbertSchmidtInner_self_eq_sum T e, ← RCLike.ofReal_sum, RCLike.ofReal_re,
      RCLike.ofReal_re] at hT
    exact hT
  rw [hinner, ← hu, ← hv]
  exact norm_inner_le_norm u v

/-- Precomposing both arguments with a linear isometric equivalence preserves the Hilbert–Schmidt
inner product. -/
@[simp]
theorem hilbertSchmidtInner_comp_linearIsometryEquiv (S T : E →L[𝕜] F) (U : E' ≃ₗᵢ[𝕜] E) :
    hilbertSchmidtInner (S ∘L U.toContinuousLinearMap) (T ∘L U.toContinuousLinearMap) =
      hilbertSchmidtInner S T := by
  let e' := stdOrthonormalBasis 𝕜 E'
  rw [hilbertSchmidtInner_eq_sum _ _ e', hilbertSchmidtInner_eq_sum S T (e'.map U)]
  rfl

/-- Postcomposing both arguments with a linear isometric map preserves the Hilbert–Schmidt inner
product. -/
@[simp]
theorem hilbertSchmidtInner_linearIsometry_comp (U : F →ₗᵢ[𝕜] G) (S T : E →L[𝕜] F) :
    hilbertSchmidtInner (U.toContinuousLinearMap ∘L S) (U.toContinuousLinearMap ∘L T) =
      hilbertSchmidtInner S T := by
  let e := stdOrthonormalBasis 𝕜 E
  simp [hilbertSchmidtInner_eq_sum _ _ e, U.inner_map_map]

/-- Left composition with the operator adjoint moves to the right in `hilbertSchmidtInner`. -/
theorem hilbertSchmidtInner_adjoint_comp [CompleteSpace F] [CompleteSpace G]
    (A : F →L[𝕜] G) (S : E →L[𝕜] G) (T : E →L[𝕜] F) :
    hilbertSchmidtInner (A.adjoint ∘L S) T = hilbertSchmidtInner S (A ∘L T) := by
  let e := stdOrthonormalBasis 𝕜 E
  simp only [hilbertSchmidtInner_eq_sum _ _ e, comp_apply, adjoint_inner_left]

/-- Pairing a rank-one operator `v ↦ ⟪x, v⟫ • y` on the left against `T` evaluates `⟪y, T x⟫_𝕜`. -/
@[simp]
theorem hilbertSchmidtInner_rankOne_left (y : F) (x : E) (T : E →L[𝕜] F) :
    hilbertSchmidtInner (InnerProductSpace.rankOne 𝕜 y x) T = ⟪y, T x⟫_𝕜 := by
  let e := stdOrthonormalBasis 𝕜 E
  rw [hilbertSchmidtInner_eq_sum _ _ e]
  calc ∑ i, ⟪InnerProductSpace.rankOne 𝕜 y x (e i), T (e i)⟫_𝕜
      = ∑ i, ⟪y, ⟪e i, x⟫_𝕜 • T (e i)⟫_𝕜 := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [InnerProductSpace.rankOne_apply, inner_smul_left, inner_smul_right, inner_conj_symm]
    _ = ⟪y, T (∑ i, ⟪e i, x⟫_𝕜 • e i)⟫_𝕜 := by
        rw [← inner_sum]
        simp_rw [← map_smul, ← map_sum]
    _ = ⟪y, T x⟫_𝕜 := by rw [e.sum_repr']

/-- Pairing `S` against a rank-one operator `v ↦ ⟪x, v⟫ • y` on the right evaluates `⟪S x, y⟫_𝕜`. -/
@[simp]
theorem hilbertSchmidtInner_rankOne_right (S : E →L[𝕜] F) (y : F) (x : E) :
    hilbertSchmidtInner S (InnerProductSpace.rankOne 𝕜 y x) = ⟪S x, y⟫_𝕜 := by
  rw [← hilbertSchmidtInner_conj_symm, hilbertSchmidtInner_rankOne_left, inner_conj_symm]

/-- When `F` is also finite-dimensional, the Hilbert–Schmidt inner product is the operator trace
`tr (S† T)`. -/
theorem hilbertSchmidtInner_eq_trace_adjoint_comp [FiniteDimensional 𝕜 F] (S T : E →L[𝕜] F) :
    hilbertSchmidtInner S T = LinearMap.trace 𝕜 E (S.toLinearMap.adjoint ∘ₗ T.toLinearMap) := by
  let e := stdOrthonormalBasis 𝕜 E
  rw [hilbertSchmidtInner_eq_sum S T e, LinearMap.trace_eq_sum_inner _ e]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  rfl

end RCLike

section Real

variable {E F ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Over `ℝ`, the Hilbert–Schmidt inner product is symmetric. -/
theorem hilbertSchmidtInner_comm (S T : E →L[ℝ] F) :
    hilbertSchmidtInner S T = hilbertSchmidtInner T S := by
  simpa using hilbertSchmidtInner_conj_symm T S

/-- Over `ℝ`, `hilbertSchmidtInner T T` equals `T.hilbertSchmidtNorm ^ 2` directly in `ℝ`. -/
theorem real_hilbertSchmidtInner_self_eq_hilbertSchmidtNorm_sq [CompleteSpace E]
    (T : E →L[ℝ] F) :
    hilbertSchmidtInner T T = T.hilbertSchmidtNorm ^ 2 :=
  hilbertSchmidtInner_self_eq_hilbertSchmidtNorm_sq T

/-- Over `ℝ`, `hilbertSchmidtInner T T` is nonnegative. -/
theorem hilbertSchmidtInner_self_nonneg (T : E →L[ℝ] F) :
    0 ≤ hilbertSchmidtInner T T :=
  re_hilbertSchmidtInner_self_nonneg T

/-- Over `ℝ`, the Hilbert–Schmidt inner product of `S` and `T` is the metric trace of the bilinear
form `(u, v) ↦ ⟪S u, T v⟫_ℝ` on `E`. -/
theorem hilbertSchmidtInner_eq_bilinFormTrace (S T : E →L[ℝ] F) :
    hilbertSchmidtInner S T =
      TauCeti.bilinFormTrace ((innerₗ F).compl₁₂ S.toLinearMap T.toLinearMap) := by
  let e := stdOrthonormalBasis ℝ E
  rw [hilbertSchmidtInner_eq_sum S T e, TauCeti.bilinFormTrace_eq_sum _ e]
  rfl

/-- In an arbitrary basis `b` of `E`, the real Hilbert–Schmidt inner product contracts the Gram
pairings `⟪S (b i), T (b j)⟫_ℝ` against the inverse Gram matrix `(Matrix.gram ℝ b)⁻¹`. -/
theorem hilbertSchmidtInner_eq_sum_inv_gram [Fintype ι] [DecidableEq ι]
    (S T : E →L[ℝ] F) (b : Module.Basis ι ℝ E) :
    hilbertSchmidtInner S T =
      ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j * ⟪S (b i), T (b j)⟫_ℝ := by
  rw [hilbertSchmidtInner_eq_bilinFormTrace, TauCeti.bilinFormTrace_eq_sum_inv_gram _ b]
  rfl

end Real

end ContinuousLinearMap

end
