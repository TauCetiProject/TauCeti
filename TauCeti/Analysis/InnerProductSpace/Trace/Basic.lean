/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.CanonicalTensor
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.Analysis.InnerProductSpace.Nondegenerate
import TauCeti.LinearAlgebra.BilinearForm.Dual.Basis

/-!
# Metric trace of a bilinear map

This file defines the metric trace of a bilinear map `W × W → N`, with values in any real vector
space `N`, on a finite-dimensional real inner product space `W`. For `N = ℝ` this is the metric
trace of a bilinear form; for a vector-valued form, such as the second covariant derivative of a
section, it is again vector-valued. The definition contracts the form against Mathlib's canonical
covariant tensor, making it independent of any choice of basis.

## Main definitions

* `LinearMap.BilinMap.metricTrace`: the metric trace of a real bilinear map.
* `LinearMap.metricTraceCompl₂`: for a bilinear map `C : W → P → N`, the contraction
  `L ↦ tr ((u, w) ↦ C u (L w))` of `C` against a linear map `L : W → P` in its second slot, as a
  linear map in `L`.

## Main statements

* `InnerProductSpace.canonicalCovariantTensor_eq_sum_dualBasis`: in an arbitrary basis `b`, the
  canonical covariant tensor is `∑ᵢ bᵢ ⊗ b'ᵢ`, where `b'` is the dual basis of `b` for the inner
  product.
* `LinearMap.BilinMap.metricTrace_eq_sum`: in an orthonormal basis, the metric trace is the sum of
  the diagonal values.
* `LinearMap.BilinMap.metricTrace_eq_sum_dualBasis`: in an arbitrary basis, the metric trace pairs
  the basis with its metric dual basis.
* `LinearMap.BilinMap.metricTrace_eq_sum_inv_gram`: in an arbitrary basis, the metric trace
  contracts the form against the inverse Gram matrix of the basis.
* `LinearMap.BilinMap.metricTrace_eq_trace_inv_gram_mul_toMatrix`: in an arbitrary basis, the
  metric trace of a bilinear form is the matrix trace of the inverse Gram matrix times the matrix
  of the form.
* `LinearMap.BilinMap.metricTrace_flip`: the metric trace is invariant under transposing the
  arguments.
* `LinearMap.BilinMap.metricTrace_compr₂`: the metric trace commutes with a linear map applied to
  the values.
* `LinearMap.BilinMap.metricTrace_compl₁₂_linearIsometryEquiv`: the metric trace is invariant
  under pulling the form back along a linear isometric equivalence.
* `LinearMap.BilinMap.metricTrace_innerₗ_smulRight`: the metric trace of the rank-one map
  `(v, w) ↦ ⟪u, v⟫ • A w` is `A u`, and `LinearMap.BilinMap.metricTrace_compl₂_innerₗ_smulRight`
  that of `(v, w) ↦ C v (⟪u, w⟫ • p)` is `C u p`.
* `LinearMap.BilinMap.metricTrace_inner`: the metric trace of the inner product is the real
  dimension.
* `LinearMap.metricTraceCompl₂_comp`: if `L` and `K` intertwine `C` and `C'`,
  `C' u (L p) = K (C u p)`, then contracting `C'` against `L ∘ A` is `K` applied to the
  contraction of `C` against `A`.
-/

public section

open LinearMap (BilinMap)
open scoped InnerProductSpace TensorProduct

/-- **The canonical covariant tensor in an arbitrary basis**: `∑ᵢ bᵢ ⊗ b'ᵢ`, where `b'` is the
dual basis of `b` for the inner product. The basis need not be orthonormal; for an orthonormal
basis `b' = b` and this is `InnerProductSpace.canonicalCovariantTensor_eq_sum`. -/
theorem InnerProductSpace.canonicalCovariantTensor_eq_sum_dualBasis (W : Type*)
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ W) :
    canonicalCovariantTensor W =
      ∑ i, b i ⊗ₜ[ℝ] LinearMap.BilinForm.dualBasis (innerₗ W) TauCeti.nondegenerate_inner b i := by
  let v := stdOrthonormalBasis ℝ W
  -- The dual basis of an orthonormal basis is the basis itself.
  have hv (k) : LinearMap.BilinForm.dualBasis (innerₗ W) TauCeti.nondegenerate_inner v.toBasis k =
      v k :=
    ext_inner_right ℝ fun w ↦ by
      rw [v.toBasis.inner_dualBasis_left, v.coe_toBasis_repr_apply, v.repr_apply_apply]
  rw [canonicalCovariantTensor_eq_sum W v]
  simpa [hv] using (TensorProduct.mk ℝ W W).sum_apply_dualBasis_eq TauCeti.nondegenerate_inner
    v.toBasis b

namespace LinearMap.BilinMap

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Type*} [AddCommMonoid N] [Module ℝ N]

/-- The metric trace of an `N`-valued bilinear map on `W`, obtained by contracting it against the
canonical covariant tensor of the inner product. -/
noncomputable def metricTrace : BilinMap ℝ W N →ₗ[ℝ] N :=
  (LinearMap.applyₗ (InnerProductSpace.canonicalCovariantTensor W)).comp
    (TensorProduct.uncurry (.id ℝ) W W N)

/-- The metric trace is evaluation on the canonical covariant tensor. -/
theorem metricTrace_apply (B : BilinMap ℝ W N) :
    metricTrace B = TensorProduct.lift B (InnerProductSpace.canonicalCovariantTensor W) := by
  rw [metricTrace, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply, TensorProduct.uncurry]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]

/-- In an orthonormal basis, the metric trace is the sum of the diagonal values. -/
theorem metricTrace_eq_sum {ι : Type*} [Fintype ι] (B : BilinMap ℝ W N)
    (b : OrthonormalBasis ι ℝ W) : metricTrace B = ∑ i, B (b i) (b i) := by
  rw [metricTrace_apply, InnerProductSpace.canonicalCovariantTensor_eq_sum W b, map_sum]
  simp only [TensorProduct.lift.tmul]

/-- In an arbitrary basis `b`, the metric trace is `∑ᵢ B(bᵢ, b'ᵢ)`, where `b'` is the dual basis of
`b` for the inner product. The basis need not be orthogonal. -/
theorem metricTrace_eq_sum_dualBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : BilinMap ℝ W N) (b : Module.Basis ι ℝ W) :
    metricTrace B =
      ∑ i, B (b i) (LinearMap.BilinForm.dualBasis (innerₗ W) TauCeti.nondegenerate_inner b i) := by
  simp only [metricTrace_apply, InnerProductSpace.canonicalCovariantTensor_eq_sum_dualBasis W b,
    map_sum, TensorProduct.lift.tmul]

/-- In an arbitrary basis `b`, the metric trace contracts the form against the inverse Gram
matrix of `b`: `tr_g B = ∑ i j, (G⁻¹)ᵢⱼ B(bᵢ, bⱼ)` with `Gᵢⱼ = ⟪bᵢ, bⱼ⟫`. This is the classical
index formula `gⁱʲ Bᵢⱼ`; the basis need not be orthogonal. -/
theorem metricTrace_eq_sum_inv_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : BilinMap ℝ W N) (b : Module.Basis ι ℝ W) :
    metricTrace B = ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j • B (b i) (b j) := by
  simp only [metricTrace_eq_sum_dualBasis B b, b.dualBasis_innerₗ_eq_sum, map_sum, map_smul]

/-- In an arbitrary basis `b`, the metric trace of a real bilinear form is the matrix trace
`tr (G⁻¹ [B]_b)` of the inverse Gram matrix `G⁻¹` of `b` times the matrix `[B]_b` of `B` in `b`.
The basis need not be orthogonal. -/
theorem metricTrace_eq_trace_inv_gram_mul_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm ℝ W) (b : Module.Basis ι ℝ W) :
    metricTrace B = ((Matrix.gram ℝ b)⁻¹ * LinearMap.BilinForm.toMatrix b B).trace := by
  have hsymm := (Matrix.isHermitian_gram ℝ b).isSymm.inv
  rw [metricTrace_eq_sum_inv_gram B b, Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, LinearMap.BilinForm.toMatrix_apply,
    smul_eq_mul, hsymm.apply]

/-- Transposing the arguments of a bilinear map preserves its metric trace. -/
@[simp]
theorem metricTrace_flip (B : BilinMap ℝ W N) : metricTrace B.flip = metricTrace B := by
  simp only [metricTrace_eq_sum _ (stdOrthonormalBasis ℝ W), LinearMap.flip_apply]

/-- The metric trace commutes with a linear map `f` applied to the values of the form. -/
@[simp]
theorem metricTrace_compr₂ {P : Type*} [AddCommMonoid P] [Module ℝ P] (B : BilinMap ℝ W N)
    (f : N →ₗ[ℝ] P) : metricTrace (B.compr₂ f) = f (metricTrace B) := by
  rw [metricTrace_apply, metricTrace_apply, TensorProduct.lift_compr₂, LinearMap.comp_apply]

/-- The metric trace is invariant under pulling the form back along a linear isometric
equivalence `e : W ≃ₗᵢ[ℝ] W'`. -/
@[simp]
theorem metricTrace_compl₁₂_linearIsometryEquiv {W' : Type*} [NormedAddCommGroup W']
    [InnerProductSpace ℝ W'] [FiniteDimensional ℝ W'] (B : BilinMap ℝ W' N) (e : W ≃ₗᵢ[ℝ] W') :
    metricTrace (B.compl₁₂ e.toLinearEquiv.toLinearMap e.toLinearEquiv.toLinearMap) =
      metricTrace B := by
  let b := stdOrthonormalBasis ℝ W
  rw [metricTrace_eq_sum _ b, metricTrace_eq_sum B (b.map e)]
  simp only [LinearMap.compl₁₂_apply, OrthonormalBasis.map_apply, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv]

/-- The metric trace of the rank-one bilinear map `(v, w) ↦ ⟪u, v⟫ • A w` is `A u`. For the
rank-one map in the other slot, combine with `metricTrace_flip`. -/
@[simp]
theorem metricTrace_innerₗ_smulRight (u : W) (A : W →ₗ[ℝ] N) :
    metricTrace ((innerₗ W u).smulRight A) = A u := by
  let b := stdOrthonormalBasis ℝ W
  conv_rhs => rw [← b.sum_repr' u]
  simp only [metricTrace_eq_sum _ b, LinearMap.smulRight_apply, innerₗ_apply_apply,
    LinearMap.smul_apply, map_sum, map_smul, real_inner_comm]

/-- The metric trace of the bilinear map `(v, w) ↦ C v (⟪u, w⟫ • p)` is `C u p`: contracting a
bilinear map `C` against the rank-one map `w ↦ ⟪u, w⟫ • p` evaluates `C` at `u`. -/
@[simp]
theorem metricTrace_compl₂_innerₗ_smulRight {P : Type*} [AddCommMonoid P] [Module ℝ P]
    (C : W →ₗ[ℝ] P →ₗ[ℝ] N) (u : W) (p : P) :
    metricTrace (C.compl₂ ((innerₗ W u).smulRight p)) = C u p := by
  have h : (C.compl₂ ((innerₗ W u).smulRight p)).flip = (innerₗ W u).smulRight (C.flip p) :=
    LinearMap.ext₂ fun w v ↦ by
      simp only [LinearMap.flip_apply, LinearMap.compl₂_apply, LinearMap.smulRight_apply,
        map_smul, LinearMap.smul_apply]
  rw [← metricTrace_flip, h, metricTrace_innerₗ_smulRight, LinearMap.flip_apply]

/-- The metric trace of the inner product is the real dimension. -/
@[simp]
theorem metricTrace_inner : metricTrace (innerₗ W) = Module.finrank ℝ W := by
  rw [metricTrace_eq_sum (innerₗ W) (stdOrthonormalBasis ℝ W)]
  simp

end LinearMap.BilinMap

namespace LinearMap

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {P N : Type*} [AddCommMonoid P] [Module ℝ P] [AddCommMonoid N] [Module ℝ N]

/-- The metric contraction `L ↦ tr ((u, w) ↦ C u (L w))` of a bilinear map `C : W → P → N` against
a linear map `L : W → P` inserted into its second slot, as a linear map in `L`: the metric trace
`LinearMap.BilinMap.metricTrace` of `C.compl₂ L` (`LinearMap.metricTraceCompl₂_apply`). For a
Clifford multiplication `C` and the covariant derivative `L = ∇σ` of a section, this is the Dirac
operator. -/
noncomputable def metricTraceCompl₂ (C : W →ₗ[ℝ] P →ₗ[ℝ] N) : (W →ₗ[ℝ] P) →ₗ[ℝ] N :=
  BilinMap.metricTrace ∘ₗ (llcomp ℝ W P N ∘ₗ C).flip

/-- The contraction of `C` against `L` is the metric trace of `C.compl₂ L`. -/
@[simp]
theorem metricTraceCompl₂_apply (C : W →ₗ[ℝ] P →ₗ[ℝ] N) (L : W →ₗ[ℝ] P) :
    C.metricTraceCompl₂ L = BilinMap.metricTrace (C.compl₂ L) := by
  have h : (llcomp ℝ W P N ∘ₗ C).flip L = C.compl₂ L :=
    ext₂ fun u w ↦ by simp only [flip_apply, comp_apply, llcomp_apply, compl₂_apply]
  rw [metricTraceCompl₂, comp_apply, h]

/-- **Contraction of intertwined bilinear maps.** If linear maps `L : P → P'` and `K : N → N'`
intertwine the bilinear maps `C` and `C'`, `C' u (L p) = K (C u p)`, then contracting `C'` against
`L ∘ A` is `K` applied to the contraction of `C` against `A`. For `K = L` this is naturality of the
contraction; for `K = -L` it is anti-naturality. -/
theorem metricTraceCompl₂_comp {P' N' : Type*} [AddCommMonoid P'] [Module ℝ P'] [AddCommMonoid N']
    [Module ℝ N'] (C : W →ₗ[ℝ] P →ₗ[ℝ] N) (C' : W →ₗ[ℝ] P' →ₗ[ℝ] N') (L : P →ₗ[ℝ] P')
    (K : N →ₗ[ℝ] N') (h : ∀ u p, C' u (L p) = K (C u p)) (A : W →ₗ[ℝ] P) :
    C'.metricTraceCompl₂ (L ∘ₗ A) = K (C.metricTraceCompl₂ A) := by
  rw [metricTraceCompl₂_apply, metricTraceCompl₂_apply, ← BilinMap.metricTrace_compr₂]
  congr 1
  exact ext₂ fun u w ↦ by simp only [compl₂_apply, compr₂_apply, comp_apply, h]

end LinearMap
