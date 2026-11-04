/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.Analysis.Matrix.Polar.Deformation
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Index

/-!
# Deforming loops of totally real subspaces to Lagrangian loops

A loop `Λ t = A t L₀` of maximal totally real subspaces of `ℂⁿ` (`TauCeti.TotallyRealLoop`) has
the Maslov index of a loop `t ↦ U t ℝⁿ` with every `U t` unitary
(`TauCeti.TotallyRealLoop.exists_unitary_maslovIndex_eq`). Each `U t ℝⁿ` is Lagrangian for the
standard symplectic form `Im ⟪·, ·⟫` of `ℂⁿ`. This is how the Maslov index of a totally real
boundary condition is compared with invariants defined only for Lagrangian loops, such as the
Robbin–Salamon index of their closed-loop specialization.

The two loops are joined by a homotopy through loops of maximal totally real subspaces with
continuous frames, built as follows. Write `Λ t = M t ℝⁿ` for a continuous path `M` of invertible
matrices; closedness of the loop says `M 1 = M 0 G` for a real invertible matrix `G`.

* **Orthonormalization.** Replacing `M` by `B = M Re (Mᴴ M) ^ (-1/2)` does not change the real
  spans `M t ℝⁿ`, because the correction is real and invertible, and it makes the columns of
  `B t` orthonormal for the real inner product `Re ⟪·, ·⟫`. Two such frames with the same real
  span differ by a real orthogonal matrix, so `B 1 = B 0 O` with `O` orthogonal, hence unitary.
* **Polar contraction.** Contracting the positive factor of the polar decomposition
  `B t = P t V t`, through `P t ^ (1 - s) V t`
  (`Matrix.GeneralLinearGroup.polarDeformation`), is equivariant under right multiplication by
  the unitary monodromy `O`. So every intermediate path still closes up as a loop of subspaces,
  and at `s = 1` it reaches the unitary path `V`. Homotopy invariance of the Maslov index
  (`TauCeti.TotallyRealLoop.maslovIndex_eq_of_homotopy`) then compares the two loops.

Without the orthonormalization the monodromy `G` need not be orthogonal, and the polar
contraction of `M` need not close up.

## Main declarations

* `TauCeti.realSubspace`: the real subspace `ℝⁿ ⊆ ℂⁿ`, which is maximal totally real
  (`TauCeti.isMaximalTotallyReal_realSubspace`).
* `TauCeti.TotallyRealLoop.exists_unitary_maslovIndex_eq`: every loop of maximal totally real
  subspaces of `ℂⁿ` has the Maslov index of a loop `t ↦ U t ℝⁿ` with `U` a continuous path of
  unitary matrices.
* `TauCeti.im_inner_eq_zero_of_mem_map_unitary`: the subspace `U ℝⁿ` is isotropic for
  `Im ⟪·, ·⟫` when `U` is unitary.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.3 (loops of totally real subspaces, their
  Maslov index, and the comparison with Lagrangian loops).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 2.3 (the Lagrangian Grassmannian `U(n) / O(n)` and its Maslov index).
-/

public section

noncomputable section

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator unitInterval

namespace TauCeti

variable {n : Type*}

variable (n) in
/-- The real subspace `ℝⁿ ⊆ ℂⁿ` of vectors with real coordinates. -/
def realSubspace : Submodule ℝ (EuclideanSpace ℂ n) where
  carrier := {v | ∀ i, (v i).im = 0}
  add_mem' {v w} hv hw i := by simp [hv i, hw i]
  zero_mem' i := by simp
  smul_mem' c v hv i := by simp [hv i]

/-- A vector lies in `ℝⁿ` exactly when all its coordinates are real. -/
@[simp]
theorem mem_realSubspace {v : EuclideanSpace ℂ n} : v ∈ realSubspace n ↔ ∀ i, (v i).im = 0 :=
  Iff.rfl

/-- The real subspace `ℝⁿ` is maximal totally real in `ℂⁿ`: every vector is uniquely the sum of
a real vector and `i` times a real vector. -/
theorem isMaximalTotallyReal_realSubspace :
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ (EuclideanSpace ℂ n) Complex.I).restrictScalars ℝ)
      (realSubspace n) := by
  rw [isMaximalTotallyReal_iff]
  constructor
  · rw [Submodule.disjoint_def]
    rintro v hv ⟨w, hw, rfl⟩
    ext i
    have h1 := hv i
    have h2 := hw i
    simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, PiLp.smul_apply,
      smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_add] at h1 ⊢
    apply Complex.ext <;> simp [h1, h2]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    let re : EuclideanSpace ℂ n := WithLp.toLp 2 fun i ↦ ((v i).re : ℂ)
    let im : EuclideanSpace ℂ n := WithLp.toLp 2 fun i ↦ ((v i).im : ℂ)
    refine Submodule.mem_sup.2 ⟨re, fun i ↦ by simp [re], _, ⟨im, fun i ↦ by simp [im], rfl⟩, ?_⟩
    ext i
    apply Complex.ext <;> simp [re, im]

variable [Fintype n] [DecidableEq n]

/-- The image `M ℝⁿ` of the real subspace under a complex matrix. -/
private abbrev realImage (M : Matrix n n ℂ) : Submodule ℝ (EuclideanSpace ℂ n) :=
  (realSubspace n).map
    (((toEuclideanCLM (𝕜 := ℂ) M : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
      EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).restrictScalars ℝ)

private theorem toEuclideanCLM_apply_apply (M : Matrix n n ℂ) (v : EuclideanSpace ℂ n) (i : n) :
    toEuclideanCLM (𝕜 := ℂ) M v i = ∑ j, M i j * v j := by
  simp [Matrix.mulVec, dotProduct]

/-- A real matrix maps `ℝⁿ` into itself. -/
private theorem realImage_map_ofReal_le (N : Matrix n n ℝ) :
    realImage (N.map ((↑) : ℝ → ℂ)) ≤ realSubspace n := by
  rintro _ ⟨v, hv, rfl⟩ i
  simp only [LinearMap.restrictScalars_apply, ContinuousLinearMap.coe_coe,
    toEuclideanCLM_apply_apply, map_apply, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  simp [(mem_realSubspace.1 hv)]

/-- The image of `ℝⁿ` under a product is the image under the left factor of its image under the
right factor. -/
private theorem realImage_mul (M N : Matrix n n ℂ) :
    realImage (M * N) = (realImage N).map
      (((toEuclideanCLM (𝕜 := ℂ) M : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
        EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).restrictScalars ℝ) := by
  rw [realImage, realImage, ← Submodule.map_comp]
  congr 1
  ext v
  simp [map_mul]

/-- An invertible real matrix maps `ℝⁿ` onto itself. -/
private theorem realImage_map_ofReal {N : Matrix n n ℝ} (hN : IsUnit N) :
    realImage (N.map ((↑) : ℝ → ℂ)) = realSubspace n := by
  refine le_antisymm (realImage_map_ofReal_le N) fun v hv ↦ ?_
  have hmul : N.map ((↑) : ℝ → ℂ) * N⁻¹.map ((↑) : ℝ → ℂ) = 1 := by
    have h := congrArg (fun A : Matrix n n ℝ ↦ A.map Complex.ofRealHom)
      (Matrix.mul_nonsing_inv N ((Matrix.isUnit_iff_isUnit_det _).1 hN))
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have h := congrArg (fun M : Matrix n n ℂ ↦ toEuclideanCLM (𝕜 := ℂ) M v) hmul
  simp only [map_mul, map_one, mul_apply_eq_comp, one_apply_eq_self] at h
  refine ⟨_, realImage_map_ofReal_le N⁻¹ ⟨v, hv, rfl⟩, ?_⟩
  simpa using h

/-- Multiplying on the right by an invertible real matrix does not change `M ℝⁿ`. -/
private theorem realImage_mul_map_ofReal (M : Matrix n n ℂ) {N : Matrix n n ℝ} (hN : IsUnit N) :
    realImage (M * N.map ((↑) : ℝ → ℂ)) = realImage M := by
  rw [realImage_mul, realImage_map_ofReal hN]

/-- Two invertible complex matrices with the same image of `ℝⁿ` differ by a real matrix on the
right. -/
private theorem exists_eq_mul_map_ofReal {M M' : GL n ℂ}
    (h : realImage (M : Matrix n n ℂ) = realImage (M' : Matrix n n ℂ)) :
    ∃ O : Matrix n n ℝ, (M' : Matrix n n ℂ) = M * O.map ((↑) : ℝ → ℂ) := by
  set X : Matrix n n ℂ := ((M⁻¹ : GL n ℂ) : Matrix n n ℂ) * M'
  have hX : ∀ i j, (X i j).im = 0 := by
    intro i j
    let e : EuclideanSpace ℂ n := EuclideanSpace.single j 1
    have he : e ∈ realSubspace n := fun k ↦ by
      by_cases hk : k = j <;> simp [e, PiLp.single_apply, hk]
    obtain ⟨w, hw, hwe⟩ :
        toEuclideanCLM (𝕜 := ℂ) (M' : Matrix n n ℂ) e ∈ realImage (M : Matrix n n ℂ) :=
      h ▸ ⟨e, he, rfl⟩
    have hXe : toEuclideanCLM (𝕜 := ℂ) X e = w := by
      have hw' : toEuclideanCLM (𝕜 := ℂ) (M : Matrix n n ℂ) w =
          toEuclideanCLM (𝕜 := ℂ) (M' : Matrix n n ℂ) e := hwe
      rw [map_mul, mul_apply_eq_comp, ← hw', ← mul_apply_eq_comp, ← map_mul, Units.inv_mul,
        map_one, one_apply_eq_self]
    have := congrArg (fun u : EuclideanSpace ℂ n ↦ u i) hXe
    simp only [toEuclideanCLM_apply_apply, e, PiLp.single_apply, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
    rw [this]
    exact hw i
  refine ⟨X.map Complex.re, ?_⟩
  have hX' : (X.map Complex.re).map ((↑) : ℝ → ℂ) = X := by
    ext i j
    apply Complex.ext <;> simp [hX i j]
  rw [hX', ← mul_assoc, Units.mul_inv, one_mul]

/-! ### Orthonormalizing a frame by a real change of basis -/

omit [DecidableEq n] in
private theorem map_re_map_ofReal_mul (N : Matrix n n ℝ) (K : Matrix n n ℂ) :
    (N.map ((↑) : ℝ → ℂ) * K).map Complex.re = N * K.map Complex.re := by
  ext i j
  simp [Matrix.mul_apply, Complex.re_sum]

omit [DecidableEq n] in
private theorem map_re_mul_map_ofReal (K : Matrix n n ℂ) (N : Matrix n n ℝ) :
    (K * N.map ((↑) : ℝ → ℂ)).map Complex.re = K.map Complex.re * N := by
  ext i j
  simp [Matrix.mul_apply, Complex.re_sum]

omit [Fintype n] [DecidableEq n] in
private theorem conjTranspose_map_ofReal (N : Matrix n n ℝ) :
    (N.map ((↑) : ℝ → ℂ))ᴴ = Nᵀ.map ((↑) : ℝ → ℂ) := by
  ext i j
  simp

/-- The real Gram matrix `Re (Mᴴ M)` of the columns of `M`, for the real inner product
`Re ⟪v, w⟫` of `ℂⁿ`. -/
private abbrev realGram (M : Matrix n n ℂ) : Matrix n n ℝ := (Mᴴ * M).map Complex.re

omit [DecidableEq n] in
private theorem realGram_mul_map_ofReal (M : Matrix n n ℂ) (N : Matrix n n ℝ) :
    realGram (M * N.map ((↑) : ℝ → ℂ)) = Nᵀ * realGram M * N := by
  have h : (M * N.map ((↑) : ℝ → ℂ))ᴴ * (M * N.map ((↑) : ℝ → ℂ)) =
      Nᵀ.map ((↑) : ℝ → ℂ) * (Mᴴ * M) * N.map ((↑) : ℝ → ℂ) := by
    rw [conjTranspose_mul, conjTranspose_map_ofReal]
    simp only [Matrix.mul_assoc]
  rw [realGram, h, map_re_mul_map_ofReal, map_re_map_ofReal_mul]

/-- The real Gram matrix of an invertible complex matrix is positive definite. -/
private theorem posDef_realGram (M : GL n ℂ) : (realGram (M : Matrix n n ℂ)).PosDef := by
  have hK : ((M : Matrix n n ℂ)ᴴ * M).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit M.isUnit)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx ↦ ?_
  · ext i j
    have := congrFun (congrFun hK.1 i) j
    simp only [conjTranspose_apply, RCLike.star_def] at this
    simp only [conjTranspose_apply, map_apply, star_trivial, ← this, Complex.conj_re]
  · set xc : n → ℂ := fun i ↦ (x i : ℂ)
    have hxc : xc ≠ 0 := fun h ↦ hx (funext fun i ↦ by simpa [xc] using congrFun h i)
    have hpos := hK.dotProduct_mulVec_pos hxc
    have hre : (star xc ⬝ᵥ (((M : Matrix n n ℂ)ᴴ * (M : Matrix n n ℂ)) *ᵥ xc)).re =
        star x ⬝ᵥ (realGram (M : Matrix n n ℂ) *ᵥ x) := by
      simp [xc, dotProduct, mulVec, Complex.re_sum, Finset.mul_sum]
    rw [← hre]
    exact (Complex.pos_iff.1 hpos).1

/-- The real matrix `Re (Mᴴ M) ^ (-1/2)`. Multiplying `M` by it on the right makes the columns
orthonormal for `Re ⟪·, ·⟫`. -/
private abbrev gramNormalizer (M : GL n ℂ) : Matrix n n ℝ :=
  realGram (M : Matrix n n ℂ) ^ (-(1 / 2) : ℝ)

private theorem posDef_gramNormalizer (M : GL n ℂ) : (gramNormalizer M).PosDef :=
  isStrictlyPositive_iff_posDef.1 <|
    IsStrictlyPositive.rpow _ _ (isStrictlyPositive_iff_posDef.2 (posDef_realGram M))

private theorem gramNormalizer_mul_realGram_mul (M : GL n ℂ) :
    (gramNormalizer M)ᵀ * realGram (M : Matrix n n ℂ) * gramNormalizer M = 1 := by
  have hH := isStrictlyPositive_iff_posDef.2 (posDef_realGram M)
  have hT : (gramNormalizer M)ᵀ = gramNormalizer M := by
    exact (by simpa [conjTranspose_eq_transpose_of_trivial] using (posDef_gramNormalizer M).1 :
      (gramNormalizer M).IsSymm).eq
  rw [hT, gramNormalizer]
  nth_rw 2 [← CFC.rpow_one (realGram (M : Matrix n n ℂ)) hH.nonneg]
  rw [← CFC.rpow_add hH.isUnit, ← CFC.rpow_add hH.isUnit]
  norm_num [CFC.rpow_zero _ hH.nonneg]

private theorem isUnit_gramNormalizer_map (M : GL n ℂ) :
    IsUnit ((gramNormalizer M).map ((↑) : ℝ → ℂ)) :=
  (posDef_gramNormalizer M).isUnit.map Complex.ofRealHom.mapMatrix

/-- The frame `M Re (Mᴴ M) ^ (-1/2)`. It spans the same real subspace as `M`, and its columns are
orthonormal for `Re ⟪·, ·⟫`. -/
private def orthoFrame (M : GL n ℂ) : GL n ℂ :=
  M * (isUnit_gramNormalizer_map M).unit

private theorem coe_orthoFrame (M : GL n ℂ) :
    (orthoFrame M : Matrix n n ℂ) = M * (gramNormalizer M).map ((↑) : ℝ → ℂ) :=
  rfl

private theorem realImage_orthoFrame (M : GL n ℂ) :
    realImage (orthoFrame M : Matrix n n ℂ) = realImage (M : Matrix n n ℂ) := by
  rw [coe_orthoFrame]
  exact realImage_mul_map_ofReal _ (posDef_gramNormalizer M).isUnit

private theorem realGram_orthoFrame (M : GL n ℂ) :
    realGram (orthoFrame M : Matrix n n ℂ) = 1 := by
  rw [coe_orthoFrame, realGram_mul_map_ofReal, gramNormalizer_mul_realGram_mul]

private theorem continuous_orthoFrame {X : Type*} [TopologicalSpace X] {M : X → GL n ℂ}
    (hM : Continuous M) : Continuous fun x ↦ orthoFrame (M x) := by
  refine Units.isOpenEmbedding_val.continuous_iff.2 ?_
  have hval : Continuous fun x ↦ (M x : Matrix n n ℂ) := Units.continuous_val.comp hM
  have hG : Continuous fun x ↦ realGram (M x : Matrix n n ℂ) :=
    (hval.matrix_conjTranspose.mul hval).matrix_map Complex.continuous_re
  have hQ : Continuous fun x ↦ gramNormalizer (M x) :=
    (Matrix.contDiffOn_rpow (𝕜 := ℝ) (n := n) (-(1 / 2)) (k := 0)).continuousOn.comp_continuous
      hG fun x ↦ posDef_realGram (M x)
  exact hval.mul (hQ.matrix_map Complex.continuous_ofReal)

/-- Two frames with the same real span whose columns are orthonormal for `Re ⟪·, ·⟫` differ by an
orthogonal matrix on the right. -/
private theorem exists_transpose_mul_self_eq_one {B B' : GL n ℂ}
    (h : realImage (B : Matrix n n ℂ) = realImage (B' : Matrix n n ℂ))
    (hB : realGram (B : Matrix n n ℂ) = 1) (hB' : realGram (B' : Matrix n n ℂ) = 1) :
    ∃ O : Matrix n n ℝ, Oᵀ * O = 1 ∧ (B' : Matrix n n ℂ) = B * O.map ((↑) : ℝ → ℂ) := by
  obtain ⟨O, hO⟩ := exists_eq_mul_map_ofReal h
  refine ⟨O, ?_, hO⟩
  have := realGram_mul_map_ofReal (B : Matrix n n ℂ) O
  rwa [← hO, hB', hB, mul_one, eq_comm] at this

private theorem map_ofReal_mem_unitaryGroup {O : Matrix n n ℝ} (hO : Oᵀ * O = 1) :
    O.map ((↑) : ℝ → ℂ) ∈ unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_map_ofReal]
  have h := congrArg (fun A : Matrix n n ℝ ↦ A.map Complex.ofRealHom) hO
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
  exact h

private theorem polarDeformation_mul_toUnits (t : ℝ) (A : GL n ℂ) (V : unitaryGroup n ℂ) :
    GeneralLinearGroup.polarDeformation (A * Unitary.toUnits V) t =
      GeneralLinearGroup.polarDeformation A t * Unitary.toUnits V := by
  simpa using GeneralLinearGroup.polarDeformation_unitary_mul_mul_unitary t A 1 V

/-- **The Lagrangian deformation of a closed frame.** A continuous path `M` of invertible complex
matrices with `M 0 ℝⁿ = M 1 ℝⁿ` is deformed, through continuous paths `F (s, ·)` with
`F (s, 0) ℝⁿ = F (s, 1) ℝⁿ`, from a path with the same real spans as `M` to a path of unitary
matrices. First orthonormalize the real frames, so that the endpoint monodromy is orthogonal;
then contract the positive factor of the polar decomposition, which is equivariant under that
monodromy. -/
private theorem exists_frameHomotopy {M : I → GL n ℂ} (hM : Continuous M)
    (h01 : realImage (M 0 : Matrix n n ℂ) = realImage (M 1 : Matrix n n ℂ)) :
    ∃ F : I × I → GL n ℂ, Continuous F ∧
      (∀ t, realImage (F (0, t) : Matrix n n ℂ) = realImage (M t : Matrix n n ℂ)) ∧
      (∀ s, realImage (F (s, 0) : Matrix n n ℂ) = realImage (F (s, 1) : Matrix n n ℂ)) ∧
      ∀ t, (F (1, t) : Matrix n n ℂ) ∈ unitaryGroup n ℂ := by
  obtain ⟨O, hOO, hO⟩ := exists_transpose_mul_self_eq_one (B := orthoFrame (M 0))
    (B' := orthoFrame (M 1)) (by rw [realImage_orthoFrame, realImage_orthoFrame, h01])
    (realGram_orthoFrame _) (realGram_orthoFrame _)
  have hOu := map_ofReal_mem_unitaryGroup hOO
  have hO1 : orthoFrame (M 1) = orthoFrame (M 0) * Unitary.toUnits ⟨_, hOu⟩ := Units.ext hO
  have hOunit : IsUnit O :=
    (Matrix.isUnit_iff_isUnit_det O).2 (Matrix.isUnit_det_of_left_inverse hOO)
  refine ⟨fun p ↦ GeneralLinearGroup.polarDeformation (orthoFrame (M p.2)) p.1, ?_,
    fun t ↦ ?_, fun s ↦ ?_, fun t ↦ ?_⟩
  · have h := (GeneralLinearGroup.contMDiff_polarDeformation (n := n) (𝕜 := ℂ) (k := 0)).continuous
    exact h.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      ((continuous_orthoFrame hM).comp continuous_snd))
  · simp [realImage_orthoFrame]
  · simp only
    rw [hO1, polarDeformation_mul_toUnits, Units.val_mul, Unitary.val_toUnits_apply]
    exact (realImage_mul_map_ofReal _ hOunit).symm
  · simp

/-! ### Loops of totally real subspaces of `ℂⁿ` -/

/-- The continuous linear automorphism of `ℂⁿ` given by an invertible matrix. -/
private abbrev frameCLE (A : GL n ℂ) : EuclideanSpace ℂ n ≃L[ℂ] EuclideanSpace ℂ n :=
  (A : Matrix n n ℂ).toEuclideanCLE A.det_ne_zero

private theorem coe_frameCLE (A : GL n ℂ) :
    ((frameCLE A).toLinearEquiv : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) =
      (toEuclideanCLM (𝕜 := ℂ) (A : Matrix n n ℂ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
  LinearMap.ext fun x ↦ by simp [frameCLE, toEuclideanCLE_apply, toEuclideanCLM_apply]

private theorem continuous_toEuclideanCLM :
    Continuous (toEuclideanCLM (n := n) (𝕜 := ℂ) :
      Matrix n n ℂ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
  LinearMap.continuous_of_finiteDimensional
    (toEuclideanCLM (n := n) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap

private theorem continuous_toEuclideanCLM_symm :
    Continuous ((toEuclideanCLM (n := n) (𝕜 := ℂ)).symm :
      (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) → Matrix n n ℂ) :=
  LinearMap.continuous_of_finiteDimensional
    (toEuclideanCLM (n := n) (𝕜 := ℂ)).symm.toAlgEquiv.toLinearEquiv.toLinearMap

/-- The invertible matrix of a continuous linear automorphism of `ℂⁿ`. -/
private def toGL (D : EuclideanSpace ℂ n ≃L[ℂ] EuclideanSpace ℂ n) : GL n ℂ where
  val := (toEuclideanCLM (n := n) (𝕜 := ℂ)).symm (D : EuclideanSpace ℂ n →L[ℂ] _)
  inv := (toEuclideanCLM (n := n) (𝕜 := ℂ)).symm (D.symm : EuclideanSpace ℂ n →L[ℂ] _)
  val_inv := by
    rw [← map_mul, ContinuousLinearMap.mul_def, ContinuousLinearEquiv.coe_comp_coe_symm,
      ← ContinuousLinearMap.one_def, map_one]
  inv_val := by
    rw [← map_mul, ContinuousLinearMap.mul_def, ContinuousLinearEquiv.coe_symm_comp_coe,
      ← ContinuousLinearMap.one_def, map_one]

private theorem realImage_toGL (D : EuclideanSpace ℂ n ≃L[ℂ] EuclideanSpace ℂ n) :
    realImage (toGL D : Matrix n n ℂ) =
      (realSubspace n).map ((D.toLinearEquiv : EuclideanSpace ℂ n →ₗ[ℂ] _).restrictScalars ℝ) := by
  simp only [realImage, toGL, Units.val_mk, StarAlgEquiv.apply_symm_apply]
  rfl

private theorem continuous_toGL {X : Type*} [TopologicalSpace X]
    {D : X → EuclideanSpace ℂ n ≃L[ℂ] EuclideanSpace ℂ n}
    (hD : Continuous fun x ↦ (D x : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)) :
    Continuous fun x ↦ toGL (D x) :=
  Units.isOpenEmbedding_val.continuous_iff.2 (continuous_toEuclideanCLM_symm.comp hD)

private theorem continuous_coe_frameCLE {X : Type*} [TopologicalSpace X] {F : X → GL n ℂ}
    (hF : Continuous F) :
    Continuous fun x ↦ (frameCLE (F x) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) := by
  have h : ∀ x, (frameCLE (F x) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) =
      toEuclideanCLM (𝕜 := ℂ) (F x : Matrix n n ℂ) := fun x ↦
    ContinuousLinearMap.coe_injective (coe_frameCLE (F x))
  simp only [h]
  exact continuous_toEuclideanCLM.comp (Units.continuous_val.comp hF)

/-- **Loops of totally real subspaces deform to Lagrangian loops.** Every loop `Λ` of maximal
totally real subspaces of `ℂⁿ` has the Maslov index of a loop `t ↦ U t ℝⁿ` of Lagrangian
subspaces, for a continuous path `U` of unitary matrices. -/
theorem TotallyRealLoop.exists_unitary_maslovIndex_eq
    (Λ : TotallyRealLoop (EuclideanSpace ℂ n)) :
    ∃ U : I → unitaryGroup n ℂ, Continuous U ∧
      ∃ Λ' : TotallyRealLoop (EuclideanSpace ℂ n),
        (∀ t, Λ' t = (realSubspace n).map
          (((toEuclideanCLM (𝕜 := ℂ) (U t : Matrix n n ℂ) :
            EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
              EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).restrictScalars ℝ)) ∧
        Λ'.maslovIndex = Λ.maslovIndex := by
  obtain ⟨L₀, hL₀, A, hAc, hA⟩ := Λ.exists_frame
  obtain ⟨C, hC⟩ := isMaximalTotallyReal_realSubspace.exists_linearEquiv_map_eq hL₀
  -- The frame `t ↦ A t ∘ C` of `Λ`, based at `ℝⁿ`, as a path of invertible matrices.
  let M : I → GL n ℂ := fun t ↦ toGL (C.toContinuousLinearEquiv.trans (A t))
  have hMc : Continuous M := continuous_toGL <|
    (hAc.clm_comp (continuous_const (y := (C.toContinuousLinearEquiv :
      EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)))).congr fun _ ↦
        ContinuousLinearMap.ext fun _ ↦ rfl
  have hMΛ (t : I) : realImage (M t : Matrix n n ℂ) = Λ t := by
    rw [realImage_toGL, hA t, ← hC, ← Submodule.map_comp]
    rfl
  obtain ⟨F, hFc, hF0, hFclosed, hF1⟩ :=
    exists_frameHomotopy hMc (by rw [hMΛ, hMΛ]; exact Λ.toFun_zero_eq_toFun_one)
  have hF1c : Continuous fun t : I ↦ F (1, t) := hFc.comp (Continuous.prodMk_right 1)
  let Λ' : TotallyRealLoop (EuclideanSpace ℂ n) :=
    { toFun := fun t ↦ realImage (F (1, t) : Matrix n n ℂ)
      exists_frame := ⟨realSubspace n, isMaximalTotallyReal_realSubspace,
        fun t ↦ frameCLE (F (1, t)), continuous_coe_frameCLE hF1c,
        fun t ↦ by rw [coe_frameCLE]⟩
      toFun_zero_eq_toFun_one := hFclosed 1 }
  refine ⟨fun t ↦ ⟨F (1, t), hF1 t⟩, (Units.continuous_val.comp hF1c).subtype_mk _,
    Λ', fun t ↦ rfl, ?_⟩
  refine (Λ.maslovIndex_eq_of_homotopy Λ' isMaximalTotallyReal_realSubspace
    (fun p ↦ frameCLE (F p)) (continuous_coe_frameCLE hFc) (fun t ↦ ?_) (fun t ↦ ?_)
    (fun s ↦ ?_)).symm
  · rw [coe_frameCLE, ← hMΛ]
    exact (hF0 t).symm
  · rw [coe_frameCLE]
  · rw [coe_frameCLE, coe_frameCLE]
    exact hFclosed s

/-- The image of `ℝⁿ` under a unitary matrix is isotropic for the standard symplectic form
`Im ⟪·, ·⟫` of `ℂⁿ`; being maximal totally real, it is a Lagrangian subspace. -/
theorem im_inner_eq_zero_of_mem_map_unitary {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ)
    {v w : EuclideanSpace ℂ n}
    (hv : v ∈ (realSubspace n).map (((toEuclideanCLM (𝕜 := ℂ) U :
      EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
        EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).restrictScalars ℝ))
    (hw : w ∈ (realSubspace n).map (((toEuclideanCLM (𝕜 := ℂ) U :
      EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
        EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).restrictScalars ℝ)) :
    (inner ℂ v w).im = 0 := by
  obtain ⟨x, hx, rfl⟩ := hv
  obtain ⟨y, hy, rfl⟩ := hw
  have hU' : toEuclideanCLM (𝕜 := ℂ) U ∈ unitary (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
    ⟨by rw [← map_star, ← map_mul, Unitary.star_mul_self_of_mem hU, map_one],
      by rw [← map_star, ← map_mul, Unitary.mul_star_self_of_mem hU, map_one]⟩
  simp only [LinearMap.restrictScalars_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.inner_map_map_of_mem_unitary hU', PiLp.inner_apply, Complex.im_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  simp [Complex.mul_im, (mem_realSubspace.1 hx) i, (mem_realSubspace.1 hy) i]

end TauCeti
