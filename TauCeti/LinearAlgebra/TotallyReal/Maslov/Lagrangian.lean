/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.Analysis.Matrix.Polar.Deformation
public import TauCeti.LinearAlgebra.TotallyReal.Euclidean
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
continuous frames, built as follows. Write `Λ t = M t ℝⁿ` (`Matrix.realImage`) for a continuous
path `M` of invertible matrices; closedness of the loop says `M 1 = M 0 G` for a real invertible
matrix `G`.

* **Orthonormalization.** Replacing `M` by `B = M Re (Mᴴ M) ^ (-1/2)` does not change the real
  spans `M t ℝⁿ`, because the correction is real and invertible, and it makes the columns of
  `B t` orthonormal for the real inner product `Re ⟪·, ·⟫`. Two such frames with the same real
  span differ by a real orthogonal matrix, so `B 1 = B 0 O` with `O` orthogonal, hence unitary.
* **Polar contraction.** Contracting the positive factor of the polar decomposition
  `B t = P t V t`, through `P t ^ (1 - s) V t`
  (`Matrix.GeneralLinearGroup.polarDeformation`), is equivariant under right multiplication by
  the unitary monodromy `O` (`Matrix.GeneralLinearGroup.polarDeformation_mul_toUnits`). So every
  intermediate path still closes up as a loop of subspaces, and at `s = 1` it reaches the unitary
  path `V`. Homotopy invariance of the Maslov index
  (`TauCeti.TotallyRealLoop.maslovIndex_eq_of_homotopy`) then compares the two loops.

Without the orthonormalization the monodromy `G` need not be orthogonal, and the polar
contraction of `M` need not close up.

## Main declarations

* `TauCeti.TotallyRealLoop.exists_unitary_maslovIndex_eq`: every loop of maximal totally real
  subspaces of `ℂⁿ` has the Maslov index of a loop `t ↦ U t ℝⁿ` with `U` a continuous path of
  unitary matrices.
* `TauCeti.im_inner_eq_zero_of_mem_realImage`: the subspace `U ℝⁿ` is isotropic for
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

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Orthonormalizing a frame by a real change of basis -/

/-- The real Gram matrix `Re (Mᴴ M)` of the columns of `M`, for the real inner product
`Re ⟪v, w⟫` of `ℂⁿ`. -/
private abbrev realGram (M : Matrix n n ℂ) : Matrix n n ℝ := (Mᴴ * M).map Complex.re

omit [DecidableEq n] in
private theorem realGram_mul_map_ofReal (M : Matrix n n ℂ) (N : Matrix n n ℝ) :
    realGram (M * N.map ((↑) : ℝ → ℂ)) = Nᵀ * realGram M * N := by
  have h : (M * N.map ((↑) : ℝ → ℂ))ᴴ * (M * N.map ((↑) : ℝ → ℂ)) =
      Nᵀ.map ((↑) : ℝ → ℂ) * (Mᴴ * M) * N.map ((↑) : ℝ → ℂ) := by
    rw [conjTranspose_mul, ← conjTranspose_map _ fun _ ↦ (Complex.conj_ofReal _).symm,
      conjTranspose_eq_transpose_of_trivial]
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
    (orthoFrame M : Matrix n n ℂ).realImage = (M : Matrix n n ℂ).realImage := by
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
    (h : (B : Matrix n n ℂ).realImage = (B' : Matrix n n ℂ).realImage)
    (hB : realGram (B : Matrix n n ℂ) = 1) (hB' : realGram (B' : Matrix n n ℂ) = 1) :
    ∃ O : Matrix n n ℝ, Oᵀ * O = 1 ∧ (B' : Matrix n n ℂ) = B * O.map ((↑) : ℝ → ℂ) := by
  obtain ⟨O, hO⟩ := exists_eq_mul_map_ofReal h
  refine ⟨O, ?_, hO⟩
  have := realGram_mul_map_ofReal (B : Matrix n n ℂ) O
  rwa [← hO, hB', hB, mul_one, eq_comm] at this

/-- **The Lagrangian deformation of a closed frame.** A continuous path `M` of invertible complex
matrices with `M 0 ℝⁿ = M 1 ℝⁿ` is deformed, through continuous paths `F (s, ·)` with
`F (s, 0) ℝⁿ = F (s, 1) ℝⁿ`, from a path with the same real spans as `M` to a path of unitary
matrices. First orthonormalize the real frames, so that the endpoint monodromy is orthogonal;
then contract the positive factor of the polar decomposition, which is equivariant under that
monodromy. -/
private theorem exists_frameHomotopy {M : I → GL n ℂ} (hM : Continuous M)
    (h01 : (M 0 : Matrix n n ℂ).realImage = (M 1 : Matrix n n ℂ).realImage) :
    ∃ F : I × I → GL n ℂ, Continuous F ∧
      (∀ t, (F (0, t) : Matrix n n ℂ).realImage = (M t : Matrix n n ℂ).realImage) ∧
      (∀ s, (F (s, 0) : Matrix n n ℂ).realImage = (F (s, 1) : Matrix n n ℂ).realImage) ∧
      ∀ t, (F (1, t) : Matrix n n ℂ) ∈ unitaryGroup n ℂ := by
  obtain ⟨O, hOO, hO⟩ := exists_transpose_mul_self_eq_one (B := orthoFrame (M 0))
    (B' := orthoFrame (M 1)) (by rw [realImage_orthoFrame, realImage_orthoFrame, h01])
    (realGram_orthoFrame _) (realGram_orthoFrame _)
  have hOu := map_ofReal_mem_unitaryGroup ((mem_orthogonalGroup_iff' n ℝ).2 hOO)
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
    rw [hO1, GeneralLinearGroup.polarDeformation_mul_toUnits, Units.val_mul,
      Unitary.val_toUnits_apply]
    exact (realImage_mul_map_ofReal _ hOunit).symm
  · simp

/-! ### Loops of totally real subspaces of `ℂⁿ` -/

/-- The continuous linear automorphism of `ℂⁿ` given by an invertible matrix. -/
private abbrev frameCLE (A : GL n ℂ) : EuclideanSpace ℂ n ≃L[ℂ] EuclideanSpace ℂ n :=
  (A : Matrix n n ℂ).toEuclideanCLE A.det_ne_zero

private theorem realImage_ofEuclideanCLE (D : EuclideanSpace ℂ n ≃L[ℂ] EuclideanSpace ℂ n) :
    (GeneralLinearGroup.ofEuclideanCLE D : Matrix n n ℂ).realImage =
      (realSubspace n).map ((D.toLinearEquiv : EuclideanSpace ℂ n →ₗ[ℂ] _).restrictScalars ℝ) := by
  rw [realImage_eq_map_toEuclideanCLE (GeneralLinearGroup.ofEuclideanCLE D).det_ne_zero,
    GeneralLinearGroup.toEuclideanCLE_ofEuclideanCLE]

private theorem continuous_coe_frameCLE {X : Type*} [TopologicalSpace X] {F : X → GL n ℂ}
    (hF : Continuous F) :
    Continuous fun x ↦ (frameCLE (F x) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) := by
  simp only [frameCLE, coe_toEuclideanCLE]
  exact continuous_toEuclideanCLM.comp (Units.continuous_val.comp hF)

/-- **Loops of totally real subspaces deform to Lagrangian loops.** Every loop `Λ` of maximal
totally real subspaces of `ℂⁿ` has the Maslov index of a loop `t ↦ U t ℝⁿ` of Lagrangian
subspaces, for a continuous path `U` of unitary matrices. -/
theorem TotallyRealLoop.exists_unitary_maslovIndex_eq
    (Λ : TotallyRealLoop (EuclideanSpace ℂ n)) :
    ∃ U : I → unitaryGroup n ℂ, Continuous U ∧
      ∃ Λ' : TotallyRealLoop (EuclideanSpace ℂ n),
        (∀ t, Λ' t = (U t : Matrix n n ℂ).realImage) ∧
        Λ'.maslovIndex = Λ.maslovIndex := by
  obtain ⟨L₀, hL₀, A, hAc, hA⟩ := Λ.exists_frame
  obtain ⟨C, hC⟩ := isMaximalTotallyReal_realSubspace.exists_linearEquiv_map_eq hL₀
  -- The frame `t ↦ A t ∘ C` of `Λ`, based at `ℝⁿ`, as a path of invertible matrices.
  let M : I → GL n ℂ := fun t ↦
    GeneralLinearGroup.ofEuclideanCLE (C.toContinuousLinearEquiv.trans (A t))
  have hMc : Continuous M := GeneralLinearGroup.continuous_ofEuclideanCLE <|
    (hAc.clm_comp (continuous_const (y := (C.toContinuousLinearEquiv :
      EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)))).congr fun _ ↦
        ContinuousLinearEquiv.comp_coe _ _
  have hMΛ (t : I) : (M t : Matrix n n ℂ).realImage = Λ t := by
    rw [realImage_ofEuclideanCLE, hA t, ← hC, ← Submodule.map_comp]
    refine congrArg (fun f ↦ (realSubspace n).map f) (LinearMap.ext fun v ↦ ?_)
    simp
  obtain ⟨F, hFc, hF0, hFclosed, hF1⟩ :=
    exists_frameHomotopy hMc (by rw [hMΛ, hMΛ]; exact Λ.toFun_zero_eq_toFun_one)
  have hF1c : Continuous fun t : I ↦ F (1, t) := hFc.comp (Continuous.prodMk_right 1)
  let Λ' : TotallyRealLoop (EuclideanSpace ℂ n) :=
    { toFun := fun t ↦ (F (1, t) : Matrix n n ℂ).realImage
      exists_frame := ⟨realSubspace n, isMaximalTotallyReal_realSubspace,
        fun t ↦ frameCLE (F (1, t)), continuous_coe_frameCLE hF1c,
        fun t ↦ realImage_eq_map_toEuclideanCLE _⟩
      toFun_zero_eq_toFun_one := hFclosed 1 }
  refine ⟨fun t ↦ ⟨F (1, t), hF1 t⟩, (Units.continuous_val.comp hF1c).subtype_mk _,
    Λ', fun t ↦ rfl, ?_⟩
  refine (Λ.maslovIndex_eq_of_homotopy Λ' isMaximalTotallyReal_realSubspace
    (fun p ↦ frameCLE (F p)) (continuous_coe_frameCLE hFc) (fun t ↦ ?_) (fun t ↦ ?_)
    (fun s ↦ ?_)).symm
  · rw [← realImage_eq_map_toEuclideanCLE, ← hMΛ]
    exact (hF0 t).symm
  · rw [← realImage_eq_map_toEuclideanCLE]
  · rw [← realImage_eq_map_toEuclideanCLE, ← realImage_eq_map_toEuclideanCLE]
    exact hFclosed s

/-- The image of `ℝⁿ` under a unitary matrix is isotropic for the standard symplectic form
`Im ⟪·, ·⟫` of `ℂⁿ`; being maximal totally real, it is a Lagrangian subspace. -/
theorem im_inner_eq_zero_of_mem_realImage {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ)
    {v w : EuclideanSpace ℂ n} (hv : v ∈ U.realImage) (hw : w ∈ U.realImage) :
    (inner ℂ v w).im = 0 := by
  obtain ⟨x, hx, rfl⟩ := mem_realImage.1 hv
  obtain ⟨y, hy, rfl⟩ := mem_realImage.1 hw
  simp only [mem_unitaryGroup_iff_inner_toEuclideanCLM.1 hU x y, PiLp.inner_apply,
    Complex.im_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  simp [Complex.mul_im, (mem_realSubspace.1 hx) i, (mem_realSubspace.1 hy) i]

end TauCeti
