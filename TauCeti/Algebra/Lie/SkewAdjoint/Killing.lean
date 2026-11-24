/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.Algebra.Lie.SkewAdjoint
import TauCeti.Algebra.Lie.GeneralLinear.Killing
import TauCeti.Algebra.Lie.OfAssociative
import TauCeti.LinearAlgebra.Matrix.SkewAdjoint
import TauCeti.LinearAlgebra.Matrix.Trace.LinearMap

/-!
# The Killing form of a skew-adjoint matrix Lie algebra

Let `J` be an invertible `n × n` matrix over a field `K` of characteristic other than two with
`Jᵀ = ε • J`. The orthogonal Lie algebras are the case `ε = 1` and the symplectic Lie algebra is
the case `ε = -1`. On the Lie algebra `skewAdjointMatricesLieSubalgebra J` of the matrices `A` with
`Aᵀ J = -J A`, the Killing form is

`κ(X, Y) = (n - 2 ε) trace (X * Y)`.

A matrix `A` lies in this Lie algebra exactly when `J⁻¹ Aᵀ J = -A`
(`Matrix.isSkewAdjoint_iff_inv_mul_transpose_mul_eq_neg`), and `Z ↦ J⁻¹ Zᵀ J` is an involution
of the matrices. So `Z ↦ Z - J⁻¹ Zᵀ J` maps `gl n K` onto the Lie algebra, acting on it as
multiplication by two. The operator `ad X ∘ ad Y` of `gl n K` preserves the Lie algebra, so twice
its trace there is its trace on `gl n K`, which is `2 n trace (X * Y)` (`Matrix.killingForm_apply`),
minus the trace of its composite with `Z ↦ J⁻¹ Zᵀ J`, which is `4 ε trace (X * Y)`.

## Main results

* `TauCeti.killingForm_skewAdjointMatricesLieSubalgebra_apply`: `κ(X, Y) = (n - 2 ε) trace (X * Y)`
  on `skewAdjointMatricesLieSubalgebra J` for an invertible `J` with `Jᵀ = ε • J`.

## References

* W. Fulton and J. Harris, *Representation Theory*, Lectures 16 and 18 (the symplectic and
  orthogonal Lie algebras).
* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics
  140, Birkhäuser, 2002, Chapter I (the Killing forms of the classical Lie algebras).
-/

public section

open Matrix _root_.LieAlgebra LieModule

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [DecidableEq n] [Fintype n] {K : Type*} [Field K] {J : Matrix n n K} {ε : K}

/-- The operator `Z ↦ J⁻¹ Zᵀ J` of the square matrices, whose fixed points up to sign are the
skew-adjoint matrices for an invertible `J`. -/
private noncomputable def transposeConj (J : Matrix n n K) : Matrix n n K →ₗ[K] Matrix n n K :=
  LinearMap.mulLeft K J⁻¹ ∘ₗ LinearMap.mulRight K J ∘ₗ
    (transposeLinearEquiv n n K K).toLinearMap

private theorem transposeConj_apply (Z : Matrix n n K) : transposeConj J Z = J⁻¹ * Zᵀ * J := by
  simp [transposeConj, mul_assoc]

/-- For an invertible `J` with `Jᵀ = ε • J`, the operator `Z ↦ J⁻¹ Zᵀ J` is an involution. -/
private theorem transposeConj_transposeConj (hJ : Jᵀ = ε • J) (hJu : IsUnit J)
    (Z : Matrix n n K) : transposeConj J (transposeConj J Z) = Z := by
  have hd := (isUnit_iff_isUnit_det J).mp hJu
  -- Transposing `Jᵀ = ε • J` gives `J = ε • Jᵀ = (ε * ε) • J`, so `(ε * ε) • 1 = 1`.
  have hJ' : J = ε • Jᵀ := by simpa using congrArg transpose hJ
  have hε : (ε * ε) • (1 : Matrix n n K) = 1 := by
    have h : (ε * ε) • J = J := by rw [mul_smul, ← hJ, ← hJ']
    rw [← mul_nonsing_inv _ hd, ← Matrix.smul_mul, h]
  have h1 : J⁻¹ * Jᵀ = ε • 1 := by
    rw [hJ, Matrix.mul_smul, nonsing_inv_mul _ hd]
  have h2 : (Jᵀ)⁻¹ * J = ε • 1 := calc
    (Jᵀ)⁻¹ * J = (Jᵀ)⁻¹ * (ε • Jᵀ) := congrArg _ hJ'
    _ = ε • 1 := by rw [Matrix.mul_smul, nonsing_inv_mul _ (isUnit_det_transpose J hd)]
  rw [transposeConj_apply, transposeConj_apply, transpose_mul, transpose_mul, transpose_transpose,
    transpose_nonsing_inv]
  calc J⁻¹ * (Jᵀ * (Z * (Jᵀ)⁻¹)) * J = (J⁻¹ * Jᵀ) * Z * ((Jᵀ)⁻¹ * J) := by
        simp only [Matrix.mul_assoc]
    _ = Z := by
        rw [h1, h2, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
          ← Matrix.one_mul Z, ← Matrix.smul_mul, hε, Matrix.one_mul]

/-- The trace of `Z ↦ J⁻¹ (A Z B)ᵀ J` on the matrices, for `Jᵀ = ε • J`. -/
private theorem trace_transposeConj_comp (hJ : Jᵀ = ε • J) (A B : Matrix n n K) :
    LinearMap.trace K _ (transposeConj J ∘ₗ LinearMap.mulLeft K A ∘ₗ LinearMap.mulRight K B) =
      ε * (J⁻¹ * Bᵀ * J * A).trace := by
  have h : transposeConj J ∘ₗ LinearMap.mulLeft K A ∘ₗ LinearMap.mulRight K B =
      LinearMap.mulLeft K (J⁻¹ * Bᵀ) ∘ₗ LinearMap.mulRight K (Aᵀ * J) ∘ₗ
        (transposeLinearEquiv n n K K).toLinearMap := by
    ext1 Z
    simp [transposeConj_apply, transpose_mul, mul_assoc]
  rw [h, trace_mulLeft_comp_mulRight_comp_transpose, transpose_mul, transpose_transpose, hJ,
    Matrix.smul_mul, Matrix.mul_smul, trace_smul, smul_eq_mul]
  simp only [mul_assoc]

/-- For `A, B` skew-adjoint for an invertible `J` with `Jᵀ = ε • J`, the operator
`Z ↦ J⁻¹ (⁅A, ⁅B, Z⁆⁆)ᵀ J` of the matrices has trace `4 ε trace (A * B)`. -/
private theorem trace_transposeConj_comp_ad_comp_ad (hJ : Jᵀ = ε • J) (hJu : IsUnit J)
    {A B : Matrix n n K} (hA : A ∈ skewAdjointMatricesLieSubalgebra J)
    (hB : B ∈ skewAdjointMatricesLieSubalgebra J) :
    LinearMap.trace K _ (transposeConj J ∘ₗ ad K _ A ∘ₗ ad K _ B) = 4 * ε * (A * B).trace := by
  have hA' := (isSkewAdjoint_iff_inv_mul_transpose_mul_eq_neg hJu).mp
    ((mem_skewAdjointMatricesSubmodule J A).mp ((mem_skewAdjointMatricesLieSubalgebra J A).mp hA))
  have hB' := (isSkewAdjoint_iff_inv_mul_transpose_mul_eq_neg hJu).mp
    ((mem_skewAdjointMatricesSubmodule J B).mp ((mem_skewAdjointMatricesLieSubalgebra J B).mp hB))
  have hJJ : J⁻¹ * J = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det J).mp hJu)
  have hJJ' : J * J⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det J).mp hJu)
  have hBA : J⁻¹ * (B * A)ᵀ * J = A * B := by
    calc J⁻¹ * (B * A)ᵀ * J = (J⁻¹ * Aᵀ * J) * (J⁻¹ * Bᵀ * J) := by
          simp only [transpose_mul, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc J J⁻¹, hJJ', Matrix.one_mul]
      _ = A * B := by rw [hA', hB', neg_mul_neg]
  have hl : transposeConj J ∘ₗ LinearMap.mulLeft K (A * B) =
      transposeConj J ∘ₗ LinearMap.mulLeft K (A * B) ∘ₗ LinearMap.mulRight K 1 := by
    ext1 Z; simp
  have hr : transposeConj J ∘ₗ LinearMap.mulRight K (B * A) =
      transposeConj J ∘ₗ LinearMap.mulLeft K 1 ∘ₗ LinearMap.mulRight K (B * A) := by
    ext1 Z; simp
  rw [ad_comp_ad]
  simp only [LinearMap.comp_add, LinearMap.comp_sub, map_add, map_sub]
  rw [hl, hr]
  simp only [trace_transposeConj_comp hJ, transpose_one, Matrix.mul_one, hJJ, Matrix.one_mul, hA',
    hB', hBA, neg_mul, trace_neg, trace_mul_comm B A]
  ring

variable [NeZero (2 : K)]

/-- Twice the Killing form of the skew-adjoint matrix Lie algebra of an invertible `J` with
`Jᵀ = ε • J` is twice `(n - 2 ε) trace (X * Y)`. -/
private theorem two_mul_killingForm_skewAdjointMatricesLieSubalgebra_apply (hJ : Jᵀ = ε • J)
    (hJu : IsUnit J) (X Y : skewAdjointMatricesLieSubalgebra J) :
    2 * killingForm K (skewAdjointMatricesLieSubalgebra J) X Y =
      2 * ((Fintype.card n - 2 * ε) * ((X : Matrix n n K) * Y).trace) := by
  set L := ad K (Matrix n n K) X ∘ₗ ad K (Matrix n n K) Y with hL
  -- `Z ↦ Z - J⁻¹ Zᵀ J` maps the matrices to the skew-adjoint matrices, as twice the identity
  -- on them.
  let P : Matrix n n K →ₗ[K] skewAdjointMatricesLieSubalgebra J :=
    LinearMap.codRestrict (skewAdjointMatricesLieSubalgebra J).toSubmodule
      (LinearMap.id - transposeConj J) fun Z ↦ (mem_skewAdjointMatricesLieSubalgebra J _).mpr
        ((mem_skewAdjointMatricesSubmodule J _).mpr
          ((isSkewAdjoint_iff_inv_mul_transpose_mul_eq_neg hJu).mpr (by
            rw [← transposeConj_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub,
              transposeConj_transposeConj hJ hJu, neg_sub])))
  -- `P` lands in the subtype of the submodule underlying the Lie subalgebra, which is the
  -- subtype of the Lie subalgebra itself, so `LinearMap.codRestrict_apply` computes it.
  have hP (Z : Matrix n n K) : (P Z : Matrix n n K) = Z - transposeConj J Z :=
    LinearMap.codRestrict_apply _ _ Z
  have h1 : P ∘ₗ L ∘ₗ (skewAdjointMatricesLieSubalgebra J).incl.toLinearMap =
      (2 : K) • (ad K _ X ∘ₗ ad K _ Y) := by
    ext1 W
    have hW : transposeConj J (L W) = -L W := by
      rw [transposeConj_apply]
      refine (isSkewAdjoint_iff_inv_mul_transpose_mul_eq_neg hJu).mp
        ((mem_skewAdjointMatricesSubmodule J _).mp
          ((mem_skewAdjointMatricesLieSubalgebra J _).mp ?_))
      exact (skewAdjointMatricesLieSubalgebra J).lie_mem X.property
        ((skewAdjointMatricesLieSubalgebra J).lie_mem Y.property W.property)
    apply Subtype.ext
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hP, LieHom.coe_toLinearMap,
      LieSubalgebra.coe_incl, hW, sub_neg_eq_add]
    simp [hL, two_smul]
  have h2 : (skewAdjointMatricesLieSubalgebra J).incl.toLinearMap ∘ₗ P =
      LinearMap.id - transposeConj J := by
    ext1 Z
    rw [LinearMap.comp_apply, LieHom.coe_toLinearMap, LieSubalgebra.coe_incl, hP,
      LinearMap.sub_apply, LinearMap.id_apply]
  -- Cycling the trace moves the computation to the matrices.
  have htrace :
      LinearMap.trace K _ (P ∘ₗ L ∘ₗ (skewAdjointMatricesLieSubalgebra J).incl.toLinearMap) =
        LinearMap.trace K _ L - LinearMap.trace K _ (transposeConj J ∘ₗ L) := by
    rw [← LinearMap.comp_assoc, ← LinearMap.trace_comp_comm', ← LinearMap.comp_assoc, h2,
      LinearMap.sub_comp, map_sub, LinearMap.id_comp]
  rw [h1, map_smul, smul_eq_mul, ← killingForm_apply_apply] at htrace
  have := invertibleOfNonzero (two_ne_zero (α := K))
  rw [htrace, hL, ← killingForm_apply_apply, Matrix.killingForm_apply,
    IsSkewAdjoint.trace_eq_zero hJu ((mem_skewAdjointMatricesSubmodule J _).mp X.property),
    trace_transposeConj_comp_ad_comp_ad hJ hJu X.property Y.property]
  ring

/-- **The Killing form of a skew-adjoint matrix Lie algebra**: on the Lie algebra of the matrices
skew-adjoint for an invertible `n × n` matrix `J` with `Jᵀ = ε • J`,
`κ(X, Y) = (n - 2 ε) trace (X * Y)`, over every field of characteristic other than two. The
orthogonal Lie algebras are the case `ε = 1`, the symplectic Lie algebra the case `ε = -1`. -/
theorem killingForm_skewAdjointMatricesLieSubalgebra_apply (hJ : Jᵀ = ε • J) (hJu : IsUnit J)
    (X Y : skewAdjointMatricesLieSubalgebra J) :
    killingForm K (skewAdjointMatricesLieSubalgebra J) X Y =
      (Fintype.card n - 2 * ε) * ((X : Matrix n n K) * Y).trace :=
  mul_left_cancel₀ two_ne_zero
    (two_mul_killingForm_skewAdjointMatricesLieSubalgebra_apply hJ hJu X Y)

end TauCeti
