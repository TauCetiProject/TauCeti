/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.IntUnitsPower
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.LinearAlgebra.Graded.LinearMap
import Mathlib.GroupTheory.GroupAction.Ring
import TauCeti.Algebra.DirectSum.Internal

/-!
# The grade involution of a parity-graded algebra

On an internally `ZMod 2`-graded algebra `A`, the linear map `proj 0 - proj 1` fixes the even piece
`𝒜 0` and negates the odd piece `𝒜 1`, so on any homogeneous element `a ∈ 𝒜 i` it acts by the
sign `(-1 : ℤˣ) ^ i`. Because multiplication adds parities and `1 ∈ 𝒜 0`, this map is an
involutive `R`-algebra automorphism `TauCeti.gradeInvolution 𝒜 : A ≃ₐ[R] A`.

No invertibility of `2` is needed: the projections come from the internal direct-sum decomposition
rather than from `±1`-eigenspaces, and in characteristic `2` the involution reduces to the identity.
This supplies the parity automorphism behind the Koszul-signed Leibniz rule on parity-graded
algebras without choosing an integer lift of the grading.

## Main definitions

* `TauCeti.gradeInvolution 𝒜`: the grade involution `A ≃ₐ[R] A` of a `ZMod 2`-graded algebra.

## Main results

* `TauCeti.gradeInvolution_apply`: `gradeInvolution 𝒜 a = proj 𝒜 0 a - proj 𝒜 1 a`.
* `TauCeti.gradeInvolution_apply_of_mem`: on `a ∈ 𝒜 i`, `gradeInvolution 𝒜 a = ((-1 : ℤˣ) ^ i) • a`.
* `TauCeti.gradeInvolution_apply_of_mem_zero` and `TauCeti.gradeInvolution_apply_of_mem_one`:
  the action on the even and odd pieces.
* `TauCeti.gradeInvolution_mem_iff`, `TauCeti.isHomogeneous_gradeInvolution`, and
  `TauCeti.decompose_gradeInvolution`: piece invariance and homogeneous component action.
* `TauCeti.LinearMap.IsHomogeneous.gradeInvolution_apply`: parity-homogeneous linear maps
  intertwine grade involutions up to sign.
* `TauCeti.gradeInvolution_gradeInvolution`, `TauCeti.gradeInvolution_symm`, and
  `TauCeti.gradeInvolution_trans_self`: involutivity and self-composition identities.
-/

public section

namespace TauCeti

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
  (𝒜 : ZMod 2 → Submodule R A) [GradedAlgebra 𝒜]

/-- The linear endomorphism `proj 0 - proj 1` underlying `gradeInvolution 𝒜`. -/
private def gradeInvolutionLinear : A →ₗ[R] A :=
  GradedAlgebra.proj 𝒜 0 - GradedAlgebra.proj 𝒜 1

private theorem gradeInvolutionLinear_of_mem {i : ZMod 2} {a : A} (ha : a ∈ 𝒜 i) :
    gradeInvolutionLinear 𝒜 a = ((-1 : ℤˣ) ^ i) • a := by
  rcases (by decide : ∀ j : ZMod 2, j = 0 ∨ j = 1) i with rfl | rfl
  · have h₀ : GradedAlgebra.proj 𝒜 0 a = a := by
      rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 ha]
    have h₁ : GradedAlgebra.proj 𝒜 1 a = 0 := by
      rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 ha (by decide)]
    simp [gradeInvolutionLinear, h₀, h₁]
  · have h₀ : GradedAlgebra.proj 𝒜 0 a = 0 := by
      rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 ha (by decide)]
    have h₁ : GradedAlgebra.proj 𝒜 1 a = a := by
      rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 ha]
    simp [gradeInvolutionLinear, h₀, h₁]

private theorem gradeInvolutionLinear_one : gradeInvolutionLinear 𝒜 1 = 1 := by
  simpa using gradeInvolutionLinear_of_mem 𝒜 (SetLike.GradedOne.one_mem (A := 𝒜))

private theorem gradeInvolutionLinear_mul (a b : A) :
    gradeInvolutionLinear 𝒜 (a * b) =
      gradeInvolutionLinear 𝒜 a * gradeInvolutionLinear 𝒜 b := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i a =>
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous j b =>
      rw [gradeInvolutionLinear_of_mem 𝒜 (SetLike.mul_mem_graded a.2 b.2),
        gradeInvolutionLinear_of_mem 𝒜 a.2, gradeInvolutionLinear_of_mem 𝒜 b.2,
        uzpow_add, smul_mul_assoc, mul_smul_comm, mul_smul]
    | add x y hx hy => simp [mul_add, hx, hy]
  | add x y hx hy => simp [add_mul, hx, hy]

private theorem gradeInvolutionLinear_involutive (a : A) :
    gradeInvolutionLinear 𝒜 (gradeInvolutionLinear 𝒜 a) = a := by
  have htwo : ∀ j : ZMod 2, j + j = 0 := by decide
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i a =>
    have hmem : gradeInvolutionLinear 𝒜 a ∈ 𝒜 i := by
      rw [gradeInvolutionLinear_of_mem 𝒜 a.2, Units.smul_def]
      exact DirectSum.Decomposition.zsmul_mem a.2 _
    rw [gradeInvolutionLinear_of_mem 𝒜 hmem, gradeInvolutionLinear_of_mem 𝒜 a.2,
      ← mul_smul, ← uzpow_add, htwo i]
    simp
  | add x y hx hy => simp [hx, hy]

/-- The **grade involution** of an internally `ZMod 2`-graded algebra, fixing `𝒜 0` and negating
`𝒜 1`. -/
def gradeInvolution : A ≃ₐ[R] A :=
  AlgEquiv.ofAlgHom
    (AlgHom.ofLinearMap (gradeInvolutionLinear 𝒜)
      (gradeInvolutionLinear_one 𝒜) (gradeInvolutionLinear_mul 𝒜))
    (AlgHom.ofLinearMap (gradeInvolutionLinear 𝒜)
      (gradeInvolutionLinear_one 𝒜) (gradeInvolutionLinear_mul 𝒜))
    (AlgHom.ext (gradeInvolutionLinear_involutive 𝒜))
    (AlgHom.ext (gradeInvolutionLinear_involutive 𝒜))

/-- The grade involution is the difference of the even and odd projections. -/
theorem gradeInvolution_apply (a : A) :
    gradeInvolution 𝒜 a = GradedAlgebra.proj 𝒜 0 a - GradedAlgebra.proj 𝒜 1 a := (rfl)

variable {𝒜} in
/-- On an element of parity `i`, the grade involution acts by the sign `(-1) ^ i`. -/
theorem gradeInvolution_apply_of_mem {i : ZMod 2} {a : A} (ha : a ∈ 𝒜 i) :
    gradeInvolution 𝒜 a = ((-1 : ℤˣ) ^ i) • a :=
  gradeInvolutionLinear_of_mem 𝒜 ha

variable {𝒜} in
/-- The grade involution fixes every even element. -/
theorem gradeInvolution_apply_of_mem_zero {a : A} (ha : a ∈ 𝒜 0) :
    gradeInvolution 𝒜 a = a := by
  simpa using gradeInvolution_apply_of_mem ha

variable {𝒜} in
/-- The grade involution negates every odd element. -/
theorem gradeInvolution_apply_of_mem_one {a : A} (ha : a ∈ 𝒜 1) :
    gradeInvolution 𝒜 a = -a := by
  simpa using gradeInvolution_apply_of_mem ha

/-- Applying the grade involution twice is the identity. -/
@[simp]
theorem gradeInvolution_gradeInvolution (a : A) :
    gradeInvolution 𝒜 (gradeInvolution 𝒜 a) = a :=
  gradeInvolutionLinear_involutive 𝒜 a

/-- The inverse of the grade involution is the grade involution itself. -/
@[simp]
theorem gradeInvolution_symm : (gradeInvolution 𝒜).symm = gradeInvolution 𝒜 := (rfl)

/-- Self-composition of `gradeInvolution 𝒜` as an algebra equivalence is the identity. -/
@[simp]
theorem gradeInvolution_trans_self :
    (gradeInvolution 𝒜).trans (gradeInvolution 𝒜) = AlgEquiv.refl := by
  ext a
  simp

/-- Self-composition of `gradeInvolution 𝒜` as an algebra homomorphism is the identity. -/
@[simp]
theorem gradeInvolution_comp_self :
    (gradeInvolution 𝒜 : A →ₐ[R] A).comp (gradeInvolution 𝒜) = AlgHom.id R A := by
  ext a
  simp

/-- Self-composition of `(gradeInvolution 𝒜).toLinearEquiv` is the identity linear equivalence. -/
@[simp]
theorem gradeInvolution_toLinearEquiv_trans_self :
    (gradeInvolution 𝒜).toLinearEquiv.trans (gradeInvolution 𝒜).toLinearEquiv =
      LinearEquiv.refl R A := by
  ext a
  simp

-- Not `@[simp]`: `LinearEquiv.comp_coe` rewrites the LHS to
-- `↑((gradeInvolution 𝒜).toLinearEquiv.trans (gradeInvolution 𝒜).toLinearEquiv)`, which `simp`
-- then closes via `gradeInvolution_toLinearEquiv_trans_self`.
/-- Self-composition of `gradeInvolution 𝒜` as a linear map is the identity. -/
theorem gradeInvolution_toLinearMap_comp_self :
    (gradeInvolution 𝒜).toLinearMap ∘ₗ (gradeInvolution 𝒜).toLinearMap = LinearMap.id := by
  simp

variable {𝒜} in
/-- The grade involution preserves each homogeneous piece. -/
theorem gradeInvolution_mem {i : ZMod 2} {a : A} (ha : a ∈ 𝒜 i) :
    gradeInvolution 𝒜 a ∈ 𝒜 i := by
  rw [gradeInvolution_apply_of_mem ha, Units.smul_def]
  exact DirectSum.Decomposition.zsmul_mem ha _

variable {𝒜} in
/-- Membership in each parity piece is invariant under the grade involution. -/
@[simp]
theorem gradeInvolution_mem_iff {i : ZMod 2} {a : A} :
    gradeInvolution 𝒜 a ∈ 𝒜 i ↔ a ∈ 𝒜 i :=
  ⟨fun h ↦ gradeInvolution_gradeInvolution 𝒜 a ▸ gradeInvolution_mem h, gradeInvolution_mem⟩

/-- The grade involution has degree zero. -/
theorem isHomogeneous_gradeInvolution :
    LinearMap.IsHomogeneous (gradeInvolution 𝒜).toLinearMap 𝒜 𝒜 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ ha ↦ by
    simpa only [add_zero, AlgEquiv.toLinearMap_apply] using gradeInvolution_mem ha

/-- On the parity-`i` component of `a`, the grade involution scales by `(-1) ^ i`. -/
@[simp]
theorem decompose_gradeInvolution (a : A) (i : ZMod 2) :
    (DirectSum.decompose 𝒜 (gradeInvolution 𝒜 a) i : A) =
      ((-1 : ℤˣ) ^ i) • (DirectSum.decompose 𝒜 a i : A) := by
  have h := DirectSum.map_decompose_shift 𝒜 𝒜 (gradeInvolution 𝒜).toAddMonoidHom id
    Function.injective_id (fun j x hx ↦ gradeInvolution_mem hx) i a
  change gradeInvolution 𝒜 (DirectSum.decompose 𝒜 a i : A) =
    (DirectSum.decompose 𝒜 (gradeInvolution 𝒜 a) i : A) at h
  rw [← h, gradeInvolution_apply_of_mem (DirectSum.decompose 𝒜 a i).2]

-- Not `@[simp]`: `GradedAlgebra.proj_apply` is `@[simp]`, so `simp` normalizes the LHS via
-- `decompose_gradeInvolution`.
/-- The parity-`i` projection of `gradeInvolution 𝒜 a` is `(-1) ^ i` times `proj 𝒜 i a`. -/
theorem proj_gradeInvolution (i : ZMod 2) (a : A) :
    GradedAlgebra.proj 𝒜 i (gradeInvolution 𝒜 a) = ((-1 : ℤˣ) ^ i) • GradedAlgebra.proj 𝒜 i a := by
  simp

/-- Composing the parity-`i` projection with `gradeInvolution 𝒜` scales by `(-1) ^ i`. -/
@[simp]
theorem proj_comp_gradeInvolution (i : ZMod 2) :
    GradedAlgebra.proj 𝒜 i ∘ₗ (gradeInvolution 𝒜).toLinearMap =
      ((-1 : ℤˣ) ^ i) • GradedAlgebra.proj 𝒜 i := by
  ext a
  simp [Units.smul_def]

/-- Composing `gradeInvolution 𝒜` with the parity-`i` projection scales by `(-1) ^ i`. -/
@[simp]
theorem gradeInvolution_comp_proj (i : ZMod 2) :
    (gradeInvolution 𝒜).toLinearMap ∘ₗ GradedAlgebra.proj 𝒜 i =
      ((-1 : ℤˣ) ^ i) • GradedAlgebra.proj 𝒜 i := by
  ext a
  simp [gradeInvolution_apply_of_mem (DirectSum.decompose 𝒜 a i).2, Units.smul_def]

/-- A parity-homogeneous linear map of degree `j` intertwines the grade involutions up to the sign
`(-1) ^ j`. -/
theorem LinearMap.IsHomogeneous.gradeInvolution_apply
    {R₁ R₂ S A B : Type*} [CommSemiring R₁] [CommSemiring R₂] [Semiring S]
    [Ring A] [Ring B] [Algebra R₁ A] [Algebra R₂ B] [Module S A] [Module S B]
    {𝒜 : ZMod 2 → Submodule R₁ A} {ℬ : ZMod 2 → Submodule R₂ B}
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] {f : A →ₗ[S] B} {j : ZMod 2}
    (hf : LinearMap.IsHomogeneous f 𝒜 ℬ j) (a : A) :
    gradeInvolution ℬ (f a) = ((-1 : ℤˣ) ^ j) • f (gradeInvolution 𝒜 a) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i a =>
    rw [gradeInvolution_apply_of_mem (hf.map_mem a.2), gradeInvolution_apply_of_mem a.2,
      uzpow_add, mul_comm, mul_smul]
    congr 1
    simp only [Units.smul_def, map_zsmul]
  | add x y hx hy => simp [hx, hy, smul_add]

end TauCeti
