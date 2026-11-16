/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Nondegeneracy of the real inner product

The real inner product `innerₗ E` is a nondegenerate bilinear form on `E`
(`TauCeti.nondegenerate_inner`): a vector orthogonal to every vector is orthogonal to itself, hence
zero. This is the hypothesis under which Mathlib's bilinear-form constructions, such as the dual
basis `LinearMap.BilinForm.dualBasis`, apply to the inner product. For any endomorphism `A`,
the bilinear form `innerₗ E ∘ₗ A` is symmetric iff `A` is symmetric
(`TauCeti.isSymm_innerₗ_comp_iff`). In finite dimension `innerₗ E` is moreover a perfect pairing
(`TauCeti.bijective_innerₗ`), as Mathlib's `exteriorPower.hodgeStar` requires of its bilinear form,
and yields the Riesz linear equivalence `TauCeti.bilinFormEquivEnd` identifying bilinear forms on
`E` with endomorphisms of `E` via `⟪bilinFormEquivEnd E B u, v⟫ = B u v` and carrying symmetric
forms to symmetric endomorphisms (`TauCeti.isSymmetric_bilinFormEquivEnd_iff`). Its pullback along
an injective linear map, such as the metric induced by an immersion, is again nondegenerate
(`TauCeti.nondegenerate_inner_comp`), so a vector is determined by its pairings with it
(`TauCeti.eq_of_forall_inner_comp`).

The dual basis of a basis `b` for the inner product pairs with a vector to give its coordinates
in `b` (`Module.Basis.inner_dualBasis_left`), and it is obtained from `b` by the inverse of the Gram
matrix (`Module.Basis.dualBasis_innerₗ_eq_sum`). In a coordinate frame of a Riemannian metric, these
are the coordinate covectors `dxⁱ` with their musical isomorphism `gⁱʲ ∂ⱼ`.
-/

public section

open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real inner product is a nondegenerate bilinear form. -/
theorem nondegenerate_inner : (innerₗ E).Nondegenerate :=
  ⟨fun x hx ↦ inner_self_eq_zero.mp (hx x), fun y hy ↦ inner_self_eq_zero.mp (hy y)⟩

/-- The bilinear form `innerₗ E ∘ₗ A` is symmetric iff the endomorphism `A` is symmetric. -/
@[simp]
theorem isSymm_innerₗ_comp_iff {A : Module.End ℝ E} :
    LinearMap.BilinForm.IsSymm (innerₗ E ∘ₗ A) ↔ A.IsSymmetric :=
  ⟨fun h u v ↦ by simpa [real_inner_comm] using h.eq u v,
    fun h ↦ ⟨fun u v ↦ by simp [h u v, real_inner_comm]⟩⟩

/-- In finite dimension the real inner product is a perfect pairing: `v ↦ ⟪v, ·⟫` is a bijection
onto the dual. -/
theorem bijective_innerₗ [FiniteDimensional ℝ E] : Function.Bijective (innerₗ E) := by
  convert (LinearMap.BilinForm.toDual (innerₗ E) nondegenerate_inner).bijective using 1
  ext v w
  exact (LinearMap.BilinForm.toDual_def nondegenerate_inner).symm

variable (E) in
/-- **Riesz equivalence between bilinear forms and endomorphisms** on a finite-dimensional real
inner product space: `bilinFormEquivEnd E B` is the unique endomorphism `A` of `E` satisfying
`⟪A u, v⟫ = B u v`, and its inverse sends `A` to `innerₗ E ∘ₗ A`. -/
noncomputable def bilinFormEquivEnd [FiniteDimensional ℝ E] :
    LinearMap.BilinForm ℝ E ≃ₗ[ℝ] Module.End ℝ E :=
  (LinearEquiv.refl ℝ E).arrowCongr
    (LinearMap.BilinForm.toDual (innerₗ E) nondegenerate_inner).symm

/-- The inverse of `bilinFormEquivEnd E` sends an endomorphism `A` to `innerₗ E ∘ₗ A`. -/
@[simp]
theorem bilinFormEquivEnd_symm_apply [FiniteDimensional ℝ E] (A : Module.End ℝ E) :
    (bilinFormEquivEnd E).symm A = innerₗ E ∘ₗ A := by
  ext u v
  exact LinearMap.BilinForm.toDual_def (B := innerₗ E) nondegenerate_inner

/-- Pairing `bilinFormEquivEnd E B u` with `v` recovers `B u v`. -/
@[simp]
theorem inner_bilinFormEquivEnd_left [FiniteDimensional ℝ E]
    (B : LinearMap.BilinForm ℝ E) (u v : E) :
    ⟪bilinFormEquivEnd E B u, v⟫ = B u v := by
  rw [← innerₗ_apply_apply]
  exact LinearMap.BilinForm.apply_toDual_symm_apply (hB := nondegenerate_inner) (B u) v

/-- Composing `innerₗ E` with `bilinFormEquivEnd E B` recovers `B`. -/
@[simp]
theorem innerₗ_comp_bilinFormEquivEnd [FiniteDimensional ℝ E]
    (B : LinearMap.BilinForm ℝ E) :
    innerₗ E ∘ₗ bilinFormEquivEnd E B = B := by
  rw [← bilinFormEquivEnd_symm_apply, LinearEquiv.symm_apply_apply]

/-- `bilinFormEquivEnd E` sends `innerₗ E ∘ₗ A` back to `A`. -/
@[simp]
theorem bilinFormEquivEnd_innerₗ_comp [FiniteDimensional ℝ E] (A : Module.End ℝ E) :
    bilinFormEquivEnd E (innerₗ E ∘ₗ A) = A := by
  rw [← bilinFormEquivEnd_symm_apply, LinearEquiv.apply_symm_apply]

/-- The Riesz endomorphism of the inner product itself is the identity. -/
@[simp]
theorem bilinFormEquivEnd_innerₗ [FiniteDimensional ℝ E] :
    bilinFormEquivEnd E (innerₗ E) = LinearMap.id := by
  simpa using bilinFormEquivEnd_innerₗ_comp (LinearMap.id : Module.End ℝ E)

/-- `bilinFormEquivEnd E B` is uniquely characterized by `⟪A u, v⟫ = B u v`. -/
theorem bilinFormEquivEnd_eq_iff [FiniteDimensional ℝ E]
    (B : LinearMap.BilinForm ℝ E) (A : Module.End ℝ E) :
    bilinFormEquivEnd E B = A ↔ ∀ u v, ⟪A u, v⟫ = B u v :=
  ⟨fun h ↦ h ▸ inner_bilinFormEquivEnd_left B, fun h ↦
    LinearMap.ext fun u ↦ ext_inner_right ℝ fun v ↦ by rw [inner_bilinFormEquivEnd_left, h]⟩

/-- `bilinFormEquivEnd E B` is symmetric iff the bilinear form `B` is symmetric. -/
@[simp]
theorem isSymmetric_bilinFormEquivEnd_iff [FiniteDimensional ℝ E]
    {B : LinearMap.BilinForm ℝ E} :
    (bilinFormEquivEnd E B).IsSymmetric ↔ B.IsSymm := by
  rw [← isSymm_innerₗ_comp_iff, innerₗ_comp_bilinFormEquivEnd]

/-- The real inner product pulled back along an injective linear map is nondegenerate: a vector
`v` with `⟪L v, L w⟫ = 0` for every `w` has `⟪L v, L v⟫ = 0`, so `L v = 0`. -/
theorem nondegenerate_inner_comp {V : Type*} [AddCommGroup V] [Module ℝ V] {L : V →ₗ[ℝ] E}
    (hL : Function.Injective L) : (LinearMap.BilinForm.comp (innerₗ E) L L).Nondegenerate :=
  ⟨fun v hv ↦ hL <| by simpa using hv v, fun w hw ↦ hL <| by simpa using hw w⟩

/-- For an injective linear map `L`, a vector `u` is determined by the pairings `⟪L u, L w⟫` of the
pulled-back inner product. -/
theorem eq_of_forall_inner_comp {V : Type*} [AddCommGroup V] [Module ℝ V] {L : V →ₗ[ℝ] E}
    (hL : Function.Injective L) {u u' : V} (H : ∀ w, ⟪L u, L w⟫ = ⟪L u', L w⟫) : u = u' := by
  rw [← sub_eq_zero]
  refine (nondegenerate_inner_comp hL).1 _ fun w ↦ ?_
  simp [H]

end TauCeti

namespace Module.Basis

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The inner product with the `i`-th vector of the dual basis of `b` is the `i`-th coordinate
in `b`. -/
theorem inner_dualBasis_left {ι : Type*} [DecidableEq ι] [Finite ι] (b : Basis ι ℝ E) (i : ι)
    (v : E) :
    ⟪LinearMap.BilinForm.dualBasis (innerₗ E) nondegenerate_inner b i, v⟫ = b.repr v i := by
  have : innerₗ E (LinearMap.BilinForm.dualBasis (innerₗ E) nondegenerate_inner b i) =
      b.coord i :=
    b.ext fun j ↦ by
      rw [LinearMap.BilinForm.apply_dualBasis_left, coord_apply, repr_self, Finsupp.single_apply]
  simpa using LinearMap.congr_fun this v

/-- **The dual basis through the inverse Gram matrix**: the `i`-th vector of the dual basis of
`b` is `∑ⱼ (G⁻¹)ᵢⱼ bⱼ`, where `G = (⟪bᵢ, bⱼ⟫)` is the Gram matrix of `b`. -/
theorem dualBasis_innerₗ_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E)
    (i : ι) :
    LinearMap.BilinForm.dualBasis (innerₗ E) nondegenerate_inner b i =
      ∑ j, (Matrix.gram ℝ b)⁻¹ i j • b j := by
  have hdet : IsUnit (Matrix.gram ℝ b).det :=
    isUnit_iff_ne_zero.2 (Matrix.det_gram_ne_zero_iff_linearIndependent.2 b.linearIndependent)
  refine InnerProductSpace.ext_inner_right_basis b fun l ↦ ?_
  have h := congr_fun (congr_fun (Matrix.nonsing_inv_mul _ hdet) i) l
  rw [Matrix.mul_apply] at h
  simp only [inner_dualBasis_left, repr_self, Finsupp.single_apply, sum_inner,
    real_inner_smul_left]
  simp only [Matrix.gram_apply, Matrix.one_apply] at h
  rw [h]
  simp [eq_comm]

end Module.Basis
