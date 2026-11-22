/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.BilinearForm.Properties
import TauCeti.Analysis.InnerProductSpace.Gram.Basic
import TauCeti.LinearAlgebra.BilinearForm.Basic
import TauCeti.LinearAlgebra.BilinearForm.Dual.Basis
import TauCeti.LinearAlgebra.Matrix.BilinearForm

/-!
# Nondegeneracy of the real inner product

The real inner product `innerₗ E` is a nondegenerate bilinear form on `E`
(`TauCeti.nondegenerate_inner`): a vector orthogonal to every vector is orthogonal to itself, hence
zero. This is the hypothesis under which Mathlib's bilinear-form constructions, such as the dual
basis `LinearMap.BilinForm.dualBasis`, apply to the inner product. In finite dimension it is
moreover a perfect pairing (`TauCeti.bijective_innerₗ`), as Mathlib's `exteriorPower.hodgeStar`
requires of its bilinear form. Its pullback along an injective linear map, such as the metric
induced by an immersion, is again nondegenerate (`TauCeti.nondegenerate_inner_comp`), so a vector
is determined by its pairings with it (`TauCeti.eq_of_forall_inner_comp`). In a one-dimensional
inner product space over `𝕜`, pairing with a nonzero vector is injective in the left argument
(`TauCeti.inner_left_injective_of_finrank_eq_one`).

The dual basis of a basis `b` for the inner product pairs with a vector to give its coordinates
in `b` (`Module.Basis.inner_dualBasis_left`), and it is obtained from `b` by the inverse of the Gram
matrix (`Module.Basis.dualBasis_innerₗ_eq_sum`). In a coordinate frame `∂ᵢ` of a Riemannian metric
`g`, the `i`-th dual basis vector is thus the image `(dxⁱ)♯ = ∑ⱼ gⁱʲ ∂ⱼ` of the coordinate covector
`dxⁱ` under the sharp isomorphism.
-/

public section

open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real inner product is a nondegenerate bilinear form. -/
theorem nondegenerate_inner : (innerₗ E).Nondegenerate :=
  ⟨fun x hx ↦ inner_self_eq_zero.mp (hx x), fun y hy ↦ inner_self_eq_zero.mp (hy y)⟩

/-- A nonzero scalar multiple of the real inner product is nondegenerate. -/
theorem nondegenerate_toBilinForm_smul_innerSL {c : ℝ} (hc : c ≠ 0) :
    (c • innerSL ℝ (E := E)).toBilinForm.Nondegenerate := by
  have hform : (c • innerSL ℝ (E := E)).toBilinForm = c • innerₗ E := by
    ext u v
    simp [innerSL_apply_apply ℝ]
  rw [hform]
  exact (BilinForm.nondegenerate_smul_iff (IsRegular.of_ne_zero hc)).2 nondegenerate_inner

/-- In finite dimension the real inner product is a perfect pairing: `v ↦ ⟪v, ·⟫` is a bijection
onto the dual. -/
theorem bijective_innerₗ [FiniteDimensional ℝ E] : Function.Bijective (innerₗ E) := by
  convert (LinearMap.BilinForm.toDual (innerₗ E) nondegenerate_inner).bijective using 1
  ext v w
  exact (LinearMap.BilinForm.toDual_def nondegenerate_inner).symm

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

open scoped InnerProductSpace in
/-- In a one-dimensional inner product space, the inner product against a nonzero vector is
injective in the left argument. -/
theorem inner_left_injective_of_finrank_eq_one {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] (hn : Module.finrank 𝕜 F = 1) {ν : F} (hν : ν ≠ 0) :
    Function.Injective (fun x => ⟪x, ν⟫_𝕜) := by
  intro x y h
  dsimp only at h
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' ν hν).1 hn (x - y)
  have h0 : ⟪c • ν, ν⟫_𝕜 = 0 := by rw [hc, inner_sub_left, h, sub_self]
  rw [inner_smul_left, mul_eq_zero, map_eq_zero, inner_self_eq_zero] at h0
  exact sub_eq_zero.1 (hc ▸ (h0.resolve_right hν).symm ▸ zero_smul 𝕜 ν)

end TauCeti

namespace Module.Basis

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The inner product with the `i`-th vector of the dual basis of `b` is the `i`-th coordinate
in `b`. -/
@[simp]
theorem inner_dualBasis_left {ι : Type*} [DecidableEq ι] [Finite ι] (b : Basis ι ℝ E) (i : ι)
    (v : E) :
    ⟪LinearMap.BilinForm.dualBasis (innerₗ E) nondegenerate_inner b i, v⟫ = b.repr v i := by
  rw [LinearMap.BilinForm.repr_apply_eq_apply_dualBasis nondegenerate_inner, innerₗ_apply_apply]

/-- **The dual basis through the inverse Gram matrix**: the `i`-th vector of the dual basis of
`b` is `∑ⱼ (G⁻¹)ᵢⱼ bⱼ`, where `G = (⟪bᵢ, bⱼ⟫)` is the Gram matrix of `b`. -/
theorem dualBasis_innerₗ_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E)
    (i : ι) :
    LinearMap.BilinForm.dualBasis (innerₗ E) nondegenerate_inner b i =
      ∑ j, (Matrix.gram ℝ b)⁻¹ i j • b j := by
  rw [LinearMap.BilinForm.dualBasis_apply_eq_sum_inv_toMatrix_smul,
    LinearMap.BilinForm.toMatrix_innerₗ]

end Module.Basis
