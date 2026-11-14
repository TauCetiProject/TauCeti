/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Isometries moving every vector to an orthogonal one

A finite-dimensional real inner product space of even dimension `2m` has a linear isometry `J`
with `⟪J x, x⟫ = 0` for every `x` (`exists_linearIsometryEquiv_inner_map_self_eq_zero`). In an
orthonormal basis `e₁, …, e_m, f₁, …, f_m` it sends `e_i` to `f_i` and `f_i` to `-e_i`, so it reads
`(x, y) ↦ (-y, x)` in the coordinates of `ℝᵐ × ℝᵐ`; it is the multiplication by `i` of a complex
structure on `ℝ²ᵐ` compatible with the inner product.

Restricted to the unit sphere, `J` is a continuous tangent vector field of norm one. So
odd-dimensional spheres carry nowhere-vanishing tangent fields, which is the converse of the hairy
ball theorem.
-/

public section

noncomputable section

open Module
open scoped InnerProductSpace

namespace EuclideanSpace

variable {ι : Type*}

/-- The linear map `(x, y) ↦ (-y, x)` of `ℝ^ι × ℝ^ι`, written on `EuclideanSpace ℝ (ι ⊕ ι)`. -/
private def negSwap : EuclideanSpace ℝ (ι ⊕ ι) →ₗ[ℝ] EuclideanSpace ℝ (ι ⊕ ι) where
  toFun z := WithLp.toLp 2 (Sum.elim (fun i ↦ -z (.inr i)) fun i ↦ z (.inl i))
  map_add' z z' := by
    ext (i | i) <;> simp [add_comm]
  map_smul' c z := by
    ext (i | i) <;> simp

private theorem negSwap_apply_inl (z : EuclideanSpace ℝ (ι ⊕ ι)) (i : ι) :
    negSwap z (.inl i) = -z (.inr i) := (rfl)

private theorem negSwap_apply_inr (z : EuclideanSpace ℝ (ι ⊕ ι)) (i : ι) :
    negSwap z (.inr i) = z (.inl i) := (rfl)

private theorem inner_negSwap_self [Fintype ι] (z : EuclideanSpace ℝ (ι ⊕ ι)) :
    ⟪negSwap z, z⟫_ℝ = 0 := by
  simp only [PiLp.inner_apply, Fintype.sum_sum_type, negSwap_apply_inl, negSwap_apply_inr,
    RCLike.inner_apply, conj_trivial, mul_neg, Finset.sum_neg_distrib, mul_comm]
  exact neg_add_cancel _

private theorem norm_negSwap [Fintype ι] (z : EuclideanSpace ℝ (ι ⊕ ι)) :
    ‖negSwap z‖ = ‖z‖ := by
  simp only [EuclideanSpace.norm_eq, Fintype.sum_sum_type, negSwap_apply_inl, negSwap_apply_inr,
    norm_neg, add_comm]

end EuclideanSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- An even-dimensional real inner product space has a linear isometry `J` moving every vector to
an orthogonal one, `⟪J x, x⟫ = 0`: in an orthonormal basis `e₁, …, e_m, f₁, …, f_m` it sends `e_i`
to `f_i` and `f_i` to `-e_i`. -/
theorem exists_linearIsometryEquiv_inner_map_self_eq_zero (h : Even (finrank ℝ E)) :
    ∃ J : E ≃ₗᵢ[ℝ] E, ∀ x, ⟪J x, x⟫_ℝ = 0 := by
  obtain ⟨m, hm⟩ := h
  let b := (stdOrthonormalBasis ℝ E).reindex ((finCongr hm).trans finSumFinEquiv.symm)
  let K : EuclideanSpace ℝ (Fin m ⊕ Fin m) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m ⊕ Fin m) :=
    ⟨EuclideanSpace.negSwap, EuclideanSpace.norm_negSwap⟩
  refine ⟨b.repr.trans ((K.toLinearIsometryEquiv rfl).trans b.repr.symm), fun x ↦ ?_⟩
  rw [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply,
    ← b.repr.inner_map_map, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometry.coe_toLinearIsometryEquiv]
  exact EuclideanSpace.inner_negSwap_self _

end TauCeti
