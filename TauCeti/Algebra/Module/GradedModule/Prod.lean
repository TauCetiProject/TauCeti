/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Module.GradedModule.Internal
public import Mathlib.LinearAlgebra.Prod

/-!
# Products of internally graded modules

The product of two internally graded modules has the componentwise grading. This supplies
the grading on finite biproducts and mapping cones of curved differential graded modules.
-/

public section

open scoped DirectSum

namespace TauCeti.InternalGrading

universe u v w

variable {R : Type u} [Semiring R] {M : Type v} {N : Type w}
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  (G : InternalGrading R M) (H : InternalGrading R N)

private def prodInl (p : ℤ) : G.piece p →ₗ[R] (G.piece p).prod (H.piece p) :=
  LinearMap.codRestrict _ ((LinearMap.inl R M N).comp (G.piece p).subtype)
    (fun x ↦ ⟨x.property, (H.piece p).zero_mem⟩)

private def prodInr (p : ℤ) : H.piece p →ₗ[R] (G.piece p).prod (H.piece p) :=
  LinearMap.codRestrict _ ((LinearMap.inr R M N).comp (H.piece p).subtype)
    (fun x ↦ ⟨(G.piece p).zero_mem, x.property⟩)

private noncomputable def prodDecompose :
    M × N →ₗ[R] ⨁ p, (G.piece p).prod (H.piece p) :=
  (DirectSum.lmap (prodInl G H)).comp
      ((DirectSum.decomposeLinearEquiv G.piece).toLinearMap.comp (LinearMap.fst R M N)) +
    (DirectSum.lmap (prodInr G H)).comp
      ((DirectSum.decomposeLinearEquiv H.piece).toLinearMap.comp (LinearMap.snd R M N))

private theorem prodDecompose_of_mem (p : ℤ) (x : M) (y : N)
    (hx : x ∈ G.piece p) (hy : y ∈ H.piece p) :
    prodDecompose G H (x, y) =
      DirectSum.lof R ℤ (fun q ↦ (G.piece q).prod (H.piece q)) p ⟨(x, y), hx, hy⟩ := by
  simp only [prodDecompose, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearEquiv.coe_toLinearMap]
  rw [DirectSum.decomposeLinearEquiv_apply_coe G.piece p ⟨x, hx⟩,
    DirectSum.decomposeLinearEquiv_apply_coe H.piece p ⟨y, hy⟩,
    DirectSum.lmap_lof, DirectSum.lmap_lof, ← map_add]
  congr 1
  apply Subtype.ext
  -- Reduce the private restricted inclusions and their subtype coercions to pair inclusions.
  change (x, 0) + (0, y) = (x, y)
  simp

private theorem coeLinearMap_comp_prodDecompose :
    (DirectSum.coeLinearMap fun p ↦ (G.piece p).prod (H.piece p)).comp
      (prodDecompose G H) = LinearMap.id := by
  apply LinearMap.prod_ext
  · apply G.linearMap_ext
    intro p x hx
    simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.id_apply]
    rw [prodDecompose_of_mem G H p x 0 hx (H.piece p).zero_mem,
      DirectSum.coeLinearMap_lof]
  · apply H.linearMap_ext
    intro p y hy
    simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.id_apply]
    rw [prodDecompose_of_mem G H p 0 y (G.piece p).zero_mem hy,
      DirectSum.coeLinearMap_lof]

private theorem prodDecompose_comp_coeLinearMap :
    (prodDecompose G H).comp
      (DirectSum.coeLinearMap fun p ↦ (G.piece p).prod (H.piece p)) = LinearMap.id := by
  apply DirectSum.linearMap_ext R
  intro p
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearMap.id_apply]
  exact prodDecompose_of_mem G H p x.1.1 x.1.2 x.2.1 x.2.2

/-- The componentwise internal grading on a product of modules. -/
noncomputable def prod : InternalGrading R (M × N) := by
  letI := DirectSum.Decomposition.ofLinearMap (fun p ↦ (G.piece p).prod (H.piece p))
    (prodDecompose G H)
    (coeLinearMap_comp_prodDecompose G H) (prodDecompose_comp_coeLinearMap G H)
  exact InternalGrading.ofDecomposition fun p ↦ (G.piece p).prod (H.piece p)

/-- The degree-`p` piece of the product is the product of the degree-`p` pieces. -/
@[simp]
theorem prod_piece (p : ℤ) : (G.prod H).piece p = (G.piece p).prod (H.piece p) := by
  simp only [prod, ofDecomposition_piece]

end TauCeti.InternalGrading
