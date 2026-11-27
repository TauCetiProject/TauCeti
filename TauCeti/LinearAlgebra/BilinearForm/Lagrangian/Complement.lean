/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Isotropic
public import TauCeti.LinearAlgebra.BilinearForm.QuotientDual
import TauCeti.LinearAlgebra.Basis.Basic
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.Prod

/-!
# Lagrangian complements

Given a Lagrangian `L` in a finite-dimensional symplectic space, a complementary Lagrangian
provides the second half of a polarization. Over every field,
`LinearMap.BilinForm.IsAlt.exists_lagrangianComplement` obtains one from a symplectic basis
extending a basis of `L`.

When two is invertible, `LinearMap.BilinForm.lagrangianComplement` constructs a Lagrangian
canonically from a specified vector-space complement `V`. The restricted perfect pairing
identifies `L` with the dual of `V`. Under this identification the correction `A : V →ₗ[K] L`
sends `v` to the functional `w ↦ -½ B(v, w)`. Its graph in the ambient space consists
of the vectors `v + A v`. The two cross terms in their pairing cancel the restriction of
`B` to `V`, and an isotropic initial complement is fixed.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, §8.2, Proposition 8.2, for the
  graph construction over the reals.
-/

public noncomputable section

open Module Submodule
open LinearMap (BilinForm)

namespace LinearMap.BilinForm

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {B : BilinForm K W} {L V : Submodule K W}

/-- Every Lagrangian in a finite-dimensional symplectic space admits a Lagrangian complement,
including in characteristic two. -/
theorem IsAlt.exists_lagrangianComplement (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hL : L = B.orthogonal L) :
    ∃ Y : Submodule K W, IsCompl L Y ∧ Y = B.orthogonal Y := by
  classical
  let e := finBasis K L
  obtain ⟨b, hb, he⟩ := hB.exists_basis_toMatrix_eq_J_inl_eq hnd e hL
  let Y := span K (Set.range fun i ↦ b (Sum.inr i))
  have hc : IsCompl L Y := by
    simpa [Y, ← Set.range_comp, Function.comp_def, he] using
      b.linearIndependent.isCompl_span_image b.span_eq Set.isCompl_range_inl_range_inr
  -- The lower right block of the symplectic Gram matrix vanishes on the generators of Y.
  refine ⟨Y, hc, eq_orthogonal_of_isCompl_of_le_orthogonal hnd hL hc ?_⟩
  intro y hy
  refine mem_orthogonal_iff.mpr fun x hx ↦ apply_eq_zero_of_mem_span ?_ hx hy
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  simpa [toMatrix_apply, Matrix.J] using congrFun (congrFun hb (.inr i)) (.inr j)

section Graph

variable [Invertible (2 : K)] (B) (hnd : B.Nondegenerate) (hL : B.orthogonal L = L)
  (hc : IsCompl L V)

/-- The linear correction sending `v` to the element of `L` that pairs with `w ∈ V` as
`-½ B(v, w)`. -/
def lagrangianCorrection : V →ₗ[K] L :=
  let := B.isPerfPair_domRestrict₁₂_of_isCompl_orthogonal hnd (hL.symm ▸ hc)
  (B.domRestrict₁₂ L V).toPerfPair.symm.toLinearMap ∘ₗ (-(⅟(2 : K)) • B.restrict V)

/-- Pairing the correction with a vector in the initial complement gives the negative half-form. -/
@[simp]
theorem apply_lagrangianCorrection (v w : V) :
    B (B.lagrangianCorrection hnd hL hc v) w = -(⅟(2 : K)) * B v w := by
  let := B.isPerfPair_domRestrict₁₂_of_isCompl_orthogonal hnd (hL.symm ▸ hc)
  exact DFunLike.congr_fun ((B.domRestrict₁₂ L V).apply_symm_toPerfPair_self
    ((-(⅟(2 : K)) • B.restrict V) v)) w

/-- The negative half-form determines the correction map uniquely. -/
theorem eq_lagrangianCorrection_iff (A : V →ₗ[K] L) :
    A = B.lagrangianCorrection hnd hL hc ↔ ∀ v w : V, B (A v) w = -(⅟(2 : K)) * B v w := by
  refine ⟨fun h ↦ h ▸ B.apply_lagrangianCorrection hnd hL hc, fun h ↦ ?_⟩
  let := B.isPerfPair_domRestrict₁₂_of_isCompl_orthogonal hnd (hL.symm ▸ hc)
  refine LinearMap.ext fun v ↦ (B.domRestrict₁₂ L V).toPerfPair.injective ?_
  refine LinearMap.ext fun w ↦ ?_
  simpa [domRestrict₁₂_apply] using (h v w).trans (B.apply_lagrangianCorrection hnd hL hc v w).symm

/-- The graph of the correction in the splitting `W = V ⊕ L`. For an alternating form it is
a Lagrangian complement to `L`. -/
def lagrangianComplement : Submodule K W :=
  (B.lagrangianCorrection hnd hL hc).graph.map (V.prodEquivOfIsCompl L hc.symm).toLinearMap

/-- A vector is in the corrected complement exactly when it is of the form `v + A v`. -/
theorem mem_lagrangianComplement_iff {z : W} :
    z ∈ B.lagrangianComplement hnd hL hc ↔
      ∃ v : V, (v : W) + B.lagrangianCorrection hnd hL hc v = z := by
  simp [lagrangianComplement, Submodule.mem_map, LinearMap.mem_graph_iff, Prod.exists]

/-- The corrected graph is a vector-space complement to the prescribed Lagrangian. -/
@[simp]
theorem isCompl_lagrangianComplement : IsCompl L (B.lagrangianComplement hnd hL hc) := by
  have hk : (ker (LinearMap.fst K V L)).map (V.prodEquivOfIsCompl L hc.symm).toLinearMap = L := by
    ext z
    simp
  simpa only [lagrangianComplement, hk] using
    isCompl_map (V.prodEquivOfIsCompl L hc.symm)
      (B.lagrangianCorrection hnd hL hc).isCompl_graph_ker_fst.symm

/-- For an alternating form, the corrected graph equals its symplectic orthogonal. -/
theorem lagrangianComplement_eq_orthogonal (hB : B.IsAlt) :
    B.lagrangianComplement hnd hL hc = B.orthogonal (B.lagrangianComplement hnd hL hc) := by
  apply eq_orthogonal_of_isCompl_of_le_orthogonal hnd hL.symm
    (B.isCompl_lagrangianComplement hnd hL hc)
  intro y hy
  refine mem_orthogonal_iff.mpr fun x hx ↦ ?_
  obtain ⟨v, rfl⟩ := (B.mem_lagrangianComplement_iff hnd hL hc).mp hx
  obtain ⟨w, rfl⟩ := (B.mem_lagrangianComplement_iff hnd hL hc).mp hy
  set A := B.lagrangianCorrection hnd hL hc
  have hAA : B (A v) (A w) = 0 :=
    mem_orthogonal_iff.mp (hL.ge (A w).property) _ (A v).property
  have hvw : B v (A w) = -(⅟(2 : K)) * B v w := by
    rw [← hB.neg_eq, B.apply_lagrangianCorrection, ← hB.neg_eq (v : W) (w : W)]
    ring
  simp only [map_add, LinearMap.add_apply, hAA, hvw, add_zero]
  rw [B.apply_lagrangianCorrection hnd hL hc v w]
  calc
    _ = (1 - (⅟(2 : K) + ⅟(2 : K))) * B v w := by ring
    _ = 0 := by rw [invOf_two_add_invOf_two, sub_self, zero_mul]

/-- An isotropic initial complement is fixed by the graph construction. -/
@[simp]
theorem lagrangianComplement_eq_self_of_le_orthogonal (hV : V ≤ B.orthogonal V) :
    B.lagrangianComplement hnd hL hc = V := by
  have hzero : (0 : V →ₗ[K] L) = B.lagrangianCorrection hnd hL hc :=
    (B.eq_lagrangianCorrection_iff hnd hL hc 0).2 fun v w ↦ by
      simp [mem_orthogonal_iff.mp (hV w.property) _ v.property]
  ext z
  simp [B.mem_lagrangianComplement_iff hnd hL hc, ← hzero]

end Graph

end LinearMap.BilinForm
