/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Realizations of possibly singular Cartan matrices

A `TauCeti.CartanRealization A H` consists of independent simple coroots in `H` and independent
simple roots in its dual, paired by `A`. No invertibility or finite-type hypothesis is imposed
on the matrix. The convention is that rows index coroots and columns index roots.

We prove the sharp dimension bound, construct a realization attaining it, and describe the
Cartan center, including its intersection with the coroot span. The ambient space is arbitrary,
so these results apply to rational realizations and to realizations over other fields alike.
Minimal realizations are constructed by adjoining a complement to the transpose matrix's image.

The mathematical source is V. G. Kac, *Infinite-dimensional Lie algebras*, third edition,
§1.1 (realizations and Proposition 1.1) and Proposition 1.6 (the Cartan center).
-/

public section

open Module
open scoped Matrix

namespace TauCeti

/-- A realization of a matrix, with independent roots and coroots in the full ambient space.
For an integral Cartan matrix over a characteristic-zero field, use its entrywise cast.
Neither family is required to span the ambient space. -/
structure CartanRealization {I K : Type*} [Field K] (A : Matrix I I K)
    (H : Type*) [AddCommGroup H] [Module K H] where
  /-- The simple coroots. -/
  coroot : I → H
  /-- The simple roots, viewed as linear functionals. -/
  root : I → Module.Dual K H
  /-- Coroots remain independent even when the matrix is singular. -/
  coroot_linearIndependent : LinearIndependent K coroot
  /-- Roots remain independent in the dual of the full realization. -/
  root_linearIndependent : LinearIndependent K root
  /-- Rows are coroots and columns are roots. -/
  root_coroot : ∀ i j, root j (coroot i) = A i j

namespace CartanRealization

variable {I K H : Type*} [Fintype I] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix I I K} (R : CartanRealization A H)

attribute [simp] root_coroot

omit [Fintype I] in
/-- A realization is determined by its roots and coroots. -/
@[ext]
theorem ext {S : CartanRealization A H} (hc : ∀ i, R.coroot i = S.coroot i)
    (hr : ∀ i, R.root i = S.root i) : R = S := by
  cases R
  cases S
  congr <;> exact funext (by assumption)

/-- The embedding of coroot coefficients into the ambient space. -/
noncomputable def corootMap : (I → K) →ₗ[K] H :=
  Fintype.linearCombination K R.coroot

/-- A coroot coefficient vector represents the corresponding linear combination. -/
theorem corootMap_apply (c : I → K) : R.corootMap c = ∑ i, c i • R.coroot i := (rfl)

/-- A single coefficient gives the corresponding multiple of a simple coroot. -/
@[simp]
theorem corootMap_single [DecidableEq I] (i : I) (c : K) :
    R.corootMap (Pi.single i c) = c • R.coroot i :=
  Fintype.linearCombination_apply_single K R.coroot i c

/-- Coroot coordinates are unique in the full realization. -/
theorem corootMap_injective : Function.Injective R.corootMap :=
  linearIndependent_iff_injective_fintypeLinearCombination.mp R.coroot_linearIndependent

/-- Evaluation against all the simple roots. -/
def rootEvaluation : H →ₗ[K] (I → K) := LinearMap.pi R.root

omit [Fintype I] in
@[simp]
theorem rootEvaluation_apply (h : H) (i : I) : R.rootEvaluation h i = R.root i h := (rfl)

/-- Restricting root evaluation to the coroot span gives the transpose of the Cartan matrix. -/
@[simp]
theorem rootEvaluation_corootMap (c : I → K) :
    R.rootEvaluation (R.corootMap c) = A.transpose *ᵥ c := by
  ext j
  simp [corootMap_apply, Matrix.mulVec, dotProduct, mul_comm]

/-- The span of the simple coroots, as an embedded coordinate space. -/
def corootSpan : Submodule K H := Submodule.span K (Set.range R.coroot)

/-- The coroot embedding has image the coroot span. -/
theorem range_corootMap : LinearMap.range R.corootMap = R.corootSpan :=
  Fintype.range_linearCombination K R.coroot

/-- Membership in the coroot span is equivalent to having coroot coordinates. -/
@[simp]
theorem mem_corootSpan_iff (h : H) : h ∈ R.corootSpan ↔ ∃ c, R.corootMap c = h := by
  rw [← R.range_corootMap, LinearMap.mem_range]

/-- The Cartan center consists of all vectors annihilated by the simple roots, not just those
in the coroot span. -/
def cartanCenter : Submodule K H := LinearMap.ker R.rootEvaluation

omit [Fintype I] in
@[simp]
theorem mem_cartanCenter_iff (h : H) : h ∈ R.cartanCenter ↔ ∀ i, R.root i h = 0 := by
  simp [cartanCenter, LinearMap.mem_ker, funext_iff]

/-- In coroot coordinates the centrality equations are the left-kernel equations for `A`. -/
theorem corootMap_mem_cartanCenter_iff (c : I → K) :
    R.corootMap c ∈ R.cartanCenter ↔ A.transpose *ᵥ c = 0 := by
  rw [cartanCenter, LinearMap.mem_ker, rootEvaluation_corootMap]

/-- The intersection of the Cartan center and the coroot span is exactly the image of the
left kernel of the matrix under the coroot embedding. -/
theorem cartanCenter_inf_corootSpan :
    R.cartanCenter ⊓ R.corootSpan = (LinearMap.ker A.transpose.mulVecLin).map R.corootMap := by
  rw [← R.range_corootMap]
  ext h
  simp only [Submodule.mem_inf, LinearMap.mem_range, Submodule.mem_map, LinearMap.mem_ker,
    Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨hh, c, rfl⟩
    exact ⟨c, (R.corootMap_mem_cartanCenter_iff c).mp hh, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨(R.corootMap_mem_cartanCenter_iff c).mpr hc, c, rfl⟩

omit [Fintype I] in
private theorem linearIndependent_root_coordinates {J : Type*} [Finite J]
    (b : Basis J K H) : LinearIndependent K (fun i j => R.root i (b j)) := by
  classical
  let := Fintype.ofFinite J
  have heq : (fun i j => R.root i (b j)) = b.dualBasis.equivFun ∘ R.root := by
    ext i j
    simp [Basis.dualBasis_equivFun]
  rw [heq]
  exact R.root_linearIndependent.map' b.dualBasis.equivFun.toLinearMap
    (LinearMap.ker_eq_bot.mpr b.dualBasis.equivFun.injective)

section FiniteDimensional

variable [FiniteDimensional K H]

omit [Fintype I] in
/-- Root evaluation is onto: the full realization retains the directions that a singular
Cartan matrix cannot detect on the coroot span. -/
theorem rootEvaluation_surjective : Function.Surjective R.rootEvaluation := by
  classical
  let := Fintype.ofFinite (Basis.ofVectorSpaceIndex K H)
  let b := Basis.ofVectorSpace K H
  let M : Matrix I (Basis.ofVectorSpaceIndex K H) K := fun i j => R.root i (b j)
  have hM : LinearIndependent K M.row := R.linearIndependent_root_coordinates b
  intro c
  obtain ⟨x, hx⟩ := hM.mulVec_surjective c
  refine ⟨b.equivFun.symm x, ?_⟩
  ext i
  simpa [M, Matrix.mulVec, dotProduct, Basis.equivFun_symm_apply, mul_comm] using
    congrFun hx i

omit [FiniteDimensional K H] in
/-- The dimension of the coroot span equals the number of simple coroots. -/
@[simp]
theorem finrank_corootSpan : finrank K R.corootSpan = Fintype.card I := by
  rw [← R.range_corootMap, LinearMap.finrank_range_of_inj R.corootMap_injective,
    Module.finrank_fintype_fun_eq_card]

/-- The center has codimension equal to the number of simple roots. -/
theorem finrank_cartanCenter_add_card :
    finrank K R.cartanCenter + Fintype.card I = finrank K H := by
  have h := R.rootEvaluation.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr R.rootEvaluation_surjective, finrank_top,
    Module.finrank_fintype_fun_eq_card] at h
  rw [cartanCenter, add_comm]
  exact h

include R

/-- A realization has dimension at least twice the number of nodes minus the matrix rank.
The addition form avoids truncated subtraction and applies in every characteristic. -/
theorem two_mul_card_le_rank_add_finrank :
    2 * Fintype.card I ≤ A.rank + finrank K H := by
  classical
  let := Fintype.ofFinite (Basis.ofVectorSpaceIndex K H)
  let b := Basis.ofVectorSpace K H
  let B : Matrix I (Basis.ofVectorSpaceIndex K H) K := fun i j => R.root i (b j)
  let C : Matrix (Basis.ofVectorSpaceIndex K H) I K := fun j i => b.equivFun (R.coroot i) j
  have hB : B.rank = Fintype.card I :=
    (R.linearIndependent_root_coordinates b).rank_matrix
  have hC : C.rank = Fintype.card I := by
    rw [← Matrix.rank_transpose]
    apply LinearIndependent.rank_matrix
    exact R.coroot_linearIndependent.map' b.equivFun.toLinearMap
      (LinearMap.ker_eq_bot.mpr b.equivFun.injective)
  have hBC : B * C = A.transpose := by
    ext i j
    calc
      (B * C) i j = R.root i (∑ k, b.equivFun (R.coroot j) k • b k) := by
        rw [Matrix.mul_apply]
        simp only [B, C, map_sum, map_smul, smul_eq_mul, mul_comm]
      _ = A j i := by rw [b.sum_equivFun, R.root_coroot]
  have h := Matrix.rank_mul_ge B C
  rw [hB, hC, hBC, Matrix.rank_transpose, ← finrank_eq_card_basis b] at h
  simpa [two_mul] using h

/-- The usual subtraction form of the dimension bound for a realization. -/
theorem two_mul_card_sub_rank_le_finrank :
    2 * Fintype.card I - A.rank ≤ finrank K H := by
  have := R.two_mul_card_le_rank_add_finrank
  omega

end FiniteDimensional

section Transport

variable {H' : Type*} [AddCommGroup H'] [Module K H']

omit [Fintype I] in
/-- Transport a realization along a linear equivalence of ambient spaces. -/
noncomputable def map (e : H ≃ₗ[K] H') : CartanRealization A H' where
  coroot := e ∘ R.coroot
  root := e.symm.toLinearMap.dualMap ∘ R.root
  coroot_linearIndependent := R.coroot_linearIndependent.map' e.toLinearMap
    (LinearMap.ker_eq_bot.mpr e.injective)
  root_linearIndependent := R.root_linearIndependent.map' e.symm.toLinearMap.dualMap
    (LinearMap.ker_eq_bot.mpr (LinearMap.dualMap_injective_of_surjective e.symm.surjective))
  root_coroot i j := by simp

omit [Fintype I] in
@[simp]
theorem map_coroot (e : H ≃ₗ[K] H') (i : I) : (R.map e).coroot i = e (R.coroot i) := (rfl)

omit [Fintype I] in
@[simp]
theorem map_root_apply (e : H ≃ₗ[K] H') (i : I) (h : H') :
    (R.map e).root i h = R.root i (e.symm h) := (rfl)

end Transport

section Construction

variable (A) (Z : Submodule K (I → K))

/-- Realize a matrix by adjoining a supplement to its transpose's image. The first factor
contains the independent coroots; the second supplies the missing root evaluations. -/
noncomputable def ofSupplement
    (hZ : LinearMap.range A.transpose.mulVecLin ⊔ Z = ⊤) :
    CartanRealization A ((I → K) × Z) := by
  classical
  have hsurj : Function.Surjective (A.transpose.mulVecLin.coprod Z.subtype) := by
    rwa [← LinearMap.range_eq_top, LinearMap.range_coprod, Submodule.range_subtype]
  exact
    { coroot := LinearMap.inl K (I → K) Z ∘ Pi.basisFun K I
      root := (A.transpose.mulVecLin.coprod Z.subtype).dualMap ∘ (Pi.basisFun K I).dualBasis
      coroot_linearIndependent := (Pi.basisFun K I).linearIndependent.map'
        (LinearMap.inl K (I → K) Z) (LinearMap.ker_eq_bot.mpr LinearMap.inl_injective)
      root_linearIndependent := (Pi.basisFun K I).dualBasis.linearIndependent.map'
        (A.transpose.mulVecLin.coprod Z.subtype).dualMap
        (LinearMap.ker_eq_bot.mpr (LinearMap.dualMap_injective_of_surjective hsurj))
      root_coroot i j := by simp }

@[simp]
theorem ofSupplement_coroot (hZ : LinearMap.range A.transpose.mulVecLin ⊔ Z = ⊤) (i : I) :
    (ofSupplement A Z hZ).coroot i = ((Pi.basisFun K I) i, 0) := (rfl)

@[simp]
theorem ofSupplement_root_apply (hZ : LinearMap.range A.transpose.mulVecLin ⊔ Z = ⊤)
    (i : I) (h : (I → K) × Z) :
    (ofSupplement A Z hZ).root i h = (A.transpose *ᵥ h.1) i + (h.2 : I → K) i := by
  simp [ofSupplement, Matrix.mulVec_transpose]

end Construction

end CartanRealization
end TauCeti

namespace Matrix

/-- Every square matrix admits a realization attaining the dimension bound, in a coordinate
space. In particular this constructs minimal rational realizations of singular Cartan matrices. -/
theorem nonempty_cartanRealization {I K : Type*} [Fintype I] [Field K] (A : Matrix I I K) :
    Nonempty (TauCeti.CartanRealization A (Fin (2 * Fintype.card I - A.rank) → K)) := by
  obtain ⟨Z, hZ⟩ := Submodule.exists_isCompl (LinearMap.range A.transpose.mulVecLin)
  have hdim : finrank K ((I → K) × Z) = 2 * Fintype.card I - A.rank := by
    have h := Submodule.finrank_add_eq_of_isCompl hZ
    rw [← Matrix.rank, Matrix.rank_transpose, Module.finrank_fintype_fun_eq_card] at h
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
    omega
  let e : ((I → K) × Z) ≃ₗ[K] (Fin (2 * Fintype.card I - A.rank) → K) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hdim)
  exact ⟨(TauCeti.CartanRealization.ofSupplement A Z hZ.sup_eq_top).map e⟩

end Matrix
