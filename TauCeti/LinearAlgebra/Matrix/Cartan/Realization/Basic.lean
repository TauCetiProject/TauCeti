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
on the matrix. The ambient dimension is unconstrained, generalizing Kac's notion of a
realization. For Cartan matrices in Kac's setting, his realizations are exactly the minimal
ones: those attaining `TauCeti.CartanRealization.two_mul_card_le_rank_add_finrank` with equality.
The convention is that rows index coroots and columns index roots.

We prove the sharp dimension bound, construct a realization attaining it, and describe the
Cartan center, including its intersection with the coroot span. The ambient space is arbitrary,
so these results apply to rational realizations and to realizations over other fields alike.
Minimal realizations are constructed by adjoining a complement to the transpose matrix's image.
Restriction to a subspace containing the coroots preserves the realization whenever that subspace
and the Cartan center together span the ambient space.

The mathematical source is V. G. Kac, *Infinite-dimensional Lie algebras*, third edition,
§1.1 (realizations and Proposition 1.1) and Proposition 1.6 (the Cartan center).
-/

public section

open Module
open scoped Matrix

namespace TauCeti

/-- A realization of a matrix, with independent roots and coroots in the full ambient space.
For an integral Cartan matrix over a characteristic-zero field, use its entrywise cast.
Neither family is required to span the ambient space, and its dimension is unconstrained.
This generalizes Kac's notion: in his setting, his realizations are exactly the minimal ones,
attaining `CartanRealization.two_mul_card_le_rank_add_finrank` with equality. -/
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
theorem corootMap_apply (c : I → K) : R.corootMap c = ∑ i, c i • R.coroot i :=
  Fintype.linearCombination_apply K R.coroot c

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

omit [Fintype I] in
/-- The coroot span is the span of the simple coroots. -/
theorem corootSpan_def : R.corootSpan = Submodule.span K (Set.range R.coroot) := (rfl)

/-- The coroot embedding has image the coroot span. -/
theorem range_corootMap : LinearMap.range R.corootMap = R.corootSpan :=
  Fintype.range_linearCombination K R.coroot

omit [Fintype I] in
/-- Every simple coroot belongs to the coroot span. -/
@[simp]
theorem coroot_mem_corootSpan (i : I) : R.coroot i ∈ R.corootSpan :=
  Submodule.subset_span (Set.mem_range_self i)

/-- Every coroot coefficient vector represents a vector in the coroot span. -/
@[simp]
theorem corootMap_mem_corootSpan (c : I → K) : R.corootMap c ∈ R.corootSpan := by
  rw [← R.range_corootMap]
  exact LinearMap.mem_range_self _ c

/-- Membership in the coroot span is equivalent to having coroot coordinates. -/
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
  have hcomp : R.rootEvaluation ∘ₗ R.corootMap = A.transpose.mulVecLin :=
    LinearMap.ext R.rootEvaluation_corootMap
  rw [← hcomp, LinearMap.ker_comp, Submodule.map_comap_eq, R.range_corootMap,
    inf_comm, cartanCenter]

/-- The central part of the coroot span has dimension equal to the nullity of the matrix. -/
theorem finrank_cartanCenter_inf_corootSpan_add_rank :
    finrank K ↥(R.cartanCenter ⊓ R.corootSpan) + A.rank = Fintype.card I := by
  rw [R.cartanCenter_inf_corootSpan,
    ← (Submodule.equivMapOfInjective R.corootMap R.corootMap_injective
      (LinearMap.ker A.transpose.mulVecLin)).finrank_eq]
  have h := A.transpose.mulVecLin.finrank_range_add_finrank_ker
  -- Matrix rank is the dimension of the range of its coordinate linear map.
  have hr : finrank K (LinearMap.range A.transpose.mulVecLin) = A.transpose.rank := (rfl)
  rw [hr, Matrix.rank_transpose, Module.finrank_fintype_fun_eq_card] at h
  omega

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

omit [Fintype I] in
private theorem rootEvaluation_eq_mulVec_coordinates {J : Type*} [Fintype J]
    (b : Basis J K H) (h : H) :
    R.rootEvaluation h = (fun i j => R.root i (b j)) *ᵥ b.equivFun h := by
  ext i
  calc
    R.rootEvaluation h i = R.root i (∑ j, b.equivFun h j • b j) := by
      rw [b.sum_equivFun, rootEvaluation_apply]
    _ = _ := by
      simp only [map_sum, map_smul, smul_eq_mul, Matrix.mulVec, dotProduct, mul_comm]

section Restriction

omit [Fintype I] in
/-- Restrict a realization to a subspace containing its coroots and supplying every root
evaluation. The latter condition is expressed by spanning together with the Cartan center. -/
def restrict (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) : CartanRealization A M where
  coroot i := ⟨R.coroot i, hc (R.coroot_mem_corootSpan i)⟩
  root i := (R.root i).comp M.subtype
  coroot_linearIndependent := R.coroot_linearIndependent.of_comp M.subtype
  root_linearIndependent := by
    classical
    refine linearIndependent_iff'.mpr fun s c h i hi => ?_
    apply linearIndependent_iff'.mp R.root_linearIndependent s c ?_ i hi
    ext x
    have hx : x ∈ M ⊔ R.cartanCenter := hs ▸ Submodule.mem_top
    obtain ⟨m, hm, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    have hm' := congrArg (fun f : Module.Dual K M => f ⟨m, hm⟩) h
    have hz' := (R.mem_cartanCenter_iff z).mp hz
    simpa [map_add, hz', LinearMap.sum_apply, LinearMap.smul_apply] using hm'
  root_coroot i j := R.root_coroot i j

omit [Fintype I] in
/-- Restriction preserves each simple coroot under the subspace inclusion. -/
@[simp]
theorem coe_restrict_coroot (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) (i : I) :
    ((R.restrict M hc hs).coroot i : H) = R.coroot i := (rfl)

omit [Fintype I] in
/-- Restricted roots are the original functionals on vectors in the subspace. -/
@[simp]
theorem restrict_root_apply (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) (i : I) (m : M) :
    (R.restrict M hc hs).root i m = R.root i m := (rfl)

/-- Restriction preserves coroot linear combinations under the subspace inclusion. -/
@[simp]
theorem coe_restrict_corootMap (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) (c : I → K) :
    ((R.restrict M hc hs).corootMap c : H) = R.corootMap c := by
  simp [corootMap_apply]

omit [Fintype I] in
/-- Root evaluation on a restriction agrees with the original evaluation. -/
@[simp]
theorem restrict_rootEvaluation (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) (m : M) :
    (R.restrict M hc hs).rootEvaluation m = R.rootEvaluation m := by
  ext i
  simp

omit [Fintype I] in
/-- The coroot span of a restriction maps onto the original coroot span. -/
theorem corootSpan_restrict_map_subtype (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) :
    (R.restrict M hc hs).corootSpan.map M.subtype = R.corootSpan := by
  have heq : M.subtype ∘ (R.restrict M hc hs).coroot = R.coroot :=
    funext (R.coe_restrict_coroot M hc hs)
  simp only [corootSpan, Submodule.map_span, ← Set.range_comp, heq]

omit [Fintype I] in
/-- The coroot span of a restricted realization is the trace of the original coroot span. -/
@[simp]
theorem corootSpan_restrict (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) :
    (R.restrict M hc hs).corootSpan = R.corootSpan.comap M.subtype := by
  rw [← R.corootSpan_restrict_map_subtype M hc hs,
    Submodule.comap_map_eq_of_injective M.injective_subtype]

omit [Fintype I] in
/-- The center of a restricted realization is the trace of the original center. -/
@[simp]
theorem cartanCenter_restrict (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) :
    (R.restrict M hc hs).cartanCenter = R.cartanCenter.comap M.subtype := by
  ext m
  simp

end Restriction

section FiniteDimensional

/-- A finite-dimensional realization is minimal if it attains the sharp dimension bound. -/
def IsMinimal (_R : CartanRealization A H) : Prop :=
  FiniteDimensional K H ∧ finrank K H = 2 * Fintype.card I - A.rank

variable {R} in
/-- A minimal realization has finite-dimensional ambient space. -/
theorem IsMinimal.finiteDimensional (hR : R.IsMinimal) : FiniteDimensional K H := hR.1

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
  rw [R.rootEvaluation_eq_mulVec_coordinates b, b.equivFun.apply_symm_apply]
  exact hx

omit [FiniteDimensional K H] in
/-- The dimension of the coroot span equals the number of simple coroots. -/
@[simp]
theorem finrank_corootSpan : finrank K R.corootSpan = Fintype.card I :=
  finrank_span_eq_card R.coroot_linearIndependent

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
    exact (congrFun (R.rootEvaluation_eq_mulVec_coordinates b (R.coroot j)) i).symm.trans
      (R.root_coroot j i)
  have h := Matrix.rank_mul_ge B C
  rw [hB, hC, hBC, Matrix.rank_transpose, ← finrank_eq_card_basis b] at h
  simpa [two_mul] using h

/-- The usual subtraction form of the dimension bound for a realization. -/
theorem two_mul_card_sub_rank_le_finrank :
    2 * Fintype.card I - A.rank ≤ finrank K H := by
  have := R.two_mul_card_le_rank_add_finrank
  omega

/-- Minimality is equivalent to attaining the dimension bound in addition form. -/
@[simp]
theorem isMinimal_iff : R.IsMinimal ↔ finrank K H + A.rank = 2 * Fintype.card I := by
  have := A.rank_le_card_width
  constructor
  · rintro ⟨_, h⟩
    omega
  · intro h
    exact ⟨inferInstance, by omega⟩

/-- A realization is minimal exactly when its full center lies in the coroot span. -/
theorem isMinimal_iff_cartanCenter_le_corootSpan :
    R.IsMinimal ↔ R.cartanCenter ≤ R.corootSpan := by
  rw [R.isMinimal_iff]
  have hc := R.finrank_cartanCenter_add_card
  have hi := R.finrank_cartanCenter_inf_corootSpan_add_rank
  constructor
  · intro h
    have heq : R.cartanCenter ⊓ R.corootSpan = R.cartanCenter :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
    exact inf_eq_left.mp heq
  · intro h
    rw [inf_eq_left.mpr h] at hi
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

/-- Transport commutes with taking a coroot linear combination. -/
@[simp]
theorem map_corootMap (e : H ≃ₗ[K] H') (c : I → K) :
    (R.map e).corootMap c = e (R.corootMap c) := by
  simp [corootMap_apply]

omit [Fintype I] in
/-- Root evaluation after transport is evaluation at the inverse image. -/
@[simp]
theorem map_rootEvaluation (e : H ≃ₗ[K] H') (h : H') :
    (R.map e).rootEvaluation h = R.rootEvaluation (e.symm h) := by
  ext i
  simp

omit [Fintype I] in
/-- Transport carries the coroot span to its image. -/
theorem corootSpan_map (e : H ≃ₗ[K] H') :
    (R.map e).corootSpan = R.corootSpan.map e.toLinearMap := by
  have hc : (R.map e).coroot = e ∘ R.coroot := funext (R.map_coroot e)
  simp only [corootSpan, hc, Submodule.map_span, ← Set.range_comp, LinearEquiv.coe_coe]

omit [Fintype I] in
/-- Transport carries the full Cartan center to its image. -/
theorem cartanCenter_map (e : H ≃ₗ[K] H') :
    (R.map e).cartanCenter = R.cartanCenter.map e.toLinearMap := by
  rw [Submodule.map_equiv_eq_comap_symm]
  ext h
  simp

omit [Fintype I] in
/-- Transport by the identity leaves a realization unchanged. -/
@[simp]
theorem map_refl : R.map (LinearEquiv.refl K H) = R := by
  ext <;> simp

omit [Fintype I] in
/-- Successive transports agree with transport by the composite equivalence. -/
@[simp]
theorem map_trans {H'' : Type*} [AddCommGroup H''] [Module K H'']
    (e : H ≃ₗ[K] H') (f : H' ≃ₗ[K] H'') : (R.map e).map f = R.map (e.trans f) := by
  ext <;> simp

/-- Minimality is invariant under linear equivalence of the ambient spaces. -/
@[simp]
theorem isMinimal_map (e : H ≃ₗ[K] H') : (R.map e).IsMinimal ↔ R.IsMinimal := by
  constructor
  · rintro ⟨hfin, hdim⟩
    let := hfin
    exact ⟨e.symm.finiteDimensional, by rw [e.finrank_eq]; exact hdim⟩
  · rintro ⟨hfin, hdim⟩
    let := hfin
    exact ⟨e.finiteDimensional, by rw [← e.finrank_eq]; exact hdim⟩

omit [Fintype I] in
/-- If the coroots span both realizations, there is a unique linear equivalence preserving
all simple roots and coroots. Unlike the singular minimal case, the coroots form a basis. -/
theorem existsUnique_equiv_of_corootSpan_eq_top (S : CartanRealization A H')
    (hR : R.corootSpan = ⊤) (hS : S.corootSpan = ⊤) :
    ∃! e : H ≃ₗ[K] H', (∀ i, e (R.coroot i) = S.coroot i) ∧
      ∀ i h, S.root i (e h) = R.root i h := by
  let b := Basis.mk R.coroot_linearIndependent (le_of_eq hR.symm)
  let c := Basis.mk S.coroot_linearIndependent (le_of_eq hS.symm)
  have hb (i : I) : b i = R.coroot i := Basis.mk_apply _ _ i
  have hc (i : I) : c i = S.coroot i := Basis.mk_apply _ _ i
  let e := b.equiv c (Equiv.refl I)
  have he (i : I) : e (R.coroot i) = S.coroot i := by
    simpa only [hb, hc, Equiv.refl_apply] using b.equiv_apply i c (Equiv.refl I)
  refine ⟨e, ⟨he, ?_⟩, ?_⟩
  · intro i h
    have hf : (S.root i).comp e.toLinearMap = R.root i := by
      apply b.ext
      intro j
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hb, he, root_coroot]
    exact LinearMap.congr_fun hf h
  · intro f hf
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro i
    simpa only [LinearEquiv.coe_coe, hb] using (hf.1 i).trans (he i).symm

end Transport

section Construction

variable (A) (Z : Submodule K (I → K))

open scoped Classical in
/-- Realize a matrix by adjoining a supplement to its transpose's image. The first factor
contains the independent coroots; the second supplies the missing root evaluations. -/
noncomputable def ofSupplement
    (hZ : LinearMap.range A.transpose.mulVecLin ⊔ Z = ⊤) :
    CartanRealization A ((I → K) × Z) where
  coroot := LinearMap.inl K (I → K) Z ∘ Pi.basisFun K I
  root := (A.transpose.mulVecLin.coprod Z.subtype).dualMap ∘ (Pi.basisFun K I).dualBasis
  coroot_linearIndependent := (Pi.basisFun K I).linearIndependent.map'
    (LinearMap.inl K (I → K) Z) (LinearMap.ker_eq_bot.mpr LinearMap.inl_injective)
  root_linearIndependent := by
    have hsurj : Function.Surjective (A.transpose.mulVecLin.coprod Z.subtype) := by
      rwa [← LinearMap.range_eq_top, LinearMap.range_coprod, Submodule.range_subtype]
    exact (Pi.basisFun K I).dualBasis.linearIndependent.map'
      (A.transpose.mulVecLin.coprod Z.subtype).dualMap
      (LinearMap.ker_eq_bot.mpr (LinearMap.dualMap_injective_of_surjective hsurj))
  root_coroot i j := by classical simp

@[simp]
theorem ofSupplement_coroot (hZ : LinearMap.range A.transpose.mulVecLin ⊔ Z = ⊤) (i : I) :
    (ofSupplement A Z hZ).coroot i = ((Pi.basisFun K I) i, 0) := (rfl)

@[simp]
theorem ofSupplement_root_apply (hZ : LinearMap.range A.transpose.mulVecLin ⊔ Z = ⊤)
    (i : I) (h : (I → K) × Z) :
    (ofSupplement A Z hZ).root i h = (A.transpose *ᵥ h.1) i + (h.2 : I → K) i := by
  classical
  exact (LinearMap.dualMap_apply _ _ _).trans (by simp [Matrix.mulVec_transpose])

/-- Adjoining a complement, rather than just a supplement, gives a minimal realization. -/
theorem isMinimal_ofSupplement (hZ : IsCompl (LinearMap.range A.transpose.mulVecLin) Z) :
    (ofSupplement A Z hZ.sup_eq_top).IsMinimal := by
  classical
  refine ⟨inferInstance, ?_⟩
  -- Matrix rank is defined as the dimension of the range of mulVecLin.
  have hrank : finrank K (LinearMap.range A.transpose.mulVecLin) = A.transpose.rank := (rfl)
  rw [Matrix.rank_transpose] at hrank
  have h := Submodule.finrank_add_eq_of_isCompl hZ
  rw [hrank, Module.finrank_fintype_fun_eq_card] at h
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
  omega

end Construction

end CartanRealization
end TauCeti

namespace Matrix

/-- Every square matrix admits a realization attaining the dimension bound, in a coordinate
space. In particular this constructs minimal rational realizations of singular Cartan matrices. -/
theorem nonempty_cartanRealization {I K : Type*} [Fintype I] [Field K] (A : Matrix I I K) :
    Nonempty (TauCeti.CartanRealization A (Fin (2 * Fintype.card I - A.rank) → K)) := by
  obtain ⟨Z, hZ⟩ := Submodule.exists_isCompl (LinearMap.range A.transpose.mulVecLin)
  have hdim := (TauCeti.CartanRealization.isMinimal_iff _).mp
    (TauCeti.CartanRealization.isMinimal_ofSupplement A Z hZ)
  let e : ((I → K) × Z) ≃ₗ[K] (Fin (2 * Fintype.card I - A.rank) → K) :=
    LinearEquiv.ofFinrankEq _ _ (by
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
      omega)
  exact ⟨(TauCeti.CartanRealization.ofSupplement A Z hZ.sup_eq_top).map e⟩

end Matrix
