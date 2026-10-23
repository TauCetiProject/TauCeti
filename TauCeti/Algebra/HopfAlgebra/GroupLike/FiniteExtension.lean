/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Bialgebra.GroupLike.ScalarTower
public import TauCeti.Algebra.Coalgebra.GroupLike.BaseChange
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import TauCeti.LinearAlgebra.TensorProduct.FiniteExtension
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import TauCeti.Algebra.Bialgebra.BaseChange

/-!
# Finite fields of definition for characters

If the characters of a Hopf algebra over an algebraic extension form a finitely generated group,
then they are all defined over one finite intermediate field. If these characters also span the
extended algebra, they span over that finite field already. This supplies finite algebraic
splitting fields for affine groups of multiplicative type.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {k K A : Type*} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
  [Ring A] [HopfAlgebra k A]
  [Group.FG (_root_.GroupLike K (K ⊗[k] A))]

/-- A finitely generated character group over an algebraic extension is defined over a common
finite intermediate field. -/
theorem exists_finiteDimensional_surjective_groupLikeScalarTowerHom :
    ∃ L : IntermediateField k K, FiniteDimensional k L ∧
      Function.Surjective (groupLikeScalarTowerHom (k := k) (L := L) (K := K) (A := A)) := by
  obtain ⟨s, hs⟩ := Group.exists_of_isMulFG (_root_.GroupLike K (K ⊗[k] A))
  obtain ⟨L, hL, hdef⟩ := Set.exists_finiteDimensional_intermediateField_tensor_range
    (_root_.GroupLike.val '' (s : Set (_root_.GroupLike K (K ⊗[k] A))))
    (s.finite_toSet.image _)
  -- Supplying the scalar field explicitly resolves the inherited intermediate-field instances.
  let : Group (_root_.GroupLike L (L ⊗[k] A)) :=
    _root_.GroupLike.instGroup (R := L) (A := L ⊗[k] A)
  refine ⟨L, hL, ?_⟩
  rw [← MonoidHom.range_eq_top (G := _root_.GroupLike L (L ⊗[k] A))
    (N := _root_.GroupLike K (K ⊗[k] A))]
  apply top_unique
  rw [← hs]
  apply (Subgroup.closure_le _).mpr
  intro g hg
  obtain ⟨x, hx⟩ := hdef ⟨g, hg, rfl⟩
  let e := Bialgebra.TensorProduct.baseChangeTowerBialgEquiv k L A K
  have he : e (1 ⊗ₜ[L] x) = g.val := by
    rw [TensorProduct.baseChangeTowerBialgEquiv_one_tmul]
    exact hx
  have hxg : IsGroupLikeElem L x := by
    rw [← isGroupLikeElem_one_tmul_iff (K := K), ← isGroupLikeElem_map_equiv e, he]
    exact g.isGroupLikeElem_val
  refine ⟨⟨x, hxg⟩, _root_.GroupLike.val_injective ?_⟩
  rw [val_groupLikeScalarTowerHom]
  exact hx

/-- If finitely generated characters span after an algebraic extension, they already span
after a finite intermediate extension. -/
theorem exists_finiteDimensional_span_groupLike_eq_top
    (hspan : Submodule.span K
      (Set.range (_root_.GroupLike.val (R := K) (A := K ⊗[k] A))) = ⊤) :
    ∃ L : IntermediateField k K, FiniteDimensional k L ∧
      Submodule.span L (Set.range (_root_.GroupLike.val (R := L) (A := L ⊗[k] A))) = ⊤ := by
  obtain ⟨L, hL, hsurj⟩ :=
    exists_finiteDimensional_surjective_groupLikeScalarTowerHom (k := k) (K := K) (A := A)
  refine ⟨L, hL, ?_⟩
  let p := Submodule.span L
    (Set.range (_root_.GroupLike.val (R := L) (A := L ⊗[k] A)))
  let e := Bialgebra.TensorProduct.baseChangeTowerBialgEquiv k L A K
  have hmap : (p.baseChange K).map e.toAlgEquiv.toLinearEquiv.toLinearMap = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    obtain ⟨x, rfl⟩ := hsurj g
    refine ⟨1 ⊗ₜ[L] x.val,
      Submodule.tmul_mem_baseChange_of_mem 1 (Submodule.subset_span ⟨x, rfl⟩), ?_⟩
    rw [val_groupLikeScalarTowerHom]
    exact TensorProduct.baseChangeTowerBialgEquiv_one_tmul k L A K x.val
  have hp : p.baseChange K = ⊤ :=
    (Submodule.map_eq_top_iff (e := e.toAlgEquiv.toLinearEquiv)).mp hmap
  apply Submodule.baseChange_injective (A := K)
  simpa only [Submodule.baseChange_top] using hp

end TauCeti
