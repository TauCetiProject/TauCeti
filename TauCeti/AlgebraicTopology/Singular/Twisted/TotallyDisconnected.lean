/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Relative

/-!
# Twisted boundaries on totally disconnected spaces

Every singular edge of a totally disconnected space is degenerate. Its two faces cancel even
with local coefficients, so the boundary into degree zero vanishes, both on absolute twisted chains
and on relative twisted chains of a pair whose ambient space is totally disconnected. This also
determines the boundary into degree zero after extending to locally finite chains. The degeneracy
argument uses Mathlib's `TopCat.toSSetIsoConst`, identifying the singular simplicial set with a
constant one.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H.
-/

public section

open CategoryTheory Limits SimplexCategory Simplicial

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}} [TotallyDisconnectedSpace X]
  (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- The boundary into degree zero vanishes on a totally disconnected space, for any local
coefficient system. -/
@[simp]
theorem twistedChainComplex_d_one_zero_eq_zero : (twistedChainComplex L).d 1 0 = 0 := by
  let e := twistedChainComplexIsoAlternatingFaceMapComplex L
  suffices h : ((AlgebraicTopology.alternatingFaceMapComplex _).obj
      (twistedChains L)).d 1 0 = 0 by
    apply (cancel_mono (e.hom.f 0)).1
    rw [← e.hom.comm, h, comp_zero, zero_comp]
  apply twistedChains_hom_ext
  intro s
  obtain ⟨t, rfl⟩ : ∃ t, (TopCat.toSSet.obj X).map (σ (0 : Fin 1)).op t = s := by
    let e := TopCat.toSSetIsoConst X
    refine ⟨e.inv.app (Opposite.op ⦋0⦌) (e.hom.app (Opposite.op ⦋1⦌) s), ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (e.hom.app _)).1
    simp
  apply (cancel_epi (eqToHom (congrArg L.obj
    (initialVertex_eq_initialVertex_map (σ (0 : Fin 1)).op t
      (σ_toOrderHom_zero 0))))).1
  rw [← Category.assoc, ← ιTwistedChains_map_σ]
  -- On a degenerate edge, the two simplicial face maps are both the identity.
  have hd : (twistedChains L).map (σ (0 : Fin 1)).op ≫
      ((AlgebraicTopology.alternatingFaceMapComplex _).obj (twistedChains L)).d 1 0 = 0 := by
    have h0 : δ (0 : Fin 2) ≫ σ (0 : Fin 1) = 𝟙 _ := δ_comp_σ_self
    have h1 : δ (1 : Fin 2) ≫ σ (0 : Fin 1) = 𝟙 _ := δ_comp_σ_succ
    simp [AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_two, h0, h1,
      SimplicialObject.δ, ← Functor.map_comp, ← op_comp]
  simp only [Category.assoc, hd, comp_zero]

end TauCeti.LocalCoefficientSystem

namespace TopPair

open TauCeti TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] (P : TopPair.{v}) [TotallyDisconnectedSpace P.fst]
  (L : LocalCoefficientSystem.{u, v, max v w} R P.fst)

/-- The relative boundary into degree zero vanishes for any topological pair whose ambient space
is totally disconnected, for any local coefficient system. -/
@[simp]
theorem twistedChainComplex_d_one_zero_eq_zero : (P.twistedChainComplex L).d 1 0 = 0 := by
  refine ModuleCat.hom_ext <| LinearMap.ext fun y ↦ ?_
  obtain ⟨a, rfl⟩ := P.twistedChainComplexπ_f_surjective L y
  have h0 : (L.twistedChainComplex.d 1 0).hom a = 0 := by
    rw [TauCeti.LocalCoefficientSystem.twistedChainComplex_d_one_zero_eq_zero L,
      ModuleCat.hom_zero, LinearMap.zero_apply]
  exact (congrArg (fun f ↦ f.hom a) ((P.twistedChainComplexπ L).comm 1 0)).trans <|
    (congrArg ((P.twistedChainComplexπ L).f 0).hom h0).trans (map_zero _)

end TopPair
