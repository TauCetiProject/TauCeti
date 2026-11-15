/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Basic

/-!
# Twisted boundaries on totally disconnected spaces

Every singular edge of a totally disconnected space is degenerate. Its two faces cancel even
with local coefficients, so the boundary into degree zero vanishes. This also determines the
boundary into degree zero after extending to locally finite chains. The degeneracy argument uses
Mathlib's `TopCat.toSSetIsoConst`, identifying the singular simplicial set with a constant one.

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
