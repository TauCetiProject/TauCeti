/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
import all TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet

/-!
# Word maps and coordinate-group homomorphisms

A tuple of coefficient words that maps one algebraic set into another induces a
coefficient-preserving homomorphism in the opposite direction between their coordinate groups.
Conversely, every such homomorphism is represented by a tuple of words. Two tuples represent the
same homomorphism precisely when their word maps agree at every point of the source algebraic
set. This describes polynomial maps without choosing presentations of coordinate functions.

The correspondence follows Baumslag, Myasnikov and Remeslennikov, *Algebraic geometry over
groups I*, Section 3.5, Theorem 4 and Corollary 9.
-/

public section

namespace TauCeti.GroupAlgGeom
namespace CoordGroup

open Monoid.Coprod

variable {G H X Y : Type*} [Group G] [Group H]
variable (ι : G →* H) (S : Set (GX G X)) (T : Set (GX G Y))

/-- Every coefficient-preserving coordinate-group homomorphism is represented by a tuple of
coefficient words, whose word map carries source solutions to target solutions. -/
theorem exists_wordMap_representation (φ : GHom (coeff ι T) (coeff ι S)) :
    ∃ w : Y → GX G X, ∃ hw : MapsToWordMap ι S T w,
      homOfMapsToWordMap ι S T w hw = φ := by
  classical
  have hsurj : ∀ y : Y, ∃ w : GX G X,
      (w : CoordGroup ι S) = φ ((inr (FreeGroup.of y) : GX G Y) : CoordGroup ι T) := by
    intro y
    exact QuotientGroup.mk_surjective _
  choose w hw using hsurj
  have hmap : MapsToWordMap ι S T w := by
    rw [mapsToWordMap_iff]
    intro v hv
    let ψ : GHom (coeff ι T) ι := (evalGHom v hv).comp φ
    have hcoords : wordMap ι w v = (homEquiv ι T ψ : Y → H) := by
      funext y
      simp only [wordMap_apply, homEquiv_apply_coe]
      rw [← evalGHom_mk (ι := ι) (S := S) hv (w y), hw y]
      exact (congrFun (GHom.coe_comp (evalGHom v hv) φ)
        ((inr (FreeGroup.of y) : GX G Y) : CoordGroup ι T)).symm
    rw [hcoords]
    exact (homEquiv ι T ψ).property
  refine ⟨w, hmap, ?_⟩
  apply gHom_ext
  intro y
  rw [homOfMapsToWordMap_mk, eval_inr_of, hw y]

/-- Two representing tuples induce the same coordinate-group homomorphism exactly when they
give the same function on the source algebraic set. -/
theorem homOfMapsToWordMap_eq_iff (w w' : Y → GX G X)
    (hw : MapsToWordMap ι S T w) (hw' : MapsToWordMap ι S T w') :
    homOfMapsToWordMap ι S T w hw = homOfMapsToWordMap ι S T w' hw' ↔
      ∀ v ∈ V ι S, wordMap ι w v = wordMap ι w' v := by
  constructor
  · intro h v hv
    have h' := congrArg (fun f : GHom (coeff ι T) (coeff ι S) =>
      (homEquiv ι T ((evalGHom v hv).comp f) : Y → H)) h
    exact (homEquiv_comp_homOfMapsToWordMap ι S T w hw ⟨v, hv⟩).symm.trans
      (h'.trans (homEquiv_comp_homOfMapsToWordMap ι S T w' hw' ⟨v, hv⟩))
  · intro h
    apply gHom_ext
    intro y
    simp only [homOfMapsToWordMap_mk, eval_inr_of]
    apply QuotientGroup.eq.mpr
    rw [mem_Rad]
    intro v hv
    have := congrFun (h v hv) y
    simpa only [wordMap_apply, map_mul, map_inv, inv_mul_eq_one] using this

end CoordGroup
end TauCeti.GroupAlgGeom
