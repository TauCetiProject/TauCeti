/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialNerve

/-!
# Chains of paths in the simplicial thickening

For a linear order `J`, Mathlib's simplicial thickening `SimplicialThickening J` is the simplicial
category `C[Δ^J]` whose mapping simplicial set from `i` to `j` is the nerve of the poset `Path i j`
of subsets of `[i, j]` containing both endpoints. This file collects basic facts about these
posets of paths and about chains of paths, the simplices of the mapping simplicial sets.

## Main declarations

* `SimplicialThickening.chainMk`: the chain of paths given by a monotone family of paths.
* `SimplicialThickening.monotone_chain`: the paths of a chain increase.
* `SimplicialThickening.isIso_eId`: the identity `𝟙_ SSet ⟶ N(Path x x)` is an isomorphism.
-/

public section

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace CategoryTheory.SimplicialThickening

variable {J : Type u} [LinearOrder J] {i j : J}

instance : Quiver.IsThin (Path i j) :=
  fun _ _ ↦ ⟨fun _ _ ↦ InducedCategory.hom_ext (Subsingleton.elim _ _)⟩

/-- The only path from an element to itself is the singleton. -/
instance (a : J) : Subsingleton (Path a a) :=
  ⟨fun p q ↦ Path.ext (Set.ext fun k ↦ by
    constructor <;> intro h
    · rw [le_antisymm (p.le_right k h) (p.left_le k h)]
      exact q.left
    · rw [le_antisymm (q.le_right k h) (q.left_le k h)]
      exact p.left)⟩

/-- The identity of an object `x` of the simplicial thickening is an isomorphism
`𝟙_ SSet ≅ N(Path x x)`, since the only path from `x` to itself is `{x}`. -/
instance isIso_eId (x : SimplicialThickening J) : IsIso (eId SSet x) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  rw [isIso_iff_bijective]
  refine ⟨fun _ _ _ ↦ rfl, fun s ↦ ⟨PUnit.unit, ?_⟩⟩
  obtain ⟨⟨d⟩⟩ := n
  exact ComposableArrows.ext (C := Path x.as x.as) (fun _ ↦ Subsingleton.elim _ _)
    (by subsingleton)

/-- The chain of paths given by a monotone family of paths. -/
def chainMk {d : ℕ} (p : Fin (d + 1) → Path i j) (hp : Monotone fun t ↦ (p t).I) :
    ComposableArrows (Path i j) d where
  obj := p
  map h := InducedCategory.homMk (homOfLE (hp (leOfHom h)))

@[simp]
lemma chainMk_obj {d : ℕ} (p : Fin (d + 1) → Path i j) (hp : Monotone fun t ↦ (p t).I)
    (t : Fin (d + 1)) : (chainMk p hp).obj t = p t := by
  rfl

/-- The paths of a chain of paths increase. -/
lemma monotone_chain {d : ℕ} (x : ComposableArrows (Path i j) d) :
    Monotone fun t ↦ (x.obj t).I :=
  fun _ _ h ↦ (x.map (homOfLE h)).hom.le

end CategoryTheory.SimplicialThickening
