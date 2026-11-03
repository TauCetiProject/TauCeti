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

* `SimplicialThickening.Path.Icc`: the path from `i` to `j` through every element in between.
* `SimplicialThickening.Path.subsingleton_of_forall_not_lt`: there is at most one path between
  two elements with nothing strictly in between.
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

/-- The path from `i` to `j` through every element in between. -/
def Path.Icc (h : i ≤ j) : Path i j where
  I := Set.Icc i j
  left := ⟨le_rfl, h⟩
  right := ⟨h, le_rfl⟩
  left_le _ hk := hk.1
  le_right _ hk := hk.2

@[simp]
lemma Path.Icc_I (h : i ≤ j) : (Path.Icc h).I = Set.Icc i j :=
  (rfl)

/-- If no element lies strictly between `i` and `j`, there is at most one path from `i` to `j`.
For instance, this holds for all `i` and `j` in a linear order with at most two elements. -/
lemma Path.subsingleton_of_forall_not_lt (h : ∀ k, i < k → ¬k < j) : Subsingleton (Path i j) := by
  have key (p q : Path i j) (k : J) (hk : k ∈ p.I) : k ∈ q.I := by
    rcases (p.left_le k hk).eq_or_lt with rfl | hik
    · exact q.left
    rcases (p.le_right k hk).eq_or_lt with rfl | hkj
    · exact q.right
    exact absurd hkj (h k hik)
  exact ⟨fun p q ↦ Path.ext (Set.ext fun k ↦ ⟨key p q k, key q p k⟩)⟩

/-- The only path from an element to itself is the singleton. -/
instance (a : J) : Subsingleton (Path a a) :=
  Path.subsingleton_of_forall_not_lt fun _ h₁ h₂ ↦ lt_asymm h₁ h₂

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
