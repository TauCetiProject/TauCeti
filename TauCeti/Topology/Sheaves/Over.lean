/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.Over
public import Mathlib.Topology.Category.TopCat.Opens

/-!
# Open embeddings and over categories of open subsets

Let `f : X ⟶ Y` be an open embedding of topological spaces, with open image `U = range f`.
Mathlib's `TopologicalSpace.Opens.overEquivalence` identifies `Over U` with the open subsets of the
subspace `U`. This file gives the corresponding equivalence `Over U ≌ Opens X` for the open
embedding itself: an open subset `W ⊆ U` goes to `f⁻¹(W)`, and an open subset `V ⊆ X` goes back to
`f(V)`. The equivalence is a dense subsite in both directions, so it induces an equivalence of
sheaf categories under which a sheaf `F` on `Y`, restricted to `U`, becomes the sheaf
`V ↦ F(f(V))` on `X`.

Working with `f` rather than with the subspace `U` keeps that sheaf literally equal to the
pushforward along `f(-)`, which is how Mathlib defines the restriction of a sheaf of modules along
an open immersion of schemes.

## Main declarations

* `Topology.IsOpenEmbedding.overEquivalence`: the equivalence `Over (range f) ≌ Opens X`.
* The instances saying that its functor and inverse are dense subsites for the Grothendieck
  topologies of open covers.
-/

public section

universe u

open CategoryTheory TopologicalSpace Topology

namespace TauCeti

variable {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenEmbedding f)

/-- An open embedding `f : X ⟶ Y` identifies the open subsets of `Y` contained in the range of
`f` with the open subsets of `X`, by taking preimages and images under `f`. -/
@[expose, simps]
def _root_.Topology.IsOpenEmbedding.overEquivalence :
    Over (⟨Set.range f, hf.isOpen_range⟩ : Opens Y) ≌ Opens X where
  functor.obj W := (Opens.map f).obj W.left
  functor.map g := (Opens.map f).map g.left
  inverse.obj V := Over.mk (Y := hf.functor.obj V) (homOfLE (Set.image_subset_range f V))
  inverse.map g := Over.homMk (hf.functor.map g)
  unitIso := NatIso.ofComponents (fun W ↦ Over.isoMk (eqToIso (by
    ext y
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := W.hom.le hy
      exact ⟨x, hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx)))
  counitIso := NatIso.ofComponents (fun V ↦ eqToIso (by
    ext x
    exact hf.injective.mem_set_image))

instance isDenseSubsite_overEquivalence_functor : hf.overEquivalence.functor.IsDenseSubsite
    ((Opens.grothendieckTopology Y).over _) (Opens.grothendieckTopology X) where
  functorPushforward_mem_iff {V S} := by
    simp only [Opens.mem_grothendieckTopology, Sieve.mem_functorPushforward_functor]
    constructor
    · intro H y hyV
      obtain ⟨x, rfl⟩ := V.hom.le hyV
      obtain ⟨W, g, hW, hxW⟩ := H x hyV
      exact ⟨_, ((hf.overEquivalence.symm.toAdjunction.homEquiv _ _).symm g).left,
        ⟨_, _, 𝟙 _, hW, rfl⟩, x, hxW, rfl⟩
    · intro H x hxV
      obtain ⟨W, g, ⟨W', hW'V, hWW', hSW'V, rfl⟩, hxW⟩ := H (f x) hxV
      exact ⟨_, hf.overEquivalence.functor.map hW'V,
        S.downward_closed hSW'V (hf.overEquivalence.unitInv.app W'), hWW'.le hxW⟩

instance isDenseSubsite_overEquivalence_symm_inverse :
    hf.overEquivalence.symm.inverse.IsDenseSubsite
    ((Opens.grothendieckTopology Y).over _) (Opens.grothendieckTopology X) :=
  inferInstanceAs (hf.overEquivalence.functor.IsDenseSubsite ..)

instance isDenseSubsite_overEquivalence_inverse : hf.overEquivalence.inverse.IsDenseSubsite
    (Opens.grothendieckTopology X) ((Opens.grothendieckTopology Y).over _) :=
  inferInstanceAs (hf.overEquivalence.symm.functor.IsDenseSubsite ..)

end TauCeti
