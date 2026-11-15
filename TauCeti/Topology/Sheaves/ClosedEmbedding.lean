/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors
public import TauCeti.Topology.Sheaves.Stalks

/-!
# Exact pushforward along a closed embedding

Pushforward of abelian sheaves along a closed embedding is exact. At a point of the
image its stalk is the original stalk, and outside the closed image its stalk is zero.
This is the exactness input for comparing sheaf cohomology with cohomology on a closed
subspace, for example when embedding a projective scheme in projective space.

## References

* R. Hartshorne, *Algebraic Geometry*, III, Lemma 2.10.
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite _root_.Topology TopCat.Presheaf

namespace TauCeti.Topology

universe u

noncomputable section

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- Direct image of abelian sheaves is additive. -/
instance additive_pushforward : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The stalk of a pushed-forward abelian sheaf vanishes outside the closure of the image. -/
theorem isZero_stalk_pushforward_of_notMem_closure_range
    (F : X.Sheaf AddCommGrpCat.{u}) {y : Y} (hy : y ∉ closure (Set.range f)) :
    IsZero (TopCat.Presheaf.stalk
      ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F).obj y) := by
  let V : Opens Y := ⟨(closure (Set.range f))ᶜ, isClosed_closure.isOpen_compl⟩
  have hV : (Opens.map f).obj V = ⊥ := by
    ext x
    exact iff_false_intro (fun hx ↦ hx (subset_closure (Set.mem_range_self x)))
  let G := (TopCat.Sheaf.pushforward AddCommGrpCat f).obj F
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨U, hUV, hyU, s, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq G.obj a (V := V) hy
  obtain ⟨W, hWV, hyW, t, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq G.obj b (V := V) hy
  -- Shrinking to the complement makes both groups of sections zero.
  have hU : (Opens.map f).obj U = ⊥ := le_bot_iff.mp (hV ▸ (Opens.map f).monotone hUV)
  have hW : (Opens.map f).obj W = ⊥ := le_bot_iff.mp (hV ▸ (Opens.map f).monotone hWV)
  have hs : s = 0 := (AddCommGrpCat.subsingleton_of_isZero
    (F.isTerminalOfEqEmpty hU).isZero).elim _ _
  have ht : t = 0 := (AddCommGrpCat.subsingleton_of_isZero
    (F.isTerminalOfEqEmpty hW).isZero).elim _ _
  simp only [hs, ht, map_zero]

/-- For an inducing map, the stalk of pushforward at an image point is naturally isomorphic
to the original stalk. -/
def pushforwardStalkIso (hf : IsInducing f) (x : X) :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
        TopCat.Sheaf.forget AddCommGrpCat Y ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x) ≅
      TopCat.Sheaf.forget AddCommGrpCat X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x := by
  exact NatIso.ofComponents (fun (F : X.Sheaf AddCommGrpCat.{u}) ↦
      @asIso _ _ _ _ (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f F.obj x)
        (TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
          AddCommGrpCat.{u} hf F.obj x))
    (fun α ↦ stalkPushforward_naturality f α.hom x)

/-- The stalk comparison is the canonical pushforward map on stalks. -/
@[simp]
lemma pushforwardStalkIso_hom_app (hf : IsInducing f) (x : X)
    (F : X.Sheaf AddCommGrpCat.{u}) :
    (pushforwardStalkIso f hf x).hom.app F =
      TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f F.obj x :=
  (rfl)

/-- Pushforward along a closed embedding preserves exact complexes of abelian sheaves. -/
theorem exact_pushforward_of_isClosedEmbedding (hf : IsClosedEmbedding f)
    (S : ShortComplex (X.Sheaf AddCommGrpCat.{u})) (hS : S.Exact) :
    (S.map (TopCat.Sheaf.pushforward AddCommGrpCat f)).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mpr
  intro y
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    have h := (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mp hS x
    exact ShortComplex.exact_of_iso
      ((S.mapNatIso (pushforwardStalkIso f hf.isEmbedding.isInducing x)).symm) h
  · apply ShortComplex.exact_of_isZero_X₂
    exact isZero_stalk_pushforward_of_notMem_closure_range f S.X₂
      (by simpa only [hf.isClosed_range.closure_eq] using hy)

/-- Closed-embedding pushforward preserves homology. -/
theorem preservesHomology_pushforward_of_isClosedEmbedding (hf : IsClosedEmbedding f) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).PreservesHomology := by
  apply ((TopCat.Sheaf.pushforward AddCommGrpCat f).exact_tfae.out 3 2).mpr
  exact exact_pushforward_of_isClosedEmbedding f hf

/-- Closed-embedding pushforward preserves finite colimits, as well as the limits preserved
by every sheaf pushforward. -/
theorem preservesFiniteColimits_pushforward_of_isClosedEmbedding (hf : IsClosedEmbedding f) :
    PreservesFiniteColimits (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) := by
  have := preservesHomology_pushforward_of_isClosedEmbedding f hf
  exact Functor.preservesFiniteColimits_of_preservesHomology _

end

end TauCeti.Topology
