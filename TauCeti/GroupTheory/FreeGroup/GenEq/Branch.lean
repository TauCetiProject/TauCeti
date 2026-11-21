/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.Transformation
public import TauCeti.GroupTheory.GroupAlgGeom.WordMap
public import TauCeti.GroupTheory.LimitGroup.NTQ.Block

/-!
# Branches of the solution tree of a generalised equation

In the Makanin–Razborov process a generalised equation `Ω` over `F = F(A)` is rewritten along the
branches of a finite tree. Every solution of `Ω` factors along some branch of this tree, from `Ω`
to a generalised equation `Ω'` at its end, as a composite `σ₀ π₁ σ₁ ⋯ πₙ σₙ U'`: canonical
epimorphisms `πᵢ` of coordinate groups, canonical automorphisms `σᵢ` of the coordinate groups on
the way, and a solution `U'` of `Ω'`. Covering all solutions is a property of the family of branches
of the tree, not of a single branch. The composites along one branch are recorded by a block of
triangular quasi-quadratic levels over the system `Ω'*`: an automorphism fixing a subgroup of the
coordinate group and acting on the rest through a quadratic system, or through the extension of a
centralizer, gives the values of a solution of that level in the coordinate group of `Ω'`
(Kharlampovich–Myasnikov, the diagram of Case 14 and Lemma 8).

A *branch* from `Ω` to `Ω'` (`TauCeti.GenEq.Branch Ω Ω'`) is a block over `Ω'*` and a word map
from the items of `Ω` to the variables of the block that sends the solutions of the block to group
solutions of `Ω`; the points of `Ω` it reaches over a set of base points (solutions of `Ω'`) are
the images of the fundamental points of the block over them, and its *image* is the set of points
it reaches over the solutions of `Ω'`. The definition says nothing about which solutions of `Ω` a
branch reaches: it carries no coverage guarantee. Branches compose: a branch followed by a branch of
its end is reached through a single branch.

Two kinds of edges are treated. A transformation of `Ω` gives, for each of its successors, the
branch with no level of its homomorphism of coordinate groups, and every solution of `Ω` is reached
through the branch of the successor to which the transformation transfers it. For a level over the
end (a quadratic system, an extension of a centralizer, a free abelian group or free variables) and
a word map from the items of `Ω`, there is the branch of that level; if a homomorphism
`F_{R(Ω)} → F_{R(Ω')}` is given, at the items, by this word map evaluated at a solution of the level
in `F_{R(Ω')}`, then its composite with any solution of `Ω'` is reached through that branch. This
last result is conditional: the level, its solution and the factorisation at the items are
hypotheses, and this file does not construct these data for the edges of the actual tree.

## Main definitions

* `TauCeti.GenEq.Branch`: a branch from one generalised equation to another.
* `TauCeti.GenEq.Branch.imageOf`, `TauCeti.GenEq.Branch.image`: the points of `Ω` reached through
  a branch, over given base points, respectively over the solutions of its end.
* `TauCeti.GenEq.Branch.refl`: the branch from `Ω` to itself.
* `TauCeti.GenEq.Branch.ofGHom`: the branch of a homomorphism of coordinate groups.
* `TauCeti.GenEq.Branch.ofLevel`: the branch of one level over a generalised equation.

## Main results

* `TauCeti.GenEq.Branch.imageOf_subset_V`: over base points that are group solutions of the end,
  a branch reaches group solutions of `Ω`.
* `TauCeti.GenEq.Branch.mem_imageOf_ofGHom`, `TauCeti.GenEq.Branch.mem_imageOf_ofLevel`: the
  points reached through the branch of a homomorphism and through the branch of one level.
* `TauCeti.GenEq.Transformation.point_mem_imageOf_ofGHom`: a solution of `Ω` is reached, over its
  transfer, through the branch of the successor to which a transformation transfers it.
* `TauCeti.GenEq.Branch.toHom_comp_mem_imageOf_ofLevel`: if a homomorphism of coordinate groups
  (in the source, a canonical automorphism followed by a canonical epimorphism) factors, at the
  items, through a solution of a level, then its composite with a solution of the end is reached
  through the branch of that level over the point of that solution.
* `TauCeti.GenEq.Branch.exists_comp`: branches compose.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §5.1 (the commutative diagram of a transformation), §5.6 (Theorem 5).
* [VAR-II] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. II:
  Systems in triangular quasi-quadratic form and description of residually free groups*,
  J. Algebra 200 (1998), §5 (Case 14, Lemmas 8–9) and §7 (Lemma 17).
-/

public section

open Monoid.Coprod TauCeti.GroupAlgGeom TauCeti.LimitGroup.NTQ

universe u

namespace TauCeti.GenEq

variable {A : Type u}

/-- A *branch* from a generalised equation `Ω` to a generalised equation `Ω'`: a block of TQ levels
over the system `Ω'*` in the variables `vars`, and a word map from the items of `Ω` to the variables
of the block that sends the solutions of the block to group solutions of `Ω`. -/
structure Branch (Ω Ω' : GenEq A) where
  /-- The variables of the block: the items of `Ω'` and the variables of the levels. -/
  vars : Type
  /-- The block of levels over the system `Ω'*`. -/
  block : Block (FreeGroup A) (Fin Ω'.numItems) Ω'.toSystem vars
  /-- The value of each item of `Ω`, as a word in the variables of the block. -/
  wordMap : Fin Ω.numItems → GX (FreeGroup A) vars
  /-- The word map sends solutions of the block to group solutions of `Ω`. -/
  mapsTo : Set.MapsTo (GroupAlgGeom.wordMap (MonoidHom.id (FreeGroup A)) wordMap)
    (V (MonoidHom.id (FreeGroup A)) block.equations) (V (MonoidHom.id (FreeGroup A)) Ω.toSystem)

namespace Branch

variable {Ω Ω' : GenEq A}

/-- The points of `Ω` reached through a branch over the base points `P₀`: the images under the
word map of the fundamental points of the block over `P₀`. -/
def imageOf (b : Branch Ω Ω') (P₀ : Set (Fin Ω'.numItems → FreeGroup A)) :
    Set (Fin Ω.numItems → FreeGroup A) :=
  GroupAlgGeom.wordMap (MonoidHom.id (FreeGroup A)) b.wordMap '' b.block.fundPoints P₀

theorem imageOf_def (b : Branch Ω Ω') (P₀ : Set (Fin Ω'.numItems → FreeGroup A)) :
    b.imageOf P₀ = GroupAlgGeom.wordMap (MonoidHom.id (FreeGroup A)) b.wordMap ''
      b.block.fundPoints P₀ := (rfl)

/-- The *image* of a branch: the points of `Ω` reached through it over the solutions of the
generalised equation at its end. -/
def image (b : Branch Ω Ω') : Set (Fin Ω.numItems → FreeGroup A) :=
  b.imageOf (Set.range Solution.point)

theorem image_def (b : Branch Ω Ω') : b.image = b.imageOf (Set.range Solution.point) := (rfl)

/-- The points reached through a branch are monotone in the base points. -/
@[gcongr]
theorem imageOf_mono (b : Branch Ω Ω') {P₀ P₁ : Set (Fin Ω'.numItems → FreeGroup A)} (h : P₀ ⊆ P₁) :
    b.imageOf P₀ ⊆ b.imageOf P₁ :=
  Set.image_mono (b.block.fundPoints_mono h)

/-- Over base points that are group solutions of the end, the points reached through a branch are
group solutions of `Ω`. -/
theorem imageOf_subset_V (b : Branch Ω Ω') {P₀ : Set (Fin Ω'.numItems → FreeGroup A)}
    (hP₀ : P₀ ⊆ V (MonoidHom.id (FreeGroup A)) Ω'.toSystem) :
    b.imageOf P₀ ⊆ V (MonoidHom.id (FreeGroup A)) Ω.toSystem :=
  (b.mapsTo.mono_left (b.block.fundPoints_subset_V hP₀)).image_subset

/-- The branch with no level of a word map `w` from the items of `Ω` to those of `Ω'` that sends
the group solutions of `Ω'` to group solutions of `Ω`. -/
private def ofWordMap (w : Fin Ω.numItems → GX (FreeGroup A) (Fin Ω'.numItems))
    (hw : Set.MapsTo (GroupAlgGeom.wordMap (MonoidHom.id (FreeGroup A)) w)
      (V (MonoidHom.id (FreeGroup A)) Ω'.toSystem) (V (MonoidHom.id (FreeGroup A)) Ω.toSystem)) :
    Branch Ω Ω' where
  vars := Fin Ω'.numItems
  block := .base
  wordMap := w
  mapsTo := by rwa [Block.equations_base]

private theorem imageOf_ofWordMap {w : Fin Ω.numItems → GX (FreeGroup A) (Fin Ω'.numItems)}
    {hw : Set.MapsTo (GroupAlgGeom.wordMap (MonoidHom.id (FreeGroup A)) w)
      (V (MonoidHom.id (FreeGroup A)) Ω'.toSystem) (V (MonoidHom.id (FreeGroup A)) Ω.toSystem)}
    (P₀ : Set (Fin Ω'.numItems → FreeGroup A)) :
    (ofWordMap w hw).imageOf P₀ = GroupAlgGeom.wordMap (MonoidHom.id (FreeGroup A)) w '' P₀ := by
  rw [imageOf_def]
  exact congrArg (Set.image _) (Block.fundPoints_base P₀)

/-- The branch from `Ω` to itself, with no level. -/
def refl (Ω : GenEq A) : Branch Ω Ω :=
  ofWordMap (fun k ↦ inr (FreeGroup.of k)) (mapsTo_wordMap_id _ _)

/-- The branch from `Ω` to itself reaches exactly its base points. -/
@[simp]
theorem imageOf_refl (Ω : GenEq A) (P₀ : Set (Fin Ω.numItems → FreeGroup A)) :
    (refl Ω).imageOf P₀ = P₀ := by
  rw [refl, imageOf_ofWordMap]
  exact (Set.image_congr' rfl wordMap_id).trans (Set.image_id' P₀)

/-! ### The branch of a homomorphism of coordinate groups -/

/-- The branch, with no level, of an `F(A)`-homomorphism `φ : F_{R(Ω)} → F_{R(Ω')}`: the items of
`Ω` are sent to representatives of their images under `φ`. -/
noncomputable def ofGHom (φ : GHom (CoordGroup.coeff (.id (FreeGroup A)) Ω.toSystem)
    (CoordGroup.coeff (.id (FreeGroup A)) Ω'.toSystem)) : Branch Ω Ω' :=
  ofWordMap _ (CoordGroup.exists_wordMap_representation _ _ _ φ).choose_spec.choose

section ofGHom

variable (φ : GHom (CoordGroup.coeff (.id (FreeGroup A)) Ω.toSystem)
  (CoordGroup.coeff (.id (FreeGroup A)) Ω'.toSystem))

private theorem apply_inr_of_eq_ofGHom (k : Fin Ω.numItems) :
    φ ((inr (FreeGroup.of k) : GX (FreeGroup A) (Fin Ω.numItems)) : Ω.coordGroup) =
      ((CoordGroup.exists_wordMap_representation _ _ _ φ).choose k : Ω'.coordGroup) := by
  obtain ⟨hw, hφ⟩ := (CoordGroup.exists_wordMap_representation _ _ _ φ).choose_spec
  rw [← DFunLike.congr_fun hφ, CoordGroup.homOfMapsToWordMap_mk, eval_inr_of]

/-- Over base points that are group solutions of `Ω'`, the points reached through the branch of
`φ` are the points `k ↦ π_u (φ hₖ)` of `Ω`, where `π_u : F_{R(Ω')} → F(A)` is evaluation at a base
point `u` and `hₖ` are the items of `Ω`. -/
theorem mem_imageOf_ofGHom {P₀ : Set (Fin Ω'.numItems → FreeGroup A)}
    (hP₀ : P₀ ⊆ V (MonoidHom.id (FreeGroup A)) Ω'.toSystem) {v : Fin Ω.numItems → FreeGroup A} :
    v ∈ (ofGHom φ).imageOf P₀ ↔ ∃ u, ∃ hu : u ∈ P₀, v = fun k ↦ CoordGroup.evalGHom u (hP₀ hu)
      (φ ((inr (FreeGroup.of k) : GX (FreeGroup A) (Fin Ω.numItems)) : Ω.coordGroup)) := by
  have key (u) (hu : u ∈ P₀) : GroupAlgGeom.wordMap (MonoidHom.id (FreeGroup A))
      (CoordGroup.exists_wordMap_representation _ _ _ φ).choose u = fun k ↦
        CoordGroup.evalGHom u (hP₀ hu)
          (φ ((inr (FreeGroup.of k) : GX (FreeGroup A) (Fin Ω.numItems)) : Ω.coordGroup)) := by
    funext k
    rw [apply_inr_of_eq_ofGHom, CoordGroup.evalGHom_mk, wordMap_apply]
  rw [ofGHom, imageOf_ofWordMap]
  exact ⟨fun ⟨u, hu, hv⟩ ↦ ⟨u, hu, hv ▸ key u hu⟩, fun ⟨u, hu, hv⟩ ↦ ⟨u, hu, hv ▸ key u hu⟩⟩

/-- Composing the homomorphism of a solution `U'` of `Ω'` with `φ` gives a point of `Ω` reached
through the branch of `φ` over every set of base points containing the point of `U'`. -/
theorem toHom_comp_mem_imageOf_ofGHom {P₀ : Set (Fin Ω'.numItems → FreeGroup A)}
    {U' : Ω'.Solution} (hU' : U'.point ∈ P₀) :
    (fun k ↦ U'.toHom (φ ((inr (FreeGroup.of k) : GX (FreeGroup A) (Fin Ω.numItems)) :
      Ω.coordGroup))) ∈ (ofGHom φ).imageOf P₀ := by
  rw [ofGHom, imageOf_ofWordMap]
  refine ⟨U'.point, hU', funext fun k ↦ ?_⟩
  rw [apply_inr_of_eq_ofGHom, Solution.toHom_mk, wordMap_apply]

end ofGHom

end Branch

/-- A solution of `Ω` is reached, over the point of its transfer, through the branch of the
homomorphism to the successor to which a transformation transfers it. -/
theorem Transformation.point_mem_imageOf_ofGHom {Ω : GenEq A} (T : Transformation Ω)
    (U : Ω.Solution) :
    U.point ∈ (Branch.ofGHom (T.hom (T.transfer U).1)).imageOf {(T.transfer U).2.point} := by
  have h : (fun k ↦ (T.transfer U).2.toHom (T.hom (T.transfer U).1
      ((inr (FreeGroup.of k) : GX (FreeGroup A) (Fin Ω.numItems)) : Ω.coordGroup))) = U.point := by
    funext k
    rw [Solution.point_apply, ← Solution.toHom_inr_of, ← T.toHom_transfer U, GHom.coe_comp,
      Function.comp_apply]
  exact h ▸ Branch.toHom_comp_mem_imageOf_ofGHom _ (Set.mem_singleton _)

namespace Branch

variable {Ω Ω' : GenEq A}

/-! ### The branch of one level -/

section ofLevel

variable {X : Type} [Finite X]

/-- The branch of one level `L` over the generalised equation `Ω'`, in the variables `X`, with a
word map `w` from the items of `Ω` to the variables of the level and the items of `Ω'` that sends
the solutions of `L` over `Ω'*` to group solutions of `Ω`. -/
def ofLevel (L : BlockLevel (GX (FreeGroup A) (Fin Ω'.numItems)) X)
    (w : Fin Ω.numItems → GX (FreeGroup A) (X ⊕ Fin Ω'.numItems))
    (hw : Set.MapsTo (GroupAlgGeom.wordMap (MonoidHom.id (FreeGroup A)) w)
      (V (MonoidHom.id (FreeGroup A)) (Block.cons (.base (S₀ := Ω'.toSystem)) X L).equations)
      (V (MonoidHom.id (FreeGroup A)) Ω.toSystem)) : Branch Ω Ω' where
  vars := X ⊕ Fin Ω'.numItems
  block := .cons .base X L
  wordMap := w
  mapsTo := hw

variable {L : BlockLevel (GX (FreeGroup A) (Fin Ω'.numItems)) X}
  {w : Fin Ω.numItems → GX (FreeGroup A) (X ⊕ Fin Ω'.numItems)}
  {hw : Set.MapsTo (GroupAlgGeom.wordMap (MonoidHom.id (FreeGroup A)) w)
    (V (MonoidHom.id (FreeGroup A)) (Block.cons (.base (S₀ := Ω'.toSystem)) X L).equations)
    (V (MonoidHom.id (FreeGroup A)) Ω.toSystem)}

/-- The points reached through the branch of one level over the base points `P₀`: the values of
the word map at a base point `u` and at the values at `u` of a solution of the level in the
coordinate group `F_{R(Ω')}`. -/
theorem mem_imageOf_ofLevel {P₀ : Set (Fin Ω'.numItems → FreeGroup A)}
    {v : Fin Ω.numItems → FreeGroup A} :
    v ∈ (ofLevel L w hw).imageOf P₀ ↔ ∃ u ∈ P₀, ∃ s : X → GX (FreeGroup A) (Fin Ω'.numItems),
      (fun x ↦ (s x : Ω'.coordGroup)) ∈
        V (QuotientGroup.mk' (Rad (MonoidHom.id (FreeGroup A)) Ω'.toSystem)) L.equations ∧
      v = GroupAlgGeom.wordMap (MonoidHom.id (FreeGroup A)) w
        (Sum.elim (fun x ↦ eval (MonoidHom.id (FreeGroup A)) u (s x)) u) := by
  -- the block of `ofLevel L w hw` is `cons base X L`, its word map `w`
  have h : (ofLevel L w hw).imageOf P₀ = GroupAlgGeom.wordMap (MonoidHom.id (FreeGroup A)) w ''
      (Block.cons (.base (S₀ := Ω'.toSystem)) X L).fundPoints P₀ := (rfl)
  rw [h, Set.mem_image]
  simp only [Block.mem_fundPoints_cons, Block.fundPoints_base]
  rw [Block.equations_base]
  constructor
  · rintro ⟨p, ⟨hp, s, hs, hps⟩, rfl⟩
    exact ⟨_, hp, s, hs, by rw [← hps, Sum.elim_comp_inl_inr]⟩
  · rintro ⟨u, hu, s, hs, rfl⟩
    exact ⟨Sum.elim (fun x ↦ eval (MonoidHom.id (FreeGroup A)) u (s x)) u,
      ⟨by rwa [Sum.elim_comp_inr], s, hs, by rw [Sum.elim_comp_inl, Sum.elim_comp_inr]⟩, rfl⟩

/-- **Composites through a level are fundamental.** Let `ψ : F_{R(Ω)} → F_{R(Ω')}` (in the source,
a canonical automorphism of `F_{R(Ω)}` followed by a canonical epimorphism) send each item of `Ω`
to the word `w` of that item evaluated at a solution `s` of the level `L` in `F_{R(Ω')}` and at
the items of `Ω'`. Then composing the homomorphism of a solution `U'` of `Ω'` with `ψ` gives a
point reached through the branch of `L` over every set of base points containing the point of
`U'`. -/
theorem toHom_comp_mem_imageOf_ofLevel {s : X → GX (FreeGroup A) (Fin Ω'.numItems)}
    (hs : (fun x ↦ (s x : Ω'.coordGroup)) ∈
      V (QuotientGroup.mk' (Rad (MonoidHom.id (FreeGroup A)) Ω'.toSystem)) L.equations)
    (ψ : GHom (CoordGroup.coeff (.id (FreeGroup A)) Ω.toSystem)
      (CoordGroup.coeff (.id (FreeGroup A)) Ω'.toSystem))
    (hψ : ∀ k, ψ ((inr (FreeGroup.of k) : GX (FreeGroup A) (Fin Ω.numItems)) : Ω.coordGroup) =
      (eval (inl : FreeGroup A →* GX (FreeGroup A) (Fin Ω'.numItems))
        (Sum.elim s fun z ↦ inr (FreeGroup.of z)) (w k) : Ω'.coordGroup))
    {P₀ : Set (Fin Ω'.numItems → FreeGroup A)} {U' : Ω'.Solution} (hU' : U'.point ∈ P₀) :
    (fun k ↦ U'.toHom (ψ ((inr (FreeGroup.of k) : GX (FreeGroup A) (Fin Ω.numItems)) :
      Ω.coordGroup))) ∈ (ofLevel L w hw).imageOf P₀ := by
  refine mem_imageOf_ofLevel.2 ⟨U'.point, hU', s, hs, funext fun k ↦ ?_⟩
  have h : GroupAlgGeom.wordMap (MonoidHom.id (FreeGroup A))
      (Sum.elim s fun z ↦ inr (FreeGroup.of z)) U'.point =
        Sum.elim (fun x ↦ eval (MonoidHom.id (FreeGroup A)) U'.point (s x)) U'.point := by
    funext z
    cases z <;> simp
  rw [hψ, Solution.toHom_mk, wordMap_apply, ← MonoidHom.comp_apply, eval_comp_eval, h]

end ofLevel

/-! ### Composition of branches -/

/-- **Branches compose.** A branch from `Ω` to `Ω'` followed by a branch from `Ω'` to `Ω''` is
reached through one branch from `Ω` to `Ω''`: over any base points, every point reached through
the first branch over the points reached through the second is reached through it. -/
theorem exists_comp {Ω'' : GenEq A} (b : Branch Ω Ω') (b' : Branch Ω' Ω'') :
    ∃ c : Branch Ω Ω'', ∀ P₀ : Set (Fin Ω''.numItems → FreeGroup A),
      b.imageOf (b'.imageOf P₀) ⊆ c.imageOf P₀ := by
  obtain ⟨Y'', B'', q, hq, hfund⟩ := b.block.exists_append b'.block b'.wordMap b'.mapsTo
  refine ⟨⟨Y'', B'', fun k ↦ eval (inl : FreeGroup A →* GX (FreeGroup A) Y'') q
    (b.wordMap k), mapsTo_wordMap_comp b.mapsTo hq⟩, fun P₀ ↦ ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨v', hv', rfl⟩ := hfund P₀ hv
  exact ⟨v', hv', by rw [wordMap_wordMap]⟩

/-! ### Examples -/

/-- The generalised equation `h₀ = h₁`: two items, each the only item of a base, the two bases
dual to each other. -/
private abbrev equalExample : GenEq A where
  numItems := 2
  numBases := 2
  left := ![0, 1]
  right := ![1, 2]
  left_lt_right := by decide
  sign := fun _ ↦ true
  dual := ![1, 0]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := ∅
  bounds_of_mem_connections := fun _ hc ↦ absurd hc (Finset.notMem_empty _)
  dual_mem_connections := fun _ hc ↦ absurd hc (Finset.notMem_empty _)

/-- The generalised equation with one item and no bases. -/
private abbrev oneItemExample : GenEq A where
  numItems := 1
  numBases := 0
  left := Fin.elim0
  right := Fin.elim0
  left_lt_right := fun μ ↦ μ.elim0
  sign := Fin.elim0
  dual := Fin.elim0
  dual_involutive := fun μ ↦ μ.elim0
  constBases := ∅
  connections := ∅
  bounds_of_mem_connections := fun _ hc ↦ absurd hc (Finset.notMem_empty _)
  dual_mem_connections := fun _ hc ↦ absurd hc (Finset.notMem_empty _)

private theorem mapsTo_equalExample {Y : Type} (y : Y) (s : Set (Y → FreeGroup A)) :
    Set.MapsTo (GroupAlgGeom.wordMap (MonoidHom.id (FreeGroup A))
      fun _ : Fin 2 ↦ inr (FreeGroup.of y)) s
      (V (MonoidHom.id (FreeGroup A)) (equalExample (A := A)).toSystem) := by
  intro v _
  have h₀ : (equalExample (A := A)).segment 0 1 true = [(Sum.inl 0, true)] :=
    equalExample.segment_succ 0 true
  have h₁ : (equalExample (A := A)).segment 1 2 true = [(Sum.inl 1, true)] :=
    equalExample.segment_succ 1 true
  refine (mem_V_toSystem_iff _).2 ((forall_mem_equations _).2 ⟨?_, by simp, by simp⟩)
  simp [Fin.forall_fin_two, h₀, h₁]

/-- The branch from `h₀ = h₁` to one free item `y`, without levels: both items are sent to `y`. -/
private def equalBranch : Branch (equalExample (A := A)) oneItemExample :=
  ofWordMap _ (mapsTo_equalExample 0 _)

/-- The branch from `h₀ = h₁` to one free item reaches exactly the pairs `(g, g)` with `g ≠ 1`,
the points of the solutions of `h₀ = h₁`. -/
example : (equalBranch (A := A)).image = {v | v 0 = v 1 ∧ v 0 ≠ 1} := by
  classical
  rw [equalBranch, image_def, imageOf_ofWordMap]
  ext v
  constructor
  · rintro ⟨_, ⟨U, rfl⟩, rfl⟩
    refine ⟨by simp, fun h1 ↦ U.word_ne_nil 0 ((U.isReduced_word 0).eq_of_mk_eq (by simp) ?_)⟩
    rw [← FreeGroup.one_eq_mk]
    simpa using h1
  · rintro ⟨h01, hv⟩
    refine ⟨_, ⟨Solution.ofNumBasesEqZero (Ω := oneItemExample) rfl rfl (fun _ ↦ (v 0).toWord)
      (fun _ ↦ FreeGroup.isReduced_toWord) fun _ ↦ by simpa using hv, rfl⟩, ?_⟩
    funext k
    fin_cases k <;> simp [h01, FreeGroup.mk_toWord]

/-- The branch from `h₀ = h₁` to the empty generalised equation with one level of one free
variable `x`, both items being sent to `x`, reaches every group solution `(g, g)` of `h₀ = h₁`
over the unique solution of the empty equation, `(1, 1)` included. -/
example : (ofLevel (Ω := equalExample (A := A)) (Ω' := empty) (X := Unit) (.level .empty)
    (fun _ ↦ inr (FreeGroup.of (.inl ()))) (mapsTo_equalExample _ _)).imageOf {Fin.elim0} =
      {v | v 0 = v 1} := by
  ext v
  rw [mem_imageOf_ofLevel]
  constructor
  · rintro ⟨u, -, s, -, rfl⟩
    simp
  · intro (h01 : v 0 = v 1)
    refine ⟨Fin.elim0, rfl, fun _ ↦ inl (v 0), by simp, funext fun k ↦ ?_⟩
    rw [wordMap_apply, eval_inr_of]
    refine Eq.trans ?_ (eval_inl (MonoidHom.id (FreeGroup A)) _ (v 0)).symm
    fin_cases k
    exacts [rfl, h01.symm]

end Branch

end TauCeti.GenEq
