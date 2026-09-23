/-
Copyright (c) 2026 Arthur Freitas Ramos, David Hulak, Ruy de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Hulak, Ruy de Queiroz,
  The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.NielsenSchreier

/-!
# A spanning-tree basis for Schreier bounds

This file supplies the graph-theoretic core of the sharp Schreier inequality.  A geodesic
spanning tree in a free groupoid gives a basis of the vertex group indexed by the directed
edges outside the underlying unoriented tree.  For a finite quiver, the number of those
non-tree edges is the total number of directed edges plus one minus the number of vertices.

Applied to the action groupoid of a free group on its cosets, these statements give the
combinatorial count `1 + [G : U] * (d(G) - 1)`.  The action-groupoid specialization and the
topological transfer are left to the profinite Schreier module that consumes this API.

The explicit spanning-tree construction is adapted from the approach in
`LeanPool/FiniteGraphFundamentalGroup/Proof.lean` in `Vilin97/lean-pool` at commit
`38b8ba36899903cb7d3a42bb9f8a3f5c70fdb05f`.  That source is licensed under Apache-2.0 and
credits Arthur Freitas Ramos, David Hulak, and Ruy de Queiroz.  This version is rewritten for
Mathlib's `WideSubquiver`, `IsFreeGroupoid`, and `FreeGroupBasis` APIs.

## Main results

* `WideSubquiver.symmetrifiedTreeSetCard`: a spanning tree has one fewer unoriented edge than
  vertices.
* `WideSubquiver.nonTreeEdgeCard`: the exact number of directed edges outside that tree.
* `WideSubquiver.spanningTreeBasis`: the non-tree directed edges freely generate the vertex
  group.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Corollary 3.6.3.
-/

attribute [local implicit_reducible]
  Quiver.Symmetrify IsFreeGroupoid.Generators
  WideSubquiver WideSubquiver.toType WideSubquiver.quiver IsFreeGroupoid.quiverGenerators
  Quiver.symmetrifyQuiver Quiver.wideSubquiverSymmetrify
  IsFreeGroupoid.SpanningTree.homOfPath

open Set Function
open CategoryTheory CategoryTheory.ActionCategory CategoryTheory.SingleObj Quiver FreeGroup

noncomputable section

public section

universe u

namespace TauCeti

namespace WideSubquiver

variable {V : Type u} [Quiver.{u} V]

private def totalEquiv (T : WideSubquiver V) :
    Quiver.Total T ≃ Σ a : V, Σ b : V, {e : a ⟶ b // e ∈ T a b} where
  toFun e := ⟨e.left, e.right, ⟨e.hom.val, e.hom.property⟩⟩
  invFun e := ⟨e.1, e.2.1, ⟨e.2.2.1, e.2.2.2⟩⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

@[reducible]
private noncomputable def totalFintype [Fintype V] [∀ a b : V, Fintype (a ⟶ b)]
    (T : WideSubquiver V) : Fintype (Quiver.Total T) := by
  classical
  exact Fintype.ofEquiv _ (totalEquiv T).symm

private noncomputable instance totalFintypeInst [Fintype V]
    [∀ a b : V, Fintype (a ⟶ b)] (T : WideSubquiver V) :
    Fintype (Quiver.Total T) := totalFintype T

private noncomputable instance wideSubquiverHomFintype
    [∀ a b : V, Fintype (a ⟶ b)] (T : WideSubquiver V) (a b : T) :
    Fintype (@Quiver.Hom T T.quiver a b) := by
  classical
  exact Fintype.subtype (Finset.univ.filter fun e => e ∈ T a b) (by simp)

private noncomputable instance wideSubquiverVertexFintype [Fintype V]
    (T : WideSubquiver V) : Fintype T :=
  Fintype.ofEquiv V (Equiv.refl _)

private noncomputable instance symmetrifyFintype [Fintype V] : Fintype (Symmetrify V) :=
  Fintype.ofEquiv V (Equiv.refl _)

private noncomputable instance symmetrifyHomFintype [∀ a b : V, Fintype (a ⟶ b)]
    (a b : Symmetrify V) : Fintype (@Quiver.Hom (Symmetrify V) _ a b) := by
  -- An arrow in the symmetrified quiver is an original arrow in either orientation.
  change Fintype ((@Quiver.Hom V _ a b) ⊕ (@Quiver.Hom V _ b a))
  infer_instance

private def baseTotalEquiv : Quiver.Total V ≃ Σ a : V, Σ b : V, a ⟶ b where
  toFun e := ⟨e.left, e.right, e.hom⟩
  invFun e := ⟨e.1, e.2.1, e.2.2⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

private noncomputable instance baseTotalFintype [Fintype V]
    [∀ a b : V, Fintype (a ⟶ b)] : Fintype (Quiver.Total V) :=
  Fintype.ofEquiv _ baseTotalEquiv.symm

private def wideTotalEquiv (H : WideSubquiver V) :
    Quiver.Total H ≃ (wideSubquiverEquivSetTotal H : Set (Quiver.Total V)) where
  toFun e := ⟨⟨e.left, e.right, e.hom.val⟩, e.hom.property⟩
  invFun e := ⟨e.1.left, e.1.right, ⟨e.1.hom, e.2⟩⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

private noncomputable instance wideSubquiverSetTotalFintype [Fintype V]
    [∀ a b : V, Fintype (a ⟶ b)] (H : WideSubquiver V) :
    Fintype (wideSubquiverEquivSetTotal H : Set (Quiver.Total V)) :=
  Fintype.ofEquiv (Quiver.Total H) (wideTotalEquiv H)

private lemma existsLastData (T : WideSubquiver V) [Arborescence T]
    {b : T} (hb : b ≠ root T) :
    Nonempty (Σ a : T, Path (root T) a × (a ⟶ b)) := by
  let q : Path (root T) b := default
  cases q with
  | nil => exact False.elim (hb rfl)
  | cons p e => exact ⟨⟨_, p, e⟩⟩

private noncomputable def lastData (T : WideSubquiver V) [Arborescence T]
    (b : {b : T // b ≠ root T}) :
    Σ a : T, Path (root T) a × (a ⟶ b.1) :=
  Classical.choice (existsLastData T (b := b.1) b.2)

private lemma defaultPathLengthRoot (T : WideSubquiver V) [Arborescence T]
    (b : T) (h : b = root T) : (default : Path (root T) b).length = 0 := by
  cases h
  exact congrArg Path.length (Subsingleton.elim _ Path.nil)

private lemma targetNeRoot (T : WideSubquiver V) [Arborescence T]
    (e : Quiver.Total T) : e.right ≠ root T := by
  intro h
  let p : Path (root T) e.left := default
  have hp : (default : Path (root T) e.right) = p.cons e.hom := Subsingleton.elim _ _
  have hlen := congrArg Path.length hp
  have hzero := defaultPathLengthRoot T e.right h
  simp [p, hzero] at hlen

private noncomputable def treeEdgeEquiv (T : WideSubquiver V) [Arborescence T] :
    Quiver.Total T ≃ {b : T // b ≠ root T} where
  toFun e := ⟨e.right, targetNeRoot T e⟩
  invFun b :=
    let d := lastData T b
    ⟨d.1, b.1, d.2.2⟩
  left_inv e := by
    let b : {b : T // b ≠ root T} := ⟨e.right, targetNeRoot T e⟩
    let d := lastData T b
    have hp : d.2.1.cons d.2.2 = (default : Path (root T) e.left).cons e.hom :=
      Subsingleton.elim _ _
    have hc := Path.cons.inj hp
    rcases hc with ⟨hab, -, hedge⟩
    exact Quiver.Total.ext hab rfl hedge
  right_inv b := by rfl

private lemma arborescenceCard [Fintype V] [∀ a b : V, Fintype (a ⟶ b)]
    (T : WideSubquiver V) [Arborescence T] :
    Fintype.card (Quiver.Total T) = Fintype.card V - 1 := by
  classical
  rw [Fintype.card_congr (treeEdgeEquiv T), Fintype.card_subtype_compl]
  have hcard : Fintype.card T = Fintype.card V := Fintype.card_congr (Equiv.refl V)
  rw [hcard]
  simp

private lemma noReverseEdges (T : WideSubquiver (Symmetrify V)) [Arborescence T]
    {a b : V} (e : @Quiver.Hom V _ a b)
    (h₁ : T a b (Sum.inl e)) (h₂ : T b a (Sum.inr e)) : False := by
  let A : Arborescence T := inferInstance
  let p : Path (root T) a := (A.uniquePath a).default
  let q : Path (root T) b := (A.uniquePath b).default
  let f : @Quiver.Hom T T.quiver a b := ⟨Sum.inl e, h₁⟩
  let g : @Quiver.Hom T T.quiver b a := ⟨Sum.inr e, h₂⟩
  have hpq : q = p.cons f :=
    (A.uniquePath b).uniq q |>.trans ((A.uniquePath b).uniq (p.cons f)).symm
  have hqp : p = q.cons g :=
    (A.uniquePath a).uniq p |>.trans ((A.uniquePath a).uniq (q.cons g)).symm
  have hpqLen : q.length = p.length + 1 := by
    simpa only [Path.length_cons] using congrArg Path.length hpq
  have hqpLen : p.length = q.length + 1 := by
    simpa only [Path.length_cons] using congrArg Path.length hqp
  omega

private def symEdgeForget (T : WideSubquiver (Symmetrify V))
    (e : Quiver.Total T) : Quiver.Total (wideSubquiverSymmetrify T) := by
  rcases e with ⟨a, b, ⟨f, hf⟩⟩
  cases f using Sum.casesOn with
  | inl f => exact ⟨a, b, ⟨f, Or.inl hf⟩⟩
  | inr f => exact ⟨b, a, ⟨f, Or.inr hf⟩⟩

private def symEdgeForgetInv (T : WideSubquiver (Symmetrify V))
    (e : Quiver.Total (wideSubquiverSymmetrify T)) : Quiver.Total T := by
  rcases e with ⟨a, b, ⟨f, hf⟩⟩
  -- Membership in the forgotten subquiver records which of the two orientations lies in `T`.
  change T a b (Sum.inl f) ∨ T b a (Sum.inr f) at hf
  by_cases h : T a b (Sum.inl f)
  · exact ⟨a, b, ⟨Sum.inl f, h⟩⟩
  · exact ⟨b, a, ⟨Sum.inr f, hf.resolve_left h⟩⟩

private lemma symEdgeForgetInvForget
    (T : WideSubquiver (Symmetrify V)) [Arborescence T]
    (e : Quiver.Total T) : symEdgeForgetInv T (symEdgeForget T e) = e := by
  rcases e with ⟨a, b, ⟨f, hf⟩⟩
  -- The vertices of the symmetrification are definitionally a type synonym for `V`.
  change V at a b
  cases f using Sum.casesOn with
  | inl f =>
      simp only [symEdgeForget, symEdgeForgetInv]
      exact dite_eq_left hf
  | inr f =>
      have hn : ¬T b a (Sum.inl f) := fun h => noReverseEdges T f h hf
      simp only [symEdgeForget, symEdgeForgetInv]
      exact dite_eq_right hn

private lemma symEdgeForgetForgetInv
    (T : WideSubquiver (Symmetrify V))
    (e : Quiver.Total (wideSubquiverSymmetrify T)) :
    symEdgeForget T (symEdgeForgetInv T e) = e := by
  rcases e with ⟨a, b, ⟨f, hf⟩⟩
  -- Remove the symmetrification's vertex type synonym before inspecting the orientation tag.
  change V at a b
  -- The forgotten edge belongs to `T` in one of its two possible orientations.
  change T a b (Sum.inl f) ∨ T b a (Sum.inr f) at hf
  by_cases h : T a b (Sum.inl f)
  · have hinv : symEdgeForgetInv T ⟨a, b, ⟨f, hf⟩⟩ =
        ⟨a, b, ⟨Sum.inl f, h⟩⟩ := by
      simp only [symEdgeForgetInv]
      exact dite_eq_left h
    rw [hinv]
    rfl
  · have h' := hf.resolve_left h
    have hinv : symEdgeForgetInv T ⟨a, b, ⟨f, hf⟩⟩ =
        ⟨b, a, ⟨Sum.inr f, h'⟩⟩ := by
      simp only [symEdgeForgetInv]
      exact dite_eq_right h
    rw [hinv]
    rfl

private def symEdgeEquiv (T : WideSubquiver (Symmetrify V)) [Arborescence T] :
    Quiver.Total T ≃ Quiver.Total (wideSubquiverSymmetrify T) where
  toFun := symEdgeForget T
  invFun := symEdgeForgetInv T
  left_inv := symEdgeForgetInvForget T
  right_inv := symEdgeForgetForgetInv T

/-- The unoriented edges of an arborescence have cardinality one less than its vertex set. -/
theorem symmetrifiedTreeSetCard [Finite V] [∀ a b : V, Finite (a ⟶ b)]
    (T : WideSubquiver (Symmetrify V)) [Arborescence T] :
    Nat.card (wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T) :
      Set (Quiver.Total V)) = Nat.card V - 1 := by
  classical
  exact (letI := Fintype.ofFinite V
    letI : ∀ a b : V, Fintype (a ⟶ b) := fun a b => Fintype.ofFinite (a ⟶ b)
    -- Keep the finite instances local to this proof while retaining `Finite` in the public API.
    show _ from by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        ← Fintype.card_congr (wideTotalEquiv (wideSubquiverSymmetrify T)),
        ← Fintype.card_congr (symEdgeEquiv T)]
      have hcard : Fintype.card (Symmetrify V) = Fintype.card V :=
        Fintype.card_congr (Equiv.refl V)
      simpa [hcard] using arborescenceCard T
  )

/-- The directed edges outside the underlying unoriented spanning tree are exactly the total
number of directed edges plus one minus the number of vertices. -/
theorem nonTreeEdgeCard [Finite V] [∀ a b : V, Finite (a ⟶ b)]
    (T : WideSubquiver (Symmetrify V)) [Arborescence T] :
    Nat.card
        ((wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ :
          Set (Quiver.Total V)) =
    Nat.card (Quiver.Total V) + 1 - Nat.card V := by
  classical
  exact (letI := Fintype.ofFinite V
    letI : ∀ a b : V, Fintype (a ⟶ b) := fun a b => Fintype.ofFinite (a ⟶ b)
    -- Reuse finite cardinality lemmas without exposing chosen `Fintype` instances.
    show _ from by
      let A : Set (Quiver.Total V) :=
        wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T)
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      -- Express membership in the set complement as the negated predicate used by the card lemma.
      change Fintype.card {e : Quiver.Total V // e ∉ A} =
        Fintype.card (Quiver.Total V) + 1 - Fintype.card V
      have hcomplement := Fintype.card_subtype_compl (fun e : Quiver.Total V ↦ e ∈ A)
      have htree : Fintype.card A = Fintype.card V - 1 := by
        simpa only [Nat.card_eq_fintype_card] using symmetrifiedTreeSetCard T
      have hle : Fintype.card V - 1 ≤ Fintype.card (Quiver.Total V) := by
        rw [← htree]
        exact Fintype.card_subtype_le _
      have hvertices : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨root T⟩
      rw [htree] at hcomplement
      exact hcomplement.trans (by omega)
  )

/-- The loops attached to the directed edges outside an unoriented spanning tree form a free
basis of the vertex group at the root. -/
noncomputable def spanningTreeBasis
    {C : Type u} [Groupoid.{u} C] [IsFreeGroupoid C]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators C))) [Arborescence T] :
    FreeGroupBasis
      ((wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ : Set _)
      -- The tree root is an ambient object after reducing the wide-subquiver synonym.
      (End (show C from root T)) := by
  classical
  let X : Set _ := (wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ
  apply FreeGroupBasis.ofUniqueLift X
    (fun e => IsFreeGroupoid.SpanningTree.loopOfHom T (IsFreeGroupoid.of e.val.hom))
  intro Y _ f
  let f' : Labelling (IsFreeGroupoid.Generators C) Y := fun a b e =>
    if h : e ∈ wideSubquiverSymmetrify T a b then 1 else f ⟨⟨a, b, e⟩, h⟩
  rcases IsFreeGroupoid.unique_lift f' with ⟨F', hF', uF'⟩
  refine ⟨F'.mapEnd _, ?_, ?_⟩
  · suffices ∀ {x y} (q : x ⟶ y),
        F'.map (IsFreeGroupoid.SpanningTree.loopOfHom T q) = (F'.map q : Y) by
      rintro ⟨⟨a, b, e⟩, h⟩
      simp only [Functor.mapEnd, DFunLike.coe, this, hF']
      exact dite_eq_right h
    intro x y q
    suffices ∀ {a : C} (p : Path (root T) a),
        F'.map (IsFreeGroupoid.SpanningTree.homOfPath T p) = 1 by
      simp only [this, IsFreeGroupoid.SpanningTree.treeHom, comp_as_mul, inv_as_inv,
        IsFreeGroupoid.SpanningTree.loopOfHom, inv_one, mul_one, one_mul, Functor.map_inv,
        Functor.map_comp]
    intro a p
    induction p with
    | nil =>
        change F'.map (𝟙 (show C from root T)) = 1
        rw [F'.map_id, id_as_one]
    | cons p e ih =>
        rw [IsFreeGroupoid.SpanningTree.homOfPath, F'.map_comp, comp_as_mul, ih, mul_one]
        rcases e with ⟨e | e, eT⟩
        · rw [hF']
          exact dite_eq_left (Or.inl eT)
        · rw [F'.map_inv, inv_as_inv, inv_eq_one, hF']
          exact dite_eq_left (Or.inr eT)
  · intro E hE
    ext x
    suffices (IsFreeGroupoid.SpanningTree.functorOfMonoidHom T E).map x = F'.map x by
      simpa only [IsFreeGroupoid.SpanningTree.loopOfHom,
        IsFreeGroupoid.SpanningTree.functorOfMonoidHom, IsIso.inv_id,
        IsFreeGroupoid.SpanningTree.treeHom_root, Category.id_comp, Category.comp_id] using! this
    congr
    apply uF'
    intro a b e
    -- Expanding the labelling exposes the tree-edge case split used in its definition.
    change E (IsFreeGroupoid.SpanningTree.loopOfHom T _) = dite _ _ _
    split_ifs with h
    · rw [IsFreeGroupoid.SpanningTree.loopOfHom_eq_id T e h,
        ← CategoryTheory.End.one_def, E.map_one]
    · exact hE ⟨⟨a, b, e⟩, h⟩

end WideSubquiver

end TauCeti
