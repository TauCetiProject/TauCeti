/-
Copyright (c) 2026 Arthur Freitas Ramos, David Hulak, Ruy de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Hulak, Ruy de Queiroz,
  The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Arborescence
public import Mathlib.Combinatorics.Quiver.ConnectedComponent
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Option
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.Combinatorics.Quiver.WideSubquiver

/-!
# Cardinalities of arborescences

For a finite quiver, an arborescence has one fewer unoriented edge than vertices.  Consequently,
the complement of its underlying unoriented edges has cardinality equal to the total number of
directed edges plus one minus the number of vertices.

The spanning-tree edge count is adapted from the approach in
`LeanPool/FiniteGraphFundamentalGroup/Proof.lean` in `Vilin97/lean-pool` at commit
`38b8ba36899903cb7d3a42bb9f8a3f5c70fdb05f`.  That source is licensed under Apache-2.0 and
credits Arthur Freitas Ramos, David Hulak, and Ruy de Queiroz.  This version uses Mathlib's
`WideSubquiver` and arborescence APIs.

## Main results

* `arborescenceEdgeEquiv`: tree edges are in bijection with non-root vertices.
* `arborescenceEdgeCard`: the directed edges of a finite arborescence have
  cardinality one less than its vertices.
* `WideSubquiver.symmetrifiedTreeEdgeEquiv`: tree edges correspond to their unoriented edges.
* `WideSubquiver.symmetrifiedTreeEdgeMap`: forgets the orientation tag of a tree edge.
* `WideSubquiver.symmetrifiedTreeEdgeEquiv_apply`: the equivalence's forward equation.
* `WideSubquiver.symmetrifiedTreeSetCard`: a spanning tree has one fewer unoriented edge than
  vertices.
* `WideSubquiver.nonTreeEdgeCard`: the exact number of directed edges outside that tree.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Corollary 3.6.3.
-/

attribute [local implicit_reducible]
  Quiver.Symmetrify WideSubquiver WideSubquiver.toType WideSubquiver.quiver
  Quiver.symmetrifyQuiver Quiver.wideSubquiverSymmetrify

open Set Function
open Quiver

noncomputable section

public section

universe u v

namespace TauCeti

namespace WideSubquiver

variable {V : Type u} [Quiver.{v, u} V]

end WideSubquiver

private lemma existsLastData {W : Type u} [Quiver.{v, u} W] [Arborescence W]
    (b : W) (hb : b ≠ root W) :
    Nonempty (Σ a : W, Path (root W) a × (a ⟶ b)) := by
  let q : Path (root W) b := default
  cases q with
  | nil => exact False.elim (hb rfl)
  | cons p e => exact ⟨⟨_, p, e⟩⟩

private noncomputable def lastData {W : Type u} [Quiver.{v, u} W] [Arborescence W]
    (b : {b : W // b ≠ root W}) :
    Σ a : W, Path (root W) a × (a ⟶ b.1) :=
  Classical.choice (existsLastData b.1 b.2)

private lemma defaultPathLengthRoot {W : Type u} [Quiver.{v, u} W] [Arborescence W]
    (b : W) (h : b = root W) :
    (default : Path (root W) b).length = 0 := by
  cases h
  exact congrArg Path.length (Subsingleton.elim _ Path.nil)

private lemma targetNeRoot {W : Type u} [Quiver.{v, u} W] [Arborescence W]
    (e : Quiver.Total W) : e.right ≠ root W := by
  intro h
  let p : Path (root W) e.left := default
  have hp : (default : Path (root W) e.right) = p.cons e.hom := Subsingleton.elim _ _
  have hlen := congrArg Path.length hp
  have hzero := defaultPathLengthRoot e.right h
  simp [p, hzero] at hlen

/-- The directed edges of an arborescence correspond to the vertices other than its root. -/
noncomputable def arborescenceEdgeEquiv (W : Type u) [Quiver.{v, u} W] [Arborescence W] :
    Quiver.Total W ≃ {b : W // b ≠ root W} where
  toFun e := ⟨e.right, targetNeRoot e⟩
  invFun b :=
    let d := lastData b
    ⟨d.1, b.1, d.2.2⟩
  left_inv e := by
    let b : {b : W // b ≠ root W} := ⟨e.right, targetNeRoot e⟩
    let d := lastData b
    have hp : d.2.1.cons d.2.2 = (default : Path (root W) e.left).cons e.hom :=
      Subsingleton.elim _ _
    have hc := Path.cons.inj hp
    rcases hc with ⟨hab, -, hedge⟩
    exact Quiver.Total.ext hab rfl hedge
  right_inv b := by rfl

/-- The forward map of `arborescenceEdgeEquiv` sends an edge to its target vertex. -/
@[simp] theorem arborescenceEdgeEquiv_apply_val (W : Type u) [Quiver.{v, u} W] [Arborescence W]
    (e : Quiver.Total W) : (arborescenceEdgeEquiv W e).val = e.right := by
  rfl

/-- The directed edges of a finite arborescence have cardinality one less than its vertices. -/
@[simp] theorem arborescenceEdgeCard (W : Type u) [Quiver.{v, u} W] [Arborescence W] [Finite W] :
    Nat.card (Quiver.Total W) = Nat.card W - 1 := by
  classical
  exact (letI := Fintype.ofFinite W
    letI : Fintype (Quiver.Total W) := Fintype.ofEquiv _ (arborescenceEdgeEquiv W).symm
    show Nat.card (Quiver.Total W) = Nat.card W - 1 from by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        Fintype.card_congr (arborescenceEdgeEquiv W), Fintype.card_subtype_compl]
      simp)

namespace WideSubquiver

variable {V : Type u} [Quiver.{v, u} V]

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

/-- Forget the orientation tag of a tree edge to obtain its unoriented edge. -/
def symmetrifiedTreeEdgeMap (T : WideSubquiver (Symmetrify V))
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
    (e : Quiver.Total T) : symEdgeForgetInv T (symmetrifiedTreeEdgeMap T e) = e := by
  rcases e with ⟨a, b, ⟨f, hf⟩⟩
  -- The vertices of the symmetrification are definitionally a type synonym for `V`.
  change V at a b
  cases f using Sum.casesOn with
  | inl f =>
      simp only [symmetrifiedTreeEdgeMap, symEdgeForgetInv]
      exact dite_eq_left hf
  | inr f =>
      have hn : ¬T b a (Sum.inl f) := fun h => noReverseEdges T f h hf
      simp only [symmetrifiedTreeEdgeMap, symEdgeForgetInv]
      exact dite_eq_right hn

private lemma symEdgeForgetForgetInv
    (T : WideSubquiver (Symmetrify V))
    (e : Quiver.Total (wideSubquiverSymmetrify T)) :
    symmetrifiedTreeEdgeMap T (symEdgeForgetInv T e) = e := by
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

/-- The directed edges of a tree in the symmetrified quiver correspond to its unoriented edges. -/
def symmetrifiedTreeEdgeEquiv (T : WideSubquiver (Symmetrify V)) [Arborescence T] :
    Quiver.Total T ≃ Quiver.Total (wideSubquiverSymmetrify T) where
  toFun := symmetrifiedTreeEdgeMap T
  invFun := symEdgeForgetInv T
  left_inv := symEdgeForgetInvForget T
  right_inv := symEdgeForgetForgetInv T

/-- The forward map of `symmetrifiedTreeEdgeEquiv` forgets the orientation tag. -/
@[simp] theorem symmetrifiedTreeEdgeEquiv_apply (T : WideSubquiver (Symmetrify V))
    [Arborescence T] (e : Quiver.Total T) :
    symmetrifiedTreeEdgeEquiv T e = symmetrifiedTreeEdgeMap T e := by
  simp [symmetrifiedTreeEdgeEquiv]

/-- The forward map sends a tree edge with the forward orientation to the same ambient edge. -/
@[simp] theorem symmetrifiedTreeEdgeMap_apply_inl (T : WideSubquiver (Symmetrify V))
    {a b : V} (e : @Quiver.Hom V _ a b) (he : T a b (Sum.inl e)) :
    symmetrifiedTreeEdgeMap T ⟨a, b, ⟨Sum.inl e, he⟩⟩ = ⟨a, b, ⟨e, Or.inl he⟩⟩ := by
  simp [symmetrifiedTreeEdgeMap]

/-- The forward map reverses an edge tagged with the reverse orientation. -/
@[simp] theorem symmetrifiedTreeEdgeMap_apply_inr (T : WideSubquiver (Symmetrify V))
    {a b : V} (e : @Quiver.Hom V _ b a) (he : T a b (Sum.inr e)) :
    symmetrifiedTreeEdgeMap T ⟨a, b, ⟨Sum.inr e, he⟩⟩ = ⟨b, a, ⟨e, Or.inr he⟩⟩ := by
  simp [symmetrifiedTreeEdgeMap]

/-- The unoriented edges of an arborescence have cardinality one less than its vertex set. -/
@[simp] theorem symmetrifiedTreeSetCard [Finite V]
    (T : WideSubquiver (Symmetrify V)) [Arborescence T] :
    Nat.card (wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T) :
      Set (Quiver.Total V)) = Nat.card V - 1 := by
  let vertexEquiv : T ≃ V := Equiv.refl V
  exact (letI : Finite T := Finite.of_equiv V vertexEquiv.symm
    show _ from calc
      Nat.card (wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T) :
          Set (Quiver.Total V)) = Nat.card (Quiver.Total (wideSubquiverSymmetrify T)) :=
        Nat.card_congr (totalEquivSet (wideSubquiverSymmetrify T)).symm
      _ = Nat.card (Quiver.Total T) := Nat.card_congr (symmetrifiedTreeEdgeEquiv T).symm
      _ = Nat.card T - 1 := arborescenceEdgeCard T
      _ = Nat.card V - 1 := by rw [Nat.card_congr vertexEquiv])

private lemma finiteVertices_of_finiteTotal [Finite (Quiver.Total V)]
    (T : WideSubquiver (Symmetrify V)) [Arborescence T] : Finite V := by
  classical
  let vertexEquiv : T ≃ V := Equiv.refl V
  exact (letI : Finite (Quiver.Total (wideSubquiverSymmetrify T)) :=
      Finite.of_equiv _ (totalEquivSet (wideSubquiverSymmetrify T)).symm
    letI : Finite (Quiver.Total T) :=
      Finite.of_equiv _ (symmetrifiedTreeEdgeEquiv T).symm
    letI : Finite {b : T // b ≠ root T} :=
      Finite.of_equiv _ (arborescenceEdgeEquiv T)
    letI : Finite T := Finite.of_equiv _ (Equiv.optionSubtypeNe (root T))
    show Finite V from Finite.of_equiv T vertexEquiv)

/-- The directed edges outside the underlying unoriented spanning tree are exactly the total
number of directed edges plus one minus the number of vertices. -/
@[simp] theorem nonTreeEdgeCard [Finite (Quiver.Total V)]
    (T : WideSubquiver (Symmetrify V)) [Arborescence T] :
    Nat.card
        ((wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ :
          Set (Quiver.Total V)) =
    Nat.card (Quiver.Total V) + 1 - Nat.card V := by
  classical
  exact (letI : Fintype (Quiver.Total V) := Fintype.ofFinite _
    let A : Set (Quiver.Total V) :=
      wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T)
    letI : Fintype A := Fintype.ofFinite _
    letI : Finite V := finiteVertices_of_finiteTotal T
    letI := Fintype.ofFinite V
    -- Reuse finite cardinality lemmas without exposing chosen `Fintype` instances.
    show _ from by
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


end WideSubquiver

end TauCeti
