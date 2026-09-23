/-
Copyright (c) 2026 Arthur Freitas Ramos, David Hulak, Ruy de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Hulak, Ruy de Queiroz,
  The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Arborescence
public import Mathlib.Combinatorics.Quiver.ConnectedComponent
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Option
public import Mathlib.SetTheory.Cardinal.Finite

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

universe u

namespace TauCeti

namespace WideSubquiver

variable {V : Type u} [Quiver.{u} V]

private noncomputable instance wideSubquiverVertexFintype [Fintype V]
    (T : WideSubquiver V) : Fintype T :=
  Fintype.ofEquiv V (Equiv.refl _)

private noncomputable instance symmetrifyFintype [Fintype V] : Fintype (Symmetrify V) :=
  Fintype.ofEquiv V (Equiv.refl _)

private def wideTotalEquiv (H : WideSubquiver V) :
    Quiver.Total H ≃ (wideSubquiverEquivSetTotal H : Set (Quiver.Total V)) where
  toFun e := ⟨⟨e.left, e.right, e.hom.val⟩, e.hom.property⟩
  invFun e := ⟨e.1.left, e.1.right, ⟨e.1.hom, e.2⟩⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

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

private lemma arborescenceCard [Finite V]
    (T : WideSubquiver V) [Arborescence T] :
    Nat.card (Quiver.Total T) = Nat.card V - 1 := by
  classical
  exact (letI := Fintype.ofFinite V
    letI : Fintype (Quiver.Total T) := Fintype.ofEquiv _ (treeEdgeEquiv T).symm
    show _ from by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        Fintype.card_congr (treeEdgeEquiv T), Fintype.card_subtype_compl]
      have hcard : Fintype.card T = Fintype.card V := Fintype.card_congr (Equiv.refl V)
      rw [hcard]
      simp)

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
theorem symmetrifiedTreeSetCard [Finite V]
    (T : WideSubquiver (Symmetrify V)) [Arborescence T] :
    Nat.card (wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T) :
      Set (Quiver.Total V)) = Nat.card V - 1 := by
  classical
  exact (letI := Fintype.ofFinite V
    letI : Fintype (Quiver.Total T) := Fintype.ofEquiv _ (treeEdgeEquiv T).symm
    letI : Fintype (Quiver.Total (wideSubquiverSymmetrify T)) :=
      Fintype.ofEquiv _ (symEdgeEquiv T)
    letI : Fintype (wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T) :
        Set (Quiver.Total V)) := Fintype.ofEquiv _ (wideTotalEquiv _)
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
theorem nonTreeEdgeCard [Finite (Quiver.Total V)]
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
    letI : Fintype (Quiver.Total (wideSubquiverSymmetrify T)) :=
      Fintype.ofEquiv _ (wideTotalEquiv _).symm
    letI : Fintype (Quiver.Total T) := Fintype.ofEquiv _ (symEdgeEquiv T).symm
    letI : Fintype {b : T // b ≠ root T} := Fintype.ofEquiv _ (treeEdgeEquiv T)
    let f : Option {b : T // b ≠ root T} → T := fun b => b.elim (root T) Subtype.val
    let hf : Function.Surjective f := by
      intro b
      by_cases h : b = root T
      · exact ⟨none, by simp [f, h]⟩
      · exact ⟨some ⟨b, h⟩, rfl⟩
    letI : Finite T := Finite.of_surjective f hf
    letI : Finite (Symmetrify V) := ‹Finite T›
    letI : Finite V := ‹Finite T›
    letI := Fintype.ofFinite V
    letI : Fintype (Quiver.Total T) := Fintype.ofEquiv _ (treeEdgeEquiv T).symm
    letI : Fintype (Quiver.Total (wideSubquiverSymmetrify T)) :=
      Fintype.ofEquiv _ (symEdgeEquiv T)
    letI : Fintype (wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T) :
        Set (Quiver.Total V)) := Fintype.ofEquiv _ (wideTotalEquiv _)
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
