/-
Copyright (c) 2026 Arthur Freitas Ramos, David Hulak, Ruy de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Hulak, Ruy de Queiroz,
  The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Arborescence
public import Mathlib.Combinatorics.Quiver.ConnectedComponent
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.SetTheory.Cardinal.NatCard
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

* `totalEquivSubtypeNeRoot`: tree edges are in bijection with non-root vertices.
* `natCard_total_eq_natCard_sub_one`: the directed edges of a finite arborescence have
  cardinality one less than its vertices.
* `WideSubquiver.totalEquivTotalSymmetrify`: tree edges correspond to their unoriented edges.
* `WideSubquiver.totalEquivTotalSymmetrify_apply`: the equivalence's forward equation.
* `WideSubquiver.ncard_wideSubquiverSymmetrify`: a spanning tree has one fewer unoriented edge than
  vertices.
* `WideSubquiver.ncard_compl_wideSubquiverSymmetrify`: the exact number of directed edges
  outside that tree.

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

/-- The target of an edge in an arborescence is not its root. -/
theorem total_right_ne_root {W : Type u} [Quiver.{v, u} W] [Arborescence W]
    (e : Quiver.Total W) : e.right ≠ root W := by
  intro h
  let p : Path (root W) e.left := default
  have hp : (default : Path (root W) e.right) = p.cons e.hom := Subsingleton.elim _ _
  have hlen := congrArg Path.length hp
  have hzero := defaultPathLengthRoot e.right h
  simp [p, hzero] at hlen

/-- The directed edges of an arborescence correspond to the vertices other than its root. -/
noncomputable def totalEquivSubtypeNeRoot (W : Type u) [Quiver.{v, u} W] [Arborescence W] :
    Quiver.Total W ≃ {b : W // b ≠ root W} where
  toFun e := ⟨e.right, total_right_ne_root e⟩
  invFun b :=
    let d := lastData b
    ⟨d.1, b.1, d.2.2⟩
  left_inv e := by
    let b : {b : W // b ≠ root W} := ⟨e.right, total_right_ne_root e⟩
    let d := lastData b
    have hp : d.2.1.cons d.2.2 = (default : Path (root W) e.left).cons e.hom :=
      Subsingleton.elim _ _
    have hc := Path.cons.inj hp
    rcases hc with ⟨hab, -, hedge⟩
    exact Quiver.Total.ext hab rfl hedge
  right_inv b := by rfl

/-- The forward map of `totalEquivSubtypeNeRoot` sends an edge to its target vertex. -/
@[simp] theorem totalEquivSubtypeNeRoot_apply_val (W : Type u) [Quiver.{v, u} W] [Arborescence W]
    (e : Quiver.Total W) : (totalEquivSubtypeNeRoot W e).val = e.right := by
  rfl

/-- The directed edges of a finite arborescence have cardinality one less than its vertices. -/
@[simp] theorem natCard_total_eq_natCard_sub_one
    (W : Type u) [Quiver.{v, u} W] [Arborescence W] [Finite W] :
    Nat.card (Quiver.Total W) = Nat.card W - 1 := by
  classical
  rw [Nat.card_congr (totalEquivSubtypeNeRoot W)]
  have h' : Nat.card {b : W // b ≠ root W} + 1 = Nat.card W := by
    rw [← Finite.card_option, Nat.card_congr (Equiv.optionSubtypeNe (root W))]
  omega

/-- An arborescence with finitely many directed edges has finitely many vertices. -/
theorem finite_of_finite_total (W : Type u) [Quiver.{v, u} W] [Arborescence W]
    [Finite (Quiver.Total W)] : Finite W := by
  classical
  exact (letI : Finite {b : W // b ≠ root W} :=
      Finite.of_equiv _ (totalEquivSubtypeNeRoot W)
    letI : Finite W := Finite.of_equiv _ (Equiv.optionSubtypeNe (root W))
    inferInstance)

namespace WideSubquiver

variable {V : Type u} [Quiver.{v, u} V]

/-- An arborescence in a symmetrified quiver cannot contain both orientations of an arrow. -/
theorem not_inl_and_inr_of_arborescence (T : WideSubquiver (Symmetrify V)) [Arborescence T]
    {a b : V} (e : @Quiver.Hom V _ a b) :
    ¬ (Sum.inl e ∈ T a b ∧ Sum.inr e ∈ T b a) := by
  rintro ⟨h₁, h₂⟩
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

open scoped Classical in
private noncomputable def symEdgeForgetInv (T : WideSubquiver (Symmetrify V))
    (e : Quiver.Total (wideSubquiverSymmetrify T)) : Quiver.Total T :=
  match e with
  | ⟨a, b, ⟨(f : @Quiver.Hom V _ a b), hf⟩⟩ =>
      if h : Sum.inl f ∈ T a b then
        ⟨a, b, ⟨Sum.inl f, h⟩⟩
      else
        ⟨b, a, ⟨Sum.inr f, hf.resolve_left h⟩⟩

private lemma symEdgeForgetInv_of_inl (T : WideSubquiver (Symmetrify V))
    {a b : V} (f : @Quiver.Hom V _ a b)
    (hf : f ∈ wideSubquiverSymmetrify T a b) (h : Sum.inl f ∈ T a b) :
    symEdgeForgetInv T ⟨a, b, ⟨f, hf⟩⟩ = ⟨a, b, ⟨Sum.inl f, h⟩⟩ := by
  simp only [symEdgeForgetInv, dite_eq_left h]

private lemma symEdgeForgetInv_of_inr (T : WideSubquiver (Symmetrify V))
    {a b : V} (f : @Quiver.Hom V _ a b)
    (hf : f ∈ wideSubquiverSymmetrify T a b) (h : ¬Sum.inl f ∈ T a b) :
    symEdgeForgetInv T ⟨a, b, ⟨f, hf⟩⟩ =
      ⟨b, a, ⟨Sum.inr f, (mem_wideSubquiverSymmetrify_iff T f).mp hf |>.resolve_left h⟩⟩ := by
  simp only [symEdgeForgetInv, dite_eq_right h]

private lemma symEdgeForgetInvForget
    (T : WideSubquiver (Symmetrify V)) [Arborescence T]
    (e : Quiver.Total T) : symEdgeForgetInv T (totalWideSubquiverSymmetrify T e) = e := by
  rcases e with ⟨a, b, ⟨f, hf⟩⟩
  -- The vertices of the symmetrification are definitionally a type synonym for `V`.
  change V at a b
  cases f using Sum.casesOn with
  | inl f =>
      rw [totalWideSubquiverSymmetrify_apply_inl]
      exact symEdgeForgetInv_of_inl T (f := f) (Or.inl hf) hf
  | inr f =>
      have hn : ¬Sum.inl f ∈ T b a := fun h =>
        not_inl_and_inr_of_arborescence T f ⟨h, hf⟩
      rw [totalWideSubquiverSymmetrify_apply_inr]
      exact symEdgeForgetInv_of_inr T (f := f) (Or.inr hf) hn

private lemma symEdgeForgetForgetInv
    (T : WideSubquiver (Symmetrify V))
    (e : Quiver.Total (wideSubquiverSymmetrify T)) :
    totalWideSubquiverSymmetrify T (symEdgeForgetInv T e) = e := by
  rcases e with ⟨a, b, ⟨f, hf⟩⟩
  -- Remove the symmetrification's vertex type synonym before inspecting the orientation tag.
  change V at a b
  by_cases h : Sum.inl f ∈ T a b
  · rw [symEdgeForgetInv_of_inl T (f := f) hf h, totalWideSubquiverSymmetrify_apply_inl]
  · rw [symEdgeForgetInv_of_inr T (f := f) hf h, totalWideSubquiverSymmetrify_apply_inr]

/-- The directed edges of a tree in the symmetrified quiver correspond to its unoriented edges. -/
def totalEquivTotalSymmetrify (T : WideSubquiver (Symmetrify V)) [Arborescence T] :
    Quiver.Total T ≃ Quiver.Total (wideSubquiverSymmetrify T) where
  toFun := totalWideSubquiverSymmetrify T
  invFun := symEdgeForgetInv T
  left_inv := symEdgeForgetInvForget T
  right_inv := symEdgeForgetForgetInv T

/-- The forward map of `totalEquivTotalSymmetrify` forgets the orientation tag. -/
@[simp] theorem totalEquivTotalSymmetrify_apply (T : WideSubquiver (Symmetrify V))
    [Arborescence T] (e : Quiver.Total T) :
    totalEquivTotalSymmetrify T e = totalWideSubquiverSymmetrify T e := by
  simp [totalEquivTotalSymmetrify]

/-- The unoriented edges of an arborescence have cardinality one less than its vertex set. -/
@[simp] theorem ncard_wideSubquiverSymmetrify [Finite V]
    (T : WideSubquiver (Symmetrify V)) [Arborescence T] :
    (wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T) : Set (Quiver.Total V)).ncard =
      Nat.card V - 1 := by
  rw [← Nat.card_coe_set_eq]
  let vertexEquiv : T ≃ V := Equiv.refl V
  exact (letI : Finite T := Finite.of_equiv V vertexEquiv.symm
    show _ from calc
      Nat.card (wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T) :
          Set (Quiver.Total V)) = Nat.card (Quiver.Total (wideSubquiverSymmetrify T)) :=
        Nat.card_congr (totalEquivSet (wideSubquiverSymmetrify T)).symm
      _ = Nat.card (Quiver.Total T) := Nat.card_congr (totalEquivTotalSymmetrify T).symm
      _ = Nat.card T - 1 := natCard_total_eq_natCard_sub_one T
      _ = Nat.card V - 1 := by rw [Nat.card_congr vertexEquiv])

/-- A spanning arborescence on a quiver with finitely many total arrows has finitely many
vertices. -/
theorem finite_of_finite_total [Finite (Quiver.Total V)]
    (T : WideSubquiver (Symmetrify V)) [Arborescence T] : Finite V := by
  classical
  exact (letI : Finite (Quiver.Total (wideSubquiverSymmetrify T)) :=
      Finite.of_equiv _ (totalEquivSet (wideSubquiverSymmetrify T)).symm
    letI : Finite (Quiver.Total T) :=
      Finite.of_equiv _ (totalEquivTotalSymmetrify T).symm
    letI : Finite T := _root_.TauCeti.finite_of_finite_total T
    let vertexEquiv : T ≃ V := Equiv.refl V
    Finite.of_equiv T vertexEquiv)

/-- The directed edges outside the underlying unoriented spanning tree are exactly the total
number of directed edges plus one minus the number of vertices. -/
@[simp] theorem ncard_compl_wideSubquiverSymmetrify [Finite (Quiver.Total V)]
    (T : WideSubquiver (Symmetrify V)) [Arborescence T] :
    ((wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ :
      Set (Quiver.Total V)).ncard =
    Nat.card (Quiver.Total V) + 1 - Nat.card V := by
  classical
  let A : Set (Quiver.Total V) :=
    wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T)
  exact (letI : Finite V := finite_of_finite_total T
    letI : Nonempty V := ⟨root T⟩
    show _ from by
      have hle := Set.ncard_le_card A
      have hpos : 0 < Nat.card V := Nat.card_pos
      rw [Set.ncard_compl, ncard_wideSubquiverSymmetrify T]
      rw [ncard_wideSubquiverSymmetrify T] at hle
      omega)


end WideSubquiver

end TauCeti
