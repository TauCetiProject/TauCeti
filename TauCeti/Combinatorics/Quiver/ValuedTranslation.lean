/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Prefunctor
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.PNat.Basic
public import TauCeti.Basic.PEquiv

/-!
# Valued translation quivers

A **valuation** of a quiver assigns a pair `(a, b)` of positive integers to every arrow
(`TauCeti.QuiverValuation`). A **valued translation quiver** is a quiver with a valuation and a
partial injection `τ` of its vertices, the translation, such that for every vertex `z` on which
`τ` is defined and every vertex `w` there is an arrow `τ z ⟶ w` exactly when there is an arrow
`w ⟶ z`, and every arrow `τ z ⟶ w` carries the valuation of every arrow `w ⟶ z` with its two
entries exchanged (`TauCeti.IsValuedTranslationQuiver`). The translation is a Mathlib partial
equivalence `V ≃. V`.

This is the combinatorial shape of the valued Auslander-Reiten quiver of an Artin algebra: its
vertices are the isomorphism classes of indecomposable modules, an arrow `M ⟶ N` records a
nonzero space of irreducible morphisms with its two dimensions over the residue division rings of
`M` and `N` as valuation, and the translation is the Auslander-Reiten translate. The end terms
`τ C` and `C` of an almost-split sequence `0 ⟶ τ C ⟶ B ⟶ C ⟶ 0` have isomorphic residue division
rings, so an arrow `τ C ⟶ B` carries the valuation of `B ⟶ C` with its two entries exchanged; the
swap is visible when the residue division ring of the middle term `B` differs from theirs.

The file proves that the notion is transported along prefunctors which are surjective on vertices
and on arrows and respect the valuations and the translations
(`Prefunctor.isValuedTranslationQuiver_iff`), and that the opposite quiver, with the two entries
of every valuation exchanged and the inverse translation, is again a valued translation quiver
(`TauCeti.isValuedTranslationQuiver_op_iff`).

A valued quiver in the sense of the references has at most one arrow between two vertices, so it
is given by its valuation matrix `val : V → V → Option (ℕ+ × ℕ+)`; `TauCeti.ValuedQuiver val` is
that quiver, and `TauCeti.ValuedQuiver.isValuedTranslationQuiver_iff` turns the condition into an
identity of valuation matrices. The final section checks the definition on small examples,
including a violation of the swap condition.

The references also ask a translation quiver to be locally finite and to have no loops. These are
conditions on the quiver alone, not on its valuation or translation, and are not part of
`TauCeti.IsValuedTranslationQuiver`.

## Main definitions

* `TauCeti.QuiverValuation V`: the valuations of the quiver `V`, with the opposite valuation
  `TauCeti.QuiverValuation.op`.
* `TauCeti.IsValuedTranslationQuiver v τ`: `τ` is a translation of the quiver with valuation `v`.
* `TauCeti.ValuedQuiver val`: the quiver with at most one arrow between two vertices whose
  valuation matrix is `val`.

## Main results

* `Prefunctor.isValuedTranslationQuiver_iff`: invariance under surjective prefunctors respecting
  valuations and translations, in particular under isomorphisms of valued quivers.
* `TauCeti.isValuedTranslationQuiver_op_iff`: the opposite of a valued translation quiver.
* `TauCeti.ValuedQuiver.isValuedTranslationQuiver_iff`: the condition for a valuation matrix.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section VII.1, and Proposition VII.1.5 for the valuations under the
  translation.
-/

public section

open Opposite

universe v₁ v₂ u₁ u₂

namespace TauCeti

/-- A valuation of the quiver `V`: a pair of positive integers on every arrow. -/
abbrev QuiverValuation (V : Type u₁) [Quiver.{v₁} V] : Type (max u₁ v₁) :=
  ∀ ⦃x y : V⦄, (x ⟶ y) → ℕ+ × ℕ+

namespace QuiverValuation

variable {V : Type u₁} [Quiver.{v₁} V]

/-- The valuation of the opposite quiver: the reversed arrow of `f` carries the valuation of `f`
with its two entries exchanged. -/
def op (v : QuiverValuation V) : QuiverValuation Vᵒᵖ :=
  fun _ _ f ↦ (v f.unop).swap

@[simp]
theorem op_apply (v : QuiverValuation V) {x y : Vᵒᵖ} (f : x ⟶ y) : v.op f = (v f.unop).swap :=
  (rfl)

theorem op_apply_op (v : QuiverValuation V) {x y : V} (f : x ⟶ y) : v.op f.op = (v f).swap :=
  (rfl)

end QuiverValuation

/-- `τ` is a translation of the quiver `V` with valuation `v`: for every vertex `z` with
translate `x = τ z` and every vertex `w`, there is an arrow `x ⟶ w` exactly when there is an arrow
`w ⟶ z`, and the valuation of every arrow `x ⟶ w` is that of every arrow `w ⟶ z` with its two
entries exchanged. -/
structure IsValuedTranslationQuiver {V : Type u₁} [Quiver.{v₁} V] (v : QuiverValuation V)
    (τ : V ≃. V) : Prop where
  /-- The arrows out of the translate of `z` go to the vertices with an arrow into `z`. -/
  nonempty_hom_iff {z x : V} (hx : τ z = some x) (w : V) :
    Nonempty (x ⟶ w) ↔ Nonempty (w ⟶ z)
  /-- The valuation of an arrow out of the translate of `z` is that of an arrow into `z`, with
  the two entries exchanged. -/
  valuation_eq {z x : V} (hx : τ z = some x) {w : V} (f : w ⟶ z) (g : x ⟶ w) :
    v g = (v f).swap

variable {V : Type u₁} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W]

/-- Every valued quiver is a valued translation quiver for the empty translation. -/
theorem isValuedTranslationQuiver_bot (v : QuiverValuation V) : IsValuedTranslationQuiver v ⊥ where
  nonempty_hom_iff hx := by simp at hx
  valuation_eq hx := by simp at hx

namespace IsValuedTranslationQuiver

variable {v : QuiverValuation V} {τ : V ≃. V}

/-- The opposite of a valued translation quiver, with the two entries of every valuation
exchanged, is a valued translation quiver for the inverse translation. -/
theorem op (h : IsValuedTranslationQuiver v τ) : IsValuedTranslationQuiver v.op τ.symm.op where
  nonempty_hom_iff {z x} hx w := by
    rw [PEquiv.op_eq_some, PEquiv.eq_some_iff] at hx
    exact Quiver.Hom.opEquiv.nonempty_congr.symm.trans
      ((h.nonempty_hom_iff hx (unop w)).symm.trans Quiver.Hom.opEquiv.nonempty_congr)
  valuation_eq {z x} hx w f g := by
    rw [PEquiv.op_eq_some, PEquiv.eq_some_iff] at hx
    simp [h.valuation_eq hx g.unop f.unop]

end IsValuedTranslationQuiver

/-- The opposite quiver, with the two entries of every valuation exchanged and with the inverse
translation, is a valued translation quiver exactly when the quiver is. -/
@[simp]
theorem isValuedTranslationQuiver_op_iff {v : QuiverValuation V} {τ : V ≃. V} :
    IsValuedTranslationQuiver v.op τ.symm.op ↔ IsValuedTranslationQuiver v τ := by
  have hop {z x : V} (hx : τ z = some x) : τ.symm.op (op x) = some (op z) :=
    (PEquiv.op_eq_some _).2 ((PEquiv.eq_some_iff _).2 hx)
  refine ⟨fun h ↦ ⟨fun {z x} hx w ↦ ?_, fun {z x} hx w f g ↦ ?_⟩, fun h ↦ h.op⟩
  · rw [(Quiver.Hom.opEquiv (X := x) (Y := w)).nonempty_congr,
      (Quiver.Hom.opEquiv (X := w) (Y := z)).nonempty_congr]
    exact (h.nonempty_hom_iff (hop hx) (op w)).symm
  · have := h.valuation_eq (hop hx) g.op f.op
    rw [QuiverValuation.op_apply_op, QuiverValuation.op_apply_op, Prod.swap_swap] at this
    exact this.symm

end TauCeti

namespace Prefunctor

open TauCeti

variable {V : Type u₁} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W]

/-- Valued translation quivers are transported along a prefunctor which is surjective on vertices
and on the arrows between any two vertices, carries the valuation `v` to `v'` and the translation
`τ` to `τ'`. This covers isomorphisms of valued quivers compatible with the translations. -/
theorem isValuedTranslationQuiver_iff (F : V ⥤q W) (hobj : Function.Surjective F.obj)
    (hmap : ∀ x y : V, Function.Surjective (F.map : (x ⟶ y) → (F.obj x ⟶ F.obj y)))
    {v : QuiverValuation V} {v' : QuiverValuation W}
    (hv : ∀ ⦃x y : V⦄ (f : x ⟶ y), v' (F.map f) = v f)
    {τ : V ≃. V} {τ' : W ≃. W} (hτ : ∀ z x : V, τ' (F.obj z) = some (F.obj x) ↔ τ z = some x) :
    IsValuedTranslationQuiver v τ ↔ IsValuedTranslationQuiver v' τ' := by
  have hnonempty (x y : V) : Nonempty (F.obj x ⟶ F.obj y) ↔ Nonempty (x ⟶ y) :=
    ⟨fun ⟨f⟩ ↦ ⟨(hmap x y f).choose⟩, fun ⟨f⟩ ↦ ⟨F.map f⟩⟩
  constructor
  · intro h
    refine ⟨fun {z' x'} hx w' ↦ ?_, fun {z' x'} hx w' f' g' ↦ ?_⟩
    · obtain ⟨z, rfl⟩ := hobj z'
      obtain ⟨x, rfl⟩ := hobj x'
      obtain ⟨w, rfl⟩ := hobj w'
      rw [hnonempty, hnonempty]
      exact h.nonempty_hom_iff ((hτ z x).1 hx) w
    · obtain ⟨z, rfl⟩ := hobj z'
      obtain ⟨x, rfl⟩ := hobj x'
      obtain ⟨w, rfl⟩ := hobj w'
      obtain ⟨f, rfl⟩ := hmap w z f'
      obtain ⟨g, rfl⟩ := hmap x w g'
      rw [hv, hv]
      exact h.valuation_eq ((hτ z x).1 hx) f g
  · intro h
    refine ⟨fun {z x} hx w ↦ ?_, fun {z x} hx w f g ↦ ?_⟩
    · rw [← hnonempty, ← hnonempty]
      exact h.nonempty_hom_iff ((hτ z x).2 hx) (F.obj w)
    · rw [← hv, ← hv]
      exact h.valuation_eq ((hτ z x).2 hx) (F.map f) (F.map g)

end Prefunctor

namespace TauCeti

variable {V : Type u₁}

/-- The vertices of the valued quiver with valuation matrix `val`: one vertex for each element of
`V`, and an arrow `x ⟶ y` exactly when `val x y` is defined, valued by `val x y`. A valued quiver
with at most one arrow between any two vertices, as in the references, is of this form. -/
structure ValuedQuiver (val : V → V → Option (ℕ+ × ℕ+)) where
  /-- The vertex of the valued quiver at an element of `V`. -/
  of ::
  /-- The element of `V` underlying a vertex of the valued quiver. -/
  vertex : V
deriving DecidableEq

namespace ValuedQuiver

variable {val : V → V → Option (ℕ+ × ℕ+)}

/-- There is one arrow `x ⟶ y` for each pair `p` with `val x y = some p`, that is, at most one. -/
instance : Quiver (ValuedQuiver val) where
  Hom x y := {p : ℕ+ × ℕ+ // val x.vertex y.vertex = some p}

/-- The arrow `x ⟶ y` of the valued quiver, given its valuation. -/
def homMk {x y : ValuedQuiver val} {p : ℕ+ × ℕ+} (h : val x.vertex y.vertex = some p) : x ⟶ y :=
  ⟨p, h⟩

/-- The valuation of the valued quiver with valuation matrix `val`. -/
def valuation (val : V → V → Option (ℕ+ × ℕ+)) : QuiverValuation (ValuedQuiver val) :=
  fun _ _ f ↦ f.1

/-- The valuation of an arrow `x ⟶ y` is the value of the valuation matrix at `(x, y)`. -/
theorem eq_some_valuation {x y : ValuedQuiver val} (f : x ⟶ y) :
    val x.vertex y.vertex = some (valuation val f) :=
  f.2

@[simp]
theorem valuation_homMk {x y : ValuedQuiver val} {p : ℕ+ × ℕ+}
    (h : val x.vertex y.vertex = some p) : valuation val (homMk h) = p :=
  (rfl)

instance {x y : ValuedQuiver val} : Subsingleton (x ⟶ y) :=
  ⟨fun f g ↦ Subtype.ext <| Option.some_injective _ <|
    (eq_some_valuation f).symm.trans (eq_some_valuation g)⟩

/-- There is an arrow `x ⟶ y` exactly when the valuation matrix is defined at `(x, y)`. -/
theorem nonempty_hom_iff {x y : ValuedQuiver val} :
    Nonempty (x ⟶ y) ↔ (val x.vertex y.vertex).isSome := by
  constructor
  · rintro ⟨f⟩
    simp [eq_some_valuation f]
  · intro h
    exact ⟨homMk (Option.some_get h).symm⟩

/-- The condition of a valued translation quiver for a valuation matrix: whenever `τ z = x`, the
row of `x` is the column of `z` with the two entries of every valuation exchanged. -/
theorem isValuedTranslationQuiver_iff {τ : ValuedQuiver val ≃. ValuedQuiver val} :
    IsValuedTranslationQuiver (valuation val) τ ↔
      ∀ ⦃z x : ValuedQuiver val⦄, τ z = some x →
        ∀ w : ValuedQuiver val, val x.vertex w.vertex = (val w.vertex z.vertex).map Prod.swap := by
  constructor
  · intro h z x hx w
    cases hwz : val w.vertex z.vertex with
    | none =>
      have : ¬ Nonempty (x ⟶ w) := by
        rw [h.nonempty_hom_iff hx, nonempty_hom_iff, hwz]
        simp
      rw [nonempty_hom_iff, Option.not_isSome_iff_eq_none] at this
      simpa using this
    | some p =>
      obtain ⟨g⟩ := (h.nonempty_hom_iff hx w).2 ⟨homMk hwz⟩
      rw [eq_some_valuation g, h.valuation_eq hx (homMk hwz) g, valuation_homMk, Option.map_some]
  · intro H
    refine ⟨fun {z x} hx w ↦ ?_, fun {z x} hx w f g ↦ ?_⟩
    · rw [nonempty_hom_iff, nonempty_hom_iff, H hx, Option.isSome_map]
    · have := eq_some_valuation g
      rw [H hx, eq_some_valuation f, Option.map_some, Option.some_inj] at this
      exact this.symm

open PEquiv in
/-- The condition of a valued translation quiver for the translation which sends only `a` to `b`:
the row of `b` is the column of `a` with the two entries of every valuation exchanged. -/
theorem isValuedTranslationQuiver_single_iff [DecidableEq V] {a b : V} :
    IsValuedTranslationQuiver (valuation val) (single (of a) (of b)) ↔
      ∀ w : V, val b w = (val w a).map Prod.swap := by
  rw [isValuedTranslationQuiver_iff]
  constructor
  · exact fun h w ↦ h (single_apply (of a) (of b)) (of w)
  · rintro h z x hx ⟨w⟩
    rw [← Option.mem_def, mem_single_iff] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact h w

/-! ### Examples -/

open PEquiv

/-- Two vertices with an arrow in each direction, both valued `(1, 1)`, and the first vertex
translated to itself: the shape of the Auslander-Reiten quiver of `ℤ ⧸ p²ℤ`. -/
example :
    IsValuedTranslationQuiver (valuation (V := Fin 2) ![![none, some (1, 1)], ![some (1, 1), none]])
      (single (of 0) (of 0)) := by
  rw [isValuedTranslationQuiver_single_iff]
  decide

/-- A path `0 ⟶ 1 ⟶ 2` with valuations `(1, 2)` and `(2, 1)`, and `2` translated to `0`: the
shape of an almost-split sequence whose middle term has a residue division ring different from
that of its end terms. -/
example :
    IsValuedTranslationQuiver
      (valuation (V := Fin 3)
        ![![none, some (1, 2), none], ![none, none, some (2, 1)], ![none, none, none]])
      (single (of 2) (of 0)) := by
  rw [isValuedTranslationQuiver_single_iff]
  decide

/-- The opposite of the previous example, with valuations `(2, 1)` on `op 1 ⟶ op 0` and `(1, 2)`
on `op 2 ⟶ op 1`, is a valued translation quiver for the inverse translation. -/
example :
    IsValuedTranslationQuiver
      (valuation (V := Fin 3)
        ![![none, some (1, 2), none], ![none, none, some (2, 1)], ![none, none, none]]).op
      (single (of 2) (of 0)).symm.op := by
  rw [isValuedTranslationQuiver_op_iff, isValuedTranslationQuiver_single_iff]
  decide

/-- Giving the arrow `1 ⟶ 2` the same valuation `(1, 2)` as the translated arrow `0 ⟶ 1`, instead
of the exchanged pair `(2, 1)`, violates the condition. -/
example :
    ¬ IsValuedTranslationQuiver
      (valuation (V := Fin 3)
        ![![none, some (1, 2), none], ![none, none, some (1, 2)], ![none, none, none]])
      (single (of 2) (of 0)) := by
  rw [isValuedTranslationQuiver_single_iff]
  decide

end ValuedQuiver

end TauCeti
