/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.BorelComplete
import TauCeti.ModelTheory.RelationalConfiguration.BackAndForth
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.ModelTheory.Graph

/-!
# Examples of relabelling and Borel completeness

Relabelling along a bijection `e` moves the truth of an atom from `v` to `e ∘ v`: along the
3-cycle `0 ↦ 1 ↦ 2 ↦ 0` of `Fin 3`, a unary predicate true at `0` becomes true at `1`, not at `2`.
Relabelling there and back is the identity, and a class and its relabelling have Borel bireducible
isomorphism relations. The empty class is not Borel complete.

Over `ℕ`, relabelling the code of `P = {0}` along the transposition of `0` and `1` gives the code
of `P = {1}`, and agrees with the logic action of that transposition. On the carrier `Fin 0`, a
language without nullary symbols has a single code, and its isomorphism relation has one class;
with one nullary symbol there are two codes, both fixed by relabelling, in two classes.
-/

public section

open FirstOrder FirstOrder.Language TauCeti RelationalConfiguration

-- Along the 3-cycle `finRotate 3`, the value at `1` of the relabelled configuration is the value
-- at `0` of the original one: a predicate true at `0` becomes true at `1`.
example {L : Language} (R : L.Relations 1) (c : RelationalConfiguration L (Fin 3)) :
    (relabel (finRotate 3) c).eval (atom R ![1]) = c.eval (atom R ![0]) := by
  rw [eval_relabel, Atom.map_atom]
  congr 2
  ext i
  fin_cases i
  rfl

-- Relabelling along `e` and then along `e.symm` is the identity, and `simp` sees it.
example {L : Language} {α β : Type*} (e : α ≃ β) (c : RelationalConfiguration L α) :
    relabel e.symm (relabel e c) = c := by
  simp

-- The same holds along a permutation of one carrier: `relabel` stays the simp normal form, so the
-- logic action does not hide the round trip.
example {L : Language} (c : RelationalConfiguration L (Fin 3)) :
    relabel (finRotate 3).symm (relabel (finRotate 3) c) = c := by
  simp

-- Isomorphism on any class of configurations on `ℕ` is Borel bireducible with isomorphism on its
-- relabelling to `ℤ`.
example {L : Language} [L.IsRelational] (K : Set (RelationalConfiguration L ℕ)) :
    (classIso K).BorelBireducible (classIso (relabel Equiv.intEquivNat.symm '' K)) :=
  borelBireducible_classIso_image_relabel _ K

-- The empty class of graphs is not Borel complete.
example : ¬ BorelComplete (∅ : Set (RelationalConfiguration Language.graph ℕ)) :=
  not_borelComplete_empty

namespace TauCeti.RelationalConfiguration.RelabelChecks

/-! ### Relabelling along a transposition -/

-- Relabelling the code of `P = {0}` along the transposition `(0 1)` gives the code of `P = {1}`.
example {L : Language} (R : L.Relations 1) (c : RelationalConfiguration L ℕ)
    (hc : ∀ v, c.eval (atom R ![v]) = decide (v = 0)) (v : ℕ) :
    (relabel (Equiv.swap 0 1) c).eval (atom R ![v]) = decide (v = 1) := by
  rw [eval_relabel, Atom.map_atom_unary, Equiv.symm_swap, hc]
  simp [Equiv.swap_apply_eq_iff]

-- Relabelling along a permutation is the logic action of that permutation.
example {L : Language} (c : RelationalConfiguration L ℕ) :
    relabel (Equiv.swap 0 1) c = Equiv.swap 0 1 • c :=
  relabel_perm _ c

/-! ### The carrier `Fin 0` -/

/-- Over the empty carrier, every configuration is fixed by every relabelling. -/
private theorem relabel_fin_zero {L : Language} (e : Fin 0 ≃ Fin 0)
    (c : RelationalConfiguration L (Fin 0)) : relabel e c = c := by
  rw [Subsingleton.elim e (Equiv.refl _), relabel_refl, Homeomorph.refl_apply, id_eq]

/-- On the empty carrier, the classes of `classIso univ` are the codes. -/
private theorem card_quotient_classIso_univ_fin_zero {L : Language} [L.IsRelational] :
    Nat.card (Quotient (classIso (Set.univ : Set (RelationalConfiguration L (Fin 0))))) =
      Nat.card (RelationalConfiguration L (Fin 0)) :=
  Nat.card_congr ((Setoid.quotientTrivialEquiv _ fun _ _ h => Subtype.ext
    (eq_of_bfEquivSetoid_zero
      ((isoSetoid_iff_bfEquivSetoid_of_isEmpty (α := (0 : Ordinal.{0}))).1 h))).trans
    (Equiv.Set.univ _))

-- Without nullary symbols there is a single code on `Fin 0`, and a single class.
example {L : Language} [L.IsRelational] [IsEmpty (L.Relations 0)] :
    Nat.card (RelationalConfiguration L (Fin 0)) = 1 ∧
      Nat.card (Quotient (classIso (Set.univ : Set (RelationalConfiguration L (Fin 0))))) = 1 := by
  have : IsEmpty (Atom L (Fin 0)) :=
    ⟨fun a => (Atom.exists_eq_atom_of_isEmpty a).elim fun R _ => IsEmpty.elim inferInstance R⟩
  have : Unique (RelationalConfiguration L (Fin 0)) := equivFun.unique
  rw [card_quotient_classIso_univ_fin_zero, Nat.card_unique]
  exact ⟨rfl, rfl⟩

/-- The language with a single nullary relation symbol and no other symbols. -/
def nullaryLanguage : Language.{0, 0} where
  Functions _ := Empty
  Relations
    | 0 => Unit
    | _ + 1 => Empty

/-- `nullaryLanguage` has no function symbols. -/
instance isRelational_nullaryLanguage : nullaryLanguage.IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)

-- With one nullary symbol there are two codes on `Fin 0`, both fixed by relabelling, and two
-- classes: the nullary symbol holds in one code and fails in the other.
example : Nat.card (RelationalConfiguration nullaryLanguage (Fin 0)) = 2 ∧
    (∀ (e : Fin 0 ≃ Fin 0) (c : RelationalConfiguration nullaryLanguage (Fin 0)),
      relabel e c = c) ∧
    Nat.card (Quotient (classIso
      (Set.univ : Set (RelationalConfiguration nullaryLanguage (Fin 0))))) = 2 := by
  have e : Atom nullaryLanguage (Fin 0) ≃ Unit :=
    { toFun _ := ()
      invFun _ := atom (L := nullaryLanguage) (n := 0) () Fin.elim0
      left_inv a := by
        obtain ⟨R, rfl⟩ := Atom.exists_eq_atom_of_isEmpty a
        rfl
      right_inv _ := rfl }
  have hcard : Nat.card (RelationalConfiguration nullaryLanguage (Fin 0)) = 2 := by
    rw [Nat.card_congr (equivFun.trans (e.arrowCongr (Equiv.refl Bool)))]
    simp
  exact ⟨hcard, relabel_fin_zero, by rw [card_quotient_classIso_univ_fin_zero, hcard]⟩

end TauCeti.RelationalConfiguration.RelabelChecks
