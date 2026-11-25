/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.RelationalConfiguration.BorelComplete
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.ModelTheory.Graph

/-!
# Examples of relabelling and Borel completeness

Relabelling along a bijection `e` moves the truth of an atom from `v` to `e ∘ v`: along the
3-cycle `0 ↦ 1 ↦ 2 ↦ 0` of `Fin 3`, a unary predicate true at `0` becomes true at `1`, not at `2`.
Relabelling there and back is the identity, and a class and its relabelling have Borel bireducible
isomorphism relations. The empty class is not Borel complete.
-/

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
