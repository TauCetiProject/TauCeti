/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.SetTheory.Descriptive.Silver
import TauCeti.SetTheory.Descriptive.Vitali

/-!
# Regression examples: the Vitali relation

The Vitali relation on `ℝ`, relating `x` and `y` when `y - x` is rational, is a second
non-smooth Borel equivalence relation alongside `E₀`:

* it is not smooth, because its quotient is not countably separated;
* it has a Cantor antichain on the whole line, by Silver's theorem: it does not have countably
  many classes, since its classes are countable, hence measurable, and a relation with countably
  many measurable classes is smooth;
* for the same reason equality on Cantor space is Borel reducible to it.

The Cantor antichain is obtained from Silver's dichotomy and non-smoothness alone, not from the
count of its classes. No Borel bireducibility with `E₀` is claimed.
-/

open Set TauCeti

-- The Vitali relation is not smooth: its quotient is not countably separated.
example : ¬ vitaliRel.IsSmooth :=
  Setoid.isSmooth_iff_countablySeparated.not.2 not_countablySeparated_quotient_vitaliRel

-- Silver's theorem gives a Cantor antichain on `ℝ`: countably many classes, each countable and
-- so measurable, would make the relation smooth.
example : vitaliRel.HasCantorAntichainOn univ :=
  (Setoid.silver_dichotomy vitaliRel measurableSet_vitaliRel).resolve_left fun _ =>
    Setoid.isSmooth_iff_countablySeparated.not.2 not_countablySeparated_quotient_vitaliRel
      (Setoid.isSmooth_of_countable_quotient fun x => (countable_setOf_vitaliRel x).measurableSet)

-- Equality on Cantor space is Borel reducible to the Vitali relation, which has uncountably many
-- classes for the same reason.
example : (⊥ : Setoid (ℕ → Bool)).BorelReducible vitaliRel :=
  (Setoid.borelReducible_bot_iff_not_countable_quotient vitaliRel measurableSet_vitaliRel).2
    fun _ => Setoid.isSmooth_iff_countablySeparated.not.2 not_countablySeparated_quotient_vitaliRel
      (Setoid.isSmooth_of_countable_quotient fun x => (countable_setOf_vitaliRel x).measurableSet)
