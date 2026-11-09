/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.SetTheory.Descriptive.Silver

/-!
# The beginning of the Borel reducibility order

Every Borel equivalence relation on a standard Borel space is Borel bireducible with equality
on a finite space or on `ℕ`, or admits a Borel reduction of equality on Cantor space. Thus the
finite and countably infinite equalities are the initial part of the Borel reducibility order;
all relations with uncountably many classes lie above equality on Cantor space.

For smooth relations the last alternative is also a normal form: a relation on a standard
Borel space is Borel bireducible with equality on Cantor space exactly when it is smooth and
has uncountably many classes. Smoothness itself ensures that its graph is Borel, so that
characterization needs no separate Borel-graph hypothesis.

## Main results

* `Setoid.borelReducibility_trichotomy`: the finite, countably infinite, and above-Cantor
  alternatives for a Borel equivalence relation.
* `Setoid.borelBireducible_bot_cantor_iff`: equality on Cantor space is the normal form for
  smooth relations with uncountably many classes.

## References

* S. Gao, *Invariant Descriptive Set Theory*, Chapman & Hall/CRC, 2009, Chapter 5
  (Borel reducibility and smooth equivalence relations).
* J. H. Silver, *Counting the number of equivalence classes of Borel and coanalytic equivalence
  relations*, Annals of Mathematical Logic 18 (1980), 1–28.
-/

public section

namespace Setoid

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] (E : Setoid X)

/-- A Borel equivalence relation on a standard Borel space is Borel bireducible with equality
on some `Fin n` or on `ℕ`, or equality on Cantor space is Borel reducible to it. The finite
alternative includes the empty space, with `n = 0`. -/
theorem borelReducibility_trichotomy (hE : MeasurableSet {p : X × X | E p.1 p.2}) :
    (∃ n : ℕ, E.BorelBireducible (⊥ : Setoid (Fin n))) ∨
      E.BorelBireducible (⊥ : Setoid ℕ) ∨
        (⊥ : Setoid (ℕ → Bool)).BorelReducible E := by
  by_cases hc : Countable (Quotient E)
  · exact (exists_borelBireducible_bot_fin_or_nat (fun _ => measurable_prodMk_left hE)).imp_right
      Or.inl
  · exact Or.inr (Or.inr ((E.borelReducible_bot_iff_not_countable_quotient hE).2 hc))

/-- A relation on a standard Borel space is Borel bireducible with equality on Cantor space
exactly when it is smooth and has uncountably many classes. No Borel-graph hypothesis is
necessary: smoothness implies that the graph is Borel. -/
theorem borelBireducible_bot_cantor_iff :
    E.BorelBireducible (⊥ : Setoid (ℕ → Bool)) ↔ E.IsSmooth ∧ ¬ Countable (Quotient E) := by
  rw [borelBireducible_iff, ← isSmooth_def]
  exact and_congr_right fun hs =>
    E.borelReducible_bot_iff_not_countable_quotient hs.measurableSet_setOf

end Setoid
