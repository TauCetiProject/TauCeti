/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.SetTheory.Descriptive.CantorScheme

/-!
# Regression examples: Cantor antichains from Cantor schemes

These examples exercise the extraction from a downstream module, through public statements only:

* for a closure-antitone scheme of nonempty sets with vanishing diameter in a complete space,
  Mathlib's `CantorScheme.ClosureAntitone.map_of_vanishingDiam` discharges the hypothesis that the
  branch intersections are nonempty, so inequivalent siblings give a Cantor antichain on the root;
* for equality, siblings sharing no point give a continuous injection along the scheme, the
  situation of Mathlib's `CantorScheme.Disjoint.map_injective`.
-/

open CantorScheme

-- In a complete space, nonempty closure-antitone pieces have nonempty branch intersections.
example {α : Type*} [MetricSpace α] [CompleteSpace α] {A : List Bool → Set α}
    (hanti : ClosureAntitone A) (hdiam : VanishingDiam A) (hne : ∀ l, (A l).Nonempty)
    (E : Setoid α) (hcross : ∀ l, ∀ x ∈ A (false :: l), ∀ y ∈ A (true :: l), ¬ E x y) :
    E.HasCantorAntichainOn (A []) :=
  hdiam.hasCantorAntichainOn E
    (fun x => by
      have h := hanti.map_of_vanishingDiam hdiam hne
      exact (h ▸ Set.mem_univ x : x ∈ (inducedMap A).1))
    hcross

-- For equality, siblings sharing no point give a continuous injection along the scheme.
example {α : Type*} [PseudoMetricSpace α] {A : List Bool → Set α} (hdiam : VanishingDiam A)
    (hlim : ∀ x : ℕ → Bool, (⋂ n, A (PiNat.res x n)).Nonempty)
    (hdisj : ∀ l, ∀ x ∈ A (false :: l), ∀ y ∈ A (true :: l), x ≠ y) :
    ∃ f : (ℕ → Bool) → α, Continuous f ∧ Function.Injective f ∧
      ∀ a n, f a ∈ A (PiNat.res a n) := by
  obtain ⟨f, hf, hinj, hmem, -⟩ := hdiam.exists_antichain_map ⊥ hlim
    fun l x hx y hy hxy => hdisj l x hx y hy (by simpa [Setoid.bot_def] using hxy)
  exact ⟨f, hf, hinj, hmem⟩
