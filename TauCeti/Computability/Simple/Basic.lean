/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Enumeration.Domain

/-!
# Immune and simple sets

A set is **immune** when it is infinite but has no infinite c.e. subset, and **simple** (Post) when
it is c.e. and its complement is immune. A simple set is c.e. but not computable, since its
complement is infinite and not c.e.

For sets of naturals, simplicity is equivalent to Post's family of positive requirements: a c.e.
coinfinite set `A` is simple exactly when it meets every infinite domain `W_c` of a code `c`. This
is the form in which constructions of simple sets meet their requirements.

## Main definitions

* `Set.Immune`: an infinite set with no infinite c.e. subset.
* `Set.Simple`: a c.e. set whose complement is immune.

## Main results

* `Set.Immune.not_rePred`: an immune set is not c.e.
* `Set.Simple.not_computablePred`: a simple set is not computable.
* `Set.simple_iff_forall_code`: a set of naturals is simple exactly when it is c.e., coinfinite,
  and meets the domain of every code whose domain is infinite.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter V.1.
-/

public section

open Nat.Partrec

namespace Set

variable {α : Type*} [Primcodable α]

/-- A set is **immune** when it is infinite and has no infinite c.e. subset. -/
structure Immune (X : Set α) : Prop where
  /-- An immune set is infinite. -/
  infinite : X.Infinite
  /-- An immune set contains no infinite c.e. set. -/
  not_subset : ∀ W : Set α, REPred (· ∈ W) → W.Infinite → ¬W ⊆ X

/-- An infinite subset of an immune set is immune. -/
theorem Immune.mono {X Y : Set α} (hX : X.Immune) (hYX : Y ⊆ X) (hY : Y.Infinite) : Y.Immune :=
  ⟨hY, fun W hW hWinf hWY => hX.not_subset W hW hWinf (hWY.trans hYX)⟩

/-- An immune set is not c.e. -/
theorem Immune.not_rePred {X : Set α} (hX : X.Immune) : ¬REPred (· ∈ X) :=
  fun h => hX.not_subset X h hX.infinite subset_rfl

/-- A set is **simple** (Post) when it is c.e. and its complement is immune: the complement is
infinite and contains no infinite c.e. set. -/
structure Simple (A : Set α) : Prop where
  /-- A simple set is c.e. -/
  rePred : REPred (· ∈ A)
  /-- The complement of a simple set is immune. -/
  immune_compl : Aᶜ.Immune

/-- The complement of a simple set is infinite. -/
theorem Simple.infinite_compl {A : Set α} (hA : A.Simple) : Aᶜ.Infinite :=
  hA.immune_compl.infinite

/-- **A simple set meets every infinite c.e. set.** -/
theorem Simple.inter_nonempty {A W : Set α} (hA : A.Simple) (hW : REPred (· ∈ W))
    (hWinf : W.Infinite) : (W ∩ A).Nonempty := by
  by_contra h
  exact hA.immune_compl.not_subset W hW hWinf fun x hxW hxA => h ⟨x, hxW, hxA⟩

/-- **A simple set is not computable**: otherwise its complement would be c.e. -/
theorem Simple.not_computablePred {A : Set α} (hA : A.Simple) : ¬ComputablePred (· ∈ A) :=
  fun h => hA.immune_compl.not_rePred h.not.to_re

/-- **Post's requirements characterize simple sets.** A set of naturals is simple exactly when it
is c.e., coinfinite, and meets the domain `W_c` of every code `c` whose domain is infinite. -/
theorem simple_iff_forall_code {A : Set ℕ} :
    A.Simple ↔ REPred (· ∈ A) ∧ Aᶜ.Infinite ∧
      ∀ c : Code, {x | (c.eval x).Dom}.Infinite → ({x | (c.eval x).Dom} ∩ A).Nonempty := by
  refine ⟨fun hA => ⟨hA.rePred, hA.infinite_compl, fun c hc =>
    hA.inter_nonempty c.rePred_dom_eval hc⟩, ?_⟩
  rintro ⟨hA, hAc, hreq⟩
  refine ⟨hA, hAc, fun W hW hWinf hWA => ?_⟩
  -- every c.e. set is the domain of a code
  obtain ⟨c, hc⟩ := TauCeti.Enumeration.rePred_iff_exists_code.1 hW
  have hWc : {x | (c.eval x).Dom} = W := Set.ext fun x => (hc x).symm
  obtain ⟨x, hxW, hxA⟩ := hreq c (hWc ▸ hWinf)
  exact hWA (hWc ▸ hxW) hxA

end Set
