/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Order.CompleteLattice.Basic

/-!
# Upper bounds for involutive mutations

For a family of involutions `μ` and lattice-valued charts `L`, the upper bound at `s`
is the meet of `L s` and the charts at its immediate neighbors. Local three-chart
inclusions imply invariance of this upper bound and identify it with the meet over
all finite mutation words. Words are evaluated by `List.foldl`, in reading order.

This is the order-theoretic part of the upper-bound argument in Berenstein–Fomin–Zelevinsky,
*Cluster algebras III: Upper bounds and double Bruhat cells*, §1 and §4.
-/

public section

namespace TauCeti.Mutation

variable {K V A : Type*} [CompleteLattice A]

/-- The meet of a chart with all of its one-step neighbors. -/
def upperBound (μ : K → V → V) (L : V → A) (s : V) : A :=
  L s ⊓ ⨅ k, L (μ k s)

variable (μ : K → V → V) (L : V → A)

/-- The upper bound is the meet of the initial and adjacent charts. -/
theorem upperBound_def (s : V) : upperBound μ L s = L s ⊓ ⨅ k, L (μ k s) :=
  (rfl)

/-- An element lies below the upper bound exactly when it lies below the initial
chart and every adjacent chart. -/
@[simp]
theorem le_upperBound_iff {a : A} {s : V} :
    a ≤ upperBound μ L s ↔ a ≤ L s ∧ ∀ k, a ≤ L (μ k s) := by
  simp [upperBound]

/-- The upper bound lies below the initial chart. -/
theorem upperBound_le (s : V) : upperBound μ L s ≤ L s :=
  inf_le_left

/-- The upper bound lies below each adjacent chart. -/
theorem upperBound_le_mutation (s : V) (k : K) : upperBound μ L s ≤ L (μ k s) :=
  inf_le_right.trans (iInf_le _ k)

/-- Local three-chart inclusions give one direction of upper-bound invariance.
Only the mutation direction being crossed needs to be involutive. -/
theorem upperBound_le_upperBound_mutation (k : K) (s : V)
    (hμ : Function.Involutive (μ k))
    (hlocal : ∀ j, k ≠ j → L s ⊓ L (μ k s) ⊓ L (μ j s) ≤ L (μ j (μ k s))) :
    upperBound μ L s ≤ upperBound μ L (μ k s) := by
  refine (le_upperBound_iff μ L).2 ⟨upperBound_le_mutation μ L s k, fun j ↦ ?_⟩
  by_cases hkj : k = j
  · subst j
    simpa only [hμ s] using upperBound_le μ L s
  · exact (le_inf (le_inf (upperBound_le μ L s)
      (upperBound_le_mutation μ L s k))
      (upperBound_le_mutation μ L s j)).trans (hlocal j hkj)

/-- Local three-chart inclusions at every state imply upper-bound invariance. -/
theorem upperBound_mutation
    (hμ : ∀ k, Function.Involutive (μ k))
    (hlocal : ∀ s i j, i ≠ j → L s ⊓ L (μ i s) ⊓ L (μ j s) ≤ L (μ j (μ i s)))
    (s : V) (k : K) : upperBound μ L (μ k s) = upperBound μ L s := by
  apply le_antisymm
  · simpa only [hμ k s] using
      upperBound_le_upperBound_mutation μ L k (μ k s) (hμ k) (hlocal (μ k s) k)
  · exact upperBound_le_upperBound_mutation μ L k s (hμ k) (hlocal s k)

/-- One-step upper-bound invariance extends to every word, without any further
assumption on the step maps. -/
theorem upperBound_foldl
    (hinv : ∀ s k, upperBound μ L (μ k s) = upperBound μ L s)
    (s : V) (w : List K) :
    upperBound μ L (w.foldl (fun t k ↦ μ k t) s) = upperBound μ L s := by
  induction w generalizing s with
  | nil => rfl
  | cons k w ih => exact (ih (μ k s)).trans (hinv s k)

/-- An invariant upper bound is precisely the meet of all charts reachable by
finite words. No finiteness or involutivity assumption is needed here. -/
theorem upperBound_eq_iInf_foldl
    (hinv : ∀ s k, upperBound μ L (μ k s) = upperBound μ L s) (s : V) :
    upperBound μ L s = ⨅ w : List K, L (w.foldl (fun t k ↦ μ k t) s) := by
  apply le_antisymm
  · refine le_iInf fun w ↦ ?_
    rw [← upperBound_foldl μ L hinv s w]
    exact upperBound_le μ L _
  · refine (le_upperBound_iff μ L).2 ⟨?_, fun k ↦ ?_⟩
    · exact (iInf_le (fun w : List K ↦ L (w.foldl (fun t k ↦ μ k t) s)) []).trans_eq
        (by simp)
    · exact (iInf_le (fun w : List K ↦ L (w.foldl (fun t k ↦ μ k t) s)) [k]).trans_eq
        (by simp)

/-- The local three-chart criterion identifies the upper bound with the
intersection of every reachable chart. -/
theorem upperBound_eq_iInf_foldl_of_local
    (hμ : ∀ k, Function.Involutive (μ k))
    (hlocal : ∀ s i j, i ≠ j → L s ⊓ L (μ i s) ⊓ L (μ j s) ≤ L (μ j (μ i s)))
    (s : V) :
    upperBound μ L s = ⨅ w : List K, L (w.foldl (fun t k ↦ μ k t) s) :=
  upperBound_eq_iInf_foldl μ L (upperBound_mutation μ L hμ hlocal) s

end TauCeti.Mutation
