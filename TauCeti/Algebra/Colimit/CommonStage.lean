/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Order.DirectedInverseSystem

/-!
# Moving finitely many elements of a directed colimit of rings to a common stage

Let `(Aᵢ, tᵢⱼ)` be a directed system of commutative rings over a directed preorder `ι`, and let
`φᵢ : Aᵢ → L` be compatible ring homomorphisms (`φⱼ ∘ tᵢⱼ = φᵢ`). The colimit conditions are
stated as hypotheses rather than for a particular construction, so the results apply to
Mathlib's `Ring.DirectLimit` with its canonical maps as well as to any other cocone with these
properties.

If every element of `L` comes from some stage, then finitely many elements of `L` come from a
common stage (`TauCeti.DirectLimit.exists_lift`). If moreover two elements of a stage with the
same image in `L` become equal at a later stage, then two pairs of elements of two stages with
the same images in `L` become equal at a common later stage
(`TauCeti.DirectLimit.exists_eq_eq_of_eq_eq`).

## Main results

* `TauCeti.DirectLimit.exists_lift`: finitely many elements of the colimit lift to a common stage.
* `TauCeti.DirectLimit.exists_eq_eq_of_eq_eq`: two pairs of elements with the same images in the
  colimit become equal at a common later stage.
-/

public section

namespace TauCeti.DirectLimit

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {A : ι → Type*} [∀ i, CommRing (A i)]
  {t : ∀ i j, i ≤ j → A i →+* A j} {L : Type*} [CommRing L] {φ : ∀ i, A i →+* L}
  (hφt : ∀ i j (h : i ≤ j) a, φ j (t i j h a) = φ i a)

include hφt in
/-- Finitely many elements of the colimit lift to a common stage. -/
theorem exists_lift (hcover : ∀ x : L, ∃ i a, φ i a = x) (S : Finset L) :
    ∃ i, ∃ g : L → A i, ∀ x ∈ S, φ i (g x) = x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨i, -⟩ := hcover 0
    exact ⟨i, 0, by simp⟩
  | insert a S _ ih =>
    obtain ⟨i, g, hg⟩ := ih
    obtain ⟨j, b, rfl⟩ := hcover a
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨k, fun x ↦ if x = φ j b then t j k hjk b else t i k hik (g x), fun x hx ↦ ?_⟩
    by_cases hxa : x = φ j b
    · simp only [hxa, ↓reduceIte, hφt]
    · simp only [hxa, ↓reduceIte, hφt]
      exact hg x ((Finset.mem_insert.mp hx).resolve_left hxa)

include hφt in
/-- Two pairs of elements of stages `i` and `j` with the same images in the colimit become equal
at a common later stage. -/
theorem exists_eq_eq_of_eq_eq [DirectedSystem A fun i j h ↦ t i j h]
    (hker : ∀ i (a b : A i), φ i a = φ i b → ∃ j, ∃ h : i ≤ j, t i j h a = t i j h b)
    {i j : ι} {a b : A i} {a' b' : A j} (ha : φ i a = φ j a') (hb : φ i b = φ j b') :
    ∃ k, ∃ (hik : i ≤ k) (hjk : j ≤ k),
      t i k hik a = t j k hjk a' ∧ t i k hik b = t j k hjk b' := by
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  have ha' : φ k (t i k hik a) = φ k (t j k hjk a') := by rw [hφt, hφt, ha]
  have hb' : φ k (t i k hik b) = φ k (t j k hjk b') := by rw [hφt, hφt, hb]
  obtain ⟨l, hkl, hal⟩ := hker k _ _ ha'
  obtain ⟨l', hkl', hbl'⟩ := hker k _ _ hb'
  obtain ⟨m, hlm, hl'm⟩ := directed_of (· ≤ ·) l l'
  refine ⟨m, hik.trans (hkl.trans hlm), hjk.trans (hkl.trans hlm), ?_, ?_⟩
  · have := congrArg (t l m hlm) hal
    simp only [DirectedSystem.map_map (f := fun i j h ↦ t i j h)] at this
    exact this
  · have := congrArg (t l' m hl'm) hbl'
    simp only [DirectedSystem.map_map (f := fun i j h ↦ t i j h)] at this
    exact this

end TauCeti.DirectLimit
