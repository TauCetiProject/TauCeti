/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.DirectedInverseSystem

/-!
# Moving finitely many elements of a directed colimit to a common stage

Let `(Aᵢ, tᵢⱼ)` be a directed system of types over a directed preorder `ι`, and let `φᵢ : Aᵢ → L`
be compatible maps (`φⱼ ∘ tᵢⱼ = φᵢ`). The colimit conditions are stated as hypotheses rather than
for a particular construction, and only the underlying functions are used, so the results apply
to Mathlib's `Ring.DirectLimit` with its canonical maps as well as to any other cocone of rings,
modules or sets with these properties.

If every element of `L` comes from some stage, then finitely many elements of `L` come from a
common stage (`TauCeti.DirectLimit.exists_lift`), and finitely many images of elements of
subsets `Sᵢ ⊆ Aᵢ` preserved by the transition maps lift into a common `Sⱼ`
(`TauCeti.DirectLimit.exists_lift_mem`). If moreover two elements of a stage with the
same image in `L` become equal at a later stage, then two pairs of elements of two stages with
the same images in `L` become equal at a common later stage
(`TauCeti.DirectLimit.exists_eq_eq_of_eq_eq`).

## Main results

* `TauCeti.DirectLimit.exists_lift`: finitely many elements of the colimit lift to a common stage.
* `TauCeti.DirectLimit.exists_lift_mem`: finitely many images of elements of a compatible family
  of subsets `Sᵢ ⊆ Aᵢ` lift into a common `Sⱼ`.
* `TauCeti.DirectLimit.exists_eq_eq_of_eq_eq`: two pairs of elements with the same images in the
  colimit become equal at a common later stage.
-/

public section

namespace TauCeti.DirectLimit

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {A : ι → Type*}
  {t : ∀ i j, i ≤ j → A i → A j} {L : Type*} {φ : ∀ i, A i → L}
  (hφt : ∀ i j (h : i ≤ j) a, φ j (t i j h a) = φ i a)

include hφt in
/-- Finitely many elements of the colimit, each the image of an element of a family of subsets
`Sᵢ ⊆ Aᵢ` preserved by the transition maps, lift into `Sⱼ` at a common stage `j`. -/
theorem exists_lift_mem [Nonempty ι] [∀ i, Nonempty (A i)] (S : ∀ i, Set (A i))
    (hS : ∀ i j (h : i ≤ j), ∀ a ∈ S i, t i j h a ∈ S j) (X : Finset L)
    (hX : ∀ x ∈ X, ∃ i, ∃ a ∈ S i, φ i a = x) :
    ∃ i, ∃ g : L → A i, ∀ x ∈ X, g x ∈ S i ∧ φ i (g x) = x := by
  have hdir : Directed (· ⊆ ·) fun i ↦ φ i '' S i := fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨k, ?_, ?_⟩ <;> rintro _ ⟨a, ha, rfl⟩
    · exact ⟨t i k hik a, hS i k hik a ha, hφt i k hik a⟩
    · exact ⟨t j k hjk a, hS j k hjk a ha, hφt j k hjk a⟩
  obtain ⟨i, hi⟩ := hdir.exists_mem_subset_of_finset_subset_biUnion fun x hx ↦
    Set.mem_iUnion.mpr (hX x hx)
  exact ⟨i, Function.invFunOn (φ i) (S i), fun x hx ↦ Function.invFunOn_pos (hi hx)⟩

include hφt in
/-- Finitely many elements of the colimit lift to a common stage. -/
theorem exists_lift [Nonempty L] [∀ i, Nonempty (A i)] (hcover : ∀ x : L, ∃ i a, φ i a = x)
    (S : Finset L) :
    ∃ i, ∃ g : L → A i, ∀ x ∈ S, φ i (g x) = x := by
  have : Nonempty ι := ⟨(hcover (Classical.arbitrary L)).choose⟩
  obtain ⟨i, g, hg⟩ := exists_lift_mem hφt (fun _ ↦ Set.univ) (fun _ _ _ _ _ ↦ trivial) S
    fun x _ ↦ (hcover x).imp fun _ ⟨a, ha⟩ ↦ ⟨a, trivial, ha⟩
  exact ⟨i, g, fun x hx ↦ (hg x hx).2⟩

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
