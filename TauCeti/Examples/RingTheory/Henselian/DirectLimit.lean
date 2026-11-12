/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Henselian.DirectLimit

/-!
# Tests for Henselian pairs under directed colimits

The constant system of a Henselian pair, the zero ideals of an arbitrary directed system, and the
unit ideal of the zero ring all give Henselian pairs in the colimit.
-/

open Ring.DirectLimit

namespace TauCeti.Examples.HenselianDirectLimit

/-- *henselian_colimit_constant*: the constant identity system of a Henselian pair has a
Henselian colimit. -/
example (R : Type*) [CommRing R] (I : Ideal R) [HenselianRing R I] :
    HenselianRing (Ring.DirectLimit (fun _ : ℕ ↦ R) fun _ _ _ ↦ RingHom.id R)
      (⨆ i, I.map (of (fun _ : ℕ ↦ R) (fun _ _ _ ↦ RingHom.id R) i)) :=
  have : DirectedSystem (fun _ : ℕ ↦ R) fun _ _ _ ↦ RingHom.id R :=
    ⟨fun _ _ ↦ rfl, fun _ _ _ _ _ _ ↦ rfl⟩
  henselianRing (I := fun _ ↦ I) fun _ _ _ ↦ le_refl I

/-- *henselian_colimit_zero_ideal*: every directed colimit is Henselian along the colimit of the
zero ideals. -/
example {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] (G : ι → Type*)
    [∀ i, CommRing (G i)] (f : ∀ i j, i ≤ j → G i →+* G j) [DirectedSystem G (f · · ·)] :
    HenselianRing (Ring.DirectLimit G (f · · ·)) (⨆ i, (⊥ : Ideal (G i)).map (of G (f · · ·) i)) :=
  have (i : ι) : HenselianRing (G i) ⊥ := ⟨bot_le, fun _ _ a₀ h _ ↦ ⟨a₀, by simpa using h, by simp⟩⟩
  henselianRing fun _ _ _ ↦ bot_le

/-- *henselian_zero_ring*: in the zero ring the unit ideal equals the zero ideal, so the zero ring
is Henselian along it, and so is the colimit of the constant system. -/
example : HenselianRing (Ring.DirectLimit (fun _ : ℕ ↦ ZMod 1) fun _ _ _ ↦ RingHom.id (ZMod 1))
    (⨆ i, (⊤ : Ideal (ZMod 1)).map (of (fun _ : ℕ ↦ ZMod 1) (fun _ _ _ ↦ RingHom.id _) i)) :=
  have : DirectedSystem (fun _ : ℕ ↦ ZMod 1) fun _ _ _ ↦ RingHom.id (ZMod 1) :=
    ⟨fun _ _ ↦ rfl, fun _ _ _ _ _ _ ↦ rfl⟩
  have : HenselianRing (ZMod 1) ⊤ :=
    ⟨le_of_eq (Subsingleton.elim _ _), fun _ _ a₀ _ _ ↦ ⟨a₀, Subsingleton.elim _ _, by simp⟩⟩
  henselianRing (I := fun _ ↦ ⊤) fun _ _ _ ↦ le_top

end TauCeti.Examples.HenselianDirectLimit
