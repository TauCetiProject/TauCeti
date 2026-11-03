/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Pairing
import Mathlib.RepresentationTheory.Maschke
import TauCeti.RepresentationTheory.Semisimple

/-!
# Finite-group representations are determined by their characters

For a finite group over a field of characteristic zero, two finite-dimensional representations
with the same character are equivalent. Maschke's theorem makes them semisimple, and semisimple
representations with the same character are equivalent
(`Representation.nonempty_equiv_of_character_eq_of_isSemisimpleRepresentation`).

## Main results

* `Representation.nonempty_equiv_of_character_eq`: equal characters determine
  equivalent finite-dimensional representations.
* `FDRep.nonempty_iso_of_character_eq`: the bundled `FDRep` form.
* `FDRep.finrank_hom_eq_sum_of_character_eq`: an identity `χ_X = ∑ᵢ aᵢ • χ_{Yᵢ}` with
  natural-number coefficients gives `dim Hom(V, X) = ∑ᵢ aᵢ · dim Hom(V, Yᵢ)` for every `V`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part I, §§2.3 and 2.5.
* C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
  §§25 and 30.
-/

public section

namespace TauCeti

universe u v w

namespace Representation

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G] [CharZero k]
variable {V W : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- **For a finite group over a field of characteristic zero,
finite-dimensional representations are determined by their characters.** -/
theorem _root_.Representation.nonempty_equiv_of_character_eq (ρ : Representation k G V)
    (σ : Representation k G W) (hchar : ρ.character = σ.character) :
    Nonempty (ρ.Equiv σ) :=
  have : NeZero (Nat.card G : k) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  _root_.Representation.nonempty_equiv_of_character_eq_of_isSemisimpleRepresentation ρ σ hchar

end Representation

/-- **For a finite group over a field of characteristic zero, objects of
`FDRep` are determined by their characters.** -/
theorem _root_.FDRep.nonempty_iso_of_character_eq {k : Type u} {G : Type v}
    [Field k] [Group G] [Finite G] [CharZero k] (X Y : FDRep k G)
    (hchar : X.character = Y.character) : Nonempty (X ≅ Y) :=
  nonempty_fdRepIso_iff.mpr
    (Representation.nonempty_equiv_of_character_eq X.ρ Y.ρ hchar)

/-- **A character identity determines multiplicities.** For a finite group over a field of
characteristic zero, if the character of `X` is a combination `∑ᵢ aᵢ • χ_{Yᵢ}` of characters with
natural-number coefficients, then for every `V` the dimension of `Hom(V, X)` is
`∑ᵢ aᵢ · dim Hom(V, Yᵢ)`. -/
theorem _root_.FDRep.finrank_hom_eq_sum_of_character_eq {k : Type u} {G : Type v} [Field k]
    [Group G] [Finite G] [CharZero k] {ι : Type*} [Fintype ι] (V : FDRep k G) {X : FDRep k G}
    {Y : ι → FDRep k G} {a : ι → ℕ} (hX : X.character = ∑ i, a i • (Y i).character) :
    Module.finrank k (V ⟶ X) = ∑ i, a i * Module.finrank k (V ⟶ Y i) := by
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Invertible (Nat.card G : k) := invertibleOfNonzero (by simp)
  -- Pairing against the character of `V` is linear and turns each character into a dimension.
  have hclass : ClassFunction.ofFDRep X = ∑ i, a i • ClassFunction.ofFDRep (Y i) :=
    Subtype.ext <| funext fun g => by simp [hX]
  have hpair := congrArg (ClassFunction.characterPairing · (ClassFunction.ofFDRep V)) hclass
  simp only [map_sum, map_nsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    ClassFunction.characterPairing_ofFDRep_eq_finrank, nsmul_eq_mul] at hpair
  exact_mod_cast hpair

end TauCeti
