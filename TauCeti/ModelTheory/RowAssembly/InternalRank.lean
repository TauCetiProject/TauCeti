/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RowAssembly.OmegaWitness
public import TauCeti.ModelTheory.Counting.Stratification
public import Mathlib.SetTheory.Cardinal.Continuum
import TauCeti.ModelTheory.RelationalConfiguration.Topology

/-!
# Internal Scott rank is not an isolating rank

Transporting `TauCeti.RowAssembly.OmegaWitness` and its companions
`TauCeti.RowAssembly.OmegaCompanion z` to relational configurations on `ℕ` yields:

* `TauCeti.RowAssembly.witnessCode`, a code on `ℕ` whose decoded structure has internal Scott rank
  `ω` and Scott height strictly above `ω`;
* `TauCeti.RowAssembly.not_isIsolatingRank_internalScottRank`: the internal Scott rank on codes
  is not an `TauCeti.IsIsolatingRank`;
* `TauCeti.RowAssembly.omega0_lt_of_isIsolatingRank`: every isolating rank strictly exceeds `ω` at
  `witnessCode`;
* `TauCeti.RowAssembly.mk_isoClasses_bfEquivSetoid_omega0_witnessCode`: the single
  `bfEquivSetoid ω`-class of `witnessCode` meets continuum many isomorphism classes.

## References

Adapted from the Cantor-family witness in Cameron Freer's `cameronfreer/infinitary-logic`,
`InfinitaryLogic/ModelTheory/FiberCantorFamily.lean` (checkpoint
`518a366cba97b1ae8c4dc64a297a396939bc3e0b`, Apache-2.0), transferred to
`TauCeti.RelationalConfiguration` and `TauCeti.IsIsolatingRank`.
-/

public section

namespace TauCeti.RowAssembly

open FirstOrder FirstOrder.Language Cardinal Ordinal TauCeti.RelationalConfiguration

/-- A relational configuration on `ℕ` encoding `OmegaWitness`. -/
noncomputable def witnessCode : RelationalConfiguration (lang ℕ Language.empty) ℕ :=
  (nonempty_equiv_of_countable.some : OmegaWitness ≃ ℕ).encodeVia

/-- A relational configuration on `ℕ` encoding the companion `OmegaCompanion z`. -/
noncomputable def companionCode (z : ℕ → Bool) :
    RelationalConfiguration (lang ℕ Language.empty) ℕ :=
  (nonempty_equiv_of_countable.some : OmegaCompanion z ≃ ℕ).encodeVia

/-- The decoded structure of `witnessCode` is isomorphic to `OmegaWitness`. -/
theorem nonempty_equiv_witnessCode :
    Nonempty (@Language.Equiv (lang ℕ Language.empty) OmegaWitness ℕ _
      witnessCode.toStructure) :=
  (nonempty_equiv_of_countable.some : OmegaWitness ≃ ℕ).nonempty_equiv_encodeVia
    (L := lang ℕ Language.empty)

/-- The decoded structure of `companionCode z` is isomorphic to `OmegaCompanion z`. -/
theorem nonempty_equiv_companionCode (z : ℕ → Bool) :
    Nonempty (@Language.Equiv (lang ℕ Language.empty) (OmegaCompanion z) ℕ _
      (companionCode z).toStructure) :=
  (nonempty_equiv_of_countable.some : OmegaCompanion z ≃ ℕ).nonempty_equiv_encodeVia
    (L := lang ℕ Language.empty)

/-- The decoded structure of `witnessCode` has internal Scott rank `ω`. -/
theorem internalScottRank_witnessCode :
    @internalScottRank (lang ℕ Language.empty) _ ℕ witnessCode.toStructure =
      Ordinal.omega0 := by
  obtain ⟨e⟩ := nonempty_equiv_witnessCode
  exact (@Language.Equiv.internalScottRank_eq (lang ℕ Language.empty) _ OmegaWitness _ ℕ
    witnessCode.toStructure e).symm.trans internalScottRank_omegaWitness

/-- The decoded structure of `witnessCode` has Scott height strictly greater than `ω`. -/
theorem omega0_lt_scottHeight_witnessCode :
    Ordinal.omega0 < @scottHeight (lang ℕ Language.empty) _ ℕ witnessCode.toStructure := by
  obtain ⟨e⟩ := nonempty_equiv_witnessCode
  rw [← @Language.Equiv.scottHeight_eq (lang ℕ Language.empty) _ OmegaWitness _ ℕ
    witnessCode.toStructure e]
  exact omega0_lt_scottHeight_omegaWitness

/-- The decoded structure of `witnessCode` has Scott height at most `ω + ω`. -/
theorem scottHeight_witnessCode_le :
    @scottHeight (lang ℕ Language.empty) _ ℕ witnessCode.toStructure ≤
      Ordinal.omega0 + Ordinal.omega0 := by
  simpa only [internalScottRank_witnessCode] using
    @scottHeight_le_internalScottRank_add_omega0 (lang ℕ Language.empty) _ ℕ
      witnessCode.toStructure

/-- Every companion code is `bfEquivSetoid ω`-equivalent to `witnessCode`. -/
theorem bfEquivSetoid_omega0_witnessCode_companionCode (z : ℕ → Bool) :
    bfEquivSetoid (lang ℕ Language.empty) ℕ Ordinal.omega0.{0}
      witnessCode (companionCode z) := by
  rw [witnessCode, companionCode, Equiv.bfEquivSetoid_encodeVia_iff]
  exact (bfEquiv_omega0_omegaCompanion_omegaWitness z).symm

/-- No companion code is isomorphic to `witnessCode`. -/
theorem not_isoSetoid_witnessCode_companionCode (z : ℕ → Bool) :
    ¬ isoSetoid (lang ℕ Language.empty) ℕ witnessCode (companionCode z) := by
  rw [witnessCode, companionCode, Equiv.isoSetoid_encodeVia_iff]
  rintro ⟨e⟩
  exact (isEmpty_equiv_omegaCompanion_omegaWitness z).false e.symm

/-- Distinct binary sequences yield non-isomorphic companion codes. -/
theorem not_isoSetoid_companionCode_of_ne {z z' : ℕ → Bool} (hz : z ≠ z') :
    ¬ isoSetoid (lang ℕ Language.empty) ℕ (companionCode z) (companionCode z') := by
  rw [companionCode, companionCode, Equiv.isoSetoid_encodeVia_iff]
  rintro ⟨e⟩
  exact (isEmpty_equiv_omegaCompanion hz).false e

/-- **The internal Scott rank is not an isolating rank.** Evaluated on relational configurations
on `ℕ` in `lang ℕ Language.empty`, `internalScottRank` fails `IsIsolatingRank`. -/
theorem not_isIsolatingRank_internalScottRank :
    ¬ IsIsolatingRank (L := lang ℕ Language.empty)
        (fun c => @internalScottRank (lang ℕ Language.empty) _ ℕ c.toStructure) := by
  intro h
  have hbf : bfEquivSetoid (lang ℕ Language.empty) ℕ
      (@internalScottRank (lang ℕ Language.empty) _ ℕ witnessCode.toStructure)
      witnessCode (companionCode fun _ => false) := by
    rw [internalScottRank_witnessCode]
    exact bfEquivSetoid_omega0_witnessCode_companionCode (fun _ => false)
  exact not_isoSetoid_witnessCode_companionCode (fun _ => false) (h.isolates hbf)

/-- Every isolating rank strictly exceeds `ω` at `witnessCode`. -/
theorem omega0_lt_of_isIsolatingRank
    {ρ : RelationalConfiguration (lang ℕ Language.empty) ℕ → Ordinal.{0}}
    (hρ : IsIsolatingRank ρ) : Ordinal.omega0 < ρ witnessCode := by
  refine lt_of_not_ge fun hle => ?_
  exact not_isoSetoid_witnessCode_companionCode (fun _ => false)
    (hρ.isolates_of_le hle (bfEquivSetoid_omega0_witnessCode_companionCode (fun _ => false)))

/-- The single `bfEquivSetoid ω`-class of `witnessCode` meets continuum many isomorphism
classes. -/
theorem mk_isoClasses_bfEquivSetoid_omega0_witnessCode :
    #(Quotient ((isoSetoid (lang ℕ Language.empty) ℕ).comap
      (Subtype.val :
        {d | bfEquivSetoid (lang ℕ Language.empty) ℕ
          Ordinal.omega0.{0} witnessCode d} → _))) = 𝔠 := by
  let K : Set (RelationalConfiguration (lang ℕ Language.empty) ℕ) :=
    {d | bfEquivSetoid (lang ℕ Language.empty) ℕ Ordinal.omega0.{0} witnessCode d}
  refine le_antisymm ?_ ?_
  · calc
      #(Quotient ((isoSetoid (lang ℕ Language.empty) ℕ).comap (Subtype.val : K → _)))
          ≤ #K := Cardinal.mk_quotient_le
      _ ≤ #(RelationalConfiguration (lang ℕ Language.empty) ℕ) := Cardinal.mk_set_le K
      _ ≤ 𝔠 := RelationalConfiguration.mk_le_continuum (lang ℕ Language.empty) ℕ
  · let f : (ℕ → Bool) →
        Quotient ((isoSetoid (lang ℕ Language.empty) ℕ).comap (Subtype.val : K → _)) :=
      fun z => Quotient.mk _ ⟨companionCode z, bfEquivSetoid_omega0_witnessCode_companionCode z⟩
    have hf : Function.Injective f := by
      intro z z' heq
      by_contra hne
      have hiso : isoSetoid (lang ℕ Language.empty) ℕ (companionCode z) (companionCode z') :=
        Quotient.exact
          (s := (isoSetoid (lang ℕ Language.empty) ℕ).comap (Subtype.val : K → _)) heq
      exact not_isoSetoid_companionCode_of_ne hne hiso
    have hcantor : #(ℕ → Bool) = 𝔠 := by simp
    exact hcantor ▸ Cardinal.mk_le_of_injective hf

end TauCeti.RowAssembly
