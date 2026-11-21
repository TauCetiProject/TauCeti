/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.Perfect

/-!
# The ATLAS presentation of the Tits group

The Tits group `²F₄(2)′` is the derived subgroup of the Ree group `²F₄(2)`, in which it has index
two; it is simple of order `17971200 = 2¹¹ · 3³ · 5² · 13`. This file records the ATLAS
presentation of the Tits group on its standard generators `a` and `b` as a
`TauCeti.GroupPresentation`:

```text
⟨ a, b | a², b³, (ab)¹³, [a,b]⁵, [a,bab]⁴, ((ab)⁴ab⁻¹)⁶ ⟩.
```

The presented group is the abstract group against which a concrete model of the Tits group, or
the group obtained from the root subgroups of `²F₄(2)`, is compared: a homomorphism out of it is
a pair of elements satisfying the six relations (`TauCeti.GroupPresentation.homEquiv`).

The source's commutator convention is `[r,s] = r⁻¹s⁻¹rs`, opposite to Mathlib's
`commutatorElement`, so each commutator is stored as `Relator.commInvInv r s`. The proved
`TauCeti.Relator.toWord_toFreeGroup` is the audit boundary between these expressions and the signed
words that `PresentedGroup` consumes.

The six entries follow the constructor `G<x,y>` of the ATLAS Magma source `TF42G1-P1.M`, whose
SHA-256 digest is `0034b6420e38051a82dc9742dae521c23e63657ae42da36f2180816986ac78f6` and whose
later assignments `a := x; b := y` fix the generator order. In particular the last relator is the
sixth power of the ten-letter word `ababababab⁻¹`, written there letter by letter; the ATLAS page
prints it as `((ab)⁴ab⁻¹)⁶`. The source records the length `143` of the presentation, which is the
total length of the compiled relators (`TauCeti.TitsGroup.presentation_totalLength`).

The only structural property proved here is perfectness: the relations `a² = b³ = (ab)¹³ = 1`
have pairwise coprime exponents. No order, finiteness or simplicity of the presented group is
asserted.

## Main definitions and results

* `TauCeti.TitsGroup.presentation`: the ATLAS presentation of the Tits group.
* `TauCeti.TitsGroup.presentation_transcribed` and the equations for the remaining fields: the
  characterization of the definition, whose body is not exposed.
* `TauCeti.TitsGroup.presentation_map_length_relators`,
  `TauCeti.TitsGroup.presentation_totalLength` and
  `TauCeti.TitsGroup.presentation_relatorsCyclicallyReduced`: three checks on the compiled words.
* `TauCeti.TitsGroup.isPerfect_presentation`: the presented group is perfect.

## References

* R. A. Wilson, R. A. Parker, J. N. Bray et al., *ATLAS of Finite Group Representations*,
  version 3, the page of the Tits group, <https://brauer.maths.qmul.ac.uk/Atlas/v3/exc/TF42/>,
  with the relators in the Magma source file
  <https://brauer.maths.qmul.ac.uk/Atlas/exc/TF42/mag/TF42G1-P1.M>.
* J. Tits, *Algebraic and abstract simple groups*, Annals of Mathematics 80 (1964), 313–329, for
  the group itself.
-/

public section

namespace TauCeti.TitsGroup

private abbrev a : Relator (Fin 2) := .gen 0

private abbrev b : Relator (Fin 2) := .gen 1

@[inherit_doc Relator.mul]
local infixl:70 " ⬝ " => Relator.mul

/-- The ATLAS presentation of the Tits group `²F₄(2)′` on its standard generators `a` and `b`:

```text
⟨ a, b | a², b³, (ab)¹³, [a,b]⁵, [a,bab]⁴, ((ab)⁴ab⁻¹)⁶ ⟩.
```

No structural property of the presented group is asserted by this definition: it records only the
cited generators and relations.

Generator order (starting at index zero): `a`, `b`.

Source: R. A. Wilson, R. A. Parker, J. N. Bray et al., ATLAS of Finite Group Representations,
version 3, https://brauer.maths.qmul.ac.uk/Atlas/v3/exc/TF42/, with the relator list in the Magma
source file https://brauer.maths.qmul.ac.uk/Atlas/exc/TF42/mag/TF42G1-P1.M

Generator convention: the ATLAS standard generators of the Tits group, that is, `a` in class 2A
and `b` of order 3 with `ab` of order 13, in that order, so index 0 is `a` and index 1 is `b`.
Products are read left to right, negative exponents denote inverses, and `[r,s]` denotes
`r⁻¹s⁻¹rs`.

Transcription notes: the six words of the source's relator list are stored as six relators equal
to the identity, in the order of the source. The last one is written there as the sixth power of
the product of the ten letters `a, b, a, b, a, b, a, b, a, b⁻¹`, and is stored in that form. -/
def presentation : GroupPresentation where
  generatorCount := 2
  expectedRelatorCount := 6
  transcribed :=
    [ .pow a 2,
      .pow b 3,
      .pow (a ⬝ b) 13,
      .pow (.commInvInv a b) 5,
      .pow (.commInvInv a (b ⬝ a ⬝ b)) 4,
      .pow (a ⬝ b ⬝ a ⬝ b ⬝ a ⬝ b ⬝ a ⬝ b ⬝ a ⬝ .inv b) 6 ]

/-- The ATLAS presentation of the Tits group has two generators. The body of the definition is
not exposed, so this is what lets a consumer see that it is a two-generator presentation. -/
@[simp]
theorem presentation_generatorCount : presentation.generatorCount = 2 := by
  simp [presentation]

/-- The relator count the source of the presentation states; see
`TauCeti.TitsGroup.presentation_generatorCount`. -/
@[simp]
theorem presentation_expectedRelatorCount : presentation.expectedRelatorCount = 6 := by
  simp [presentation]

/-- The six relator expressions of the ATLAS presentation of the Tits group, with their generator
indices written out.

The body of the definition is not exposed, so this is the equation that characterizes it: with
`TauCeti.GroupPresentation.relators_def` it determines the compiled words, and with
`TauCeti.GroupPresentation.mem_relatorSet_iff` it determines the relations defining
`TauCeti.GroupPresentation.Group`. Index `0` is the generator `a` and index `1` is `b`, and the
bounds come from `TauCeti.TitsGroup.presentation_generatorCount`. -/
@[simp]
theorem presentation_transcribed :
    presentation.transcribed =
      [
        -- a²
        .pow (.gen ⟨0, by simp⟩) 2,
        -- b³
        .pow (.gen ⟨1, by simp⟩) 3,
        -- (ab)¹³
        .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩) 13,
        -- [a,b]⁵, in the source's commutator convention
        .pow (.comm (.inv (.gen ⟨0, by simp⟩)) (.inv (.gen ⟨1, by simp⟩))) 5,
        -- [a,bab]⁴
        .pow (.comm (.inv (.gen ⟨0, by simp⟩))
          (.inv (.gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩))) 4,
        -- (ababababab⁻¹)⁶
        .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝
          .gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝
          .gen ⟨0, by simp⟩ ⬝ .inv (.gen ⟨1, by simp⟩)) 6 ] := by
  simp [presentation, Relator.commInvInv]

/-- The relator count recorded for the presentation agrees with the transcribed data. -/
theorem presentation_matchesMetadata : presentation.matchesMetadata := by decide

/-- The lengths of the six compiled relator words, in the order of the source. -/
theorem presentation_map_length_relators :
    presentation.relators.map List.length = [2, 3, 26, 20, 32, 60] := by
  simp [GroupPresentation.relators_def, presentation]

/-- The compiled relator words have `143` letters in total, the length that the source records
for this presentation. -/
theorem presentation_totalLength : presentation.totalLength = 143 := by
  rw [GroupPresentation.totalLength_def, presentation_map_length_relators]
  decide

/-- Every compiled relator word is cyclically reduced. This is what makes the letter count of
`TauCeti.TitsGroup.presentation_totalLength` comparable with the length the source records, which
is measured after free and cyclic reduction of each relator. -/
theorem presentation_relatorsCyclicallyReduced : presentation.relatorsCyclicallyReduced := by
  simp only [GroupPresentation.relatorsCyclicallyReduced_iff, GroupPresentation.relators_def,
    presentation, List.map_cons, List.map_nil, Relator.toWord_mul, Relator.toWord_pow,
    Relator.toWord_inv, Relator.toWord_commInvInv, Relator.toWord_gen]
  decide

/-- The group presented by the ATLAS presentation of the Tits group is perfect: the exponents of
the relations `a² = b³ = (ab)¹³ = 1` are pairwise coprime. -/
instance isPerfect_presentation : Group.IsPerfect presentation.Group := by
  apply presentation.isPerfect_of_coprime presentation_generatorCount (a := 2) (b := 3) (c := 13)
  · rw [presentation_transcribed]; simp
  · rw [presentation_transcribed]; simp
  · rw [presentation_transcribed]; simp
  all_goals decide

end TauCeti.TitsGroup
