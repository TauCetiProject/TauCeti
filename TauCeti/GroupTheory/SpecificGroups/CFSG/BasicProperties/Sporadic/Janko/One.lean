/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.Enumeration
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Janko.One.PermutationModel

/-!
# An element of order `19` in the presented group of `J₁`

The classification list carries the first Janko group as the group `SporadicName.J1.Group`
defined by the transcribed ATLAS presentation

```text
⟨a, b | a², b³, (ab)⁷, (ab(abab⁻¹)³)⁵, (ab(abab⁻¹)⁶abab(ab⁻¹)²)²⟩
```

(`TauCeti.Sporadic.j1Presentation`). None of the five relators bounds the order of the word
`u = abab⁻¹` that the two long relators repeat. This file proves that `u ^ 19 = 1` in the presented
group, and hence, comparing with the permutation model, that `u` has order exactly `19` there.

The cyclic subgroup `⟨u⟩` is the largest cyclic subgroup of `J₁`, whose order is
`175560 = 9240 * 19`: bounding the presented group from above by coset enumeration over `⟨u⟩`
needs `9240` cosets and this bound on `⟨u⟩` itself.

The relation `u ^ 19 = 1` is a consequence of the five relators, obtained from a partial coset
enumeration over `⟨u⟩`: a replay that stops before the coset table closes still records a power of
`u` that is trivial in the presented group
(`TauCeti.CosetEnumeration.wordValue_pow_exponent_replay_eq_one`). Since `u ^ 19 = 1`, an
enumeration over `⟨u⟩` may record the elements of `⟨u⟩` it tracks as exponents modulo `19`.

In the signed letters of `TauCeti.CosetEnumeration.wordValue`, `0` is `a`, `2` is `b` and `3` is
`b⁻¹`, so `u` is the value of the word `[0, 2, 0, 3]`.

## Main results

* `TauCeti.SporadicName.wordValue_pow_eq_one_group_J1`: `(abab⁻¹) ^ 19 = 1` in the presented group
  of `J₁`.
* `TauCeti.SporadicName.orderOf_wordValue_group_J1`: `abab⁻¹` has order `19` there.

## References

* R. A. Wilson, R. A. Parker, and J. N. Bray, *ATLAS of Finite Group Representations*,
  version 3, `J₁`, section "Presentation",
  <https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J1/>.
* D. F. Holt, B. Eick and E. A. O'Brien, *Handbook of Computational Group Theory*, Chapman &
  Hall/CRC (2005), §5.3.3, for coset enumeration that tracks subgroup elements.
-/

public section

namespace TauCeti.SporadicName

open CosetEnumeration

/-- The parent codes of the certificate: the entry `c` for the point `p + 1` defines it as
`g_t * w_j` with `t = c % 4` and `j = c / 4`. -/
private def parentCodes : List ℕ :=
   [3, 4, 10, 2, 16, 22, 23, 24, 28, 34, 35, 38, 39, 44, 48, 58, 59, 62, 63, 64, 68, 72, 76, 83,
    87, 90, 94, 96, 108, 114, 119, 120, 124, 131, 134, 136, 140, 146, 151, 152, 156, 163, 166, 168,
    172]

/-- The step codes of the certificate: `0` defines the next point, `1` scans `abab⁻¹` at the point
`0`, and `k + 2` scans the rotation `k % 157` of the relators at the point `k / 157`. -/
private def stepCodes : List ℕ :=
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 162, 630, 1104, 944, 1101, 1732, 2046, 2056, 1572,
    1729, 1886, 2674, 2988, 2514, 2671, 2828, 2985, 3938, 4085, 3770, 4241, 4712, 4869, 5340, 5497,
    5968, 6125, 6596, 6753, 7205, 1504]

/-- The replay of the certificate records the exponent `19` for the word `abab⁻¹`, whose signed
letters are `[0, 2, 0, 3]`. -/
private theorem exponent_replay_J1 :
    (replay J1.presentation.generatorCount
      (J1.presentation.relatorLetters.map (List.map signedLetter)) [0, 2, 0, 3] parentCodes
      stepCodes).extra = 19 := by
  rw [presentation_J1, Sporadic.j1Presentation_generatorCount,
    Sporadic.j1Presentation_relatorLetters]
  decide +kernel

/-- **The relation `(abab⁻¹) ^ 19 = 1` holds in the presented group of `J₁`.** Here `abab⁻¹` is
the value of the signed word `[0, 2, 0, 3]` at the generators of the presented group. The relation
is a consequence of the five relators, none of which states it. -/
theorem wordValue_pow_eq_one_group_J1 :
    wordValue (PresentedGroup.of (rels := J1.presentation.relatorSet)) [0, 2, 0, 3] ^ 19 = 1 :=
  exponent_replay_J1 ▸
    J1.presentation.wordValue_pow_exponent_replay_eq_one [0, 2, 0, 3] parentCodes stepCodes

/-- The element `abab⁻¹` of the presented group of `J₁` is not the identity. -/
private theorem wordValue_ne_one :
    wordValue (PresentedGroup.of (rels := J1.presentation.relatorSet)) [0, 2, 0, 3] ≠ 1 := by
  rw [presentation_J1]
  intro h
  -- The canonical presentation map to the permutation model sends `abab⁻¹` to a permutation
  -- that moves the point `0`.
  let f := Sporadic.j1Presentation.homEquiv.symm
    ⟨Sporadic.J1.presentationImage, Sporadic.J1.lift_presentationImage_toFreeGroup_eq_one⟩
  have hcomp : ⇑f ∘ PresentedGroup.of = Sporadic.J1.presentationImage :=
    funext fun i ↦ GroupPresentation.homEquiv_symm_apply_of _ _ i
  have h0 : letter Sporadic.J1.presentationImage 0 = Sporadic.J1.a⁻¹ :=
    (letter_two_mul Sporadic.J1.presentationImage ⟨0, by simp⟩).trans
      Sporadic.J1.presentationImage_zero
  have h2 : letter Sporadic.J1.presentationImage 2 = Sporadic.J1.b⁻¹ :=
    (letter_two_mul Sporadic.J1.presentationImage ⟨1, by simp⟩).trans
      Sporadic.J1.presentationImage_one
  have h3 : letter Sporadic.J1.presentationImage 3 = Sporadic.J1.b⁻¹⁻¹ :=
    (letter_two_mul_add_one Sporadic.J1.presentationImage ⟨1, by simp⟩).trans
      (congrArg _ Sporadic.J1.presentationImage_one)
  have h' : wordValue Sporadic.J1.presentationImage [0, 2, 0, 3] = 1 := by
    simpa only [map_wordValue, map_one, hcomp] using congrArg f h
  simp only [wordValue_cons, wordValue_nil, h0, h2, h3] at h'
  exact absurd (DFunLike.congr_fun h' 0) (by decide +kernel)

/-- **The element `abab⁻¹` of the presented group of `J₁` has order `19`.** Here `abab⁻¹` is the
value of the signed word `[0, 2, 0, 3]` at the generators of the presented group. -/
theorem orderOf_wordValue_group_J1 :
    orderOf (wordValue (PresentedGroup.of (rels := J1.presentation.relatorSet)) [0, 2, 0, 3]) =
      19 :=
  have : Fact (Nat.Prime 19) := ⟨by decide⟩
  orderOf_eq_prime wordValue_pow_eq_one_group_J1 wordValue_ne_one

end TauCeti.SporadicName
