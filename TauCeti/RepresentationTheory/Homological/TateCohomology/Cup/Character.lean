/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Character
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Delta

/-!
# The low-degree Tate pairing with a character class

For a finite group `G`, the cup product pairs its additive abelianization, identified with
`Ĥ⁻²(G, ℤ)`, with the connecting class `δχ ∈ Ĥ²(G, ℤ)` of a character
`χ : Gᵃᵇ → ℚ/ℤ`. This file reduces that pairing to the concrete degree `(-2, 1)` product
with the character class: for `x ∈ Ĥ⁻²(G, ℤ)`, the product `x ∪ χ` is a class in
`Ĥ⁻¹(G, ℚ/ℤ)`, which is left unevaluated here. Identifying it with the value of the character
(and hence `x ∪ δχ` with the corresponding residue class in `Ĥ⁰(G, ℤ) = ℤ/|G|ℤ`) is a
subsequent step not established in this file.

This is the low-degree normalization that fixes the sign in the character description of the
Artin map: for `x ∈ Ĥ⁻²(G, ℤ)`, the class `x ∪ δχ` is the Tate connecting map of the tensored
sequence applied to `x ∪ χ`, with positive sign because `x` has even degree.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §3.
* J.-P. Serre, *Local Fields*, Chapter XI, §3.
-/

public noncomputable section

open CategoryTheory Rep

namespace TauCeti.TateCohomology

variable (G : Type) [Group G] [Fintype G]

/-- Cup product with the connecting class `δχ` is the connecting map of the tensored
sequence applied to the degree `(-2, 1)` cup product with the character class. The sign is positive
because the left degree is even. -/
theorem cup_characterConnectingClass_eq_tateδ
    (x : tateCohomology (Rep.trivial ℤ G ℤ) (-2))
    (χ : Additive (Abelianization G) →+ AddCircle (1 : ℚ)) :
    cup (Rep.trivial ℤ G ℤ) (Rep.ratAddCircleShortComplex G).X₁ (-2) 2 0 (by omega) x
        (characterConnectingClass G χ) =
      _root_.TateCohomology.δ
        (shortExact_map_tensorLeft_of_flat
          (Rep.ratAddCircleShortComplex_shortExact G) (Rep.trivial ℤ G ℤ)) (-1)
        (cup (Rep.trivial ℤ G ℤ) (Rep.ratAddCircleShortComplex G).X₃
          (-2) 1 (-1) (by omega) x
          (Rep.fromGroupCohomology (Rep.ratAddCircleShortComplex G).X₃ 1
            ((groupCohomology.H1IsoOfIsTrivial (Rep.ratAddCircleShortComplex G).X₃).inv
              (χ.comp Abelianization.of.toAdditive)))) := by
  rw [characterConnectingClass_eq_tateδ]
  have h := cup_δ_of_flat (Rep.trivial ℤ G ℤ)
    (Rep.ratAddCircleShortComplex_shortExact G) (p := (-2)) (q := 1) (n := (-1))
    (by omega) x
    (Rep.fromGroupCohomology (Rep.ratAddCircleShortComplex G).X₃ 1
      ((groupCohomology.H1IsoOfIsTrivial (Rep.ratAddCircleShortComplex G).X₃).inv
        (χ.comp Abelianization.of.toAdditive)))
  rw [Int.negOnePow_even _ (by use (-1); norm_num), one_smul] at h
  norm_num at h ⊢
  exact h

end TauCeti.TateCohomology
