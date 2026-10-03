/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Character
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Connecting.GroupCohomology
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Delta

/-!
# The low-degree Tate pairing with a character class

For a finite group `G`, the cup product pairs its additive abelianization, identified with
`Ĥ⁻²(G, ℤ)`, with the connecting class `δχ ∈ Ĥ²(G, ℤ)` of a character
`χ : Gᵃᵇ → ℚ/ℤ`. This file reduces that pairing to the concrete degree `(-2, 1)` product
with the character class. Evaluating that last low-degree product gives the residue class in
`Ĥ⁰(G, ℤ) = ℤ/|G|ℤ` whose image in `ℚ/ℤ` is the value of the character.

This is the low-degree normalization that fixes the sign in the character description of the
Artin map. The proof compares the concrete degree-one connecting map in group cohomology with its
Tate counterpart, then applies the cup-product boundary law.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §3.
* J.-P. Serre, *Local Fields*, Chapter XI, §3.
-/

public noncomputable section

open CategoryTheory Rep

namespace TauCeti.TateCohomology

variable (G : Type) [Group G] [Fintype G]

private abbrev ratCircleRep : Rep ℤ G := Rep.trivial ℤ G (AddCircle (1 : ℚ))

/-- The canonical invariant in the first upward dimension shift of `ℚ/ℤ` attached to a
character. Its connecting image is the ordinary degree-one class of the character. -/
def characterDimensionShift
    (χ : Additive (Abelianization G) →+ AddCircle (1 : ℚ)) :
    (dimensionShiftUp (Rep.ratAddCircleShortComplex G).X₃).ρ.invariants := by
  -- The function `g ↦ χ(g)` changes under right translation by the constant function
  -- `χ(g)`, so its image in the coinduced quotient is invariant.
  let f : coindBot ℤ G (AddCircle (1 : ℚ)) :=
    (coindBotEquivPi ℤ G (AddCircle (1 : ℚ))).symm fun g ↦
      χ (Additive.ofMul (Abelianization.of g))
  refine ⟨(dimensionShiftUpπ (ratCircleRep G)).hom f, ?_⟩
  intro g
  rw [← Rep.hom_comm_apply (dimensionShiftUpπ (ratCircleRep G)) g f]
  have hfun : ((coindBot ℤ G (AddCircle (1 : ℚ))).ρ g) f =
      f + (coindBotUnit (ratCircleRep G)).hom
        (χ (Additive.ofMul (Abelianization.of g))) := by
    apply (coindBotEquivPi ℤ G (AddCircle (1 : ℚ))).injective
    rw [map_add]
    funext h
    rw [coindBotEquivPi_apply, coindBot_ρ_apply_coe]
    simp only [Pi.add_apply]
    rw [coindBotEquivPi_apply, coindBotEquivPi_apply,
      coindBotEquivPi_symm_apply_coe, coindBotUnit_hom_apply_coe]
    simp only [Representation.trivial_apply]
    rw [map_mul, ofMul_mul, map_add]
  rw [hfun, map_add]
  have hzero : (dimensionShiftUpπ (ratCircleRep G)).hom
      ((coindBotUnit (ratCircleRep G)).hom
        (χ (Additive.ofMul (Abelianization.of g)))) = 0 := by
    rw [← ConcreteCategory.comp_apply,
      coindBotUnit_comp_dimensionShiftUpπ (ratCircleRep G)]
    rfl
  rw [hzero, add_zero]

/-- The connecting isomorphism sends `characterDimensionShift` to the standard Tate
degree-one class of the character. -/
theorem dimensionShiftUpIso_characterDimensionShift
    (χ : Additive (Abelianization G) →+ AddCircle (1 : ℚ)) :
    (dimensionShiftUpIso (Rep.ratAddCircleShortComplex G).X₃ 0).hom
        (H0π (dimensionShiftUp (Rep.ratAddCircleShortComplex G).X₃)
          (characterDimensionShift G χ)) =
      Rep.fromGroupCohomology (Rep.ratAddCircleShortComplex G).X₃ 1
        ((groupCohomology.H1IsoOfIsTrivial (Rep.ratAddCircleShortComplex G).X₃).inv
          (χ.comp Abelianization.of.toAdditive)) := by
  let S := ShortComplex.mk (coindBotUnit (ratCircleRep G))
    (dimensionShiftUpπ (ratCircleRep G))
    (coindBotUnit_comp_dimensionShiftUpπ (ratCircleRep G))
  have hS : S.ShortExact := by
    simpa only [S, dimensionShiftUpSES_def] using
      dimensionShiftUpSES_shortExact (ratCircleRep G)
  let f : coindBot ℤ G (AddCircle (1 : ℚ)) :=
    (coindBotEquivPi ℤ G (AddCircle (1 : ℚ))).symm fun g ↦
      χ (Additive.ofMul (Abelianization.of g))
  let c : G → AddCircle (1 : ℚ) := fun g ↦
    χ (Additive.ofMul (Abelianization.of g))
  have hc : S.f.hom ∘ c = groupCohomology.d₀₁ S.X₂ f := by
    funext g
    apply (coindBotEquivPi ℤ G (AddCircle (1 : ℚ))).injective
    rw [groupCohomology.d₀₁_hom_apply, map_sub]
    funext h
    simp only [S, Function.comp_apply]
    rw [coindBotEquivPi_apply, coindBotUnit_hom_apply_coe, Pi.sub_apply,
      coindBotEquivPi_apply, coindBot_ρ_apply_coe, coindBotEquivPi_apply]
    simp only [c, f, coindBotEquivPi_symm_apply_coe, Representation.trivial_apply]
    rw [map_mul, ofMul_mul, map_add]
    abel
  let coc : groupCohomology.cocycles₁ S.X₁ :=
    ⟨c, groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁ hS hc⟩
  have hordinary :
      groupCohomology.δ hS 0 1 rfl
          ((groupCohomology.H0Iso S.X₃).inv (characterDimensionShift G χ)) =
        groupCohomology.H1π S.X₁ coc :=
    groupCohomology.δ₀_apply hS (characterDimensionShift G χ) f rfl c hc
  have hcoc : coc =
      (groupCohomology.cocycles₁IsoOfIsTrivial (ratCircleRep G)).inv
        (χ.comp Abelianization.of.toAdditive) := by
    apply groupCohomology.cocycles₁_ext
    intro g
    rfl
  have hcomparison := ConcreteCategory.congr_hom
    (δ_comp_fromGroupCohomology hS 0)
    ((groupCohomology.H0Iso S.X₃).inv (characterDimensionShift G χ))
  rw [Rep.fromGroupCohomology_zero] at hcomparison
  simp only [ConcreteCategory.comp_apply] at hcomparison
  dsimp only [S] at hcomparison
  rw [(groupCohomology.H0Iso (dimensionShiftUp (ratCircleRep G))).inv_hom_id_apply]
    at hcomparison
  rw [hordinary, hcoc, ← groupCohomology.H1IsoOfIsTrivial_inv_apply] at hcomparison
  rw [dimensionShiftUpIso_hom]
  convert hcomparison.symm using 1

/-- The connecting class of a character is the Tate connecting map applied to its canonical
degree-one class. This compares the definition through ordinary group cohomology with the Tate
connecting homomorphism used by the cup-product boundary formula. -/
theorem characterConnectingClass_eq_tateδ
    (χ : Additive (Abelianization G) →+ AddCircle (1 : ℚ)) :
    characterConnectingClass G χ =
      _root_.TateCohomology.δ (Rep.ratAddCircleShortComplex_shortExact G) 1
        (Rep.fromGroupCohomology (Rep.ratAddCircleShortComplex G).X₃ 1
          ((groupCohomology.H1IsoOfIsTrivial (Rep.ratAddCircleShortComplex G).X₃).inv
            (χ.comp Abelianization.of.toAdditive))) := by
  have h := ConcreteCategory.congr_hom
    (δ_comp_fromGroupCohomology (Rep.ratAddCircleShortComplex_shortExact G) 1)
    ((groupCohomology.H1IsoOfIsTrivial (ratCircleRep G)).inv
      (χ.comp Abelianization.of.toAdditive))
  rw [characterConnectingClass_def]
  simp only [Rep.fromGroupCohomology_succ] at h ⊢
  norm_num at h ⊢
  exact h

/-- The connecting class can be computed by first representing the character in the initial
upward dimension shift and then applying the Tate connecting map for `ℤ → ℚ → ℚ/ℤ`. -/
theorem characterConnectingClass_eq_tateδ_dimensionShift
    (χ : Additive (Abelianization G) →+ AddCircle (1 : ℚ)) :
    characterConnectingClass G χ =
      _root_.TateCohomology.δ (Rep.ratAddCircleShortComplex_shortExact G) 1
        ((dimensionShiftUpIso (Rep.ratAddCircleShortComplex G).X₃ 0).hom
          (H0π (dimensionShiftUp (Rep.ratAddCircleShortComplex G).X₃)
            (characterDimensionShift G χ))) := by
  rw [characterConnectingClass_eq_tateδ,
    dimensionShiftUpIso_characterDimensionShift]

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
