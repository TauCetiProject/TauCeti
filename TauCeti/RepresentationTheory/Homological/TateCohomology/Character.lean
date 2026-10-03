/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Connecting.GroupCohomology
public import TauCeti.RepresentationTheory.Homological.TateCohomology.DimensionShift
public import TauCeti.RepresentationTheory.Rep.Trivial

/-!
# The connecting class of a character

Let `G` be a finite group. A character `χ : Gᵃᵇ → ℚ/ℤ` is a homomorphism `G → ℚ/ℤ`, which is a
class in `H¹(G, ℚ/ℤ)` for the trivial action. The connecting map of the sequence
`0 → ℤ → ℚ → ℚ/ℤ → 0` of trivial `G`-modules sends it to a class `δχ ∈ H²(G, ℤ)`, which is read
in the Tate group of degree `2`.

The character also has a canonical invariant representative in the first upward dimension shift
of `ℚ/ℤ`, whose connecting image is its standard Tate degree-one class. This identifies `δχ` with
the Tate connecting map of `0 → ℤ → ℚ → ℚ/ℤ → 0` applied to that class.

As elsewhere in this development, `ℚ/ℤ` is the rational circle `AddCircle (1 : ℚ)`.

## Main definitions

* `TauCeti.TateCohomology.characterConnectingClass`: the connecting class `δχ ∈ H²(G, ℤ)` of a
  character `χ : Gᵃᵇ → ℚ/ℤ`, in the Tate group of degree `2`, as an additive map in `χ`.
* `TauCeti.TateCohomology.characterDimensionShift`: the canonical invariant in the first upward
  dimension shift of `ℚ/ℤ` attached to a character, as an additive map in the character.

## Main results

* `TauCeti.TateCohomology.characterConnectingClass_def`: `δχ` is the connecting map of
  `Rep.ratAddCircleShortComplex` applied to the class of `χ` in `H¹(G, ℚ/ℤ)`, read in Tate
  cohomology.
* `TauCeti.TateCohomology.dimensionShiftUpIso_characterDimensionShift`: the connecting
  isomorphism sends `characterDimensionShift` to the standard Tate degree-one class of `χ`.
* `TauCeti.TateCohomology.characterConnectingClass_eq_tateδ`: `δχ` is the Tate connecting map
  applied to the standard Tate degree-one class of `χ`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §3.
* J.-P. Serre, *Local Fields*, Chapter XI, §3.
-/

public noncomputable section

open CategoryTheory Rep

namespace TauCeti.TateCohomology

variable (G : Type) [Group G] [Fintype G]

/-- The **connecting class** `δχ ∈ H²(G, ℤ)` of a character `χ : Gᵃᵇ → ℚ/ℤ` of a finite group `G`,
in the Tate group of degree `2`: the image of `χ`, as a class in `H¹(G, ℚ/ℤ)` for the trivial
action, under the connecting map of `0 → ℤ → ℚ → ℚ/ℤ → 0`. The character is read on `G` through
the abelianization map `G → Gᵃᵇ`. It is additive in the character. -/
def characterConnectingClass :
    (Additive (Abelianization G) →+ AddCircle (1 : ℚ)) →+ tateCohomology (Rep.trivial ℤ G ℤ) 2 :=
  ((_root_.TateCohomology.isoGroupCohomology 2).inv.app
      (Rep.trivial ℤ G ℤ)).hom.toAddMonoidHom.comp <|
    (groupCohomology.δ (Rep.ratAddCircleShortComplex_shortExact G) 1 2
        rfl).hom.toAddMonoidHom.comp <|
      (groupCohomology.H1IsoOfIsTrivial
          (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).inv.hom.toAddMonoidHom.comp <|
        AddMonoidHom.compHom' Abelianization.of.toAdditive

/-- The connecting class of `χ` is the connecting map applied to the class of `G → Gᵃᵇ → ℚ/ℤ`
in `H¹(G, ℚ/ℤ)`, carried to Tate cohomology by the comparison of positive degrees. -/
theorem characterConnectingClass_def (χ : Additive (Abelianization G) →+ AddCircle (1 : ℚ)) :
    characterConnectingClass G χ =
      (_root_.TateCohomology.isoGroupCohomology 2).inv.app (Rep.trivial ℤ G ℤ)
        (groupCohomology.δ (Rep.ratAddCircleShortComplex_shortExact G) 1 2 rfl
          ((groupCohomology.H1IsoOfIsTrivial (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).inv
            (χ.comp Abelianization.of.toAdditive))) :=
  (rfl)

private abbrev ratCircleRep : Rep ℤ G := Rep.trivial ℤ G (AddCircle (1 : ℚ))

/-- The canonical invariant in the first upward dimension shift of `ℚ/ℤ` attached to a
character. Its image under the dimension-shift isomorphism is the Tate degree-one class obtained
from the ordinary character class in `H¹(G, ℚ/ℤ)`. -/
def characterDimensionShift
    : (Additive (Abelianization G) →+ AddCircle (1 : ℚ)) →+
      (dimensionShiftUp (Rep.ratAddCircleShortComplex G).X₃).ρ.invariants where
  toFun χ := by
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
  map_zero' := by
    apply Subtype.ext
    simp only [AddMonoidHom.zero_apply, ← Pi.zero_def, map_zero, ZeroMemClass.coe_zero]
  map_add' χ ψ := by
    apply Subtype.ext
    simp only [AddMonoidHom.add_apply, ← Pi.add_def, map_add, AddMemClass.coe_add]

omit [Fintype G] in
/-- The underlying value of `characterDimensionShift` is the image in the first upward dimension
shift of the coinduced function `g ↦ χ(g)`. -/
@[simp]
theorem coe_characterDimensionShift
    (χ : Additive (Abelianization G) →+ AddCircle (1 : ℚ)) :
    (characterDimensionShift G χ : dimensionShiftUp (Rep.ratAddCircleShortComplex G).X₃) =
      (dimensionShiftUpπ (Rep.ratAddCircleShortComplex G).X₃).hom
        ((coindBotEquivPi ℤ G (AddCircle (1 : ℚ))).symm fun g ↦
          χ (Additive.ofMul (Abelianization.of g))) :=
  (rfl)

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

end TauCeti.TateCohomology
