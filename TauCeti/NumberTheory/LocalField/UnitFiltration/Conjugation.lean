/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.RamificationGroup
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Uniformizer

/-!
# Conjugation on ramification quotients

Let a group `G` act on a nonarchimedean local field `L`, preserving its ring of integers.
Conjugation by an element `σ` of inertia acts on every ramification quotient `G_i/G_{i+1}`.
At depth zero this action is trivial. At positive depth, the embedding into the additive residue
field transforms by the `i`th power of the tame character:

`theta_i(σ τ σ⁻¹) = theta_0(σ)^i * theta_i(τ)`.

Here the positive-depth maps are read in the residue coordinate associated to a uniformizer.
The exponent is forced by changing from the uniformizer `π` to `σ⁻¹ π`. This formula is the
finite-level cyclotomic twist and supplies the constant appearing in ramification-theoretic norm
computations.

## Main definitions

* `TauCeti.ramificationGroupGradedToResidueField`: the positive-depth ramification quotient
  embedded additively in the residue field using a uniformizer.

## Main results

* `TauCeti.tameCharacterGraded_ramificationGroupGradedConj`: inertia acts trivially on
  `G_0/G_1`.
* `TauCeti.ramificationGroupGradedToResidueField_conj`: at depth `i > 0`, conjugation scales the
  residue coordinate by the `i`th power of the tame character.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2, Proposition 9.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField TauCeti.IsLocalRing

namespace TauCeti

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
variable {G : Type*} [Group G] [MulSemiringAction G L] [IsInvariantSubring G 𝒪[L]]

variable (G L) in
/-- The positive-depth embedding of `G_{n+1}/G_{n+2}` into the additive residue field, in the
coordinate determined by a uniformizer `π`. -/
noncomputable def ramificationGroupGradedToResidueField (n : ℕ) (π : 𝒪[L])
    (hπ : Irreducible π) :
    Additive (RamificationGroupGraded G 𝒪[L] ((n : ℤ) + 1)) →+
      IsLocalRing.ResidueField 𝒪[L] :=
  by
    simpa only [Int.natCast_add, Int.cast_ofNat_Int] using
      (unitFiltrationGradedSuccEquivResidueFieldOfUniformizer n π hπ).toAddMonoidHom.comp
        (ramificationGroupGradedToUnitFiltrationGraded (G := G) (n + 1) hπ).toAdditive

@[simp]
theorem ramificationGroupGradedToResidueField_ofMul_mk (n : ℕ) (π : 𝒪[L])
    (hπ : Irreducible π)
    (τ : ramificationGroup G 𝒪[L] ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField (G := G) (L := L) n π hπ
        (Additive.ofMul (QuotientGroup.mk τ)) =
      unitFiltrationGradedSuccEquivResidueFieldOfUniformizer n π hπ
        (Additive.ofMul (QuotientGroup.mk (uniformizerRatio (n + 1) hπ τ))) :=
  by
    rw [ramificationGroupGradedToResidueField]
    simp only [AddMonoidHom.comp_apply]
    apply congrArg _
    exact congrArg Additive.ofMul
      (ramificationGroupGradedToUnitFiltrationGraded_mk (i := n + 1) hπ τ)

/-- The positive-depth ramification quotient embeds in the additive residue field. -/
theorem ramificationGroupGradedToResidueField_injective (n : ℕ) (π : 𝒪[L])
    (hπ : Irreducible π) :
    Function.Injective (ramificationGroupGradedToResidueField (G := G) (L := L) n π hπ) :=
  (unitFiltrationGradedSuccEquivResidueFieldOfUniformizer n π hπ).injective.comp
    (ramificationGroupGradedToUnitFiltrationGraded_injective (G := G)
      (i := n + 1) hπ)

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- Coercion from the invariant integer ring to the ambient field respects the group action. -/
private theorem coe_smul_integer (g : G) (x : 𝒪[L]) :
    ((g • x : 𝒪[L]) : L) = g • (x : L) :=
  map_smul (IsInvariantSubring.subtypeHom G 𝒪[L]) g x

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- Coercion from the invariant integer ring respects an action displacement. -/
private theorem coe_smul_sub_integer (g : G) (x : 𝒪[L]) :
    ((g • x - x : 𝒪[L]) : L) = g • (x : L) - (x : L) := by
  calc
    ((g • x - x : 𝒪[L]) : L) = ((g • x : 𝒪[L]) : L) - (x : L) := rfl
    _ = g • (x : L) - (x : L) := by rw [coe_smul_integer]

/-- Compute a positive-depth residue coordinate from the displacement of a representative. -/
private theorem ramificationGroupGradedToResidueField_of_smul_sub_eq
    (n : ℕ) (π : 𝒪[L]) (hπ : Irreducible π)
    (τ : ramificationGroup G 𝒪[L] ((n : ℤ) + 1)) (y : 𝒪[L])
    (hmove : (τ : G) • π - π = y * π ^ (n + 2)) :
    ramificationGroupGradedToResidueField (G := G) (L := L) n π hπ
        (Additive.ofMul (QuotientGroup.mk τ)) = residue 𝒪[L] y := by
  have hπ0 : (π : L) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
  have hmoveL := congrArg (fun z : 𝒪[L] ↦ (z : L)) hmove
  have hmoveL' : (τ : G) • (π : L) - (π : L) =
      (y : L) * (π : L) ^ (n + 2) := by
    calc
      _ = (((τ : G) • π - π : 𝒪[L]) : L) := (coe_smul_sub_integer (τ : G) π).symm
      _ = ((y * π ^ (n + 2) : 𝒪[L]) : L) := hmoveL
      _ = _ := by rfl
  have hdiff :
      (unitFiltrationDifference n (uniformizerRatio (n + 1) hπ τ) : 𝒪[L]) =
        y * π ^ (n + 1) := by
    apply Subtype.ext
    rw [coe_coe_unitFiltrationDifference, coe_uniformizerRatio, div_sub_one hπ0, hmoveL']
    field_simp
    push_cast
    ring
  rw [ramificationGroupGradedToResidueField_ofMul_mk]
  exact unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk_eq_residue
    n π hπ _ y hdiff

/-- Change the uniformizer used for a positive-depth ramification coordinate. -/
private theorem ramificationGroupGradedToResidueField_change
    (n : ℕ) (π π' : 𝒪[L]) (hπ : Irreducible π) (hπ' : Irreducible π')
    (τ : RamificationGroupGraded G 𝒪[L] ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField (G := G) (L := L) n π hπ (Additive.ofMul τ) =
      residue 𝒪[L] (uniformizerChangeUnit π π' hπ hπ' : 𝒪[L]) ^ (n + 1) *
        ramificationGroupGradedToResidueField (G := G) (L := L) n π' hπ'
          (Additive.ofMul τ) := by
  have hchange :=
    unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_change n π π' hπ hπ'
      (Additive.ofMul
        (ramificationGroupGradedToUnitFiltrationGraded (G := G) (n + 1) hπ τ))
  rw [uniformizerChangeResidueAddEquiv_apply] at hchange
  have htheta := DFunLike.congr_fun
    (ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible
      (G := G) (i := n + 1) hπ hπ') τ
  rw [ramificationGroupGradedToResidueField, ramificationGroupGradedToResidueField]
  simp only [AddMonoidHom.comp_apply]
  simpa [htheta] using hchange

/-- The change from `π` to `g⁻¹ • π` is the inverse tame-character coordinate of `g`. -/
private theorem residue_uniformizerChangeUnit_inv_smul
    (π π' : 𝒪[L]) (hπ : Irreducible π) (hπ' : Irreducible π')
    (σ : ramificationGroup G 𝒪[L] 0)
    (hπ'coe : (π' : L) = (σ : G)⁻¹ • (π : L)) :
    residue 𝒪[L] (uniformizerChangeUnit π π' hπ hπ' : 𝒪[L]) =
      ((tameCharacter hπ σ : (ResidueField 𝒪[L])ˣ)⁻¹ : ResidueField 𝒪[L]) := by
  let a := uniformizerChangeUnit π π' hπ hπ'
  have hπ0 : (π : L) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
  have haRing := mul_uniformizerChangeUnit π π' hπ hπ'
  have haField : (π : L) * ((a : 𝒪[L]) : L) = (π' : L) := by
    exact congrArg (fun z : 𝒪[L] ↦ (z : L)) haRing
  have ha : ((a : 𝒪[L]) : L) = (σ : G)⁻¹ • (π : L) / (π : L) := by
    apply mul_left_cancel₀ hπ0
    rw [mul_div_cancel₀ _ hπ0, ← hπ'coe]
    exact haField
  calc
    residue 𝒪[L] (a : 𝒪[L]) =
        (tameCharacter hπ σ⁻¹ : ResidueField 𝒪[L]) :=
      (coe_tameCharacter_of_val_eq_smul_div hπ σ⁻¹ ha).symm
    _ = ((tameCharacter hπ σ : (ResidueField 𝒪[L])ˣ)⁻¹ :
        ResidueField 𝒪[L]) := by
      rw [map_inv]
      exact Units.val_inv_eq_inv_val (tameCharacter hπ σ)

/-- Conjugation by inertia acts trivially on the tame quotient `G_0/G_1`. -/
@[simp]
theorem tameCharacterGraded_ramificationGroupGradedConj (π : 𝒪[L]) (hπ : Irreducible π)
    (σ : ramificationGroup G 𝒪[L] 0)
    (τ : RamificationGroupGraded G 𝒪[L] 0) :
    tameCharacterGraded hπ
        (ramificationGroupGradedConj G 𝒪[L] (σ : G) 0 τ) =
      tameCharacterGraded hπ τ := by
  induction τ using QuotientGroup.induction_on with
  | _ τ =>
    simp only [ramificationGroupGradedConj_mk, tameCharacterGraded_mk]
    rw [MulAut.conjNormal_val, MulAut.conj_apply, map_mul, map_mul, map_inv,
      mul_comm (tameCharacter hπ σ) (tameCharacter hπ τ), mul_assoc, mul_inv_cancel,
      mul_one]

/-- **The conjugation action formula on positive ramification quotients.** In the residue
coordinate determined by `π`, conjugation by `σ ∈ G_0` acts on `G_i/G_{i+1}` as
multiplication by `theta_0(σ)^i`, where `theta_0` is the tame character. -/
@[simp]
theorem ramificationGroupGradedToResidueField_conj (n : ℕ) (π : 𝒪[L])
    (hπ : Irreducible π) (σ : ramificationGroup G 𝒪[L] 0)
    (τ : RamificationGroupGraded G 𝒪[L] ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField (G := G) (L := L) n π hπ
        (Additive.ofMul (ramificationGroupGradedConj G 𝒪[L]
          (σ : G) ((n : ℤ) + 1) τ)) =
      (tameCharacter hπ σ : IsLocalRing.ResidueField 𝒪[L]) ^ (n + 1) *
        ramificationGroupGradedToResidueField (G := G) (L := L) n π hπ
          (Additive.ofMul τ) := by
  induction τ using QuotientGroup.induction_on with
  | _ τ =>
    let g : G := σ
    let π' : 𝒪[L] := g⁻¹ • π
    have hπ' : Irreducible π' := hπ.map (MulSemiringAction.toRingAut G 𝒪[L] g⁻¹)
    have hmove : (τ : G) • π' - π' ∈ maximalIdeal 𝒪[L] ^ (n + 2) :=
      (mem_ramificationGroup_natCast_iff.mp τ.2) π'
    rw [hπ'.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmove
    obtain ⟨y, hy⟩ := hmove
    -- First compute the coordinate of `τ` using the moved uniformizer `π' = g⁻¹ • π`.
    have hτcoord :
        ramificationGroupGradedToResidueField (G := G) (L := L) n π' hπ'
            (Additive.ofMul (QuotientGroup.mk τ)) = residue 𝒪[L] y := by
      exact ramificationGroupGradedToResidueField_of_smul_sub_eq n π' hπ' τ y hy.symm
    let τ' : ramificationGroup G 𝒪[L] ((n : ℤ) + 1) :=
      MulAut.conjNormal g τ
    have hgπ' : g • π' = π := by simp [π', g]
    -- Conjugating transports the displacement coefficient `y` to `g • y`.
    have hconjMove : (τ' : G) • π - π = g • y * π ^ (n + 2) := by
      calc
        (τ' : G) • π - π = g • ((τ : G) • π' - π') := by
          simp [τ', π', g, MulAut.conjNormal_apply, mul_smul, smul_sub]
        _ = g • (y * π' ^ (n + 2)) := by rw [hy]
        _ = g • y * π ^ (n + 2) := by rw [smul_mul', smul_pow', hgπ']
    have hconjCoord :
        ramificationGroupGradedToResidueField (G := G) (L := L) n π hπ
            (Additive.ofMul (QuotientGroup.mk τ')) = residue 𝒪[L] (g • y) := by
      exact ramificationGroupGradedToResidueField_of_smul_sub_eq n π hπ τ' (g • y) hconjMove
    have hresidue : residue 𝒪[L] (g • y) = residue 𝒪[L] y :=
      residue_smul_eq_of_mem_ramificationGroup_zero G 𝒪[L] σ.2 y
    -- Changing back from `π'` to `π` contributes the inverse tame-character factor.
    have hπ'coe : (π' : L) = (σ : G)⁻¹ • (π : L) := by
      simpa only [π', g] using coe_smul_integer ((σ : G)⁻¹) π
    have haResidue :
        residue 𝒪[L] (uniformizerChangeUnit π π' hπ hπ' : 𝒪[L]) =
        ((tameCharacter hπ σ : (ResidueField 𝒪[L])ˣ)⁻¹ : ResidueField 𝒪[L]) := by
      exact residue_uniformizerChangeUnit_inv_smul π π' hπ hπ' σ hπ'coe
    have hchange' := ramificationGroupGradedToResidueField_change
      (G := G) n π π' hπ hπ' (QuotientGroup.mk τ)
    rw [haResidue] at hchange'
    have hconjCoord' :
        ramificationGroupGradedToResidueField (G := G) (L := L) n π hπ
            (Additive.ofMul (QuotientGroup.mk (MulAut.conjNormal g τ))) =
          residue 𝒪[L] (g • y) := by
      simpa only [τ'] using hconjCoord
    simp only [ramificationGroupGradedConj_mk]
    rw [hconjCoord', hresidue, ← hτcoord]
    calc
      ramificationGroupGradedToResidueField (G := G) (L := L) n π' hπ'
          (Additive.ofMul (QuotientGroup.mk τ)) =
          (tameCharacter hπ σ : ResidueField 𝒪[L]) ^ (n + 1) *
            (((tameCharacter hπ σ : (ResidueField 𝒪[L])ˣ)⁻¹ : ResidueField 𝒪[L]) ^
              (n + 1) *
                ramificationGroupGradedToResidueField (G := G) (L := L) n π' hπ'
                  (Additive.ofMul (QuotientGroup.mk τ))) := by simp
      _ = (tameCharacter hπ σ : ResidueField 𝒪[L]) ^ (n + 1) *
            ramificationGroupGradedToResidueField (G := G) (L := L) n π hπ
              (Additive.ofMul (QuotientGroup.mk τ)) := by rw [← hchange']

end TauCeti
