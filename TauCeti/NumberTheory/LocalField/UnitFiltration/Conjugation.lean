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

Let `L/K` be a finite extension of nonarchimedean local fields. Conjugation by an element `σ`
of inertia acts on every ramification quotient `G_i/G_{i+1}`. At depth zero this action is
trivial. At positive depth, the embedding into the additive residue field transforms by the
`i`th power of the tame character:

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

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]

variable (K L) in
/-- The positive-depth embedding of `G_{n+1}/G_{n+2}` into the additive residue field, in the
coordinate determined by a uniformizer `π`. -/
noncomputable def ramificationGroupGradedToResidueField (n : ℕ) (π : 𝒪[L])
    (hπ : Irreducible π) :
    Additive (RamificationGroupGraded (L ≃ₐ[K] L) 𝒪[L] ((n + 1 : ℕ) : ℤ)) →+
      IsLocalRing.ResidueField 𝒪[L] :=
  (unitFiltrationGradedSuccEquivResidueFieldOfUniformizer n π hπ).toAddMonoidHom.comp
    (ramificationGroupGradedToUnitFiltrationGraded (G := L ≃ₐ[K] L) (n + 1) hπ).toAdditive

theorem ramificationGroupGradedToResidueField_ofMul_mk (n : ℕ) (π : 𝒪[L])
    (hπ : Irreducible π)
    (τ : ramificationGroup (L ≃ₐ[K] L) 𝒪[L] ((n + 1 : ℕ) : ℤ)) :
    ramificationGroupGradedToResidueField (K := K) (L := L) n π hπ
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
    Function.Injective (ramificationGroupGradedToResidueField (K := K) (L := L) n π hπ) :=
  (unitFiltrationGradedSuccEquivResidueFieldOfUniformizer n π hπ).injective.comp
    (ramificationGroupGradedToUnitFiltrationGraded_injective (G := L ≃ₐ[K] L)
      (i := n + 1) hπ)

/-- Conjugation by inertia acts trivially on the tame quotient `G_0/G_1`. -/
@[simp]
theorem tameCharacterGraded_ramificationGroupGradedConj (π : 𝒪[L]) (hπ : Irreducible π)
    (σ : ramificationGroup (L ≃ₐ[K] L) 𝒪[L] 0)
    (τ : RamificationGroupGraded (L ≃ₐ[K] L) 𝒪[L] 0) :
    tameCharacterGraded hπ
        (ramificationGroupGradedConj (L ≃ₐ[K] L) 𝒪[L] (σ : L ≃ₐ[K] L) 0 τ) =
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
theorem ramificationGroupGradedToResidueField_conj (n : ℕ) (π : 𝒪[L])
    (hπ : Irreducible π) (σ : ramificationGroup (L ≃ₐ[K] L) 𝒪[L] 0)
    (τ : RamificationGroupGraded (L ≃ₐ[K] L) 𝒪[L] ((n + 1 : ℕ) : ℤ)) :
    ramificationGroupGradedToResidueField (K := K) (L := L) n π hπ
        (Additive.ofMul (ramificationGroupGradedConj (L ≃ₐ[K] L) 𝒪[L]
          (σ : L ≃ₐ[K] L) ((n + 1 : ℕ) : ℤ) τ)) =
      (tameCharacter hπ σ : IsLocalRing.ResidueField 𝒪[L]) ^ (n + 1) *
        ramificationGroupGradedToResidueField (K := K) (L := L) n π hπ
          (Additive.ofMul τ) := by
  induction τ using QuotientGroup.induction_on with
  | _ τ =>
    let g : L ≃ₐ[K] L := σ
    let π' : 𝒪[L] := g⁻¹ • π
    have hπ' : Irreducible π' := hπ.map (MulSemiringAction.toRingAut (L ≃ₐ[K] L) 𝒪[L] g⁻¹)
    have hmove : (τ : L ≃ₐ[K] L) • π' - π' ∈ maximalIdeal 𝒪[L] ^ (n + 2) :=
      (mem_ramificationGroup_natCast_iff.mp τ.2) π'
    rw [hπ'.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmove
    obtain ⟨y, hy⟩ := hmove
    have hπ'0 : (π' : L) ≠ 0 := fun h ↦ hπ'.ne_zero (Subtype.ext h)
    have hyL := congrArg (fun z : 𝒪[L] ↦ (z : L)) hy
    have hyL' : (y : L) * (π' : L) ^ (n + 2) =
        (τ : L ≃ₐ[K] L) • (π' : L) - (π' : L) := by
      change (y : L) * (π' : L) ^ (n + 2) =
        (τ : L ≃ₐ[K] L) • (π' : L) - (π' : L) at hyL
      exact hyL
    have hτdiff :
        (unitFiltrationDifference n (uniformizerRatio (n + 1) hπ' τ) : 𝒪[L]) =
          y * π' ^ (n + 1) := by
      apply Subtype.ext
      rw [coe_coe_unitFiltrationDifference, coe_uniformizerRatio, div_sub_one hπ'0, ← hyL']
      field_simp
      push_cast
      ring
    have hτcoord :
        ramificationGroupGradedToResidueField (K := K) (L := L) n π' hπ'
            (Additive.ofMul (QuotientGroup.mk τ)) = residue 𝒪[L] y := by
      rw [ramificationGroupGradedToResidueField_ofMul_mk]
      exact
        unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk_eq_residue
          n π' hπ' _ y hτdiff
    let τ' : ramificationGroup (L ≃ₐ[K] L) 𝒪[L] ((n + 1 : ℕ) : ℤ) :=
      MulAut.conjNormal g τ
    have hgπ' : g • π' = π := by simp [π', g]
    have hconjMove : (τ' : L ≃ₐ[K] L) • π - π = g • y * π ^ (n + 2) := by
      calc
        (τ' : L ≃ₐ[K] L) • π - π = g • ((τ : L ≃ₐ[K] L) • π' - π') := by
          simp [τ', π', g, MulAut.conjNormal_apply, mul_smul, smul_sub]
        _ = g • (y * π' ^ (n + 2)) := by rw [hy]
        _ = g • y * π ^ (n + 2) := by rw [smul_mul', smul_pow', hgπ']
    have hπ0 : (π : L) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
    have hconjMoveL := congrArg (fun z : 𝒪[L] ↦ (z : L)) hconjMove
    have hconjMoveL' : (τ' : L ≃ₐ[K] L) • (π : L) - (π : L) =
        (g • y : 𝒪[L]) * (π : L) ^ (n + 2) := by
      change (τ' : L ≃ₐ[K] L) • (π : L) - (π : L) =
        (g • y : 𝒪[L]) * (π : L) ^ (n + 2) at hconjMoveL
      exact hconjMoveL
    have hconjDiff :
        (unitFiltrationDifference n (uniformizerRatio (n + 1) hπ τ') : 𝒪[L]) =
          g • y * π ^ (n + 1) := by
      apply Subtype.ext
      rw [coe_coe_unitFiltrationDifference, coe_uniformizerRatio, div_sub_one hπ0,
        hconjMoveL']
      field_simp
      push_cast
      ring
    have hconjCoord :
        ramificationGroupGradedToResidueField (K := K) (L := L) n π hπ
            (Additive.ofMul (QuotientGroup.mk τ')) = residue 𝒪[L] (g • y) := by
      rw [ramificationGroupGradedToResidueField_ofMul_mk]
      exact
        unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk_eq_residue
          n π hπ _ (g • y) hconjDiff
    have hresidue : residue 𝒪[L] (g • y) = residue 𝒪[L] y :=
      residue_smul_eq_of_mem_ramificationGroup_zero (L ≃ₐ[K] L) 𝒪[L] σ.2 y
    let a := uniformizerChangeUnit π π' hπ hπ'
    have ha : ((a : 𝒪[L]) : L) = g⁻¹ (π : L) / (π : L) := by
      apply mul_left_cancel₀ hπ0
      rw [mul_div_cancel₀ _ hπ0]
      have haRing := mul_uniformizerChangeUnit π π' hπ hπ'
      have haField := congrArg (fun z : 𝒪[L] ↦ (z : L)) haRing
      change (π : L) * (a : 𝒪[L]) = (π' : L) at haField
      rw [show (π' : L) = g⁻¹ (π : L) from AlgEquiv.coe_smul_integerRing g⁻¹ π] at haField
      exact haField
    have haResidue : residue 𝒪[L] (a : 𝒪[L]) =
        ((tameCharacter hπ σ : (ResidueField 𝒪[L])ˣ)⁻¹ : ResidueField 𝒪[L]) := by
      calc
        residue 𝒪[L] (a : 𝒪[L]) =
            (tameCharacter hπ σ⁻¹ : ResidueField 𝒪[L]) :=
          (coe_tameCharacter_of_val_eq_smul_div hπ σ⁻¹ ha).symm
        _ = ((tameCharacter hπ σ : (ResidueField 𝒪[L])ˣ)⁻¹ :
            ResidueField 𝒪[L]) := by
          rw [map_inv]
          exact Units.val_inv_eq_inv_val (tameCharacter hπ σ)
    have hchange :=
      unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_change n π π' hπ hπ'
        (Additive.ofMul
          (ramificationGroupGradedToUnitFiltrationGraded (G := L ≃ₐ[K] L) (n + 1) hπ
            (QuotientGroup.mk τ)))
    rw [uniformizerChangeResidueAddEquiv_apply, haResidue] at hchange
    have htheta := DFunLike.congr_fun
      (ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible
        (G := L ≃ₐ[K] L) (i := n + 1) hπ hπ') (QuotientGroup.mk τ)
    have hchange' :
        ramificationGroupGradedToResidueField (K := K) (L := L) n π hπ
            (Additive.ofMul (QuotientGroup.mk τ)) =
          ((tameCharacter hπ σ : (ResidueField 𝒪[L])ˣ)⁻¹ : ResidueField 𝒪[L]) ^
              (n + 1) *
            ramificationGroupGradedToResidueField (K := K) (L := L) n π' hπ'
              (Additive.ofMul (QuotientGroup.mk τ)) := by
      change
        unitFiltrationGradedSuccEquivResidueFieldOfUniformizer n π hπ
            (Additive.ofMul
              (ramificationGroupGradedToUnitFiltrationGraded (G := L ≃ₐ[K] L) (n + 1) hπ
                (QuotientGroup.mk τ))) =
          ((tameCharacter hπ σ : (ResidueField 𝒪[L])ˣ)⁻¹ : ResidueField 𝒪[L]) ^
              (n + 1) *
            unitFiltrationGradedSuccEquivResidueFieldOfUniformizer n π' hπ'
              (Additive.ofMul
                (ramificationGroupGradedToUnitFiltrationGraded (G := L ≃ₐ[K] L) (n + 1) hπ'
                  (QuotientGroup.mk τ)))
      rw [← htheta]
      exact hchange
    simp only [ramificationGroupGradedConj_mk]
    rw [show MulAut.conjNormal g τ = τ' from rfl]
    rw [hconjCoord, hresidue, ← hτcoord]
    calc
      ramificationGroupGradedToResidueField (K := K) (L := L) n π' hπ'
          (Additive.ofMul (QuotientGroup.mk τ)) =
          (tameCharacter hπ σ : ResidueField 𝒪[L]) ^ (n + 1) *
            (((tameCharacter hπ σ : (ResidueField 𝒪[L])ˣ)⁻¹ : ResidueField 𝒪[L]) ^
              (n + 1) *
                ramificationGroupGradedToResidueField (K := K) (L := L) n π' hπ'
                  (Additive.ofMul (QuotientGroup.mk τ))) := by simp
      _ = (tameCharacter hπ σ : ResidueField 𝒪[L]) ^ (n + 1) *
            ramificationGroupGradedToResidueField (K := K) (L := L) n π hπ
              (Additive.ofMul (QuotientGroup.mk τ)) := by rw [← hchange']

end TauCeti
