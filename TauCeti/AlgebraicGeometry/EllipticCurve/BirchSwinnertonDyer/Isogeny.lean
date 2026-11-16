/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny.Ratio
public import TauCeti.AlgebraicGeometry.EllipticCurve.BirchSwinnertonDyer.Statement
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Sha
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny.Tamagawa
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Finite
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.LFunction.Isogeny
import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.Regulator.Isogeny

/-!
# The Birch–Swinnerton-Dyer quotient under an isogeny

Let `φ : E₁ → E₂` be an isogeny of elliptic curves over `ℚ` with finite Shafarevich–Tate groups.
Combining Cassels' global period–Tamagawa–Kummer product formula
(`TauCeti.Isogeny.minimalRealPeriod_mul_tamagawaProduct_mul_kummerRatioProduct`),

  `Ω(E₁) · (∏_p c_p(E₁)) · φ.kummerRatioProduct = Ω(E₂) · (∏_p c_p(E₂))`,

with the transformation of the regulator and torsion factor under isogeny
(`TauCeti.Isogeny.Hom.regulator_div_card_torsion_sq_mul_index_dual_div_card_ker_eq`),

  `Reg(E₁) / #E₁(ℚ)_tors² · φ.dual.kummerRatio = φ.kummerRatio · Reg(E₂) / #E₂(ℚ)_tors²`,

gives the master algebraic identity

  `E₁.bsdQuotient · #Sha(E₂) · φ.kummerRatioProduct · φ.dual.kummerRatio =`
  `  E₂.bsdQuotient · #Sha(E₁) · φ.kummerRatio`.

Using the descent order formula `#Sel_φ = [E₂(ℚ) : φ E₁(ℚ)] · #Sha(E₁)[φ]`
(`TauCeti.Isogeny.card_selmerGroup`) and `#Sha(E₁) = #Sha(E₁)[φ] · #φ(Sha(E₁))` for `φ` and its
dual rewrites this directly as

  `E₁.bsdQuotient · (#Sel_φ̂ · #E₁(ℚ)[φ] · φ.kummerRatioProduct) · #φ̂(Sha(E₂)) =`
  `  E₂.bsdQuotient · (#Sel_φ · #E₂(ℚ)[φ̂]) · #φ(Sha(E₁))`.

This reduces the isogeny invariance of `WeierstrassCurve.bsdQuotient` (and hence, together with
the invariance of the `L`-function, Mordell–Weil rank, and finiteness of `Sha`, of the full
`WeierstrassCurve.BirchSwinnertonDyer` conjecture) to two global duality statements:
the global Selmer-ratio formula `#Sel_φ · #E₂(ℚ)[φ̂] = #Sel_φ̂ · #E₁(ℚ)[φ] · φ.kummerRatioProduct`
and the equality `#φ(Sha(E₁)) = #φ̂(Sha(E₂))` of image orders on `Sha`.

For degree-one isogenies, and in particular changes of Weierstrass variables, both invariants and
the full Birch–Swinnerton-Dyer conjecture are unconditionally preserved.

## Main results

* `TauCeti.Isogeny.bsdQuotient_mul_card_sha_mul_kummerRatioProduct_mul_kummerRatio_dual`: the
  master algebraic relation between `E₁.bsdQuotient` and `E₂.bsdQuotient` via `Sha` and the
  Kummer ratios.
* `TauCeti.Isogeny.bsdQuotient_mul_card_selmerGroup_dual`: the Selmer-and-`Sha`-image form of the
  relation for any family `τ` of embeddings of separable closures over the places of `ℚ`.
* `TauCeti.Isogeny.bsdQuotient_eq_of_card_selmerGroup_and_card_range_shafarevichTateMap`:
  reduction of `E₁.bsdQuotient = E₂.bsdQuotient` to the global Selmer ratio and equality of image
  orders on `Sha`.
* `TauCeti.Isogeny.birchSwinnertonDyer_iff_of_bsdQuotient_eq`: reduction of
  `E₁.BirchSwinnertonDyer ↔ E₂.BirchSwinnertonDyer` along an isogeny to equality of BSD quotients.
* `TauCeti.Isogeny.bsdQuotient_eq_of_degree_eq_one` and
  `TauCeti.Isogeny.birchSwinnertonDyer_iff_of_degree_eq_one`: unconditional invariance under
  degree-one isogenies.
* `WeierstrassCurve.VariableChange.bsdQuotient_smul` and
  `WeierstrassCurve.VariableChange.birchSwinnertonDyer_smul_iff`: unconditional invariance under a
  change of Weierstrass variables.

## References

* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti.Isogeny

section BSDQuotient

variable {E₁ E₂ : WeierstrassCurve ℚ} [E₁.IsElliptic] [E₂.IsElliptic]

/-- **Master algebraic relation for the Birch–Swinnerton-Dyer quotient under an isogeny**:
`E₁.bsdQuotient · #Sha(E₂) · φ.kummerRatioProduct · φ.dual.kummerRatio =`
`  E₂.bsdQuotient · #Sha(E₁) · φ.kummerRatio`.

This combines Cassels' global period–Tamagawa–Kummer product formula with the transformation of
the regulator and squared torsion order along `φ`. -/
theorem bsdQuotient_mul_card_sha_mul_kummerRatioProduct_mul_kummerRatio_dual
    [Finite E₁.sha] [Finite E₂.sha] (φ : Isogeny E₁.toAffine E₂.toAffine) :
    E₁.bsdQuotient * Nat.card E₂.sha * φ.kummerRatioProduct * φ.dual.kummerRatio =
      E₂.bsdQuotient * Nat.card E₁.sha * φ.kummerRatio := by
  have hpt := φ.minimalRealPeriod_mul_tamagawaProduct_mul_kummerRatioProduct
  have hreg := Hom.regulator_div_card_torsion_sq_mul_index_dual_div_card_ker_eq
    (f := Hom.ofIsogeny φ) (Hom.ofIsogeny_ne_zero φ)
  rw [Hom.dual_ofIsogeny] at hreg
  have hk₁ : (φ.kummerRatio : ℝ) =
      ((Hom.ofIsogeny φ).pointMapHom.range.index : ℝ) /
        Nat.card (Hom.ofIsogeny φ).pointMapHom.ker := by
    rw [kummerRatio_def, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]
  have hk₂ : (φ.dual.kummerRatio : ℝ) =
      ((Hom.ofIsogeny φ.dual).pointMapHom.range.index : ℝ) /
        Nat.card (Hom.ofIsogeny φ.dual).pointMapHom.ker := by
    rw [kummerRatio_def, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]
  rw [← hk₁, ← hk₂] at hreg
  rw [E₁.bsdQuotient_def, E₂.bsdQuotient_def]
  calc E₁.minimalRealPeriod * E₁.toAffine.regulator * Nat.card E₁.sha *
          E₁.tamagawaProduct (R := ℤ) /
          Nat.card (AddCommGroup.torsion E₁.toAffine.Point) ^ 2 *
        Nat.card E₂.sha * φ.kummerRatioProduct * φ.dual.kummerRatio
      = (E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ) * φ.kummerRatioProduct) *
          (E₁.toAffine.regulator / Nat.card (AddCommGroup.torsion E₁.toAffine.Point) ^ 2 *
            φ.dual.kummerRatio) *
          (Nat.card E₁.sha * Nat.card E₂.sha) := by ring
    _ = (E₂.minimalRealPeriod * E₂.tamagawaProduct (R := ℤ)) *
          (φ.kummerRatio *
            (E₂.toAffine.regulator / Nat.card (AddCommGroup.torsion E₂.toAffine.Point) ^ 2)) *
          (Nat.card E₁.sha * Nat.card E₂.sha) := by rw [hpt, hreg]
    _ = E₂.minimalRealPeriod * E₂.toAffine.regulator * Nat.card E₂.sha *
          E₂.tamagawaProduct (R := ℤ) /
          Nat.card (AddCommGroup.torsion E₂.toAffine.Point) ^ 2 *
        Nat.card E₁.sha * φ.kummerRatio := by ring

/-- Factoring `#Sha(W₁)` into kernel and image orders of `ψ` along a place family `τ`. -/
private theorem card_sha_eq_mul_range {W₁ W₂ : WeierstrassCurve ℚ} [W₁.IsElliptic] [W₂.IsElliptic]
    (ψ : Isogeny W₁.toAffine W₂.toAffine)
    (τ : ∀ v : GlobalNumberFields.Place ℚ,
      SeparableClosure ℚ →ₐ[ℚ] SeparableClosure v.Completion) :
    (Nat.card W₁.sha : ℝ) =
      Nat.card (ψ.shafarevichTateGroupKer τ) *
        Nat.card ((Hom.ofIsogeny ψ).shafarevichTateMap τ).range := by
  rw [W₁.sha_eq_shafarevichTateGroup τ]
  have h := AddSubgroup.card_ker_mul_card_range ((Hom.ofIsogeny ψ).shafarevichTateMap τ)
  rw [← ψ.shafarevichTateGroupKer_eq_ker_shafarevichTateMap τ] at h
  exact_mod_cast h.symm

/-- **Selmer-and-`Sha`-image identity for the Birch–Swinnerton-Dyer quotient under an isogeny**:
for any family `τ` of embeddings of separable closures over the places of `ℚ`,

  `E₁.bsdQuotient · (#Sel_φ̂ · #E₁(ℚ)[φ] · φ.kummerRatioProduct) · #φ̂(Sha(E₂)) =`
  `  E₂.bsdQuotient · (#Sel_φ · #E₂(ℚ)[φ̂]) · #φ(Sha(E₁))`. -/
theorem bsdQuotient_mul_card_selmerGroup_dual [Finite E₁.sha] [Finite E₂.sha]
    (φ : Isogeny E₁.toAffine E₂.toAffine)
    (τ : ∀ v : GlobalNumberFields.Place ℚ,
      SeparableClosure ℚ →ₐ[ℚ] SeparableClosure v.Completion) :
    E₁.bsdQuotient *
        (Nat.card (φ.dual.selmerGroup τ) * Nat.card (Hom.ofIsogeny φ).pointMapHom.ker *
          (φ.kummerRatioProduct : ℝ)) *
        Nat.card ((Hom.ofIsogeny φ.dual).shafarevichTateMap τ).range =
      E₂.bsdQuotient *
        (Nat.card (φ.selmerGroup τ) * Nat.card (Hom.ofIsogeny φ.dual).pointMapHom.ker) *
        Nat.card ((Hom.ofIsogeny φ).shafarevichTateMap τ).range := by
  have hbase := φ.bsdQuotient_mul_card_sha_mul_kummerRatioProduct_mul_kummerRatio_dual
  have hsha₁ := card_sha_eq_mul_range φ τ
  have hsha₂ := card_sha_eq_mul_range φ.dual τ
  have hsel₁ : (Nat.card (φ.selmerGroup τ) : ℝ) =
      (Hom.ofIsogeny φ).pointMapHom.range.index * Nat.card (φ.shafarevichTateGroupKer τ) := by
    exact_mod_cast φ.card_selmerGroup τ
  have hsel₂ : (Nat.card (φ.dual.selmerGroup τ) : ℝ) =
      (Hom.ofIsogeny φ.dual).pointMapHom.range.index *
        Nat.card (φ.dual.shafarevichTateGroupKer τ) := by
    exact_mod_cast φ.dual.card_selmerGroup τ
  have hk₁ : (φ.kummerRatio : ℝ) * Nat.card (Hom.ofIsogeny φ).pointMapHom.ker =
      (Hom.ofIsogeny φ).pointMapHom.range.index := by
    exact_mod_cast φ.kummerRatio_mul_card_ker
  have hk₂ : (φ.dual.kummerRatio : ℝ) * Nat.card (Hom.ofIsogeny φ.dual).pointMapHom.ker =
      (Hom.ofIsogeny φ.dual).pointMapHom.range.index := by
    exact_mod_cast φ.dual.kummerRatio_mul_card_ker
  rw [hsel₁, hsel₂, ← hk₁, ← hk₂]
  rw [hsha₁, hsha₂] at hbase
  linear_combination
    (Nat.card (Hom.ofIsogeny φ).pointMapHom.ker *
      Nat.card (Hom.ofIsogeny φ.dual).pointMapHom.ker : ℝ) * hbase

/-- **Cassels' reduction of isogeny invariance of the BSD quotient**:
`E₁.bsdQuotient = E₂.bsdQuotient` follows from the global Selmer ratio formula and the equality of
image orders `#φ(Sha(E₁)) = #φ̂(Sha(E₂))` for any family `τ` of embeddings of separable closures
over the places of `ℚ`. -/
theorem bsdQuotient_eq_of_card_selmerGroup_and_card_range_shafarevichTateMap
    [Finite E₁.sha] [Finite E₂.sha] (φ : Isogeny E₁.toAffine E₂.toAffine)
    (τ : ∀ v : GlobalNumberFields.Place ℚ,
      SeparableClosure ℚ →ₐ[ℚ] SeparableClosure v.Completion)
    (hsel : (Nat.card (φ.selmerGroup τ) : ℚ) * Nat.card (Hom.ofIsogeny φ.dual).pointMapHom.ker =
      Nat.card (φ.dual.selmerGroup τ) * Nat.card (Hom.ofIsogeny φ).pointMapHom.ker *
        φ.kummerRatioProduct)
    (hsha : Nat.card ((Hom.ofIsogeny φ).shafarevichTateMap τ).range =
      Nat.card ((Hom.ofIsogeny φ.dual).shafarevichTateMap τ).range) :
    E₁.bsdQuotient = E₂.bsdQuotient := by
  have h := φ.bsdQuotient_mul_card_selmerGroup_dual τ
  have hselR :
      (Nat.card (φ.selmerGroup τ) : ℝ) * Nat.card (Hom.ofIsogeny φ.dual).pointMapHom.ker =
        Nat.card (φ.dual.selmerGroup τ) * Nat.card (Hom.ofIsogeny φ).pointMapHom.ker *
          (φ.kummerRatioProduct : ℝ) := by
    exact_mod_cast hsel
  have : Finite (φ.selmerGroup τ) := φ.finite_selmerGroup_place τ
  have : Finite (Hom.ofIsogeny φ.dual).pointMapHom.ker :=
    (Hom.ofIsogeny φ.dual).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero φ.dual)
  have : Finite (E₂.shafarevichTateGroup τ) := by
    rwa [← E₂.sha_eq_shafarevichTateGroup τ]
  have hpos₁ :
      (0 : ℝ) < Nat.card (φ.selmerGroup τ) * Nat.card (Hom.ofIsogeny φ.dual).pointMapHom.ker :=
    mul_pos (Nat.cast_pos.2 Nat.card_pos) (Nat.cast_pos.2 Nat.card_pos)
  have hpos₂ :
      (0 : ℝ) < Nat.card ((Hom.ofIsogeny φ).shafarevichTateMap τ).range :=
    Nat.cast_pos.2 Nat.card_pos
  rw [← hselR, ← hsha] at h
  exact mul_right_cancel₀ hpos₁.ne' (mul_right_cancel₀ hpos₂.ne' h)

/-- **Isogeny invariance of the full Birch–Swinnerton-Dyer conjecture reduces to equality of the
BSD quotients**: isogenous elliptic curves over `ℚ` already share their `L`-function, Mordell–Weil
rank, and finiteness of `Sha`. -/
theorem birchSwinnertonDyer_iff_of_bsdQuotient_eq (φ : Isogeny E₁.toAffine E₂.toAffine)
    (h : ∀ [Finite E₁.sha] [Finite E₂.sha], E₁.bsdQuotient = E₂.bsdQuotient) :
    E₁.BirchSwinnertonDyer ↔ E₂.BirchSwinnertonDyer := by
  have hL : E₁.LFunction = E₂.LFunction := φ.LFunction_eq
  have hrank : Module.finrank ℤ E₁.toAffine.Point = Module.finrank ℤ E₂.toAffine.Point := by
    rw [← finrank_quotient_eq_of_le_torsion (M' := Submodule.torsion ℤ E₁.toAffine.Point) le_rfl,
      ← finrank_quotient_eq_of_le_torsion (M' := Submodule.torsion ℤ E₂.toAffine.Point) le_rfl]
    exact Hom.finrank_pointModTorsion_eq (f := Hom.ofIsogeny φ) (Hom.ofIsogeny_ne_zero φ)
  have hsha : Finite E₁.sha ↔ Finite E₂.sha :=
    (Hom.ofIsogeny φ).finite_sha_iff (Hom.ofIsogeny_ne_zero φ)
  constructor
  · intro h₁
    refine ⟨fun F U hF hU ↦ ?_, fun hF hU ↦ ?_⟩
    · rw [← hrank]
      exact h₁.analyticOrderAt_eq_finrank (by rwa [hL]) hU
    · have : Finite E₁.sha := hsha.2 inferInstance
      rw [← h]
      exact h₁.leadingCoeff_eq_bsdQuotient (by rwa [hL]) hU
  · intro h₂
    refine ⟨fun F U hF hU ↦ ?_, fun hF hU ↦ ?_⟩
    · rw [hrank]
      exact h₂.analyticOrderAt_eq_finrank (by rwa [← hL]) hU
    · have : Finite E₂.sha := hsha.1 inferInstance
      rw [h]
      exact h₂.leadingCoeff_eq_bsdQuotient (by rwa [← hL]) hU

/-- **Degree-one isogenies unconditionally preserve the Birch–Swinnerton-Dyer quotient.** -/
theorem bsdQuotient_eq_of_degree_eq_one [Finite E₁.sha] [Finite E₂.sha]
    (φ : Isogeny E₁.toAffine E₂.toAffine) (hφ : φ.degree = 1) :
    E₁.bsdQuotient = E₂.bsdQuotient := by
  have h := φ.bsdQuotient_mul_card_sha_mul_kummerRatioProduct_mul_kummerRatio_dual
  have hsha : Nat.card E₁.sha = Nat.card E₂.sha :=
    (Hom.ofIsogeny φ).card_sha_eq_of_degree_eq_one (by rw [Hom.degree_ofIsogeny, hφ])
  have hk₁ : φ.kummerRatio = 1 := kummerRatio_eq_one_of_degree_eq_one φ hφ
  have hk₂ : φ.dual.kummerRatio = 1 :=
    kummerRatio_eq_one_of_degree_eq_one φ.dual (by rw [degree_dual, hφ])
  have hkp : φ.kummerRatioProduct = 1 := kummerRatioProduct_eq_one_of_degree_eq_one φ hφ
  rw [hk₁, hk₂, hkp, hsha] at h
  simp only [Rat.cast_one, mul_one] at h
  have hpos : (Nat.card E₂.sha : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  exact mul_right_cancel₀ hpos h

/-- **Degree-one isogenies unconditionally preserve the Birch–Swinnerton-Dyer conjecture.** -/
theorem birchSwinnertonDyer_iff_of_degree_eq_one (φ : Isogeny E₁.toAffine E₂.toAffine)
    (hφ : φ.degree = 1) : E₁.BirchSwinnertonDyer ↔ E₂.BirchSwinnertonDyer :=
  birchSwinnertonDyer_iff_of_bsdQuotient_eq φ fun {_ _} ↦ φ.bsdQuotient_eq_of_degree_eq_one hφ

end BSDQuotient

end TauCeti.Isogeny

namespace WeierstrassCurve.VariableChange

/-- **The Birch–Swinnerton-Dyer quotient is invariant under a change of Weierstrass variables.** -/
@[simp]
theorem bsdQuotient_smul (C : VariableChange ℚ) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [Finite E.sha] :
    (C • E).bsdQuotient = E.bsdQuotient :=
  (TauCeti.Isogeny.bsdQuotient_eq_of_degree_eq_one
    (TauCeti.Isogeny.variableChangeIsogeny C rfl)
    (TauCeti.Isogeny.degree_variableChangeIsogeny C rfl)).symm

/-- **The Birch–Swinnerton-Dyer conjecture is invariant under a change of Weierstrass
variables.** -/
@[simp]
theorem birchSwinnertonDyer_smul_iff (C : VariableChange ℚ) (E : WeierstrassCurve ℚ)
    [E.IsElliptic] :
    (C • E).BirchSwinnertonDyer ↔ E.BirchSwinnertonDyer :=
  (TauCeti.Isogeny.birchSwinnertonDyer_iff_of_degree_eq_one
    (TauCeti.Isogeny.variableChangeIsogeny C rfl)
    (TauCeti.Isogeny.degree_variableChangeIsogeny C rfl)).symm

end WeierstrassCurve.VariableChange
