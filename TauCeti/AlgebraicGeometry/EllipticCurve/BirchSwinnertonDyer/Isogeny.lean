/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny.Ratio
public import TauCeti.AlgebraicGeometry.EllipticCurve.BirchSwinnertonDyer.Quotient
public import TauCeti.AlgebraicGeometry.EllipticCurve.BirchSwinnertonDyer.Statement
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Sha
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Finite
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.Regulator.Isogeny
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny.ProductFormula
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Cokernel
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.LFunction.Isogeny

/-!
# The Birch–Swinnerton-Dyer quotient along an isogeny

Let `K` be a field with a theory of heights, and `E₁`, `E₂` elliptic curves over `K` whose
groups of rational points are finitely generated modulo torsion. Let `ψ : E₁ → E₂` be a separable
isogeny with separable dual `ψ̂`, and fix a family of field extensions of `K` along which
Shafarevich–Tate groups and Selmer groups are cut out. The descent sequences of `ψ` and `ψ̂` read

  `#Sel_ψ = [E₂(K) : ψ E₁(K)] · #Sha(E₁)[ψ]`,   `#Sel_ψ̂ = [E₁(K) : ψ̂ E₂(K)] · #Sha(E₂)[ψ̂]`,

and combined with the transformation of `Reg / #tors²` under `ψ`
(`TauCeti.Isogeny.Hom.regulator_div_card_torsion_sq_mul_index_dual_div_card_ker_eq`) they give

  `Reg(E₁) · #Sha(E₁)[ψ] / #E₁(K)_tors² · (#Sel_ψ̂ / #E₂(K)[ψ̂]) =
    (#Sel_ψ / #E₁(K)[ψ]) · Reg(E₂) · #Sha(E₂)[ψ̂] / #E₂(K)_tors²`.

If moreover `ψ` and `ψ̂` induce the zero map on Shafarevich–Tate groups, then `Sha(E₁)[ψ]` and
`Sha(E₂)[ψ̂]` are the whole groups `Sha(E₁)` and `Sha(E₂)`. When `Sha(E₂)` is finite, every
nonzero morphism `f : E₁ → E₂` has a multiple that is an isogeny killing Sha in both directions,
namely `ψ = #Sha(E₂) • f` (`TauCeti.Isogeny.Hom.exists_isogeny_shafarevichTateMap_eq_zero`).

Over `ℚ`, with `Sha` finite, combining this with Cassels' global period–Tamagawa–Kummer product
formula (`TauCeti.Isogeny.minimalRealPeriod_mul_tamagawaProduct_mul_kummerRatioProduct`),

  `Ω(E₁) · (∏_p c_p(E₁)) · φ.kummerRatioProduct = Ω(E₂) · (∏_p c_p(E₂))`,

gives the master algebraic identity

  `E₁.bsdQuotient · #Sha(E₂) · φ.kummerRatioProduct · φ.dual.kummerRatio =`
  `  E₂.bsdQuotient · #Sha(E₁) · φ.kummerRatio`,

and its Selmer-and-`Sha`-image form, reducing the isogeny invariance of
`WeierstrassCurve.bsdQuotient` and `WeierstrassCurve.BirchSwinnertonDyer` to the global Selmer
ratio formula and `#φ(Sha(E₁)) = #φ̂(Sha(E₂))`. For degree-one isogenies, and in particular changes
of Weierstrass variables, both invariants and the full Birch–Swinnerton-Dyer conjecture are
unconditionally preserved.

## Main results

* `regulator_mul_card_shafarevichTateGroupKer_div_card_torsion_sq_mul_card_selmerGroup_dual_eq`:
  the regulator, Sha-kernel and torsion factors along a separable isogeny.
* `regulator_mul_card_shafarevichTateGroup_div_card_torsion_sq_mul_card_selmerGroup_dual_eq`:
  the regulator, Sha and torsion factors along an isogeny that kills Sha in both directions.
* `TauCeti.Isogeny.bsdQuotient_div_bsdQuotient`: the ratio of Birch–Swinnerton-Dyer quotients over
  `ℚ` along such an isogeny.
* `TauCeti.Isogeny.Hom.exists_isogeny_bsdQuotient_div_bsdQuotient`: for every nonzero morphism
  over `ℚ`, the same ratio along the isogeny `#Sha(E₂) • f`.
* `TauCeti.Isogeny.bsdQuotient_mul_card_sha_mul_kummerRatioProduct_mul_kummerRatio_dual`: the
  master algebraic relation between `E₁.bsdQuotient` and `E₂.bsdQuotient` via `Sha` and the
  Kummer ratios.
* `TauCeti.Isogeny.bsdQuotient_mul_card_selmerGroup_dual`: the Selmer-and-`Sha`-image form of the
  relation for any family `τ` of embeddings of separable closures over the places of `ℚ`.
* `TauCeti.Isogeny.bsdQuotient_eq_of_card_selmerGroup_and_card_range_shaMap`:
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
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
-/

public section

noncomputable section

namespace TauCeti.Isogeny

open Height WeierstrassCurve WeierstrassCurve.Affine TauCeti.ContCohomology
open Hom (ofIsogeny)

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
        Nat.card (Hom.ofIsogeny φ.dual).shaMap.range =
      E₂.bsdQuotient *
        (Nat.card (φ.selmerGroup τ) * Nat.card (Hom.ofIsogeny φ.dual).pointMapHom.ker) *
        Nat.card (Hom.ofIsogeny φ).shaMap.range := by
  have hbase := φ.bsdQuotient_mul_card_sha_mul_kummerRatioProduct_mul_kummerRatio_dual
  have hsha₁ : (Nat.card E₁.sha : ℝ) =
      Nat.card (φ.shafarevichTateGroupKer τ) * Nat.card (Hom.ofIsogeny φ).shaMap.range := by
    exact_mod_cast φ.card_sha_eq_card_shafarevichTateGroupKer_mul τ
  have hsha₂ : (Nat.card E₂.sha : ℝ) =
      Nat.card (φ.dual.shafarevichTateGroupKer τ) *
        Nat.card (Hom.ofIsogeny φ.dual).shaMap.range := by
    exact_mod_cast φ.dual.card_sha_eq_card_shafarevichTateGroupKer_mul τ
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
theorem bsdQuotient_eq_of_card_selmerGroup_and_card_range_shaMap
    [Finite E₁.sha] [Finite E₂.sha] (φ : Isogeny E₁.toAffine E₂.toAffine)
    (τ : ∀ v : GlobalNumberFields.Place ℚ,
      SeparableClosure ℚ →ₐ[ℚ] SeparableClosure v.Completion)
    (hsel : (Nat.card (φ.selmerGroup τ) : ℚ) * Nat.card (Hom.ofIsogeny φ.dual).pointMapHom.ker =
      Nat.card (φ.dual.selmerGroup τ) * Nat.card (Hom.ofIsogeny φ).pointMapHom.ker *
        φ.kummerRatioProduct)
    (hsha : Nat.card (Hom.ofIsogeny φ).shaMap.range =
      Nat.card (Hom.ofIsogeny φ.dual).shaMap.range) :
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
  have hpos₁ :
      (0 : ℝ) < Nat.card (φ.selmerGroup τ) * Nat.card (Hom.ofIsogeny φ.dual).pointMapHom.ker :=
    mul_pos (Nat.cast_pos.2 Nat.card_pos) (Nat.cast_pos.2 Nat.card_pos)
  have hpos₂ : (0 : ℝ) < Nat.card (Hom.ofIsogeny φ).shaMap.range :=
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

section Regulator

variable {F : Type*} [Field F] [DecidableEq F] [AdmissibleAbsValues F]
  {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
  [Module.Finite ℤ (PointModTorsion W₁.toAffine)] [Module.Finite ℤ (PointModTorsion W₂.toAffine)]
  {ι : Type*} {L : ι → Type*} [∀ i, Field (L i)] [∀ i, Algebra F (L i)]
  (τ : ∀ i, SeparableClosure F →ₐ[F] SeparableClosure (L i))
  (ψ : Isogeny W₁.toAffine W₂.toAffine)
  [Algebra.IsSeparable ψ.fieldPullback.fieldRange W₁.toAffine.FunctionField]
  [Algebra.IsSeparable ψ.dual.fieldPullback.fieldRange W₂.toAffine.FunctionField]

/-- **The regulator, Sha-kernel and torsion factors along an isogeny**: for a separable isogeny
`ψ : W₁ → W₂` with separable dual `ψ̂`,

  `Reg(W₁) · #Sha(W₁)[ψ] / #W₁(F)_tors² · (#Sel_ψ̂ / #W₂(F)[ψ̂]) =
    (#Sel_ψ / #W₁(F)[ψ]) · Reg(W₂) · #Sha(W₂)[ψ̂] / #W₂(F)_tors²`,

where `W₁(F)[ψ]` is the kernel of `ψ` on rational points and `Sha(W₁)[ψ]` its kernel on
Shafarevich–Tate groups. Orders are read as `0` when infinite. -/
theorem regulator_mul_card_shafarevichTateGroupKer_div_card_torsion_sq_mul_card_selmerGroup_dual_eq
    : regulator W₁.toAffine * Nat.card (ψ.shafarevichTateGroupKer τ) /
          Nat.card (AddCommGroup.torsion W₁.toAffine.Point) ^ 2 *
        (Nat.card (ψ.dual.selmerGroup τ) / Nat.card (ofIsogeny ψ.dual).pointMapHom.ker) =
      Nat.card (ψ.selmerGroup τ) / Nat.card (ofIsogeny ψ).pointMapHom.ker *
        (regulator W₂.toAffine * Nat.card (ψ.dual.shafarevichTateGroupKer τ) /
          Nat.card (AddCommGroup.torsion W₂.toAffine.Point) ^ 2) := by
  have h := Hom.regulator_div_card_torsion_sq_mul_index_dual_div_card_ker_eq
    (Hom.ofIsogeny_ne_zero ψ)
  rw [Hom.dual_ofIsogeny] at h
  rw [card_selmerGroup ψ τ, card_selmerGroup ψ.dual τ]
  push_cast
  linear_combination (Nat.card (ψ.shafarevichTateGroupKer τ) : ℝ) *
    Nat.card (ψ.dual.shafarevichTateGroupKer τ) * h

/-- **The regulator, Sha and torsion factors along an isogeny killing Sha**: if a separable
isogeny `ψ : W₁ → W₂` with separable dual `ψ̂` induces the zero map on Shafarevich–Tate groups, as
does `ψ̂`, then

  `Reg(W₁) · #Sha(W₁) / #W₁(F)_tors² · (#Sel_ψ̂ / #W₂(F)[ψ̂]) =
    (#Sel_ψ / #W₁(F)[ψ]) · Reg(W₂) · #Sha(W₂) / #W₂(F)_tors²`,

where `W₁(F)[ψ]` is the kernel of `ψ` on rational points. Orders are read as `0` when infinite. -/
theorem regulator_mul_card_shafarevichTateGroup_div_card_torsion_sq_mul_card_selmerGroup_dual_eq
    (h₁ : (ofIsogeny ψ).shafarevichTateMap τ = 0)
    (h₂ : (ofIsogeny ψ.dual).shafarevichTateMap τ = 0) :
    regulator W₁.toAffine * Nat.card (W₁.shafarevichTateGroup τ) /
          Nat.card (AddCommGroup.torsion W₁.toAffine.Point) ^ 2 *
        (Nat.card (ψ.dual.selmerGroup τ) / Nat.card (ofIsogeny ψ.dual).pointMapHom.ker) =
      Nat.card (ψ.selmerGroup τ) / Nat.card (ofIsogeny ψ).pointMapHom.ker *
        (regulator W₂.toAffine * Nat.card (W₂.shafarevichTateGroup τ) /
          Nat.card (AddCommGroup.torsion W₂.toAffine.Point) ^ 2) := by
  have h :=
    regulator_mul_card_shafarevichTateGroupKer_div_card_torsion_sq_mul_card_selmerGroup_dual_eq τ ψ
  rwa [shafarevichTateGroupKer_eq_ker_shafarevichTateMap,
    shafarevichTateGroupKer_eq_ker_shafarevichTateMap, AddMonoidHom.ker_eq_top_iff.2 h₁,
    AddMonoidHom.ker_eq_top_iff.2 h₂, AddSubgroup.card_top, AddSubgroup.card_top] at h

end Regulator

section Rat

variable {E₁ E₂ : WeierstrassCurve ℚ} [E₁.IsElliptic] [E₂.IsElliptic] [Finite E₁.sha]
  [Finite E₂.sha]
  (τ : ∀ v : GlobalNumberFields.Place ℚ, SeparableClosure ℚ →ₐ[ℚ] SeparableClosure v.Completion)

/-- **The ratio of Birch–Swinnerton-Dyer quotients along an isogeny killing Sha**: let `E₁` and
`E₂` be elliptic curves over `ℚ` with finite Shafarevich–Tate groups. If an isogeny
`ψ : E₁ → E₂` and its dual `ψ̂` induce the zero map on Shafarevich–Tate groups, then

  `BSD(E₁) / BSD(E₂) = (#Sel_ψ / #Sel_ψ̂) / (#E₁(ℚ)[ψ] / #E₂(ℚ)[ψ̂]) ·
    (Ω(E₁) · ∏_p c_p(E₁)) / (Ω(E₂) · ∏_p c_p(E₂))`,

with `Ω` the real period of a global minimal equation and `c_p` the local Tamagawa numbers. The
Selmer groups are cut out at every place of `ℚ`. -/
theorem bsdQuotient_div_bsdQuotient (ψ : Isogeny E₁.toAffine E₂.toAffine)
    (h₁ : (ofIsogeny ψ).shafarevichTateMap τ = 0)
    (h₂ : (ofIsogeny ψ.dual).shafarevichTateMap τ = 0) :
    E₁.bsdQuotient / E₂.bsdQuotient =
      (Nat.card (ψ.selmerGroup τ) / Nat.card (ψ.dual.selmerGroup τ)) /
          (Nat.card (ofIsogeny ψ).pointMapHom.ker / Nat.card (ofIsogeny ψ.dual).pointMapHom.ker) *
        (E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ) /
          (E₂.minimalRealPeriod * E₂.tamagawaProduct (R := ℤ))) := by
  have h :=
    regulator_mul_card_shafarevichTateGroup_div_card_torsion_sq_mul_card_selmerGroup_dual_eq
      τ ψ h₁ h₂
  rw [← E₁.sha_eq_shafarevichTateGroup τ, ← E₂.sha_eq_shafarevichTateGroup τ] at h
  -- every factor is positive, so the identity can be cleared of denominators
  have := ψ.finite_selmerGroup_place τ
  have := ψ.dual.finite_selmerGroup_place τ
  have := (ofIsogeny ψ).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero ψ)
  have := (ofIsogeny ψ.dual).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero ψ.dual)
  have := finite_torsion (W := E₁.toAffine)
  have := finite_torsion (W := E₂.toAffine)
  have := E₁.minimalRealPeriod_pos
  have := E₂.minimalRealPeriod_pos
  have := E₁.tamagawaProduct_pos (R := ℤ)
  have := E₂.tamagawaProduct_pos (R := ℤ)
  have := E₂.toAffine.regulator_pos
  have : 0 < Nat.card E₁.sha := Nat.card_pos
  have : 0 < Nat.card E₂.sha := Nat.card_pos
  have : 0 < Nat.card (ψ.selmerGroup τ) := Nat.card_pos
  have : 0 < Nat.card (ψ.dual.selmerGroup τ) := Nat.card_pos
  have : 0 < Nat.card (ofIsogeny ψ).pointMapHom.ker := Nat.card_pos
  have : 0 < Nat.card (ofIsogeny ψ.dual).pointMapHom.ker := Nat.card_pos
  have : 0 < Nat.card (AddCommGroup.torsion E₁.toAffine.Point) := Nat.card_pos
  have : 0 < Nat.card (AddCommGroup.torsion E₂.toAffine.Point) := Nat.card_pos
  rw [bsdQuotient_def, bsdQuotient_def, div_eq_iff (by positivity)]
  field_simp at h ⊢
  linear_combination h

/-- **The ratio of Birch–Swinnerton-Dyer quotients along an isogeny**: let `E₁` and `E₂` be
elliptic curves over `ℚ` with finite Shafarevich–Tate groups. For every nonzero morphism
`f : E₁ → E₂`, the multiple `ψ = #Sha(E₂) • f` is an isogeny along which

  `BSD(E₁) / BSD(E₂) = (#Sel_ψ / #Sel_ψ̂) / (#E₁(ℚ)[ψ] / #E₂(ℚ)[ψ̂]) ·
    (Ω(E₁) · ∏_p c_p(E₁)) / (Ω(E₂) · ∏_p c_p(E₂))`.

So `BSD(E₁) = BSD(E₂)` holds exactly when

  `#Sel_ψ / #Sel_ψ̂ = (#E₁(ℚ)[ψ] / #E₂(ℚ)[ψ̂]) · (Ω(E₂) · ∏_p c_p(E₂)) / (Ω(E₁) · ∏_p c_p(E₁))`. -/
theorem Hom.exists_isogeny_bsdQuotient_div_bsdQuotient {f : Hom E₁.toAffine E₂.toAffine}
    (hf : f ≠ 0) :
    ∃ ψ : Isogeny E₁.toAffine E₂.toAffine, ofIsogeny ψ = Nat.card E₂.sha • f ∧
      E₁.bsdQuotient / E₂.bsdQuotient =
        (Nat.card (ψ.selmerGroup τ) / Nat.card (ψ.dual.selmerGroup τ)) /
            (Nat.card (ofIsogeny ψ).pointMapHom.ker /
              Nat.card (ofIsogeny ψ.dual).pointMapHom.ker) *
          (E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ) /
            (E₂.minimalRealPeriod * E₂.tamagawaProduct (R := ℤ))) := by
  have : Finite (E₂.shafarevichTateGroup τ) := by rwa [← E₂.sha_eq_shafarevichTateGroup τ]
  obtain ⟨ψ, hψ, h₁, h₂⟩ := f.exists_isogeny_shafarevichTateMap_eq_zero τ hf
  rw [← E₂.sha_eq_shafarevichTateGroup τ] at hψ
  exact ⟨ψ, hψ, bsdQuotient_div_bsdQuotient τ ψ h₁ h₂⟩

end Rat

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

end
