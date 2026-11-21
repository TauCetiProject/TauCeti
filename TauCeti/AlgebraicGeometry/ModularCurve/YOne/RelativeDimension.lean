/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ModularCurve.YOne.Basic
import TauCeti.AlgebraicGeometry.ModularCurve.Rigidifier.LevelThree
import TauCeti.AlgebraicGeometry.ModularCurve.Simultaneous.RelativeDimension
import TauCeti.AlgebraicGeometry.ModularCurve.YOne.LevelFour

/-!
# Relative dimension of the fine modular curve `Y₁(N)`

For `N ≥ 4` invertible on a base scheme `B`, the fine moduli scheme `Y₁(N)` (`EllObj.yOne B N`) is
already known to be smooth over `B` (`EllObj.smooth_yOne_structureMap`), by exhibiting it as a
retract over `B` of a finite étale cover of the two-dimensional universal Tate normal form base
`B × Spec ℤ[A, B][Δ⁻¹]`. Because a retract of a smooth scheme of relative dimension `2` need not
have relative dimension `1`, that argument does not determine the dimension of the fibres of
`Y₁(N)`.

This file proves that `Y₁(N)` is smooth of relative dimension `1` over `B`
(`EllObj.smoothOfRelativeDimension_one_yOne_structureMap`), by transferring smooth relative
dimension along étale surjective rigidifiers
(`ModuliProblem.RelRepData.smoothOfRelativeDimension_of_representableBy`) over open subsets
covering `B`:

* At every point of `B`, either `2` (and hence `4`) or `3` is invertible in the residue field.
* Over `B[1/2]`, comparing `[Γ₁(N)]` with the étale surjective rigidifier `[Γ₁(4)]` transfers
  relative dimension `1` from `Y₁(4)`
  (`EllObj.smoothOfRelativeDimension_one_yOne_four_structureMap`) to `Y₁(N)`.
* Over `B[1/3]`, comparing `[Γ₁(N)]` with `[Γ(3)]`, represented by `EllObj.universalLevelThree` of
  relative dimension `1` (`EllObj.smoothOfRelativeDimension_universalLevelThree_structureMap`),
  transfers relative dimension `1` to `Y₁(N)`.
* Since `EllObj.yOne B N` commutes with base change in `B` (`EllObj.isPullback_yOneBaseMap`),
  target-locality concludes the proof.

## Main results

* `TauCeti.AlgebraicGeometry.EllObj.smoothOfRelativeDimension_one_yOne_structureMap`: for `N ≥ 4`
  invertible on `B`, `Y₁(N)` is smooth of relative dimension `1` over `B`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 2.2, 4.7 and 4.12.
* D. S. Kubert, *Universal bounds on the torsion of elliptic curves*, Proc. London Math. Soc. (3)
  33 (1976), 193–237.
* D. Loeffler, *Modular Curves*, lecture notes, §3.3 and §3.8.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.EllObj

private theorem smoothOfRelativeDimension_restrict_yOne_of_open (B : Scheme.{u}) (U : B.Opens)
    (N : ℕ) [NeZero N] (hU : SmoothOfRelativeDimension 1 (yOne U.toScheme N).structureMap) :
    SmoothOfRelativeDimension 1 ((yOne B N).structureMap ∣_ U) := by
  let h₁ := (isPullback_morphismRestrict (yOne B N).structureMap U).flip
  let h₂ := isPullback_yOneBaseMap U.ι N
  let e : ↑((yOne B N).structureMap ⁻¹ᵁ U) ≅ (yOne U.toScheme N).base :=
    h₁.isoPullback ≪≫ h₂.isoPullback.symm
  have he : ((yOne B N).structureMap ∣_ U) = e.hom ≫ (yOne U.toScheme N).structureMap := by
    simp [e]
  have h : SmoothOfRelativeDimension (0 + 1) (e.hom ≫ (yOne U.toScheme N).structureMap) :=
    inferInstance
  rw [he]
  simpa only [Nat.zero_add] using h

-- Over `D(2) ⊆ B`, `4` is invertible, so `[Γ₁(4)]` transfers relative dimension `1` to `Y₁(N)`.
private theorem smoothOfRelativeDimension_one_yOne_restrict_basicOpen_two (B : Scheme.{u})
    (N : ℕ) [NeZero N] (hN : ∀ b : B, (N : B.residueField b) ≠ 0) (h4 : 4 ≤ N) :
    SmoothOfRelativeDimension 1 ((yOne B N).structureMap ∣_ B.basicOpen (2 : Γ(B, ⊤))) := by
  let U : B.Opens := B.basicOpen (2 : Γ(B, ⊤))
  have hNU (x : U.toScheme) : (N : U.toScheme.residueField x) ≠ 0 :=
    Scheme.Hom.natCast_residueField_ne_zero U.ι (hN _)
  have h4U (x : U.toScheme) : (4 : U.toScheme.residueField x) ≠ 0 := fun h4 ↦
    mul_ne_zero (B.natCast_residueField_basicOpen_ne_zero 2 x)
      (B.natCast_residueField_basicOpen_ne_zero 2 x) (by linear_combination h4)
  have : Smooth (yOne U.toScheme N).structureMap :=
    smooth_yOne_structureMap U.toScheme N hNU h4
  exact smoothOfRelativeDimension_restrict_yOne_of_open B U N <|
    ModuliProblem.RelRepData.smoothOfRelativeDimension_of_representableBy
      (ModuliProblem.gammaOneNaiveRepresentableBy h4)
      (ModuliProblem.gammaOneNaiveRepresentableBy (N := 4) le_rfl)
      ModuliProblem.gammaOneNaiveRelRepData ModuliProblem.gammaOneNaiveRelRepData
      (ModuliProblem.hasProperty_etale_gammaOneNaiveRelRepData hNU)
      (ModuliProblem.hasProperty_etale_gammaOneNaiveRelRepData h4U)
      (ModuliProblem.hasProperty_surjective_gammaOneNaiveRelRepData h4U)

-- Over `D(3) ⊆ B`, `3` is invertible, so `[Γ(3)]` transfers relative dimension `1` to `Y₁(N)`.
private theorem smoothOfRelativeDimension_one_yOne_restrict_basicOpen_three (B : Scheme.{u})
    (N : ℕ) [NeZero N] (hN : ∀ b : B, (N : B.residueField b) ≠ 0) (h4 : 4 ≤ N) :
    SmoothOfRelativeDimension 1 ((yOne B N).structureMap ∣_ B.basicOpen (3 : Γ(B, ⊤))) := by
  let U : B.Opens := B.basicOpen (3 : Γ(B, ⊤))
  have hNU (x : U.toScheme) : (N : U.toScheme.residueField x) ≠ 0 :=
    Scheme.Hom.natCast_residueField_ne_zero U.ι (hN _)
  have h3U (x : U.toScheme) : (3 : U.toScheme.residueField x) ≠ 0 :=
    B.natCast_residueField_basicOpen_ne_zero 3 x
  have : Smooth (yOne U.toScheme N).structureMap :=
    smooth_yOne_structureMap U.toScheme N hNU h4
  exact smoothOfRelativeDimension_restrict_yOne_of_open B U N <|
    ModuliProblem.RelRepData.smoothOfRelativeDimension_of_representableBy
      (ModuliProblem.gammaOneNaiveRepresentableBy h4)
      (ModuliProblem.gammaNaiveThreeRepresentableBy U.toScheme)
      ModuliProblem.gammaOneNaiveRelRepData ModuliProblem.gammaNaiveRelRepData
      (ModuliProblem.hasProperty_etale_gammaOneNaiveRelRepData hNU)
      ModuliProblem.hasProperty_etale_gammaNaiveRelRepData
      (ModuliProblem.hasProperty_surjective_gammaNaiveRelRepData h3U)

variable (B : Scheme.{u}) (N : ℕ) [NeZero N]

/-- **`Y₁(N)` is smooth of relative dimension `1` over `B`.** For `N ≥ 4` invertible on `B`, the
structure morphism of the fine moduli scheme `Y₁(N)` to `B` is smooth of relative dimension `1`. -/
theorem smoothOfRelativeDimension_one_yOne_structureMap
    (hN : ∀ b : B, (N : B.residueField b) ≠ 0) (h4 : 4 ≤ N) :
    SmoothOfRelativeDimension 1 (yOne B N).structureMap := by
  have := HasRingHomProperty.instIsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{u} 1)
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := @SmoothOfRelativeDimension.{u} 1) fun b ↦ ?_
  by_cases h2 : (2 : B.residueField b) = 0
  · have h3 : (3 : B.residueField b) ≠ 0 := fun h3 ↦
      one_ne_zero (α := B.residueField b) (by linear_combination h3 - h2)
    exact ⟨B.basicOpen (3 : Γ(B, ⊤)),
      (B.evaluation_ne_zero_iff_mem_basicOpen b trivial (3 : Γ(B, ⊤))).mp
        (by simpa only [map_ofNat] using h3),
      smoothOfRelativeDimension_one_yOne_restrict_basicOpen_three B N hN h4⟩
  · exact ⟨B.basicOpen (2 : Γ(B, ⊤)),
      (B.evaluation_ne_zero_iff_mem_basicOpen b trivial (2 : Γ(B, ⊤))).mp
        (by simpa only [map_ofNat] using h2),
      smoothOfRelativeDimension_one_yOne_restrict_basicOpen_two B N hN h4⟩

end TauCeti.AlgebraicGeometry.EllObj
