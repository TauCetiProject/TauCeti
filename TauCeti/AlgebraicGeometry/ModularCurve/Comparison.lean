/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.ExactOrder.Comparison
public import TauCeti.AlgebraicGeometry.ModularCurve.Gamma.One
public import TauCeti.AlgebraicGeometry.ModularCurve.NaiveLevel
public import TauCeti.AlgebraicGeometry.ModularCurve.YOne
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Drinfeld and naive `[Γ₁(N)]`-structures where `N` is invertible

Over a base scheme `B` on which `N` is invertible, a Drinfeld `[Γ₁(N)]`-structure on an elliptic
curve `E/S` over `B`, a point `P` of exact order `N` (`ModuliProblem.gammaOne`), is also a naive
`[Γ₁(N)]`-structure: the homomorphism `ℤ/Nℤ →* E(S)`, `a ↦ aP`, is injective on every fibre
(`EllipticCurveGeom.IsOfExactOrder.isFiberwiseInjective`). This defines a morphism of moduli
problems `[Γ₁(N)] ⟶ [Γ₁(N)]_naive` over `Ell/B`, which is an isomorphism. Consequently
the existing fine curve `Y₁(N)` represents the Drinfeld problem too for `N ≥ 4`.

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneToGammaOneNaive B N hN`: the morphism from
  Drinfeld to naive `[Γ₁(N)]`-structures over a base `B` on which `N` is invertible.

## Main results

* `TauCeti.AlgebraicGeometry.ModuliProblem.naiveLevelEquiv_gammaOneToGammaOneNaive_app_apply`: the
  naive structure of a point `P` of exact order `N` sends `a` to `aP`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.isIso_gammaOneToGammaOneNaive`: the comparison is an
  isomorphism.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneRepresentableBy`: `Y₁(N)` represents the
  Drinfeld problem for `N ≥ 4` invertible on the base.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §3.2 (`[Γ₁(N)]`-structures)
  and §3.7 (comparison with naive level structures where `N` is invertible).
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry
  MonObj

universe u

namespace TauCeti.AlgebraicGeometry

namespace ModuliProblem

variable {B : Scheme.{u}} {N : ℕ} [NeZero N]

variable (B N) in
/-- **Drinfeld `[Γ₁(N)]`-structures are naive where `N` is invertible.** Over a base `B` on which
`N` is invertible, the point `P` of exact order `N` of a `[Γ₁(N)]`-structure gives the naive
`[Γ₁(N)]`-structure `a ↦ aP`, injective on every fibre by
`EllipticCurveGeom.IsOfExactOrder.isFiberwiseInjective`. This is natural in the object of
`Ell/B`. -/
noncomputable def gammaOneToGammaOneNaive (hN : ∀ b : B, (N : B.residueField b) ≠ 0) :
    gammaOne B N ⟶ gammaOneNaive B N where
  app X := TypeCat.ofHom fun α ↦ (naiveLevelEquiv X.unop).symm
    ⟨(zmodMonoidHomEquiv N _).symm
        ⟨(gammaOneEquiv X.unop α).1, (gammaOneEquiv X.unop α).2.pow_eq_one⟩,
      EllipticCurveGeom.IsOfExactOrder.isFiberwiseInjective
        (by rw [← coe_zmodMonoidHomEquiv_apply, Equiv.apply_symm_apply]
            exact (gammaOneEquiv X.unop α).2)
        fun s ↦ X.unop.structureMap.natCast_residueField_ne_zero (hN _)⟩
  naturality X Y φ := by
    ext α
    apply (naiveLevelEquiv _).injective
    apply Subtype.ext
    apply (zmodMonoidHomEquiv N _).injective
    apply Subtype.ext
    simp only [op_unop, TypeCat.Fun.toFun_apply, comp_apply, TypeCat.hom_ofHom,
      TypeCat.Fun.coe_mk, Equiv.apply_symm_apply, coe_zmodMonoidHomEquiv_apply]
    rw [← Quiver.Hom.op_unop φ, gammaOneEquiv_map, naiveLevelEquiv_map, Equiv.apply_symm_apply,
      MonoidHom.comp_apply, ← coe_zmodMonoidHomEquiv_apply, Equiv.apply_symm_apply]

variable {hN : ∀ b : B, (N : B.residueField b) ≠ 0}

/-- The naive `[Γ₁(N)]`-structure of a point `P` of exact order `N` sends `a` to `aP`. -/
@[simp]
theorem naiveLevelEquiv_gammaOneToGammaOneNaive_app_apply (X : EllObj B)
    (α : (gammaOne B N).obj (op X)) (a : ZMod N) :
    (naiveLevelEquiv X ((gammaOneToGammaOneNaive B N hN).app (op X) α)).1 (.ofAdd a) =
      (gammaOneEquiv X α).1 ^ a.val := by
  simp [gammaOneToGammaOneNaive]

/-- **Drinfeld `[Γ₁(N)]`-structures form a subproblem of the naive ones** where `N` is
invertible: a `[Γ₁(N)]`-structure is determined by its naive `[Γ₁(N)]`-structure. -/
instance mono_gammaOneToGammaOneNaive : Mono (gammaOneToGammaOneNaive B N hN) := by
  have (X : (EllObj B)ᵒᵖ) : Mono ((gammaOneToGammaOneNaive B N hN).app X) := by
    refine (mono_iff_injective _).mpr fun α β hαβ ↦ ?_
    apply (gammaOneEquiv X.unop).injective
    apply Subtype.ext
    have := congrArg (fun γ ↦ (naiveLevelEquiv X.unop γ).1 (.ofAdd 1)) hαβ
    simpa [gammaOneToGammaOneNaive, ← coe_zmodMonoidHomEquiv_apply] using this
  exact NatTrans.mono_of_mono_app _

/-- Where `N` is invertible, the comparison from Drinfeld to naive `[Γ₁(N)]` is an
isomorphism of moduli problems. -/
instance isIso_gammaOneToGammaOneNaive : IsIso (gammaOneToGammaOneNaive B N hN) := by
  have (X : (EllObj B)ᵒᵖ) : IsIso ((gammaOneToGammaOneNaive B N hN).app X) := by
    apply (isIso_iff_bijective _).mpr
    refine ⟨(mono_iff_injective _).mp inferInstance, fun α ↦ ?_⟩
    let φ := (naiveLevelEquiv X.unop α).1
    have hφ := (naiveLevelEquiv X.unop α).2
    have hP := EllipticCurveGeom.isFiberwiseInjective_iff_isOfNaiveExactOrder.mp hφ
    let β := (gammaOneEquiv X.unop).symm
      ⟨φ (.ofAdd 1), hP.isOfExactOrder fun s ↦
        X.unop.structureMap.natCast_residueField_ne_zero (hN _)⟩
    refine ⟨β, ?_⟩
    apply (naiveLevelEquiv X.unop).injective
    apply Subtype.ext
    apply (zmodMonoidHomEquiv N _).injective
    apply Subtype.ext
    simp only [coe_zmodMonoidHomEquiv_apply]
    simp [gammaOneToGammaOneNaive, β, φ, ← coe_zmodMonoidHomEquiv_apply]
  exact NatIso.isIso_of_isIso_app _

/-- The inverse comparison retains the point given by the image of `1` under the naive level
structure. -/
@[simp]
theorem gammaOneEquiv_inv_gammaOneToGammaOneNaive_app (X : EllObj B)
    (α : (gammaOneNaive B N).obj (op X)) :
    (gammaOneEquiv X (inv ((gammaOneToGammaOneNaive B N hN).app (op X)) α)).1 =
      (naiveLevelEquiv X α).1 (.ofAdd 1) := by
  have h : (gammaOneToGammaOneNaive B N hN).app (op X)
      ((inv (gammaOneToGammaOneNaive B N hN)).app (op X) α) = α := by
    exact congrArg (fun k : gammaOneNaive B N ⟶ gammaOneNaive B N ↦ k.app (op X) α)
      (IsIso.inv_hom_id (gammaOneToGammaOneNaive B N hN))
  have hp := congrArg (fun β ↦ (naiveLevelEquiv X β).1 (Multiplicative.ofAdd 1)) h
  simpa [gammaOneToGammaOneNaive, ← coe_zmodMonoidHomEquiv_apply] using hp

/-- For `N ≥ 4` invertible on `B`, the existing fine curve `Y₁(N)` also represents the
integral Drinfeld `[Γ₁(N)]` problem restricted to `B`. -/
noncomputable def gammaOneRepresentableBy (h4 : 4 ≤ N) :
    (gammaOne B N).RepresentableBy (EllObj.yOne B N hN) :=
  (gammaOneNaiveRepresentableBy hN h4).ofIso
    (asIso (gammaOneToGammaOneNaive B N hN)).symm

/-- The Drinfeld point classified by an arrow to `Y₁(N)` is the pullback of the universal
Tate point `(0, 0)`. -/
@[simp]
theorem gammaOneEquiv_gammaOneRepresentableBy_homEquiv (h4 : 4 ≤ N) {X : EllObj B}
    (k : X ⟶ EllObj.yOne B N hN) :
    (gammaOneEquiv X ((gammaOneRepresentableBy (hN := hN) h4).homEquiv k)).1 =
      EllipticCurveGeom.pointsPullback (k ≫ EllObj.yOneι B N hN).isPullback
        (k ≫ EllObj.yOneι B N hN).zero_total (EllObj.universalTatePoint B) :=
  by
    have h : (gammaOneEquiv X ((inv (gammaOneToGammaOneNaive B N hN)).app (op X)
        ((gammaOneNaiveRepresentableBy hN h4).homEquiv k))).1 =
        EllipticCurveGeom.pointsPullback (k ≫ EllObj.yOneι B N hN).isPullback
          (k ≫ EllObj.yOneι B N hN).zero_total (EllObj.universalTatePoint B) := by
      rw [NatIso.isIso_inv_app, gammaOneEquiv_inv_gammaOneToGammaOneNaive_app]
      exact naiveLevelEquiv_gammaOneNaiveRepresentableBy_homEquiv hN h4 k
    exact h

end ModuliProblem

end TauCeti.AlgebraicGeometry
