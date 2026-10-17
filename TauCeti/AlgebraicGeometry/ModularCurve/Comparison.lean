/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.ExactOrder.Naive
public import TauCeti.AlgebraicGeometry.ModularCurve.FullLevel
public import TauCeti.AlgebraicGeometry.ModularCurve.Gamma.One
public import TauCeti.AlgebraicGeometry.ModularCurve.NaiveLevel
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.DrinfeldBasis.Naive
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Drinfeld and naive level structures where `N` is invertible

Over a base scheme `B` on which `N` is invertible, a Drinfeld `[Γ₁(N)]`-structure on an elliptic
curve `E/S` over `B`, a point `P` of exact order `N` (`ModuliProblem.gammaOne`), is also a naive
`[Γ₁(N)]`-structure: the homomorphism `ℤ/Nℤ →* E(S)`, `a ↦ aP`, is injective on every fibre
(`EllipticCurveGeom.IsOfExactOrder.isFiberwiseInjective`). This defines a morphism of moduli
problems `[Γ₁(N)] ⟶ [Γ₁(N)]_naive` over `Ell/B`, which is injective on every object.

For full level `N` the comparison is an isomorphism. Over such a base, a homomorphism
`φ : (ℤ/Nℤ)² →* E(S)` is a Drinfeld basis of `E[N]` exactly when it is injective on every fibre
(`EllipticCurveGeom.isDrinfeldBasis_iff_isFiberwiseInjective`), so the moduli problem `[Γ(N)]`
(`ModuliProblem.gamma`) is the naive moduli problem `[Γ(N)]` (`ModuliProblem.gammaNaive`) over
`Ell/B`, by an isomorphism keeping the underlying homomorphism.

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneToGammaOneNaive B N hN`: the morphism from
  Drinfeld to naive `[Γ₁(N)]`-structures over a base `B` on which `N` is invertible.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaIsoGammaNaive B N hN`: the isomorphism between
  Drinfeld and naive `[Γ(N)]`-structures over a base `B` on which `N` is invertible.

## Main results

* `TauCeti.AlgebraicGeometry.ModuliProblem.naiveLevelEquiv_gammaOneToGammaOneNaive_app_apply`: the
  naive structure of a point `P` of exact order `N` sends `a` to `aP`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.mono_gammaOneToGammaOneNaive`: the morphism is a
  monomorphism, so Drinfeld `[Γ₁(N)]`-structures form a subproblem of the naive ones.
* `TauCeti.AlgebraicGeometry.ModuliProblem.naiveLevelEquiv_gammaIsoGammaNaive_hom_app` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.gammaEquiv_gammaIsoGammaNaive_inv_app`: the isomorphism
  keeps the underlying homomorphism `(ℤ/Nℤ)² →* E(S)`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §3.1 (`[Γ(N)]`-structures),
  §3.2 (`[Γ₁(N)]`-structures) and §3.7 (comparison with naive level structures where `N` is
  invertible).
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

/-! ### Full level `N` -/

variable (B N) in
/-- **Drinfeld and naive `[Γ(N)]`-structures agree where `N` is invertible** (Katz–Mazur §3.7).
Over a base `B` on which `N` is invertible, a homomorphism `φ : (ℤ/Nℤ)² →* E(S)` is a Drinfeld
basis of `E[N]` exactly when it is injective on every fibre, so the moduli problem `[Γ(N)]` is
isomorphic to the naive moduli problem `[Γ(N)]` over `Ell/B`, by an isomorphism keeping the
underlying homomorphism. -/
noncomputable def gammaIsoGammaNaive (hN : ∀ b : B, (N : B.residueField b) ≠ 0) :
    gamma B N ≅ gammaNaive B N :=
  NatIso.ofComponents (fun X ↦ ((gammaEquiv X.unop).trans <|
      (Equiv.subtypeEquivRight fun _ ↦ EllipticCurveGeom.isDrinfeldBasis_iff_isFiberwiseInjective
        fun _ ↦ X.unop.structureMap.natCast_residueField_ne_zero (hN _)).trans
      (naiveLevelEquiv X.unop).symm).toIso) fun f ↦ by
    ext α
    apply (naiveLevelEquiv _).injective
    apply Subtype.ext
    simp only [op_unop, TypeCat.Fun.toFun_apply, comp_apply, Equiv.toIso_hom_hom_apply,
      Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.subtypeEquivRight_apply_coe]
    rw [← Quiver.Hom.op_unop f, gammaEquiv_map, naiveLevelEquiv_map, Equiv.apply_symm_apply,
      Equiv.subtypeEquivRight_apply_coe]

/-- The naive `[Γ(N)]`-structure of a Drinfeld basis `φ` under `gammaIsoGammaNaive` is `φ`. -/
@[simp]
theorem naiveLevelEquiv_gammaIsoGammaNaive_hom_app (X : EllObj B) (α : (gamma B N).obj (op X)) :
    (naiveLevelEquiv X ((gammaIsoGammaNaive B N hN).hom.app (op X) α)).1 = (gammaEquiv X α).1 := by
  simp [gammaIsoGammaNaive]

/-- The `[Γ(N)]`-structure of a naive `[Γ(N)]`-structure `φ` under `gammaIsoGammaNaive` is `φ`. -/
@[simp]
theorem gammaEquiv_gammaIsoGammaNaive_inv_app (X : EllObj B) (α : (gammaNaive B N).obj (op X)) :
    (gammaEquiv X ((gammaIsoGammaNaive B N hN).inv.app (op X) α)).1 = (naiveLevelEquiv X α).1 := by
  simp [gammaIsoGammaNaive]

end ModuliProblem

end TauCeti.AlgebraicGeometry
