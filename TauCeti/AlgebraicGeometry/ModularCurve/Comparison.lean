/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.ExactOrder.Naive
public import TauCeti.AlgebraicGeometry.ModularCurve.GammaOne
public import TauCeti.AlgebraicGeometry.ModularCurve.NaiveLevel

/-!
# Drinfeld and naive `[Γ₁(N)]`-structures where `N` is invertible

Over a base scheme `B` on which `N` is invertible, a Drinfeld `[Γ₁(N)]`-structure on an elliptic
curve `E/S` over `B`, a point `P` of exact order `N` (`ModuliProblem.gammaOne`), is also a naive
`[Γ₁(N)]`-structure: the homomorphism `ℤ/Nℤ →* E(S)`, `a ↦ aP`, is injective on every fibre
(`EllipticCurveGeom.IsOfExactOrder.isFiberwiseInjective`). This defines a morphism of moduli
problems `[Γ₁(N)] ⟶ [Γ₁(N)]_naive` over `Ell/B`, which is injective on every object.

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneToGammaOneNaive B N hN`: the morphism from
  Drinfeld to naive `[Γ₁(N)]`-structures over a base `B` on which `N` is invertible.

## Main results

* `TauCeti.AlgebraicGeometry.ModuliProblem.naiveLevelEquiv_gammaOneToGammaOneNaive_app_apply`: the
  naive structure of a point `P` of exact order `N` sends `a` to `aP`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.mono_gammaOneToGammaOneNaive`: the morphism is a
  monomorphism, so Drinfeld `[Γ₁(N)]`-structures form a subproblem of the naive ones.

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

variable {B : Scheme.{u}} {N : ℕ}

/-- If `N` is invertible on `B`, it is invertible on the base of every object of `Ell/B`. -/
private theorem natCast_residueField_ne_zero (hN : ∀ b : B, (N : B.residueField b) ≠ 0)
    (X : EllObj B) (s : X.base) : (N : X.base.residueField s) ≠ 0 := by
  rw [← map_natCast (X.structureMap.residueFieldMap s).hom]
  exact (map_ne_zero _).mpr (hN _)

variable [NeZero N]

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
        (natCast_residueField_ne_zero hN X.unop)⟩
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

end ModuliProblem

end TauCeti.AlgebraicGeometry
