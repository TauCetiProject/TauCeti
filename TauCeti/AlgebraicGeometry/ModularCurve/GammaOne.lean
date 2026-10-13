/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.ExactOrder.Basic
public import TauCeti.AlgebraicGeometry.ModularCurve.ModuliProblem

/-!
# The moduli problem `[Γ₁(N)]`

Following Katz and Mazur, a `[Γ₁(N)]`-structure on an elliptic curve `E` over a scheme `S` is an
`S`-point `P` of `E` of exact order `N`: the divisor `[P] + [2P] + ⋯ + [NP]` on `E` is a subgroup
scheme (`EllipticCurveGeom.IsOfExactOrder`). This is Drinfeld's notion, which makes sense over
every base, including bases on which `N` is not invertible.

An arrow `(E'/S') ⟶ (E/S)` of `Ell/B` exhibits `E'` as the base change of `E`, so every `S`-point
of `E` has a base change, an `S'`-point of `E'` (`EllipticCurveGeom.pointsPullback`), and points
of exact order `N` pull back to points of exact order `N`
(`EllipticCurveGeom.IsOfExactOrder.pointsPullback`). Base change of points is functorial, so the
`[Γ₁(N)]`-structures form a moduli problem over `Ell/B` (`ModuliProblem.gammaOne`). For `N = 1`
the only point of exact order one is the zero section, so `[Γ₁(1)]` is the trivial moduli problem
`[Γ(1)]` (`ModuliProblem.gammaOneOneIso`).

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOne B N`: the moduli problem `[Γ₁(N)]` over
  `Ell/B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneEquiv`: the `[Γ₁(N)]`-structures on an object
  `(E/S)` of `Ell/B` are the `S`-points of `E` of exact order `N`.

## Main results

* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneEquiv_map`: the pull-back of a
  `[Γ₁(N)]`-structure along an arrow of `Ell/B` is the base change of its point.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneOneIso`: `[Γ₁(1)]` is the trivial moduli
  problem.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.4 (points of exact order
  `N`), §3.2 (the moduli problem `[Γ₁(N)]`) and Chapter 4.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry
  MonObj

universe u

namespace TauCeti.AlgebraicGeometry

variable {B : Scheme.{u}}

namespace ModuliProblem

variable (B) (N : ℕ)

/-- **The moduli problem `[Γ₁(N)]`** over `Ell/B` (Katz–Mazur, §3.2). A `[Γ₁(N)]`-structure on an
object `(E/S)` of `Ell/B` is an `S`-point of `E` of exact order `N` (`gammaOneEquiv`), and it pulls
back along an arrow of `Ell/B` by base change of points (`gammaOneEquiv_map`). -/
noncomputable def gammaOne : ModuliProblem B where
  obj X := ULift.{u + 1}
    {P : 𝟙_ (Over X.unop.base) ⟶ Over.mk X.unop.curve.structureMap //
      X.unop.curve.IsOfExactOrder P N}
  map φ := TypeCat.ofHom fun P ↦
    ⟨⟨EllipticCurveGeom.pointsPullback φ.unop.isPullback φ.unop.zero_total P.down.1,
      P.down.2.pointsPullback φ.unop.isPullback φ.unop.zero_total⟩⟩
  map_id X := by
    ext P
    exact congrArg Over.Hom.left ((EllipticCurveGeom.eq_pointsPullback_iff _ _).mpr
      (by simp)).symm
  map_comp φ ψ := by
    ext P
    exact congrArg Over.Hom.left ((EllipticCurveGeom.eq_pointsPullback_iff _ _).mpr
      (by simp)).symm

variable {B N}

/-- The `[Γ₁(N)]`-structures on an object `(E/S)` of `Ell/B` are the `S`-points of `E` of exact
order `N`. -/
noncomputable def gammaOneEquiv (X : EllObj B) :
    (gammaOne B N).obj (op X) ≃
      {P : 𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap // X.curve.IsOfExactOrder P N} :=
  Equiv.ulift

/-- The pull-back of a `[Γ₁(N)]`-structure along an arrow `φ` of `Ell/B` is the base change of its
point along `φ`. -/
@[simp]
theorem gammaOneEquiv_map {X Y : EllObj B} (φ : X ⟶ Y) (α : (gammaOne B N).obj (op Y)) :
    (gammaOneEquiv X ((gammaOne B N).map φ.op α)).1 =
      EllipticCurveGeom.pointsPullback φ.isPullback φ.zero_total (gammaOneEquiv Y α).1 :=
  (rfl)

/-- An `S`-point of exact order one is the zero section, so an object of `Ell/B` has exactly one
`[Γ₁(1)]`-structure. -/
noncomputable instance (X : (EllObj B)ᵒᵖ) : Unique ((gammaOne B 1).obj X) where
  default := (gammaOneEquiv X.unop).symm ⟨1, EllipticCurveGeom.isOfExactOrder_one_iff.mpr rfl⟩
  uniq α := (gammaOneEquiv X.unop).injective <| Subtype.ext <| by
    simpa using EllipticCurveGeom.isOfExactOrder_one_iff.mp (gammaOneEquiv X.unop α).2

variable (B) in
/-- **`[Γ₁(1)]` is the trivial moduli problem** `[Γ(1)]`: the only point of exact order one of an
elliptic curve is its zero section. -/
noncomputable def gammaOneOneIso : gammaOne B 1 ≅ 𝟙_ (ModuliProblem B) :=
  isoTensorUnitOfUnique _

end ModuliProblem

end TauCeti.AlgebraicGeometry
