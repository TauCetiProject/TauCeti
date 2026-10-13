/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.NaiveExactOrder
public import TauCeti.AlgebraicGeometry.ModularCurve.ModuliProblem

/-!
# The naive moduli problem `[Γ₁(N)]`

A *naive `[Γ₁(N)]`-structure* on an elliptic curve `E` over a scheme `S` is an `S`-point `P` of
`E` of naive exact order `N`: `NP = 0`, and for every divisor `d ≠ N` of `N` the point `dP` meets
the zero section nowhere (`EllipticCurveGeom.IsOfNaiveExactOrder`), the scheme-theoretic form of
asking that `P` have order exactly `N` in every geometric fibre of `E`. This is the classical level
structure over bases on which `N` is invertible; over other bases the right notion is Drinfeld's
(`ModuliProblem.gammaOne`), which Katz and Mazur compare with the naive one when `N` is invertible
(Katz–Mazur 1.4.4).

Points of naive exact order `N` pull back along base change
(`EllipticCurveGeom.IsOfNaiveExactOrder.pointsPullback`), so the naive `[Γ₁(N)]`-structures form
a moduli problem over `Ell/B` (`ModuliProblem.naiveGammaOne`). It is defined over every base `B`,
but it is meant for `B` over `ℤ[1/N]`.

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem.naiveGammaOne B N`: the naive moduli problem
  `[Γ₁(N)]` over `Ell/B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.naiveGammaOneEquiv`: the naive `[Γ₁(N)]`-structures on
  an object `(E/S)` of `Ell/B` are the `S`-points of `E` of naive exact order `N`.

## Main results

* `TauCeti.AlgebraicGeometry.ModuliProblem.naiveGammaOneEquiv_map`: the pull-back of a naive
  `[Γ₁(N)]`-structure along an arrow of `Ell/B` is the base change of its point.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §3.7 and Chapter 4.
* D. Loeffler, *Modular Curves*, lecture notes, Definition 3.8.1.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

variable {B : Scheme.{u}}

namespace ModuliProblem

variable (B) (N : ℕ)

/-- **The naive moduli problem `[Γ₁(N)]`** over `Ell/B`. A naive `[Γ₁(N)]`-structure on an object
`(E/S)` of `Ell/B` is an `S`-point of `E` of naive exact order `N` (`naiveGammaOneEquiv`), and it
pulls back along an arrow of `Ell/B` by base change of points (`naiveGammaOneEquiv_map`). -/
noncomputable def naiveGammaOne : ModuliProblem B where
  obj X := ULift.{u + 1}
    {P : 𝟙_ (Over X.unop.base) ⟶ Over.mk X.unop.curve.structureMap //
      X.unop.curve.IsOfNaiveExactOrder P N}
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

/-- The naive `[Γ₁(N)]`-structures on an object `(E/S)` of `Ell/B` are the `S`-points of `E` of
naive exact order `N`. -/
noncomputable def naiveGammaOneEquiv (X : EllObj B) :
    (naiveGammaOne B N).obj (op X) ≃
      {P : 𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap //
        X.curve.IsOfNaiveExactOrder P N} :=
  Equiv.ulift

/-- The pull-back of a naive `[Γ₁(N)]`-structure along an arrow `φ` of `Ell/B` is the base change
of its point along `φ`. -/
@[simp]
theorem naiveGammaOneEquiv_map {X Y : EllObj B} (φ : X ⟶ Y)
    (α : (naiveGammaOne B N).obj (op Y)) :
    (naiveGammaOneEquiv X ((naiveGammaOne B N).map φ.op α)).1 =
      EllipticCurveGeom.pointsPullback φ.isPullback φ.zero_total (naiveGammaOneEquiv Y α).1 :=
  (rfl)

end ModuliProblem

end TauCeti.AlgebraicGeometry
