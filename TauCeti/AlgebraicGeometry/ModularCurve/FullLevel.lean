/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.DrinfeldBasis
public import TauCeti.AlgebraicGeometry.ModularCurve.HomLevel

/-!
# The moduli problem `[Γ(N)]`

Following Katz and Mazur, a `[Γ(N)]`-structure on an elliptic curve `E` over a scheme `S` is a
Drinfeld basis of `E[N]`: a homomorphism `φ : (ℤ/Nℤ)² →* E(S)` such that the divisor
`∑_{a ∈ (ℤ/Nℤ)²} [φ a]` on `E` is the closed subscheme `E[N]`
(`EllipticCurveGeom.IsDrinfeldBasis`). This is the notion of full level-`N` structure over every
base, including bases on which `N` is not invertible; there the naive `[Γ(N)]`-structures
(`ModuliProblem.gammaNaive`) are not the right notion.

An arrow `(E'/S') ⟶ (E/S)` of `Ell/B` exhibits `E'` as the base change of `E`, and Drinfeld bases
pull back to Drinfeld bases under base change of points
(`EllipticCurveGeom.IsDrinfeldBasis.pointsPullback`). Base change of points is functorial, so the
`[Γ(N)]`-structures form a moduli problem over `Ell/B` (`ModuliProblem.gamma`), an instance of
`ModuliProblem.homLevel`. For `N = 1` every homomorphism from the trivial group is a Drinfeld
basis, so `[Γ(1)]` is the trivial moduli problem (`ModuliProblem.gammaLevelOneIso`).

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem.gamma B N`: the moduli problem `[Γ(N)]` over `Ell/B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaEquiv`: the `[Γ(N)]`-structures on an object
  `(E/S)` of `Ell/B` are the Drinfeld bases of `E[N]`.

## Main results

* `TauCeti.AlgebraicGeometry.EllObj.Hom.isDrinfeldBasis_pointsPullback`: Drinfeld bases pull back
  along arrows of `Ell/B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaEquiv_map`: the pull-back of a `[Γ(N)]`-structure
  along an arrow of `Ell/B` is its composite with base change of points.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaLevelOneIso`: `[Γ(1)]` is the trivial moduli
  problem.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, §3.1 (the moduli problem `[Γ(N)]`) and Chapter 4.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry
  MonObj

universe u

namespace TauCeti.AlgebraicGeometry

variable {B : Scheme.{u}}

/-- **Drinfeld bases pull back along arrows of `Ell/B`**: an arrow `f : X ⟶ Y` exhibits `X` as a
base change of `Y`, and a Drinfeld basis `(ℤ/Nℤ)² →* E(S)` of `E[N]` stays one after composing
with base change of points along `f`. -/
theorem EllObj.Hom.isDrinfeldBasis_pointsPullback {X Y : EllObj B} {N : ℕ} [NeZero N]
    {φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over Y.base) ⟶ Over.mk Y.curve.structureMap)}
    (f : X ⟶ Y) (h : Y.curve.IsDrinfeldBasis N φ) :
    X.curve.IsDrinfeldBasis N
      ((EllipticCurveGeom.pointsPullback f.isPullback f.zero_total).comp φ) :=
  h.pointsPullback f.isPullback f.zero_total

namespace ModuliProblem

variable (B) (N : ℕ) [NeZero N]

/-- **The moduli problem `[Γ(N)]`** over `Ell/B` (Katz–Mazur, §3.1). A `[Γ(N)]`-structure on an
object `(E/S)` of `Ell/B` is a Drinfeld basis `φ : (ℤ/Nℤ)² →* E(S)` of `E[N]` (`gammaEquiv`), and
it pulls back along an arrow of `Ell/B` by base change of points (`gammaEquiv_map`). -/
noncomputable def gamma : ModuliProblem B :=
  homLevel B (Multiplicative (ZMod N × ZMod N)) (fun X φ ↦ X.curve.IsDrinfeldBasis N φ)
    EllObj.Hom.isDrinfeldBasis_pointsPullback

variable {B N}

/-- The `[Γ(N)]`-structures on an object `(E/S)` of `Ell/B` are the Drinfeld bases
`(ℤ/Nℤ)² →* E(S)` of `E[N]`. -/
noncomputable def gammaEquiv (X : EllObj B) :
    (gamma B N).obj (op X) ≃
      {φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap) //
        X.curve.IsDrinfeldBasis N φ} :=
  homLevelEquiv (hp := EllObj.Hom.isDrinfeldBasis_pointsPullback) X

/-- The pull-back of a `[Γ(N)]`-structure along an arrow `φ` of `Ell/B` is its composite with base
change of points along `φ`. -/
@[simp]
theorem gammaEquiv_map {X Y : EllObj B} (φ : X ⟶ Y) (α : (gamma B N).obj (op Y)) :
    (gammaEquiv X ((gamma B N).map φ.op α)).1 =
      (EllipticCurveGeom.pointsPullback φ.isPullback φ.zero_total).comp (gammaEquiv Y α).1 :=
  homLevelEquiv_map φ α

/-- Every homomorphism from the trivial group `(ℤ/1ℤ)²` is a Drinfeld basis of `E[1]`, so an object
of `Ell/B` has exactly one `[Γ(1)]`-structure. -/
noncomputable instance (X : (EllObj B)ᵒᵖ) : Unique ((gamma B 1).obj X) where
  default := (gammaEquiv X.unop).symm ⟨1, EllipticCurveGeom.isDrinfeldBasis_one 1⟩
  uniq α := (gammaEquiv X.unop).injective <| Subtype.ext <| MonoidHom.ext fun a ↦ by
    rw [Subsingleton.elim a 1, map_one, map_one]

variable (B) in
/-- **`[Γ(1)]` is the trivial moduli problem**: every homomorphism from the trivial group is a
Drinfeld basis of `E[1]`. -/
noncomputable def gammaLevelOneIso : gamma B 1 ≅ 𝟙_ (ModuliProblem B) :=
  isoTensorUnitOfUnique _

end ModuliProblem

end TauCeti.AlgebraicGeometry
