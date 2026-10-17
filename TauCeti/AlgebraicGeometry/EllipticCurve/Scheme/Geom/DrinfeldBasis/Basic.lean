/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.PointsDivisor
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion

/-!
# Drinfeld bases of the `N`-torsion of an elliptic curve

Let `E` be an elliptic curve over a scheme `S` and `N` a positive integer. Following Drinfeld and
Katz–Mazur, a **Drinfeld basis** of `E[N]`, or `[Γ(N)]`-structure on `E`, is a homomorphism
`φ : (ℤ/Nℤ)² →* E(S)` to the group of `S`-points of `E` such that the effective Cartier divisor

  `D = ∑_{a ∈ (ℤ/Nℤ)²} [φ a]`

on `E` is the closed subscheme `E[N]` (`EllipticCurveGeom.IsDrinfeldBasis`). In the language of
Katz and Mazur, `φ` is a `(ℤ/Nℤ)²`-generator of the subgroup scheme `E[N]` of the curve `E`; they
show that this says that the `N²` points `φ a`, counted with multiplicity, form a full set of
sections of the finite locally free `S`-scheme `E[N]`. That comparison is not made here.

The definition makes sense over every base, including bases on which `N` is not invertible, where
the points `φ a` need not be distinct: for a supersingular elliptic curve over a field of
characteristic `p`, the subgroup scheme `E[p]` is the divisor `p²[0]`, so the homomorphism all of
whose points are the zero section is a Drinfeld basis of `E[p]`. It is the integral counterpart
of the naive `[Γ(N)]`-structures (`EllipticCurveGeom.IsFiberwiseInjective`), which ask instead
that the `φ a` be distinct in every fibre and are the right notion only where `N` is invertible.
Every naive full level structure is a Drinfeld basis over an arbitrary base; this direction is
proved in `DrinfeldBasis.Naive`. The converse where `N` is invertible remains to be established.

The divisor `∑_a [φ a]` is the divisor of a finite family of `S`-points of `E`
(`EllipticCurveGeom.pointsDivisor`), the product of the ideal sheaves of the sections `φ a`; it is
a relative effective Cartier divisor on `E` over `S`. The `N`-torsion `E[N]` is the inverse
image `[N]⁻¹[0]` of the zero-section divisor (`EllipticCurveGeom.ker_torsionι_left`), so a Drinfeld
basis is a homomorphism with `∑_a [φ a] = [N]⁻¹[0]` (`EllipticCurveGeom.isDrinfeldBasis_iff`).

Both `∑_a [φ a]` and `E[N]` are compatible with base change
(`EllipticCurveGeom.pointsDivisor_pointsPullback`,
`EllipticCurveGeom.ker_torsionι_left_of_isPullback`), so Drinfeld bases are stable under arbitrary
base change (`EllipticCurveGeom.IsDrinfeldBasis.pointsPullback`). The divisor does not depend on
how its points are indexed, so precomposing a Drinfeld basis with an automorphism of `(ℤ/Nℤ)²`, in
particular with an element of `GL₂(ℤ/Nℤ)`, gives a Drinfeld basis
(`EllipticCurveGeom.isDrinfeldBasis_comp_mulEquiv_iff`). For `N = 1` every homomorphism is a
Drinfeld basis (`EllipticCurveGeom.isDrinfeldBasis_one`).

Following `EllipticCurveGeom.mulBy`, the group law on points of `E` is written multiplicatively.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsDrinfeldBasis E N φ`: the homomorphism
  `φ : (ℤ/Nℤ)² →* E(S)` is a Drinfeld basis of `E[N]`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isDrinfeldBasis_iff`: a Drinfeld basis is a
  homomorphism with `∑_a [φ a] = [N]⁻¹[0]`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsDrinfeldBasis.pointsPullback`: Drinfeld bases
  are stable under base change.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isDrinfeldBasis_comp_mulEquiv_iff`: Drinfeld bases
  are stable under automorphisms of `(ℤ/Nℤ)²`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isDrinfeldBasis_one`: every homomorphism is a
  Drinfeld basis of `E[1]`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, Chapter 1 (generators of a subgroup scheme of a smooth
  curve, and full sets of sections) and §3.1 (`[Γ(N)]`-structures).
* V. G. Drinfeld, *Elliptic modules*, Mat. Sb. 94 (136) (1974), 594–627.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S) (N : ℕ) [NeZero N]

/-- **Drinfeld bases of `E[N]`** (Drinfeld; Katz–Mazur §3.1). A homomorphism
`φ : (ℤ/Nℤ)² →* E(S)` to the group of `S`-points of an elliptic curve `E` over `S` is a Drinfeld
basis of the `N`-torsion `E[N]`, or `[Γ(N)]`-structure on `E`, when the divisor
`∑_{a ∈ (ℤ/Nℤ)²} [φ a]` on `E` is the closed subscheme `E[N]`: their ideal sheaves agree.
Equivalently (`isDrinfeldBasis_iff`), `∑_a [φ a]` is the inverse image `[N]⁻¹[0]` of the zero
section. The points `φ a` are counted with multiplicity and need not be distinct. -/
def IsDrinfeldBasis
    (φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) : Prop :=
  E.pointsDivisor φ = (E.torsionι N).left.ker

variable {E N}

/-- **A Drinfeld basis is a homomorphism with `∑_a [φ a] = [N]⁻¹[0]`.** -/
theorem isDrinfeldBasis_iff
    {φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)} :
    E.IsDrinfeldBasis N φ ↔ E.pointsDivisor φ = E.zero.ker.comap (E.mulBy N).left := by
  rw [IsDrinfeldBasis, ker_torsionι_left]

/-- **Drinfeld bases are stable under automorphisms of `(ℤ/Nℤ)²`.** Precomposing with an
automorphism `σ`, for instance the right action of an element of `GL₂(ℤ/Nℤ)`, reindexes the
divisor `∑_a [φ a]` without changing it. -/
@[simp]
theorem isDrinfeldBasis_comp_mulEquiv_iff
    {φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)}
    (σ : Multiplicative (ZMod N × ZMod N) ≃* Multiplicative (ZMod N × ZMod N)) :
    E.IsDrinfeldBasis N (φ.comp ↑σ) ↔ E.IsDrinfeldBasis N φ := by
  rw [IsDrinfeldBasis, IsDrinfeldBasis, MonoidHom.coe_comp, MonoidHom.coe_ofClass]
  exact Iff.of_eq (congrArg (· = _) (pointsDivisor_comp_equiv φ σ.toEquiv))

/-- **Every homomorphism is a Drinfeld basis of `E[1]`**: both `[0]` and `E[1]` are the zero
section. -/
theorem isDrinfeldBasis_one
    (φ : Multiplicative (ZMod 1 × ZMod 1) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    E.IsDrinfeldBasis 1 φ := by
  rw [isDrinfeldBasis_iff, pointsDivisor_def, Fintype.prod_subsingleton _ 1]
  simp [mulBy_one, hom_one_left]

section BaseChange

variable {S' : Scheme.{u}} {E' : EllipticCurveGeom S'} {g : E'.carrier ⟶ E.carrier}
  {f : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap f)
  (h0 : E'.zero ≫ g = f ≫ E.zero)

/-- **Drinfeld bases are stable under base change** (Katz–Mazur §3.1): if `φ : (ℤ/Nℤ)² →* E(S)` is
a Drinfeld basis of `E[N]`, then so is its composite with base change of points,
`(ℤ/Nℤ)² →* E'(S')`. -/
theorem IsDrinfeldBasis.pointsPullback
    {φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)}
    (h : E.IsDrinfeldBasis N φ) : E'.IsDrinfeldBasis N ((pointsPullback hg h0).comp φ) := by
  rw [IsDrinfeldBasis, MonoidHom.coe_comp, pointsDivisor_pointsPullback, h,
    ker_torsionι_left_of_isPullback _ hg h0]

end BaseChange

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
