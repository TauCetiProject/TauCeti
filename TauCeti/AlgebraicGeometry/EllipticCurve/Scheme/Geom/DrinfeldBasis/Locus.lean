/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.DrinfeldBasis.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.WeilRestriction
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Finite
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Rank
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Rank

/-!
# The Drinfeld-basis locus

Let `E` be an elliptic curve over a scheme `S`, `N` a positive integer and
`φ : (ℤ/Nℤ)² →* E(S)` a homomorphism to the group of `S`-points of `E`. Whether the base change of
`φ` to a scheme `S'` over `S` is a Drinfeld basis of `E'[N]`, that is a `[Γ(N)]`-structure on the
base change `E'` of `E`, is a closed condition on `S'`: there is an ideal sheaf
`E.drinfeldBasisLocus N φ` on `S` such that the base change of `φ` along `f : S' ⟶ S` is a
Drinfeld basis exactly when `f` factors through its closed subscheme
(`EllipticCurveGeom.isDrinfeldBasis_pointsPullback_iff`). Its formation commutes with arbitrary
base change (`EllipticCurveGeom.drinfeldBasisLocus_pointsPullback`). No hypothesis is placed on
`S`, which may be nonreduced, and `N` need not be invertible on it.

A Drinfeld basis is a homomorphism `φ` with `∑_a [φ a] = E[N]` as closed subschemes of `E`. Both
sides are finite locally free over `S` of rank `N²`: the divisor `∑_a [φ a]` is a sum of `N²`
divisors of sections, each of degree one (`EllipticCurveGeom.finrank_pointsDivisor`), and `E[N]`
has rank `N²` by Katz–Mazur 2.3.1 (`EllipticCurveGeom.finrank_torsion_hom`). A closed immersion
between finite locally free schemes of the same rank is an isomorphism, so it is enough that the
divisor `∑_a [φ a]` lies in `E[N]` (`EllipticCurveGeom.isDrinfeldBasis_iff_ker_torsionι_left_le`).
That says the closed immersion of the finite locally free scheme `∑_a [φ a]` into `E` factors
through `E[N]`, a condition cut out on the base by a Weil restriction of a closed subscheme
(`AlgebraicGeometry.Scheme.IdealSheafData.weilRestriction_comap_le_ker_iff`).

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.drinfeldBasisLocus E N φ`: the ideal sheaf on `S`
  of the locus over which `φ` is a Drinfeld basis of `E[N]`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isDrinfeldBasis_iff_ker_torsionι_left_le`: a
  homomorphism is a Drinfeld basis as soon as its divisor lies in `E[N]`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isDrinfeldBasis_pointsPullback_iff`: the universal
  property of the Drinfeld-basis locus; being a Drinfeld basis is a closed condition on the base.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isDrinfeldBasis_iff_drinfeldBasisLocus_eq_bot`:
  `φ` is a Drinfeld basis exactly when its locus is all of `S`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.drinfeldBasisLocus_pointsPullback`: the
  Drinfeld-basis locus commutes with base change.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, Chapter 1 (closed conditions on relative effective
  Cartier divisors and finite locally free families), 2.3.1 (the rank of `E[N]`), §3.1
  (`[Γ(N)]`-structures) and 3.6.0 (relative representability of `[Γ(N)]`, whose proof cuts the
  `[Γ(N)]`-structures out by this closed condition).
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj
open Scheme.IdealSheafData

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} {E : EllipticCurveGeom S}

/-- Through the isomorphism `E[n] ≅ V(ker (E[n] ⟶ E))`, the closed subscheme cut out by the ideal
sheaf of `E[n]` is `E[n]` over `S`. -/
private theorem ker_torsionι_left_subschemeι_comp (n : ℤ) :
    (E.torsionι n).left.ker.subschemeι ≫ E.structureMap =
      inv (E.torsionι n).left.toImage ≫ (E.torsion n).X.hom := by
  rw [IsIso.eq_inv_comp, ← torsionι_left_structureMap]
  exact Scheme.Hom.toImage_imageι_assoc _ _

variable {N : ℕ} [NeZero N]

/-- **A Drinfeld basis is a homomorphism whose divisor lies in `E[N]`.** The divisor `∑_a [φ a]`
and `E[N]` are both finite locally free of rank `N²` over `S`, so the containment of the closed
subscheme `∑_a [φ a]` in `E[N]` is already an equality. The order on ideal sheaves reverses
containment of their closed subschemes. -/
theorem isDrinfeldBasis_iff_ker_torsionι_left_le
    {φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)} :
    E.IsDrinfeldBasis N φ ↔ (E.torsionι N).left.ker ≤ E.pointsDivisor φ := by
  rw [isDrinfeldBasis_iff, ← ker_torsionι_left]
  refine ⟨fun h ↦ h.ge, fun h ↦ ?_⟩
  have hN : (N : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne N)
  have := E.isFinite_torsion_hom hN
  have := E.flat_torsion_hom hN
  have : IsFinite ((E.torsionι N).left.ker.subschemeι ≫ E.structureMap) := by
    rw [ker_torsionι_left_subschemeι_comp]
    infer_instance
  have : Flat ((E.torsionι N).left.ker.subschemeι ≫ E.structureMap) := by
    rw [ker_torsionι_left_subschemeι_comp]
    infer_instance
  refine (eq_of_le_of_finrank_eq h E.structureMap ?_).symm
  funext s
  rw [ker_torsionι_left_subschemeι_comp, Scheme.Hom.finrank_comp_left_of_isIso,
    E.finrank_torsion_hom hN, finrank_pointsDivisor]
  simp [sq]

variable (E N) in
/-- The ideal sheaf on `S` of the **Drinfeld-basis locus** of a homomorphism
`φ : (ℤ/Nℤ)² →* E(S)`: a morphism `S' ⟶ S` factors through its closed subscheme exactly when the
base change of `φ` to `S'` is a Drinfeld basis of `E'[N]`, for the base change `E'` of `E`
(`EllipticCurveGeom.isDrinfeldBasis_pointsPullback_iff`). It is the Weil restriction, along the
finite locally free divisor `∑_a [φ a]`, of the inverse image of `E[N]` in that divisor: the
locus over which `∑_a [φ a]` lies in `E[N]`. -/
noncomputable def drinfeldBasisLocus
    (φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    S.IdealSheafData :=
  ((E.torsionι N).left.ker.comap (E.pointsDivisor φ).subschemeι).weilRestriction
    ((E.pointsDivisor φ).subschemeι ≫ E.structureMap)

/-- The Drinfeld-basis locus of `φ` is the Weil restriction, along the finite locally free divisor
`∑_a [φ a]`, of the inverse image of `E[N]` in that divisor. -/
theorem drinfeldBasisLocus_def
    (φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    E.drinfeldBasisLocus N φ =
      ((E.torsionι N).left.ker.comap (E.pointsDivisor φ).subschemeι).weilRestriction
        ((E.pointsDivisor φ).subschemeι ≫ E.structureMap) :=
  (rfl)

variable {S' : Scheme.{u}} {E' : EllipticCurveGeom S'} {g : E'.carrier ⟶ E.carrier}
  {f : S' ⟶ S}

/-- **The universal property of the Drinfeld-basis locus**: being a Drinfeld basis is a closed
condition on the base (Katz–Mazur §3.1; compare the proof of 3.6.0). Let `g : E' ⟶ E` be a
morphism of elliptic curves lying over `f : S' ⟶ S`, forming a pullback square with the structure
morphisms and carrying the zero section of `E'` to that of `E`. The base change of
`φ : (ℤ/Nℤ)² →* E(S)` along `f` is a Drinfeld basis of `E'[N]` exactly when `f` factors through
the closed subscheme of `E.drinfeldBasisLocus N φ`. -/
theorem isDrinfeldBasis_pointsPullback_iff (hg : IsPullback g E'.structureMap E.structureMap f)
    (h0 : E'.zero ≫ g = f ≫ E.zero)
    (φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    E'.IsDrinfeldBasis N ((pointsPullback hg h0).comp φ) ↔
      E.drinfeldBasisLocus N φ ≤ f.ker := by
  -- `∑_a [φ' a]` is the base change of `∑_a [φ a]`, and `E'[N]` that of `E[N]`.
  have hD := (E.pointsDivisor φ).isPullback_subschemeMap_comap E.structureMap hg
  rw [isDrinfeldBasis_iff_ker_torsionι_left_le, MonoidHom.coe_comp, pointsDivisor_pointsPullback,
    ker_torsionι_left_of_isPullback _ hg h0, drinfeldBasisLocus_def,
    weilRestriction_comap_le_ker_iff _ _ hD.flip (subschemeMap_subschemeι _ _ _ _).symm,
    ker_subschemeι]

/-- **A homomorphism is a Drinfeld basis exactly when its Drinfeld-basis locus is all of the
base.** -/
theorem isDrinfeldBasis_iff_drinfeldBasisLocus_eq_bot
    (φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    E.IsDrinfeldBasis N φ ↔ E.drinfeldBasisLocus N φ = ⊥ := by
  have hid : (pointsPullback (.id_horiz E.structureMap) (by simp)).comp φ = φ :=
    MonoidHom.ext fun a ↦ pointsPullback_id (φ a)
  rw [← le_bot_iff, ← Scheme.Hom.ker_eq_bot_of_isIso (𝟙 S),
    ← isDrinfeldBasis_pointsPullback_iff (.id_horiz E.structureMap) (by simp), hid]

/-- **The Drinfeld-basis locus commutes with base change.** For a pullback square of elliptic
curves `g : E' ⟶ E` over `f : S' ⟶ S`, the Drinfeld-basis locus of the base change of
`φ : (ℤ/Nℤ)² →* E(S)` is the inverse image along `f` of the Drinfeld-basis locus of `φ`. -/
theorem drinfeldBasisLocus_pointsPullback (hg : IsPullback g E'.structureMap E.structureMap f)
    (h0 : E'.zero ≫ g = f ≫ E.zero)
    (φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    E'.drinfeldBasisLocus N ((pointsPullback hg h0).comp φ) =
      (E.drinfeldBasisLocus N φ).comap f := by
  -- Both sides have the same morphisms `t : T ⟶ S'` factoring through their closed subschemes:
  -- those along which the base change of `φ` to `T` is a Drinfeld basis.
  have key {T : Scheme.{u}} (t : T ⟶ S') :
      E'.drinfeldBasisLocus N ((pointsPullback hg h0).comp φ) ≤ t.ker ↔
        (E.drinfeldBasisLocus N φ).comap f ≤ t.ker := by
    have ht := E'.isPullback_baseChange t
    have ht0 : (E'.baseChange t).zero ≫ (E'.baseChangeIso t).hom ≫
        pullback.fst E'.structureMap t = t ≫ E'.zero := by
      simp [pullbackSection_fst]
    have hcomp : (pointsPullback ht ht0).comp ((pointsPullback hg h0).comp φ) =
        (pointsPullback (ht.paste_horiz hg) (by simp [reassoc_of% ht0, h0])).comp φ :=
      MonoidHom.ext fun a ↦ (pointsPullback_comp hg h0 ht ht0 (φ a)).symm
    rw [← isDrinfeldBasis_pointsPullback_iff ht ht0, hcomp, ← le_map_iff_comap_le, map_ker,
      isDrinfeldBasis_pointsPullback_iff]
  exact le_antisymm (((key _).2 (ker_subschemeι _).ge).trans (ker_subschemeι _).le)
    (((key _).1 (ker_subschemeι _).ge).trans (ker_subschemeι _).le)

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
