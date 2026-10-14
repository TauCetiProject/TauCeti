/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.DrinfeldBasis.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.WeilRestriction
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Finite
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Rank
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Being a Drinfeld basis is a closed condition

Let `E` be an elliptic curve over a scheme `S`, `N` a positive integer and
`φ : (ℤ/Nℤ)² →* E(S)` a homomorphism to the group of `S`-points of `E`. Whether the base change of
`φ` along a scheme `S'` over `S` is a Drinfeld basis of `E'[N]` is a closed condition on `S'`:
there is an ideal sheaf `E.drinfeldBasisLocus N φ` on `S` such that the base change of `φ` is a
Drinfeld basis exactly when `S' ⟶ S` factors through its closed subscheme
(`EllipticCurveGeom.isDrinfeldBasis_pointsPullback_iff`).

A Drinfeld basis is a homomorphism whose divisor `D = ∑_{a ∈ (ℤ/Nℤ)²} [φ a]` is the closed
subscheme `E[N]`. Both `D` and `E[N]` are finite locally free over `S` and commute with base
change, so equality of their base changes is the conjunction of two closed conditions: the
finite locally free family `D ⟶ E` lies in `E[N]`, and the finite locally free family
`E[N] ⟶ E` lies in `D`. Each is cut out by a Weil restriction of a closed subscheme
(`AlgebraicGeometry.Scheme.IdealSheafData.weilRestriction_comap_le_ker_iff`), and the
Drinfeld-basis locus is the intersection of the two closed subschemes.

The locus commutes with base change (`EllipticCurveGeom.drinfeldBasisLocus_pointsPullback`), is
invariant under automorphisms of `(ℤ/Nℤ)²`, in particular under `GL₂(ℤ/Nℤ)`
(`EllipticCurveGeom.drinfeldBasisLocus_comp_mulEquiv`), and over it the base change of `φ` is a
Drinfeld basis (`EllipticCurveGeom.isDrinfeldBasis_pointsPullback_baseChange_subschemeι`). No
hypothesis is placed on `S`, which may be nonreduced, and `N` need not be invertible on it: the
condition is scheme-theoretic, not a condition on geometric fibres.

Applied to a universal homomorphism `(ℤ/Nℤ)² →* E_H(H)`, of which every homomorphism
`(ℤ/Nℤ)² →* E_T(T)` is the base change along a unique morphism `T ⟶ H` (for instance the one
given by the pair of universal points over `H = E[N] ×_S E[N]`), the universal property says that
the `[Γ(N)]`-structures on base changes of `E` are the points of the closed subscheme of `H` cut
out by the Drinfeld-basis locus.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.drinfeldBasisLocus E N φ`: the ideal sheaf on `S`
  of the locus over which `φ` is a Drinfeld basis of `E[N]`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isDrinfeldBasis_pointsPullback_iff`: the universal
  property of the Drinfeld-basis locus.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isDrinfeldBasis_iff_drinfeldBasisLocus_eq_bot`:
  `φ` is a Drinfeld basis exactly when its locus is all of `S`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.drinfeldBasisLocus_pointsPullback`: the locus
  commutes with base change.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 1.3.7 and 1.6.2 (conditions on finite locally free closed
  subschemes of a curve are closed), §1.10 (the closed subscheme of generators) and §3.1
  (`[Γ(N)]`-structures).
* S. Bosch, W. Lütkebohmert and M. Raynaud, *Néron Models*, §7.6, for Weil restriction.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj
open Scheme.IdealSheafData

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S) (N : ℕ) [NeZero N]

/-- The ideal sheaf on `S` of the **Drinfeld-basis locus** of a homomorphism
`φ : (ℤ/Nℤ)² →* E(S)` (Katz–Mazur, 1.6.2 and §3.1): a morphism `S' ⟶ S` factors through its
closed subscheme exactly when the base change of `φ` is a Drinfeld basis of `E'[N]`
(`EllipticCurveGeom.isDrinfeldBasis_pointsPullback_iff`). It is the supremum of the ideal sheaves
of two loci, cut out by Weil restrictions: where the divisor `∑_a [φ a]` lies in `E[N]`, and where
`E[N]` lies in the divisor `∑_a [φ a]`. -/
noncomputable def drinfeldBasisLocus
    (φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    S.IdealSheafData :=
  have hN : (N : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne N)
  have := E.isFinite_torsion_hom hN
  have := E.flat_torsion_hom hN
  ((E.torsionι N).left.ker.comap (E.pointsDivisor φ).subschemeι).weilRestriction
      ((E.pointsDivisor φ).subschemeι ≫ E.structureMap) ⊔
    ((E.pointsDivisor φ).comap (E.torsionι N).left).weilRestriction (E.torsion N).X.hom

variable {E N} {S' : Scheme.{u}} {E' : EllipticCurveGeom S'} {g : E'.carrier ⟶ E.carrier}
  {f : S' ⟶ S}

/-- **The universal property of the Drinfeld-basis locus** (Katz–Mazur, 1.6.2 and §3.1). Let
`g : E' ⟶ E` be a morphism of elliptic curves lying over `f : S' ⟶ S`, forming a pullback square
with the structure morphisms and carrying the zero section of `E'` to that of `E`. Then the base
change `(ℤ/Nℤ)² →* E'(S')` of `φ` is a Drinfeld basis of `E'[N]` exactly when `f` factors through
the closed subscheme of `E.drinfeldBasisLocus N φ`. -/
theorem isDrinfeldBasis_pointsPullback_iff (hg : IsPullback g E'.structureMap E.structureMap f)
    (h0 : E'.zero ≫ g = f ≫ E.zero)
    (φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    E'.IsDrinfeldBasis N ((pointsPullback hg h0).comp φ) ↔ E.drinfeldBasisLocus N φ ≤ f.ker := by
  have hN : (N : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne N)
  have := E.isFinite_torsion_hom hN
  have := E.flat_torsion_hom hN
  set D := E.pointsDivisor φ
  -- `V(D)` and `E[N]` commute with base change
  have hD := D.isPullback_subschemeMap_comap E.structureMap hg
  have hT := isPullback_torsionMap (N : ℤ) hg h0
  rw [isDrinfeldBasis_iff, ← ker_torsionι_left, MonoidHom.coe_comp, pointsDivisor_pointsPullback,
    ker_torsionι_left_of_isPullback _ hg h0, drinfeldBasisLocus, sup_le_iff,
    le_antisymm_iff, and_comm]
  refine and_congr ?_ ?_
  · -- `V(D)` lies in `E[N]`
    rw [weilRestriction_comap_le_ker_iff _ _ hD.flip (subschemeMap_subschemeι _ _ _ _).symm,
      ker_subschemeι]
  · -- `E[N]` lies in `V(D)`
    rw [weilRestriction_comap_le_ker_iff _ _ hT.flip (torsionMap_torsionι _ hg h0).symm,
      ker_torsionι_left_of_isPullback _ hg h0]

/-- A homomorphism `φ : (ℤ/Nℤ)² →* E(S)` is a Drinfeld basis of `E[N]` exactly when its
Drinfeld-basis locus is all of `S`. -/
theorem isDrinfeldBasis_iff_drinfeldBasisLocus_eq_bot
    (φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    E.IsDrinfeldBasis N φ ↔ E.drinfeldBasisLocus N φ = ⊥ := by
  have hφ : (pointsPullback (.id_horiz E.structureMap) (by simp)).comp φ = φ :=
    MonoidHom.ext fun a ↦ pointsPullback_id (φ a)
  rw [← le_bot_iff, ← Scheme.Hom.ker_eq_bot_of_isIso (𝟙 S),
    ← isDrinfeldBasis_pointsPullback_iff (.id_horiz E.structureMap) (by simp), hφ]

/-- **Over the Drinfeld-basis locus, `φ` is a Drinfeld basis**: the base change of `φ` to the
closed subscheme of `E.drinfeldBasisLocus N φ` is a Drinfeld basis. -/
theorem isDrinfeldBasis_pointsPullback_baseChange_subschemeι
    (φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    (E.baseChange (E.drinfeldBasisLocus N φ).subschemeι).IsDrinfeldBasis N
      ((pointsPullback (E.isPullback_baseChange _) (by simp)).comp φ) :=
  (isDrinfeldBasis_pointsPullback_iff _ _ φ).2 (ker_subschemeι _).ge

/-- **The Drinfeld-basis locus is invariant under automorphisms of `(ℤ/Nℤ)²`**, in particular under
the right action of `GL₂(ℤ/Nℤ)`: reindexing the points `φ a` does not change their divisor. -/
@[simp]
theorem drinfeldBasisLocus_comp_mulEquiv
    (φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap))
    (σ : Multiplicative (ZMod N × ZMod N) ≃* Multiplicative (ZMod N × ZMod N)) :
    E.drinfeldBasisLocus N (φ.comp ↑σ) = E.drinfeldBasisLocus N φ :=
  -- both sides have the same morphisms factoring through their closed subschemes
  ext_of_le_ker_iff fun t ↦ by
    have ht := E.isPullback_baseChange t
    have h0t : (E.baseChange t).zero ≫ (E.baseChangeIso t).hom ≫ pullback.fst _ _ =
        t ≫ E.zero := by simp
    rw [← isDrinfeldBasis_pointsPullback_iff ht h0t, ← isDrinfeldBasis_pointsPullback_iff ht h0t,
      ← MonoidHom.comp_assoc, isDrinfeldBasis_comp_mulEquiv_iff]

/-- **The Drinfeld-basis locus commutes with base change.** For a morphism `g : E' ⟶ E` of
elliptic curves forming a pullback square over `f : S' ⟶ S` and carrying the zero section of `E'`
to that of `E`, the Drinfeld-basis locus of the base change of `φ` is the inverse image along `f`
of the Drinfeld-basis locus of `φ`. -/
theorem drinfeldBasisLocus_pointsPullback (hg : IsPullback g E'.structureMap E.structureMap f)
    (h0 : E'.zero ≫ g = f ≫ E.zero)
    (φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    E'.drinfeldBasisLocus N ((pointsPullback hg h0).comp φ) =
      (E.drinfeldBasisLocus N φ).comap f :=
  -- both sides have the same morphisms factoring through their closed subschemes
  ext_of_le_ker_iff fun t ↦ by
    have ht := E'.isPullback_baseChange t
    have h0t : (E'.baseChange t).zero ≫ (E'.baseChangeIso t).hom ≫ pullback.fst _ _ =
        t ≫ E'.zero := by simp
    have h0' : (E'.baseChange t).zero ≫ ((E'.baseChangeIso t).hom ≫ pullback.fst _ _) ≫ g =
        (t ≫ f) ≫ E.zero := by
      rw [← Category.assoc, h0t, Category.assoc, h0, Category.assoc]
    have hφ : (pointsPullback (ht.paste_horiz hg) h0').comp φ =
        (pointsPullback ht h0t).comp ((pointsPullback hg h0).comp φ) :=
      MonoidHom.ext fun a ↦ pointsPullback_comp hg h0 ht h0t (φ a)
    rw [← isDrinfeldBasis_pointsPullback_iff ht h0t, ← le_map_iff_comap_le, map_ker,
      ← isDrinfeldBasis_pointsPullback_iff (ht.paste_horiz hg) h0', hφ]

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
