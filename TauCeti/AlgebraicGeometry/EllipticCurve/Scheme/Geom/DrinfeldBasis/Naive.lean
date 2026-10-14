/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.DrinfeldBasis.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.NaiveLevel
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Rank
import TauCeti.AlgebraicGeometry.IdealSheaf.Product
import TauCeti.AlgebraicGeometry.IdealSheaf.Rank

/-!
# Naive full level structures are Drinfeld bases

A fibrewise injective homomorphism `(ℤ/Nℤ)² → E(S)` is a Drinfeld basis over an arbitrary
base scheme. No invertibility hypothesis on `N` is needed for this direction.

The section divisors are pairwise disjoint, so their sum is their scheme-theoretic union.
It is contained in `E[N]` and has the same rank `N²`; finite flat rank comparison identifies
the two closed subschemes. This argument also works over nonreduced and empty bases.

The converse on the locus where `N` is invertible is not established here.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §§1.4, 3.7.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry MonObj

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

universe u

variable {S : Scheme.{u}} {E : EllipticCurveGeom S} {N : ℕ} [NeZero N]

/-- Every naive full level structure is a Drinfeld basis, without requiring `N` to be invertible
on the base. -/
theorem IsFiberwiseInjective.isDrinfeldBasis
    {φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)}
    (hφ : E.IsFiberwiseInjective φ) : E.IsDrinfeldBasis N φ := by
  have hn : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have (a : Multiplicative (ZMod N × ZMod N)) : IsClosedImmersion (φ a).left :=
    (φ a).left.isClosedImmersion_of_comp_eq_id (left_comp_structureMap _)
  let i := (E.torsionι N).left
  have hi : i.toImage ≫ i.ker.subschemeι ≫ E.structureMap = (E.torsion N).X.hom := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    exact E.torsionι_left_structureMap N
  have hg : i.ker.subschemeι ≫ E.structureMap = inv i.toImage ≫ (E.torsion N).X.hom := by
    rw [← hi]
    simp
  have : Flat (i.ker.subschemeι ≫ E.structureMap) := by
    rw [hg]
    have := E.flat_torsion_hom hn
    infer_instance
  have : IsFinite (i.ker.subschemeι ≫ E.structureMap) := by
    rw [hg]
    have := E.isFinite_torsion_hom hn
    infer_instance
  have hrel := E.isRelativeEffectiveCartier_pointsDivisor φ
  have := hrel.flat
  have hprod : E.pointsDivisor φ = ⨅ a, (φ a).left.ker := by
    rw [pointsDivisor_def]
    apply Scheme.IdealSheafData.prod_eq_iInf_of_pairwise_disjoint_support
    intro a b hab
    apply disjoint_iff.mpr
    apply SetLike.coe_injective
    simpa only [Set.inf_eq_inter, Set.bot_eq_empty,
      TopologicalSpace.Closeds.coe_inf, TopologicalSpace.Closeds.coe_bot,
      Scheme.Hom.support_ker,
      (IsClosedImmersion.isClosedEmbedding (φ a).left).isClosed_range.closure_eq,
      (IsClosedImmersion.isClosedEmbedding (φ b).left).isClosed_range.closure_eq] using
      (hφ.disjoint_range hab).eq_bot
  have hle : i.ker ≤ E.pointsDivisor φ := by
    rw [hprod]
    refine le_iInf fun a ↦ ?_
    have ha : a ^ N = 1 := Multiplicative.toAdd.injective <| by
      ext <;> simp [nsmul_eq_mul]
    have hx : φ a ≫ E.mulBy N = 1 := by
      rw [comp_mulBy, zpow_natCast, ← map_pow, ha, map_one]
    simpa [i, ← Over.comp_left, E.torsionLift_torsionι (φ a) hx] using
      Scheme.Hom.le_ker_comp (E.torsionLift (φ a) hx).left i
  rw [isDrinfeldBasis_iff, ← ker_torsionι_left]
  exact (Scheme.IdealSheafData.eq_of_le_of_finrank_eq hle E.structureMap (by
    rw [← Scheme.Hom.finrank_comp_left_of_isIso i.toImage, hi]
    funext s
    simp [E.finrank_torsion_hom hn, sq])).symm

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
