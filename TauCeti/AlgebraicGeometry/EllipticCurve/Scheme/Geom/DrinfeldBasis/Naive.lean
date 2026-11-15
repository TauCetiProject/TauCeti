/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.DrinfeldBasis.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.NaiveLevel
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.GeometricFiber
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Rank
import TauCeti.AlgebraicGeometry.IdealSheaf.Rank
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Comparison of Drinfeld bases and naive full level structures

Let `E` be an elliptic curve over a scheme `S` and `N` a positive integer. This file compares
Drinfeld bases of `E[N]` (`EllipticCurveGeom.IsDrinfeldBasis`) with naive `[Γ(N)]`-structures
(`EllipticCurveGeom.IsFiberwiseInjective`), following Katz–Mazur §3.7:

1. **Over any base scheme**, every naive `[Γ(N)]`-structure is a Drinfeld basis
   (`EllipticCurveGeom.IsFiberwiseInjective.isDrinfeldBasis`). The section divisors `[φ a]` are
   pairwise disjoint, so their sum is their scheme-theoretic union; it is contained in `E[N]` and
   has the same rank `N²`, so finite flat rank comparison identifies the two closed subschemes. No
   invertibility hypothesis on `N` is needed for this direction, and the argument works over
   nonreduced and empty bases.
2. **Where `N` is invertible on the base**, every Drinfeld basis is a naive `[Γ(N)]`-structure
   (`EllipticCurveGeom.IsDrinfeldBasis.isFiberwiseInjective`), so the two notions coincide
   (`EllipticCurveGeom.isDrinfeldBasis_iff_isFiberwiseInjective`). Over any field `K`, the divisor
   equality `∑_a [φ a] = E[N]` forces every `K`-point of `E[N]` to lie on one of the sections `φ a`,
   so the image of `φ` is `E[N](K)` (`EllipticCurveGeom.IsDrinfeldBasis.range_eq_ker`). Over a
   separably closed field in which `N` is invertible, `E[N](K)` has `N²` points, so `φ` is
   injective (`EllipticCurveGeom.isFiberwiseInjective_iff_range_eq_ker`). The general case reduces
   to this one by base change to the algebraic closures of the residue fields of `S`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsFiberwiseInjective.isDrinfeldBasis`: every naive
  `[Γ(N)]`-structure is a Drinfeld basis, over an arbitrary base.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsDrinfeldBasis.left_apply_ne_zero`: on a fibre
  where `N` is invertible, no `φ a` with `a ≠ 1` meets the zero section.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsDrinfeldBasis.isFiberwiseInjective`: where `N` is
  invertible on the base, every Drinfeld basis is a naive `[Γ(N)]`-structure.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isDrinfeldBasis_iff_isFiberwiseInjective`: where
  `N` is invertible on the base, Drinfeld bases and naive `[Γ(N)]`-structures coincide.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isDrinfeldBasis_iff_injective`: over a field in
  which `N` is invertible, a homomorphism `(ℤ/Nℤ)² →* E(K)` is a Drinfeld basis if and only if it
  is injective.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §§1.4, 1.10, 3.1, 3.7.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

universe u

variable {S : Scheme.{u}} {E : EllipticCurveGeom S} {N : ℕ} [NeZero N]

/-- Every naive full level structure is a Drinfeld basis, without requiring `N` to be invertible
on the base. -/
theorem IsFiberwiseInjective.isDrinfeldBasis
    {φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)}
    (hφ : E.IsFiberwiseInjective φ) : E.IsDrinfeldBasis N φ := by
  have hn : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  let i := (E.torsionι N).left
  have hrel := E.isRelativeEffectiveCartier_pointsDivisor φ
  have := hrel.flat
  have hle : i.ker ≤ E.pointsDivisor φ := by
    apply hφ.ker_torsionι_left_le_pointsDivisor
    intro a
    simpa [IsMonHom.monoidHom_apply, comp_mulBy] using range_le_ker_mulBy φ ⟨a, rfl⟩
  rw [isDrinfeldBasis_iff, ← ker_torsionι_left]
  exact (Scheme.IdealSheafData.eq_of_le_of_finrank_eq hle E.structureMap (by
    rw [← Scheme.Hom.finrank_comp_left_of_isIso i.toImage,
      subschemeι_ker_torsionι_left_structureMap, IsIso.hom_inv_id_assoc]
    funext s
    simp [E.finrank_torsion_hom hn, sq])).symm

/-- **A Drinfeld basis of `E[N]` is injective on every fibre where `N` is invertible.** If `φ` is a
Drinfeld basis of `E[N]` and `N` is invertible in the residue field at `s`, then for every `a ≠ 1`
in `(ℤ/Nℤ)²` the section `φ a` misses the zero section at `s`. -/
theorem IsDrinfeldBasis.left_apply_ne_zero
    {φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)}
    (h : E.IsDrinfeldBasis N φ) {s : S} (hN : (N : S.residueField s) ≠ 0)
    {a : Multiplicative (ZMod N × ZMod N)} (ha : a ≠ 1) :
    (φ a).left s ≠ E.zero s := by
  refine left_apply_ne_zero_of_forall_isAlgClosed (φ a) hN fun K _ _ t hNK ↦ ?_
  have h' : (E.baseChange t).IsFiberwiseInjective
      ((EllipticCurveGeom.pointsPullback (E.isPullback_baseChange t) (by simp)).comp φ) :=
    ((E.baseChange t).isFiberwiseInjective_iff_range_eq_ker hNK _).mpr
      (h.pointsPullback (E.isPullback_baseChange t) (by simp)).range_eq_ker
  exact fun he ↦ ha ((injective_iff_map_eq_one _).mp h'.injective a he)

/-- **Every Drinfeld basis is a naive `[Γ(N)]`-structure where `N` is invertible** (Katz–Mazur,
§3.7): if `N` is invertible in every residue field of `S`, a Drinfeld basis `φ : (ℤ/Nℤ)² →* E(S)`
is injective on every fibre of `E` over `S`. -/
theorem IsDrinfeldBasis.isFiberwiseInjective
    {φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)}
    (h : E.IsDrinfeldBasis N φ) (hN : ∀ s : S, (N : S.residueField s) ≠ 0) :
    E.IsFiberwiseInjective φ :=
  isFiberwiseInjective_iff.mpr fun _ ha s ↦ h.left_apply_ne_zero (hN s) ha

/-- **Drinfeld bases and naive `[Γ(N)]`-structures coincide where `N` is invertible** (Katz–Mazur,
§3.7). If `N` is invertible in every residue field of `S`, a homomorphism `φ : (ℤ/Nℤ)² →* E(S)` is
a Drinfeld basis of `E[N]` if and only if it is injective on every fibre of `E` over `S`. -/
theorem isDrinfeldBasis_iff_isFiberwiseInjective
    {φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)}
    (hN : ∀ s : S, (N : S.residueField s) ≠ 0) :
    E.IsDrinfeldBasis N φ ↔ E.IsFiberwiseInjective φ :=
  ⟨fun h ↦ h.isFiberwiseInjective hN, fun h ↦ h.isDrinfeldBasis⟩

section Field

variable {K : Type u} [Field K] {E : EllipticCurveGeom (Spec (.of K))}
  {φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E.structureMap)}

/-- **Over a field in which `N` is invertible, a Drinfeld basis is injective.** -/
theorem IsDrinfeldBasis.injective (h : E.IsDrinfeldBasis N φ) (hN : (N : K) ≠ 0) :
    Function.Injective φ :=
  (E.isFiberwiseInjective_iff_injective φ).mp
    (h.isFiberwiseInjective (Spec.natCast_residueField_ne_zero hN))

/-- **Over a field in which `N` is invertible, the Drinfeld bases of `E[N]` are the injective
homomorphisms `(ℤ/Nℤ)² →* E(K)`.** -/
theorem isDrinfeldBasis_iff_injective (hN : (N : K) ≠ 0) :
    E.IsDrinfeldBasis N φ ↔ Function.Injective φ :=
  (isDrinfeldBasis_iff_isFiberwiseInjective (Spec.natCast_residueField_ne_zero hN)).trans
    (E.isFiberwiseInjective_iff_injective φ)

end Field

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
