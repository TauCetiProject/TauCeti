/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.DrinfeldBasis.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.NaiveLevel
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Rank
import TauCeti.AlgebraicGeometry.IdealSheaf.Product
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
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsDrinfeldBasis.range_eq_ker`: over a field, the
  image of a Drinfeld basis of `E[N]` is `E[N](K)`.
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
  have (a : Multiplicative (ZMod N × ZMod N)) : IsClosedImmersion (φ a).left :=
    (φ a).left.isClosedImmersion_of_comp_eq_id (left_comp_structureMap _)
  let i := (E.torsionι N).left
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
    rw [← Scheme.Hom.finrank_comp_left_of_isIso i.toImage,
      subschemeι_ker_torsionι_left_structureMap, IsIso.hom_inv_id_assoc]
    funext s
    simp [E.finrank_torsion_hom hn, sq])).symm

section Field

variable {K : Type u} [Field K] {E : EllipticCurveGeom (Spec (.of K))}
  {φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E.structureMap)}

/-- **Over a field, the image of a Drinfeld basis of `E[N]` is `E[N](K)`.** Every `K`-point of `E`
killed by `N` lies on the closed subscheme `E[N]`, hence on the divisor `∑_a [φ a]`, whose support
is the union of the images of the sections `φ a`. No hypothesis on the characteristic of `K` is
needed. -/
theorem IsDrinfeldBasis.range_eq_ker (h : E.IsDrinfeldBasis N φ) :
    φ.range = (IsMonHom.monoidHom (E.mulBy N) _).ker := by
  ext x
  simp only [MonoidHom.mem_range, MonoidHom.mem_ker, IsMonHom.monoidHom_apply]
  obtain ⟨p⟩ : Nonempty (Spec (.of K)) := inferInstance
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨a, rfl⟩
    have ha : a ^ N = 1 := Multiplicative.toAdd.injective <| by
      ext <;> simp [nsmul_eq_mul]
    rw [comp_mulBy, zpow_natCast, ← map_pow, ha, map_one]
  · rw [← Set.mem_range, ← mem_support_pointsDivisor_iff φ x p, h.pointsDivisor_eq,
      Scheme.Hom.support_ker]
    refine subset_closure ⟨(E.torsionLift x hx).left p, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, E.torsionLift_torsionι x hx]

end Field

/-- **A Drinfeld basis of `E[N]` is injective on every fibre where `N` is invertible.** If `φ` is a
Drinfeld basis of `E[N]` and `N` is invertible in the residue field at `s`, then for every `a ≠ 1`
in `(ℤ/Nℤ)²` the section `φ a` misses the zero section at `s`. -/
theorem IsDrinfeldBasis.left_apply_ne_zero
    {φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)}
    (h : E.IsDrinfeldBasis N φ) {s : S} (hN : (N : S.residueField s) ≠ 0)
    {a : Multiplicative (ZMod N × ZMod N)} (ha : a ≠ 1) :
    (φ a).left s ≠ E.zero s := by
  -- base change `E` to an algebraic closure `L` of the residue field at `s`
  let L := AlgebraicClosure (S.residueField s)
  let t : Spec (.of L) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) L)) ≫ S.fromSpecResidueField s
  have hg := E.isPullback_baseChange t
  have h0 : (E.baseChange t).zero ≫ (E.baseChangeIso t).hom ≫ pullback.fst _ _ = t ≫ E.zero := by
    simp
  have hNL : (N : L) ≠ 0 := by
    rw [← map_natCast (algebraMap (S.residueField s) L)]
    exact (map_ne_zero_iff _ (algebraMap (S.residueField s) L).injective).mpr hN
  have h' : (E.baseChange t).IsFiberwiseInjective
      ((EllipticCurveGeom.pointsPullback hg h0).comp φ) :=
    ((E.baseChange t).isFiberwiseInjective_iff_range_eq_ker hNL _).mpr
      (h.pointsPullback hg h0).range_eq_ker
  obtain ⟨p⟩ : Nonempty (Spec (.of L)) := inferInstance
  have htp : t p = s := Scheme.fromSpecResidueField_apply s _
  intro hs
  exact isFiberwiseInjective_iff.mp h' a ha p
    ((pointsPullback_left_apply_eq_zero_iff hg h0 (φ a) p).mpr (htp.symm ▸ hs))

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
