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
import TauCeti.AlgebraicGeometry.RationalPoint.Basic
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Naive full level structures and Drinfeld bases

Let `E` be an elliptic curve over a scheme `S`. A naive full level-`N` structure on `E`, a
homomorphism `φ : (ℤ/Nℤ)² →* E(S)` injective on every fibre
(`EllipticCurveGeom.IsFiberwiseInjective`), is a Drinfeld basis of `E[N]`
(`EllipticCurveGeom.IsDrinfeldBasis`) over an arbitrary base scheme.
No invertibility hypothesis on `N` is needed for this direction. The section divisors are pairwise
disjoint, so their sum is their scheme-theoretic union. It is contained in `E[N]` and has the same
rank `N²`; finite flat rank comparison identifies the two closed subschemes. This argument also
works over nonreduced and empty bases.

Conversely, if `N` is invertible in every residue field of `S`, then every Drinfeld basis is
injective on every fibre, so the two notions agree there
(`EllipticCurveGeom.isDrinfeldBasis_iff_isFiberwiseInjective`). Over a separably closed field `K`,
every `K`-point of `E[N]` lies on the divisor `∑_a [φ a]`, whose support is the union of the
images of the points `φ a`; hence `φ` is onto `E[N](K)`, which has `N²` elements because `N` is
invertible in `K`, and so `φ` is injective. The general case follows by base change to algebraic
closures of the residue fields of `S`. The converse fails where `N` is not invertible: for a
supersingular elliptic curve over a field of characteristic `p`, the trivial homomorphism is a
Drinfeld basis of `E[p]`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsFiberwiseInjective.isDrinfeldBasis`: a naive
  full level-`N` structure is a Drinfeld basis of `E[N]`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsDrinfeldBasis.isFiberwiseInjective`: where `N`
  is invertible, a Drinfeld basis of `E[N]` is injective on every fibre.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isDrinfeldBasis_iff_isFiberwiseInjective`: where
  `N` is invertible, Drinfeld bases of `E[N]` are exactly the naive full level-`N` structures.

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
    have hx : φ a ≫ E.mulBy N = 1 := range_le_ker_mulBy φ ⟨a, rfl⟩
    simpa [i, ← Over.comp_left, E.torsionLift_torsionι (φ a) hx] using
      Scheme.Hom.le_ker_comp (E.torsionLift (φ a) hx).left i
  rw [isDrinfeldBasis_iff, ← ker_torsionι_left]
  exact (Scheme.IdealSheafData.eq_of_le_of_finrank_eq hle E.structureMap (by
    rw [← Scheme.Hom.finrank_comp_left_of_isIso i.toImage,
      subschemeι_ker_torsionι_left_structureMap, IsIso.hom_inv_id_assoc]
    funext s
    simp [E.finrank_torsion_hom hn, sq])).symm

section SepClosed

variable {K : Type u} [Field K] [IsSepClosed K] {E : EllipticCurveGeom (Spec (.of K))}

/-- Over a separably closed field in which `N` is invertible, a Drinfeld basis of `E[N]` is
injective. -/
private theorem IsDrinfeldBasis.isFiberwiseInjective_of_isSepClosed (hN : (N : K) ≠ 0)
    {φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E.structureMap)}
    (h : E.IsDrinfeldBasis N φ) : E.IsFiberwiseInjective φ := by
  -- `E[N](K)` has `N²` elements, and every `K`-point of `E[N]` is one of the points `φ a`, since it
  -- lies on the divisor `∑_a [φ a]`; so `φ` maps onto `E[N](K)`
  obtain ⟨p⟩ : Nonempty (Spec (.of K)) := inferInstance
  rw [isFiberwiseInjective_iff_range_eq_ker E hN]
  refine le_antisymm (range_le_ker_mulBy φ) fun x hx ↦ ?_
  rw [MonoidHom.mem_ker, IsMonHom.monoidHom_apply] at hx
  rw [isDrinfeldBasis_iff, ← ker_torsionι_left] at h
  -- `x` factors through `E[N]`, the closed subscheme cut out by the divisor `∑_a [φ a]`
  have hmem : x.left p ∈ ((E.pointsDivisor φ).support : Set E.carrier) := by
    rw [h, Scheme.Hom.support_ker, (E.torsionι N).left.isClosedEmbedding.isClosed_range.closure_eq,
      ← E.torsionLift_torsionι x hx, Over.comp_left]
    exact ⟨_, rfl⟩
  rw [coe_support_pointsDivisor] at hmem
  obtain ⟨a, q, hq⟩ := Set.mem_iUnion.mp hmem
  rw [Subsingleton.elim (α := Spec (.of K)) q p] at hq
  refine ⟨a, Over.OverMorphism.ext ?_⟩
  simpa using (comp_eq_comp_iff_of_section (f := E.structureMap) (s₁ := (φ a).left)
    (s₂ := x.left) (by simp) (by simp) (𝟙 _) p).mpr (by simpa using hq)

end SepClosed

/-- **A Drinfeld basis is a naive full level structure where `N` is invertible** (Katz–Mazur
§3.7). If `N` is invertible in every residue field of `S`, then a Drinfeld basis
`φ : (ℤ/Nℤ)² →* E(S)` of `E[N]` is injective on every fibre. -/
theorem IsDrinfeldBasis.isFiberwiseInjective
    {φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)}
    (h : E.IsDrinfeldBasis N φ) (hN : ∀ s : S, (N : S.residueField s) ≠ 0) :
    E.IsFiberwiseInjective φ := by
  rw [isFiberwiseInjective_iff]
  intro a ha s hs
  -- base change to an algebraic closure of the residue field at `s`
  let t := S.fromSpecAlgebraicClosure s
  obtain ⟨p⟩ : Nonempty (Spec (.of (AlgebraicClosure (S.residueField s)))) := inferInstance
  refine isFiberwiseInjective_iff.mp ((h.pointsPullback (E.isPullback_baseChange t)
    (by simp)).isFiberwiseInjective_of_isSepClosed
      (Scheme.natCast_algebraicClosure_residueField_ne_zero (hN s))) a ha p ?_
  rwa [MonoidHom.comp_apply, pointsPullback_left_apply_eq_zero_iff,
    Scheme.fromSpecAlgebraicClosure_apply]

/-- **Drinfeld bases are the naive full level structures where `N` is invertible** (Katz–Mazur
§3.7). If `N` is invertible in every residue field of `S`, then a homomorphism
`φ : (ℤ/Nℤ)² →* E(S)` is a Drinfeld basis of `E[N]` exactly when it is injective on every
fibre. -/
theorem isDrinfeldBasis_iff_isFiberwiseInjective (hN : ∀ s : S, (N : S.residueField s) ≠ 0)
    {φ : Multiplicative (ZMod N × ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)} :
    E.IsDrinfeldBasis N φ ↔ E.IsFiberwiseInjective φ :=
  ⟨fun h ↦ h.isFiberwiseInjective hN, IsFiberwiseInjective.isDrinfeldBasis⟩

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
