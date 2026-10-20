/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Points
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Section
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.Sum
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Finite
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.FinitePresentation
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
import TauCeti.AlgebraicGeometry.IdealSheaf.Product
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.AlgebraicGeometry.RationalPoint.Basic

/-!
# The divisor of a finite family of points on an elliptic curve

Let `E` be an elliptic curve over a scheme `S` and `x : A → E(S)` a finite family of `S`-points
of `E`. Each `x a` is a section of the smooth separated curve `E ⟶ S`, so it cuts out a relative
effective Cartier divisor `[x a]` on `E`. The divisor `∑_{a ∈ A} [x a]`
(`EllipticCurveGeom.pointsDivisor`) is the product of their ideal sheaves; points occurring several
times in the family are counted with multiplicity.

The divisor `∑_a [x a]` is a relative effective Cartier divisor on `E` over `S`, hence finite
locally free over `S` since `E` is proper. It contains each of the points `x a`, its support is the
union of their images, it does not depend on how the points are indexed, and it commutes with base
change.
Particular cases are the divisor `[P] + [2P] + ⋯ + [NP]` of points of exact order `N`
(`EllipticCurveGeom.multiplesDivisor`) and the divisor `∑_{a ∈ (ℤ/Nℤ)²} [φ a]` of Drinfeld bases
(`EllipticCurveGeom.IsDrinfeldBasis`).

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.pointsDivisor E x`: the divisor `∑_a [x a]` of a
  finite family of `S`-points of `E`, as an ideal sheaf on `E`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isRelativeEffectiveCartier_pointsDivisor`:
  `∑_a [x a]` is a relative effective Cartier divisor on `E` over `S`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFinite_pointsDivisor`,
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.flat_pointsDivisor` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.locallyOfFinitePresentation_pointsDivisor`:
  `∑_a [x a]` is finite locally free over `S`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.coe_support_pointsDivisor`: the support of
  `∑_a [x a]` is the union of the images of the sections `x a`; over a field, a point lies on
  `∑_a [x a]` exactly when it is one of the `x a`
  (`TauCeti.AlgebraicGeometry.EllipticCurveGeom.mem_support_pointsDivisor_iff`).
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.pointsDivisor_comp_equiv`: `∑_a [x a]` does not
  depend on the indexing.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.pointsDivisor_pointsPullback`: `∑_a [x a]`
  commutes with base change.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.finrank_pointsDivisor`: its rank is the number
  of sections, counted with multiplicity.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, Chapter 1 (sums of sections of a smooth curve).
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S) {A : Type*} [Fintype A]

/-- The divisor `∑_{a ∈ A} [x a]` of a finite family `x` of `S`-points of an elliptic curve `E`
over `S`, as an ideal sheaf on `E`: the product of the ideal sheaves of the sections `x a`. Points
occurring several times in the family are counted with multiplicity. -/
noncomputable def pointsDivisor (x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    E.carrier.IdealSheafData :=
  ∏ a, (x a).left.ker

variable {E}

/-- The divisor `∑_a [x a]` is the product of the ideal sheaves of the sections `x a`. -/
theorem pointsDivisor_def (x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    E.pointsDivisor x = ∏ a, (x a).left.ker :=
  (rfl)

/-- **`∑_a [x a]` is a relative effective Cartier divisor** on `E` over `S`, as a sum of the
divisors of sections of the smooth separated curve `E ⟶ S`. -/
theorem isRelativeEffectiveCartier_pointsDivisor (x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    (E.pointsDivisor x).IsRelativeEffectiveCartier E.structureMap :=
  isRelativeEffectiveCartier_prod fun a _ ↦
    Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension (f := E.structureMap)
      _ (Over.w (x a))

/-- The divisor `∑_a [x a]` is finite over the base. -/
instance isFinite_pointsDivisor (x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    IsFinite ((E.pointsDivisor x).subschemeι ≫ E.structureMap) :=
  (isRelativeEffectiveCartier_pointsDivisor x).isFinite

/-- The divisor `∑_a [x a]` is flat over the base. -/
instance flat_pointsDivisor (x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    Flat ((E.pointsDivisor x).subschemeι ≫ E.structureMap) :=
  (isRelativeEffectiveCartier_pointsDivisor x).flat

/-- The divisor `∑_a [x a]` is locally of finite presentation over the base. Together with
finiteness and flatness, this makes it finite locally free. -/
instance locallyOfFinitePresentation_pointsDivisor
    (x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    LocallyOfFinitePresentation ((E.pointsDivisor x).subschemeι ≫ E.structureMap) := by
  have : Smooth E.structureMap := SmoothOfRelativeDimension.smooth 1 _
  exact TauCeti.locallyOfFinitePresentation_subschemeι_comp_of_isEffectiveCartier
    (isRelativeEffectiveCartier_pointsDivisor x).isEffectiveCartier

/-- Each of the points `x a` lies on the divisor `∑_a [x a]`. -/
theorem pointsDivisor_le_ker (x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) (a : A) :
    E.pointsDivisor x ≤ (x a).left.ker := by
  classical
  rw [pointsDivisor, ← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
  exact mul_le_of_le_one_right bot_le le_top

/-- The support of the divisor `∑_a [x a]` is the union of the images of the sections `x a`. -/
theorem coe_support_pointsDivisor (x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    ((E.pointsDivisor x).support : Set E.carrier) = ⋃ a, Set.range (x a).left := by
  have (a : A) : IsClosedImmersion (x a).left :=
    (x a).left.isClosedImmersion_of_comp_eq_id (left_comp_structureMap _)
  rw [pointsDivisor_def, Scheme.IdealSheafData.coe_support_prod]
  exact Set.iUnion_congr fun a ↦ by
    rw [Scheme.Hom.support_ker,
      (IsClosedImmersion.isClosedEmbedding (x a).left).isClosed_range.closure_eq]

/-- **Over a field, the points of `E` on `∑_a [x a]` are the `x a`.** -/
theorem mem_support_pointsDivisor_iff {K : Type u} [Field K] {E : EllipticCurveGeom (Spec (.of K))}
    (x : A → (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E.structureMap))
    (y : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E.structureMap) (p : Spec (.of K)) :
    y.left p ∈ ((E.pointsDivisor x).support : Set E.carrier) ↔ y ∈ Set.range x := by
  rw [coe_support_pointsDivisor]
  simp only [Set.mem_iUnion, Set.mem_range]
  refine exists_congr fun a ↦ ⟨fun ⟨q, hq⟩ ↦ ?_, fun h ↦ ⟨p, congrArg (fun z ↦ z.left p) h⟩⟩
  rw [Subsingleton.elim (α := Spec (.of K)) q p] at hq
  exact Over.OverMorphism.ext <| by
    simpa using (comp_eq_comp_iff_of_section (f := E.structureMap) (s₁ := (x a).left)
      (s₂ := y.left) (by simp) (by simp) (𝟙 _) p).mpr (by simpa using hq)

/-- **The divisor `∑_a [x a]` does not depend on the indexing** of the family of points. -/
@[simp]
theorem pointsDivisor_comp_equiv {A' : Type*} [Fintype A']
    (x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) (e : A' ≃ A) :
    E.pointsDivisor (x ∘ e) = E.pointsDivisor x :=
  Fintype.prod_equiv e _ _ fun _ ↦ rfl

/-- A sum of section divisors has rank equal to the number of sections, with multiplicity. -/
@[simp]
theorem finrank_pointsDivisor (x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) (s : S) :
    ((E.pointsDivisor x).subschemeι ≫ E.structureMap).finrank s = Fintype.card A := by
  have (a : A) : IsClosedImmersion (x a).left :=
    (x a).left.isClosedImmersion_of_comp_eq_id (left_comp_structureMap _)
  have := (isRelativeEffectiveCartier_pointsDivisor x).isFinite
  rw [pointsDivisor_def] at this ⊢
  rw [finrank_prod_subschemeι_comp Finset.univ (fun a ↦ (x a).left.ker)
    (fun a _ ↦ Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension
      (x a).left (left_comp_structureMap _))]
  have hr (a : A) : ((x a).left.ker.subschemeι ≫ E.structureMap).finrank = 1 :=
    Scheme.Hom.finrank_ker_comp_eq_one_of_comp_eq_id (x a).left (left_comp_structureMap _)
  simp [hr]

section BaseChange

variable {S' : Scheme.{u}} {E' : EllipticCurveGeom S'} {g : E'.carrier ⟶ E.carrier}
  {f : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap f)
  (h0 : E'.zero ≫ g = f ≫ E.zero)

/-- **The divisor `∑_a [x a]` commutes with base change**: for the base changes `x' a` of the
`S`-points `x a` of `E`, the divisor `∑_a [x' a]` on `E'` is the inverse image along `g` of the
divisor `∑_a [x a]` on `E`. -/
theorem pointsDivisor_pointsPullback (x : A → (𝟙_ (Over S) ⟶ Over.mk E.structureMap)) :
    E'.pointsDivisor (pointsPullback hg h0 ∘ x) = (E.pointsDivisor x).comap g := by
  simp only [pointsDivisor, Scheme.IdealSheafData.comap_prod, Function.comp_apply,
    ker_pointsPullback_left]

end BaseChange

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
