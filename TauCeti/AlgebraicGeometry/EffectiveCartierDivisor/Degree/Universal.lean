/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.Basic
public import TauCeti.CategoryTheory.Subfunctor.Representable

/-!
# The universal divisor of a represented divisor functor

A representation of the degree-`d` relative effective Cartier divisor functor determines an
actual effective Cartier divisor on `H ×_S X`: the divisor corresponding to `𝟙 H`. Every family
is its pullback, and its projection to `H` is finite flat of constant degree `d`.

## References

* The Stacks Project, Tag 0B9I.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  Opposite TauCeti.AlgebraicGeometry

universe u

namespace CategoryTheory.Functor.RepresentableBy

variable {X S : Scheme.{u}} {f : X ⟶ S} [IsProper f] [RelativeDimensionLE 1 f]
  {d : ℕ} {H : Over S}
  (e : (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.RepresentableBy H)

/-- The ideal of the universal effective Cartier divisor on `H ×_S X`. -/
def effectiveCartierUniversalIdeal : (pullback H.hom f).IdealSheafData :=
  (e.homEquiv (𝟙 H)).val.val

/-- The universal ideal is the ideal classified by the identity of its parameter scheme. -/
theorem effectiveCartierUniversalIdeal_def :
    e.effectiveCartierUniversalIdeal = (e.homEquiv (𝟙 H)).val.val := (rfl)

/-- The divisor classified by a morphism to `H` is the pullback of the universal divisor. -/
@[simp↓]
theorem effectiveCartierUniversalIdeal_comap {T : Over S} (t : T ⟶ H) :
    (e.effectiveCartierUniversalIdeal.comap ((Over.pullback f).map t).left) =
      (e.homEquiv t).val.val := by
  have h := congrArg Subtype.val (e.homEquiv_comp_val t (𝟙 H))
  simpa only [Category.comp_id, Subfunctor.toFunctor_map_val, baseChangeIdealSheafFunctor_map_apply,
    effectiveCartierUniversalIdeal_def, Quiver.Hom.unop_op] using h.symm

/-- The universal ideal is a relative effective Cartier divisor over its parameter scheme. -/
theorem isRelativeEffectiveCartier_effectiveCartierUniversalIdeal :
    e.effectiveCartierUniversalIdeal.IsRelativeEffectiveCartier (pullback.fst H.hom f) :=
  (mem_relativeEffectiveCartierSubfunctor_obj_iff f).mp (e.homEquiv (𝟙 H)).val.property

instance : IsFinite (e.effectiveCartierUniversalIdeal.subschemeι ≫ pullback.fst H.hom f) :=
  e.isRelativeEffectiveCartier_effectiveCartierUniversalIdeal.isFinite

instance : Flat (e.effectiveCartierUniversalIdeal.subschemeι ≫ pullback.fst H.hom f) :=
  e.isRelativeEffectiveCartier_effectiveCartierUniversalIdeal.flat

/-- The universal divisor is locally finitely presented over its parameter scheme when the
ambient morphism is locally finitely presented. -/
instance locallyOfFinitePresentation_effectiveCartierUniversalIdeal_subschemeι_comp_fst
    [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation
      (e.effectiveCartierUniversalIdeal.subschemeι ≫ pullback.fst H.hom f) :=
  TauCeti.locallyOfFinitePresentation_subschemeι_comp_of_isEffectiveCartier
    e.isRelativeEffectiveCartier_effectiveCartierUniversalIdeal.isEffectiveCartier

/-- The projection of the universal divisor has constant rank equal to its degree. -/
@[simp]
theorem finrank_effectiveCartierUniversalIdeal_subschemeι_comp_fst (h : H.left) :
    (e.effectiveCartierUniversalIdeal.subschemeι ≫ pullback.fst H.hom f).finrank h = d :=
  congrFun ((mem_relativeEffectiveCartierDegreeSubfunctor_obj_iff f).mp
    (e.homEquiv (𝟙 H)).property) h

/-- The total space of the universal divisor, regarded as a scheme over `S`. -/
abbrev effectiveCartierUniversalDivisor : Over S :=
  Over.mk (e.effectiveCartierUniversalIdeal.subschemeι ≫ pullback.fst H.hom f ≫ H.hom)

/-- The projection of the universal divisor to its parameter scheme. -/
def effectiveCartierUniversalProjection : e.effectiveCartierUniversalDivisor ⟶ H :=
  Over.homMk (e.effectiveCartierUniversalIdeal.subschemeι ≫ pullback.fst H.hom f)

/-- The marked point of the universal divisor as a morphism to the relative curve. -/
def effectiveCartierUniversalPoint : e.effectiveCartierUniversalDivisor ⟶ Over.mk f :=
  Over.homMk (e.effectiveCartierUniversalIdeal.subschemeι ≫ pullback.snd H.hom f)
    (by simp [pullback.condition])

/-- The underlying projection is the first component of the universal closed immersion. -/
@[simp]
theorem effectiveCartierUniversalProjection_left :
    e.effectiveCartierUniversalProjection.left =
      e.effectiveCartierUniversalIdeal.subschemeι ≫ pullback.fst H.hom f := (rfl)

/-- The underlying marked point is the second component of the universal closed immersion. -/
@[simp]
theorem effectiveCartierUniversalPoint_left :
    e.effectiveCartierUniversalPoint.left =
      e.effectiveCartierUniversalIdeal.subschemeι ≫ pullback.snd H.hom f := (rfl)

/-- Pairing the universal projection and point recovers the universal closed immersion. -/
@[simp↓]
theorem lift_effectiveCartierUniversalProjection_effectiveCartierUniversalPoint_left :
    (lift e.effectiveCartierUniversalProjection e.effectiveCartierUniversalPoint).left =
      e.effectiveCartierUniversalIdeal.subschemeι := by
  apply pullback.hom_ext <;> simp

/-- The universal marked point is contained in the divisor classified by the universal
projection. The reversed order is the order on defining ideals. -/
theorem homEquiv_effectiveCartierUniversalProjection_le_ker_graphSection :
    (e.homEquiv e.effectiveCartierUniversalProjection).val.val ≤
      (graphSection e.effectiveCartierUniversalPoint).ker := by
  rw [← e.effectiveCartierUniversalIdeal_comap,
    ← Scheme.IdealSheafData.le_map_iff_comap_le]
  simp only [Scheme.IdealSheafData.map_ker, graphSection_comp_pullback_map_eq_lift,
    lift_effectiveCartierUniversalProjection_effectiveCartierUniversalPoint_left,
    Scheme.IdealSheafData.ker_subschemeι, le_refl]

end CategoryTheory.Functor.RepresentableBy
