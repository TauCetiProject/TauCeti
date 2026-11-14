/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.Basic
public import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.StandardSmooth

/-!
# Coordinate opens of a node

The open subset `u ≠ 0` of `uv = a` is the punctured affine line: its coordinate algebra is
`R[t, t⁻¹]`, with `u = t` and `v = a/t`. This identification lets an invertible étale coordinate
on a smooth relative curve give an étale map to the smooth part of the split node `uv = 0`.

The étale coordinate is supplied by Mathlib's
`Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`; translation uses
`Polynomial.algEquivAevalXAddC`.

## References

* Stacks Project, [Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC).
-/

public section

noncomputable section

namespace TauCeti.NodeAlgebra

open Polynomial

universe u

variable {R : Type u} [CommRing R] (a : R)

private def toPuncturedLine : NodeAlgebra R a →ₐ[R] Localization.Away (X : R[X]) :=
  lift a (algebraMap R[X] _ X)
    (algebraMap R _ a * IsLocalization.Away.invSelf (X : R[X])) (by
      rw [mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one])

private def fromPuncturedLine : Localization.Away (X : R[X]) →ₐ[R]
    Localization.Away (coord a 0) :=
  IsLocalization.Away.liftAlgHom (X : R[X])
    (f := aeval (algebraMap (NodeAlgebra R a) _ (coord a 0)))
    (by simpa using IsLocalization.Away.algebraMap_isUnit (coord a 0))

/-- Inverting the first coordinate of `uv = a` identifies it with the punctured affine line. -/
def coordinateOpenEquiv : Localization.Away (coord a 0) ≃ₐ[R]
    Localization.Away (X : R[X]) := by
  let f : Localization.Away (coord a 0) →ₐ[R] Localization.Away (X : R[X]) :=
    IsLocalization.Away.liftAlgHom (coord a 0) (f := toPuncturedLine a)
      (by simpa [toPuncturedLine] using IsLocalization.Away.algebraMap_isUnit (X : R[X]))
  let g := fromPuncturedLine a
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply IsLocalization.algHom_ext (Submonoid.powers (X : R[X]))
    ext
    simp [f, g, fromPuncturedLine, toPuncturedLine, Algebra.algHom]
  · apply IsLocalization.algHom_ext (Submonoid.powers (coord a 0))
    apply hom_ext
    · simp [f, g, fromPuncturedLine, toPuncturedLine, Algebra.algHom]
    · have hf₁ : f (algebraMap _ _ (coord a 1)) =
          algebraMap R _ a * IsLocalization.Away.invSelf (X : R[X]) := by
        simp [f, toPuncturedLine]
      simp only [AlgHom.comp_apply, AlgHom.id_apply, Algebra.algHom,
        IsScalarTower.toAlgHom_apply]
      rw [hf₁, map_mul, AlgHom.commutes]
      apply (IsLocalization.Away.algebraMap_isUnit (coord a 0)
        (S := Localization.Away (coord a 0))).mul_left_cancel
      rw [mul_left_comm, ← map_mul, coord_zero_mul_coord_one]
      rw [← IsScalarTower.algebraMap_apply]
      have hgX : g (algebraMap R[X] _ X) = algebraMap _ _ (coord a 0) := by
        simp [g, fromPuncturedLine]
      have h := congrArg g (IsLocalization.Away.mul_invSelf (S := Localization.Away (X : R[X]))
        (X : R[X]))
      rw [map_mul, map_one, hgX] at h
      rw [h, mul_one]

/-- The coordinate-open comparison sends the first coordinate to the Laurent variable. -/
@[simp]
theorem coordinateOpenEquiv_algebraMap_coord_zero :
    coordinateOpenEquiv a (algebraMap _ _ (coord a 0)) = algebraMap R[X] _ X := by
  simp [coordinateOpenEquiv, toPuncturedLine]

/-- The coordinate-open comparison sends the second coordinate to `a/t`. -/
@[simp]
theorem coordinateOpenEquiv_algebraMap_coord_one :
    coordinateOpenEquiv a (algebraMap _ _ (coord a 1)) =
      algebraMap R _ a * IsLocalization.Away.invSelf (X : R[X]) := by
  simp [coordinateOpenEquiv, toPuncturedLine]

/-- The inverse coordinate-open comparison sends the Laurent variable to the first
coordinate of the node. -/
@[simp]
theorem coordinateOpenEquiv_symm_algebraMap_X :
    (coordinateOpenEquiv a).symm (algebraMap R[X] _ X) = algebraMap _ _ (coord a 0) := by
  apply (coordinateOpenEquiv a).injective
  simp

/-- An invertible étale coordinate `x` on an `R`-algebra gives an étale node chart
`u ↦ x`, `v ↦ y` whenever `xy = a`. -/
theorem etale_lift_of_isUnit_of_etale_aeval {T : Type u} [CommRing T] [Algebra R T]
    (x y : T) (hxy : x * y = algebraMap R T a) (hx : IsUnit x)
    (he : (aeval (R := R) x).toRingHom.Etale) :
    (lift a x y hxy).toRingHom.Etale := by
  let P := R[X]
  let L := Localization.Away (X : P)
  let g : L →ₐ[R] T := IsLocalization.Away.liftAlgHom (X : P) (f := aeval x)
    (by simpa using hx)
  have hg : g.toRingHom.Etale := by
    let : Algebra P T := (aeval (R := R) x).toRingHom.toAlgebra
    have : Algebra.Etale P T := he
    let : Algebra L T := g.toRingHom.toAlgebra
    have : IsScalarTower P L T := .of_algebraMap_eq fun p ↦
      (IsLocalization.Away.lift_eq (X : P) (g := (aeval x).toRingHom)
        (by simpa using hx) p).symm
    have : Algebra.Etale P L := .of_isLocalizationAway X
    exact RingHom.etale_algebraMap.mpr (Algebra.Etale.of_restrictScalars P L T)
  let f := (g.comp (coordinateOpenEquiv a).toAlgHom).comp
    (IsScalarTower.toAlgHom R (NodeAlgebra R a) (Localization.Away (coord a 0)))
  have hf₀ : f (coord a 0) = x := by
    simp only [f, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, AlgEquiv.coe_toAlgHom,
      coordinateOpenEquiv_algebraMap_coord_zero]
    exact (IsLocalization.Away.lift_eq (X : P) (g := (aeval x).toRingHom)
      (by simpa using hx) X).trans (aeval_X x)
  have hf : f = lift a x y hxy := by
    apply hom_ext a
    · simpa using hf₀
    apply hx.mul_left_cancel
    rw [lift_coord_one, ← hf₀, ← map_mul, coord_zero_mul_coord_one, AlgHom.commutes, hf₀, hxy]
  rw [← hf]
  exact RingHom.Etale.stableUnderComposition
    (algebraMap (NodeAlgebra R a) (Localization.Away (coord a 0)))
    (g.toRingHom.comp (coordinateOpenEquiv a).toRingHom)
    (RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway (coord a 0)))
    (RingHom.Etale.stableUnderComposition (coordinateOpenEquiv a).toRingHom g.toRingHom
      (RingHom.Etale.of_bijective (coordinateOpenEquiv a).bijective)
      hg)

/-- Every point of a standard smooth relative curve has a principal open neighbourhood
mapping étale to `uv = 0`, with the first node coordinate invertible. -/
theorem _root_.Ideal.exists_notMem_etale_nodeAlgebra_hom_of_isStandardSmooth
    {S : Type u} [CommRing S] [Algebra R S]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R S] (q : Ideal S) [q.IsPrime] :
    ∃ t ∉ q, ∃ φ : NodeAlgebra R 0 →ₐ[R] Localization.Away t,
      φ.toRingHom.Etale ∧ IsUnit (φ (coord 0 0)) ∧ φ (coord 0 1) = 0 := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 R S
  let e := MvPolynomial.uniqueAlgEquiv R (Fin 1)
  let p := g.comp e.symm.toAlgHom
  have hp : p.toRingHom.Etale := RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective e.symm.bijective) hg
  -- Translate the coordinate by either zero or one so that it does not vanish at `q`.
  obtain ⟨c, hc⟩ : ∃ c : R, p X + algebraMap R S c ∉ q := by
    by_cases h : p X ∈ q
    · refine ⟨1, fun h' ↦ ?_⟩
      have h1 : (1 : S) ∈ q := by simpa using q.sub_mem h' h
      exact Ideal.IsPrime.ne_top' ((Ideal.eq_top_iff_one q).mpr h1)
    · exact ⟨0, by simpa using h⟩
  let p' := p.comp (algEquivAevalXAddC c).toAlgHom
  have hp' : p'.toRingHom.Etale := RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (algEquivAevalXAddC c).bijective) hp
  let t := p' X
  have ht : t ∉ q := by simpa [t, p', Polynomial.C_eq_algebraMap] using hc
  let x : Localization.Away t := algebraMap S _ t
  have hx : IsUnit x := IsLocalization.Away.algebraMap_isUnit t
  have he : (aeval (R := R) x).toRingHom.Etale := by
    have heq : (aeval (R := R) x).toRingHom = (algebraMap S (Localization.Away t)).comp
        p'.toRingHom := by
      apply Polynomial.ringHom_ext
      · intro r
        simp [Polynomial.C_eq_algebraMap, IsScalarTower.algebraMap_apply R S (Localization.Away t)]
      · simp [x, t]
    rw [heq]
    exact RingHom.Etale.stableUnderComposition _ _ hp'
      (RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway t))
  refine ⟨t, ht, lift 0 x 0 (by simp),
    etale_lift_of_isUnit_of_etale_aeval 0 x 0 (by simp) hx he, ?_, ?_⟩
  · simpa using hx
  · simp

end TauCeti.NodeAlgebra
