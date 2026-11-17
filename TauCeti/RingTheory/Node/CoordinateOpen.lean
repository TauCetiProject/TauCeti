/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.Basic
public import TauCeti.RingTheory.RingHom.Etale
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

variable {R : Type*} [CommRing R] (a : R)

private def toPuncturedLine (i : Fin 2) :
    NodeAlgebra R a →ₐ[R] Localization.Away (X : R[X]) :=
  lift a (if i = 0 then algebraMap R[X] _ X else
      algebraMap R _ a * IsLocalization.Away.invSelf (X : R[X]))
    (if i = 0 then algebraMap R _ a * IsLocalization.Away.invSelf (X : R[X]) else
      algebraMap R[X] _ X) (by
      fin_cases i
      · simp [mul_left_comm, IsLocalization.Away.mul_invSelf]
      · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
        rw [mul_comm, mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one])

private lemma toPuncturedLine_coord (i : Fin 2) :
    toPuncturedLine a i (coord a i) = algebraMap R[X] _ X := by
  fin_cases i <;> simp [toPuncturedLine]

private lemma toPuncturedLine_coord_one_sub (i : Fin 2) :
    toPuncturedLine a i (coord a (1 - i)) =
      algebraMap R _ a * IsLocalization.Away.invSelf (X : R[X]) := by
  fin_cases i <;> simp [toPuncturedLine]

private def fromPuncturedLine (i : Fin 2) : Localization.Away (X : R[X]) →ₐ[R]
    Localization.Away (coord a i) :=
  IsLocalization.Away.liftAlgHom (X : R[X])
    (f := aeval (algebraMap (NodeAlgebra R a) _ (coord a i)))
    (by simpa using IsLocalization.Away.algebraMap_isUnit (coord a i))

/-- Inverting either coordinate of `uv = a` identifies it with the punctured affine line. -/
def localizationAwayCoordEquiv (i : Fin 2) : Localization.Away (coord a i) ≃ₐ[R]
    Localization.Away (X : R[X]) := by
  let f : Localization.Away (coord a i) →ₐ[R] Localization.Away (X : R[X]) :=
    IsLocalization.Away.liftAlgHom (coord a i) (f := toPuncturedLine a i)
      (by simpa [toPuncturedLine_coord] using IsLocalization.Away.algebraMap_isUnit (X : R[X]))
  let g := fromPuncturedLine a i
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply IsLocalization.algHom_ext (Submonoid.powers (X : R[X]))
    ext
    simp [f, g, fromPuncturedLine, toPuncturedLine_coord, Algebra.algHom]
  · apply IsLocalization.algHom_ext (Submonoid.powers (coord a i))
    -- Check the inverted coordinate first, then recover the other from their product.
    have hcoord (j : Fin 2) :
        g (f (algebraMap _ _ (coord a j))) = algebraMap _ _ (coord a j) := by
      by_cases hj : j = i
      · subst j
        simp [f, g, fromPuncturedLine, toPuncturedLine_coord]
      · have hj' : j = 1 - i := by fin_cases i <;> fin_cases j <;> simp_all
        subst j
        have hf₁ : f (algebraMap _ _ (coord a (1 - i))) =
            algebraMap R _ a * IsLocalization.Away.invSelf (X : R[X]) := by
          simp [f, toPuncturedLine_coord_one_sub]
        rw [hf₁, map_mul, AlgHom.commutes]
        apply (IsLocalization.Away.algebraMap_isUnit (coord a i)
          (S := Localization.Away (coord a i))).mul_left_cancel
        rw [mul_left_comm, ← map_mul, coord_mul_coord_one_sub]
        rw [← IsScalarTower.algebraMap_apply]
        have hgX : g (algebraMap R[X] _ X) = algebraMap _ _ (coord a i) := by
          simp [g, fromPuncturedLine]
        have h := congrArg g (IsLocalization.Away.mul_invSelf
          (S := Localization.Away (X : R[X])) (X : R[X]))
        rw [map_mul, map_one, hgX] at h
        rw [h, mul_one]
    exact hom_ext a (hcoord 0) (hcoord 1)

/-- The comparison sends the inverted coordinate to the Laurent variable. -/
@[simp]
theorem localizationAwayCoordEquiv_algebraMap_coord (i : Fin 2) :
    localizationAwayCoordEquiv a i (algebraMap _ _ (coord a i)) = algebraMap R[X] _ X := by
  simp [localizationAwayCoordEquiv, toPuncturedLine_coord]

/-- The comparison sends the other coordinate to `a/t`. -/
@[simp]
theorem localizationAwayCoordEquiv_algebraMap_coord_one_sub (i : Fin 2) :
    localizationAwayCoordEquiv a i (algebraMap _ _ (coord a (1 - i))) =
      algebraMap R _ a * IsLocalization.Away.invSelf (X : R[X]) := by
  simp [localizationAwayCoordEquiv, toPuncturedLine_coord_one_sub]

/-- The comparison sends the inverse of the inverted coordinate to the inverse variable. -/
@[simp]
theorem localizationAwayCoordEquiv_invSelf (i : Fin 2) :
    localizationAwayCoordEquiv a i (IsLocalization.Away.invSelf (coord a i)) =
      IsLocalization.Away.invSelf (X : R[X]) := by
  apply (IsLocalization.Away.algebraMap_isUnit (X : R[X])
    (S := Localization.Away (X : R[X]))).mul_left_cancel
  rw [IsLocalization.Away.mul_invSelf, ← localizationAwayCoordEquiv_algebraMap_coord a i,
    ← map_mul, IsLocalization.Away.mul_invSelf, map_one]

/-- The inverse comparison sends the inverse variable to the inverse node coordinate. -/
@[simp]
theorem localizationAwayCoordEquiv_symm_invSelf (i : Fin 2) :
    (localizationAwayCoordEquiv a i).symm (IsLocalization.Away.invSelf (X : R[X])) =
      IsLocalization.Away.invSelf (coord a i) := by
  apply (localizationAwayCoordEquiv a i).injective
  simp

/-- On a polynomial, the inverse comparison is evaluation at the inverted coordinate. -/
@[simp]
theorem localizationAwayCoordEquiv_symm_algebraMap (i : Fin 2) (p : R[X]) :
    (localizationAwayCoordEquiv a i).symm (algebraMap R[X] _ p) =
      aeval (algebraMap (NodeAlgebra R a) _ (coord a i)) p := by
  simp [localizationAwayCoordEquiv, fromPuncturedLine]

/-- An invertible étale coordinate `x` on an `R`-algebra gives an étale node chart
`u ↦ x`, `v ↦ y` whenever `xy = a`. -/
theorem etale_lift_of_isUnit_of_etale_aeval {T : Type*} [CommRing T] [Algebra R T]
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
  let f := (g.comp (localizationAwayCoordEquiv a 0).toAlgHom).comp
    (IsScalarTower.toAlgHom R (NodeAlgebra R a) (Localization.Away (coord a 0)))
  have hf₀ : f (coord a 0) = x := by
    simp only [f, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, AlgEquiv.coe_toAlgHom,
      localizationAwayCoordEquiv_algebraMap_coord]
    exact (IsLocalization.Away.lift_eq (X : P) (g := (aeval x).toRingHom)
      (by simpa using hx) X).trans (aeval_X x)
  have hf : f = lift a x y hxy := by
    apply hom_ext a
    · simpa using hf₀
    apply hx.mul_left_cancel
    rw [lift_coord_one, ← hf₀, ← map_mul, coord_zero_mul_coord_one, AlgHom.commutes, hf₀, hxy]
  rw [← hf]
  exact (hg.comp (RingHom.Etale.of_bijective
    (localizationAwayCoordEquiv a 0).bijective)).comp
    (RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway (coord a 0)))

variable (R) in
/-- Given a proper ideal of a standard smooth relative curve, some element outside the ideal
defines a principal open mapping étale to `uv = 0`, with the first node coordinate invertible. -/
theorem _root_.Ideal.exists_notMem_etale_nodeAlgebra_hom_of_isStandardSmoothOfRelativeDimension_one
    {S : Type*} [CommRing S] [Algebra R S]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R S] (q : Ideal S) (hq : q ≠ ⊤) :
    ∃ t ∉ q, ∃ φ : NodeAlgebra R 0 →ₐ[R] Localization.Away t,
      φ.toRingHom.Etale ∧ IsUnit (φ (coord 0 0)) ∧ φ (coord 0 1) = 0 := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 R S
  let e := MvPolynomial.uniqueAlgEquiv R (Fin 1)
  let p := g.comp e.symm.toAlgHom
  have hp : p.toRingHom.Etale := hg.comp (RingHom.Etale.of_bijective e.symm.bijective)
  -- Translate the coordinate by either zero or one so that it does not vanish at `q`.
  obtain ⟨c, hc⟩ : ∃ c : R, p X + algebraMap R S c ∉ q := by
    by_cases h : p X ∈ q
    · refine ⟨1, fun h' ↦ ?_⟩
      have h1 : (1 : S) ∈ q := by simpa using q.sub_mem h' h
      exact hq ((Ideal.eq_top_iff_one q).mpr h1)
    · exact ⟨0, by simpa using h⟩
  let p' := p.comp (algEquivAevalXAddC c).toAlgHom
  have hp' : p'.toRingHom.Etale := hp.comp
    (RingHom.Etale.of_bijective (algEquivAevalXAddC c).bijective)
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
    exact (RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway t)).comp hp'
  refine ⟨t, ht, lift 0 x 0 (by simp),
    etale_lift_of_isUnit_of_etale_aeval 0 x 0 (by simp) hx he, ?_, ?_⟩
  · simpa using hx
  · simp

end TauCeti.NodeAlgebra
