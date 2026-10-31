/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCocone.Basic
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Relative coordinates on the shifted mapping cone

For a morphism `f : K ⟶ L` of complexes of modules, relative cochains in degree `p`
are pairs in `K.X p × L.X (p - 1)`, with differential
`(a, b) ↦ (d a, f a - d b)`. They are coordinates on Mathlib's actual
`mappingCocone f = (mappingCone f)⟦-1⟧`, obtained by negating its second projection.
Thus relative cocycles and coboundaries can be used with the native homology and
derived-category constructions, without introducing another complex carrier.

`relativeCoordinates` gives the degreewise linear equivalence. The differential,
cycle and boundary formulas fix its signs, and `relativeCoordinates_map` proves
compatibility with maps of pairs. In particular these formulas apply to restriction
maps between complexes of differential forms, where relative cocycles satisfy
`d a = 0` and `f a = d b`.

The construction uses the projections and inclusions of Mathlib's
`CochainComplex.mappingCocone`, and the component and naturality lemmas in
`TauCeti.Algebra.Homology.HomotopyCategory.MappingCocone.Basic`.

## References

* N. Honda, T. Izawa and T. Suwa, *Sato hyperfunctions via relative Dolbeault
  cohomology*, relative cochain convention.
-/

public section

open CategoryTheory Limits HomologicalComplex

universe u v

namespace CochainComplex.mappingCocone

open HomComplex

variable {R : Type u} [Ring R] {K L : CochainComplex (ModuleCat.{v} R) ℤ} (f : K ⟶ L)

noncomputable section

/-- Relative cochain coordinates on the native shifted cone. The second coordinate is
the negative of `mappingCocone.snd`, so the differential has positive restriction term. -/
def relativeCoordinates (p q : ℤ) (hpq : p + -1 = q) :
    (mappingCocone f).X p ≃ₗ[R] K.X p × L.X q where
  toFun x := ((fst f).f p x, -(snd f).v p q hpq x)
  invFun x := (inl f).v p p (add_zero p) x.1 -
    (inr f).1.v q p (by omega) x.2
  left_inv x := by
    have h := congrArg (fun g : (mappingCocone f).X p ⟶ (mappingCocone f).X p ↦ g x)
      (id_X f p q hpq)
    simpa only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply,
      ModuleCat.id_apply, map_neg, sub_neg_eq_add] using h
  right_inv x := by
    ext <;> simp [← ModuleCat.comp_apply]
  map_add' x y := by simp [add_comm]
  map_smul' r x := by simp

lemma relativeCoordinates_apply (p q : ℤ) (hpq : p + -1 = q) (x : (mappingCocone f).X p) :
    relativeCoordinates f p q hpq x = ((fst f).f p x, -(snd f).v p q hpq x) :=
  (rfl)

lemma relativeCoordinates_symm_apply (p q : ℤ) (hpq : p + -1 = q) (x : K.X p × L.X q) :
    (relativeCoordinates f p q hpq).symm x = (inl f).v p p (add_zero p) x.1 -
      (inr f).1.v q p (by omega) x.2 :=
  (rfl)

/-- In relative coordinates the shifted cone differential is `(a, b) ↦ (d a, f a - d b)`. -/
lemma relativeCoordinates_d (p q : ℤ) (hpq : p + -1 = q)
    (x : (mappingCocone f).X p) :
    relativeCoordinates f (p + 1) p (by omega) ((mappingCocone f).d p (p + 1) x) =
      (K.d p (p + 1) (relativeCoordinates f p q hpq x).1,
        f.f p (relativeCoordinates f p q hpq x).1 -
          L.d q p (relativeCoordinates f p q hpq x).2) := by
  subst hpq
  apply Prod.ext
  · exact congrArg (fun g : (mappingCocone f).X p ⟶ K.X (p + 1) ↦ g x)
      ((fst f).comm p (p + 1)).symm
  · have h := congrArg (fun g : (mappingCocone f).X p ⟶ L.X p ↦ g x) (d_snd_v f p)
    simp only [ModuleCat.hom_sub, LinearMap.sub_apply, ModuleCat.comp_apply,
      ModuleCat.hom_neg, LinearMap.neg_apply] at h
    simpa [relativeCoordinates_apply, sub_eq_add_neg, add_comm] using congrArg Neg.neg h

/-- The differential of a pair inserted into the native shifted cone. -/
lemma d_relativeCoordinates_symm (p q : ℤ) (hpq : p + -1 = q) (x : K.X p × L.X q) :
    (mappingCocone f).d p (p + 1) ((relativeCoordinates f p q hpq).symm x) =
      (relativeCoordinates f (p + 1) p (by omega)).symm
        (K.d p (p + 1) x.1, f.f p x.1 - L.d q p x.2) := by
  apply (relativeCoordinates f (p + 1) p (by omega)).injective
  simp only [relativeCoordinates_d f p q hpq, LinearEquiv.apply_symm_apply]

/-- A relative pair is a cocycle exactly when its first component is closed and
its restriction is the differential of the second component. -/
lemma d_relativeCoordinates_symm_eq_zero_iff (p q : ℤ) (hpq : p + -1 = q)
    (x : K.X p × L.X q) :
    (mappingCocone f).d p (p + 1) ((relativeCoordinates f p q hpq).symm x) = 0 ↔
      K.d p (p + 1) x.1 = 0 ∧ f.f p x.1 = L.d q p x.2 := by
  rw [d_relativeCoordinates_symm]
  rw [← (relativeCoordinates f (p + 1) p (by omega)).symm.map_zero,
    (relativeCoordinates f (p + 1) p (by omega)).symm.injective.eq_iff]
  exact Prod.mk_eq_zero.trans (and_congr_right fun _ ↦ sub_eq_zero)

/-- Relative coboundaries are precisely the pairs `(d c, f c - d e)`. -/
lemma relativeCoordinates_symm_mem_range_d_iff (p q r : ℤ)
    (hpq : p + -1 = q) (hqr : q + -1 = r) (x : K.X p × L.X q) :
    (relativeCoordinates f p q hpq).symm x ∈
        LinearMap.range ((mappingCocone f).d q p).hom ↔
      ∃ c : K.X q, ∃ e : L.X r, K.d q p c = x.1 ∧ f.f q c - L.d r q e = x.2 := by
  obtain rfl : p = q + 1 := by omega
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(relativeCoordinates f q r hqr y).1,
      (relativeCoordinates f q r hqr y).2, ?_⟩
    have h := congrArg (relativeCoordinates f (q + 1) q hpq) hy
    rw [relativeCoordinates_d f q r hqr, LinearEquiv.apply_symm_apply] at h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨c, e, hc, he⟩
    refine ⟨(relativeCoordinates f q r hqr).symm (c, e), ?_⟩
    rw [d_relativeCoordinates_symm f q r hqr]
    congr 1
    exact Prod.ext hc he

/-- A map of pairs acts componentwise in relative coordinates. This includes restriction
and coefficient morphisms whenever they commute with the original map of complexes. -/
lemma relativeCoordinates_map {K' L' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f' : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L') (comm : f ≫ b = a ≫ f')
    (p q : ℤ) (hpq : p + -1 = q) (x : (mappingCocone f).X p) :
    relativeCoordinates f' p q hpq
        (((mappingCone.map f f' a b comm)⟦(-1 : ℤ)⟧').f p x) =
      (a.f p (relativeCoordinates f p q hpq x).1,
        b.f q (relativeCoordinates f p q hpq x).2) := by
  subst hpq
  apply Prod.ext
  · exact congrArg (fun g : (mappingCocone f).X p ⟶ K'.X p ↦ g x)
      (HomologicalComplex.congr_hom
        (shiftFunctor_map_mappingCone_map_comp_fst f f' a b comm) p)
  · have h := congrArg (fun g : (mappingCocone f).X p ⟶ L'.X (p + -1) ↦ g x)
      (shiftFunctor_map_mappingCone_map_f_snd_v f f' a b comm p)
    simp only [ModuleCat.comp_apply] at h
    exact (congrArg Neg.neg h).trans (map_neg _ _).symm

end

end CochainComplex.mappingCocone
