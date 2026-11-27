/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Polynomial coordinates on base changes of affine space

For `g : T ⟶ S`, the polynomial coordinate map identifies the global functions on
`T ×_S 𝔸(n; S)` with `Γ(T)[n]` when `T` is affine. Its constants, coordinates and naturality
laws use the first projection to `T`, as in the functor of ideal sheaves on base changes.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits MvPolynomial

namespace AlgebraicGeometry.AffineSpace

variable (n : Type u) {S T : Scheme.{u}}

/-- The polynomial coordinate map of `T ×_S 𝔸(n; S)` over `T`. -/
def toΓBaseChange (g : T ⟶ S) :
    MvPolynomial n Γ(T, ⊤) →+* Γ(pullback g (𝔸(n; S) ↘ S), ⊤) :=
  eval₂Hom (pullback.fst g (𝔸(n; S) ↘ S)).appTop.hom
    fun i ↦ (pullback.snd g (𝔸(n; S) ↘ S)).appTop (coord S i)

/-- Constants pull back from the test scheme. -/
@[simp]
theorem toΓBaseChange_C (g : T ⟶ S) (a : Γ(T, ⊤)) :
    toΓBaseChange n g (C a) = (pullback.fst g (𝔸(n; S) ↘ S)).appTop a :=
  eval₂_C _ _ _

/-- Indeterminates pull back from the corresponding affine-space coordinates. -/
@[simp]
theorem toΓBaseChange_X (g : T ⟶ S) (i : n) :
    toΓBaseChange n g (X i) = (pullback.snd g (𝔸(n; S) ↘ S)).appTop (coord S i) :=
  eval₂_X _ _ _

/-- Over an affine test scheme, the base-changed affine space has polynomial coordinate ring. -/
theorem toΓBaseChange_bijective (g : T ⟶ S) [IsAffine T] :
    Function.Bijective (toΓBaseChange n g) := by
  let e := (isPullback_map (n := n) g).flip.isoPullback
  have : IsIso e.hom.appTop := Scheme.Γ.map_isIso e.hom.op
  have he : Function.Bijective e.hom.appTop := ConcreteCategory.bijective_of_isIso _
  have key : e.hom.appTop.hom.comp (toΓBaseChange n g) =
      eval₂Hom (𝔸(n; T) ↘ T).appTop.hom (coord T) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
    · simp [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e]
    · simp [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e]
  rw [← Function.Bijective.of_comp_iff' he, ← RingHom.coe_comp, key]
  have h : eval₂Hom (𝔸(n; T) ↘ T).appTop.hom (coord T) =
      ((Scheme.ΓSpecIso _).inv ≫ (isoOfIsAffine n T).hom.appTop).hom := by
    rw [isoOfIsAffine_hom_appTop, Iso.inv_hom_id_assoc, CommRingCat.hom_ofHom]
  rw [h]
  have : IsIso (isoOfIsAffine n T).hom.appTop :=
    Scheme.Γ.map_isIso (isoOfIsAffine n T).hom.op
  exact ConcreteCategory.bijective_of_isIso _

/-- The polynomial coordinate isomorphism of an affine base change of affine space. -/
def toΓBaseChangeEquiv (g : T ⟶ S) [IsAffine T] :
    MvPolynomial n Γ(T, ⊤) ≃+* Γ(pullback g (𝔸(n; S) ↘ S), ⊤) :=
  RingEquiv.ofBijective _ (toΓBaseChange_bijective n g)

/-- The coordinate isomorphism has the original polynomial coordinate map as ring map. -/
@[simp]
theorem toΓBaseChangeEquiv_toRingHom (g : T ⟶ S) [IsAffine T] :
    (toΓBaseChangeEquiv n g : _ →+* _) = toΓBaseChange n g :=
  (rfl)

/-- The coordinate isomorphism sends constants to functions from the test scheme. -/
theorem toΓBaseChangeEquiv_comp_C (g : T ⟶ S) [IsAffine T] :
    (toΓBaseChangeEquiv n g).toRingHom.comp C =
      (pullback.fst g (𝔸(n; S) ↘ S)).appTop.hom := by
  ext a
  exact toΓBaseChange_C n g a

/-- Polynomial coordinates commute with a change of test scheme. -/
theorem appTop_pullbackMap_toΓBaseChange {T' : Scheme.{u}} (g : T ⟶ S) (g' : T' ⟶ S)
    (h : T' ⟶ T) (hh : h ≫ g = g') (p : MvPolynomial n Γ(T, ⊤)) :
    (pullback.map g' (𝔸(n; S) ↘ S) g (𝔸(n; S) ↘ S) h (𝟙 _) (𝟙 S)
        (by simp [hh]) (by simp)).appTop (toΓBaseChange n g p) =
      toΓBaseChange n g' (MvPolynomial.map h.appTop.hom p) := by
  refine RingHom.congr_fun (f := RingHom.comp _ (toΓBaseChange n g))
    (g := (toΓBaseChange n g').comp (MvPolynomial.map h.appTop.hom)) ?_ p
  refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
  · simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_C, toΓBaseChange_C]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, pullback.lift_fst]
  · simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_X, toΓBaseChange_X]
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_snd,
      Category.comp_id]

end AlgebraicGeometry.AffineSpace
