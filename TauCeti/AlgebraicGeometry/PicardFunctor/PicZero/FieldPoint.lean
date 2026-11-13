/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.AlgebraicGeometry.LineBundle.BaseChange
public import TauCeti.AlgebraicGeometry.PicardFunctor.PicZero.Basic

/-!
# `Pic⁰_{X/S}` at field-valued points, and its torsion

Let `f : X ⟶ S` be a morphism of schemes and `g : Spec L ⟶ S` a point with values in a field
`L`, with fibre `X_L = Spec L ×_S X`. The value of the relative Picard presheaf at `g` is
`Pic(X_L) / Pic(Spec L) = Pic(X_L)`, because every line bundle on the spectrum of a field is
trivial (`TauCeti.AlgebraicGeometry.relativePicardPresheafObjMulEquiv`). This file identifies the
value of the degree-zero subfunctor `Pic⁰_{X/S}` at `g` inside it.

When `f` is quasi-compact with affine diagonal, a geometric point `Spec Ω ⟶ Spec L` only extends the
ground field of `X_L`, which does not change the Euler-characteristic degree of a line bundle
(`TauCeti.AlgebraicGeometry.LineBundleClass.eulerDegree_pullback`). So the fibre degree of a
class on `X_L` at every geometric point is its degree over `L`, and the class lies in
`Pic⁰_{X/S}` at `g` exactly when its degree over `L` is zero. The field `L` is arbitrary; it need
not be perfect or algebraically closed.

For a smooth proper geometrically connected family of curves, the `n`-torsion of `Pic⁰_{X/S}(T)`
is the `n`-torsion of `Pic(X_T) / Pic(T)` for every nonzero integer `n`
(`TauCeti.AlgebraicGeometry.relativePicardDegreeZeroTorsionMulEquiv`). When `Pic(T)` is trivial,
as for `T = Spec L`, it is therefore the `n`-torsion `Pic(X_T)[n]` of the Picard group of `X_T`
(`TauCeti.AlgebraicGeometry.relativePicardDegreeZeroTorsionLineBundleClassMulEquiv`, also in
`PicZero.Basic`).
No rational point and no hypothesis on the characteristic is needed. This is the form in which
torsion of a scheme representing `Pic⁰_{X/S}` is compared with torsion line bundles on the curve
`X_L`: the points of the representing scheme with values in `L` are the sections of `Pic⁰_{X/S}`
at `Spec L`.

## Main declarations

* `TauCeti.AlgebraicGeometry.relativePicardFiberDegree_mk_eq_eulerDegree`: at a point of
  `Spec L`, the fibre degree of a class on `X_L` is its degree over `L`;
* `TauCeti.AlgebraicGeometry.mem_relativePicardDegreeZeroSubfunctor_obj_iff_eulerDegree_eq_zero`:
  a section at `Spec L` lies in `Pic⁰_{X/S}` exactly when its class on `X_L` has degree zero.

## References

* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Sections 9.2 and 9.5.
* The Stacks Project, [Tag 0CDN](https://stacks.math.columbia.edu/tag/0CDN), where the
  `ℓ`-torsion of the Picard group of a curve is made rational over a finite separable extension.
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S)

section FieldPoint

variable [QuasiCompact f] [IsAffineHom (pullback.diagonal f)] {L : Type u} [Field L]
  (g : Spec (.of L) ⟶ S)

/-- **At a field-valued point, the fibre degree is the degree on the fibre.** For `f`
quasi-compact with affine diagonal and a point `g : Spec L ⟶ S`, the degree of a line-bundle
class on `X_L = Spec L ×_S X` on the fibre over any point `Spec Ω ⟶ Spec L` is its degree over
`L`: extending the ground field does not change the degree. -/
theorem relativePicardFiberDegree_mk_eq_eulerDegree {Ω : Type u} [Field Ω]
    (ξ : Spec (.of Ω) ⟶ Spec (.of L)) (a : LineBundleClass (pullback g f)) :
    relativePicardFiberDegree f (T := op (Over.mk g)) ξ (QuotientGroup.mk a) =
      letI : (pullback g f).Over (Spec (.of L)) := ⟨pullback.fst g f⟩
      LineBundleClass.eulerDegree L a := by
  let _ : (pullback g f).Over (Spec (.of L)) := ⟨pullback.fst g f⟩
  -- The fibre over `ξ`, written as in `relativePicardFiberDegree_mk`, is a scheme over `Ω`.
  let _ : (pullback (ξ ≫ (op (Over.mk g)).unop.hom) f).Over (Spec (.of Ω)) := ⟨pullback.fst _ _⟩
  -- Make `ξ` the morphism of spectra of a field extension `L → Ω`.
  let _ : Algebra L Ω := (Spec.preimage ξ).hom.toAlgebra
  have hξ : Spec.map (CommRingCat.ofHom (algebraMap L Ω)) = ξ := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  -- `X_L` is quasi-compact with affine diagonal, as a base change of `f`.
  have : CompactSpace ↥(pullback g f) :=
    (quasiCompact_iff_compactSpace (pullback.fst g f)).mp inferInstance
  have : IsAffineHom (pullback.diagonal (terminal.from (pullback g f))) := by
    -- Instance search does not find these closure properties of `@IsAffineHom` and its diagonal.
    have : MorphismProperty.RespectsIso @IsAffineHom.{u} :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have : MorphismProperty.IsStableUnderComposition @IsAffineHom.{u} :=
      MorphismProperty.IsMultiplicative.toIsStableUnderComposition
    have : (MorphismProperty.diagonal @IsAffineHom.{u}).IsStableUnderBaseChange :=
      MorphismProperty.IsStableUnderBaseChange.diagonal
    have : (MorphismProperty.diagonal @IsAffineHom.{u}).IsStableUnderComposition :=
      MorphismProperty.diagonal_isStableUnderComposition
    rw [← terminal.comp_from (pullback.fst g f)]
    exact MorphismProperty.comp_mem (MorphismProperty.diagonal @IsAffineHom) _ _
      (MorphismProperty.pullback_fst g f ‹IsAffineHom (pullback.diagonal f)›)
      (inferInstanceAs (IsAffineHom (pullback.diagonal (terminal.from (Spec (.of L))))))
  -- The fibre over `ξ` is the base change of `X_L` along `ξ`.
  have hsnd : pullback.map (ξ ≫ g) f g f ξ (𝟙 X) (𝟙 S) (by simp) (by simp) ≫ pullback.snd g f =
      pullback.snd (ξ ≫ g) f := by
    simp
  have H : IsPullback (pullback.map (ξ ≫ g) f g f ξ (𝟙 X) (𝟙 S) (by simp) (by simp))
      (pullback.fst (ξ ≫ g) f) (pullback.fst g f)
      (Spec.map (CommRingCat.ofHom (algebraMap L Ω))) := by
    rw [hξ]
    exact IsPullback.of_right (by rw [hsnd]; exact (IsPullback.of_hasPullback (ξ ≫ g) f).flip)
      (by simp) (IsPullback.of_hasPullback g f).flip
  exact (relativePicardFiberDegree_mk f (T := op (Over.mk g)) ξ a).trans
    (LineBundleClass.eulerDegree_pullback H a)

/-- **`Pic⁰_{X/S}` at a field-valued point.** For `f` quasi-compact with affine diagonal and a
point `g : Spec L ⟶ S`, a section of `Pic(X_L) / Pic(Spec L) = Pic(X_L)` at `g`, with
`X_L = Spec L ×_S X`, lies in `Pic⁰_{X/S}` exactly when its line-bundle class on `X_L` has degree
zero over `L`. -/
theorem mem_relativePicardDegreeZeroSubfunctor_obj_iff_eulerDegree_eq_zero
    (c : (relativePicardPresheaf f).obj (op (Over.mk g))) :
    c ∈ (relativePicardDegreeZeroSubfunctor f).obj (op (Over.mk g)) ↔
      letI : (pullback g f).Over (Spec (.of L)) := ⟨pullback.fst g f⟩
      haveI : Subsingleton (LineBundleClass (op (Over.mk g)).unop.left) :=
        inferInstanceAs (Subsingleton (LineBundleClass (Spec (.of L))))
      LineBundleClass.eulerDegree L (X := pullback g f)
        (relativePicardPresheafObjMulEquiv f (op (Over.mk g)) c) = 0 := by
  have : Subsingleton (LineBundleClass (op (Over.mk g)).unop.left) :=
    inferInstanceAs (Subsingleton (LineBundleClass (Spec (.of L))))
  obtain ⟨a, rfl⟩ := (relativePicardPresheafObjMulEquiv f (op (Over.mk g))).symm.surjective c
  -- Every fibre degree of `a` is its degree over `L`.
  have key (Ω : Type u) [Field Ω] (ξ : Spec (.of Ω) ⟶ Spec (.of L)) :
      relativePicardFiberDegree f ξ
          ((relativePicardPresheafObjMulEquiv f (op (Over.mk g))).symm a) =
        letI : (pullback g f).Over (Spec (.of L)) := ⟨pullback.fst g f⟩
        LineBundleClass.eulerDegree L (X := pullback g f) a :=
    (congrArg (relativePicardFiberDegree f ξ)
      (relativePicardPresheafObjMulEquiv_symm_apply f _ a)).trans
        (relativePicardFiberDegree_mk_eq_eulerDegree f g ξ a)
  rw [mem_relativePicardDegreeZeroSubfunctor_obj_iff, MulEquiv.apply_symm_apply]
  simp only [key]
  exact ⟨fun h ↦ h (AlgebraicClosure L)
    (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))), fun h _ _ _ _ ↦ h⟩

end FieldPoint

end

end AlgebraicGeometry

end TauCeti
