/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import TauCeti.AlgebraicGeometry.Compactification.BaseChange
public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# Dense replacement of scheme compactifications

The dense replacement of a compactification `X ⟶ Xbar ⟶ S` replaces `Xbar` by the
scheme-theoretic closure of the interior, that is, the scheme-theoretic image of the open
immersion `j : X ⟶ Xbar`. The interior map to this closed subscheme is still a quasi-compact
open immersion (Mathlib's instance for `Scheme.Hom.toImage` of a quasi-compact immersion), so the
open subscheme `X` is kept with its full scheme structure, including nilpotents. It is
scheme-theoretically dense by construction.

A closed immersion of compactifications is a monomorphism through which every map out of a
dense compactification factors (`Compactification.liftOfIsClosedImmersion`). Applied to the
closed immersion `denseReplacementMap C` from the dense replacement to `C`, this shows that dense
replacement is right adjoint to the inclusion of dense compactifications, so the dense
compactifications form a coreflective full subcategory. A compactification is isomorphic to its
dense replacement exactly when it is already dense.

Under an arbitrary base change, the dense replacement of the pulled-back compactification maps
canonically to the base change of the dense replacement (`denseReplacementBaseChange`). For a
flat base change this comparison is an isomorphism.

## Main declarations

* `TauCeti.Compactification.denseReplacement`: the dense compactification given by the
  scheme-theoretic closure of the interior.
* `TauCeti.Compactification.denseReplacementMap`: its canonical closed immersion back to the
  original compactification.
* `TauCeti.Compactification.denseReplacementFunctor` and
  `TauCeti.Compactification.denseReplacementAdjunction`: dense replacement is right adjoint to
  the inclusion of dense compactifications.
* `TauCeti.Compactification.isIso_denseReplacementMap_iff`: the canonical map is an isomorphism
  exactly for dense compactifications.
* `TauCeti.Compactification.denseReplacementBaseChange`: the base-change comparison, an
  isomorphism for flat base change.

## References

* The Stacks Project, Section 29.6, *Scheme theoretic image* (tag 01R5).
* The Stacks Project, Section 29.7, *Scheme theoretic closure and density* (tag 01RB).
* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT).
-/

public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace TauCeti

variable {X S T : Scheme.{u}} {f : X ⟶ S}

namespace Compactification

noncomputable section

/-- The dense replacement of a compactification: the ambient scheme is the scheme-theoretic
image of the interior, with the induced open immersion and the restricted proper map. -/
-- Exposure and implicit reducibility keep the projection formulas of the ambient scheme and its
-- maps usable for dependent morphism equations in importing modules.
@[expose, implicit_reducible] def denseReplacement (C : Compactification f) :
    DenseCompactification f :=
  ⟨ofHom C.j.toImage (C.j.imageι ≫ C.p) (by simp),
    (denseCompactificationProperty_iff f _).mpr inferInstance⟩

@[simp]
theorem denseReplacement_Xbar (C : Compactification f) :
    (denseReplacement C).obj.Xbar = C.j.image :=
  (rfl)

@[simp]
theorem denseReplacement_j (C : Compactification f) :
    (denseReplacement C).obj.j = C.j.toImage :=
  (rfl)

@[simp]
theorem denseReplacement_p (C : Compactification f) :
    (denseReplacement C).obj.p = C.j.imageι ≫ C.p :=
  (rfl)

/-- The canonical closed immersion from the dense replacement to the original
compactification. -/
def denseReplacementMap (C : Compactification f) : (denseReplacement C).obj ⟶ C :=
  ObjectProperty.homMk
    { h := C.j.imageι
      ι_h := C.j.toImage_imageι }

@[simp]
theorem denseReplacementMap_hom_h (C : Compactification f) :
    (denseReplacementMap C).hom.h = C.j.imageι :=
  (rfl)

instance (C : Compactification f) : IsClosedImmersion (denseReplacementMap C).hom.h := by
  rw [denseReplacementMap_hom_h]
  infer_instance

/-- Maps into a dense replacement are determined by their composite with the canonical map. -/
theorem denseReplacement_hom_ext {C : Compactification f} {E : DenseCompactification f}
    {a b : E ⟶ denseReplacement C}
    (h : a.hom ≫ denseReplacementMap C = b.hom ≫ denseReplacementMap C) : a = b :=
  ObjectProperty.hom_ext _ <| (cancel_mono (denseReplacementMap C)).mp h

/-- The map from a dense compactification to the dense replacement of `C` induced by a map
to `C`. -/
def liftDenseReplacement {C : Compactification f} {E : DenseCompactification f}
    (h : E.obj ⟶ C) : E ⟶ denseReplacement C :=
  ObjectProperty.homMk (liftOfIsClosedImmersion (denseReplacementMap C) E h)

@[reassoc (attr := simp)]
theorem liftDenseReplacement_hom_comp {C : Compactification f} {E : DenseCompactification f}
    (h : E.obj ⟶ C) : (liftDenseReplacement h).hom ≫ denseReplacementMap C = h :=
  liftOfIsClosedImmersion_comp _ _ _

@[reassoc (attr := simp)]
theorem liftDenseReplacement_hom_hom_h_comp {C : Compactification f}
    {E : DenseCompactification f} (h : E.obj ⟶ C) :
    (liftDenseReplacement h).hom.hom.h ≫ C.j.imageι = h.hom.h :=
  liftOfIsClosedImmersion_hom_h_comp _ _ _

variable (f) in
/-- Dense replacement, as a functor from compactifications to dense compactifications. -/
-- The object equations must remain available when elaborating dependent morphism formulas.
@[expose, implicit_reducible]
def denseReplacementFunctor : Compactification f ⥤ DenseCompactification f where
  obj := denseReplacement
  map h := liftDenseReplacement (denseReplacementMap _ ≫ h)
  map_id C := denseReplacement_hom_ext (by simp)
  map_comp h k := denseReplacement_hom_ext (by simp)

@[simp]
theorem denseReplacementFunctor_obj (C : Compactification f) :
    (denseReplacementFunctor f).obj C = denseReplacement C :=
  (rfl)

@[reassoc (attr := simp)]
theorem denseReplacementFunctor_map_hom_comp {C D : Compactification f} (h : C ⟶ D) :
    ((denseReplacementFunctor f).map h).hom ≫ denseReplacementMap D =
      denseReplacementMap C ≫ h :=
  liftDenseReplacement_hom_comp _

@[reassoc (attr := simp)]
theorem denseReplacementFunctor_map_hom_hom_h_comp {C D : Compactification f} (h : C ⟶ D) :
    ((denseReplacementFunctor f).map h).hom.hom.h ≫ D.j.imageι = C.j.imageι ≫ h.hom.h :=
  liftDenseReplacement_hom_hom_h_comp _

variable (f) in
/-- Dense replacement is right adjoint to the inclusion of dense compactifications; the counit
is the canonical map `denseReplacementMap`. -/
def denseReplacementAdjunction :
    (denseCompactificationProperty f).ι ⊣ denseReplacementFunctor f :=
  Adjunction.mkOfHomEquiv
    { homEquiv E C :=
        { toFun := liftDenseReplacement
          invFun a := a.hom ≫ denseReplacementMap C
          left_inv h := liftDenseReplacement_hom_comp h
          right_inv a := denseReplacement_hom_ext (liftDenseReplacement_hom_comp _) }
      homEquiv_naturality_left_symm _ _ := by simp
      homEquiv_naturality_right _ _ := denseReplacement_hom_ext (by simp [Equiv.coe_fn_mk]) }

@[simp]
theorem denseReplacementAdjunction_unit_app (E : DenseCompactification f) :
    (denseReplacementAdjunction f).unit.app E = liftDenseReplacement (𝟙 E.obj) := by
  simp [denseReplacementAdjunction]

@[simp]
theorem denseReplacementAdjunction_counit_app (C : Compactification f) :
    (denseReplacementAdjunction f).counit.app C = denseReplacementMap C := by
  simp [denseReplacementAdjunction]

variable (f) in
/-- Dense compactifications form a coreflective full subcategory of compactifications. -/
instance : Coreflective (denseCompactificationProperty f).ι :=
  ⟨_, denseReplacementAdjunction f⟩

/-- A compactification is isomorphic to its dense replacement through the canonical map exactly
when its interior is scheme-theoretically dense. -/
theorem isIso_denseReplacementMap_iff (C : Compactification f) :
    IsIso (denseReplacementMap C) ↔ IsSchemeTheoreticallyDominant C.j := by
  refine ⟨fun _ ↦ ?_, fun hC ↦ ?_⟩
  · rw [← C.j.toImage_imageι, ← denseReplacementMap_hom_h]
    infer_instance
  · let E : DenseCompactification f := ⟨C, (denseCompactificationProperty_iff f C).mpr hC⟩
    refine ⟨(liftDenseReplacement (E := E) (𝟙 C)).hom, ?_, by simp⟩
    rw [← cancel_mono (denseReplacementMap C)]
    simp

instance isIso_denseReplacementMap (C : DenseCompactification f) :
    IsIso (denseReplacementMap C.obj) :=
  (isIso_denseReplacementMap_iff C.obj).mpr inferInstance

/-- The canonical comparison from the dense replacement of a base change to the base change of
the dense replacement. -/
def denseReplacementBaseChange (C : Compactification f) (g : T ⟶ S) :
    (denseReplacement (C.baseChange g)).obj ⟶ (denseReplacement C).obj.baseChange g :=
  liftOfIsClosedImmersion (baseChangeMap (denseReplacementMap C) g) _
    (denseReplacementMap (C.baseChange g))

@[reassoc (attr := simp)]
theorem denseReplacementBaseChange_comp (C : Compactification f) (g : T ⟶ S) :
    denseReplacementBaseChange C g ≫ baseChangeMap (denseReplacementMap C) g =
      denseReplacementMap (C.baseChange g) :=
  liftOfIsClosedImmersion_comp _ _ _

/-- For a flat base change, the dense replacement commutes with base change. -/
instance isIso_denseReplacementBaseChange (C : Compactification f) (g : T ⟶ S) [Flat g] :
    IsIso (denseReplacementBaseChange C g) := by
  let E : DenseCompactification (pullback.snd f g) :=
    ⟨(denseReplacement C).obj.baseChange g, (denseCompactificationProperty_iff _ _).mpr
      (baseChange_isSchemeTheoreticallyDominant (denseReplacement C).obj g)⟩
  refine ⟨(liftDenseReplacement (E := E) (baseChangeMap (denseReplacementMap C) g)).hom, ?_, ?_⟩
  · rw [← cancel_mono (denseReplacementMap (C.baseChange g))]
    simp
  · rw [← cancel_mono (baseChangeMap (denseReplacementMap C) g)]
    simp

end

end Compactification

end TauCeti
