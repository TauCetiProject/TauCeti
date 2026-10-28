/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Compactification.DenseReplacement
public import TauCeti.AlgebraicGeometry.Compactification.Uniqueness
public import TauCeti.AlgebraicGeometry.Restrict

/-!
# Restricting scheme compactifications over opens of the base

A compactification `X ⟶ Xbar ⟶ S` of `f : X ⟶ S` restricts over an open `U` of `S` to a
compactification of Mathlib's restriction `f ∣_ U : f ⁻¹ᵁ U ⟶ U`. The ambient scheme is the open
subscheme `p ⁻¹ᵁ U` of `Xbar`, the proper map is `p ∣_ U`, and the interior map is the
restriction of `j`. Unlike the base change along the inclusion of `U`, no pullback is formed: the
restricted compactification lives on the open subschemes themselves.

Both squares comparing the restricted and original maps are cartesian, so the restricted interior
is again a quasi-compact open immersion and restriction preserves scheme-theoretic density (an
open immersion is flat). Maps of compactifications restrict functorially, as pullbacks of the
original maps of ambient schemes; in particular closed immersions restrict to closed immersions.
Restriction commutes with dense replacement: the dense replacement of the restriction is
canonically isomorphic to the restriction of the dense replacement.

## Main declarations

* `TauCeti.Compactification.restrict`: the restriction of a compactification over a base open.
* `TauCeti.Compactification.restrictFunctor`: restriction as a functor of compactifications.
* `TauCeti.DenseCompactification.restrictFunctor`: its restriction to dense compactifications.
* `TauCeti.Compactification.denseReplacementRestrictIso`: restriction commutes with dense
  replacement.

## References

* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT).
* The Stacks Project, Section 29.7, *Scheme theoretic closure and density* (tag 01RB).
-/

public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace TauCeti

variable {X S : Scheme.{u}} {f : X ⟶ S} (U : S.Opens)

namespace Compactification

/-- The preimage of a base open under `f` is its preimage under the factorization `j ≫ p`. -/
theorem preimage_eq_j_preimage_p_preimage (C : Compactification f) :
    f ⁻¹ᵁ U = C.j ⁻¹ᵁ C.p ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, C.obj.ι_π]

/-- The preimage of a base open in the source of a map of compactifications is the preimage of
the corresponding open of its target. -/
theorem Hom.p_preimage_eq_h_preimage {C D : Compactification f} (h : C ⟶ D) :
    C.p ⁻¹ᵁ U = h.hom.h ⁻¹ᵁ D.p ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, h.hom.h_π]

noncomputable section

/-- The restriction of the interior map is a pullback of the interior map. -/
private theorem isPullback_restrictJ (C : Compactification f) :
    IsPullback (C.j.resLE (C.p ⁻¹ᵁ U) (f ⁻¹ᵁ U) (C.preimage_eq_j_preimage_p_preimage U).le)
      (f ⁻¹ᵁ U).ι (C.p ⁻¹ᵁ U).ι C.j :=
  C.j.isPullback_resLE_of_eq _ (C.preimage_eq_j_preimage_p_preimage U)

/-- Restrict a compactification of `f` over an open `U` of the base. The compactification of
`f ∣_ U` has ambient scheme `C.p ⁻¹ᵁ U`, interior map the restriction of `C.j`, and proper map
`C.p ∣_ U`. -/
-- Exposure and implicit reducibility keep dependent projection formulas usable across modules.
-- Keep the exposed data explicit; only proof blocks can refer to the private helper.
@[expose, implicit_reducible] def restrict (C : Compactification f) :
    Compactification (f ∣_ U) :=
  @ofHom _ _ _ _ (C.j.resLE (C.p ⁻¹ᵁ U) (f ⁻¹ᵁ U) (C.preimage_eq_j_preimage_p_preimage U).le)
    (C.p ∣_ U)
    (by exact MorphismProperty.of_isPullback (isPullback_restrictJ U C).flip
          (inferInstance : IsOpenImmersion C.j))
    (by exact MorphismProperty.of_isPullback (isPullback_restrictJ U C).flip
          (inferInstance : QuasiCompact C.j))
    inferInstance (by simp [← cancel_mono U.ι])

@[simp]
theorem restrict_Xbar (C : Compactification f) : (C.restrict U).Xbar = C.p ⁻¹ᵁ U :=
  (rfl)

@[simp]
theorem restrict_j (C : Compactification f) :
    (C.restrict U).j =
      C.j.resLE (C.p ⁻¹ᵁ U) (f ⁻¹ᵁ U) (C.preimage_eq_j_preimage_p_preimage U).le :=
  (rfl)

@[simp]
theorem restrict_p (C : Compactification f) : (C.restrict U).p = C.p ∣_ U :=
  (rfl)

/-- The square relating the original and restricted interiors is cartesian. -/
theorem isPullback_restrict_j (C : Compactification f) :
    IsPullback (f ⁻¹ᵁ U).ι (C.restrict U).j C.j (C.p ⁻¹ᵁ U).ι :=
  (isPullback_restrictJ U C).flip

/-- The square relating the original and restricted proper maps is cartesian. -/
theorem isPullback_restrict_p (C : Compactification f) :
    IsPullback (C.p ⁻¹ᵁ U).ι (C.restrict U).p C.p U.ι :=
  (isPullback_morphismRestrict C.p U).flip

/-- Restriction over a base open preserves scheme-theoretic density of the interior. -/
instance restrict_isSchemeTheoreticallyDominant (C : Compactification f)
    [IsSchemeTheoreticallyDominant C.j] : IsSchemeTheoreticallyDominant (C.restrict U).j :=
  IsSchemeTheoreticallyDominant.of_isPullback (C.isPullback_restrict_j U)

/-- Restrict a morphism of compactifications over a base open. -/
def restrictMap {C D : Compactification f} (h : C ⟶ D) : C.restrict U ⟶ D.restrict U :=
  ObjectProperty.homMk
    { h := h.hom.h.resLE (D.p ⁻¹ᵁ U) (C.p ⁻¹ᵁ U) (Hom.p_preimage_eq_h_preimage U h).le
      ι_h := by simp [← cancel_mono (D.p ⁻¹ᵁ U).ι, h.hom.ι_h]
      h_π := by simp [← cancel_mono U.ι] }

@[simp]
theorem restrictMap_hom_h {C D : Compactification f} (h : C ⟶ D) :
    (restrictMap U h).hom.h =
      h.hom.h.resLE (D.p ⁻¹ᵁ U) (C.p ⁻¹ᵁ U) (Hom.p_preimage_eq_h_preimage U h).le :=
  (rfl)

/-- The restricted map of ambient schemes is a pullback of the original map. -/
theorem isPullback_restrictMap {C D : Compactification f} (h : C ⟶ D) :
    IsPullback (C.p ⁻¹ᵁ U).ι (restrictMap U h).hom.h h.hom.h (D.p ⁻¹ᵁ U).ι :=
  (h.hom.h.isPullback_resLE_of_eq _ (Hom.p_preimage_eq_h_preimage U h)).flip

/-- Restriction over a base open preserves closed immersions of compactifications. -/
instance {C D : Compactification f} (h : C ⟶ D) [IsClosedImmersion h.hom.h] :
    IsClosedImmersion (restrictMap U h).hom.h :=
  MorphismProperty.of_isPullback (isPullback_restrictMap U h)
    (inferInstance : IsClosedImmersion h.hom.h)

variable (f) in
/-- Restriction over a base open acts functorially on all compactifications of `f`. -/
-- The object equations must remain available when elaborating dependent morphism formulas.
@[expose, implicit_reducible, simps obj map]
def restrictFunctor : Compactification f ⥤ Compactification (f ∣_ U) where
  obj C := C.restrict U
  map h := restrictMap U h
  map_id C := by
    apply ObjectProperty.hom_ext
    apply Factorisation.Hom.ext
    rw [← cancel_mono (C.p ⁻¹ᵁ U).ι]
    simp
  map_comp {C D E} h k := by
    apply ObjectProperty.hom_ext
    apply Factorisation.Hom.ext
    simp [← cancel_mono (E.p ⁻¹ᵁ U).ι]

end

end Compactification

namespace DenseCompactification

variable (f) in
/-- Restriction over a base open on the full subcategories of dense compactifications. -/
-- The underlying morphism formula needs definitionally matching endpoints under `simp`.
@[expose, implicit_reducible] noncomputable def restrictFunctor :
    DenseCompactification f ⥤ DenseCompactification (f ∣_ U) :=
  (denseCompactificationProperty (f ∣_ U)).lift
    ((denseCompactificationProperty f).ι ⋙ Compactification.restrictFunctor f U)
    (fun C ↦ (denseCompactificationProperty_iff _ _).mpr
      (Compactification.restrict_isSchemeTheoreticallyDominant U C.obj))

@[simp]
theorem restrictFunctor_obj_obj (C : DenseCompactification f) :
    ((restrictFunctor f U).obj C).obj = C.obj.restrict U :=
  (rfl)

@[simp]
theorem restrictFunctor_map_hom {C D : DenseCompactification f} (h : C ⟶ D) :
    ((restrictFunctor f U).map h).hom = Compactification.restrictMap U h.hom :=
  (rfl)

end DenseCompactification

namespace Compactification

noncomputable section

/-- Restriction over a base open commutes with dense replacement: the dense replacement of the
restriction is canonically isomorphic to the restriction of the dense replacement. -/
def denseReplacementRestrictIso (C : Compactification f) :
    denseReplacement (C.restrict U) ≅
      (DenseCompactification.restrictFunctor f U).obj (denseReplacement C) :=
  iso_of_both_ways
    (ObjectProperty.homMk (liftOfIsClosedImmersion (restrictMap U (denseReplacementMap C))
      (denseReplacement (C.restrict U)) (denseReplacementMap (C.restrict U))))
    (liftDenseReplacement (restrictMap U (denseReplacementMap C)))

@[reassoc (attr := simp)]
theorem denseReplacementRestrictIso_hom_hom_comp (C : Compactification f) :
    (denseReplacementRestrictIso U C).hom.hom ≫ restrictMap U (denseReplacementMap C) =
      denseReplacementMap (C.restrict U) :=
  hom_unique _ _

@[reassoc (attr := simp)]
theorem denseReplacementRestrictIso_inv_hom_comp (C : Compactification f) :
    (denseReplacementRestrictIso U C).inv.hom ≫ denseReplacementMap (C.restrict U) =
      restrictMap U (denseReplacementMap C) :=
  hom_unique _ _

end

end Compactification

end TauCeti
