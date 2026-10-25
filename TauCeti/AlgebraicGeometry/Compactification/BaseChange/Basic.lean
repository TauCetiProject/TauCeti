/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Compactification.Basic

/-!
# Base change of scheme compactifications

Pulling back both maps of a compactification gives a compactification over any new base.
The induced map on interiors is itself a pullback of the original open immersion, and
maps of compactifications pull back functorially, as pullbacks of the original maps of ambient
schemes; in particular closed immersions of compactifications pull back to closed immersions.
Scheme-theoretic density of the interior is preserved when the base change is flat, using
Mathlib's `AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isPullback`.

## References

* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT).
-/

public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace TauCeti

variable {X S T : Scheme.{u}} {f : X ⟶ S}

namespace Compactification

noncomputable section

/-- The open interior map induced on the pullbacks of a compactification. -/
private def baseChangeJ (C : Compactification f) (g : T ⟶ S) :
    pullback f g ⟶ pullback C.p g :=
  pullback.lift (pullback.fst f g ≫ C.j) (pullback.snd f g)
    (by simp [← pullback.condition])

@[reassoc (attr := simp)]
private theorem baseChangeJ_fst (C : Compactification f) (g : T ⟶ S) :
    baseChangeJ C g ≫ pullback.fst C.p g = pullback.fst f g ≫ C.j :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem baseChangeJ_snd (C : Compactification f) (g : T ⟶ S) :
    baseChangeJ C g ≫ pullback.snd C.p g = pullback.snd f g :=
  pullback.lift_snd _ _ _

private theorem isPullback_baseChangeJ (C : Compactification f) (g : T ⟶ S) :
    IsPullback (pullback.fst f g) (baseChangeJ C g) C.j (pullback.fst C.p g) := by
  apply IsPullback.of_bot (t := IsPullback.of_hasPullback C.p g)
  · simpa using (IsPullback.of_hasPullback f g)
  · simp

private instance (C : Compactification f) (g : T ⟶ S) :
    IsOpenImmersion (baseChangeJ C g) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeJ C g)
    (inferInstance : IsOpenImmersion C.j)

private instance (C : Compactification f) (g : T ⟶ S) :
    QuasiCompact (baseChangeJ C g) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeJ C g)
    (inferInstance : QuasiCompact C.j)

/-- Pull back a compactification along an arbitrary map of bases.
The compactification of `pullback.snd f g` has ambient scheme `pullback C.p g`,
open immersion induced by `pullback.lift`, and proper map `pullback.snd C.p g`. -/
-- Exposure and implicit reducibility keep dependent projection formulas usable across modules.
-- Keep the exposed data explicit; only proof blocks can refer to the private helpers.
@[expose, implicit_reducible] def baseChange (C : Compactification f) (g : T ⟶ S) :
    Compactification (pullback.snd f g) :=
  @ofHom _ _ _ _ (pullback.lift (pullback.fst f g ≫ C.j) (pullback.snd f g)
    (by simp [← pullback.condition])) (pullback.snd C.p g)
    (by exact inferInstanceAs (IsOpenImmersion (baseChangeJ C g)))
    (by exact inferInstanceAs (QuasiCompact (baseChangeJ C g))) inferInstance
    (by exact baseChangeJ_snd C g)

@[simp]
theorem baseChange_Xbar (C : Compactification f) (g : T ⟶ S) :
    (C.baseChange g).Xbar = pullback C.p g :=
  (rfl)

@[simp]
theorem baseChange_p (C : Compactification f) (g : T ⟶ S) :
    (C.baseChange g).p = pullback.snd C.p g :=
  (rfl)

/-- The projection from the base-changed ambient scheme respects the interior. -/
@[reassoc (attr := simp)]
theorem baseChange_j_fst (C : Compactification f) (g : T ⟶ S) :
    (C.baseChange g).j ≫ pullback.fst C.p g = pullback.fst f g ≫ C.j :=
  baseChangeJ_fst C g

/-- The interior of a base change lies over the new base. -/
@[reassoc (attr := simp)]
theorem baseChange_j_snd (C : Compactification f) (g : T ⟶ S) :
    (C.baseChange g).j ≫ pullback.snd C.p g = pullback.snd f g :=
  baseChangeJ_snd C g

/-- The square relating the original and pulled-back interiors is cartesian. -/
theorem isPullback_baseChange (C : Compactification f) (g : T ⟶ S) :
    IsPullback (pullback.fst f g) (C.baseChange g).j C.j (pullback.fst C.p g) :=
  isPullback_baseChangeJ C g

/-- Flat base change preserves scheme-theoretic density of the interior. -/
instance baseChange_isSchemeTheoreticallyDominant (C : Compactification f)
    [IsSchemeTheoreticallyDominant C.j] (g : T ⟶ S) [Flat g] :
    IsSchemeTheoreticallyDominant (C.baseChange g).j :=
  IsSchemeTheoreticallyDominant.of_isPullback (C.isPullback_baseChange g)

/-- Pull back a morphism of compactifications. -/
def baseChangeMap {C D : Compactification f} (h : C ⟶ D) (g : T ⟶ S) :
    C.baseChange g ⟶ D.baseChange g :=
  ObjectProperty.homMk
    { h := pullback.map C.p g D.p g h.hom.h (𝟙 T) (𝟙 S)
        (by simp) (by simp)
      ι_h := by
        apply pullback.hom_ext <;> simp [Category.assoc]
      h_π := by simp }

@[simp]
theorem baseChangeMap_hom_h {C D : Compactification f} (h : C ⟶ D) (g : T ⟶ S) :
    (baseChangeMap h g).hom.h =
      pullback.map C.p g D.p g h.hom.h (𝟙 T) (𝟙 S) (by simp) (by simp) :=
  (rfl)

/-- The pulled-back map of ambient schemes is a pullback of the original map. -/
theorem isPullback_baseChangeMap {C D : Compactification f} (h : C ⟶ D) (g : T ⟶ S) :
    IsPullback (pullback.fst C.p g) (baseChangeMap h g).hom.h h.hom.h (pullback.fst D.p g) := by
  apply IsPullback.of_bot (t := IsPullback.of_hasPullback D.p g)
  · simpa using IsPullback.of_hasPullback C.p g
  · simp

/-- Base change preserves closed immersions of compactifications. -/
instance {C D : Compactification f} (h : C ⟶ D) [IsClosedImmersion h.hom.h] (g : T ⟶ S) :
    IsClosedImmersion (baseChangeMap h g).hom.h :=
  MorphismProperty.of_isPullback (isPullback_baseChangeMap h g)
    (inferInstance : IsClosedImmersion h.hom.h)

/-- Base change acts functorially on all compactifications of a fixed morphism. -/
-- The object equations must remain available when elaborating dependent morphism formulas.
@[expose, implicit_reducible, simps obj map]
def baseChangeFunctor (g : T ⟶ S) :
    Compactification f ⥤ Compactification (pullback.snd f g) where
  obj C := C.baseChange g
  map h := baseChangeMap h g
  map_id C := by
    apply ObjectProperty.hom_ext
    apply Factorisation.Hom.ext
    -- Normalize the identity map's dependent endpoint before categorical simplification.
    dsimp only [baseChange, ofHom]
    apply pullback.hom_ext <;> simp
  map_comp h k := by
    apply ObjectProperty.hom_ext
    apply Factorisation.Hom.ext
    apply pullback.hom_ext <;> simp [Category.assoc]


end

end Compactification

namespace DenseCompactification

/-- Flat base change on the full subcategories of dense compactifications. -/
-- The underlying morphism formula needs definitionally matching endpoints under `simp`.
@[expose, implicit_reducible] noncomputable def baseChangeFunctor (g : T ⟶ S) [Flat g] :
    DenseCompactification f ⥤ DenseCompactification (pullback.snd f g) :=
  (denseCompactificationProperty (pullback.snd f g)).lift
    ((denseCompactificationProperty f).ι ⋙ Compactification.baseChangeFunctor g)
    (fun C ↦ (denseCompactificationProperty_iff _ _).mpr
      (Compactification.baseChange_isSchemeTheoreticallyDominant C.obj g))

@[simp]
theorem baseChangeFunctor_obj_obj (g : T ⟶ S) [Flat g] (C : DenseCompactification f) :
    ((baseChangeFunctor g).obj C).obj = C.obj.baseChange g :=
  (rfl)

@[simp]
theorem baseChangeFunctor_map_hom (g : T ⟶ S) [Flat g]
    {C D : DenseCompactification f} (h : C ⟶ D) :
    ((baseChangeFunctor g).map h).hom = Compactification.baseChangeMap h.hom g :=
  (rfl)

end DenseCompactification

end TauCeti
