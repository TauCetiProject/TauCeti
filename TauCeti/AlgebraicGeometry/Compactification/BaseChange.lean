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
maps of compactifications pull back functorially. Scheme-theoretic density of the interior
is preserved when the base change is flat, using Mathlib's
`AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isPullback`.

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

/-- Pull back a compactification along an arbitrary map of bases.
The scheme and arrows remain available for dependent pullback constructions. -/
abbrev baseChange (C : Compactification f) (g : T ⟶ S) :
    Compactification (pullback.snd f g) := by
  let j' : pullback f g ⟶ pullback C.p g :=
    pullback.lift (pullback.fst f g ≫ C.j) (pullback.snd f g)
      (by simp [← pullback.condition])
  have sq : IsPullback (pullback.fst f g) j' C.j (pullback.fst C.p g) := by
    apply IsPullback.of_bot (t := IsPullback.of_hasPullback C.p g)
    · simpa [j'] using (IsPullback.of_hasPullback f g)
    · simp [j']
  have : IsOpenImmersion j' := by
    exact MorphismProperty.of_isPullback sq
      (inferInstance : IsOpenImmersion C.j)
  have : QuasiCompact j' := by
    exact MorphismProperty.of_isPullback sq
      (inferInstance : QuasiCompact C.j)
  exact ofHom j' (pullback.snd C.p g) (pullback.lift_snd _ _ _)

/-- The square relating the original and pulled-back interiors is cartesian. -/
theorem isPullback_baseChange (C : Compactification f) (g : T ⟶ S) :
    IsPullback (pullback.fst f g) (C.baseChange g).j C.j (pullback.fst C.p g) := by
  apply IsPullback.of_bot (t := IsPullback.of_hasPullback C.p g)
  · simpa [baseChange] using (IsPullback.of_hasPullback f g)
  · simp [baseChange]

/-- The projection from the base-changed ambient scheme respects the interior. -/
@[reassoc (attr := simp)]
theorem baseChange_j_fst (C : Compactification f) (g : T ⟶ S) :
    (C.baseChange g).j ≫ pullback.fst C.p g = pullback.fst f g ≫ C.j :=
  pullback.lift_fst _ _ _

/-- Flat base change preserves scheme-theoretic density of the interior. -/
instance baseChange_isSchemeTheoreticallyDominant (C : Compactification f)
    [IsSchemeTheoreticallyDominant C.j] (g : T ⟶ S) [Flat g] :
    IsSchemeTheoreticallyDominant (C.baseChange g).j :=
  IsSchemeTheoreticallyDominant.of_isPullback (C.isPullback_baseChange g)

/-- Pull back a morphism of compactifications. -/
abbrev baseChangeMap {C D : Compactification f} (h : C ⟶ D) (g : T ⟶ S) :
    C.baseChange g ⟶ D.baseChange g :=
  ObjectProperty.homMk
    { h := pullback.map C.p g D.p g h.hom.h (𝟙 T) (𝟙 S)
        (by simp) (by simp)
      ι_h := by
        apply pullback.hom_ext <;> simp [Category.assoc]
      h_π := by simp }

/-- Base change acts functorially on all compactifications of a fixed morphism. -/
@[simps obj map]
abbrev baseChangeFunctor (g : T ⟶ S) :
    Compactification f ⥤ Compactification (pullback.snd f g) where
  obj C := C.baseChange g
  map h := baseChangeMap h g
  map_id C := by
    apply ObjectProperty.hom_ext
    apply Factorisation.Hom.ext
    apply pullback.hom_ext <;> simp
  map_comp h k := by
    apply ObjectProperty.hom_ext
    apply Factorisation.Hom.ext
    apply pullback.hom_ext <;> simp [Category.assoc]


end

end Compactification

namespace DenseCompactification

/-- Flat base change on the full subcategories of dense compactifications. -/
noncomputable def baseChangeFunctor (g : T ⟶ S) [Flat g] :
    DenseCompactification f ⥤ DenseCompactification (pullback.snd f g) :=
  (denseCompactificationProperty (pullback.snd f g)).lift
    ((denseCompactificationProperty f).ι ⋙ Compactification.baseChangeFunctor g)
    (fun C ↦ by
      rw [Functor.comp_obj, ObjectProperty.ι_obj, Compactification.baseChangeFunctor_obj]
      exact (denseCompactificationProperty_iff _ _).mpr inferInstance)

@[simp]
theorem baseChangeFunctor_obj_obj (g : T ⟶ S) [Flat g] (C : DenseCompactification f) :
    ((baseChangeFunctor g).obj C).obj = C.obj.baseChange g :=
  (rfl)

end DenseCompactification

end TauCeti
