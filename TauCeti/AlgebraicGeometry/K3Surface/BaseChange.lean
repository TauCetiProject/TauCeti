/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.K3Surface.Basic
import TauCeti.AlgebraicGeometry.Cohomology.FlatBaseChange

/-!
# Base change of K3 surfaces

A K3 surface remains a K3 surface after any field extension, including a purely inseparable
extension. The statement accepts an arbitrary cartesian square, so it applies directly to a
caller's scheme and structure morphism. It also specializes to the canonical pullback and to
invariance under an isomorphism over the ground field.

The triviality of the canonical sheaf is transported by base change of differential forms.
The vanishing of the first structure-sheaf cohomology follows from flat cohomology base change.

## References

* D. Huybrechts, *Lectures on K3 Surfaces*, Chapter 17, Section 2.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

namespace IsK3

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {X Y : Scheme.{u}} {f : X ⟶ Spec (.of k)} {f' : Y ⟶ Spec (.of K)} {g : Y ⟶ X}

/-- A K3 surface remains a K3 surface after any field extension. The extension need not be
separable, and the cartesian square may use any chosen model of the base change. -/
theorem baseChange (h : IsK3 k f)
    (H : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) : IsK3 K f' := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  let : Y.Over (Spec (.of K)) := ⟨f'⟩
  have := h.isProper
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  refine ⟨MorphismProperty.of_isPullback H h.smoothOfRelativeDimension,
    MorphismProperty.of_isPullback H h.isProper,
    MorphismProperty.of_isPullback H h.geometricallyIntegral, ?_, ?_⟩
  · obtain ⟨e⟩ := h.nonempty_differentialFormsIso
    exact ⟨(differentialFormsBaseChangeIso H 2).symm ≪≫
      (Scheme.Modules.pullback g).mapIso e ≪≫ Scheme.Modules.pullbackObjUnitIso g⟩
  · have := h.subsingleton_cohomology_one
    exact ((cohomologyBaseChangeLinearEquiv (R := k) (R' := K) H
      (SheafOfModules.unit X.ringCatSheaf) 1).trans
      (Scheme.Modules.cohomologyBaseLinearEquivOfIso K
        (Scheme.Modules.pullbackObjUnitIso g) 1)).surjective.subsingleton

/-- The canonical scheme-theoretic pullback of a K3 surface along a field extension is K3. -/
theorem pullback (h : IsK3 k f) :
    IsK3 K (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
  h.baseChange (IsPullback.of_hasPullback _ _)

/-- An isomorphism over the ground field transports the K3 property. -/
theorem of_iso (h : IsK3 k f) {f' : Y ⟶ Spec (.of k)} (e : Y ≅ X)
    (w : e.hom ≫ f = f') : IsK3 k f' := by
  apply h.baseChange (K := k) (g := e.hom)
  have hb : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (.of k)) := by simp
  rw [hb]
  exact IsPullback.of_horiz_isIso ⟨by simpa using w⟩

/-- The K3 property is invariant under an isomorphism over the ground field. -/
theorem iso_iff {f' : Y ⟶ Spec (.of k)} (e : Y ≅ X) (w : e.hom ≫ f = f') :
    IsK3 k f ↔ IsK3 k f' := by
  refine ⟨fun h ↦ h.of_iso e w, fun h ↦ h.of_iso e.symm ?_⟩
  simp [← w]

end IsK3

end TauCeti.AlgebraicGeometry
