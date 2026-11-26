/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import TauCeti.AlgebraicGeometry.IdealSheaf.Module

/-!
# Sections of an ideal sheaf along an open immersion

The section ring isomorphism for an open immersion identifies the ideal sections over an open
in the source with the ideal sections over its image. This extends the affine-open formula
`Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion` to arbitrary opens.
-/

public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The section isomorphisms of an open immersion commute with restriction of sections. -/
theorem appIso_hom_naturality_apply {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {U V : X.Opens} (i : V ⟶ U) (s : Γ(Y, f ''ᵁ U)) :
    (f.appIso V).hom (Y.presheaf.map (f.opensFunctor.map i).op s) =
      X.presheaf.map i.op ((f.appIso U).hom s) := by
  simpa only [CommRingCat.comp_apply, Quiver.Hom.unop_op] using
    congrArg (fun g : Γ(Y, f ''ᵁ U) ⟶ Γ(X, V) ↦ g s) (f.appIso_hom_naturality i.op)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- A section on the image of an open immersion lies in the ideal if and only if its pullback
lies in the pulled-back ideal. -/
theorem appIso_hom_mem_sections_comap_iff {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (f : X ⟶ Y) [IsOpenImmersion f] {U : X.Opens} (s : Γ(Y, f ''ᵁ U)) :
    (f.appIso U).hom s ∈ (I.comap f).sections U ↔ s ∈ I.sections (f ''ᵁ U) := by
  have ha (V : X.affineOpens) (s : Γ(Y, f ''ᵁ V.val)) :
      (f.appIso V.val).hom s ∈ (I.comap f).sections V.val ↔
        s ∈ I.sections (f ''ᵁ V.val) := by
    let W : Y.affineOpens := ⟨f ''ᵁ V.val, V.property.image_of_isOpenImmersion f⟩
    rw [sections_eq_ideal, ideal_comap_of_isOpenImmersion, ← I.sections_eq_ideal W]
    simp only [Ideal.mem_comap, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
    -- The underlying open of the affine open `W` is `f ''ᵁ V.val`.
    rfl
  constructor
  · intro hs
    apply I.mem_sections_of_forall_exists
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
    let i : V ⟶ U := homOfLE hVU
    refine ⟨f ''ᵁ V, f.opensFunctor.map i, ⟨x, hxV, rfl⟩, (ha ⟨V, hV⟩ _).mp ?_⟩
    rw [f.appIso_hom_naturality_apply]
    exact (I.comap f).map_mem_sections i hs
  · intro hs
    apply mem_sections_of_forall_affineOpens
    intro V i
    rw [← sections_eq_ideal, ← f.appIso_hom_naturality_apply]
    exact (ha V _).mpr (I.map_mem_sections (f.opensFunctor.map i) hs)

/-- Pulling back an ideal sheaf along an open immersion identifies its sections on an open
with the original ideal sections on the image open. -/
theorem sections_comap_of_isOpenImmersion {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Opens) :
    (I.comap f).sections U = (I.sections (f ''ᵁ U)).map (f.appIso U).hom.hom := by
  rw [← Iso.commRingCatIsoToRingEquiv_toRingHom, Ideal.map_comap_of_equiv]
  ext t
  obtain ⟨s, rfl⟩ := (f.appIso U).commRingCatIsoToRingEquiv.surjective t
  rw [Ideal.mem_comap, RingEquiv.symm_apply_apply, ← RingEquiv.coe_toRingHom,
    Iso.commRingCatIsoToRingEquiv_toRingHom]
  exact I.appIso_hom_mem_sections_comap_iff f s

end AlgebraicGeometry.Scheme.IdealSheafData
