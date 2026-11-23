/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import TauCeti.AlgebraicGeometry.Scheme.Opens

import Mathlib.Tactic.Observe

/-!
# Zariski locality of finite morphisms

Finite morphisms are local on the target. The cover restriction theorem is kept with the
finite-morphism infrastructure so it can be used by geometric limit arguments and other
consumers independently of any particular descent presentation.
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism finite over every member of an open cover is finite over the covered open. -/
theorem isFinite_morphismRestrict_of_cover
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    {B : Type*} (U : B → Y.Opens)
    (hcover : V ≤ ⨆ b, U b) (hfin : ∀ b, IsFinite (f ∣_ U b)) :
    IsFinite (f ∣_ V) := by
  observe hFinite : HasAffineProperty (@IsFinite : MorphismProperty Scheme.{u})
    (fun X _ f _ ↦ IsAffine X ∧ RingHom.Finite (f.appTop).hom)
  have : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ hFinite
  have : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite)
    (fun b ↦ V.ι ⁻¹ᵁ U b)
  · apply top_unique
    intro x _
    obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover x.property)
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨b, ?_⟩
    -- Membership in the preimage open is membership of the original point.
    change x.val ∈ U b
    exact hb
  · intro b
    apply (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
      (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U b))).mpr
    have H := IsZariskiLocalAtTarget.restrict (P := @IsFinite) (hfin b)
      ((U b).ι ⁻¹ᵁ V)
    have H' := (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
      (morphismRestrictRestrict f (U b) ((U b).ι ⁻¹ᵁ V))).mp H
    have he : (U b).ι ''ᵁ ((U b).ι ⁻¹ᵁ V) = V.ι ''ᵁ (V.ι ⁻¹ᵁ U b) := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, inf_comm]
    rw [he] at H'
    exact H'

end AlgebraicGeometry.Scheme.Hom
