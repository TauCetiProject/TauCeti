/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Colimit.Ring
import Mathlib.CategoryTheory.Filtered.Final
import TauCeti.Algebra.Category.Ring.DirectLimit

/-!
# Restriction of directed colimits of rings to cofinal subsets

`TauCeti.Ring.DirectLimit.mapSubtype` compares the colimit over any subset with the full colimit
and preserves the canonical maps from the retained stages. For a cofinal subset of a directed
system, `TauCeti.Ring.DirectLimit.ringEquivOfIsCofinal` identifies the two colimits by Mathlib's
`Functor.Final.isColimitWhiskerEquiv`.
-/

public section

namespace TauCeti.Ring.DirectLimit

open _root_.Ring.DirectLimit CategoryTheory CategoryTheory.Limits

variable {ι : Type*} [Preorder ι] {G : ι → Type*} [∀ i, CommRing (G i)]
  {f : ∀ i j, i ≤ j → G i →+* G j} {s : Set ι}

/-- The comparison from the colimit over a subset to the full colimit. -/
noncomputable def mapSubtype :
    RingHom (_root_.Ring.DirectLimit (fun i : s ↦ G i) (fun i j h ↦ f i j h))
      (_root_.Ring.DirectLimit G (f · · ·)) :=
  lift _ _ _ (fun i ↦ of G (f · · ·) i) fun i j h x ↦
    of_f (G := G) (f := (f · · ·)) (i := i.val) (j := j.val) h x

/-- The comparison on elements represented at a stage in the subset. -/
@[simp]
theorem mapSubtype_of (i : s) (x : G i) :
    mapSubtype (f := f) (s := s) (of (fun j : s ↦ G j) (fun j k h ↦ f j k h) i x) =
      of G (f · · ·) i x := by
  exact lift_of _ (fun j : s ↦ of G (f · · ·) j) _ i x

/-- The comparison commutes with the bundled stage maps. -/
@[simp]
theorem mapSubtype_comp_of (i : s) :
    (mapSubtype (f := f) (s := s)).comp (of (fun j : s ↦ G j) (fun j k h ↦ f j k h) i) =
      of G (f · · ·) i :=
  RingHom.ext fun x ↦ (RingHom.comp_apply ..).trans (mapSubtype_of i x)

variable [IsDirectedOrder ι] [DirectedSystem G (f · · ·)]

/-- The canonical comparison from a cofinal subsystem is an isomorphism in `CommRingCat`. -/
theorem isIso_ofHom_mapSubtype_of_isCofinal (hs : IsCofinal s) :
    IsIso (CommRingCat.ofHom (mapSubtype (f := f) (s := s))) := by
  let ιs := (OrderEmbedding.subtype (· ∈ s)).monotone.functor
  have : ιs.Final := Functor.final_of_exists_of_isFiltered_of_fullyFaithful ιs fun i ↦ by
    obtain ⟨j, hjs, hij⟩ := hs i
    exact ⟨⟨j, hjs⟩, ⟨homOfLE hij⟩⟩
  let C := (cocone f).whisker ιs
  have : DirectedSystem (fun i : s ↦ G i) (fun i j h ↦ f i j h) :=
    ⟨fun i x ↦ DirectedSystem.map_self' (i := i.val) f x,
      fun _ _ _ hij hjk x ↦ DirectedSystem.map_map' f hij hjk x⟩
  let D := cocone (G := fun i : s ↦ G i) (fun i j h ↦ f i j h)
  have hC : IsColimit C :=
    (Functor.Final.isColimitWhiskerEquiv ιs (cocone f)).symm (isColimitCocone f)
  have hD : IsColimit D := isColimitCocone _
  let e := hD.coconePointUniqueUpToIso hC
  have he : e.hom = CommRingCat.ofHom (mapSubtype (f := f) (s := s)) := by
    apply CommRingCat.hom_ext
    apply _root_.Ring.DirectLimit.hom_ext
    intro i
    apply RingHom.ext
    intro x
    have hi := ConcreteCategory.congr_hom
      (hD.comp_coconePointUniqueUpToIso_hom hC i) (ULift.up x)
    exact ((ConcreteCategory.comp_apply (D.ι.app i) e.hom (ULift.up x)).symm.trans hi).trans
      (mapSubtype_of i x).symm
  rw [← he]
  infer_instance

/-- Restricting the index set to a cofinal subset preserves the directed colimit of rings. -/
noncomputable def ringEquivOfIsCofinal (hs : IsCofinal s) :
    _root_.Ring.DirectLimit (fun i : s ↦ G i) (fun i j h ↦ f i j h) ≃+*
      _root_.Ring.DirectLimit G (f · · ·) :=
  letI := isIso_ofHom_mapSubtype_of_isCofinal (f := f) hs
  (asIso (CommRingCat.ofHom (mapSubtype (f := f) (s := s)))).commRingCatIsoToRingEquiv

/-- The cofinality isomorphism is induced by the comparison of colimits. -/
@[simp]
theorem toRingHom_ringEquivOfIsCofinal (hs : IsCofinal s) :
    ↑(ringEquivOfIsCofinal (f := f) hs) = mapSubtype (f := f) (s := s) := by
  -- Read the defining equation of the equivalence on its bundled forward map.
  rw [ringEquivOfIsCofinal, Iso.commRingCatIsoToRingEquiv_toRingHom, asIso_hom,
    CommRingCat.hom_ofHom]

/-- The cofinality isomorphism preserves the canonical images of the retained stages. -/
@[simp]
theorem ringEquivOfIsCofinal_apply_of (hs : IsCofinal s) (i : s) (x : G i) :
    ringEquivOfIsCofinal (f := f) hs (of (fun j : s ↦ G j) (fun j k h ↦ f j k h) i x) =
      of G (f · · ·) i x := by
  have h := DFunLike.congr_fun (toRingHom_ringEquivOfIsCofinal (f := f) hs)
    (of (fun j : s ↦ G j) (fun j k h ↦ f j k h) i x)
  simpa only [RingEquiv.coe_toRingHom] using h.trans (mapSubtype_of i x)

/-- The inverse comparison sends the image of a retained stage to its image in the subsystem. -/
@[simp]
theorem ringEquivOfIsCofinal_symm_apply_of (hs : IsCofinal s) (i : s) (x : G i) :
    (ringEquivOfIsCofinal (f := f) hs).symm (of G (f · · ·) i x) =
      of (fun j : s ↦ G j) (fun j k h ↦ f j k h) i x :=
  (RingEquiv.symm_apply_eq _).mpr (ringEquivOfIsCofinal_apply_of hs i x).symm

/-- The inverse comparison transports a stage element to any retained stage above it. -/
theorem ringEquivOfIsCofinal_symm_apply_of_le (hs : IsCofinal s) {i : ι} (j : s)
    (hij : i ≤ j) (x : G i) :
    (ringEquivOfIsCofinal (f := f) hs).symm (of G (f · · ·) i x) =
      of (fun k : s ↦ G k) (fun k l h ↦ f k l h) j (f i j hij x) := by
  rw [← of_f (G := G) (f := (f · · ·)) hij x, ringEquivOfIsCofinal_symm_apply_of hs j]

end TauCeti.Ring.DirectLimit
