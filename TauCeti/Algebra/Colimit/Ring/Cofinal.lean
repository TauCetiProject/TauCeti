/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Colimit.Ring.Basic
public import Mathlib.Order.Cofinal

/-!
# Restriction of directed colimits of rings to cofinal subsets

`Ring.DirectLimit.mapSubtype` is the comparison induced by the stage maps, via
`Ring.DirectLimit.lift`. When the subset is cofinal, `Ring.DirectLimit.ringEquivOfIsCofinal`
identifies the restricted colimit with the full colimit.
-/

public section

namespace Ring.DirectLimit

variable {ι : Type*} [Preorder ι] {G : ι → Type*} [∀ i, CommRing (G i)]
  {f : ∀ i j, i ≤ j → G i →+* G j} {s : Set ι}

/-- The comparison from the colimit over a subset to the full colimit. -/
noncomputable def mapSubtype :
    DirectLimit (fun i : s ↦ G i) (fun i j h ↦ f i j h) →+* DirectLimit G (f · · ·) :=
  lift _ _ _ (fun i ↦ of G (f · · ·) i) fun i j h x ↦
    of_f (G := G) (f := (f · · ·)) (i := i.val) (j := j.val) h x

/-- The comparison on elements represented at a stage in the subset. -/
@[simp]
theorem mapSubtype_of (i : s) (x : G i) :
    mapSubtype (f := f) (s := s) (of (fun j : s ↦ G j) (fun j k h ↦ f j k h) i x) =
      of G (f · · ·) i x := by
  -- This is the defining equation of the comparison, obtained from the colimit lift.
  simp only [mapSubtype, lift_of]

variable [IsDirectedOrder ι] [DirectedSystem G (f · · ·)]

/-- The canonical comparison from a cofinal subsystem is bijective. -/
theorem mapSubtype_bijective_of_isCofinal (hs : IsCofinal s) :
    Function.Bijective (mapSubtype (f := f) (s := s)) := by
  classical
  -- Send each stage to a chosen later stage in the cofinal subset.
  choose k hk hik using hs
  let tailOf := of (fun j : s ↦ G j) (fun j l h ↦ f j l h)
  have htail {a b : s} (hab : a ≤ b) (x : G a) :
      tailOf b (f a b hab x) = tailOf a x :=
    of_f (G := fun j : s ↦ G j) (f := fun j l h ↦ f j l h) hab x
  let g (i : ι) := (tailOf ⟨k i, hk i⟩).comp (f i (k i) (hik i))
  have hg (i j : ι) (hij : i ≤ j) (x : G i) : g j (f i j hij x) = g i x := by
    obtain ⟨m, him, hjm⟩ := exists_ge_ge (k i) (k j)
    let l : s := ⟨k m, hk m⟩
    have hi' : k i ≤ l.val := him.trans (hik m)
    have hj' : k j ≤ l.val := hjm.trans (hik m)
    calc
      g j (f i j hij x) =
          tailOf l (f (k j) l hj' (f j (k j) (hik j) (f i j hij x))) :=
        (htail (a := ⟨k j, hk j⟩) (b := l) hj' _).symm
      _ = tailOf l (f (k i) l hi' (f i (k i) (hik i) x)) := by
        simp only [DirectedSystem.map_map' f]
      _ = g i x := htail (a := ⟨k i, hk i⟩) (b := l) hi' _
  -- The universal property reduces both inverse identities to stage elements.
  let inv := lift G (f · · ·) _ g hg
  have hright : (mapSubtype (f := f) (s := s)).comp inv = RingHom.id _ := by
    apply hom_ext
    intro i
    ext x
    simp only [RingHom.comp_apply, RingHom.id_apply, inv, lift_of, g, tailOf,
      mapSubtype_of, of_f]
  have hleft : inv.comp (mapSubtype (f := f) (s := s)) = RingHom.id _ := by
    apply hom_ext
    intro i
    ext x
    simp only [RingHom.comp_apply, RingHom.id_apply, mapSubtype_of, inv, lift_of, g, tailOf]
    exact htail (a := i) (b := ⟨k i, hk i⟩) (hik i) x
  exact Function.bijective_iff_has_inverse.mpr
    ⟨inv, fun x ↦ congr($hleft x), fun x ↦ congr($hright x)⟩

/-- Restricting the index set to a cofinal subset preserves the directed colimit of rings. -/
noncomputable def ringEquivOfIsCofinal (hs : IsCofinal s) :
    DirectLimit (fun i : s ↦ G i) (fun i j h ↦ f i j h) ≃+* DirectLimit G (f · · ·) :=
  RingEquiv.ofBijective (mapSubtype (s := s)) (mapSubtype_bijective_of_isCofinal hs)

/-- The cofinality isomorphism is induced by the comparison of colimits. -/
@[simp]
theorem coe_ringEquivOfIsCofinal (hs : IsCofinal s) :
    (ringEquivOfIsCofinal (f := f) hs :
      DirectLimit (fun i : s ↦ G i) (fun i j h ↦ f i j h) →+* DirectLimit G (f · · ·)) =
        mapSubtype (s := s) :=
  (rfl)

/-- The cofinality isomorphism preserves the canonical images of the retained stages. -/
@[simp]
theorem ringEquivOfIsCofinal_apply_of (hs : IsCofinal s) (i : s) (x : G i) :
    ringEquivOfIsCofinal (f := f) hs (of (fun j : s ↦ G j) (fun j k h ↦ f j k h) i x) =
      of G (f · · ·) i x := by
  have h := DFunLike.congr_fun (coe_ringEquivOfIsCofinal (f := f) hs)
    (of (fun j : s ↦ G j) (fun j k h ↦ f j k h) i x)
  simpa only [RingEquiv.coe_toRingHom] using h.trans (mapSubtype_of i x)

end Ring.DirectLimit
