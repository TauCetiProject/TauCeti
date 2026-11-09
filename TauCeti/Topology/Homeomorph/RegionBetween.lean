/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Order.RegionBetween

/-!
# Homeomorphisms of closed bands

Affine interpolation lifts a homeomorphism of bases to a homeomorphism of closed bands
when their collapse loci match. No compactness or strict endpoint separation is required.
In particular, the construction applies to bands over closed simplices whose widths vanish
on some faces. Bases can themselves be subspaces, so continuity is only required on the
actual base.

The underlying map is `TauCeti.regionBetweenMap`. Its continuity at collapsed fibres and
its inverse, identity and composition laws are supplied by the closed-band calculus.
Here we bundle the result as `Homeomorph.closedRegionBetween` and prove its functorial laws.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Ann. Scuola Norm. Sup. Pisa (3)
  **18** (1964), 449–474, §2, Lemmas 12 and 14.
-/

public section

open Set

namespace Homeomorph

open TauCeti

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A homeomorphism of bases lifts by affine interpolation to their closed bands if the
continuous endpoints are ordered and the collapse loci match. The inverse is interpolation
over the inverse base homeomorphism with the endpoint pairs exchanged. -/
noncomputable def closedRegionBetween (e : X ≃ₜ Y) (a b : X → ℝ) (c d : Y → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hd : Continuous d)
    (hab : ∀ x, a x ≤ b x) (hcd : ∀ y, c y ≤ d y)
    (hcollapse : ∀ x, a x = b x ↔ c (e x) = d (e x)) :
    TauCeti.closedRegionBetween a b univ ≃ₜ TauCeti.closedRegionBetween c d univ where
  toFun p := ⟨regionBetweenMap e a b c d p,
    mapsTo_regionBetweenMap_closedRegionBetween (mapsTo_univ _ _)
      (fun y _ ↦ hcd y) p.2⟩
  invFun p := ⟨regionBetweenMap e.symm c d a b p,
    mapsTo_regionBetweenMap_closedRegionBetween (mapsTo_univ _ _)
      (fun x _ ↦ hab x) p.2⟩
  left_inv p := Subtype.ext <| regionBetweenMap_regionBetweenMap (e.symm_apply_apply _)
    (hcollapse _).mpr (mem_closedRegionBetween.mp p.2).2
  right_inv p := Subtype.ext <| regionBetweenMap_regionBetweenMap (e.apply_symm_apply _) (by
    simpa using (hcollapse (e.symm p.1.1)).mp) (mem_closedRegionBetween.mp p.2).2
  continuous_toFun := (continuousOn_regionBetweenMap e.continuous.continuousOn
    ha.continuousOn hb.continuousOn hc.continuousOn hd.continuousOn (mapsTo_univ _ _)
      (fun x _ ↦ (hcollapse x).mp)).domRestrict.codRestrict _
  continuous_invFun := (continuousOn_regionBetweenMap e.symm.continuous.continuousOn
    hc.continuousOn hd.continuousOn ha.continuousOn hb.continuousOn (mapsTo_univ _ _)
      (fun y _ ↦ by simpa using (hcollapse (e.symm y)).mpr)).domRestrict.codRestrict _

variable (e : X ≃ₜ Y) (a b : X → ℝ) (c d : Y → ℝ)
  (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hd : Continuous d)
  (hab : ∀ x, a x ≤ b x) (hcd : ∀ y, c y ≤ d y)
  (hcollapse : ∀ x, a x = b x ↔ c (e x) = d (e x))

/-- The closed-band homeomorphism has the prescribed interpolation map. -/
@[simp]
theorem coe_closedRegionBetween_apply (p : TauCeti.closedRegionBetween a b univ) :
    (e.closedRegionBetween a b c d ha hb hc hd hab hcd hcollapse p : Y × ℝ) =
      regionBetweenMap e a b c d p := (rfl)

/-- Its inverse interpolates over the inverse base map. -/
@[simp]
theorem coe_closedRegionBetween_symm_apply (p : TauCeti.closedRegionBetween c d univ) :
    ((e.closedRegionBetween a b c d ha hb hc hd hab hcd hcollapse).symm p : X × ℝ) =
      regionBetweenMap e.symm c d a b p := (rfl)

/-- Exchanging the bases and endpoints gives the inverse closed-band homeomorphism. -/
theorem closedRegionBetween_symm :
    (e.closedRegionBetween a b c d ha hb hc hd hab hcd hcollapse).symm =
      e.symm.closedRegionBetween c d a b hc hd ha hb hcd hab
        (fun y ↦ by simpa using (hcollapse (e.symm y)).symm) := by
  apply Homeomorph.ext
  intro p
  apply Subtype.ext
  rw [coe_closedRegionBetween_apply, coe_closedRegionBetween_symm_apply]

/-- Identity base and endpoint data give the identity on the closed band. -/
@[simp]
theorem closedRegionBetween_refl :
    (Homeomorph.refl X).closedRegionBetween a b a b ha hb ha hb hab hab (fun _ ↦ by simp) =
      Homeomorph.refl (TauCeti.closedRegionBetween a b univ) := by
  apply Homeomorph.ext
  intro p
  apply Subtype.ext
  simpa only [coe_closedRegionBetween_apply, Homeomorph.coe_refl, Homeomorph.refl_apply,
    id_eq] using
    regionBetweenMap_id (mem_closedRegionBetween.mp p.2).2

/-- Closed-band transfer commutes with composition of the base homeomorphisms. -/
theorem closedRegionBetween_trans (f : Y ≃ₜ Z) (u v : Z → ℝ)
    (hu : Continuous u) (hv : Continuous v) (huv : ∀ z, u z ≤ v z)
    (hcollapse' : ∀ y, c y = d y ↔ u (f y) = v (f y)) :
    (e.closedRegionBetween a b c d ha hb hc hd hab hcd hcollapse).trans
        (f.closedRegionBetween c d u v hc hd hu hv hcd huv hcollapse') =
      (e.trans f).closedRegionBetween a b u v ha hb hu hv hab huv
        (fun x ↦ (hcollapse x).trans (hcollapse' (e x))) := by
  apply Homeomorph.ext
  intro p
  apply Subtype.ext
  simp only [Homeomorph.trans_apply, coe_closedRegionBetween_apply]
  exact regionBetweenMap_comp e f a b c d u v p (hcollapse' _).mp

end Homeomorph
