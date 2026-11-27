/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Rel
public import Mathlib.Order.Setoid.Basic

/-!
# Setoid helpers

This file records small generic additions to Mathlib's `Setoid` API.

## Main declarations

* `TauCeti.Setoid.map_of_le_mk`: the quotient map induced by a setoid inequality sends a
  representative to the same representative in the larger quotient.
* `Setoid.ofPred_rel_eq_iff`: two elements have the same class exactly when they are related.
* `Setoid.map_of_le_surjective`: the quotient map induced by a setoid inequality is surjective.
* `Setoid.preimage_image_quotientMk_eq_relPreimage` and `Setoid.preimage_image_quotientMk`: the
  saturation of a set described via `SetRel.preimage` and via the projections of the graph subtype.
* `Setoid.preimage_image_quotientMk_setOfPred_rel`: every equivalence class `{y | r x y}` is
  saturated under `Quotient.mk r`.
* `Quotient.congrRight_mk`, `Quotient.rel_out_congrRight_out`: `Quotient.congrRight` sends the
  class of `a` to the class of `a`, so a representative and the representative of its image are
  related.
-/

public section

namespace TauCeti

namespace Setoid

/-- The quotient map induced by a setoid inequality sends a representative to the same
representative in the larger quotient. -/
@[simp]
lemma map_of_le_mk {α : Type*} {s t : Setoid α} (h : s ≤ t) (x : α) :
    _root_.Setoid.map_of_le h (Quotient.mk'' x : Quotient s) =
      (Quotient.mk'' x : Quotient t) :=
  Quotient.map'_mk'' id h x

end Setoid

end TauCeti

namespace Setoid

/-- Two elements have the same class exactly when they are related. -/
theorem ofPred_rel_eq_iff {α : Type*} {r : Setoid α} {x y : α} :
    {z | r z x} = {z | r z y} ↔ r x y :=
  ⟨fun h => (Set.ext_iff.mp h x).mp (r.refl' x), fun h =>
    Set.ext fun _ => ⟨fun hx => r.trans' hx h, fun hy => r.trans' hy (r.symm' h)⟩⟩

/-- The quotient map induced by a setoid inequality is surjective: every class of the coarser
setoid is the image of the class of any of its representatives. -/
theorem map_of_le_surjective {α : Type*} {s t : Setoid α} (h : s ≤ t) :
    Function.Surjective (map_of_le h) :=
  Quotient.map_surjective _ Function.surjective_id

/-- The saturation `Quotient.mk r ⁻¹' (Quotient.mk r '' s)` of a set `s`, the set of points related
to a point of `s`, is the preimage of `s` under the graph of `r`. -/
theorem preimage_image_quotientMk_eq_relPreimage {α : Type*} (r : Setoid α) (s : Set α) :
    Quotient.mk r ⁻¹' (Quotient.mk r '' s) = SetRel.preimage {p : α × α | r p.1 p.2} s := by
  ext x
  simp only [Set.mem_preimage, Set.mem_image, Quotient.eq, SetRel.mem_preimage, Set.mem_ofPred_eq]
  exact exists_congr fun y ↦ and_congr_right fun _ ↦ ⟨r.symm, r.symm⟩

/-- The saturation `Quotient.mk r ⁻¹' (Quotient.mk r '' s)` of a set `s` is the image under the
second projection of the inverse image of `s` under the first projection of the graph of `r`. -/
theorem preimage_image_quotientMk {α : Type*} (r : Setoid α) (s : Set α) :
    Quotient.mk r ⁻¹' (Quotient.mk r '' s) =
      (fun q : {q : α × α // r q.1 q.2} ↦ q.val.2) ''
        ((fun q : {q : α × α // r q.1 q.2} ↦ q.val.1) ⁻¹' s) := by
  ext x
  constructor
  · rintro ⟨y, hys, hyx⟩
    exact ⟨⟨(y, x), Quotient.exact hyx⟩, hys, rfl⟩
  · rintro ⟨⟨⟨y, _⟩, hyx⟩, hys, rfl⟩
    exact ⟨y, hys, Quotient.sound hyx⟩

/-- Every equivalence class `{y : α | r x y}` is saturated under `Quotient.mk r`. -/
@[simp]
theorem preimage_image_quotientMk_setOfPred_rel {α : Type*} (r : Setoid α) (x : α) :
    Quotient.mk r ⁻¹' (Quotient.mk r '' {y : α | r x y}) = {y : α | r x y} := by
  ext y
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_ofPred_eq, Quotient.eq]
  exact ⟨fun ⟨z, hxz, hzy⟩ ↦ r.trans hxz hzy, fun hxy ↦ ⟨y, hxy, r.refl y⟩⟩

end Setoid

namespace Quotient

variable {α : Type*} {r r' : Setoid α} (e : ∀ a b, r a b ↔ r' a b)

/-- `Quotient.congrRight` sends the class of `a` to the class of `a`. -/
@[simp]
theorem congrRight_mk (a : α) :
    Quotient.congrRight e (Quotient.mk'' a : Quotient r) = (Quotient.mk'' a : Quotient r') :=
  rfl

/-- The representative of a class and the representative of its image under
`Quotient.congrRight` are related by the target relation. -/
theorem rel_out_congrRight_out (q : Quotient r) : r' q.out (Quotient.congrRight e q).out := by
  refine Quotient.exact' ?_
  rw [Quotient.out_eq', ← congrRight_mk e, Quotient.out_eq']

end Quotient
