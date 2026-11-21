/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.ULift
import TauCeti.GroupTheory.CoprodI
import TauCeti.GroupTheory.CoprodI.Centralizer
import TauCeti.GroupTheory.Subgroup.Centralizer

/-!
# Centralizers of factor elements in a free product of two groups

In the free product `G ∗ H` of two groups, the centralizer of a nontrivial element `g` of `G` is
the centralizer of `g` in `G`, and likewise for `H`. This is the case of a family indexed by `Bool`
of the description of the centralizers of factor elements of a free product
(`Monoid.CoprodI.centralizer_of_eq_map`).

## Main results

* `Monoid.Coprod.centralizer_inl_eq_map`: the centralizer of `inl g`, for `g ≠ 1`, is the image
  of the centralizer of `g` in `G`.
* `Monoid.Coprod.centralizer_inr_eq_map`: the centralizer of `inr h`, for `h ≠ 1`, is the image
  of the centralizer of `h` in `H`.

## References

* R. C. Lyndon, P. E. Schupp, *Combinatorial group theory*, Springer (1977), Chapter IV, §1
  (the normal form theorem for free products).
-/

public section

open Subgroup

universe u v

namespace Monoid.Coprod

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- **Centralizers of elements of the first factor of a free product.** The centralizer in `G ∗ H`
of a nontrivial `g ∈ G` is the centralizer of `g` in `G`. -/
theorem centralizer_inl_eq_map {g : G} (hg : g ≠ 1) :
    centralizer {(inl g : G ∗ H)} = (centralizer {g}).map inl := by
  -- `G ∗ H` is the free product of the family `ULift G`, `ULift H` indexed by `Bool`.
  let _ : ∀ b, Group (cond b (ULift.{u} H) (ULift.{v} G))
    | false => inferInstanceAs (Group (ULift G))
    | true => inferInstanceAs (Group (ULift H))
  let e : CoprodI (fun b => cond b (ULift.{u} H) (ULift.{v} G)) ≃* G ∗ H :=
    (CoprodI.boolEquivCoprod _).trans (MulEquiv.coprodCongr MulEquiv.ulift MulEquiv.ulift)
  have he : (e : _ →* G ∗ H).comp
      (CoprodI.of (M := fun b => cond b (ULift.{u} H) (ULift.{v} G)) (i := false)) =
      inl.comp ((MulEquiv.ulift : ULift.{v} G ≃* G) : ULift.{v} G →* G) := by
    ext
    simp [e]
  have hc := congrArg (Subgroup.map (e : _ →* G ∗ H))
    (CoprodI.centralizer_of_eq_map (G := fun b => cond b (ULift.{u} H) (ULift.{v} G))
      (i := false) (g := ULift.up.{v} g) fun h => hg (congrArg ULift.down h))
  rw [MulEquiv.map_centralizer, Set.image_singleton, Subgroup.map_map, he, ← Subgroup.map_map,
    MulEquiv.map_centralizer, Set.image_singleton] at hc
  simp only [e, MulEquiv.trans_apply, CoprodI.boolEquivCoprod_of_false,
    MulEquiv.coprodCongr_apply, map_apply_inl] at hc
  -- `MulEquiv.ulift` sends `ULift.up g` to `g`.
  exact hc

/-- **Centralizers of elements of the second factor of a free product.** The centralizer in
`G ∗ H` of a nontrivial `h ∈ H` is the centralizer of `h` in `H`. -/
theorem centralizer_inr_eq_map {h : H} (hh : h ≠ 1) :
    centralizer {(inr h : G ∗ H)} = (centralizer {h}).map inr := by
  have he : ((MulEquiv.coprodComm H G : H ∗ G →* G ∗ H)).comp inl = inr := by
    ext
    simp
  rw [← he, MonoidHom.comp_apply, ← Subgroup.map_map, ← centralizer_inl_eq_map hh,
    MulEquiv.map_centralizer, Set.image_singleton]
  rfl

end Monoid.Coprod
