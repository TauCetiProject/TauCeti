/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.PartialEquiv

/-!
# Image transport for compositions and restrictions of partial equivalences

This file supplements `PartialEquiv.image_source_inter_eq'` and `PartialEquiv.image_trans_source` in
`Mathlib.Logic.Equiv.PartialEquiv` with equational formulas for source-restricted images under
compositions `e.trans e'`, source restrictions `e.restr u`, and coordinate transitions
`e.symm.trans e'` (with or without restriction to a subset `u` of the intermediate space).

## Main declarations

* `PartialEquiv.image_trans_source_inter`: `(e.trans e') '' ((e.trans e').source ∩ s) =
  e' '' (e'.source ∩ e '' (e.source ∩ s))`.
* `PartialEquiv.image_restr_source_inter`: `(e.restr u) '' ((e.restr u).source ∩ s) =
  (e.restr u).target ∩ e '' (e.source ∩ s)`.
* `PartialEquiv.image_symm_trans_source_inter` and
  `PartialEquiv.image_restr_symm_trans_source_inter`: transport of `e '' (e.source ∩ s)` onto
  `e' '' (e'.source ∩ s)` intersected with the transition target.
-/

public section

namespace PartialEquiv

variable {α β γ : Type*}

/-- Pushing a set forward along a composition `e.trans e'` of partial equivalences pushes its
`e`-source trace through `e` and then its `e'`-source trace through `e'`. -/
theorem image_trans_source_inter (e : PartialEquiv α β) (e' : PartialEquiv β γ) (s : Set α) :
    (e.trans e') '' ((e.trans e').source ∩ s) = e' '' (e'.source ∩ e '' (e.source ∩ s)) := by
  rw [(e.trans e').image_source_inter_eq', e'.image_source_inter_eq', e.image_source_inter_eq',
    trans_target, coe_trans_symm, Set.preimage_comp, Set.preimage_inter, Set.inter_assoc]

/-- Restricting a partial equivalence to `u` intersects source-restricted images with the
restricted target. -/
theorem image_restr_source_inter (e : PartialEquiv α β) (u s : Set α) :
    (e.restr u) '' ((e.restr u).source ∩ s) = (e.restr u).target ∩ e '' (e.source ∩ s) := by
  rw [(e.restr u).image_source_inter_eq', e.image_source_inter_eq', restr_target, restr_coe_symm,
    ← Set.inter_inter_distrib_left, Set.inter_assoc]

/-- A transition partial equivalence `e.symm.trans e'` transports the `e`-image of `s` onto the part
of the `e'`-image of `s` lying in `(e.symm.trans e').target`. -/
theorem image_symm_trans_source_inter (e : PartialEquiv α β) (e' : PartialEquiv α γ) (s : Set α) :
    (e.symm.trans e') '' ((e.symm.trans e').source ∩ e '' (e.source ∩ s)) =
      (e.symm.trans e').target ∩ e' '' (e'.source ∩ s) := by
  have hsub : e '' (e.source ∩ s) ⊆ e.target :=
    e.image_source_inter_eq' s ▸ Set.inter_subset_left
  rw [e.symm.image_trans_source_inter e', symm_source, Set.inter_eq_self_of_subset_right hsub,
    e.symm_image_image_of_subset_source Set.inter_subset_left, e'.image_source_inter_eq',
    e'.image_source_inter_eq', trans_target, symm_target, Set.preimage_inter,
    Set.inter_inter_distrib_left]

/-- Restricting a transition partial equivalence `e.symm.trans e'` to `u ⊆ β` transports the
`e`-image of `s` onto the part of the `e'`-image of `s` lying in
`((e.symm.trans e').restr u).target`. -/
theorem image_restr_symm_trans_source_inter (e : PartialEquiv α β) (e' : PartialEquiv α γ)
    (u : Set β) (s : Set α) :
    ((e.symm.trans e').restr u) ''
        (((e.symm.trans e').restr u).source ∩ e '' (e.source ∩ s)) =
      ((e.symm.trans e').restr u).target ∩ e' '' (e'.source ∩ s) := by
  have hsub : ((e.symm.trans e').restr u).target ⊆ (e.symm.trans e').target :=
    Set.inter_subset_left
  rw [(e.symm.trans e').image_restr_source_inter u, e.image_symm_trans_source_inter e',
    ← Set.inter_assoc, Set.inter_eq_self_of_subset_left hsub]

end PartialEquiv
