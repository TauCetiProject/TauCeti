/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Centralizers under group homomorphisms

A homomorphism `f : G →* G'` maps the centralizer `C_G(s)` of a subset `s` into the centralizer
`C_{G'}(f(s))`, hence into `C_{G'}(t)` for every `t ⊆ f(s)`. This file records the restriction of
`f` as a homomorphism `C_G(s) →* C_{G'}(t)`; the case `s = {u}`, `t = {f u}` gives a homomorphism
`C_G(u) →* C_{G'}(f u)`. An injective `f` pulls `C_{G'}(f(s))` back to `C_G(s)`, and an
isomorphism `e : G ≃* G'` maps `C_G(s)` onto `C_{G'}(e(s))`, so restricts to an isomorphism
`C_G(s) ≃* C_{G'}(e(s))`; for an inner automorphism this identifies the centralizers of conjugate
elements, `C_G(g⁻¹ x g) = g⁻¹ C_G(x) g`. In pointwise form, an automorphism `e` of `G` gives
`C_G(e • s) = e • C_G(s)`, so conjugate subsets have conjugate centralizers,
`C_G(gsg⁻¹) = g C_G(s) g⁻¹`.

## Main definitions

* `MonoidHom.centralizerMap`: the restriction `C_G(s) →* C_{G'}(t)` of `f : G →* G'`, for
  `t ⊆ f(s)`.
* `MulEquiv.centralizerMap`: the restriction `C_G(s) ≃* C_{G'}(t)` of `e : G ≃* G'`, for
  `t = e(s)`.

## Main results

* `Subgroup.comap_centralizer_image_of_injective`: `f⁻¹(C_{G'}(f(s))) = C_G(s)` for injective `f`.
* `Subgroup.map_center_subtype`: the centre of a subgroup `H ≤ G` embeds into `G` as
  `H ⊓ C_G(H)`.
* `MulEquiv.map_centralizer`: a group isomorphism carries the centralizer of a set onto the
  centralizer of its image.
* `Subgroup.centralizer_pointwise_smul`: `C_G(e • s) = e • C_G(s)` for an automorphism `e` of `G`.
-/

public section

open Subgroup

namespace MonoidHom

variable {G G' : Type*} [Group G] [Group G']

/-- The restriction of `f : G →* G'` to a homomorphism `C_G(s) →* C_{G'}(t)` of centralizers, for
any subset `t` of the image `f(s)`. -/
@[to_additive /-- The restriction of `f : G →+ G'` to a homomorphism of centralizers
`C_G(s) →+ C_{G'}(t)`, for any subset `t` of the image `f(s)`. -/]
def centralizerMap (f : G →* G') {s : Set G} {t : Set G'} (h : t ⊆ f '' s) :
    centralizer s →* centralizer t :=
  (f.comp (centralizer s).subtype).codRestrict _ fun c =>
    centralizer_le h (map_centralizer_le_centralizer_image s f (mem_map_of_mem f c.property))

@[to_additive (attr := simp)]
theorem centralizerMap_apply_coe (f : G →* G') {s : Set G} {t : Set G'} (h : t ⊆ f '' s)
    (c : centralizer s) : (f.centralizerMap h c : G') = f c :=
  (rfl)

@[to_additive]
theorem centralizerMap_injective {f : G →* G'} (hf : Function.Injective f) {s : Set G}
    {t : Set G'} (h : t ⊆ f '' s) : Function.Injective (f.centralizerMap h) :=
  fun _ _ hc => Subtype.ext (hf (congrArg Subtype.val hc))

end MonoidHom

namespace Subgroup

variable {G G' : Type*} [Group G] [Group G']

/-- An injective homomorphism `f : G →* G'` pulls the centralizer `C_{G'}(f(s))` back to
`C_G(s)`. -/
@[to_additive /-- An injective homomorphism `f : G →+ G'` pulls the centralizer `C_{G'}(f(s))`
back to `C_G(s)`. -/]
theorem comap_centralizer_image_of_injective {f : G →* G'} (hf : Function.Injective f)
    (s : Set G) : (centralizer (f '' s)).comap f = centralizer s := by
  ext g
  simp [mem_centralizer_iff, ← map_mul, hf.eq_iff]

/-- The image of the centre of a subgroup `H ≤ G` under `H.subtype` is
`H ⊓ Subgroup.centralizer H`. -/
@[to_additive /-- The image of the centre of an additive subgroup `H ≤ G` under `H.subtype` is
`H ⊓ AddSubgroup.centralizer H`. -/]
theorem map_center_subtype (H : Subgroup G) :
    (Subgroup.center H).map H.subtype = H ⊓ centralizer (H : Set G) := by
  have him : H.subtype '' Set.univ = (H : Set G) := by
    rw [Set.image_univ, ← MonoidHom.coe_range, range_subtype]
  rw [← centralizer_univ, ← comap_centralizer_image_of_injective H.subtype_injective Set.univ, him,
    map_comap_eq, range_subtype]

end Subgroup

namespace MulEquiv

variable {G G' : Type*} [Group G] [Group G']

/-- A group isomorphism carries the centralizer of a set onto the centralizer of its image. -/
@[to_additive /-- An additive group isomorphism carries the centralizer of a set onto the
centralizer of its image. -/]
theorem map_centralizer (e : G ≃* G') (s : Set G) :
    (centralizer s).map (e : G →* G') = centralizer (e '' s) := by
  ext y
  rw [← toMonoidHom_eq_coe, mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff,
    Set.forall_mem_image]
  exact forall₂_congr fun x _ ↦ by rw [← e.injective.eq_iff, map_mul, map_mul, apply_symm_apply]

/-- The restriction of `e : G ≃* G'` to an isomorphism `C_G(s) ≃* C_{G'}(t)` of centralizers, for
`t` the image `e(s)`. -/
@[to_additive /-- The restriction of `e : G ≃+ G'` to an isomorphism of centralizers
`C_G(s) ≃+ C_{G'}(t)`, for `t` the image `e(s)`. -/]
def centralizerMap (e : G ≃* G') {s : Set G} {t : Set G'} (h : e '' s = t) :
    centralizer s ≃* centralizer t :=
  (e.subgroupMap _).trans (.subgroupCongr (h ▸ e.map_centralizer s))

@[to_additive (attr := simp)]
theorem centralizerMap_apply_coe (e : G ≃* G') {s : Set G} {t : Set G'} (h : e '' s = t)
    (c : centralizer s) : (e.centralizerMap h c : G') = e c :=
  (rfl)

@[to_additive (attr := simp)]
theorem centralizerMap_symm_apply_coe (e : G ≃* G') {s : Set G} {t : Set G'} (h : e '' s = t)
    (c : centralizer t) : ((e.centralizerMap h).symm c : G) = e.symm c :=
  (rfl)

end MulEquiv

namespace Subgroup

open scoped Pointwise

variable {G : Type*} [Group G]

/-- An automorphism `e` of `G` carries the centralizer of `s` onto the centralizer of `e • s`,
`C_G(e • s) = e • C_G(s)`; for `e = MulAut.conj g` this is `C_G(gsg⁻¹) = g C_G(s) g⁻¹`. -/
theorem centralizer_pointwise_smul (e : MulAut G) (s : Set G) :
    centralizer (e • s) = e • centralizer s := by
  rw [← Set.image_smul]
  exact (e.map_centralizer s).symm

end Subgroup
