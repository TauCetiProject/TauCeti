/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Homomorphisms and equivalences of centralizers

A homomorphism `f : G →* G'` maps the centralizer `C_G(s)` of a subset `s` into the centralizer
`C_{G'}(f(s))`, hence into `C_{G'}(t)` for every `t ⊆ f(s)`. This file records the restriction of
`f` as a homomorphism `C_G(s) →* C_{G'}(t)`; the case `s = {u}`, `t = {f u}` gives a homomorphism
`C_G(u) →* C_{G'}(f u)`. When `e : G ≃* G'` is a multiplicative equivalence, the image of
`C_G(s)` is `C_{G'}(e(s))`, the preimage of `C_{G'}(t)` is `C_G(e⁻¹(t))`, and `e` restricts to a
multiplicative equivalence `C_G(s) ≃* C_{G'}(t)` whenever `t = e(s)`.

## Main definitions

* `MonoidHom.centralizerMap`: the restriction `C_G(s) →* C_{G'}(t)` of `f : G →* G'`, for
  `t ⊆ f(s)`.
* `MulEquiv.centralizerMap`: the restriction `C_G(s) ≃* C_{G'}(t)` of `e : G ≃* G'`, for
  `t = e(s)`.

## Main results

* `Subgroup.map_centralizer_equiv`: the image of `centralizer s` under `e : G ≃* G'` is
  `centralizer (e '' s)`.
* `Subgroup.comap_centralizer_equiv`: the preimage of `centralizer s` under `e : G ≃* G'` is
  `centralizer (e ⁻¹' s)`.
-/

public section

open Subgroup

namespace Subgroup

variable {G G' : Type*} [Group G] [Group G']

/-- The image of a centralizer under a multiplicative equivalence is the centralizer of the image
set. -/
@[to_additive
/-- The image of a centralizer under an additive equivalence is the centralizer of the image
set. -/]
theorem map_centralizer_equiv (e : G ≃* G') (s : Set G) :
    (centralizer s).map (e : G →* G') = centralizer (e '' s) := by
  refine le_antisymm ?_ ?_
  · simpa using map_centralizer_le_centralizer_image s (e : G →* G')
  · intro y hy
    refine ⟨e.symm y, fun x hx => e.injective ?_, e.apply_symm_apply y⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using hy (e x) (Set.mem_image_of_mem e hx)

/-- The preimage of a centralizer under a multiplicative equivalence is the centralizer of the
preimage set. -/
@[to_additive
/-- The preimage of a centralizer under an additive equivalence is the centralizer of the
preimage set. -/]
theorem comap_centralizer_equiv (e : G ≃* G') (s : Set G') :
    (centralizer s).comap (e : G →* G') = centralizer (e ⁻¹' s) := by
  rw [comap_equiv_eq_map_symm, map_centralizer_equiv]
  congr 1
  exact e.toEquiv.image_symm_eq_preimage s

end Subgroup

namespace MonoidHom

variable {G G' : Type*} [Group G] [Group G']

/-- The restriction of `f : G →* G'` to a homomorphism `C_G(s) →* C_{G'}(t)` of centralizers, for
any subset `t` of the image `f(s)`. -/
@[to_additive /-- The restriction of `f : G →+ G'` to a homomorphism of centralizers
`C_G(s) →+ C_{G'}(t)`, for any subset `t` of the image `f(s)`. -/]
def centralizerMap (f : G →* G') {s : Set G} {t : Set G'} (h : t ⊆ f '' s) :
    centralizer s →* centralizer t :=
  (f.comp (centralizer s).subtype).codRestrict _ fun c =>
    centralizer_le h (map_centralizer_le_centralizer_image s f (mem_map_of_mem f c.2))

@[to_additive (attr := simp)]
theorem centralizerMap_apply_coe (f : G →* G') {s : Set G} {t : Set G'} (h : t ⊆ f '' s)
    (c : centralizer s) : (f.centralizerMap h c : G') = f c :=
  (rfl)

@[to_additive]
theorem centralizerMap_injective {f : G →* G'} (hf : Function.Injective f) {s : Set G}
    {t : Set G'} (h : t ⊆ f '' s) : Function.Injective (f.centralizerMap h) :=
  fun _ _ hc => Subtype.ext (hf (congrArg Subtype.val hc))

end MonoidHom

namespace MulEquiv

variable {G G' : Type*} [Group G] [Group G']

/-- The restriction of `e : G ≃* G'` to a multiplicative equivalence `C_G(s) ≃* C_{G'}(t)` of
centralizers, for any subset `t` equal to the image `e(s)`. -/
@[to_additive /-- The restriction of `e : G ≃+ G'` to an additive equivalence
`C_G(s) ≃+ C_{G'}(t)` of centralizers, for any subset `t` equal to the image `e(s)`. -/]
def centralizerMap (e : G ≃* G') {s : Set G} {t : Set G'} (h : t = e '' s) :
    centralizer s ≃* centralizer t :=
  (e.subgroupMap (centralizer s)).trans
    (subgroupCongr (by rw [Subgroup.map_centralizer_equiv, h]))

@[to_additive (attr := simp)]
theorem centralizerMap_apply_coe (e : G ≃* G') {s : Set G} {t : Set G'} (h : t = e '' s)
    (c : centralizer s) : ((e.centralizerMap h c : centralizer t) : G') = e c :=
  (rfl)

@[to_additive (attr := simp)]
theorem centralizerMap_symm_apply_coe (e : G ≃* G') {s : Set G} {t : Set G'} (h : t = e '' s)
    (c : centralizer t) : (((e.centralizerMap h).symm c : centralizer s) : G) = e.symm c :=
  (rfl)

end MulEquiv
