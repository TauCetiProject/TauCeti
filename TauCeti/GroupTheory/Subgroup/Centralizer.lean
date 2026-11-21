/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Centralizers under group homomorphisms

A homomorphism `f : G →* G'` maps the centralizer `C_G(s)` of a subset `s` into the centralizer
`C_{G'}(f(s))`, hence into `C_{G'}(t)` for every `t ⊆ f(s)`. This file records the restriction of
`f` as a homomorphism `C_G(s) →* C_{G'}(t)`; the case `s = {u}`, `t = {f u}` gives a homomorphism
`C_G(u) →* C_{G'}(f u)`. An injective `f` pulls `C_{G'}(f(s))` back to `C_G(s)`, and an
isomorphism `e : G ≃* G'` maps `C_G(s)` onto `C_{G'}(e(s))`, so restricts to an isomorphism
`C_G(s) ≃* C_{G'}(e(s))`; for an inner automorphism this identifies the centralizers of conjugate
elements, `C_G(g⁻¹ x g) = g⁻¹ C_G(x) g`.

## Main definitions

* `MonoidHom.centralizerMap`: the restriction `C_G(s) →* C_{G'}(t)` of `f : G →* G'`, for
  `t ⊆ f(s)`.
* `MulEquiv.centralizerMap`: the restriction `C_G(s) ≃* C_{G'}(t)` of `e : G ≃* G'`, for
  `t = e(s)`.

## Main results

* `Subgroup.comap_centralizer_image_of_injective`: `f⁻¹(C_{G'}(f(s))) = C_G(s)` for injective `f`.
* `MulEquiv.map_centralizer`: a group isomorphism carries the centralizer of a set onto the
  centralizer of its image.
* `MulEquiv.centralizer_image_eq_map`: a description `C_G(f(s)) = f(C_K(s))` of a centralizer is
  carried along an isomorphism and a homomorphism intertwining `f` with another homomorphism.
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

/-- Let `f : K →* G` and `f' : K' →* G'` be intertwined by an isomorphism `e : G ≃* G'` and a
homomorphism `e₁ : K →* K'`, that is `e ∘ f = f' ∘ e₁`. If the centralizer of the image `f(s)` of a
set `s` is the image under `f` of the centralizer of `s`, then the centralizer of `f'(e₁(s))` is the
image under `f'` of the centralizer of `e₁(s)`. -/
@[to_additive /-- Let `f : K →+ G` and `f' : K' →+ G'` be intertwined by an isomorphism
`e : G ≃+ G'` and a homomorphism `e₁ : K →+ K'`, that is `e ∘ f = f' ∘ e₁`. If the centralizer of
the image `f(s)` of a set `s` is the image under `f` of the centralizer of `s`, then the centralizer
of `f'(e₁(s))` is the image under `f'` of the centralizer of `e₁(s)`. -/]
theorem centralizer_image_eq_map {K K' : Type*} [Group K] [Group K'] (e : G ≃* G')
    (e₁ : K →* K') {f : K →* G} {f' : K' →* G'} (hf : ∀ k, e (f k) = f' (e₁ k)) {s : Set K}
    (h : centralizer (f '' s) = (centralizer s).map f) :
    centralizer (f' '' (e₁ '' s)) = (centralizer (e₁ '' s)).map f' := by
  have hs : f' '' (e₁ '' s) = e '' (f '' s) := by simp only [Set.image_image, hf]
  have hf' : (e : G →* G').comp f = f'.comp e₁ := MonoidHom.ext hf
  refine le_antisymm ?_ (map_centralizer_le_centralizer_image _ f')
  rw [hs, ← e.map_centralizer, h, map_map, hf', ← map_map]
  exact map_mono (map_centralizer_le_centralizer_image s e₁)

end MulEquiv
