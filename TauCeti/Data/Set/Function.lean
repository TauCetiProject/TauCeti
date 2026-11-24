/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Function

/-!
# Injectivity on a union, involutions and invariant sets of injective maps

* `Set.InjOn.union_of_disjoint_image`: a map injective on two sets with disjoint images is
  injective on their union.
* `Set.MapsTo.image_eq_of_involutive`: an involution mapping a set into itself maps it onto
  itself.
* `Set.MapsTo.image_inter_eq_preimage_of_involutive`: such an involution carries `s ∩ t` onto
  `s ∩ f ⁻¹' t`.
* `Set.mapsTo_preimage_of_apply_eq`: a map compatible with maps `q` and `q'` to a common type
  carries preimages under `q` into preimages under `q'`.
* `Set.bijOn_preimage_iff`: a map restricts to a bijection from the preimage of `t` onto `t` if
  and only if it is injective on that preimage and `t` is contained in its range.
* `Function.Injective.mapsTo_of_eq_self`: an injective self-map fixing every point outside a
  set `K` maps `K` into itself.
* `Function.Injective.apply_mem_iff_of_eq_self`: such a map preserves membership in every set
  containing `K`.
* `Function.Injective.apply_notMem_pair`: an injective map sends a point other than `b` and `c`
  outside the pair `{f b, f c}`.
* `Function.Injective.val_mem_of_subset_insert`: an injective map into a set `T ⊆ insert z₀ S`
  sends every point other than a preimage of `z₀` into `S`.
* `Function.Injective.eq_of_apply_eq_of_range_inter_subset_singleton`: if `f` is injective,
  `range f ∩ range g ⊆ {z}`, `f x₀ = z`, and `f x = g y`, then `x = x₀`.
-/

public section

namespace Set

variable {α β : Type*} {f : α → β} {s t : Set α}

/-- A map injective on two sets whose images are disjoint is injective on their union. -/
theorem InjOn.union_of_disjoint_image (hs : InjOn f s) (ht : InjOn f t)
    (h : Disjoint (f '' s) (f '' t)) : InjOn f (s ∪ t) :=
  (injOn_union h.of_image).2 ⟨hs, ht, fun _ hx _ hy hxy ↦
    disjoint_left.1 h (mem_image_of_mem f hx) (hxy ▸ mem_image_of_mem f hy)⟩

/-- An involution mapping a set into itself maps it onto itself. -/
theorem MapsTo.image_eq_of_involutive {f : α → α} {s : Set α} (hf : Function.Involutive f)
    (h : MapsTo f s s) : f '' s = s :=
  h.image_subset.antisymm fun x hx => ⟨f x, h hx, hf x⟩

/-- An involution mapping a set `s` into itself carries `s ∩ t` onto `s ∩ f ⁻¹' t`. -/
theorem MapsTo.image_inter_eq_preimage_of_involutive {f : α → α} {s : Set α}
    (hf : Function.Involutive f) (h : MapsTo f s s) : f '' (s ∩ t) = s ∩ f ⁻¹' t := by
  have hs : f ⁻¹' s = s := by rw [← hf.image_eq_preimage_symm, h.image_eq_of_involutive hf]
  rw [hf.image_eq_preimage_symm, preimage_inter, hs]

/-- A map `f` compatible with maps `q` and `q'` to a common type, that is with `q' ∘ f = q`,
carries preimages under `q` into preimages under `q'`. -/
theorem mapsTo_preimage_of_apply_eq {γ : Type*} (f : α → β) {q : α → γ} {q' : β → γ}
    (hf : ∀ x, q' (f x) = q x) (S : Set γ) : MapsTo f (q ⁻¹' S) (q' ⁻¹' S) :=
  fun x hx ↦ by rw [mem_preimage, hf]; exact hx

/-- A map restricts to a bijection from the preimage of `t` onto `t` if and only if it is
injective on that preimage and `t` is contained in its range. -/
theorem bijOn_preimage_iff {t : Set β} :
    BijOn f (f ⁻¹' t) t ↔ InjOn f (f ⁻¹' t) ∧ t ⊆ range f :=
  ⟨fun h ↦ ⟨h.injOn, h.surjOn.trans (image_subset_range _ _)⟩, fun ⟨hinj, hsub⟩ ↦ by
    simpa only [image_preimage_eq_of_subset hsub] using hinj.bijOn_image⟩

end Set

open Set

namespace Function.Injective

/-- An injective map fixing every point outside `K` maps `K` into itself. -/
theorem mapsTo_of_eq_self {α : Type*} {f : α → α} (hf : Injective f) {K : Set α}
    (h : ∀ p ∉ K, f p = p) : MapsTo f K K := by
  have hs : SurjOn f Kᶜ Kᶜ := fun p hp ↦ ⟨p, hp, h p hp⟩
  simpa using hs.mapsTo_compl hf

/-- An injective map fixing every point outside `K` preserves membership in every set `s`
containing `K`. -/
theorem apply_mem_iff_of_eq_self {α : Type*} {f : α → α} (hf : Injective f) {K s : Set α}
    (h : ∀ p ∉ K, f p = p) (hKs : K ⊆ s) (x : α) : f x ∈ s ↔ x ∈ s := by
  by_cases hx : x ∈ K
  · exact iff_of_true (hKs (hf.mapsTo_of_eq_self h hx)) (hKs hx)
  · rw [h x hx]

/-- An injective map sends a point other than `b` and `c` outside the pair `{f b, f c}`. -/
theorem apply_notMem_pair {α : Sort*} {β : Type*} {f : α → β} (hf : Injective f) {a b c : α}
    (hb : a ≠ b) (hc : a ≠ c) : f a ∉ ({f b, f c} : Set β) := by
  simp [hf.ne hb, hf.ne hc]

/-- An injective map `e` into a set `T ⊆ insert z₀ S` with `e a₀ = z₀` sends every `a ≠ a₀`
into `S`. -/
theorem val_mem_of_subset_insert {α : Sort*} {β : Type*} {T S : Set β} {z₀ : β} {e : α → T}
    (he : Injective e) (hT : T ⊆ insert z₀ S) {a₀ a : α} (he₀ : (e a₀).val = z₀)
    (ha : a ≠ a₀) : (e a).val ∈ S :=
  mem_of_mem_insert_of_ne (hT (e a).property) fun h ↦ ha (he (Subtype.ext (h.trans he₀.symm)))

/-- If `f` is injective, `range f ∩ range g ⊆ {z}`, `f x₀ = z`, and `f x = g y`, then `x = x₀`. -/
theorem eq_of_apply_eq_of_range_inter_subset_singleton {α β : Sort*} {γ : Type*}
    {f : α → γ} {g : β → γ} (hf : Injective f) {z : γ} {x₀ x : α} {y : β}
    (hfg : range f ∩ range g ⊆ {z}) (hx₀ : f x₀ = z) (h : f x = g y) : x = x₀ :=
  hf ((mem_singleton_iff.mp (hfg ⟨mem_range_self x, h ▸ mem_range_self y⟩)).trans hx₀.symm)

end Function.Injective
