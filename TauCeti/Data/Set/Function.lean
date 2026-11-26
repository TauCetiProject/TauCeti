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
* `Set.mem_univ_pi_sdiff_update_iff`: membership in `univ.pi A \ univ.pi (Function.update A k B)`.
* `Function.Injective.mapsTo_of_eq_self`: an injective self-map fixing every point outside a
  set `K` maps `K` into itself.
* `Function.Injective.apply_mem_iff_of_eq_self`: such a map preserves membership in every set
  containing `K`.
* `Function.Injective.apply_notMem_pair`: an injective map sends a point other than `b` and `c`
  outside the pair `{f b, f c}`.
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

/-- Removing from a full product `univ.pi A` the subproduct with coordinate `k` updated to `B`
leaves the tuples in `univ.pi A` whose `k`-th coordinate lies outside `B`. -/
theorem mem_univ_pi_sdiff_update_iff {ι : Type*} [DecidableEq ι] {γ : ι → Type*}
    (A : ∀ i, Set (γ i)) (k : ι) (B : Set (γ k)) {x : ∀ i, γ i} :
    x ∈ univ.pi A \ univ.pi (Function.update A k B) ↔ (∀ i, x i ∈ A i) ∧ x k ∉ B := by
  rw [mem_sdiff, mem_univ_pi, mem_univ_pi]
  refine and_congr_right fun hx ↦ not_congr ?_
  refine ⟨fun h ↦ by simpa only [Function.update_self] using h k, fun h i ↦ ?_⟩
  rcases eq_or_ne i k with rfl | hik
  · simpa only [Function.update_self] using h
  · simpa only [Function.update_of_ne hik] using hx i

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

end Function.Injective
