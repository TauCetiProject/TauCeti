/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Set

/-!
# Equivalences and sets

An equivalence `e : α ≃ β` carries `s` onto `t`, in the sense that `e x ∈ t ↔ x ∈ s` for every
`x`, exactly when `e` maps `s` into `t` and `e.symm` maps `t` into `s`.

A map `g : α → β` that agrees on `s` with an equivalence `s ≃ t` is a bijection from `s` onto `t`
(`Equiv.bijOn_of_coe_eq`). This is a converse to `Set.BijOn.equiv`, which turns a bijection
between sets into an equivalence of the subtypes.

An injective map `f : α → β` identifies `β` with the sum of `α` and the complement of the range
of `f` (`Equiv.ofInjectiveSumCompl`).
-/

public section

namespace Equiv

/-- An equivalence carries `s` onto `t` exactly when it maps `s` into `t` and its inverse maps `t`
into `s`. -/
theorem forall_apply_mem_iff_iff_mapsTo {α β : Type*} (e : α ≃ β) (s : Set α) (t : Set β) :
    (∀ x, e x ∈ t ↔ x ∈ s) ↔ Set.MapsTo e s t ∧ Set.MapsTo e.symm t s :=
  ⟨fun h ↦ ⟨fun x hx ↦ (h x).mpr hx, fun y hy ↦ (h _).mp (by rwa [apply_symm_apply])⟩,
    fun ⟨h, hsymm⟩ x ↦ ⟨fun hx ↦ by simpa using hsymm hx, fun hx ↦ h hx⟩⟩

/-- A map that agrees on `s` with an equivalence `s ≃ t` is a bijection from `s` onto `t`. -/
theorem bijOn_of_coe_eq {α β : Type*} {s : Set α} {t : Set β} {g : α → β}
    (e : s ≃ t) (he : ∀ z : s, (e z : β) = g z) : Set.BijOn g s t := by
  refine ⟨fun z hz => he ⟨z, hz⟩ ▸ (e ⟨z, hz⟩).2, fun x hx y hy hxy => ?_, fun y hy => ?_⟩
  · have := e.injective (Subtype.ext ((he ⟨x, hx⟩).trans (hxy.trans (he ⟨y, hy⟩).symm)))
    exact congrArg Subtype.val this
  · exact ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).2, by rw [← he, e.apply_symm_apply]⟩

open Classical in
/-- An injective map `f : α → β` identifies `β` with the sum of `α`, sent to `β` by `f`, and the
complement of the range of `f`. -/
noncomputable def ofInjectiveSumCompl {α β : Type*} (f : α → β) (hf : f.Injective) :
    α ⊕ ↥(Set.range f)ᶜ ≃ β :=
  ((ofInjective f hf).sumCongr (.refl _)).trans (Set.sumCompl (Set.range f))

variable {α β : Type*} {f : α → β} (hf : f.Injective)

@[simp]
theorem ofInjectiveSumCompl_apply_inl (a : α) : ofInjectiveSumCompl f hf (.inl a) = f a := by
  simp [ofInjectiveSumCompl]

@[simp]
theorem ofInjectiveSumCompl_apply_inr (b : ↥(Set.range f)ᶜ) :
    ofInjectiveSumCompl f hf (.inr b) = b := by
  simp [ofInjectiveSumCompl]

@[simp]
theorem ofInjectiveSumCompl_symm_apply (a : α) : (ofInjectiveSumCompl f hf).symm (f a) = .inl a :=
  (ofInjectiveSumCompl f hf).symm_apply_eq.2 (ofInjectiveSumCompl_apply_inl hf a).symm

@[simp]
theorem ofInjectiveSumCompl_symm_apply_compl (b : ↥(Set.range f)ᶜ) :
    (ofInjectiveSumCompl f hf).symm b = .inr b :=
  (ofInjectiveSumCompl f hf).symm_apply_eq.2 (ofInjectiveSumCompl_apply_inr hf b).symm

end Equiv
