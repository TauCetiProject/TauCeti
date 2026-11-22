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

The preimage of `{y}` under `e` is `{e.symm y}` (`Equiv.preimage_singleton`). Together with
`Set.preimage_comp`, this identifies fibres after relabelling the base by an equivalence.

A map `g : α → β` that agrees on `s` with an equivalence `s ≃ t` is a bijection from `s` onto `t`
(`Equiv.bijOn_of_coe_eq`). This is a converse to `Set.BijOn.equiv`, which turns a bijection
between sets into an equivalence of the subtypes.

An injective map `f : α → β` identifies `β` with the sum of `α` and the complement of the range
of `f` (`Equiv.ofInjectiveSumCompl`).

Two injective maps `f : α → γ` and `g : β → γ` with equal ranges induce a canonical equivalence
`α ≃ β` (`Equiv.ofRangeEq`), intertwining `g` and `f` (`Equiv.apply_ofRangeEq` and
`Equiv.apply_ofRangeEq_symm`), uniquely characterized by `Equiv.eq_ofRangeEq_iff`.
-/

public section

namespace Equiv

/-- The preimage of a singleton under an equivalence is the singleton of its inverse image. -/
@[simp]
theorem preimage_singleton {α β : Type*} (e : α ≃ β) (y : β) :
    e ⁻¹' {y} = {e.symm y} := by
  rw [← e.image_symm_eq_preimage, Set.image_singleton]

/-- An equivalence carries `s` onto `t` exactly when it maps `s` into `t` and its inverse maps `t`
into `s`. -/
theorem forall_apply_mem_iff_iff_mapsTo {α β : Type*} (e : α ≃ β) (s : Set α) (t : Set β) :
    (∀ x, e x ∈ t ↔ x ∈ s) ↔ Set.MapsTo e s t ∧ Set.MapsTo e.symm t s :=
  ⟨fun h ↦ ⟨fun x hx ↦ (h x).mpr hx, fun y hy ↦ (h _).mp (by rwa [apply_symm_apply])⟩,
    fun ⟨h, hsymm⟩ x ↦ ⟨fun hx ↦ by simpa using hsymm hx, fun hx ↦ h hx⟩⟩

/-- A map that agrees on `s` with an equivalence `s ≃ t` is a bijection from `s` onto `t`. -/
theorem bijOn_of_coe_eq {α β : Type*} {s : Set α} {t : Set β} {g : α → β}
    (e : s ≃ t) (he : ∀ z : s, (e z : β) = g z) : Set.BijOn g s t := by
  refine ⟨fun z hz => he ⟨z, hz⟩ ▸ (e ⟨z, hz⟩).property, fun x hx y hy hxy => ?_, fun y hy => ?_⟩
  · have := e.injective (Subtype.ext ((he ⟨x, hx⟩).trans (hxy.trans (he ⟨y, hy⟩).symm)))
    exact congrArg Subtype.val this
  · exact ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, by rw [← he, e.apply_symm_apply]⟩

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

/-- Two injective maps `f : α → γ` and `g : β → γ` with equal ranges induce a canonical
equivalence `α ≃ β`. -/
noncomputable def ofRangeEq {α β : Sort*} {γ : Type*} {f : α → γ} {g : β → γ}
    (hf : f.Injective) (hg : g.Injective) (h : Set.range f = Set.range g) :
    α ≃ β :=
  (ofInjective f hf).trans ((Set.equivOfEq h).trans (ofInjective g hg).symm)

/-- Applying `g` after `Equiv.ofRangeEq hf hg h` recovers `f`.

Not a `simp` lemma: the left-hand side has the bare function variable `g` at the head. -/
theorem apply_ofRangeEq {α β : Sort*} {γ : Type*} {f : α → γ} {g : β → γ}
    (hf : f.Injective) (hg : g.Injective) (h : Set.range f = Set.range g) (x : α) :
    g (ofRangeEq hf hg h x) = f x := by
  simp only [ofRangeEq, trans_apply, apply_ofInjective_symm,
    Set.equivOfEq_apply, ofInjective_apply]

/-- Applying `f` after the inverse of `Equiv.ofRangeEq hf hg h` recovers `g`.

Not a `simp` lemma: the left-hand side has the bare function variable `f` at the head. -/
theorem apply_ofRangeEq_symm {α β : Sort*} {γ : Type*} {f : α → γ} {g : β → γ}
    (hf : f.Injective) (hg : g.Injective) (h : Set.range f = Set.range g) (y : β) :
    f ((ofRangeEq hf hg h).symm y) = g y := by
  simp only [ofRangeEq, symm_trans_apply, symm_symm,
    apply_ofInjective_symm, Set.equivOfEq_symm_apply, ofInjective_apply]

/-- An equivalence `e : α ≃ β` equals `Equiv.ofRangeEq hf hg h` if and only if it intertwines
`g` and `f`, i.e. `g ∘ e = f`. -/
theorem eq_ofRangeEq_iff {α β : Sort*} {γ : Type*} {f : α → γ} {g : β → γ}
    (hf : f.Injective) (hg : g.Injective) (h : Set.range f = Set.range g) (e : α ≃ β) :
    e = ofRangeEq hf hg h ↔ g ∘ e = f := by
  refine ⟨fun he ↦ ?_, fun he ↦ ?_⟩
  · subst he
    exact funext (apply_ofRangeEq hf hg h)
  · ext x
    exact hg ((congrFun he x).trans (apply_ofRangeEq hf hg h x).symm)

/-- Comparing an injective map with itself gives the identity equivalence. -/
@[simp]
theorem ofRangeEq_self {α : Sort*} {γ : Type*} {f : α → γ}
    (hf : f.Injective) (h : Set.range f = Set.range f := rfl) :
    ofRangeEq hf hf h = Equiv.refl α :=
  ((eq_ofRangeEq_iff hf hf h (.refl α)).2 rfl).symm

/-- The inverse of `Equiv.ofRangeEq hf hg h` is `Equiv.ofRangeEq hg hf h.symm`. -/
@[simp]
theorem ofRangeEq_symm {α β : Sort*} {γ : Type*} {f : α → γ} {g : β → γ}
    (hf : f.Injective) (hg : g.Injective) (h : Set.range f = Set.range g) :
    (ofRangeEq hf hg h).symm = ofRangeEq hg hf h.symm :=
  (eq_ofRangeEq_iff hg hf h.symm _).2 (funext (apply_ofRangeEq_symm hf hg h))

/-- Composing two canonical equal-range equivalences gives the direct equal-range equivalence. -/
@[simp]
theorem ofRangeEq_trans {α β δ : Sort*} {γ : Type*} {f : α → γ} {g : β → γ} {k : δ → γ}
    (hf : f.Injective) (hg : g.Injective) (hk : k.Injective)
    (h₁ : Set.range f = Set.range g) (h₂ : Set.range g = Set.range k) :
    (ofRangeEq hf hg h₁).trans (ofRangeEq hg hk h₂) = ofRangeEq hf hk (h₁.trans h₂) := by
  rw [eq_ofRangeEq_iff]
  funext x
  simp only [Function.comp_apply, trans_apply, apply_ofRangeEq]

end Equiv
