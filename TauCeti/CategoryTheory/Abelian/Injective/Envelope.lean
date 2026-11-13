/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import TauCeti.CategoryTheory.Injective.Envelope

/-!
# Injective envelopes in an abelian category

An injective envelope `ι : A ⟶ E` (an essential monomorphism into an injective object,
`TauCeti.IsEssentialMono`) is a retract of every monomorphism of `A` into an injective object
(`TauCeti.IsEssentialMono.exists_comp_eq_and_isSplitMono`). In an abelian category this
comparison passes to cokernels, which is the inductive step comparing a minimal injective
coresolution with an arbitrary one: if `A` is a retract of `B` and `j : B ⟶ I` is a monomorphism
into an injective object, then `E` is a retract of `I` and `cokernel ι` is a retract of
`cokernel j` (`TauCeti.IsEssentialMono.nonempty_retract_and_nonempty_retract_cokernel`).

The proof needs that adding a summand keeps a monomorphism essential: if `ι` is essential, so is
`biprod.map ι (𝟙 K)` for every `K` (`TauCeti.IsEssentialMono.biprod_map_id`). For modules this is
the familiar fact that `A ⊕ K` is essential in `E ⊕ K` when `A` is essential in `E`.

## Main results

* `TauCeti.IsEssentialMono.biprod_map_id`: `biprod.map ι (𝟙 K)` is an essential monomorphism
  when `ι` is.
* `TauCeti.IsEssentialMono.nonempty_retract_and_nonempty_retract_cokernel`: an injective envelope
  of a retract of `B` is a retract of every injective object containing `B`, compatibly with the
  cokernels.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, LMS Student Texts 65, CUP (2006), I.5.
* F. W. Anderson, K. R. Fuller, *Rings and Categories of Modules*, 2nd ed., Springer GTM 13
  (1992), §18.
-/

public section

universe v u

namespace TauCeti

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace IsEssentialMono

/-- **Adding a summand keeps a monomorphism essential.** If `ι : A ⟶ E` is an essential
monomorphism, then so is `biprod.map ι (𝟙 K) : A ⊞ K ⟶ E ⊞ K`. -/
theorem biprod_map_id {A E : C} {ι : A ⟶ E} (hι : IsEssentialMono ι) (K : C) :
    IsEssentialMono (biprod.map ι (𝟙 K)) where
  mono := by
    have := hι.mono
    infer_instance
  mono_of_mono_comp {X} g hg := by
    -- The restriction `g₂` of `g` to `K` is a monomorphism, and `g` restricted to `E` stays a
    -- monomorphism after dividing out the image of `g₂`.
    let g₂ : K ⟶ X := biprod.inr ≫ g
    have hg₂ : Mono g₂ := by
      have : g₂ = biprod.inr ≫ biprod.map ι (𝟙 K) ≫ g := by simp [g₂]
      rw [this]
      infer_instance
    let h : E ⟶ cokernel g₂ := biprod.inl ≫ g ≫ cokernel.π g₂
    have hh : Mono h := by
      refine hι.mono_of_mono_comp h (Preadditive.mono_of_cancel_zero _ fun {W} a ha ↦ ?_)
      have ha' : (a ≫ ι ≫ biprod.inl ≫ g) ≫ cokernel.π g₂ = 0 := by simpa [h] using ha
      let b : W ⟶ K := Abelian.monoLift g₂ _ ha'
      have hb : b ≫ g₂ = a ≫ ι ≫ biprod.inl ≫ g := Abelian.monoLift_comp g₂ _ ha'
      have : (a ≫ biprod.inl - b ≫ biprod.inr) ≫ biprod.map ι (𝟙 K) ≫ g = 0 := by
        simp only [Preadditive.sub_comp, Category.assoc, biprod.inl_map_assoc,
          biprod.inr_map_assoc, Category.id_comp]
        rw [sub_eq_zero, ← hb]
      have := (cancel_mono (biprod.map ι (𝟙 K) ≫ g)).1 (this.trans (zero_comp).symm)
      simpa using congrArg (· ≫ biprod.fst) this
    refine Preadditive.mono_of_cancel_zero _ fun {W} c hc ↦ ?_
    have hc' : (c ≫ biprod.fst) ≫ biprod.inl ≫ g + (c ≫ biprod.snd) ≫ g₂ = 0 := by
      calc _ = c ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ g := by
            rw [Preadditive.add_comp, Preadditive.comp_add]
            simp only [g₂, Category.assoc]
        _ = 0 := by rw [biprod.total, Category.id_comp, hc]
    have h₁ : c ≫ biprod.fst = 0 := by
      rw [← cancel_mono h, zero_comp]
      simpa [h, g₂] using congrArg (· ≫ cokernel.π g₂) hc'
    have h₂ : c ≫ biprod.snd = 0 := by
      rw [h₁, zero_comp, zero_add] at hc'
      rwa [← cancel_mono g₂, zero_comp]
    ext <;> simp [h₁, h₂]

/-- **An injective envelope of a retract is a retract, compatibly with cokernels.** Let
`ι : A ⟶ E` be an essential monomorphism into an injective object, `j : B ⟶ I` a monomorphism
into an injective object, and `A` a retract of `B`. Then `E` is a retract of `I`, and
`cokernel ι` is a retract of `cokernel j`.

Taking `B = A`, this says that the injective envelope is a retract of every injective object
containing `A`, together with the cosyzygies; iterating it compares a minimal injective
coresolution with an arbitrary one. -/
theorem nonempty_retract_and_nonempty_retract_cokernel {A B E I : C} [Injective E] [Injective I]
    {ι : A ⟶ E} (hι : IsEssentialMono ι) {j : B ⟶ I} [Mono j] (h : Retract A B) :
    Nonempty (Retract E I) ∧ Nonempty (Retract (cokernel ι) (cokernel j)) := by
  have := hι.mono
  -- `g : E ⟶ I` extends `A ⟶ B ⟶ I` along `ι`.
  let g : E ⟶ I := Injective.factorThru (h.i ≫ j) ι
  have hg : ι ≫ g = h.i ≫ j := Injective.comp_factorThru _ _
  -- The complement `K` of `A` in `B`.
  let κ : kernel h.r ⟶ B := kernel.ι h.r
  let p : B ⟶ kernel h.r := kernel.lift h.r (𝟙 B - h.r ≫ h.i) (by simp)
  have hp : p ≫ κ = 𝟙 B - h.r ≫ h.i := kernel.lift_ι _ _ _
  have hip : h.i ≫ p = 0 := by
    rw [← cancel_mono κ, Category.assoc, hp]
    simp
  have hκp : κ ≫ p = 𝟙 _ := by
    rw [← cancel_mono κ, Category.assoc, hp]
    simp [κ]
  -- `B ≅ A ⊞ K`, through `biprod.desc h.i κ` with left inverse `biprod.lift h.r p`.
  have hd : Mono (biprod.desc h.i κ) := by
    have : biprod.desc h.i κ ≫ biprod.lift h.r p = 𝟙 _ := by
      ext <;> simp [hip, hκp, κ]
    exact ⟨fun a b hab ↦ by simpa [this] using congrArg (· ≫ biprod.lift h.r p) hab⟩
  -- `u : E ⊞ K ⟶ I` is a monomorphism, since `A ⊞ K ⟶ E ⊞ K` is essential.
  let u : E ⊞ kernel h.r ⟶ I := biprod.desc g (κ ≫ j)
  have hu : Mono u := by
    refine (hι.biprod_map_id _).mono_of_mono_comp u ?_
    have : biprod.map ι (𝟙 _) ≫ u = biprod.desc h.i κ ≫ j := by
      ext <;> simp [u, hg]
    rw [this]
    infer_instance
  -- `q : I ⟶ E` retracts `g` and kills `K`.
  let q : I ⟶ E := Injective.factorThru biprod.fst u
  have hq : u ≫ q = biprod.fst := Injective.comp_factorThru _ _
  have hgq : g ≫ q = 𝟙 E := by simpa [u] using congrArg (biprod.inl ≫ ·) hq
  have hκq : κ ≫ j ≫ q = 0 := by simpa [u] using congrArg (biprod.inr ≫ ·) hq
  have hjq : j ≫ q = h.r ≫ ι := by
    have : 𝟙 B = h.r ≫ h.i + p ≫ κ := by rw [hp]; abel
    calc j ≫ q = (h.r ≫ h.i + p ≫ κ) ≫ j ≫ q := by rw [← this, Category.id_comp]
      _ = h.r ≫ ι := by
        rw [Preadditive.add_comp, Category.assoc, Category.assoc, hκq, comp_zero, add_zero,
          ← Category.assoc h.i, ← hg, Category.assoc, hgq, Category.comp_id]
  refine ⟨⟨⟨g, q, hgq⟩⟩, ⟨⟨cokernel.desc ι (g ≫ cokernel.π j) ?_,
    cokernel.desc j (q ≫ cokernel.π ι) ?_, ?_⟩⟩⟩
  · rw [← Category.assoc, hg]
    simp
  · rw [← Category.assoc, hjq]
    simp
  · ext
    simp [reassoc_of% hgq]

end IsEssentialMono

end TauCeti
