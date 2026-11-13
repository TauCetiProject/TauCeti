/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import TauCeti.CategoryTheory.Projective.Cover

/-!
# Projective covers in an abelian category

A projective cover `π : P ⟶ A` (an essential epimorphism from a projective object,
`TauCeti.IsEssentialEpi`) is a retract of every epimorphism onto `A` from a projective object
(`TauCeti.IsEssentialEpi.exists_comp_eq_and_isSplitEpi`). In an abelian category this comparison
passes to kernels, which is the inductive step comparing a minimal projective resolution with an
arbitrary one: if `A` is a retract of `B` and `q : J ⟶ B` is an epimorphism from a projective
object, then `P` is a retract of `J` and `kernel π` is a retract of `kernel q`
(`TauCeti.IsEssentialEpi.nonempty_retract_and_nonempty_retract_kernel`).

The proof needs that adding a summand keeps an epimorphism essential: if `π` is essential, so is
`biprod.map π (𝟙 K)` for every `K` (`TauCeti.IsEssentialEpi.biprod_map_id`). This file is the dual
of `TauCeti/CategoryTheory/Abelian/Injective/Envelope.lean`.

## Main results

* `TauCeti.IsEssentialEpi.biprod_map_id`: `biprod.map π (𝟙 K)` is an essential epimorphism when
  `π` is.
* `TauCeti.IsEssentialEpi.nonempty_retract_and_nonempty_retract_kernel`: a projective cover of a
  retract of `B` is a retract of every projective object mapping onto `B`, compatibly with the
  kernels.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, LMS Student Texts 65, CUP (2006), I.5.
* F. W. Anderson, K. R. Fuller, *Rings and Categories of Modules*, 2nd ed., Springer GTM 13
  (1992), §17.
-/

public section

universe v u

namespace TauCeti

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace IsEssentialEpi

/-- **Adding a summand keeps an epimorphism essential.** If `π : P ⟶ A` is an essential
epimorphism, then so is `biprod.map π (𝟙 K) : P ⊞ K ⟶ A ⊞ K`. -/
theorem biprod_map_id {P A : C} {π : P ⟶ A} (hπ : IsEssentialEpi π) (K : C) :
    IsEssentialEpi (biprod.map π (𝟙 K)) where
  epi := by
    have := hπ.epi
    infer_instance
  epi_of_epi_comp {X} g hg := by
    -- The component `g₂` of `g` towards `K` is an epimorphism, and `g` restricted to the kernel of
    -- `g₂` stays an epimorphism onto `P`.
    let g₂ : X ⟶ K := g ≫ biprod.snd
    have hg₂ : Epi g₂ := by
      have : g₂ = (g ≫ biprod.map π (𝟙 K)) ≫ biprod.snd := by simp [g₂]
      rw [this]
      infer_instance
    let h : kernel g₂ ⟶ P := kernel.ι g₂ ≫ g ≫ biprod.fst
    have hh : Epi h := by
      refine hπ.epi_of_epi_comp h (Preadditive.epi_of_cancel_zero _ fun {W} a ha ↦ ?_)
      have ha' : kernel.ι g₂ ≫ g ≫ biprod.fst ≫ π ≫ a = 0 := by simpa [h] using ha
      let b : K ⟶ W := Abelian.epiDesc g₂ _ ha'
      have hb : g₂ ≫ b = g ≫ biprod.fst ≫ π ≫ a := Abelian.comp_epiDesc g₂ _ ha'
      have : (g ≫ biprod.map π (𝟙 K)) ≫ (biprod.fst ≫ a - biprod.snd ≫ b) = 0 := by
        simp only [Preadditive.comp_sub, Category.assoc, biprod.map_fst_assoc,
          biprod.map_snd_assoc, Category.id_comp]
        rw [sub_eq_zero, ← hb]
        simp [g₂]
      have := (cancel_epi (g ≫ biprod.map π (𝟙 K))).1 (this.trans comp_zero.symm)
      simpa using congrArg (biprod.inl ≫ ·) this
    refine Preadditive.epi_of_cancel_zero _ fun {W} c hc ↦ ?_
    have hc' : g ≫ biprod.fst ≫ biprod.inl ≫ c + g₂ ≫ biprod.inr ≫ c = 0 := by
      calc _ = g ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ c := by
            rw [Preadditive.add_comp, Preadditive.comp_add]
            simp only [g₂, Category.assoc]
        _ = 0 := by rw [biprod.total, Category.id_comp, hc]
    have h₁ : biprod.inl ≫ c = 0 := by
      have := congrArg (kernel.ι g₂ ≫ ·) hc'
      simp only [Preadditive.comp_add, kernel.condition_assoc, zero_comp, add_zero,
        comp_zero] at this
      rw [← cancel_epi h, comp_zero]
      simpa [h] using this
    have h₂ : biprod.inr ≫ c = 0 := by
      simp only [h₁, comp_zero, zero_add] at hc'
      rwa [← cancel_epi g₂, comp_zero]
    ext <;> simp [h₁, h₂]

/-- **A projective cover of a retract is a retract, compatibly with kernels.** Let `π : P ⟶ A`
be an essential epimorphism from a projective object, `q : J ⟶ B` an epimorphism from a
projective object, and `A` a retract of `B`. Then `P` is a retract of `J`, and `kernel π` is a
retract of `kernel q`.

Taking `B = A`, this says that the projective cover is a retract of every projective object
mapping onto `A`, together with the syzygies; iterating it compares a minimal projective
resolution with an arbitrary one. -/
theorem nonempty_retract_and_nonempty_retract_kernel {A B P J : C} [Projective P] [Projective J]
    {π : P ⟶ A} (hπ : IsEssentialEpi π) {q : J ⟶ B} [Epi q] (h : Retract A B) :
    Nonempty (Retract P J) ∧ Nonempty (Retract (kernel π) (kernel q)) := by
  have := hπ.epi
  -- `g : J ⟶ P` lifts `J ⟶ B ⟶ A` along `π`.
  let g : J ⟶ P := Projective.factorThru (q ≫ h.r) π
  have hg : g ≫ π = q ≫ h.r := Projective.factorThru_comp _ _
  -- The complement `K` of `A` in `B`.
  let κ : B ⟶ cokernel h.i := cokernel.π h.i
  let p : cokernel h.i ⟶ B := cokernel.desc h.i (𝟙 B - h.r ≫ h.i) (by simp)
  have hp : κ ≫ p = 𝟙 B - h.r ≫ h.i := cokernel.π_desc _ _ _
  have hpr : p ≫ h.r = 0 := by
    rw [← cancel_epi κ, reassoc_of% hp]
    simp
  have hpκ : p ≫ κ = 𝟙 _ := by
    rw [← cancel_epi κ, reassoc_of% hp]
    simp [κ]
  -- `B ≅ A ⊞ K`, through `biprod.lift h.r κ` with right inverse `biprod.desc h.i p`.
  have hd : Epi (biprod.lift h.r κ) := by
    have : biprod.desc h.i p ≫ biprod.lift h.r κ = 𝟙 _ := by
      ext <;> simp [hpr, hpκ, κ]
    exact ⟨fun a b hab ↦ by simpa [reassoc_of% this] using congrArg (biprod.desc h.i p ≫ ·) hab⟩
  -- `u : J ⟶ P ⊞ K` is an epimorphism, since `P ⊞ K ⟶ A ⊞ K` is essential.
  let u : J ⟶ P ⊞ cokernel h.i := biprod.lift g (q ≫ κ)
  have hu : Epi u := by
    refine (hπ.biprod_map_id _).epi_of_epi_comp u ?_
    have : u ≫ biprod.map π (𝟙 _) = q ≫ biprod.lift h.r κ := by
      ext <;> simp [u, hg]
    rw [this]
    infer_instance
  -- `s : P ⟶ J` is a section of `g` landing in the kernel of `J ⟶ K`.
  let s : P ⟶ J := Projective.factorThru biprod.inl u
  have hs : s ≫ u = biprod.inl := Projective.factorThru_comp _ _
  have hsg : s ≫ g = 𝟙 P := by simpa [u] using congrArg (· ≫ biprod.fst) hs
  have hsκ : s ≫ q ≫ κ = 0 := by simpa [u] using congrArg (· ≫ biprod.snd) hs
  have hsq : s ≫ q = π ≫ h.i := by
    have : 𝟙 B = h.r ≫ h.i + κ ≫ p := by rw [hp]; abel
    calc s ≫ q = s ≫ q ≫ (h.r ≫ h.i + κ ≫ p) := by rw [← this, Category.comp_id]
      _ = s ≫ (q ≫ h.r) ≫ h.i + (s ≫ q ≫ κ) ≫ p := by
        simp only [Preadditive.comp_add, Category.assoc]
      _ = π ≫ h.i := by rw [hsκ, zero_comp, add_zero, ← hg, Category.assoc, reassoc_of% hsg]
  refine ⟨⟨⟨s, g, hsg⟩⟩, ⟨⟨kernel.lift q (kernel.ι π ≫ s) ?_,
    kernel.lift π (kernel.ι q ≫ g) ?_, ?_⟩⟩⟩
  · rw [Category.assoc, hsq]
    simp
  · rw [Category.assoc, hg]
    simp
  · ext
    simp [hsg]

end IsEssentialEpi

end TauCeti
