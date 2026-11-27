/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Spectrum.Maximal.Basic

import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Maximal spectra of integral ring extensions

An integral ring homomorphism `f : A →+* B` contracts maximal ideals of `B` to maximal ideals
of `A`, inducing `MaximalSpectrum.comapOfIsIntegral`. When the kernel of `f` is contained in the
Jacobson radical of `A` (in particular, when `f` is injective or has nilpotent kernel), lying-over
ensures that every maximal ideal of `A` lies under a maximal ideal of `B`, so `comapOfIsIntegral`
is surjective (`MaximalSpectrum.comapOfIsIntegral_surjective`).

## Main definitions

* `MaximalSpectrum.comapOfIsIntegral`: the map `MaximalSpectrum B → MaximalSpectrum A` induced by
  an integral ring homomorphism `f : A →+* B`.

## Main results

* `MaximalSpectrum.comapOfIsIntegral_asIdeal`:
  `(comapOfIsIntegral f hf y).asIdeal = y.asIdeal.comap f`.
* `MaximalSpectrum.comapOfIsIntegral_surjective`: if `RingHom.ker f ≤ Ideal.jacobson ⊥`, then
  `comapOfIsIntegral f hf` is surjective.
-/

public section

namespace MaximalSpectrum

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Contraction on maximal spectra induced by an integral ring homomorphism `f : A →+* B`. -/
def comapOfIsIntegral (f : A →+* B) (hf : f.IsIntegral) :
    MaximalSpectrum B → MaximalSpectrum A :=
  fun y ↦ ⟨y.asIdeal.comap f, Ideal.isMaximal_comap_of_isIntegral_of_isMaximal f hf y.asIdeal⟩

@[simp]
theorem comapOfIsIntegral_asIdeal (f : A →+* B) (hf : f.IsIntegral) (y : MaximalSpectrum B) :
    (comapOfIsIntegral f hf y).asIdeal = y.asIdeal.comap f :=
  (rfl)

/-- If an integral ring homomorphism `f : A →+* B` has kernel contained in the Jacobson radical
`Ideal.jacobson (⊥ : Ideal A)`, then its contraction map `comapOfIsIntegral f hf` on maximal
spectra is surjective. -/
theorem comapOfIsIntegral_surjective (f : A →+* B) (hf : f.IsIntegral)
    (hker : RingHom.ker f ≤ Ideal.jacobson (⊥ : Ideal A)) :
    Function.Surjective (comapOfIsIntegral f hf) := by
  intro x
  algebraize [f]
  let _ : Algebra.IsIntegral A B := ⟨hf⟩
  have hx : RingHom.ker (algebraMap A B) ≤ x.asIdeal :=
    hker.trans (sInf_le ⟨bot_le, x.isMaximal⟩)
  obtain ⟨m, hm, hmcomap⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral x.asIdeal hx
  exact ⟨⟨m, hm⟩, MaximalSpectrum.ext hmcomap⟩

end MaximalSpectrum
