/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralObject.SpectralSequenceMap

/-!
# Isomorphisms of spectral objects

A morphism `φ : X ⟶ Y` of spectral objects in an abelian category consists of natural
transformations `φ.hom n : X.H n ⟶ Y.H n` commuting with the connecting maps. It is an isomorphism
as soon as each component `(φ.hom n).app D` is one
(`CategoryTheory.Abelian.SpectralObject.isIso_of_isIso_hom_app`): the inverses of the components
again commute with the connecting maps. An isomorphism of spectral objects induces an isomorphism
of the spectral sequences of any recipe, since `spectralSequenceMap` is functorial.

## Main results

* `CategoryTheory.Abelian.SpectralObject.isIso_of_isIso_hom_app`: a morphism of spectral objects
  which is an isomorphism on every component is an isomorphism.
* An isomorphism of spectral objects induces an isomorphism of spectral sequences (an instance on
  `CategoryTheory.Abelian.SpectralObject.spectralSequenceMap`).
-/

public section

namespace CategoryTheory.Abelian.SpectralObject

open ComposableArrows

variable {C ι : Type*} [Category* C] [Abelian C]

section

variable [Category* ι] {X Y : SpectralObject C ι}

/-- **A morphism of spectral objects is an isomorphism when all its components are.** -/
lemma isIso_of_isIso_hom_app (φ : X ⟶ Y)
    (h : ∀ (n : ℤ) (D : ComposableArrows ι 1), IsIso ((φ.hom n).app D)) : IsIso φ := by
  have (n : ℤ) : IsIso (φ.hom n) := NatIso.isIso_of_isIso_app _
  let ψ : Y ⟶ X :=
    { hom n := inv (φ.hom n)
      comm n₀ n₁ hn₁ i j k f g := by
        rw [← cancel_epi ((φ.hom n₀).app (mk₁ g)), ← cancel_mono ((φ.hom n₁).app (mk₁ f))]
        simp only [Category.assoc, NatIso.isIso_inv_app, IsIso.inv_hom_id, Category.comp_id,
          IsIso.hom_inv_id_assoc, Hom.comm] }
  exact ⟨ψ, Hom.ext <| funext fun n ↦ by simp [ψ], Hom.ext <| funext fun n ↦ by simp [ψ]⟩

end

variable [Preorder ι] {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (data : SpectralSequenceDataCore ι c r₀) {X Y : SpectralObject C ι}
  [X.HasSpectralSequence data] [Y.HasSpectralSequence data]

/-- An isomorphism of spectral objects induces an isomorphism of spectral sequences. -/
instance (φ : X ⟶ Y) [IsIso φ] : IsIso (spectralSequenceMap data φ) :=
  ⟨spectralSequenceMap data (inv φ), by simp [← spectralSequenceMap_comp],
    by simp [← spectralSequenceMap_comp]⟩

end CategoryTheory.Abelian.SpectralObject
