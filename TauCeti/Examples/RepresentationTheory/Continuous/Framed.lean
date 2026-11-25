/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Framed

/-!
# Examples: framed continuous representations

* In rank zero there is exactly one framed representation, and its carrier is zero.
* In rank one a framed representation is a character: `ofFramed ρ ≅ ofCharacter χ` for
  `χ = det ∘ ρ`.
* Changing coefficients along the identity changes nothing.
-/

open TauCeti ContinuousRep

variable {Γ A : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CommRing A]
  [TopologicalSpace A] [IsTopologicalRing A]

-- In rank zero there is exactly one framed representation.
example : Unique (Γ →ₜ* GL (Fin 0) A) where
  default := 1
  uniq _ := ContinuousMonoidHom.ext fun _ => Units.ext (Subsingleton.elim _ _)

-- The framed representation of rank zero lives on the zero module.
example : Subsingleton (Fin 0 → A) :=
  inferInstance

-- In rank one a framed representation is the character line of its determinant.
example (ρ : Γ →ₜ* GL (Fin 1) A) (χ : Γ →ₜ* Aˣ)
    (hχ : ∀ g, (χ g : A) = Matrix.det (ρ g : Matrix (Fin 1) (Fin 1) A)) :
    Nonempty (Iso (ofFramed ρ) (ofCharacter χ)) :=
  ⟨Iso.ofEquiv (.mk (LinearEquiv.funUnique (Fin 1) A A) fun g => LinearMap.ext fun v => by
    simp [hχ, Matrix.mulVec, dotProduct, Matrix.det_unique])⟩

-- Coefficient change along the identity changes nothing.
example (ρ : Γ →ₜ* GL (Fin 2) A) : framedMap (RingHom.id A) continuous_id ρ = ρ :=
  framedMap_id ρ
