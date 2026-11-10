/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Almost complex structures on quotient spaces

An invariant real subspace of an almost complex vector space has an almost complex quotient.
The quotient projection intertwines the two structures. In particular this constructs the
complex structure on the normal quotient of a pseudoholomorphic immersion, without a metric
or a choice of complement.
-/

public section

namespace TauCeti.AlmostComplexStructure

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The almost complex structure induced on the quotient by an invariant real subspace. -/
def quotient (J : AlmostComplexStructure V) (p : Submodule ℝ V)
    (hp : ∀ v ∈ p, J v ∈ p) : AlmostComplexStructure (V ⧸ p) where
  toLinearMap := p.mapQ p J.toLinearMap hp
  square_neg := by
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := p.mkQ_surjective v
    simp [Submodule.mapQ_apply, J.apply_apply]

/-- On a quotient class the induced structure applies the original structure to a lift. -/
@[simp]
theorem quotient_mk (J : AlmostComplexStructure V) (p : Submodule ℝ V)
    (hp : ∀ v ∈ p, J v ∈ p) (v : V) :
    J.quotient p hp (Submodule.Quotient.mk v) = Submodule.Quotient.mk (J v) := (rfl)

/-- The quotient projection is complex linear. -/
theorem isComplexLinearMap_mkQ (J : AlmostComplexStructure V) (p : Submodule ℝ V)
    (hp : ∀ v ∈ p, J v ∈ p) :
    IsComplexLinearMap J (J.quotient p hp) p.mkQ := by
  exact (isComplexLinearMap_iff_apply _ _ _).2 fun _ ↦ rfl

/-- The quotient structure is characterized by complex linearity of the quotient projection. -/
theorem quotient_eq_iff (J : AlmostComplexStructure V) (p : Submodule ℝ V)
    (hp : ∀ v ∈ p, J v ∈ p) (K : AlmostComplexStructure (V ⧸ p)) :
    J.quotient p hp = K ↔ IsComplexLinearMap J K p.mkQ := by
  constructor
  · rintro rfl
    exact J.isComplexLinearMap_mkQ p hp
  · intro h
    ext v
    obtain ⟨w, rfl⟩ := p.mkQ_surjective v
    exact (isComplexLinearMap_iff_apply _ _ _).1 h w

end TauCeti.AlmostComplexStructure
