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

/-- The underlying endomorphism is the map induced on the quotient. -/
theorem quotient_toLinearMap (J : AlmostComplexStructure V) (p : Submodule ℝ V)
    (hp : ∀ v ∈ p, J v ∈ p) :
    (J.quotient p hp).toLinearMap = p.mapQ p J.toLinearMap hp := (rfl)

/-- On a quotient class the induced structure applies the original structure to a lift. -/
@[simp]
theorem quotient_mk (J : AlmostComplexStructure V) (p : Submodule ℝ V)
    (hp : ∀ v ∈ p, J v ∈ p) (v : V) :
    J.quotient p hp (Submodule.Quotient.mk v) = Submodule.Quotient.mk (J v) := by
  simp [quotient]

/-- The quotient projection is complex linear. -/
@[simp]
theorem isComplexLinearMap_mkQ (J : AlmostComplexStructure V) (p : Submodule ℝ V)
    (hp : ∀ v ∈ p, J v ∈ p) :
    IsComplexLinearMap J (J.quotient p hp) p.mkQ := by
  simp [isComplexLinearMap_iff_apply]

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
    rw [← (isComplexLinearMap_iff_apply _ _ _).1 h w]
    simp

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- Complex linearity out of a quotient can be tested after the quotient projection. -/
theorem isComplexLinearMap_comp_mkQ_iff (J : AlmostComplexStructure V)
    (p : Submodule ℝ V) (hp : ∀ v ∈ p, J v ∈ p) (K : AlmostComplexStructure W)
    (f : V ⧸ p →ₗ[ℝ] W) :
    IsComplexLinearMap J K (f.comp p.mkQ) ↔ IsComplexLinearMap (J.quotient p hp) K f := by
  simp only [isComplexLinearMap_iff_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
  constructor
  · intro h v
    obtain ⟨w, rfl⟩ := p.mkQ_surjective v
    simpa using h w
  · intro h v
    simpa using h (p.mkQ v)

/-- The quotient lift is complex-linear exactly when the original map is. -/
@[simp]
theorem isComplexLinearMap_liftQ_iff (J : AlmostComplexStructure V)
    (p : Submodule ℝ V) (hp : ∀ v ∈ p, J v ∈ p) (K : AlmostComplexStructure W)
    (f : V →ₗ[ℝ] W) (hf : p ≤ LinearMap.ker f) :
    IsComplexLinearMap (J.quotient p hp) K (p.liftQ f hf) ↔ IsComplexLinearMap J K f := by
  rw [← isComplexLinearMap_comp_mkQ_iff]
  simp

end TauCeti.AlmostComplexStructure

namespace TauCeti

/-- A complex-linear map preserving invariant submodules induces a complex-linear quotient map. -/
theorem IsComplexLinearMap.mapQ {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {J : AlmostComplexStructure V} {K : AlmostComplexStructure W} {f : V →ₗ[ℝ] W}
    (h : IsComplexLinearMap J K f) (p : Submodule ℝ V) (q : Submodule ℝ W)
    (hp : ∀ v ∈ p, J v ∈ p) (hq : ∀ w ∈ q, K w ∈ q) (hf : p ≤ q.comap f) :
    IsComplexLinearMap (J.quotient p hp) (K.quotient q hq) (p.mapQ q f hf) := by
  rw [← AlmostComplexStructure.isComplexLinearMap_comp_mkQ_iff]
  rw [Submodule.mapQ_mkQ]
  exact (K.isComplexLinearMap_mkQ q hq).comp h

end TauCeti
