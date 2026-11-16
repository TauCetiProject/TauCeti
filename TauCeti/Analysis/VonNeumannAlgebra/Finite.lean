/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import TauCeti.Analysis.VonNeumannAlgebra.Basic
import TauCeti.Analysis.CStarAlgebra.DedekindFinite

/-!
# Tracial states and finite von Neumann algebras

Tracial states and von Neumann finiteness underpin the theory of finite and II₁ von Neumann
algebras, in particular proving that discrete group von Neumann algebras `L(Γ)` are finite
(`TauCeti.isFinite_groupVonNeumannAlgebra`). `VonNeumannAlgebra.IsTracialState` packages
normalization, positivity, and traciality; `VonNeumannAlgebra.IsFinite` states that every isometry
in `M` is unitary, which follows from Dedekind-finiteness
(`VonNeumannAlgebra.IsFinite.of_isDedekindFiniteMonoid`) and hence from any projection-faithful
additive trace (`VonNeumannAlgebra.IsFinite.of_tracial`).

## References

* J. Peterson, *Notes on von Neumann Algebras* (2013), §3.2.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, §§2.1 and 6.1.
-/

public section

open scoped ComplexOrder

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A **tracial state** on `M`: a linear functional satisfying `τ 1 = 1`, `0 ≤ τ (star x * x)`,
and `τ (x * y) = τ (y * x)`. -/
structure IsTracialState (M : VonNeumannAlgebra H) (τ : M.toStarSubalgebra →ₗ[ℂ] ℂ) : Prop where
  /-- A tracial state is normalized at `1`. -/
  map_one : τ 1 = 1
  /-- A tracial state is nonnegative on elements of the form `star x * x`. -/
  star_mul_self_nonneg : ∀ x, 0 ≤ τ (star x * x)
  /-- A tracial state vanishes on commutators (`τ (x * y) = τ (y * x)`). -/
  mul_comm : ∀ x y, τ (x * y) = τ (y * x)

theorem isTracialState_def (M : VonNeumannAlgebra H) (τ : M.toStarSubalgebra →ₗ[ℂ] ℂ) :
    M.IsTracialState τ ↔ τ 1 = 1 ∧ (∀ x, 0 ≤ τ (star x * x)) ∧ ∀ x y, τ (x * y) = τ (y * x) :=
  ⟨fun ⟨h1, hpos, htr⟩ => ⟨h1, hpos, htr⟩, fun ⟨h1, hpos, htr⟩ => ⟨h1, hpos, htr⟩⟩

/-- A von Neumann algebra `M` is **finite** when every isometry in `M` is unitary. -/
def IsFinite (M : VonNeumannAlgebra H) : Prop :=
  ∀ v ∈ M, star v * v = 1 → v * star v = 1

theorem isFinite_def (M : VonNeumannAlgebra H) :
    M.IsFinite ↔ ∀ v ∈ M, star v * v = 1 → v * star v = 1 :=
  Iff.rfl

/-- In a finite von Neumann algebra `M`, every isometry `v ∈ M` (`star v * v = 1`) is unitary
(`v * star v = 1`). -/
theorem IsFinite.mul_star_self {M : VonNeumannAlgebra H} (hM : M.IsFinite) {v : H →L[ℂ] H}
    (hv : v ∈ M) (hvv : star v * v = 1) : v * star v = 1 :=
  hM v hv hvv

/-- Any von Neumann algebra whose underlying star subalgebra is Dedekind-finite is finite. -/
theorem IsFinite.of_isDedekindFiniteMonoid (M : VonNeumannAlgebra H)
    [IsDedekindFiniteMonoid M.toStarSubalgebra] : M.IsFinite := fun v hv hvv =>
  congr_arg Subtype.val
    (mul_eq_one_symm (a := (star ⟨v, hv⟩ : M.toStarSubalgebra)) (b := ⟨v, hv⟩) (Subtype.ext hvv))

/-- A von Neumann algebra carrying a projection-faithful additive trace on `M.toStarSubalgebra` is
finite. -/
theorem IsFinite.of_tracial (M : VonNeumannAlgebra H) {F G : Type*} [AddZero G]
    [FunLike F M.toStarSubalgebra G] [AddMonoidHomClass F M.toStarSubalgebra G] (τ : F)
    (htr : ∀ x y, τ (x * y) = τ (y * x))
    (hfaith : ∀ q : M.toStarSubalgebra, IsStarProjection q → τ q = 0 → q = 0) :
    M.IsFinite := by
  have := CStarAlgebra.isDedekindFiniteMonoid_of_tracial τ htr hfaith
  exact IsFinite.of_isDedekindFiniteMonoid M

end VonNeumannAlgebra
