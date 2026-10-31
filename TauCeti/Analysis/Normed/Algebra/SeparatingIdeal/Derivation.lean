/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.SeparatingIdeal.Radical
public import TauCeti.RingTheory.Jacobson.Basic

/-!
# Automatic continuity of derivations on semisimple Banach algebras

A derivation of an algebra `B` is a linear map `D : B → B` satisfying the Leibniz rule
`D (x * y) = x * D y + D x * y`; here `B` need not be commutative, so Mathlib's `Derivation`,
which requires a commutative algebra, does not apply, and the Leibniz rule is a hypothesis on a
linear map. This file proves the theorem of Johnson and Sinclair: every derivation of a
semisimple complex Banach algebra is continuous, with no continuity assumption on `D`.

The separating space `S(D)` of a derivation is a separating ideal, because the commutators of `D`
with left and right multiplication by `b` are multiplications by `D b`. In a semisimple algebra
a separating ideal is finite-dimensional. A finite-dimensional separating space squares to zero:
if `q, s ∈ S(D)`, take `x n → 0` with `D (x n) → s`. Then `q * x n` lies in the
finite-dimensional space `S(D)`, on which `D` is continuous, so
`q * D (x n) = D (q * x n) - D q * x n → 0`, while `q * D (x n) → q * s`. Consequently every
product `b * s` with `s ∈ S(D)` is nilpotent, so `S(D)` lies in the Jacobson radical, which is
zero.

## Main results

* `LinearMap.isSeparatingIdeal_separatingSpace_of_derivation`: the separating space of a
  derivation of a Banach algebra is a separating ideal.
* `LinearMap.mul_eq_zero_of_derivation_of_mem_separatingSpace`: a finite-dimensional separating
  space of a derivation squares to zero.
* `LinearMap.continuous_of_derivation_of_jacobson_eq_bot`: a derivation of a unital semisimple
  complex Banach algebra is continuous.

## References

* B. E. Johnson and A. M. Sinclair, *Continuity of derivations and a problem of Kaplansky*,
  Amer. J. Math. 90 (1968), 1067–1073.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §5.2: separating ideals and the
  automatic continuity of derivations.
-/

public section

namespace LinearMap

section Field

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing B] [NormedSpace 𝕜 B]
  [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B]

/-- **The separating space of a derivation is a separating ideal.** If `D : B → B` is a linear
map on a Banach algebra satisfying the Leibniz rule `D (x * y) = x * D y + D x * y`, not assumed
continuous, then the separating space of `D` is a separating ideal of `B`. -/
theorem isSeparatingIdeal_separatingSpace_of_derivation [CompleteSpace B] (D : B →ₗ[𝕜] B)
    (hD : ∀ x y, D (x * y) = x * D y + D x * y) : D.separatingSpace.IsSeparatingIdeal :=
  -- The commutators of `D` with multiplication by `b` are multiplications by `D b`.
  D.isSeparatingIdeal_separatingSpace (ContinuousLinearMap.mul 𝕜 B)
    (fun b ↦ (ContinuousLinearMap.mul 𝕜 B).flip b)
    (fun b ↦ (continuous_const_mul (D b)).congr fun x ↦ by simp [hD])
    (fun b ↦ (continuous_mul_const (D b)).congr fun x ↦ by simp [hD])

/-- **A finite-dimensional separating space of a derivation squares to zero.** If `D : B → B` is
a linear map on a normed algebra over a complete field satisfying the Leibniz rule, not assumed
continuous, and its separating space is finite-dimensional, then `q * s = 0` for all `q` and `s`
in the separating space. -/
theorem mul_eq_zero_of_derivation_of_mem_separatingSpace [CompleteSpace 𝕜] (D : B →ₗ[𝕜] B)
    (hD : ∀ x y, D (x * y) = x * D y + D x * y) [FiniteDimensional 𝕜 D.separatingSpace]
    {q s : B} (hq : q ∈ D.separatingSpace) (hs : s ∈ D.separatingSpace) : q * s = 0 := by
  let M : B →L[𝕜] B →L[𝕜] B := ContinuousLinearMap.mul 𝕜 B
  -- The separating space is a right ideal: `y ↦ D y * x - D (y * x) = -(y * D x)` is continuous.
  have hqM (x : B) : M q x ∈ D.separatingSpace :=
    D.map_separatingSpace_le_of_continuous_sub D (M.flip x) (M.flip x)
      ((continuous_mul_const (D x)).neg.congr fun y ↦ by simp [M, hD]) ⟨q, hq, rfl⟩
  -- Hence `D ∘ (q * ·)` factors through the finite-dimensional separating space, so it is
  -- continuous and has zero separating space.
  have hc : Continuous (D ∘ₗ (M q : B →ₗ[𝕜] B)) :=
    ((D ∘ₗ D.separatingSpace.subtype).continuous_of_finiteDimensional.comp
      ((M q).codRestrict D.separatingSpace hqM).continuous).congr fun x ↦ by simp [M]
  -- It differs from `(q * ·) ∘ D` by the continuous map `x ↦ -(D q * x)`.
  have hsub : Continuous ((M q : B →ₗ[𝕜] B) ∘ₗ D - D ∘ₗ (M q : B →ₗ[𝕜] B)) :=
    (continuous_const_mul (D q)).neg.congr fun x ↦ by simp [M, hD]
  have h := D.map_separatingSpace_le (M q) ⟨s, hs, rfl⟩
  rw [separatingSpace_eq_of_continuous_sub hsub, separatingSpace_eq_bot_of_continuous _ hc] at h
  simpa [M] using h

end Field

/-- **Johnson–Sinclair theorem: derivations of semisimple Banach algebras are continuous.** Let
`B` be a unital complex Banach algebra with zero Jacobson radical. Every linear map `D : B → B`
satisfying the Leibniz rule `D (x * y) = x * D y + D x * y` is continuous. -/
theorem continuous_of_derivation_of_jacobson_eq_bot {B : Type*} [NormedRing B]
    [NormedAlgebra ℂ B] [CompleteSpace B] (D : B →ₗ[ℂ] B)
    (hD : ∀ x y, D (x * y) = x * D y + D x * y) (hB : Ring.jacobson B = ⊥) : Continuous D := by
  have hJ := D.isSeparatingIdeal_separatingSpace_of_derivation hD
  have := hJ.finiteDimensional_of_jacobson_eq_bot hB
  rw [continuous_iff_separatingSpace_eq_bot, Submodule.eq_bot_iff]
  intro s hs
  -- Every `y * s` squares to zero, so `s` lies in the Jacobson radical.
  have hsJ : s ∈ Ring.jacobson B :=
    TauCeti.Ring.mem_jacobson_iff_isUnit_one_add_mul_left.2 fun y ↦ IsNilpotent.isUnit_one_add
      ⟨2, by rw [pow_two, mul_assoc,
        D.mul_eq_zero_of_derivation_of_mem_separatingSpace hD hs (hJ.mul_mem_left y hs),
        mul_zero]⟩
  rwa [hB, Ideal.mem_bot] at hsJ

end LinearMap
