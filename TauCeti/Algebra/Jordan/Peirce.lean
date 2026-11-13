/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.Algebra.Jordan.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic

import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

/-!
# Peirce decomposition at an idempotent

The Jordan identity implies `2L³ - 3L² + L = 0` for multiplication by an idempotent.
Its Lagrange projections give a unique decomposition into the `1`, `⅟2` and `0` spaces.
The base ring need only have `2` invertible; no unit in the algebra, inner product or
finite dimension is required.

The projection proofs are adapted from Bryan Ehrlich's euclidean-jordan,
`EuclideanJordan/Peirce.lean`, `PeirceMul.lean` and `Orthogonal.lean` at a83407e4.
The linearization already in Mathlib replaces the source's polarization argument.

## References

* Faraut and Korányi, *Analysis on Symmetric Cones*, Proposition IV.1.1.
* McCrimmon, *A Taste of Jordan Algebras*, §II.8.
-/

public section

namespace TauCeti.Jordan

variable {R J : Type*} [CommRing R] [NonUnitalNonAssocCommRing J] [Module R J]
  [SMulCommClass R J J]

variable (R) in
/-- The Peirce space of eigenvalue `μ` for multiplication by `c`. -/
def peirceSpace (c : J) (μ : R) : Submodule R J := Module.End.eigenspace (LinearMap.mulLeft R c) μ

@[simp]
theorem mem_peirceSpace {c y : J} {μ : R} : y ∈ peirceSpace R c μ ↔ c * y = μ • y :=
  Module.End.mem_eigenspace_iff

variable (R) in
/-- The projection polynomial `2L² - L` onto the `1`-space. -/
def peirceOne (c : J) : J →ₗ[R] J :=
  (2 : R) • ((LinearMap.mulLeft R c).comp (LinearMap.mulLeft R c)) - LinearMap.mulLeft R c

variable (R) in
/-- The projection polynomial `4L - 4L²` onto the half-space. -/
def peirceHalf (c : J) : J →ₗ[R] J :=
  (4 : R) • LinearMap.mulLeft R c -
    (4 : R) • ((LinearMap.mulLeft R c).comp (LinearMap.mulLeft R c))

variable (R) in
/-- The projection polynomial `1 - 3L + 2L²` onto the `0`-space. -/
def peirceZero (c : J) : J →ₗ[R] J :=
  LinearMap.id - (3 : R) • LinearMap.mulLeft R c +
    (2 : R) • ((LinearMap.mulLeft R c).comp (LinearMap.mulLeft R c))

@[simp]
theorem peirceOne_apply (c y : J) : peirceOne R c y = (2 : R) • (c * (c * y)) - c * y := by
  simp [peirceOne]

@[simp]
theorem peirceHalf_apply (c y : J) :
    peirceHalf R c y = (4 : R) • (c * y) - (4 : R) • (c * (c * y)) := by
  simp [peirceHalf]

@[simp]
theorem peirceZero_apply (c y : J) :
    peirceZero R c y = y - (3 : R) • (c * y) + (2 : R) • (c * (c * y)) := by
  simp [peirceZero]

/-- The three projection polynomials resolve the identity, even without idempotence. -/
theorem peirce_add_add (c y : J) : peirceOne R c y + peirceHalf R c y + peirceZero R c y = y := by
  simp only [peirceOne_apply, peirceHalf_apply, peirceZero_apply]
  module

/-- On an eigenvector the projection polynomials act by their scalar values. -/
theorem peirce_of_eigen {c y : J} {μ : R} (h : c * y = μ • y) :
    peirceOne R c y = (2 * μ * μ - μ) • y ∧
    peirceHalf R c y = (4 * μ - 4 * μ * μ) • y ∧
    peirceZero R c y = (1 - 3 * μ + 2 * μ * μ) • y := by
  simp only [peirceOne_apply, peirceHalf_apply, peirceZero_apply, h, mul_smul_comm]
  exact ⟨by module, by module, by module⟩

variable [Invertible (2 : R)]

/-- The projections read off the three Peirce components. -/
theorem peirce_on_spaces {c x y z : J} (hx : c * x = x)
    (hy : c * y = ⅟(2 : R) • y) (hz : c * z = 0) :
    (peirceOne R c x = x ∧ peirceOne R c y = 0 ∧ peirceOne R c z = 0) ∧
    (peirceHalf R c x = 0 ∧ peirceHalf R c y = y ∧ peirceHalf R c z = 0) := by
  have h₁ := peirce_of_eigen (R := R) (μ := 1) (by simpa using hx)
  have hₕ := peirce_of_eigen hy
  have h₀ := peirce_of_eigen (R := R) (c := c) (y := z) (μ := 0) (by simpa using hz)
  have ht : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self _
  have hp : (2 * ⅟(2 : R) * ⅟(2 : R) - ⅟(2 : R)) = 0 := by rw [ht]; ring
  have hh : (4 * ⅟(2 : R) - 4 * ⅟(2 : R) * ⅟(2 : R)) = 1 := by
    linear_combination (1 - 2 * ⅟(2 : R)) * ht
  norm_num only [mul_one, mul_zero, sub_zero, sub_self, zero_sub, zero_smul, one_smul,
    hp, hh] at h₁ hₕ h₀
  exact ⟨⟨h₁.1, hₕ.1, h₀.1⟩, ⟨h₁.2.1, hₕ.2.1, h₀.2.1⟩⟩

variable [IsCommJordan J]

omit [SMulCommClass R J J] in
/-- The Peirce polynomial `2L³ - 3L² + L = 0`, evaluated at `y`. -/
theorem peirce_poly {c : J} (hc : c * c = c) (y : J) :
    (2 : R) • (c * (c * (c * y))) + c * y = (3 : R) • (c * (c * y)) := by
  have h := DFunLike.congr_fun (two_nsmul_lie_lmul_lmul_add_add_eq_zero c c y) c
  -- Evaluating the additive endomorphism commutators uses their definitional operations.
  change (2 : ℕ) • (c * (c * y * c) - c * y * (c * c) +
    (c * (y * c * c) - y * c * (c * c)) +
    (y * (c * c * c) - c * c * (y * c))) = 0 at h
  simp only [hc, mul_comm y c, mul_comm (c * y) c] at h
  have h' := congrArg (⅟(2 : R) • ·) h
  simp only [← Nat.cast_smul_eq_nsmul R, Nat.cast_ofNat, invOf_smul_smul, smul_zero] at h'
  rw [← sub_eq_zero]
  convert h' using 1; module

omit [SMulCommClass R J J] in
/-- The polynomial solved for twice the cube, without dividing scalars in subsequent proofs. -/
theorem peirce_twice_cube {c : J} (hc : c * c = c) (y : J) :
    (2 : R) • (c * (c * (c * y))) = (3 : R) • (c * (c * y)) - c * y :=
  eq_sub_of_add_eq (peirce_poly hc y)

/-- The first projection takes values in the `1`-space. -/
theorem mul_peirceOne {c : J} (hc : c * c = c) (y : J) :
    c * peirceOne R c y = peirceOne R c y := by
  simp only [peirceOne_apply, mul_sub, mul_smul_comm, peirce_twice_cube hc]
  module

/-- The half projection takes values in the half-space. -/
theorem mul_peirceHalf {c : J} (hc : c * c = c) (y : J) :
    c * peirceHalf R c y = ⅟(2 : R) • peirceHalf R c y := by
  apply (smul_eq_iff_eq_invOf_smul (c := (2 : R))).mp
  simp only [peirceHalf_apply, mul_sub, mul_smul_comm]
  simp only [smul_sub, smul_smul]
  -- Reorder the scalar factors to apply the twice-cube identity.
  simp only [show (2 : R) * 4 = 4 * 2 by ring, mul_smul, peirce_twice_cube hc]
  module

/-- The last projection takes values in the `0`-space. -/
theorem mul_peirceZero {c : J} (hc : c * c = c) (y : J) : c * peirceZero R c y = 0 := by
  simp only [peirceZero_apply, mul_add, mul_sub, mul_smul_comm, peirce_twice_cube hc]
  module

/-- Each Peirce projection is idempotent. -/
theorem peirce_idempotent {c : J} (hc : c * c = c) (y : J) :
    peirceOne R c (peirceOne R c y) = peirceOne R c y ∧
    peirceHalf R c (peirceHalf R c y) = peirceHalf R c y ∧
    peirceZero R c (peirceZero R c y) = peirceZero R c y := by
  have h := peirce_on_spaces (R := R) (mul_peirceOne (R := R) hc y)
    (mul_peirceHalf (R := R) hc y) (mul_peirceZero (R := R) hc y)
  refine ⟨h.1.1, h.2.2.1, ?_⟩
  simpa only [h.1.2.2, h.2.2.2, zero_add] using peirce_add_add (R := R) c (peirceZero R c y)

/-- Every element is a sum of elements of the three Peirce spaces. -/
theorem exists_peirce_decomposition {c : J} (hc : c * c = c) (y : J) :
    ∃ x ∈ peirceSpace R c 1, ∃ h ∈ peirceSpace R c ⅟(2 : R),
      ∃ z ∈ peirceSpace R c 0, y = x + h + z := by
  exact ⟨peirceOne R c y, by simpa only [mem_peirceSpace, one_smul] using mul_peirceOne hc y,
    peirceHalf R c y, by exact mem_peirceSpace.mpr (mul_peirceHalf hc y),
    peirceZero R c y, by simpa only [mem_peirceSpace, zero_smul] using mul_peirceZero hc y,
    (peirce_add_add c y).symm⟩

omit [IsCommJordan J] in
/-- A zero sum of Peirce components has all components zero: the sum is internal. -/
theorem peirce_eq_zero_of_add_eq_zero {c x y z : J} (hx : c * x = x)
    (hy : c * y = ⅟(2 : R) • y) (hz : c * z = 0) (h : x + y + z = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  obtain ⟨⟨hxx, hxy, hxz⟩, ⟨hyx, hyy, hyz⟩⟩ := peirce_on_spaces hx hy hz
  have h₁ := congrArg (peirceOne R c) h
  have h₂ := congrArg (peirceHalf R c) h
  simp only [map_add, map_zero, hxx, hxy, hxz, add_zero] at h₁
  simp only [map_add, map_zero, hyx, hyy, hyz, zero_add, add_zero] at h₂
  exact ⟨h₁, h₂, by simpa [h₁, h₂] using h⟩

include R in
omit [SMulCommClass R J J] in
/-- The fully linearized Jordan identity over a ring with `2` invertible. -/
theorem linearized (a b c d : J) :
    a * (b * c * d) - b * c * (a * d) + (b * (c * a * d) - c * a * (b * d)) +
      (c * (a * b * d) - a * b * (c * d)) = 0 := by
  have h := DFunLike.congr_fun (two_nsmul_lie_lmul_lmul_add_add_eq_zero a b c) d
  simp only [Ring.lie_def] at h
  -- Endomorphism evaluation is definitionally compatible with addition and composition.
  change (2 : ℕ) • (a * (b * c * d) - b * c * (a * d) +
    (b * (c * a * d) - c * a * (b * d)) +
    (c * (a * b * d) - a * b * (c * d))) = 0 at h
  simpa only [← Nat.cast_smul_eq_nsmul R, Nat.cast_ofNat, invOf_smul_smul, smul_zero]
    using congrArg (⅟(2 : R) • ·) h

include R in
omit [SMulCommClass R J J] in
/-- Multiplication by an element of either extreme Peirce space commutes with `L_c`. -/
theorem mul_comm_of_eigen_extreme {c x : J} (hc : c * c = c)
    (hx : c * x = x ∨ c * x = 0) (w : J) : c * (x * w) = x * (c * w) := by
  have h := linearized (R := R) c c x w
  rcases hx with hx | hx
  · simp only [hc, mul_comm x c, hx] at h
    apply sub_eq_zero.mp
    convert h using 1; abel
  · simpa only [hc, mul_comm x c, hx, zero_mul, mul_zero, sub_self, zero_add,
      sub_eq_zero, eq_comm] using h

/-- The extreme Peirce spaces are closed under multiplication. -/
theorem eigen_extreme_mul {c x y : J} {μ : R} (hc : c * c = c)
    (hx : c * x = x ∨ c * x = 0) (hy : c * y = μ • y) :
    c * (x * y) = μ • (x * y) := by
  rw [mul_comm_of_eigen_extreme (R := R) hc hx, hy, mul_smul_comm]

include R in
omit [SMulCommClass R J J] in
/-- The `1`-space annihilates the `0`-space. -/
theorem eigen_one_mul_zero {c x y : J} (hc : c * c = c) (hx : c * x = x)
    (hy : c * y = 0) : x * y = 0 := by
  have h₀ : c * (x * y) = 0 := by
    rw [mul_comm_of_eigen_extreme (R := R) hc (Or.inl hx), hy, mul_zero]
  have h₁ : c * (x * y) = x * y := by
    rw [mul_comm x y, mul_comm_of_eigen_extreme (R := R) hc (Or.inr hy), hx, mul_comm y x]
  exact h₁.symm.trans h₀

/-- A product of half-space elements has zero half-component. -/
theorem peirceHalf_mul_half_eq_zero {c x y : J} (hc : c * c = c)
    (hx : c * x = ⅟(2 : R) • x) (hy : c * y = ⅟(2 : R) • y) :
    peirceHalf R c (x * y) = 0 := by
  have h := linearized (R := R) c y x c
  simp only [hc, mul_comm y c, mul_comm x c, mul_comm (x * y) c, mul_comm y x,
    hx, hy, mul_smul_comm, mul_comm (⅟(2 : R) • x) c,
    mul_comm (⅟(2 : R) • y) c, mul_comm (⅟(2 : R) • x) y,
    mul_comm (⅟(2 : R) • y) x] at h
  have he : c * (c * (x * y)) = c * (x * y) := by
    apply sub_eq_zero.mp
    convert h using 1; module
  simp only [peirceHalf_apply, he, sub_self]

include R in
omit [SMulCommClass R J J] in
/-- The `1`- and `0`-space multiplication operators commute. -/
theorem opCommute_eigen_one_zero {c x y : J} (hc : c * c = c) (hx : c * x = x)
    (hy : c * y = 0) (w : J) : x * (y * w) = y * (x * w) := by
  have h := linearized (R := R) x y c w
  simp only [eigen_one_mul_zero (R := R) hc hx hy, mul_comm y c, hx, hy,
    zero_mul, mul_zero, sub_self, zero_add, add_zero] at h
  exact (sub_eq_zero.mp h).symm

end TauCeti.Jordan
