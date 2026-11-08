/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.RingTheory.AlgebraTower
public import TauCeti.Algebra.OreExtension.Basic

/-!
# The quantum plane

For a commutative semiring `R` and a parameter `q : R`, the quantum plane is the `R`-algebra
`R⟨x, y⟩ / (x y - q y x)`. This file constructs it as the Ore extension `R[y][x; σ]` of the
polynomial ring in `y` by the twist `σ(y) = q y`, so that the defining relation is the Ore
commutation rule `x y = σ(y) x = q y x`.

The Ore model gives the normal form directly: the ordered monomials `y^j x^k` form an `R`-basis
(`TauCeti.QuantumPlane.basis`), multiplied by
`(y^j x^k) (y^a x^b) = q^(k a) y^(j + a) x^(k + b)` (`TauCeti.QuantumPlane.basis_mul_basis`).
The universal property (`TauCeti.QuantumPlane.lift`, `TauCeti.QuantumPlane.algHom_ext`) says
that algebra maps out of the quantum plane are exactly the pairs `a, b` with `a b = q b a`, so
this is the quotient of the free algebra on `x, y` by the single relation `x y = q y x`.

The construction is made over an arbitrary commutative semiring, so that it covers both the
quantum plane over a field and its integral form over `ℤ[v, v⁻¹]`. Over `ℂ` it is a module algebra
for the rank-one quantum group `UqSl2 q`; see `TauCeti.QuantumGroups.QuantumPlane.ModuleAlgebra`.

## Main definitions

* `TauCeti.QuantumPlane q`: the quantum plane with parameter `q`.
* `TauCeti.QuantumPlane.x`, `TauCeti.QuantumPlane.y`: its generators.
* `TauCeti.QuantumPlane.basis`: the monomial basis `y^j x^k`.
* `TauCeti.QuantumPlane.lift`: the algebra map determined by a `q`-commuting pair.

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapter IV, for the quantum
  plane and its monomial basis.
-/

public section

noncomputable section

namespace TauCeti

open Polynomial

variable {R : Type*} [CommSemiring R]

namespace QuantumPlane

/-- The twist `y ↦ q y` of the polynomial ring `R[y]`, whose Ore extension is the quantum
plane. -/
def twist (q : R) : R[X] →ₐ[R] R[X] := aeval (C q * X)

/-- The twist multiplies the variable `y` by `q`. -/
theorem twist_X (q : R) : twist q X = q • X := by
  rw [twist, aeval_X, smul_eq_C_mul]

end QuantumPlane

/-- The quantum plane `R⟨x, y⟩ / (x y - q y x)`, realized as the Ore extension `R[y][x; σ]`
with `σ(y) = q y` and no skew derivation. -/
abbrev QuantumPlane (q : R) : Type _ := OreExtension (QuantumPlane.twist q) 0

namespace QuantumPlane

variable (q : R)

/-- The generator `x` of the quantum plane, the Ore variable. -/
def x : QuantumPlane q := OreExtension.X (σ := twist q) (δ := 0)

/-- The generator `y` of the quantum plane, the polynomial variable of the coefficients. -/
def y : QuantumPlane q := OreExtension.C (σ := twist q) (δ := 0) X

/-- The defining relation `x y = q y x` of the quantum plane. -/
theorem x_mul_y : x q * y q = q • (y q * x q) := by
  have h := OreExtension.X_mul_C (σ := twist q) (δ := 0) X
  rw [SigmaDerivation.coe_zero, Pi.zero_apply, map_zero, add_zero, twist_X, map_smul,
    smul_mul_assoc] at h
  exact h

/-- Moving `x^k` past `y^a` produces the factor `q^(k a)`. -/
theorem x_pow_mul_y_pow (k a : ℕ) : x q ^ k * y q ^ a = q ^ (k * a) • (y q ^ a * x q ^ k) := by
  -- First move a single `x` past `y^a`, using that `x` conjugates `y` to `q y`.
  have hx : x q * y q ^ a = q ^ a • (y q ^ a * x q) := by
    have h : SemiconjBy (x q) (y q) (q • y q) := by
      rw [SemiconjBy, smul_mul_assoc]
      exact x_mul_y q
    rw [(h.pow_right a).eq, smul_pow, smul_mul_assoc]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_assoc, hx, mul_smul_comm, ← mul_assoc, ih]
    simp only [smul_mul_assoc, smul_smul, mul_assoc, ← pow_succ, ← pow_add]
    congr 1
    ring

/-- The monomials `y^j x^k`, indexed by `(j, k)`, form a basis of the quantum plane. -/
def basis : Module.Basis (ℕ × ℕ) R (QuantumPlane q) :=
  (Polynomial.basisMonomials R).smulTower OreExtension.monomialBasis

/-- The basis vector indexed by `(j, k)` is the monomial `y^j x^k`. -/
theorem basis_apply (j k : ℕ) : basis q (j, k) = y q ^ j * x q ^ k := by
  simp only [basis, Module.Basis.smulTower_apply, coe_basisMonomials,
    OreExtension.monomialBasis_apply, OreExtension.smul_eq_C_mul, ← OreExtension.X_pow_eq_monomial,
    ← X_pow_eq_monomial, y, x, ← OreExtension.CAlgHom_eq_C, map_pow]

/-- The product of two basis monomials: `(y^j x^k) (y^a x^b) = q^(k a) y^(j + a) x^(k + b)`. -/
@[simp]
theorem basis_mul_basis (j k a b : ℕ) :
    basis q (j, k) * basis q (a, b) = q ^ (k * a) • basis q (j + a, k + b) := by
  simp only [basis_apply, pow_add, mul_assoc]
  rw [← mul_assoc (x q ^ k), x_pow_mul_y_pow]
  simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]

/-- The constant monomial is the unit. -/
@[simp]
theorem basis_zero_zero : basis q (0, 0) = 1 := by
  rw [basis_apply, pow_zero, pow_zero, one_mul]

/-- The generator `x` is the monomial `y^0 x^1`. -/
theorem x_eq_basis : x q = basis q (0, 1) := by
  rw [basis_apply, pow_zero, pow_one, one_mul]

/-- The generator `y` is the monomial `y^1 x^0`. -/
theorem y_eq_basis : y q = basis q (1, 0) := by
  rw [basis_apply, pow_zero, pow_one, mul_one]

section lift

variable {q} {A : Type*} [Semiring A] [Algebra R A] {a b : A}

/-- An element `a` with `a b = q b a` satisfies the Ore commutation rule against the polynomials
in `b`. -/
private theorem mul_aeval_eq (h : a * b = q • (b * a)) (p : R[X]) :
    a * aeval b p = aeval b (twist q p) * a := by
  have hab : SemiconjBy a b (algebraMap R A q * b) := by
    rw [SemiconjBy, mul_assoc, ← Algebra.smul_def]
    exact h
  rw [twist, ← aeval_algHom_apply, map_mul, aeval_C, aeval_X]
  induction p using Polynomial.induction_on' with
  | add p p' hp hp' => rw [map_add, map_add, mul_add, add_mul, hp, hp']
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Algebra.left_comm, (hab.pow_right n).eq, mul_assoc]

variable (a b) in
/-- The algebra map out of the quantum plane sending `x` to `a` and `y` to `b`, for a pair with
`a b = q b a`. -/
def lift (h : a * b = q • (b * a)) : QuantumPlane q →ₐ[R] A :=
  OreExtension.liftAlgHom (aeval b) a fun p => by
    rw [SigmaDerivation.coe_zero, Pi.zero_apply, map_zero, add_zero]
    exact mul_aeval_eq h p

/-- `QuantumPlane.lift` sends `x` to `a`. -/
@[simp]
theorem lift_x (h : a * b = q • (b * a)) : lift a b h (x q) = a :=
  OreExtension.liftAlgHom_X _ _ _

/-- `QuantumPlane.lift` sends `y` to `b`. -/
@[simp]
theorem lift_y (h : a * b = q • (b * a)) : lift a b h (y q) = b :=
  (OreExtension.liftAlgHom_C _ _ _ X).trans (aeval_X b)

/-- Algebra maps out of the quantum plane agree when they agree on `x` and `y`. -/
@[ext]
theorem algHom_ext {f g : QuantumPlane q →ₐ[R] A} (hx : f (x q) = g (x q))
    (hy : f (y q) = g (y q)) : f = g := by
  refine OreExtension.algHom_ext (σ := twist q) (δ := 0) (fun p => ?_) hx
  have : f.comp (OreExtension.CAlgHom (σ := twist q) (δ := 0)) =
      g.comp (OreExtension.CAlgHom (σ := twist q) (δ := 0)) :=
    Polynomial.algHom_ext (by rwa [AlgHom.comp_apply, AlgHom.comp_apply, OreExtension.CAlgHom_eq_C])
  simpa only [AlgHom.comp_apply, OreExtension.CAlgHom_eq_C] using DFunLike.congr_fun this p

end lift

end QuantumPlane

end TauCeti
