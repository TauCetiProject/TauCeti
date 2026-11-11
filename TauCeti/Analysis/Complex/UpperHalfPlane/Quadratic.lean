/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PeriodPair
public import TauCeti.Algebra.QuadraticAlgebra.PeriodMatrix

/-!
# Multipliers of a principal quadratic period lattice

If `τ ∈ ℍ` satisfies `τ² + Bτ + C = 0` with integral coefficients, the lattice
`ℤ τ + ℤ` is a subalgebra of `ℂ`. It is exactly the ring of complex scalars preserving that
lattice, and evaluation at `τ` identifies it with `QuadraticAlgebra ℤ (-C) (-B)`.
These are scalar endomorphisms of the lattice; no algebraic elliptic-curve comparison is asserted.

The multiplication matrix uses row coordinates in the ordered periods `(τ, 1)`, as for division
points of a complex torus. Thus multiplication by `t + sτ` sends a row `r` to
`r * !![t - B*s, -C*s; s, t]`. The construction reuses the native regular representation of
`QuadraticAlgebra`, reversing its basis `(1, ω)` and transposing to the row convention.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, Chapter 11, for the lattice description of complex
  multiplication.
* D. H. Shin, *Generation of class fields by Siegel-Ramachandra invariants*, §2, for the
  multiplication matrices in the row-coordinate convention.
-/

public section

noncomputable section

open Complex Matrix

namespace UpperHalfPlane

variable (τ : ℍ) {B C : ℤ}

/-- The lattice of a monic integral quadratic point is closed under multiplication. -/
theorem mul_mem_lattice_periodPair_of_quadratic
    (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0) {x y : ℂ}
    (hx : x ∈ τ.periodPair.lattice) (hy : y ∈ τ.periodPair.lattice) :
    x * y ∈ τ.periodPair.lattice := by
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hx
  obtain ⟨p, q, rfl⟩ := PeriodPair.mem_lattice.mp hy
  refine PeriodPair.mem_lattice.mpr ⟨m * q + n * p - B * m * p, n * q - C * m * p, ?_⟩
  simp only [periodPair_ω₁, periodPair_ω₂, mul_one]
  push_cast
  linear_combination -(m : ℂ) * p * hτ

/-- The integral quadratic order carried by the principal lattice `ℤ τ + ℤ`. -/
def quadraticOrder (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0) : Subalgebra ℤ ℂ :=
  τ.periodPair.lattice.toSubalgebra (by simpa using τ.periodPair.ω₂_mem_lattice)
    (fun _ _ hx hy ↦ τ.mul_mem_lattice_periodPair_of_quadratic hτ hx hy)

/-- Membership in the quadratic order is membership in the original period lattice. -/
@[simp]
theorem mem_quadraticOrder (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0) (x : ℂ) :
    x ∈ τ.quadraticOrder hτ ↔ x ∈ τ.periodPair.lattice := Iff.rfl

/-- The quadratic order is precisely the complex scalars preserving the period lattice. -/
theorem mem_quadraticOrder_iff_mul_mem (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0) (x : ℂ) :
    x ∈ τ.quadraticOrder hτ ↔ ∀ y ∈ τ.periodPair.lattice, x * y ∈ τ.periodPair.lattice := by
  constructor
  · intro hx y hy
    exact τ.mul_mem_lattice_periodPair_of_quadratic hτ hx hy
  · intro hx
    simpa using hx 1 (by simpa using τ.periodPair.ω₂_mem_lattice)

/-- Evaluation at `τ` identifies its quadratic algebra with its integral period order. -/
def quadraticOrderEquiv (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0) :
    QuadraticAlgebra ℤ (-C) (-B) ≃ₐ[ℤ] τ.quadraticOrder hτ := by
  let u : τ.quadraticOrder hτ := ⟨τ, by simpa using τ.periodPair.ω₁_mem_lattice⟩
  let f : QuadraticAlgebra ℤ (-C) (-B) →ₐ[ℤ] τ.quadraticOrder hτ :=
    QuadraticAlgebra.lift ⟨u, by
      apply Subtype.ext
      simp [u, zsmul_eq_mul]
      linear_combination hτ⟩
  refine AlgEquiv.ofBijective f ⟨?_, ?_⟩
  · apply (QuadraticAlgebra.lift_injective_iff _).mpr
    apply LinearIndependent.of_comp (τ.quadraticOrder hτ).val.toLinearMap
    have hi := (LinearIndependent.pair_symm_iff).mpr (τ.periodPair.indep.restrict_scalars' ℤ)
    convert hi using 1
    ext i
    fin_cases i <;> simp [u]
  · intro x
    obtain ⟨s, t, hst⟩ := PeriodPair.mem_lattice.mp x.property
    refine ⟨⟨t, s⟩, Subtype.ext ?_⟩
    simpa [f, u, QuadraticAlgebra.lift_apply_apply, add_comm] using hst

/-- Evaluation is `t + sτ` in the native coordinates `(t,s)` of the quadratic algebra. -/
@[simp↓]
theorem coe_quadraticOrderEquiv (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0)
    (z : QuadraticAlgebra ℤ (-C) (-B)) :
    (τ.quadraticOrderEquiv hτ z : ℂ) = z.re + z.im * τ := by
  dsimp only [quadraticOrderEquiv, AlgEquiv.ofBijective, RingEquiv.ofBijective]
  simp [QuadraticAlgebra.lift_apply_apply]

/-- The inverse coordinates recover the unique expression `t + sτ`. -/
theorem quadraticOrderEquiv_symm_apply_eq_iff (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0)
    (x : τ.quadraticOrder hτ) (z : QuadraticAlgebra ℤ (-C) (-B)) :
    (τ.quadraticOrderEquiv hτ).symm x = z ↔ (x : ℂ) = z.re + z.im * τ := by
  rw [AlgEquiv.symm_apply_eq]
  exact Subtype.ext_iff.trans (by rw [coe_quadraticOrderEquiv])

/-- Multiplication acts on row coordinates of division points on the right by the period matrix.
The identity is valid for every complex denominator, including its totalized zero value. -/
theorem quadraticOrderEquiv_mul_divisionPoint
    (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0) (z : QuadraticAlgebra ℤ (-C) (-B))
    (r : Fin 2 → ℤ) (N : ℂ) :
    (τ.quadraticOrderEquiv hτ z : ℂ) * (((r 0 : ℂ) * τ + r 1) / N) =
      ((((r ᵥ* z.periodMulMatrix) 0 : ℂ) * τ + (r ᵥ* z.periodMulMatrix) 1) / N) := by
  rw [coe_quadraticOrderEquiv, QuadraticAlgebra.periodMulMatrix_eq, ← mul_div_assoc]
  congr 1
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  linear_combination (z.im : ℂ) * r 0 * hτ

end UpperHalfPlane
