/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.Bialgebra
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Structure
public import TauCeti.RingTheory.MvPolynomial.Finrank
import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# Homogeneous matrix-coordinate coalgebras

Matrix multiplication is linear in each of its two factors. Consequently comultiplication
carries a homogeneous polynomial of degree `d` to the tensor square of the degree-`d`
polynomials. These finite free coalgebras are the coefficient coalgebras for homogeneous
polynomial representations of the matrix monoid and the general linear group.

The ambient bialgebra is `MatrixMonoid.coordinateBialgebra`, with matrix-multiplication
comultiplication, rather than the group-like bialgebra on the underlying monoid algebra.
The underlying modules and their monomial bases come from `homogeneousSubmodule` and
`TauCeti.homogeneousMonomialBasis`. The construction works over arbitrary commutative rings,
including size zero and degree zero.

## References

* J. A. Green, *Polynomial Representations of GLₙ*, §1, the coalgebras `A(n, d)`.
-/

public section

open scoped TensorProduct
open MvPolynomial

namespace TauCeti.MatrixMonoid

section Semiring

variable (R : Type*) [CommSemiring R] (n : ℕ)

private theorem comul_homogeneous_one :
    (homogeneousSubmodule (Fin n × Fin n) R 1).map (comul R n).toLinearMap ≤
      Submodule.map₂ (TensorProduct.mk R (CoordinateRing R n) (CoordinateRing R n))
        (homogeneousSubmodule (Fin n × Fin n) R 1)
        (homogeneousSubmodule (Fin n × Fin n) R 1) := by
  nth_rw 1 [homogeneousSubmodule_one_eq_span_X]
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨⟨i, j⟩, rfl⟩, rfl⟩
  rw [AlgHom.toLinearMap_apply, comul_X]
  exact Submodule.sum_mem _ fun k _ ↦
    Submodule.apply_mem_map₂ _ (isHomogeneous_X R (i, k)) (isHomogeneous_X R (k, j))

/-- Matrix comultiplication preserves homogeneous degree separately in both tensor factors. -/
theorem comul_mem_homogeneous_tensorSquare {d : ℕ} {p : CoordinateRing R n}
    (hp : p.IsHomogeneous d) :
    comul R n p ∈
      Submodule.map₂ (TensorProduct.mk R (CoordinateRing R n) (CoordinateRing R n))
        (homogeneousSubmodule (Fin n × Fin n) R d)
        (homogeneousSubmodule (Fin n × Fin n) R d) := by
  suffices h : ∀ d, (homogeneousSubmodule (Fin n × Fin n) R d).map
      (comul R n).toLinearMap ≤
        Submodule.map₂ (TensorProduct.mk R (CoordinateRing R n) (CoordinateRing R n))
          (homogeneousSubmodule (Fin n × Fin n) R d)
          (homogeneousSubmodule (Fin n × Fin n) R d) from h d ⟨p, hp, rfl⟩
  intro d
  induction d with
  | zero =>
    rw [homogeneousSubmodule_zero, Submodule.one_eq_span, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, rfl, rfl⟩
    rw [AlgHom.toLinearMap_apply, map_one, Algebra.TensorProduct.one_def]
    exact Submodule.apply_mem_map₂ _
      (Submodule.mem_span_singleton_self (1 : CoordinateRing R n))
      (Submodule.mem_span_singleton_self (1 : CoordinateRing R n))
  | succ d ih =>
    nth_rw 1 [← homogeneousSubmodule_one_pow (σ := Fin n × Fin n) (R := R) (d + 1)]
    rw [pow_succ, Submodule.map_mul, homogeneousSubmodule_one_pow]
    exact (mul_le_mul' ih (comul_homogeneous_one R n)).trans
      ((Submodule.map₂_tmul_mul_le _ _ _ _).trans
        (Submodule.map₂_le_map₂ (homogeneousSubmodule_mul d 1)
          (homogeneousSubmodule_mul d 1)))

end Semiring

section Ring

variable (R : Type*) [CommRing R] (n : ℕ)

/-- The subcoalgebra of homogeneous degree-`d` matrix coordinates. -/
noncomputable def homogeneousSubcoalgebra (d : ℕ) :
    Subcoalgebra R (coordinateBialgebra R n) :=
  Subcoalgebra.ofSubmodule
    ((homogeneousSubmodule (Fin n × Fin n) R d).map
      (coordinateBialgebraAlgEquiv R n).toLinearMap) (by
    rintro _ ⟨p, hp, rfl⟩
    rw [TensorProduct.range_mapIncl, AlgEquiv.toLinearMap_apply, coordinateBialgebra_comul_apply]
    have h : Submodule.map₂
        (TensorProduct.mk R (CoordinateRing R n) (CoordinateRing R n))
        (homogeneousSubmodule (Fin n × Fin n) R d)
        (homogeneousSubmodule (Fin n × Fin n) R d) ≤
        (Submodule.map₂ (TensorProduct.mk R (coordinateBialgebra R n)
          (coordinateBialgebra R n))
          ((homogeneousSubmodule (Fin n × Fin n) R d).map
            (coordinateBialgebraAlgEquiv R n).toLinearMap)
          ((homogeneousSubmodule (Fin n × Fin n) R d).map
            (coordinateBialgebraAlgEquiv R n).toLinearMap)).comap
          (Algebra.TensorProduct.map (coordinateBialgebraAlgEquiv R n).toAlgHom
            (coordinateBialgebraAlgEquiv R n).toAlgHom).toLinearMap := by
      apply Submodule.map₂_le.mpr
      intro x hx y hy
      exact Submodule.apply_mem_map₂ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact h (comul_mem_homogeneous_tensorSquare R n hp))

/-- The underlying module consists exactly of the homogeneous matrix coordinates. -/
@[simp]
theorem homogeneousSubcoalgebra_toSubmodule (d : ℕ) :
    (homogeneousSubcoalgebra R n d).toSubmodule =
      (homogeneousSubmodule (Fin n × Fin n) R d).map
        (coordinateBialgebraAlgEquiv R n).toLinearMap := (rfl)

/-- Membership in the homogeneous coordinate coalgebra is ordinary polynomial homogeneity. -/
@[simp]
theorem mem_homogeneousSubcoalgebra (d : ℕ) (p : CoordinateRing R n) :
    coordinateBialgebraAlgEquiv R n p ∈ homogeneousSubcoalgebra R n d ↔
      p.IsHomogeneous d := by
  rw [← Subcoalgebra.mem_toSubmodule, homogeneousSubcoalgebra_toSubmodule,
    Submodule.mem_map]
  exact ⟨fun ⟨q, hq, hqp⟩ ↦ (coordinateBialgebraAlgEquiv R n).injective hqp ▸ hq,
    fun hp ↦ ⟨p, hp, rfl⟩⟩

/-- Homogeneous polynomials identify linearly with the homogeneous coordinate coalgebra. -/
noncomputable def homogeneousSubcoalgebraEquiv (d : ℕ) :
    homogeneousSubmodule (Fin n × Fin n) R d ≃ₗ[R]
      (homogeneousSubcoalgebra R n d).toSubmodule :=
  ((coordinateBialgebraAlgEquiv R n).toLinearEquiv.submoduleMap
    (homogeneousSubmodule (Fin n × Fin n) R d)).trans
      (LinearEquiv.ofEq _ _ (homogeneousSubcoalgebra_toSubmodule R n d).symm)

/-- The homogeneous-coordinate equivalence includes a polynomial by the ambient coordinate map. -/
@[simp]
theorem coe_homogeneousSubcoalgebraEquiv (d : ℕ)
    (p : homogeneousSubmodule (Fin n × Fin n) R d) :
    (homogeneousSubcoalgebraEquiv R n d p : coordinateBialgebra R n) =
      coordinateBialgebraAlgEquiv R n p := (rfl)

/-- The inverse homogeneous-coordinate equivalence recovers the underlying polynomial. -/
@[simp]
theorem coe_homogeneousSubcoalgebraEquiv_symm (d : ℕ)
    (p : (homogeneousSubcoalgebra R n d).toSubmodule) :
    ((homogeneousSubcoalgebraEquiv R n d).symm p : CoordinateRing R n) =
      (coordinateBialgebraAlgEquiv R n).symm (p : coordinateBialgebra R n) := (rfl)

instance (d : ℕ) : Module.Finite R (homogeneousSubcoalgebra R n d).toSubmodule :=
  Module.Finite.equiv (homogeneousSubcoalgebraEquiv R n d)

instance (d : ℕ) : Module.Free R (homogeneousSubcoalgebra R n d).toSubmodule :=
  Module.Free.of_equiv (homogeneousSubcoalgebraEquiv R n d)

/-- The homogeneous matrix-coordinate coalgebra, with its inherited comultiplication and counit. -/
noncomputable instance homogeneousSubcoalgebraCoalgebra (d : ℕ) :
    Coalgebra R (homogeneousSubcoalgebra R n d).toSubmodule := by
  letI : Module.Free R (coordinateBialgebra R n) :=
    Module.Free.of_equiv (coordinateBialgebraAlgEquiv R n).toLinearEquiv
  exact (homogeneousSubcoalgebra R n d).coalgebra

/-- The monomial basis of the homogeneous matrix-coordinate coalgebra. -/
noncomputable def homogeneousSubcoalgebraBasis (d : ℕ) :
    Module.Basis {s : (Fin n × Fin n) →₀ ℕ // s.degree = d} R
      (homogeneousSubcoalgebra R n d).toSubmodule :=
  (homogeneousMonomialBasis d).map (homogeneousSubcoalgebraEquiv R n d)

/-- A homogeneous coordinate basis vector is its named matrix monomial. -/
@[simp]
theorem coe_homogeneousSubcoalgebraBasis (d : ℕ)
    (s : {s : (Fin n × Fin n) →₀ ℕ // s.degree = d}) :
    (homogeneousSubcoalgebraBasis R n d s : coordinateBialgebra R n) =
      coordinateBialgebraAlgEquiv R n (monomial s.1 1) := by
  simp [homogeneousSubcoalgebraBasis]

/-- A matrix-entry coordinate, as an element of the degree-one coalgebra. -/
noncomputable def homogeneousEntry (i j : Fin n) :
    (homogeneousSubcoalgebra R n 1).toSubmodule :=
  homogeneousSubcoalgebraEquiv R n 1 ⟨X (i, j), isHomogeneous_X R (i, j)⟩

/-- The inclusion of a degree-one entry is the corresponding polynomial variable. -/
@[simp]
theorem coe_homogeneousEntry (i j : Fin n) :
    (homogeneousEntry R n i j : coordinateBialgebra R n) =
      coordinateBialgebraAlgEquiv R n (X (i, j)) := by
  simp [homogeneousEntry]

/-- Degree-one matrix coordinates have the usual matrix-coalgebra comultiplication.

Use this as an explicit rewrite: the generic subcoalgebra simp rule first expresses
comultiplication as `Subcoalgebra.comulLinearMap`. -/
theorem comul_homogeneousEntry (i j : Fin n) :
    Coalgebra.comul (R := R) (homogeneousEntry R n i j) =
      ∑ k, homogeneousEntry R n i k ⊗ₜ[R] homogeneousEntry R n k j := by
  let : Module.Free R (coordinateBialgebra R n) :=
    Module.Free.of_equiv (coordinateBialgebraAlgEquiv R n).toLinearEquiv
  apply TensorProduct.map_injective_of_flat_flat
    (homogeneousSubcoalgebra R n 1).toSubmodule.subtype
    (homogeneousSubcoalgebra R n 1).toSubmodule.subtype
    Subtype.val_injective Subtype.val_injective
  simp

/-- The rank of the degree-`d` matrix-coordinate coalgebra. -/
@[simp]
theorem finrank_homogeneousSubcoalgebra [StrongRankCondition R] (d : ℕ) :
    Module.finrank R (homogeneousSubcoalgebra R n d).toSubmodule =
      (n * n).multichoose d := by
  rw [← (homogeneousSubcoalgebraEquiv R n d).finrank_eq,
    finrank_homogeneousSubmodule_eq_multichoose]
  simp

end Ring

end TauCeti.MatrixMonoid
