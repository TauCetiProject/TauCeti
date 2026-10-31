/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MatrixMonoid.Bialgebra
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
including an empty index type and degree zero.

## References

* J. A. Green, *Polynomial Representations of GLₙ*, §1, the coalgebras `A(n, d)`.
-/

public section

open scoped TensorProduct
open MvPolynomial

namespace TauCeti.MatrixMonoid

section Semiring

variable (R : Type*) [CommSemiring R] (ι : Type*) [Fintype ι]

private theorem comul_homogeneous_one :
    (homogeneousSubmodule (ι × ι) R 1).map (comul R ι).toLinearMap ≤
      Submodule.map₂ (TensorProduct.mk R (CoordinateRing R ι) (CoordinateRing R ι))
        (homogeneousSubmodule (ι × ι) R 1)
        (homogeneousSubmodule (ι × ι) R 1) := by
  nth_rw 1 [homogeneousSubmodule_one_eq_span_X]
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨⟨i, j⟩, rfl⟩, rfl⟩
  rw [AlgHom.toLinearMap_apply, comul_X]
  exact Submodule.sum_mem _ fun k _ ↦
    Submodule.apply_mem_map₂ _ (isHomogeneous_X R (i, k)) (isHomogeneous_X R (k, j))

/-- Matrix comultiplication preserves homogeneous degree separately in both tensor factors. -/
theorem comul_mem_homogeneous_tensorSquare {d : ℕ} {p : CoordinateRing R ι}
    (hp : p.IsHomogeneous d) :
    comul R ι p ∈
      Submodule.map₂ (TensorProduct.mk R (CoordinateRing R ι) (CoordinateRing R ι))
        (homogeneousSubmodule (ι × ι) R d)
        (homogeneousSubmodule (ι × ι) R d) := by
  suffices h : ∀ d, (homogeneousSubmodule (ι × ι) R d).map
      (comul R ι).toLinearMap ≤
        Submodule.map₂ (TensorProduct.mk R (CoordinateRing R ι) (CoordinateRing R ι))
          (homogeneousSubmodule (ι × ι) R d)
          (homogeneousSubmodule (ι × ι) R d) from h d ⟨p, hp, rfl⟩
  intro d
  induction d with
  | zero =>
    rw [homogeneousSubmodule_zero, Submodule.one_eq_span, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, rfl, rfl⟩
    rw [AlgHom.toLinearMap_apply, map_one, Algebra.TensorProduct.one_def]
    exact Submodule.apply_mem_map₂ _
      (Submodule.mem_span_singleton_self (1 : CoordinateRing R ι))
      (Submodule.mem_span_singleton_self (1 : CoordinateRing R ι))
  | succ d ih =>
    nth_rw 1 [← homogeneousSubmodule_one_pow (σ := ι × ι) (R := R) (d + 1)]
    rw [pow_succ, Submodule.map_mul, homogeneousSubmodule_one_pow]
    exact (mul_le_mul' ih (comul_homogeneous_one R ι)).trans
      ((Submodule.map₂_tmul_mul_le _ _ _ _).trans
        (Submodule.map₂_le_map₂ (homogeneousSubmodule_mul d 1)
          (homogeneousSubmodule_mul d 1)))

end Semiring

section Ring

variable (R : Type*) [CommRing R] (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The subcoalgebra of homogeneous degree-`d` matrix coordinates. -/
noncomputable def homogeneousSubcoalgebra (d : ℕ) :
    Subcoalgebra R (coordinateBialgebra R ι) :=
  Subcoalgebra.ofSubmodule
    ((homogeneousSubmodule (ι × ι) R d).map
      (coordinateBialgebraAlgEquiv R ι).toLinearMap) (by
    rintro _ ⟨p, hp, rfl⟩
    rw [TensorProduct.range_mapIncl, AlgEquiv.toLinearMap_apply, coordinateBialgebra_comul_apply]
    have h : Submodule.map₂
        (TensorProduct.mk R (CoordinateRing R ι) (CoordinateRing R ι))
        (homogeneousSubmodule (ι × ι) R d)
        (homogeneousSubmodule (ι × ι) R d) ≤
        (Submodule.map₂ (TensorProduct.mk R (coordinateBialgebra R ι)
          (coordinateBialgebra R ι))
          ((homogeneousSubmodule (ι × ι) R d).map
            (coordinateBialgebraAlgEquiv R ι).toLinearMap)
          ((homogeneousSubmodule (ι × ι) R d).map
            (coordinateBialgebraAlgEquiv R ι).toLinearMap)).comap
          (Algebra.TensorProduct.map (coordinateBialgebraAlgEquiv R ι).toAlgHom
            (coordinateBialgebraAlgEquiv R ι).toAlgHom).toLinearMap := by
      apply Submodule.map₂_le.mpr
      intro x hx y hy
      exact Submodule.apply_mem_map₂ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact h (comul_mem_homogeneous_tensorSquare R ι hp))

/-- The underlying module consists exactly of the homogeneous matrix coordinates. -/
@[simp]
theorem homogeneousSubcoalgebra_toSubmodule (d : ℕ) :
    (homogeneousSubcoalgebra R ι d).toSubmodule =
      (homogeneousSubmodule (ι × ι) R d).map
        (coordinateBialgebraAlgEquiv R ι).toLinearMap := (rfl)

/-- Membership in the homogeneous coordinate coalgebra is ordinary polynomial homogeneity. -/
@[simp]
theorem mem_homogeneousSubcoalgebra (d : ℕ) (p : CoordinateRing R ι) :
    coordinateBialgebraAlgEquiv R ι p ∈ homogeneousSubcoalgebra R ι d ↔
      p.IsHomogeneous d := by
  rw [← Subcoalgebra.mem_toSubmodule, homogeneousSubcoalgebra_toSubmodule,
    Submodule.mem_map]
  exact ⟨fun ⟨q, hq, hqp⟩ ↦ (coordinateBialgebraAlgEquiv R ι).injective hqp ▸ hq,
    fun hp ↦ ⟨p, hp, rfl⟩⟩

/-- Homogeneous polynomials identify linearly with the homogeneous coordinate coalgebra. -/
noncomputable def homogeneousSubcoalgebraEquiv (d : ℕ) :
    homogeneousSubmodule (ι × ι) R d ≃ₗ[R]
      (homogeneousSubcoalgebra R ι d).toSubmodule :=
  ((coordinateBialgebraAlgEquiv R ι).toLinearEquiv.submoduleMap
    (homogeneousSubmodule (ι × ι) R d)).trans
      (LinearEquiv.ofEq _ _ (homogeneousSubcoalgebra_toSubmodule R ι d).symm)

/-- The homogeneous-coordinate equivalence includes a polynomial by the ambient coordinate map. -/
@[simp]
theorem coe_homogeneousSubcoalgebraEquiv (d : ℕ)
    (p : homogeneousSubmodule (ι × ι) R d) :
    (homogeneousSubcoalgebraEquiv R ι d p : coordinateBialgebra R ι) =
      coordinateBialgebraAlgEquiv R ι p := (rfl)

/-- The inverse homogeneous-coordinate equivalence recovers the underlying polynomial. -/
@[simp]
theorem coe_homogeneousSubcoalgebraEquiv_symm (d : ℕ)
    (p : (homogeneousSubcoalgebra R ι d).toSubmodule) :
    ((homogeneousSubcoalgebraEquiv R ι d).symm p : CoordinateRing R ι) =
      (coordinateBialgebraAlgEquiv R ι).symm (p : coordinateBialgebra R ι) := (rfl)

instance (d : ℕ) : Module.Finite R (homogeneousSubcoalgebra R ι d).toSubmodule :=
  Module.Finite.equiv (homogeneousSubcoalgebraEquiv R ι d)

instance (d : ℕ) : Module.Free R (homogeneousSubcoalgebra R ι d).toSubmodule :=
  Module.Free.of_equiv (homogeneousSubcoalgebraEquiv R ι d)

/-- The homogeneous matrix-coordinate coalgebra, with its inherited comultiplication and counit. -/
noncomputable instance homogeneousSubcoalgebraCoalgebra (d : ℕ) :
    Coalgebra R (homogeneousSubcoalgebra R ι d).toSubmodule := by
  letI : Module.Free R (coordinateBialgebra R ι) :=
    Module.Free.of_equiv (coordinateBialgebraAlgEquiv R ι).toLinearEquiv
  exact (homogeneousSubcoalgebra R ι d).coalgebra

/-- The monomial basis of the homogeneous matrix-coordinate coalgebra. -/
noncomputable def homogeneousSubcoalgebraBasis (d : ℕ) :
    Module.Basis {s : (ι × ι) →₀ ℕ // s.degree = d} R
      (homogeneousSubcoalgebra R ι d).toSubmodule :=
  (homogeneousMonomialBasis d).map (homogeneousSubcoalgebraEquiv R ι d)

/-- A homogeneous coordinate basis vector is its named matrix monomial. -/
@[simp]
theorem coe_homogeneousSubcoalgebraBasis (d : ℕ)
    (s : {s : (ι × ι) →₀ ℕ // s.degree = d}) :
    (homogeneousSubcoalgebraBasis R ι d s : coordinateBialgebra R ι) =
      coordinateBialgebraAlgEquiv R ι (monomial s.1 1) := by
  simp [homogeneousSubcoalgebraBasis]

/-- A matrix-entry coordinate, as an element of the degree-one coalgebra. -/
noncomputable def homogeneousEntry (i j : ι) :
    (homogeneousSubcoalgebra R ι 1).toSubmodule :=
  homogeneousSubcoalgebraEquiv R ι 1 ⟨X (i, j), isHomogeneous_X R (i, j)⟩

/-- The inclusion of a degree-one entry is the corresponding polynomial variable. -/
@[simp]
theorem coe_homogeneousEntry (i j : ι) :
    (homogeneousEntry R ι i j : coordinateBialgebra R ι) =
      coordinateBialgebraAlgEquiv R ι (X (i, j)) := by
  simp [homogeneousEntry]

/-- Degree-one matrix coordinates have the usual matrix-coalgebra comultiplication.

Use this as an explicit rewrite: the generic subcoalgebra simp rule first expresses
comultiplication as `Subcoalgebra.comulLinearMap`. -/
theorem comul_homogeneousEntry (i j : ι) :
    Coalgebra.comul (R := R) (homogeneousEntry R ι i j) =
      ∑ k, homogeneousEntry R ι i k ⊗ₜ[R] homogeneousEntry R ι k j := by
  let : Module.Free R (coordinateBialgebra R ι) :=
    Module.Free.of_equiv (coordinateBialgebraAlgEquiv R ι).toLinearEquiv
  apply TensorProduct.map_injective_of_flat_flat
    (homogeneousSubcoalgebra R ι 1).toSubmodule.subtype
    (homogeneousSubcoalgebra R ι 1).toSubmodule.subtype
    Subtype.val_injective Subtype.val_injective
  simp

/-- The rank of the degree-`d` matrix-coordinate coalgebra. -/
@[simp]
theorem finrank_homogeneousSubcoalgebra [StrongRankCondition R] (d : ℕ) :
    Module.finrank R (homogeneousSubcoalgebra R ι d).toSubmodule =
      (Fintype.card ι * Fintype.card ι).multichoose d := by
  rw [← (homogeneousSubcoalgebraEquiv R ι d).finrank_eq,
    finrank_homogeneousSubmodule_eq_multichoose]
  simp

end Ring

end TauCeti.MatrixMonoid
