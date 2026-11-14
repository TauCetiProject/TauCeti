/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.Basis.Submodule
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import TauCeti.LinearAlgebra.Basis.RangeSpan

/-!
# Algebra models from coordinates of a basis

An algebra basis descends to an under-semiring when the coordinates of its unit and multiplication
table belong to that under-semiring. `Module.Basis.descendSubalgebra` is its span over the
under-semiring, and `Module.Basis.descendBasis` preserves the chosen basis and its coordinates.
Extension of scalars recovers the original algebra. The compatible-basis criterion
`Module.Basis.isPushout_of_algebraMap_eq` also applies to independently constructed models.
-/

public section

namespace Module.Basis

section Pushout

variable {A S C B ι : Type*} [CommSemiring A] [CommSemiring S] [CommSemiring C]
  [CommSemiring B] [Algebra A S] [Algebra A C] [Algebra S B] [Algebra C B]
  [Algebra A B] [IsScalarTower A S B] [IsScalarTower A C B]

/-- Compatible bases identify an algebra as the scalar extension of an under-semiring model. -/
theorem isPushout_of_algebraMap_eq (c : Basis ι A C) (b : Basis ι S B)
    (h : ∀ i, algebraMap C B (c i) = b i) : Algebra.IsPushout A S C B := by
  have he : (Finsupp.linearCombination A b).comp c.repr.toLinearMap =
      (IsScalarTower.toAlgHom A C B).toLinearMap := by
    apply c.ext
    intro i
    simp [h]
  have hbase := (IsBaseChange.of_basis A b).comp_equiv c.repr (Finsupp.linearCombination A b)
  rw [he] at hbase
  exact ⟨hbase⟩

end Pushout

private theorem mem_span_iff_repr_range
    {A S M ι : Type*} [CommSemiring A] [CommSemiring S] [AddCommMonoid M]
    [Algebra A S] [Module S M] [Module A M] [IsScalarTower A S M]
    (b : Basis ι S M) (x : M) :
    x ∈ Submodule.span A (Set.range b) ↔ ∀ i, b.repr x i ∈ Set.range (algebraMap A S) := by
  simpa [Submodule.span_le, Set.range_subset_iff, Basis.toMatrix_apply] using
    (b.span_range_le_span_range_iff_forall_toMatrix_mem (fun _ : Unit ↦ x))

variable {A S B ι : Type*} [CommSemiring A] [CommSemiring S] [CommSemiring B]
  [Algebra A S] [Algebra S B] [Algebra A B] [IsScalarTower A S B]

variable (b : Basis ι S B) (A)

/-- The subalgebra spanned over an under-semiring by a basis whose unit and multiplication
coordinates belong to that under-semiring. -/
noncomputable def descendSubalgebra
    (h₁ : ∀ i, b.repr 1 i ∈ Set.range (algebraMap A S))
    (hmul : ∀ i j l, b.repr (b i * b j) l ∈ Set.range (algebraMap A S)) : Subalgebra A B := by
  let M := Submodule.span A (Set.range b)
  have hunit : (1 : B) ∈ M := (mem_span_iff_repr_range b 1).mpr h₁
  have hprod : ∀ x ∈ M, ∀ y ∈ M, x * y ∈ M := by
    intro x hx y hy
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem x y hx hy =>
        obtain ⟨i, rfl⟩ := hx
        obtain ⟨j, rfl⟩ := hy
        exact (mem_span_iff_repr_range b _).mpr (hmul i j)
    | zero_left => simp
    | zero_right => simp
    | add_left x y z _ _ _ hx hy => simpa [add_mul] using M.add_mem hx hy
    | add_right x y z _ _ _ hx hy => simpa [mul_add] using M.add_mem hx hy
    | smul_left a x y _ _ h => simpa [smul_mul_assoc] using M.smul_mem a h
    | smul_right a x y _ _ h => simpa [mul_smul_comm] using M.smul_mem a h
  exact M.toSubalgebra hunit fun x y hx hy ↦ hprod x hx y hy

variable (h₁ : ∀ i, b.repr 1 i ∈ Set.range (algebraMap A S))
  (hmul : ∀ i j l, b.repr (b i * b j) l ∈ Set.range (algebraMap A S))

/-- The descended subalgebra has the expected underlying span. -/
@[simp]
theorem descendSubalgebra_toSubmodule :
    (b.descendSubalgebra A h₁ hmul).toSubmodule = Submodule.span A (Set.range b) := by
  unfold descendSubalgebra
  rfl

/-- The carrier of the descended subalgebra is the span of the original basis. -/
@[simp]
theorem coe_descendSubalgebra :
    (b.descendSubalgebra A h₁ hmul : Set B) = Submodule.span A (Set.range b) := by
  rw [← Subalgebra.coe_toSubmodule, descendSubalgebra_toSubmodule]

/-- Membership in the descended subalgebra is detected by the original coordinates. -/
theorem mem_descendSubalgebra_iff (x : B) :
    x ∈ b.descendSubalgebra A h₁ hmul ↔
      ∀ i, b.repr x i ∈ Set.range (algebraMap A S) :=
  mem_span_iff_repr_range b x

/-- Each original basis vector belongs to the descended subalgebra. -/
@[simp]
theorem basis_mem_descendSubalgebra (i : ι) : b i ∈ b.descendSubalgebra A h₁ hmul :=
  Submodule.subset_span (Set.mem_range_self i)

variable [FaithfulSMul A S]

/-- The basis of the descended subalgebra given by the original basis vectors. -/
noncomputable def descendBasis : Basis ι A (b.descendSubalgebra A h₁ hmul) :=
  Basis.span (b.linearIndependent.restrict_scalars' A)

@[simp]
theorem coe_descendBasis_apply (i : ι) :
    (b.descendBasis A h₁ hmul i : B) = b i :=
  Basis.coe_span_apply _ i

/-- Coordinates in the descended basis map to the original coordinates. -/
@[simp]
theorem descendBasis_repr_apply (x : b.descendSubalgebra A h₁ hmul) (i : ι) :
    algebraMap A S ((b.descendBasis A h₁ hmul).repr x i) = b.repr (x : B) i := by
  -- Adapt the coordinate-map argument of `Basis.restrictScalars_repr_apply` to semirings.
  have hre : Finsupp.mapRange.linearMap (Algebra.linearMap A S) ∘ₗ
      (b.descendBasis A h₁ hmul).repr.toLinearMap =
      ((b.repr : B →ₗ[S] ι →₀ S).restrictScalars A).domRestrict
        (b.descendSubalgebra A h₁ hmul).toSubmodule := by
    apply (b.descendBasis A h₁ hmul).ext
    intro j
    -- Evaluate both maps on the actual subalgebra carrier before simplifying its coercion.
    change Finsupp.mapRange.linearMap (Algebra.linearMap A S)
      ((b.descendBasis A h₁ hmul).repr (b.descendBasis A h₁ hmul j)) =
        b.repr (b.descendBasis A h₁ hmul j : B)
    simp
  exact congr($hre x i)

/-- Extending scalars from the descended subalgebra recovers the original algebra. -/
instance isPushout_descendSubalgebra :
    Algebra.IsPushout A S (b.descendSubalgebra A h₁ hmul) B :=
  (b.descendBasis A h₁ hmul).isPushout_of_algebraMap_eq b (b.coe_descendBasis_apply A h₁ hmul)

end Module.Basis
