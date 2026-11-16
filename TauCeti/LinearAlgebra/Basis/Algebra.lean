/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import TauCeti.LinearAlgebra.Basis.RangeSpan
import Mathlib.Algebra.Algebra.Operations

/-!
# Algebra models from coordinates of a basis

For an associative semiring algebra over `A`, an `S`-module basis descends to an `A`-subalgebra
when the coordinates of its unit and multiplication table belong to the image of `A → S`.
`Module.Basis.descendSubalgebra` is its `A`-span. If the scalar action of `A` on `S` is faithful,
`Module.Basis.descendBasis` gives an `A`-basis with the same vectors and coordinates.

For commutative semiring algebras, extension of scalars recovers the original algebra without
requiring faithfulness. The compatible-basis criterion
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
    (h : ∀ i, algebraMap C B (c i) = b i) : Algebra.IsPushout A S C B :=
  ⟨c.isBaseChange_of_map_basis b (IsScalarTower.toAlgHom A C B).toLinearMap h⟩

end Pushout

section Descent

variable {A S B ι : Type*} [CommSemiring A] [CommSemiring S] [Semiring B]
  [Algebra A S] [Module S B] [Algebra A B] [IsScalarTower A S B]

variable (b : Basis ι S B) (A)

/-- The subalgebra spanned over an under-semiring by a basis whose unit and multiplication
coordinates belong to that under-semiring. -/
noncomputable def descendSubalgebra
    (h₁ : ∀ i, b.repr 1 i ∈ Set.range (algebraMap A S))
    (hmul : ∀ i j l, b.repr (b i * b j) l ∈ Set.range (algebraMap A S)) : Subalgebra A B := by
  let M := Submodule.span A (Set.range b)
  have hunit : (1 : B) ∈ M := (mem_span_iff_repr_range b 1).mpr h₁
  have hprod : M * M ≤ M := by
    dsimp only [M]
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact (b.mem_span_iff_repr_range _).mpr (hmul i j)
  exact M.toSubalgebra hunit fun _ _ hx hy ↦ hprod (Submodule.mul_mem_mul hx hy)

variable (h₁ : ∀ i, b.repr 1 i ∈ Set.range (algebraMap A S))
  (hmul : ∀ i j l, b.repr (b i * b j) l ∈ Set.range (algebraMap A S))

/-- The descended subalgebra has the expected underlying span. -/
@[simp]
theorem descendSubalgebra_toSubmodule :
    (b.descendSubalgebra A h₁ hmul).toSubmodule = Submodule.span A (Set.range b) := by
  simp [descendSubalgebra]

/-- The carrier of the descended subalgebra is the span of the original basis. -/
@[simp]
theorem coe_descendSubalgebra :
    (b.descendSubalgebra A h₁ hmul : Set B) = Submodule.span A (Set.range b) := by
  rw [← Subalgebra.coe_toSubmodule, descendSubalgebra_toSubmodule]

/-- Membership in the descended subalgebra is detected by the original coordinates. -/
theorem mem_descendSubalgebra_iff (x : B) :
    x ∈ b.descendSubalgebra A h₁ hmul ↔
      ∀ i, b.repr x i ∈ Set.range (algebraMap A S) := by
  rw [← Subalgebra.mem_toSubmodule, descendSubalgebra_toSubmodule, mem_span_iff_repr_range]

/-- Each original basis vector belongs to the descended subalgebra. -/
@[simp]
theorem self_mem_descendSubalgebra (i : ι) : b i ∈ b.descendSubalgebra A h₁ hmul := by
  rw [← Subalgebra.mem_toSubmodule, descendSubalgebra_toSubmodule]
  exact Submodule.subset_span (Set.mem_range_self i)

/-- Extending scalars from the underlying module of the descended subalgebra recovers the
original module. Faithfulness of `A → S` is not required. -/
theorem isBaseChange_descendSubalgebra :
    IsBaseChange S (b.descendSubalgebra A h₁ hmul).val.toLinearMap := by
  let e := (LinearEquiv.ofEq _ _ (b.descendSubalgebra_toSubmodule A h₁ hmul).symm).trans
    (b.descendSubalgebra A h₁ hmul).toSubmoduleEquiv
  have he : (Submodule.span A (Set.range b)).subtype.comp e.symm.toLinearMap =
      (b.descendSubalgebra A h₁ hmul).val.toLinearMap := by
    ext x
    simp only [LinearMap.coe_comp, Submodule.coe_subtype, LinearEquiv.coe_coe,
      Function.comp_apply, AlgHom.toLinearMap_apply, Subalgebra.coe_val]
    exact LinearEquiv.coe_ofEq_apply (b.descendSubalgebra_toSubmodule A h₁ hmul) x
  simpa only [he] using (b.isBaseChange_span (A := A)).comp_equiv e.symm _

variable [FaithfulSMul A S]

/-- The basis of the descended subalgebra given by the original basis vectors. Faithfulness
of the scalar action of `A` on `S` ensures that these vectors are `A`-linearly independent. -/
noncomputable def descendBasis : Basis ι A (b.descendSubalgebra A h₁ hmul) :=
  (Basis.span (b.linearIndependent.restrict_scalars' A)).map
    ((LinearEquiv.ofEq _ _ (b.descendSubalgebra_toSubmodule A h₁ hmul).symm).trans
      (b.descendSubalgebra A h₁ hmul).toSubmoduleEquiv)

@[simp]
theorem coe_descendBasis_apply (i : ι) :
    (b.descendBasis A h₁ hmul i : B) = b i := by
  simp only [descendBasis, Basis.map_apply, LinearEquiv.trans_apply,
    Subalgebra.toSubmoduleEquiv, Basis.span_apply]
  exact LinearEquiv.coe_ofEq_apply _ _

/-- Coordinates in the descended basis map to the original coordinates. -/
@[simp]
theorem descendBasis_repr_apply (x : b.descendSubalgebra A h₁ hmul) (i : ι) :
    algebraMap A S ((b.descendBasis A h₁ hmul).repr x i) = b.repr (x : B) i := by
  have ibc := b.isBaseChange_descendSubalgebra A h₁ hmul
  have hb : ibc.basis (b.descendBasis A h₁ hmul) = b := by
    ext j
    simp [IsBaseChange.basis_apply]
  simpa [hb] using (ibc.basis_repr_comp_apply (b.descendBasis A h₁ hmul) x i).symm

end Descent

section Pushout

variable {A S B ι : Type*} [CommSemiring A] [CommSemiring S] [CommSemiring B]
  [Algebra A S] [Algebra S B] [Algebra A B] [IsScalarTower A S B]

variable (b : Basis ι S B) (A)
  (h₁ : ∀ i, b.repr 1 i ∈ Set.range (algebraMap A S))
  (hmul : ∀ i j l, b.repr (b i * b j) l ∈ Set.range (algebraMap A S))

/-- Extending scalars from the descended subalgebra recovers the original commutative semiring
algebra, without requiring faithful scalar action. -/
instance isPushout_descendSubalgebra :
    Algebra.IsPushout A S (b.descendSubalgebra A h₁ hmul) B :=
  ⟨b.isBaseChange_descendSubalgebra A h₁ hmul⟩

end Pushout

end Module.Basis
