/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.Basis.Submodule
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-!
# Algebra models from coordinates of a basis

An algebra basis descends to an under-ring when the coordinates of its unit and multiplication
table belong to that under-ring. The span of the original basis is then a subalgebra with the
same basis, and extension of scalars recovers the original algebra. This retains the chosen
coordinates, rather than replacing the algebra by an unspecified finitely presented model.
-/

public section

namespace Module.Basis

variable {A S B ι : Type*} [CommRing A] [IsDomain A] [CommRing S] [Nontrivial S]
  [Algebra A S] [IsTorsionFree A S] [CommRing B] [Algebra S B] [Algebra A B]
  [IsScalarTower A S B]

/-- If the coordinates of the unit and multiplication table of an algebra basis lie in an
under-ring, its span over that ring is an algebra model with the original basis and scalar
extension diagram. -/
theorem exists_subalgebra_basis_of_repr_mem (b : Basis ι S B)
    (h₁ : ∀ i, b.repr 1 i ∈ Set.range (algebraMap A S))
    (hmul : ∀ i j l, b.repr (b i * b j) l ∈ Set.range (algebraMap A S)) :
    ∃ C : Subalgebra A B, ∃ c : Basis ι A C,
      C.toSubmodule = Submodule.span A (Set.range b) ∧
        (∀ i, (c i : B) = b i) ∧ Algebra.IsPushout A S C B := by
  let M := Submodule.span A (Set.range b)
  have hunit : (1 : B) ∈ M := (b.mem_span_iff_repr_mem A 1).mpr h₁
  have hprod : ∀ x ∈ M, ∀ y ∈ M, x * y ∈ M := by
    intro x hx y hy
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem x y hx hy =>
        obtain ⟨i, rfl⟩ := hx
        obtain ⟨j, rfl⟩ := hy
        exact (b.mem_span_iff_repr_mem A _).mpr (hmul i j)
    | zero_left => simp
    | zero_right => simp
    | add_left x y z _ _ _ hx hy => simpa [add_mul] using M.add_mem hx hy
    | add_right x y z _ _ _ hx hy => simpa [mul_add] using M.add_mem hx hy
    | smul_left a x y _ _ h => simpa [smul_mul_assoc] using M.smul_mem a h
    | smul_right a x y _ _ h => simpa [mul_smul_comm] using M.smul_mem a h
  let C : Subalgebra A B := M.toSubalgebra hunit fun x y hx hy ↦ hprod x hx y hy
  let c : Basis ι A C := b.restrictScalars A
  have hc : ∀ i, (c i : B) = b i := b.restrictScalars_apply A
  have he : (Finsupp.linearCombination A b).comp c.repr.toLinearMap = C.val.toLinearMap := by
    apply c.ext
    intro i
    simp [hc]
  have hbase := (IsBaseChange.of_basis A b).comp_equiv c.repr (Finsupp.linearCombination A b)
  rw [he] at hbase
  exact ⟨C, c, M.toSubalgebra_toSubmodule _ _, hc, ⟨hbase⟩⟩

end Module.Basis
