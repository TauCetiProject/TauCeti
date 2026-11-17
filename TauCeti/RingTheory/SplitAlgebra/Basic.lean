/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Unimodular
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Linear splittings of algebra units

An algebra is split when its unit map has a linear retraction, not necessarily a ring
retraction. We use Mathlib's `Module.IsUnimodular` at one, with `SplitAlgebra` as the
algebra-oriented abbreviation. Evaluation at one on the dual detects splitting: its image is the
`unitTraceIdeal`, and the algebra splits exactly when this ideal is the unit ideal.

Splittings compose, restrict along algebra maps, and survive arbitrary base change.
The tensor-unit map of a split algebra is injective for every module, without any
flatness or finiteness assumption. These facts provide the elementary retraction
calculus for direct summand arguments.

## References

* Y. André, *La conjecture du facteur direct*, Publ. Math. IHÉS 127 (2018),
  §0.1 and Annexe A.2, Lemme A.2.1.
-/

public section

namespace TauCeti

open TensorProduct

universe u v w

variable (R : Type u) (S : Type v) [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- An algebra is split if an `R`-linear functional takes one to one.
The functional is not required to preserve multiplication. -/
abbrev SplitAlgebra : Prop := Module.IsUnimodular R (1 : S)

/-- The image of evaluation at one on the module dual. -/
def unitTraceIdeal : Ideal R := LinearMap.range (Module.Dual.eval R S 1)

/-- Elements of the unit trace ideal are precisely values of linear functionals at one. -/
@[simp]
theorem mem_unitTraceIdeal_iff (r : R) :
    r ∈ unitTraceIdeal R S ↔ ∃ ρ : S →ₗ[R] R, ρ 1 = r := Iff.rfl

/-- Splitting is equivalent to surjectivity of evaluation at one on the dual. -/
theorem splitAlgebra_iff_surjective_eval_one :
    SplitAlgebra R S ↔ Function.Surjective (Module.Dual.eval R S 1) := by
  constructor
  · intro h r
    obtain ⟨ρ, hρ⟩ := Module.isUnimodular_iff.mp h
    exact ⟨r • ρ, by simp [hρ]⟩
  · intro h
    exact Module.isUnimodular_iff.mpr (h 1)

/-- The unit trace ideal is the unit ideal exactly when the algebra splits. -/
@[simp]
theorem unitTraceIdeal_eq_top_iff : unitTraceIdeal R S = ⊤ ↔ SplitAlgebra R S := by
  rw [Ideal.eq_top_iff_one, mem_unitTraceIdeal_iff]
  exact Module.isUnimodular_iff.symm

/-- A value-one linear functional is a retraction of the algebra map. -/
theorem splitAlgebra_iff_exists_retraction :
    SplitAlgebra R S ↔ ∃ ρ : S →ₗ[R] R, Function.LeftInverse ρ (algebraMap R S) := by
  constructor
  · intro h
    obtain ⟨ρ, hρ⟩ := Module.isUnimodular_iff.mp h
    refine ⟨ρ, fun r ↦ ?_⟩
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hρ, smul_eq_mul, mul_one]
  · rintro ⟨ρ, hρ⟩
    exact Module.isUnimodular_iff.mpr ⟨ρ, by simpa using hρ 1⟩

/-- Splitting is equivalent to the existence of a functional with unit value at one. -/
theorem splitAlgebra_iff_exists_isUnit :
    SplitAlgebra R S ↔ ∃ ρ : S →ₗ[R] R, IsUnit (ρ 1) := by
  constructor
  · intro h
    obtain ⟨ρ, hρ⟩ := Module.isUnimodular_iff.mp h
    exact ⟨ρ, hρ ▸ isUnit_one⟩
  · rintro ⟨ρ, u, hu⟩
    exact Module.isUnimodular_iff.mpr ⟨(↑u⁻¹ : R) • ρ, by simp [← hu]⟩

variable {R S}

namespace SplitAlgebra

/-- The structure map of a split algebra is injective. -/
theorem injective (h : SplitAlgebra R S) : Function.Injective (algebraMap R S) := by
  obtain ⟨ρ, hρ⟩ := (splitAlgebra_iff_exists_retraction R S).mp h
  exact hρ.injective

/-- Splitting restricts along any algebra map into a split algebra. -/
theorem of_algHom {T : Type w} [CommSemiring T] [Algebra R T]
    (h : SplitAlgebra R T) (f : S →ₐ[R] T) : SplitAlgebra R S := by
  obtain ⟨ρ, hρ⟩ := Module.isUnimodular_iff.mp h
  exact Module.isUnimodular_iff.mpr ⟨ρ.comp f.toLinearMap, by simp [hρ]⟩

/-- Splittings in an algebra tower compose. -/
theorem trans {T : Type w} [CommSemiring T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] (hS : SplitAlgebra R S) (hT : SplitAlgebra S T) :
    SplitAlgebra R T := by
  obtain ⟨ρ, hρ⟩ := Module.isUnimodular_iff.mp hS
  obtain ⟨σ, hσ⟩ := Module.isUnimodular_iff.mp hT
  exact Module.isUnimodular_iff.mpr ⟨ρ.comp (σ.restrictScalars R), by simp [hρ, hσ]⟩

/-- A splitting survives arbitrary extension of scalars. -/
theorem baseChange (h : SplitAlgebra R S) (A : Type w) [CommSemiring A] [Algebra R A] :
    SplitAlgebra A (A ⊗[R] S) := by
  obtain ⟨ρ, hρ⟩ := Module.isUnimodular_iff.mp h
  refine Module.isUnimodular_iff.mpr ⟨
    (TensorProduct.AlgebraTensorModule.rid R A A).toLinearMap.comp
    (ρ.baseChange A), ?_⟩
  simp [Algebra.TensorProduct.one_def, hρ]

/-- Tensoring the unit of a split algebra with any module is injective.
This is tensor purity, with no flatness assumption on the module. -/
theorem tensorUnit_injective (h : SplitAlgebra R S) (M : Type w)
    [AddCommMonoid M] [Module R M] :
    Function.Injective (fun m : M ↦ m ⊗ₜ[R] (1 : S)) := by
  obtain ⟨ρ, hρ⟩ := Module.isUnimodular_iff.mp h
  have hinv : Function.LeftInverse
      (fun t : M ⊗[R] S ↦ (TensorProduct.rid R M) (ρ.lTensor M t))
      (fun m : M ↦ m ⊗ₜ[R] (1 : S)) := by
    intro m
    simp [hρ]
  exact hinv.injective

end SplitAlgebra

/-- The identity algebra splits by the identity linear map. -/
@[simp]
theorem splitAlgebra_self : SplitAlgebra R R :=
  Module.isUnimodular_iff.mpr ⟨LinearMap.id, rfl⟩

/-- Splitness is invariant under algebra isomorphism. -/
theorem _root_.AlgEquiv.splitAlgebra_iff {T : Type w} [CommSemiring T] [Algebra R T]
    (e : S ≃ₐ[R] T) : SplitAlgebra R S ↔ SplitAlgebra R T :=
  ⟨fun h ↦ h.of_algHom e.symm.toAlgHom, fun h ↦ h.of_algHom e.toAlgHom⟩

/-- The zero algebra over a nonzero base does not split. -/
theorem not_splitAlgebra_of_subsingleton [Nontrivial R] [Subsingleton S] :
    ¬ SplitAlgebra R S := by
  intro h
  obtain ⟨ρ, hρ⟩ := Module.isUnimodular_iff.mp h
  simp [Subsingleton.elim (1 : S) 0] at hρ

end TauCeti
