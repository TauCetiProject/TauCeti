/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Circle coordinates of a real basis

A basis `b` of a real vector space `E` gives the homomorphism `x ↦ (exp (2πi bᵢ*(x)))ᵢ` from `E`
onto the product `ι → Circle` of circles, where `bᵢ*` is the `i`-th coordinate functional
(`Module.Basis.circleExp`). It is continuous and surjective, and its kernel is the integer span
of `b`. For a `ℤ`-basis of a lattice `L`, read as a real basis of `E`, the kernel is exactly `L`.
These are the coordinates in which the quotient `E ⧸ L` is a product of circles: a compact
connected commutative Lie group is such a quotient of its Lie algebra by the kernel of its
exponential map, so these coordinates exhibit it as a product of circles.

## Main definitions

* `Module.Basis.circleExp`: the circle coordinates of a real basis, as a homomorphism to the
  product of circles written additively.

## Main results

* `Module.Basis.continuous_circleExp` and `Module.Basis.circleExp_surjective`: the circle
  coordinates are continuous and surjective.
* `Module.Basis.ker_circleExp`: their kernel is the integer span of the basis.
* `Module.Basis.ker_circleExp_ofZLatticeBasis`: for a `ℤ`-basis of a lattice, it is the lattice.
-/

public section

noncomputable section

open Real Submodule

namespace Module.Basis

section Coordinates

variable {ι E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The **circle coordinates** of a real basis `b`: the homomorphism
`x ↦ (exp (2πi bᵢ*(x)))ᵢ` from `E` to the product `ι → Circle` of circles, written additively. -/
def circleExp (b : Basis ι ℝ E) : E →+ Additive (ι → Circle) where
  toFun x := Additive.ofMul fun i => Circle.exp (2 * π * b.repr x i)
  map_zero' := by
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply, mul_zero, Circle.exp_zero]
    rfl
  map_add' x y := by
    simp only [map_add, Finsupp.coe_add, Pi.add_apply, mul_add, Circle.exp_add]
    rfl

@[simp]
theorem circleExp_apply (b : Basis ι ℝ E) (x : E) :
    b.circleExp x = Additive.ofMul fun i => Circle.exp (2 * π * b.repr x i) := by
  rw [circleExp]
  rfl

/-- **The circle coordinates of a finite basis are surjective.** -/
theorem circleExp_surjective [Finite ι] (b : Basis ι ℝ E) : Function.Surjective b.circleExp := by
  intro z
  choose t ht using fun i => Circle.exp_surjective (z.toMul i)
  refine ⟨b.equivFun.symm fun i => t i / (2 * π), ?_⟩
  rw [circleExp_apply, ← Additive.toMul.apply_eq_iff_eq, toMul_ofMul]
  funext i
  rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply,
    mul_div_cancel₀ _ (mul_ne_zero two_ne_zero pi_ne_zero), ht]

/-- Membership in the kernel of the circle coordinates: all coordinates are integers. -/
theorem mem_ker_circleExp (b : Basis ι ℝ E) {x : E} :
    x ∈ b.circleExp.ker ↔ ∀ i, b.repr x i ∈ Set.range (Int.cast : ℤ → ℝ) := by
  rw [AddMonoidHom.mem_ker, circleExp_apply, ← ofMul_one, Additive.ofMul.apply_eq_iff_eq,
    funext_iff]
  refine forall_congr' fun i => ?_
  rw [Pi.one_apply, Circle.exp_eq_one]
  refine exists_congr fun n => ?_
  rw [mul_comm (n : ℝ), mul_eq_mul_left_iff, eq_comm]
  simp only [mul_eq_zero, two_ne_zero, pi_ne_zero, or_self, or_false]

/-- **The kernel of the circle coordinates is the integer span of the basis.** -/
theorem ker_circleExp (b : Basis ι ℝ E) :
    b.circleExp.ker = (span ℤ (Set.range b)).toAddSubgroup := by
  ext x
  rw [mem_ker_circleExp, mem_toAddSubgroup, b.mem_span_iff_repr_mem ℤ, algebraMap_int_eq,
    Int.coe_castRingHom]

/-- **The circle coordinates of a finite basis are continuous.** -/
theorem continuous_circleExp [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [T2Space E] [Finite ι] (b : Basis ι ℝ E) : Continuous b.circleExp := by
  have : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  refine continuous_ofMul.comp (continuous_pi fun i => Circle.exp.continuous.comp ?_)
  exact continuous_const.mul (b.coord i).continuous_of_finiteDimensional

end Coordinates

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **For a `ℤ`-basis of a lattice, the kernel of the circle coordinates is the lattice.** -/
theorem ker_circleExp_ofZLatticeBasis (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L) :
    (b.ofZLatticeBasis ℝ L).circleExp.ker = L.toAddSubgroup := by
  rw [ker_circleExp, ofZLatticeBasis_span]

end Module.Basis
