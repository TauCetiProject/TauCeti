/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
public import TauCeti.Topology.Homotopy.HomotopyClassGroup.Basic

/-!
# Elementary matrices of continuous functions are nullhomotopic

Let `R` be a topological ring and `X` a topological space. An invertible matrix `g` over the ring
`C(X, R)` of continuous functions is a family of invertible matrices over `R` depending
continuously on a point of `X`: evaluating its entries at `x` gives the continuous map
`ContinuousMap.evalGL g : C(X, GL n R)`, and `ContinuousMap.evalGL` is a group homomorphism.

When `R` is a topological real vector space, as for `ℝ` or `ℂ`, scaling the coefficient of an
elementary matrix `1 + a Eᵢⱼ` gives the homotopy `(t, x) ↦ 1 + (1 - t) a(x) Eᵢⱼ` from its
evaluation to the constant map `1`. Since pointwise products and inverses of nullhomotopic maps
into the topological group `GL n R` are nullhomotopic, the evaluation of every matrix in the
elementary subgroup `E n C(X, R)` is nullhomotopic. Since ring maps carry elementary matrices to
elementary matrices, the same holds for elementary matrices over any ring mapping to `C(X, R)`.
If moreover the evaluation equals `1` at a basepoint `x₀`, the nullhomotopy can be chosen
relative to `x₀`.

Contrapositively, an invertible matrix over a ring of continuous functions whose evaluation is not
nullhomotopic is not elementary. For `X` the circle this is how loops of matrices detect
nontrivial classes in algebraic `K₁`, as for the rotation matrix over the coordinate ring of the
real circle.

## Main definitions

* `ContinuousMap.evalGL`: the homomorphism `GL n C(X, R) →* C(X, GL n R)` evaluating the entries
  pointwise.

## Main results

* `TauCeti.continuous_transvectionUnit`: the elementary matrix `1 + a Eᵢⱼ` depends continuously
  on `a`.
* `ContinuousMap.evalGL_homotopic_one_of_mem_elementarySubgroup`: the evaluation of an elementary
  matrix over `C(X, R)` is homotopic to the constant map `1`.
* `ContinuousMap.evalGL_homotopicRel_one_of_mem_elementarySubgroup`: if moreover it equals `1`
  at `x₀`, it is homotopic to `1` relative to `x₀`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Example 1.5.4.
-/

public section

open Matrix

namespace TauCeti

variable {n R : Type*} [Fintype n] [DecidableEq n] [Ring R] [TopologicalSpace R] [ContinuousNeg R]

/-- The elementary matrix `1 + a Eᵢⱼ` depends continuously on its coefficient `a`. -/
@[fun_prop]
theorem continuous_transvectionUnit {i j : n} (hij : i ≠ j) :
    Continuous (transvectionUnit hij : R → GL n R) := by
  -- every entry of `1 ± a Eᵢⱼ` is constant, `a` or `-a`
  refine Units.continuous_iff.2
    ⟨continuous_matrix fun k l ↦ ?_, continuous_matrix fun k l ↦ ?_⟩ <;>
  · simp only [Function.comp_def, transvectionUnit_inv, coe_transvectionUnit_eq_one_add_single,
      Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    by_cases h : i = k ∧ j = l
    · obtain ⟨rfl, rfl⟩ := h
      simp only [hij, ite_false, and_self, ite_true, zero_add]
      fun_prop
    · simp only [h, ite_false, add_zero]
      fun_prop

end TauCeti

namespace ContinuousMap

open TauCeti

variable {X R n : Type*} [Fintype n] [DecidableEq n] [TopologicalSpace X] [Ring R]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- An invertible matrix of continuous functions on `X` evaluates to a continuous map from `X` to
invertible matrices: its value at `x` is obtained by evaluating every entry at `x`. This is a
homomorphism for pointwise multiplication of maps into `GL n R`. -/
def evalGL : GL n C(X, R) →* C(X, GL n R) where
  toFun g :=
    { toFun x := Units.map ((Pi.evalRingHom _ x).comp coeFnRingHom).mapMatrix.toMonoidHom g
      continuous_toFun := Units.continuous_iff.2
        ⟨continuous_matrix fun i j ↦ by simpa using (g.val i j).continuous,
          continuous_matrix fun i j ↦ by simpa using (g⁻¹.val i j).continuous⟩ }
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

/-- The entries of the evaluation of an invertible matrix of continuous functions are the values
of its entries. -/
@[simp]
theorem coe_evalGL_apply (g : GL n C(X, R)) (x : X) (i j : n) :
    (evalGL g x : Matrix n n R) i j = (g : Matrix n n C(X, R)) i j x :=
  (rfl)

/-- The entries of the inverse of the evaluation are the values of the entries of the inverse. -/
@[simp]
theorem coe_inv_evalGL_apply (g : GL n C(X, R)) (x : X) (i j : n) :
    (((evalGL g x)⁻¹ : GL n R) : Matrix n n R) i j =
      ((g⁻¹ : GL n C(X, R)) : Matrix n n C(X, R)) i j x :=
  (rfl)

/-- An elementary matrix of continuous functions evaluates to the elementary matrix of the value
of its coefficient. -/
@[simp]
theorem evalGL_transvectionUnit_apply {i j : n} (hij : i ≠ j) (a : C(X, R)) (x : X) :
    -- the ascription avoids a slow unification of the unknown coefficient ring
    evalGL (transvectionUnit hij a : GL n C(X, R)) x = transvectionUnit hij (a x) := by
  ext k l
  rw [coe_evalGL_apply]
  simp only [coe_transvectionUnit_eq_one_add_single, Matrix.add_apply, ContinuousMap.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

/-- **Elementary matrices of continuous functions are nullhomotopic.** If `R` is a topological
real vector space, the evaluation of a matrix in the elementary subgroup of `GL n C(X, R)` is
homotopic to the constant map `1`. -/
theorem evalGL_homotopic_one_of_mem_elementarySubgroup [Module ℝ R] [ContinuousSMul ℝ R]
    {g : GL n C(X, R)} (hg : g ∈ elementarySubgroup n C(X, R)) : (evalGL g).Homotopic 1 := by
  rw [elementarySubgroup_def] at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, j, hij, a, rfl⟩ := hg
    -- shrink the coefficient: `(t, x) ↦ 1 + (1 - t) a(x) Eᵢⱼ`
    exact ⟨{ toFun := fun p ↦ transvectionUnit hij ((1 - (p.1 : ℝ)) • a p.2)
             continuous_toFun := by fun_prop
             map_zero_left := fun x ↦ by simp
             map_one_left := fun x ↦ by simp }⟩
  | one => simpa using Homotopic.refl 1
  | mul g h _ _ hg hh => simpa using hg.mul hh
  | inv g _ hg => simpa using hg.inv

/-- **Elementary loops of continuous functions are based nullhomotopic.** If `R` is a topological
real vector space and the evaluation of a matrix in the elementary subgroup of `GL n C(X, R)` is
`1` at `x₀`, then it is homotopic to the constant map `1` relative to `x₀`. -/
theorem evalGL_homotopicRel_one_of_mem_elementarySubgroup [Module ℝ R] [ContinuousSMul ℝ R]
    {g : GL n C(X, R)} (hg : g ∈ elementarySubgroup n C(X, R)) {x₀ : X}
    (hx₀ : evalGL g x₀ = 1) : (evalGL g).HomotopicRel 1 {x₀} :=
  (homotopicRel_singleton_iff_homotopic_of_apply_eq hx₀).2 <|
    evalGL_homotopic_one_of_mem_elementarySubgroup hg

end ContinuousMap
