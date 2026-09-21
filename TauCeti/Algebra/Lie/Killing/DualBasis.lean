/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Dual bases for the Killing form

For a Lie algebra with nondegenerate Killing form, every basis has a Killing-dual basis. This file
develops its coordinate equations and the canonical basis-independent contraction of a bilinear map
against a basis and its Killing dual.

## Main definitions

* `TauCeti.killingDualBasis`: the basis dual to a given one under the Killing form.

## Main results

* `TauCeti.sum_killingForm_killingDualBasis_eq_trace`: contraction against a Killing-dual basis
  computes the trace.
* `TauCeti.sum_apply_killingDualBasis_eq`: contraction of a bilinear map against a basis and its
  Killing dual is independent of the basis.
* `TauCeti.sum_apply_killingDualBasis_of_isAdjointPair`: a Killing-adjoint pair may be moved between
  the two slots of the contraction.
* `TauCeti.sum_apply_lie_killingDualBasis_add_eq_zero`: the canonical contraction is invariant under
  the adjoint action.
-/

public section

open Finset LieAlgebra LieModule

namespace TauCeti

universe u v w

variable {K : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L]

/-! ### The Killing-dual basis -/

section DualBasis

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

omit [LieAlgebra.IsKilling K L] in
/-- The Killing form is symmetric, in the bundled `LinearMap.BilinForm.IsSymm` form that the
dual-basis API asks for; Mathlib supplies it as the unbundled `LieModule.traceForm_isSymm`. -/
private theorem killingForm_isSymm : (killingForm K L).IsSymm :=
  LinearMap.BilinForm.isSymm_def.mpr fun x y ↦ LieModule.traceForm_comm K L L x y

/-- The basis of `L` **dual to `b` under the Killing form**: `κ (b i) (killingDualBasis b j)` is
`1` when `i = j` and `0` otherwise (`TauCeti.killingForm_killingDualBasis`). -/
noncomputable def killingDualBasis (b : Module.Basis ι K L) : Module.Basis ι K L :=
  (killingForm K L).dualBasis (LieAlgebra.IsKilling.killingForm_nondegenerate K L) b

/-- The defining biorthogonality of the Killing-dual basis. -/
@[simp]
theorem killingForm_killingDualBasis (b : Module.Basis ι K L) (i j : ι) :
    killingForm K L (b i) (killingDualBasis b j) = if i = j then 1 else 0 :=
  LinearMap.BilinForm.apply_dualBasis_right _ killingForm_isSymm b i j

/-- The symmetric orientation of the defining biorthogonality of the Killing-dual basis. -/
@[simp]
theorem killingForm_killingDualBasis_left (b : Module.Basis ι K L) (i j : ι) :
    killingForm K L (killingDualBasis b i) (b j) = if i = j then 1 else 0 := by
  rw [LieModule.traceForm_comm, killingForm_killingDualBasis]
  simp only [eq_comm]

/-- Coordinates in the Killing-dual basis are Killing pairings against `b`. -/
@[simp]
theorem killingDualBasis_repr (b : Module.Basis ι K L) (v : L) (i : ι) :
    (killingDualBasis b).repr v i = killingForm K L (b i) v :=
  (LinearMap.BilinForm.dualBasis_repr_apply _ b v i).trans
    (LieModule.traceForm_comm K L L v (b i))

/-- Conjugating twice returns the original basis: the Killing-dual basis of the Killing-dual
basis of `b` is `b`. -/
@[simp]
theorem killingDualBasis_killingDualBasis (b : Module.Basis ι K L) :
    killingDualBasis (killingDualBasis b) = b :=
  LinearMap.BilinForm.dualBasis_dualBasis _ killingForm_isSymm b

/-- Coordinates in `b` are Killing pairings against the Killing-dual basis. -/
theorem repr_eq_killingForm (b : Module.Basis ι K L) (v : L) (i : ι) :
    b.repr v i = killingForm K L v (killingDualBasis b i) := by
  conv_lhs => rw [← killingDualBasis_killingDualBasis b]
  rw [killingDualBasis_repr, LieModule.traceForm_comm]

/-- **Expansion in `b`**, with the coefficients read off by the Killing-dual basis. -/
theorem sum_killingForm_smul_basis (b : Module.Basis ι K L) (v : L) :
    ∑ i, killingForm K L v (killingDualBasis b i) • b i = v := by
  conv_rhs => rw [← b.sum_repr v]
  exact sum_congr rfl fun i _ ↦ by rw [repr_eq_killingForm]

/-- **Expansion in the Killing-dual basis**, with the coefficients read off by `b`. -/
theorem sum_killingForm_smul_killingDualBasis (b : Module.Basis ι K L) (v : L) :
    ∑ i, killingForm K L (b i) v • killingDualBasis b i = v := by
  conv_rhs => rw [← (killingDualBasis b).sum_repr v]
  exact sum_congr rfl fun i _ ↦ by rw [killingDualBasis_repr]

/-- **The sum `∑ᵢ κ (p xᵢ) yᵢ` along a basis and its Killing-dual basis is the trace of `p`.**  The
Killing-dual basis reads off the coordinates in `b` (`TauCeti.repr_eq_killingForm`), so the sum is
the sum of the diagonal entries of the matrix of `p`. -/
theorem sum_killingForm_killingDualBasis_eq_trace (b : Module.Basis ι K L) (p : L →ₗ[K] L) :
    ∑ i, killingForm K L (p (b i)) (killingDualBasis b i) = LinearMap.trace K L p := by
  rw [LinearMap.trace_eq_matrix_trace K b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  exact sum_congr rfl fun i _ ↦ (repr_eq_killingForm b (p (b i)) i).symm

end DualBasis

/-! ### The canonical invariant element `∑ᵢ xᵢ ⊗ yᵢ` -/

section Bilinear

variable {W : Type w} [AddCommGroup W] [Module K W] (f : L →ₗ[K] L →ₗ[K] W)

/-- **The sum `∑ᵢ f xᵢ yᵢ` of a bilinear map along a basis and its Killing-dual basis does not
depend on the basis.**  Expanding each `c j` in the basis `b` produces exactly the coefficients
that expand `killingDualBasis b i` in `killingDualBasis c`. -/
theorem sum_apply_killingDualBasis_eq {ι ι' : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq ι']
    [Fintype ι'] (b : Module.Basis ι K L) (c : Module.Basis ι' K L) :
    ∑ i, f (b i) (killingDualBasis b i) = ∑ j, f (c j) (killingDualBasis c j) := by
  have expand : ∀ j : ι', f (c j) (killingDualBasis c j)
      = ∑ i, killingForm K L (c j) (killingDualBasis b i) • f (b i) (killingDualBasis c j) := by
    intro j
    conv_lhs => rw [← sum_killingForm_smul_basis b (c j)]
    rw [map_sum, LinearMap.sum_apply]
    exact sum_congr rfl fun i _ ↦ by rw [map_smul, LinearMap.smul_apply]
  rw [sum_congr rfl fun j _ ↦ expand j, Finset.sum_comm]
  refine sum_congr rfl fun i _ ↦ ?_
  conv_lhs => rw [← sum_killingForm_smul_killingDualBasis c (killingDualBasis b i)]
  rw [map_sum]
  exact sum_congr rfl fun j _ ↦ map_smul _ _ _

/-- **A Killing-adjoint pair of operators may be moved from one slot to the other.**  If `κ (p x) y`
is `κ x (q y)` then applying `p` to the basis vectors and applying `q` to their Killing duals give
the same sum, because both expand to `∑ᵢ ∑ⱼ κ (p xᵢ) yⱼ • f xⱼ yᵢ`. -/
theorem sum_apply_killingDualBasis_of_isAdjointPair {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι K L) {p q : L →ₗ[K] L}
    (hpq : LinearMap.IsAdjointPair (killingForm K L) (killingForm K L) p q) :
    ∑ i, f (p (b i)) (killingDualBasis b i) = ∑ i, f (b i) (q (killingDualBasis b i)) := by
  have expand₁ : ∀ i : ι, f (p (b i)) (killingDualBasis b i)
      = ∑ j, killingForm K L (p (b i)) (killingDualBasis b j) •
          f (b j) (killingDualBasis b i) := by
    intro i
    conv_lhs => rw [← sum_killingForm_smul_basis b (p (b i))]
    rw [map_sum, LinearMap.sum_apply]
    exact sum_congr rfl fun j _ ↦ by rw [map_smul, LinearMap.smul_apply]
  have expand₂ : ∀ i : ι, f (b i) (q (killingDualBasis b i))
      = ∑ j, killingForm K L (p (b j)) (killingDualBasis b i) •
          f (b i) (killingDualBasis b j) := by
    intro i
    conv_lhs => rw [← sum_killingForm_smul_killingDualBasis b (q (killingDualBasis b i))]
    rw [map_sum]
    exact sum_congr rfl fun j _ ↦ by rw [map_smul, hpq (b j) (killingDualBasis b i)]
  rw [sum_congr rfl fun i _ ↦ expand₁ i, sum_congr rfl fun i _ ↦ expand₂ i, Finset.sum_comm]

/-- **The element `∑ᵢ xᵢ ⊗ yᵢ` is invariant under the adjoint action.**  Read through a bilinear
map `f`, the Leibniz expansion of the adjoint action of `z` vanishes, because the two coefficient
families it produces are negatives of each other by the invariance of the Killing form. -/
theorem sum_apply_lie_killingDualBasis_add_eq_zero {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι K L) (z : L) :
    ∑ i, f ⁅z, b i⁆ (killingDualBasis b i) + ∑ i, f (b i) ⁅z, killingDualBasis b i⁆ = 0 := by
  have expand₁ : ∀ i : ι, f ⁅z, b i⁆ (killingDualBasis b i)
      = ∑ j, killingForm K L ⁅z, b i⁆ (killingDualBasis b j) •
          f (b j) (killingDualBasis b i) := by
    intro i
    conv_lhs => rw [← sum_killingForm_smul_basis b ⁅z, b i⁆]
    rw [map_sum, LinearMap.sum_apply]
    exact sum_congr rfl fun j _ ↦ by rw [map_smul, LinearMap.smul_apply]
  have expand₂ : ∀ i : ι, f (b i) ⁅z, killingDualBasis b i⁆
      = ∑ j, killingForm K L (b j) ⁅z, killingDualBasis b i⁆ •
          f (b i) (killingDualBasis b j) := by
    intro i
    conv_lhs => rw [← sum_killingForm_smul_killingDualBasis b ⁅z, killingDualBasis b i⁆]
    rw [map_sum]
    exact sum_congr rfl fun j _ ↦ map_smul _ _ _
  rw [sum_congr rfl fun i _ ↦ expand₁ i, sum_congr rfl fun i _ ↦ expand₂ i, Finset.sum_comm,
    ← Finset.sum_add_distrib]
  refine sum_eq_zero fun i _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine sum_eq_zero fun j _ ↦ ?_
  rw [← add_smul, LieModule.traceForm_apply_lie_apply' K L L z (b j) (killingDualBasis b i),
    neg_add_cancel, zero_smul]

end Bilinear

end TauCeti
