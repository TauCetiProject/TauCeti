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

variable {ι : Type*} [DecidableEq ι]

omit [LieAlgebra.IsKilling K L] in
/-- The Killing form is symmetric, in the `LinearMap.BilinForm.IsSymm` form that the dual-basis API
asks for; Mathlib states it as `LinearMap.IsSymm` (`LieModule.traceForm_isSymm`). -/
private theorem killingForm_isSymm : (killingForm K L).IsSymm :=
  LinearMap.BilinForm.isSymm_iff.mpr (LieModule.traceForm_isSymm K L L)

section Finite

variable [Finite ι]

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

/-- Taking the Killing dual twice returns the original basis: the Killing-dual basis of the
Killing-dual basis of `b` is `b`. -/
@[simp]
theorem killingDualBasis_killingDualBasis (b : Module.Basis ι K L) :
    killingDualBasis (killingDualBasis b) = b :=
  LinearMap.BilinForm.dualBasis_dualBasis _ killingForm_isSymm b

/-- Coordinates in `b` are Killing pairings against the Killing-dual basis. -/
theorem repr_eq_killingForm (b : Module.Basis ι K L) (v : L) (i : ι) :
    b.repr v i = killingForm K L v (killingDualBasis b i) := by
  rw [LieModule.traceForm_comm, ← killingDualBasis_repr, killingDualBasis_killingDualBasis]

end Finite

variable [Fintype ι]

/-- **Expansion in `b`**, with the coefficients read off by the Killing-dual basis. -/
@[simp]
theorem sum_killingForm_smul_basis (b : Module.Basis ι K L) (v : L) :
    ∑ i, killingForm K L v (killingDualBasis b i) • b i = v := by
  simp only [← repr_eq_killingForm, Module.Basis.sum_repr]

/-- **Expansion in the Killing-dual basis**, with the coefficients read off by `b`. -/
@[simp]
theorem sum_killingForm_smul_killingDualBasis (b : Module.Basis ι K L) (v : L) :
    ∑ i, killingForm K L (b i) v • killingDualBasis b i = v := by
  simp only [← killingDualBasis_repr, Module.Basis.sum_repr]

/-- **The sum `∑ᵢ κ (p xᵢ) yᵢ` along a basis and its Killing-dual basis is the trace of `p`.**  The
Killing-dual basis reads off the coordinates in `b` (`TauCeti.repr_eq_killingForm`), so the sum is
the sum of the diagonal entries of the matrix of `p`. -/
theorem sum_killingForm_killingDualBasis_eq_trace (b : Module.Basis ι K L) (p : L →ₗ[K] L) :
    ∑ i, killingForm K L (p (b i)) (killingDualBasis b i) = LinearMap.trace K L p := by
  simp [LinearMap.trace_eq_matrix_trace K b, Matrix.trace, LinearMap.toMatrix_apply,
    repr_eq_killingForm]

end DualBasis

/-! ### The canonical invariant element `∑ᵢ xᵢ ⊗ yᵢ` -/

section Bilinear

variable {W : Type w} [AddCommGroup W] [Module K W] (f : L →ₗ[K] L →ₗ[K] W)
  {ι ι' : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq ι'] [Fintype ι']

/-- **Expansion of the first argument of a bilinear map in `b`**, with the coefficients read off
by the Killing-dual basis. -/
@[simp]
theorem _root_.LinearMap.sum_killingForm_smul_apply_basis (b : Module.Basis ι K L) (u v : L) :
    ∑ j, killingForm K L u (killingDualBasis b j) • f (b j) v = f u v := by
  conv_rhs => rw [← sum_killingForm_smul_basis b u]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]

/-- **Expansion of the second argument of a bilinear map in the Killing-dual basis**, with the
coefficients read off by `b`. -/
@[simp]
theorem _root_.LinearMap.sum_killingForm_smul_apply_killingDualBasis (b : Module.Basis ι K L)
    (u v : L) :
    ∑ j, killingForm K L (b j) v • f u (killingDualBasis b j) = f u v := by
  conv_rhs => rw [← sum_killingForm_smul_killingDualBasis b v]
  simp only [map_sum, map_smul]

/-- **The sum `∑ᵢ f xᵢ yᵢ` of a bilinear map along a basis and its Killing-dual basis does not
depend on the basis.**  Expanding each `c j` in the basis `b` produces exactly the coefficients
that expand `killingDualBasis b i` in `killingDualBasis c`. -/
theorem sum_apply_killingDualBasis_eq (b : Module.Basis ι K L) (c : Module.Basis ι' K L) :
    ∑ i, f (b i) (killingDualBasis b i) = ∑ j, f (c j) (killingDualBasis c j) :=
  calc ∑ i, f (b i) (killingDualBasis b i)
      = ∑ i, ∑ j, killingForm K L (c j) (killingDualBasis b i) •
          f (b i) (killingDualBasis c j) :=
        sum_congr rfl fun i _ ↦ (f.sum_killingForm_smul_apply_killingDualBasis c _ _).symm
    _ = ∑ j, f (c j) (killingDualBasis c j) := by
        rw [Finset.sum_comm]
        exact sum_congr rfl fun j _ ↦ f.sum_killingForm_smul_apply_basis b _ _

/-- **A Killing-adjoint pair of operators may be moved from one slot to the other.**  If `κ (p x) y`
is `κ x (q y)` then applying `p` to the basis vectors and applying `q` to their Killing duals give
the same sum, because both expand to `∑ᵢ ∑ⱼ κ (p xᵢ) yⱼ • f xⱼ yᵢ`. -/
theorem sum_apply_killingDualBasis_of_isAdjointPair (b : Module.Basis ι K L) {p q : L →ₗ[K] L}
    (hpq : LinearMap.IsAdjointPair (killingForm K L) (killingForm K L) p q) :
    ∑ i, f (p (b i)) (killingDualBasis b i) = ∑ i, f (b i) (q (killingDualBasis b i)) :=
  calc ∑ i, f (p (b i)) (killingDualBasis b i)
      = ∑ i, ∑ j, killingForm K L (p (b i)) (killingDualBasis b j) •
          f (b j) (killingDualBasis b i) :=
        sum_congr rfl fun i _ ↦ (f.sum_killingForm_smul_apply_basis b _ _).symm
    _ = ∑ i, ∑ j, killingForm K L (b j) (q (killingDualBasis b i)) •
          f (b i) (killingDualBasis b j) := by
        rw [Finset.sum_comm]
        simp only [hpq _ _]
    _ = ∑ i, f (b i) (q (killingDualBasis b i)) :=
        sum_congr rfl fun i _ ↦ f.sum_killingForm_smul_apply_killingDualBasis b _ _

/-- **The element `∑ᵢ xᵢ ⊗ yᵢ` is invariant under the adjoint action.**  Read through a bilinear
map `f`, the Leibniz expansion of the adjoint action of `z` vanishes, because the two coefficient
families it produces are negatives of each other by the invariance of the Killing form. -/
theorem sum_apply_lie_killingDualBasis_add_eq_zero (b : Module.Basis ι K L) (z : L) :
    ∑ i, f ⁅z, b i⁆ (killingDualBasis b i) + ∑ i, f (b i) ⁅z, killingDualBasis b i⁆ = 0 := by
  simp_rw [← f.sum_killingForm_smul_apply_basis b ⁅z, b _⁆,
    ← f.sum_killingForm_smul_apply_killingDualBasis b (b _) ⁅z, _⁆]
  rw [Finset.sum_comm]
  simp [LieModule.traceForm_apply_lie_apply' K L L z]

end Bilinear

end TauCeti
