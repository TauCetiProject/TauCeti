/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic
public import TauCeti.Topology.Algebra.CliffordAlgebra.Basic
public import Mathlib.Analysis.Matrix.Normed

/-!
# Normed real Clifford algebras

This file equips every real Clifford algebra `Cliff(p, q)` with a normed-algebra structure whose
topology is the existing module topology. The norm is induced from the matrix norm along the
left-regular representation in the standard Clifford basis. Left multiplication is injective, so
this is a genuine norm, and its realization as a ring homomorphism makes it submultiplicative.

The topology does not depend on this presentation: an injective linear map from a
finite-dimensional real vector space is a closed embedding, so the induced norm topology agrees
with the module topology already installed on Clifford algebras.

## Main results

* `CliffordAlgebra.instNormedRingRealCliffordAlgebra` gives `Cliff(p, q)` a normed-ring structure.
* `CliffordAlgebra.instNormOneClassRealCliffordAlgebra` proves that the unit has norm one.
* `CliffordAlgebra.instNormedAlgebraRealCliffordAlgebra` makes it a real normed algebra.
* `CliffordAlgebra.norm_def` and `CliffordAlgebra.nnnorm_def` characterize the norm by the
  left-regular representation.
-/

public section

noncomputable section

namespace CliffordAlgebra

open TauCeti
open scoped Matrix.Norms.Operator

/-- The metric induced by the left-regular matrix norm on a real Clifford algebra. Its topology
is the existing module topology. -/
noncomputable instance instMetricSpaceRealCliffordAlgebra (p q : ℕ) :
    MetricSpace (CliffordAlgebra (realCliffordForm p q)) := by
  let b := basis (realCliffordForm p q) (Pi.basisFun ℝ (Fin (p + q)))
  let f := Algebra.leftMulMatrix b
  let induced := NormedRing.induced (CliffordAlgebra (realCliffordForm p q))
    (Matrix (Finset (Fin (p + q))) (Finset (Fin (p + q))) ℝ) f
    (Algebra.leftMulMatrix_injective b)
  apply induced.toMetricSpace.replaceTopology
  have hinjective : Function.Injective f.toLinearMap :=
    Algebra.leftMulMatrix_injective b
  exact (LinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr hinjective)).isEmbedding.eq_induced

/-- A real Clifford algebra is a normed ring for its left-regular matrix norm. -/
noncomputable instance instNormedRingRealCliffordAlgebra (p q : ℕ) :
    NormedRing (CliffordAlgebra (realCliffordForm p q)) := by
  let b := basis (realCliffordForm p q) (Pi.basisFun ℝ (Fin (p + q)))
  let f := Algebra.leftMulMatrix b
  let induced := NormedRing.induced (CliffordAlgebra (realCliffordForm p q))
    (Matrix (Finset (Fin (p + q))) (Finset (Fin (p + q))) ℝ) f
    (Algebra.leftMulMatrix_injective b)
  exact {
    norm := induced.norm
    dist_eq := induced.dist_eq
    norm_mul_le := induced.norm_mul_le
  }

/-- The norm on a real Clifford algebra is the operator norm of its left-regular matrix in the
standard Clifford basis. -/
theorem norm_def {p q : ℕ} (x : CliffordAlgebra (realCliffordForm p q)) :
    ‖x‖ =
      ‖Algebra.leftMulMatrix (basis (realCliffordForm p q) (Pi.basisFun ℝ (Fin (p + q)))) x‖ :=
  rfl

/-- The nonnegative norm on a real Clifford algebra is the operator nonnegative norm of its
left-regular matrix in the standard Clifford basis. -/
theorem nnnorm_def {p q : ℕ} (x : CliffordAlgebra (realCliffordForm p q)) :
    ‖x‖₊ =
      ‖Algebra.leftMulMatrix (basis (realCliffordForm p q) (Pi.basisFun ℝ (Fin (p + q)))) x‖₊ :=
  rfl

/-- The unit of a real Clifford algebra has norm one for the left-regular matrix norm. -/
noncomputable instance instNormOneClassRealCliffordAlgebra (p q : ℕ) :
    NormOneClass (CliffordAlgebra (realCliffordForm p q)) :=
  let b := basis (realCliffordForm p q) (Pi.basisFun ℝ (Fin (p + q)))
  NormOneClass.induced (CliffordAlgebra (realCliffordForm p q))
    (Matrix (Finset (Fin (p + q))) (Finset (Fin (p + q))) ℝ)
    (Algebra.leftMulMatrix b)

/-- A real Clifford algebra is a normed algebra for its left-regular matrix norm. -/
noncomputable instance instNormedAlgebraRealCliffordAlgebra (p q : ℕ) :
    NormedAlgebra ℝ (CliffordAlgebra (realCliffordForm p q)) where
  norm_smul_le := by
    let b := basis (realCliffordForm p q) (Pi.basisFun ℝ (Fin (p + q)))
    exact (NormedAlgebra.induced ℝ (CliffordAlgebra (realCliffordForm p q))
      (Matrix (Finset (Fin (p + q))) (Finset (Fin (p + q))) ℝ)
      (Algebra.leftMulMatrix b)).norm_smul_le

end CliffordAlgebra
