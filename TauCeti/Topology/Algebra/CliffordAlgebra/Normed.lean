/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic
public import TauCeti.Topology.Algebra.CliffordAlgebra.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.ToLin

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

* `CliffordAlgebra.realCliffordNormedRing` is the normed-ring structure induced by the
  left-regular representation.
* `CliffordAlgebra.instNormedRingRealCliffordAlgebra` gives `Cliff(p, q)` a normed-ring structure.
* `CliffordAlgebra.instNormedAlgebraRealCliffordAlgebra` makes it a real normed algebra.
-/

public section

noncomputable section

namespace CliffordAlgebra

open TauCeti
open scoped Matrix.Norms.Operator

/-- The normed-ring structure on a real Clifford algebra induced from the operator norm of its
left-regular matrix representation. -/
noncomputable abbrev realCliffordNormedRing (p q : ℕ) :
    NormedRing (CliffordAlgebra (realCliffordForm p q)) :=
  let b := basis (realCliffordForm p q) (Pi.basisFun ℝ (Fin (p + q)))
  let f := Algebra.leftMulMatrix b
  NormedRing.induced (CliffordAlgebra (realCliffordForm p q))
    (Matrix (Finset (Fin (p + q))) (Finset (Fin (p + q))) ℝ) f
    (Algebra.leftMulMatrix_injective b)

/-- The real normed-algebra structure associated to `realCliffordNormedRing`. -/
noncomputable abbrev realCliffordNormedAlgebra (p q : ℕ) :
    @NormedAlgebra ℝ (CliffordAlgebra (realCliffordForm p q)) _
      (realCliffordNormedRing p q).toSeminormedRing :=
  let b := basis (realCliffordForm p q) (Pi.basisFun ℝ (Fin (p + q)))
  NormedAlgebra.induced ℝ (CliffordAlgebra (realCliffordForm p q))
    (Matrix (Finset (Fin (p + q))) (Finset (Fin (p + q))) ℝ)
    (Algebra.leftMulMatrix b)

/-- The metric induced by the left-regular matrix norm on a real Clifford algebra. Its topology
is the existing module topology. -/
noncomputable instance instMetricSpaceRealCliffordAlgebra (p q : ℕ) :
    MetricSpace (CliffordAlgebra (realCliffordForm p q)) := by
  let b := basis (realCliffordForm p q) (Pi.basisFun ℝ (Fin (p + q)))
  let f := Algebra.leftMulMatrix b
  apply (realCliffordNormedRing p q).toMetricSpace.replaceTopology
  have hinjective : Function.Injective f.toLinearMap :=
    Algebra.leftMulMatrix_injective b
  exact (LinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr hinjective)).isEmbedding.eq_induced

/-- The normed additive group induced by the left-regular matrix norm on a real Clifford algebra. -/
noncomputable instance instNormedAddCommGroupRealCliffordAlgebra (p q : ℕ) :
    NormedAddCommGroup (CliffordAlgebra (realCliffordForm p q)) where
  norm := (realCliffordNormedRing p q).norm
  dist_eq := (realCliffordNormedRing p q).dist_eq

/-- A real Clifford algebra is a normed ring for its left-regular matrix norm. -/
noncomputable instance instNormedRingRealCliffordAlgebra (p q : ℕ) :
    NormedRing (CliffordAlgebra (realCliffordForm p q)) where
  dist_eq := (realCliffordNormedRing p q).dist_eq
  norm_mul_le := (realCliffordNormedRing p q).norm_mul_le

/-- A real Clifford algebra is a real normed space for its left-regular matrix norm. -/
noncomputable instance instNormedSpaceRealCliffordAlgebra (p q : ℕ) :
    NormedSpace ℝ (CliffordAlgebra (realCliffordForm p q)) where
  norm_smul_le := (realCliffordNormedAlgebra p q).norm_smul_le

/-- A real Clifford algebra is a normed algebra for its left-regular matrix norm. -/
noncomputable instance instNormedAlgebraRealCliffordAlgebra (p q : ℕ) :
    NormedAlgebra ℝ (CliffordAlgebra (realCliffordForm p q)) where
  norm_smul_le := (realCliffordNormedAlgebra p q).norm_smul_le

end CliffordAlgebra
