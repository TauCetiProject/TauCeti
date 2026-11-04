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
# Normed real and complex Clifford algebras

This file equips every real Clifford algebra `Cliff(p, q)`, and the Clifford algebra of every
quadratic form on a complex coordinate space `ℂⁿ`, with a normed-algebra structure whose topology is
the existing module topology. The norm is induced from the matrix norm along the left-regular
representation in the Clifford basis of the standard basis. Left multiplication is injective, so
this is a genuine norm, and its realization as a ring homomorphism makes it submultiplicative.

The topology does not depend on this presentation: an injective linear map from a
finite-dimensional real or complex vector space is a closed embedding, so the induced norm topology
agrees with the module topology already installed on Clifford algebras.

A complex Clifford algebra is in particular a finite-dimensional normed real algebra. Its group of
units is therefore a real Lie group, and the closed-subgroup theorem applies to the complex Spin
groups inside it.

## Main results

* `CliffordAlgebra.isClosedEmbedding_leftMulMatrix`: for a quadratic form on `𝕜ⁿ`, the
  left-regular matrix representation is a closed embedding for the module topology.
* `CliffordAlgebra.instNormedRingRealCliffordAlgebra` gives `Cliff(p, q)` a normed-ring structure.
* `CliffordAlgebra.instNormOneClassRealCliffordAlgebra` proves that the unit has norm one.
* `CliffordAlgebra.instNormedAlgebraRealCliffordAlgebra` makes it a real normed algebra.
* `CliffordAlgebra.norm_def` and `CliffordAlgebra.nnnorm_def` characterize the norm by the
  left-regular representation.
* `CliffordAlgebra.instNormedRingComplexCliffordAlgebra`,
  `CliffordAlgebra.instNormOneClassComplexCliffordAlgebra` and
  `CliffordAlgebra.instNormedAlgebraComplexCliffordAlgebra` are the same structures for the
  Clifford algebra of a quadratic form `Q` on `Fin n → ℂ`, and `CliffordAlgebra.norm_complex_def`
  and `CliffordAlgebra.nnnorm_complex_def` characterize its norm.
* `CliffordAlgebra.instNormedAlgebraRealComplexCliffordAlgebra`,
  `CliffordAlgebra.instNormedSpaceRealComplexCliffordAlgebra` and
  `CliffordAlgebra.instFiniteDimensionalRealComplexCliffordAlgebra` make that complex Clifford
  algebra a finite-dimensional real normed algebra, with real scalars acting through `ℂ`.
-/

public section

noncomputable section

namespace CliffordAlgebra

open TauCeti
open scoped Matrix.Norms.Operator

/-- For a quadratic form on a coordinate space `𝕜ⁿ` over a complete nontrivially normed field, the
left-regular matrix representation in the Clifford basis of the standard basis is a closed
embedding for the module topology of the Clifford algebra. Both the real and the complex normed
structures below transport their norm along it without changing the topology. -/
theorem isClosedEmbedding_leftMulMatrix {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [Invertible (2 : 𝕜)] {n : ℕ} (Q : QuadraticForm 𝕜 (Fin n → 𝕜)) :
    Topology.IsClosedEmbedding (Algebra.leftMulMatrix (basis Q (Pi.basisFun 𝕜 (Fin n)))) := by
  let b := basis Q (Pi.basisFun 𝕜 (Fin n))
  have hinjective : Function.Injective (Algebra.leftMulMatrix b).toLinearMap :=
    Algebra.leftMulMatrix_injective b
  exact LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hinjective)

/-- The metric induced by the left-regular matrix norm on a real Clifford algebra. Its topology
is the existing module topology. -/
noncomputable instance instMetricSpaceRealCliffordAlgebra (p q : ℕ) :
    MetricSpace (CliffordAlgebra (realCliffordForm p q)) := by
  let b := basis (realCliffordForm p q) (Pi.basisFun ℝ (Fin (p + q)))
  let f := Algebra.leftMulMatrix b
  let induced := NormedRing.induced (CliffordAlgebra (realCliffordForm p q))
    (Matrix (Finset (Fin (p + q))) (Finset (Fin (p + q))) ℝ) f
    (Algebra.leftMulMatrix_injective b)
  exact induced.toMetricSpace.replaceTopology
    (isClosedEmbedding_leftMulMatrix _).isEmbedding.eq_induced

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

/-! ### Complex coordinate spaces -/

section Complex

variable {n : ℕ} (Q : QuadraticForm ℂ (Fin n → ℂ))

/-- The metric induced by the left-regular matrix norm on the Clifford algebra of a quadratic form
on `ℂⁿ`. Its topology is the existing module topology. -/
noncomputable instance instMetricSpaceComplexCliffordAlgebra :
    MetricSpace (CliffordAlgebra Q) := by
  let b := basis Q (Pi.basisFun ℂ (Fin n))
  let f := Algebra.leftMulMatrix b
  let induced := NormedRing.induced (CliffordAlgebra Q) (Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ)
    f (Algebra.leftMulMatrix_injective b)
  exact induced.toMetricSpace.replaceTopology
    (isClosedEmbedding_leftMulMatrix _).isEmbedding.eq_induced

/-- The Clifford algebra of a quadratic form on `ℂⁿ` is a normed ring for its left-regular matrix
norm. -/
noncomputable instance instNormedRingComplexCliffordAlgebra : NormedRing (CliffordAlgebra Q) := by
  let b := basis Q (Pi.basisFun ℂ (Fin n))
  let induced := NormedRing.induced (CliffordAlgebra Q) (Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ)
    (Algebra.leftMulMatrix b) (Algebra.leftMulMatrix_injective b)
  exact {
    norm := induced.norm
    dist_eq := induced.dist_eq
    norm_mul_le := induced.norm_mul_le
  }

/-- The norm on the Clifford algebra of a quadratic form on `ℂⁿ` is the operator norm of its
left-regular matrix in the Clifford basis of the standard basis. -/
theorem norm_complex_def (x : CliffordAlgebra Q) :
    ‖x‖ = ‖Algebra.leftMulMatrix (basis Q (Pi.basisFun ℂ (Fin n))) x‖ :=
  rfl

/-- The nonnegative norm on the Clifford algebra of a quadratic form on `ℂⁿ` is the operator
nonnegative norm of its left-regular matrix in the Clifford basis of the standard basis. -/
theorem nnnorm_complex_def (x : CliffordAlgebra Q) :
    ‖x‖₊ = ‖Algebra.leftMulMatrix (basis Q (Pi.basisFun ℂ (Fin n))) x‖₊ :=
  rfl

/-- The unit of the Clifford algebra of a quadratic form on `ℂⁿ` has norm one for the left-regular
matrix norm. -/
noncomputable instance instNormOneClassComplexCliffordAlgebra : NormOneClass (CliffordAlgebra Q) :=
  NormOneClass.induced (CliffordAlgebra Q) (Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ)
    (Algebra.leftMulMatrix (basis Q (Pi.basisFun ℂ (Fin n))))

/-- The Clifford algebra of a quadratic form on `ℂⁿ` is a complex normed algebra for its
left-regular matrix norm. -/
noncomputable instance instNormedAlgebraComplexCliffordAlgebra :
    NormedAlgebra ℂ (CliffordAlgebra Q) where
  norm_smul_le :=
    (NormedAlgebra.induced ℂ (CliffordAlgebra Q) (Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ)
      (Algebra.leftMulMatrix (basis Q (Pi.basisFun ℂ (Fin n))))).norm_smul_le

/-- The Clifford algebra of a quadratic form on `ℂⁿ` is a real normed algebra for its left-regular
matrix norm, with real scalars acting through `ℂ`.

The algebra structure is the Clifford algebra's own `CliffordAlgebra.instAlgebra'`, rather than
Mathlib's restriction of scalars `Algebra.complexToReal`, so that real scalar multiplication is
syntactically the one that the Clifford algebra API produces. -/
noncomputable instance instNormedAlgebraRealComplexCliffordAlgebra :
    NormedAlgebra ℝ (CliffordAlgebra Q) where
  toAlgebra := instAlgebra' Q
  norm_smul_le r x := by
    rw [← IsScalarTower.algebraMap_smul ℂ r x]
    simpa only [Complex.coe_algebraMap, Complex.norm_real] using norm_smul_le (algebraMap ℝ ℂ r) x

/-- The real normed-space structure of the Clifford algebra of a quadratic form on `ℂⁿ`, through
its own real scalar multiplication. This takes precedence over `NormedSpace.complexToReal`. -/
noncomputable instance instNormedSpaceRealComplexCliffordAlgebra :
    NormedSpace ℝ (CliffordAlgebra Q) :=
  @NormedAlgebra.toNormedSpace ℝ (CliffordAlgebra Q) _ _
    (instNormedAlgebraRealComplexCliffordAlgebra Q)

/-- The Clifford algebra of a quadratic form on `ℂⁿ` is finite-dimensional over `ℝ`. -/
instance instFiniteDimensionalRealComplexCliffordAlgebra :
    FiniteDimensional ℝ (CliffordAlgebra Q) :=
  Module.Finite.trans ℂ (CliffordAlgebra Q)

end Complex

end CliffordAlgebra
