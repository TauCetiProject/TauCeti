/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Euclidean coordinates in a finite basis

A finite basis `b : Module.Basis ι 𝕜 E` identifies a Hausdorff topological vector space `E`
over `ℝ` or `ℂ` with `EuclideanSpace 𝕜 ι`. This identification sends the basis vectors to
the standard basis and reads directional derivatives along `b` as partial derivatives.
Over `ℝ`, it carries the Haar measure of the basis to Lebesgue measure.

For a finite-dimensional real normed space, take `b = Module.finBasis ℝ E` to hand a function
on the model space of a manifold, such as a function read in a chart, to the analysis on
Euclidean domains.

## Main declarations

* `Module.Basis.euclideanEquivL`: the coordinates in a finite basis, as a continuous linear
  equivalence with Euclidean space.
* `Module.Basis.fderiv_comp_euclideanEquivL_symm_single`: derivatives in Euclidean coordinates
  along standard basis vectors are directional derivatives along the given basis.
* `Module.Basis.measurePreserving_euclideanEquivL` and
  `Module.Basis.measurePreserving_euclideanEquivL_symm`: transport between the Haar measure
  of a real basis and Lebesgue measure.
-/

public section

open MeasureTheory

noncomputable section

namespace Module.Basis

variable {ι 𝕜 E : Type*} [RCLike 𝕜]

section Topological

variable [Finite ι] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] (b : Basis ι 𝕜 E)

/-- Coordinates in a finite basis, as a continuous linear equivalence with Euclidean space. -/
def euclideanEquivL : E ≃L[𝕜] EuclideanSpace 𝕜 ι :=
  b.equivFunL.trans (EuclideanSpace.equiv ι 𝕜).symm

/-- The Euclidean coordinate equivalence is the basis coordinate map followed by the inverse
of the identification of Euclidean space with the space of coordinate functions. -/
theorem euclideanEquivL_def :
    b.euclideanEquivL = b.equivFunL.trans (EuclideanSpace.equiv ι 𝕜).symm := (rfl)

/-- Evaluation of Euclidean coordinates agrees with the basis representation. -/
@[simp]
theorem euclideanEquivL_apply (v : E) (i : ι) :
    b.euclideanEquivL v i = b.repr v i := (rfl)

/-- The inverse coordinate map expands a vector in the given basis. -/
theorem euclideanEquivL_symm_apply [Fintype ι] (z : EuclideanSpace 𝕜 ι) :
    b.euclideanEquivL.symm z = ∑ i, z i • b i :=
  b.equivFun_symm_apply z

/-- The inverse coordinate map sends a standard basis vector to the corresponding vector of
the given basis. -/
@[simp]
theorem euclideanEquivL_symm_single [DecidableEq ι] (i : ι) :
    b.euclideanEquivL.symm (EuclideanSpace.single i 1) = b i :=
  _root_.Basis.equivFun_symm_single b i

/-- The coordinate map sends a vector of the given basis to the corresponding standard basis
vector. -/
@[simp]
theorem euclideanEquivL_basis [DecidableEq ι] (i : ι) :
    b.euclideanEquivL (b i) = EuclideanSpace.single i 1 := by
  rw [← b.euclideanEquivL_symm_single i, ContinuousLinearEquiv.apply_symm_apply]

/-- The coordinate map carries the given basis to the standard Euclidean basis. -/
theorem map_euclideanEquivL [Fintype ι] :
    b.map b.euclideanEquivL.toLinearEquiv = (EuclideanSpace.basisFun ι 𝕜).toBasis := by
  classical
  ext i
  simp

end Topological

section Derivative

variable [Finite ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (b : Basis ι 𝕜 E)

/-- The derivative of a function read in Euclidean coordinates, along a standard basis vector,
is the derivative of the function along the corresponding vector of the given basis. -/
theorem fderiv_comp_euclideanEquivL_symm_single {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] (f : E → F) (z : EuclideanSpace 𝕜 ι) (i : ι) :
    fderiv 𝕜 (f ∘ b.euclideanEquivL.symm) z (EuclideanSpace.single i 1) =
      fderiv 𝕜 f (b.euclideanEquivL.symm z) (b i) := by
  let := Fintype.ofFinite ι
  rw [ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, euclideanEquivL_symm_single]

end Derivative

section Measure

variable [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] (b : Basis ι ℝ E)

/-- Euclidean coordinates carry the Haar measure of the given basis to Lebesgue measure. -/
@[simp]
theorem map_euclideanEquivL_addHaar :
    b.addHaar.map b.euclideanEquivL = volume := by
  rw [Module.Basis.map_addHaar, b.map_euclideanEquivL, OrthonormalBasis.addHaar_eq_volume]

/-- The coordinate map preserves the Haar measure of the given basis and Lebesgue measure. -/
theorem measurePreserving_euclideanEquivL :
    MeasurePreserving b.euclideanEquivL b.addHaar volume :=
  ⟨b.euclideanEquivL.continuous.measurable, b.map_euclideanEquivL_addHaar⟩

/-- The inverse coordinate map preserves Lebesgue measure and the Haar measure of the basis. -/
theorem measurePreserving_euclideanEquivL_symm :
    MeasurePreserving b.euclideanEquivL.symm volume b.addHaar :=
  MeasurePreserving.symm b.euclideanEquivL.toHomeomorph.toMeasurableEquiv
    b.measurePreserving_euclideanEquivL

/-- Inverse Euclidean coordinates carry Lebesgue measure to the Haar measure of the basis. -/
@[simp]
theorem map_euclideanEquivL_symm_volume :
    (volume : Measure (EuclideanSpace ℝ ι)).map b.euclideanEquivL.symm = b.addHaar :=
  b.measurePreserving_euclideanEquivL_symm.map_eq

end Measure

end Module.Basis
