/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Bianchi
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Derivative.Form
public import Mathlib.Topology.VectorBundle.Riemannian

/-!
# The divergence of the curvature of a connection over a four-manifold

Let `∇` be a smooth connection on a vector bundle `V` over a Riemannian manifold `M`, with
curvature `R`, and let `∇ᵀ` be a smooth torsion-free connection on the tangent bundle, such as the
Levi-Civita connection. At a point `x`, the covariant derivative `∇_v R` of the curvature
(`CovariantDerivative.derivCurvatureTensor`) is antisymmetric in its two curvature arguments, so it
is a two-form on `T_x M` with values in the endomorphisms of `V x`,
`CovariantDerivative.derivCurvatureForm`, with `u ∧ w ↦ (∇_v R)(u, w)`
(`TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Derivative.Form`). The
second Bianchi identity for these forms
(`CovariantDerivative.derivCurvatureForm_cyclic_eq_zero`) says that this linear family of
two-forms is a Bianchi family in the sense of
`TauCeti.Analysis.InnerProductSpace.HodgeStar.Bianchi`.

The **divergence of the curvature** at `x`, along an orthonormal basis `(eᵢ)` of `T_x M`, is
`a ↦ ∑ᵢ (∇_{eᵢ} R)(a, eᵢ)`, the endomorphism-valued one-form `d_∇^* R`. When `M` has dimension four
and `T_x M` is oriented, the Hodge star acts on the form side of `∇_v R`, and the pointwise results
of that file give:

* the divergence of the Hodge dual of `∇R` vanishes,
  `∑ᵢ (⋆∇_{eᵢ} R)(a ∧ eᵢ) = 0`
  (`CovariantDerivative.sum_vectorFormHodgeStar_derivCurvatureForm_apply_ιMulti_eq_zero`);
* the divergence of the curvature is twice the divergence of the self-dual part of `∇R`, and twice
  that of its anti-self-dual part:
  `∑ᵢ (∇_{eᵢ} R)(a, eᵢ) = 2 ∑ᵢ (∇_{eᵢ} R)⁺(a ∧ eᵢ) = 2 ∑ᵢ (∇_{eᵢ} R)⁻(a ∧ eᵢ)`
  (`CovariantDerivative.sum_derivCurvatureTensor_eq_two_smul_sum_vectorFormSelfDualPart`,
  `CovariantDerivative.sum_derivCurvatureTensor_eq_two_smul_sum_vectorFormAntiSelfDualPart`).

Here `(∇_v R)⁺` is the self-dual part of the two-form `∇_v R`, not the covariant derivative of the
self-dual part `R⁺` of the curvature. The two agree once `∇_v` commutes with `⋆`, which needs a
metric-compatible `∇ᵀ` such as the Levi-Civita connection; that step is not proved here and `∇ᵀ`
is only assumed torsion-free. With it, the identity above becomes `d_∇^* F = 2 d_∇^* F⁺` of
four-dimensional gauge theory. For the large-parameter Seiberg–Witten equations, whose curvature
equation prescribes the self-dual part of the curvature but not its anti-self-dual part, this
is the route by which the curvature equation is expected to control the divergence
`∑ᵢ (∇_{eᵢ} R)(·, eᵢ)` that enters the differentiated Weitzenböck inequalities behind Taubes's
gradient bound
(`TauCeti.SeibergWitten.innerCovariantDerivative_self_add_mul_innerCovariantDerivative_self_le`),
although `∇R` itself is not bounded.

## Main results

* `CovariantDerivative.sum_vectorFormHodgeStar_derivCurvatureForm_apply_ιMulti_eq_zero`: the
  divergence of the Hodge dual of `∇R` vanishes in dimension four.
* `CovariantDerivative.sum_derivCurvatureTensor_eq_two_smul_sum_vectorFormSelfDualPart`,
  `CovariantDerivative.sum_derivCurvatureTensor_eq_two_smul_sum_vectorFormAntiSelfDualPart`: the
  divergence of the curvature is twice that of the self-dual part of `∇R`, and twice that of its
  anti-self-dual part.

## References

* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University Press,
  1990, Section 2.1.
* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 2.
-/

public section

open Bundle Module exteriorPower
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  (covT : CovariantDerivative I E (TangentSpace I : M → Type _))

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [ContMDiffCovariantDerivative covT ∞]
  (ht : covT.torsion = 0) (x : M) [Fact (finrank ℝ (TangentSpace I x) = 4)]
  (o : Orientation ℝ (TangentSpace I x) (Fin 4)) (hkl : 2 + 2 = finrank ℝ (TangentSpace I x))
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (a : TangentSpace I x)
include ht

/-- **The divergence of the Hodge dual of `∇R` vanishes** in dimension four: for a smooth
torsion-free `∇ᵀ`, an orientation of `T_x M` and an orthonormal basis `(eᵢ)`,
`∑ᵢ (⋆∇_{eᵢ} R)(a ∧ eᵢ) = 0`. -/
theorem sum_vectorFormHodgeStar_derivCurvatureForm_apply_ιMulti_eq_zero :
    ∑ i, o.vectorFormHodgeStar hkl (cov.derivCurvatureForm covT x (b i)) (ιMulti ℝ 2 ![a, b i]) =
      0 :=
  o.sum_vectorFormHodgeStar_apply_ιMulti_eq_zero hkl b _
    (cov.derivCurvatureForm_cyclic_eq_zero covT ht x) a

/-- **The divergence of the curvature is twice that of the self-dual part of `∇R`** in dimension
four: for a smooth torsion-free `∇ᵀ`, an orientation of `T_x M` and an orthonormal basis `(eᵢ)`,
`∑ᵢ (∇_{eᵢ} R)(a, eᵢ) = 2 ∑ᵢ (∇_{eᵢ} R)⁺(a ∧ eᵢ)`. This is `d_∇^* F = 2 d_∇^* F⁺` once `∇_v`
commutes with `⋆`, as it does for a metric-compatible `∇ᵀ`. -/
theorem sum_derivCurvatureTensor_eq_two_smul_sum_vectorFormSelfDualPart :
    ∑ i, cov.derivCurvatureTensor covT x (b i) a (b i) =
      (2 : ℝ) • ∑ i, o.vectorFormSelfDualPart hkl (cov.derivCurvatureForm covT x (b i))
        (ιMulti ℝ 2 ![a, b i]) := by
  simpa using o.sum_apply_ιMulti_eq_two_smul_sum_vectorFormSelfDualPart hkl b _
    (cov.derivCurvatureForm_cyclic_eq_zero covT ht x) a

/-- **The divergence of the curvature is twice that of the anti-self-dual part of `∇R`** in
dimension four: `∑ᵢ (∇_{eᵢ} R)(a, eᵢ) = 2 ∑ᵢ (∇_{eᵢ} R)⁻(a ∧ eᵢ)`. This is
`d_∇^* F = 2 d_∇^* F⁻` once `∇_v` commutes with `⋆`, as it does for a metric-compatible `∇ᵀ`. -/
theorem sum_derivCurvatureTensor_eq_two_smul_sum_vectorFormAntiSelfDualPart :
    ∑ i, cov.derivCurvatureTensor covT x (b i) a (b i) =
      (2 : ℝ) • ∑ i, o.vectorFormAntiSelfDualPart hkl (cov.derivCurvatureForm covT x (b i))
        (ιMulti ℝ 2 ![a, b i]) := by
  simpa using o.sum_apply_ιMulti_eq_two_smul_sum_vectorFormAntiSelfDualPart hkl b _
    (cov.derivCurvatureForm_cyclic_eq_zero covT ht x) a

end CovariantDerivative
