/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar
import Mathlib.Analysis.InnerProductSpace.Dual
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ContractedBianchi
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Einstein's constancy theorem

Let `∇` be a smooth metric-compatible torsion-free connection on the tangent bundle of a
Riemannian manifold `M` of dimension `n`, such as its Levi-Civita connection, and suppose that its
Ricci tensor is pointwise proportional to the metric, `Ric = a g` for a function `a : M → ℝ`.
If `n ≠ 2`, then `da = 0`; hence `a` is constant when `M` is connected, and an Einstein metric in
dimension at least three has constant Einstein factor.

The proof contracts the second Bianchi identity twice. With
`(∇_X R)(Y, Z) σ = ∇_X (R(Y, Z) σ) - R(∇_X Y, Z) σ - R(Y, ∇_X Z) σ - R(Y, Z) (∇_X σ)`, contracting
the direction `X` against the output turns the identity into
`(div R)(Y, Z) W = (∇_Y Ric)(Z, W) - (∇_Z Ric)(Y, W)`, and contracting `Z` with `W` through the
metric, using pair symmetry, turns the left side into `(div Ric)(Y)`: this is the contracted
Bianchi identity `2 div Ric = d Scal`. For `Ric = a g`, metric compatibility gives
`(∇_X Ric)(Y, Z) = da(X) ⟪Y, Z⟫`, and the twice contracted identity reads `da = n da - da`, that
is `(n - 2) da = 0`. In dimension two every metric has `Ric = K g` for its Gaussian curvature `K`,
which need not be constant.

The contractions are taken in an orthonormal basis of the tangent space at the point, using the
covariant derivative of the curvature tensor: the Riemannian divergence formula
`CovariantDerivative.IsMetricCompatible.sum_inner_derivCurvatureTensor_self_eq_sub`, pair
interchange `CovariantDerivative.IsMetricCompatible.inner_derivCurvatureTensor_swap_pairs`, and the
trace identity `CovariantDerivative.sum_inner_derivCurvatureTensor_eq_derivRicciTensor`.

## Main results

* `CovariantDerivative.mfderiv_eq_zero_of_ricciTensor_eq_smul_inner`: if `Ric = a g` and
  `n ≠ 2`, then `da` vanishes at every point.
* `CovariantDerivative.eq_of_ricciTensor_eq_smul_inner`: **Einstein's constancy theorem**; on a
  preconnected manifold of positive dimension other than two, `Ric = a g` forces `a` to be
  constant.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7 (the contracted Bianchi identity and Einstein metrics).
-/

public section

open Bundle
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  [ContMDiffCovariantDerivative cov ∞]

/-- For a metric-compatible connection whose Ricci tensor is `a g`, the covariant derivative of the
Ricci tensor is `(∇_X Ric)(B, C) = da(X) ⟪B, C⟫`. -/
private theorem IsMetricCompatible.covariantDerivative_ricciTensor_eq
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {a : M → ℝ} (ha : ∀ y, cov.ricciTensor y = a y • innerₗ (TangentSpace I y)) {x : M}
    (hax : MDifferentiableAt I 𝓘(ℝ) a x) (X : Π y : M, TangentSpace I y)
    {B C : Π y : M, TangentSpace I y} (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) :
    mvfderiv I (fun y ↦ cov.ricciTensor y (B y) (C y)) x (X x) -
        cov.ricciTensor x (cov B x (X x)) (C x) - cov.ricciTensor x (B x) (cov C x (X x)) =
      mvfderiv I a x (X x) * ⟪B x, C x⟫_ℝ := by
  have hfun : (fun y ↦ cov.ricciTensor y (B y) (C y)) = a * fun y ↦ ⟪B y, C y⟫_ℝ := by
    funext y
    simp [ha]
  -- The bundle argument of `ContMDiff.inner_bundle` is not inferred through `TangentSpace`.
  have hBC' : CMDiff ∞ fun y ↦ ⟪B y, C y⟫_ℝ :=
    ContMDiff.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x) (b := id) hB hC
  have hBC : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ ⟪B y, C y⟫_ℝ) x := hBC'.mdifferentiableAt (by simp)
  have hd : mvfderiv I (fun y ↦ ⟪B y, C y⟫_ℝ) x (X x) =
      ⟪cov B x (X x), C x⟫_ℝ + ⟪B x, cov C x (X x)⟫_ℝ :=
    hcov.mvfderiv_inner_eq X (hB.mdifferentiableAt (by simp)) (hC.mdifferentiableAt (by simp))
  rw [hfun, mvfderiv_mul hax hBC]
  simp only [add_apply, smul_apply, smul_eq_mul, hd, ha, LinearMap.smul_apply, innerₗ_apply_apply]
  ring

/-- For a metric-compatible connection whose Ricci tensor is `a g`, the covariant derivative of the
Ricci tensor at `x` is `(∇_v Ric)(u, w) = da(v) ⟪u, w⟫`. -/
private theorem IsMetricCompatible.derivRicciTensor_eq_mvfderiv_mul_inner
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {a : M → ℝ} (ha : ∀ y, cov.ricciTensor y = a y • innerₗ (TangentSpace I y)) {x : M}
    (hax : MDifferentiableAt I 𝓘(ℝ) a x) (u w v : TangentSpace I x) :
    cov.derivRicciTensor x u w v = mvfderiv I a x v * ⟪u, w⟫_ℝ := by
  obtain ⟨B, hB, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E u
  obtain ⟨C, hC, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E w
  have h := hcov.covariantDerivative_ricciTensor_eq ha hax (FiberBundle.extend E v) hB hC
  rw [FiberBundle.extend_apply_self] at h
  rw [derivRicciTensor_apply cov (hB.mdifferentiableAt (by simp))
    (hC.mdifferentiableAt (by simp)), h]

/-- The twice contracted second Bianchi identity for a metric-compatible torsion-free connection
with Ricci tensor `Ric = a g`: in dimension `n`, `(n - 2) da = 0` wherever `a` is differentiable. -/
private theorem IsMetricCompatible.finrank_sub_two_mul_mvfderiv_eq_zero
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (ht : cov.torsion = 0) {a : M → ℝ}
    (ha : ∀ y, cov.ricciTensor y = a y • innerₗ (TangentSpace I y)) {x : M}
    (hax : MDifferentiableAt I 𝓘(ℝ) a x) (v : TangentSpace I x) :
    ((Module.finrank ℝ E : ℝ) - 2) * mvfderiv I a x v = 0 := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  have hD := hcov.derivRicciTensor_eq_mvfderiv_mul_inner ha hax
  have hv : ∑ i, mvfderiv I a x (b i) * ⟪b i, v⟫_ℝ = mvfderiv I a x v := by
    conv_rhs => rw [← b.sum_repr' v]
    simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
  -- Contract `∑ᵢ (∇_{bᵢ} Rm)(bᵢ, u, w, v) = (∇_v Ric)(u, w) - (∇_w Ric)(u, v)` over `u = w = bⱼ`;
  -- the right side sums to `n da(v) - da(v)`.
  have h₁ : ∑ j, ∑ i, ⟪cov.derivCurvatureTensor cov x (b i) (b i) (b j) (b j), v⟫_ℝ =
      Module.finrank ℝ E * mvfderiv I a x v - mvfderiv I a x v := by
    simp only [hcov.sum_inner_derivCurvatureTensor_self_eq_sub ht, hD, b.inner_eq_one, mul_one,
      Finset.sum_sub_distrib, hv, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    -- `TangentSpace I x` is `E` by definition, so the two dimensions agree.
    rfl
  -- After pair interchange, the left side is the contraction `∑ᵢ (∇_{bᵢ} Ric)(v, bᵢ) = da(v)`.
  have h₂ : ∑ j, ∑ i, ⟪cov.derivCurvatureTensor cov x (b i) (b i) (b j) (b j), v⟫_ℝ =
      mvfderiv I a x v := by
    simp only [hcov.inner_derivCurvatureTensor_swap_pairs ht x (b _) (b _) (b _) (b _) v,
      real_inner_comm (b _)]
    rw [Finset.sum_comm]
    simpa only [cov.sum_inner_derivCurvatureTensor_eq_derivRicciTensor, hD, real_inner_comm v]
      using hv
  linarith

/-- **Einstein's constancy theorem**, local form. Let a metric-compatible torsion-free connection
have Ricci tensor `Ric = a g` for a function `a`, in dimension other than two. Then `da`
vanishes at every point. -/
theorem mfderiv_eq_zero_of_ricciTensor_eq_smul_inner
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (ht : cov.torsion = 0) (hdim : Module.finrank ℝ E ≠ 2) {a : M → ℝ}
    (ha : ∀ y, cov.ricciTensor y = a y • innerₗ (TangentSpace I y)) (x : M) :
    mfderiv I 𝓘(ℝ) a x = 0 := by
  by_cases hax : MDifferentiableAt I 𝓘(ℝ) a x
  swap
  · exact mfderiv_zero_of_not_mdifferentiableAt hax
  have h2 : ((Module.finrank ℝ E : ℝ) - 2) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hdim
  have hzero (v : TangentSpace I x) : mvfderiv I a x v = 0 :=
    (mul_eq_zero.1 (hcov.finrank_sub_two_mul_mvfderiv_eq_zero ht ha hax v)).resolve_left h2
  ext v
  simpa [mvfderiv] using hzero v

/-- **Einstein's constancy theorem.** Let a metric-compatible torsion-free connection on a
preconnected manifold, of positive dimension other than two, have Ricci tensor `Ric = a g` for a
function `a`. Then `a` is constant. -/
theorem eq_of_ricciTensor_eq_smul_inner [PreconnectedSpace M]
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (ht : cov.torsion = 0) (hpos : Module.finrank ℝ E ≠ 0) (hdim : Module.finrank ℝ E ≠ 2)
    {a : M → ℝ} (ha : ∀ y, cov.ricciTensor y = a y • innerₗ (TangentSpace I y)) (x y : M) :
    a x = a y := by
  -- `a` is the smooth scalar curvature divided by the dimension.
  have hn : (Module.finrank ℝ E : ℝ) ≠ 0 := by exact_mod_cast hpos
  have haeq : a = fun y ↦ cov.scalarCurvature y / Module.finrank ℝ E := by
    funext y
    rw [cov.scalarCurvature_eq_of_ricciTensor_eq_smul_inner y (a y) (ha y), eq_div_iff hn]
    exact mul_comm _ _
  have had : MDifferentiable I 𝓘(ℝ) a := by
    rw [haeq]
    exact (cov.contMDiff_scalarCurvature.div_const _).mdifferentiable (by simp)
  exact had.apply_eq_of_mfderiv_eq_zero (fun z ↦
    mfderiv_eq_zero_of_ricciTensor_eq_smul_inner hcov ht hdim ha z) x y

end CovariantDerivative
