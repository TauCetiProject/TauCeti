/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.SecondCovariantDerivative
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Dirac
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian
import TauCeti.Algebra.BigOperators.Finset.OffDiagonal
import TauCeti.Algebra.BigOperators.Finset.Pairs
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt

/-!
# The Weitzenböck formula for the Dirac operator

Let `V` be a vector bundle over a Riemannian manifold `M`, with a smooth connection `∇` and a
Clifford multiplication `c x : T_x M → End (V x)`, and let `∇ᵀ` be a connection on the tangent
bundle. The Dirac operator `D σ = ∑ᵢ c(eᵢ) ∇_{eᵢ} σ` is `CovariantDerivative.diracOperator`.
Assume that `∇ᵀ` is compatible with the metric on all of `M`, and, at a point `x`, that `c` is
differentiable and compatible with the two connections: for vector fields `v` and sections `s`
differentiable at `x`, the section `c(v) s` is differentiable at `x` and
`∇_w (c(v) s) = c(∇ᵀ_w v) s + c(v) ∇_w s`.

Then the covariant derivative of `D σ` at `x` is the Clifford contraction of the second
covariant derivative `∇²σ(u, v) = ∇_u ∇_v σ - ∇_{∇ᵀ_u v} σ`
(`CovariantDerivative.secondCovariantDerivative`) in its second slot:

`∇_w (D σ) = ∑ᵢ c(eᵢ) ∇²σ(w, eᵢ)`

(`CovariantDerivative.covariantDerivative_diracOperator_apply`), for every orthonormal basis
`eᵢ` of `T_x M`. If moreover the torsion of `∇ᵀ` vanishes at `x` (for instance, `∇ᵀ` is the
Levi-Civita connection) and `c` satisfies the Clifford relation `c(v)² = -⟪v, v⟫` at `x`, then
splitting
`∑ₖ ∑ᵢ c(eₖ) c(eᵢ) ∇²σ(eₖ, eᵢ)` into its symmetric and antisymmetric parts gives the
**Weitzenböck formula** (the general Bochner–Lichnerowicz–Weitzenböck square formula)

`D (D σ) = ∇*∇ σ + ∑_{i < j} c(eᵢ) c(eⱼ) R(eᵢ, eⱼ) σ`

(`CovariantDerivative.diracOperator_diracOperator_eq_sum_lt`), where `∇*∇` is the rough Laplacian
`CovariantDerivative.roughLaplacian` and `R` is the curvature of `∇`. The symmetric part is the
negative trace of `∇²σ` because `c(eₖ) c(eᵢ) + c(eᵢ) c(eₖ) = -2 δₖᵢ`, and the antisymmetric part
is the curvature by the Ricci identity (`CovariantDerivative.secondCovariantDerivative_sub_swap`).
Summed over all
ordered pairs, the curvature term carries a factor `1 / 2`
(`CovariantDerivative.diracOperator_diracOperator_eq`).

This is the formula for the Dirac operator induced by the connection: adding a term of order
zero to `D` changes its square by terms of order one and zero which do not have this form. Its
curvature term is the one computed by the Lichnerowicz formula `D² = ∇*∇ + Scal / 4` of a spin
manifold, where the curvature of the spin connection contracts to `Scal / 4`
(`TauCeti.FourTensor.sum_sum_inv_two_smul_ι_mul_ι_mul_inv_four_smul_sum_sum_smul_ι_mul_ι`), and by
the Weitzenböck formula `D_A² = ∇_A*∇_A + Scal / 4 + c(F_A⁺) / 2` of Seiberg–Witten theory, where
the curvature of the twisting line contributes the last term. Those computations of the curvature
of an actual spinor bundle are not made here.

## Proof

Choose smooth vector fields `Yᵢ` that form an orthonormal basis of each tangent space near `x`
(`TauCeti.exists_contMDiff_orthonormal_frame_nhds`). Near `x`,
`D σ = ∑ᵢ c(Yᵢ) ∇_{Yᵢ} σ`, so the compatibility of `c` gives
`∇_w (D σ) = ∑ᵢ c(Yᵢ) ∇²σ(w, Yᵢ) + ∑ᵢ (c(∇ᵀ_w Yᵢ) ∇_{Yᵢ} σ + c(Yᵢ) ∇_{∇ᵀ_w Yᵢ} σ)`. Writing
`∇ᵀ_w Yᵢ = ∑ⱼ aᵢⱼ Yⱼ`, the last sum is `∑ᵢⱼ aᵢⱼ (c(Yⱼ) ∇_{Yᵢ} σ + c(Yᵢ) ∇_{Yⱼ} σ)`: the
coefficients are skew-symmetric because `∇ᵀ` is metric and the frame is orthonormal, while the
bracket is symmetric, so the sum vanishes.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Chapter II, Theorem 8.2.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., World Scientific,
  Theorem 12.1.67.
-/

public section

open Bundle Filter Set
open scoped ContDiff Manifold RealInnerProductSpace Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V]
  (cov : _root_.CovariantDerivative I F V)
  (c : Π x : M, TangentSpace I x →L[ℝ] V x →L[ℝ] V x)
  {σ : Π y : M, V y} {x : M}

section Frame

variable [VectorBundle ℝ F V] [IsManifold I ∞ M] [ContMDiffCovariantDerivative cov ∞]
  (hσ : CMDiff ∞ (T% σ))
  (hcd : ∀ {v : Π y : M, TangentSpace I y} {s : Π y : M, V y}, MDiffAt (T% v) x →
    MDiffAt (T% s) x → MDiffAt (T% (fun y ↦ c y (v y) (s y))) x)
include hσ hcd

/-- The terms `c(Yᵢ) ∇_{Yᵢ} σ` of the Dirac operator in a smooth frame are differentiable. -/
private theorem mdifferentiableAt_sum_frame {ι : Type*} [Fintype ι]
    {Y : ι → Π y : M, TangentSpace I y} (hYs : ∀ i, CMDiff ∞ (T% (Y i))) :
    MDiffAt (T% (∑ i, fun y : M ↦ c y (Y i y) (cov σ y (Y i y)))) x := by
  have hσ' : CMDiff (∞ + 1) (T% σ) := by simpa using hσ
  have h (i : ι) : MDiffAt (T% (fun y : M ↦ c y (Y i y) (cov σ y (Y i y)))) x :=
    hcd ((hYs i).mdifferentiable (by simp) x)
      ((cov.contMDiff_apply (hYs i) hσ').mdifferentiable (by simp) x)
  simpa [Finset.sum_apply] using
    MDifferentiableAt.sum_section (t := fun i (y : M) ↦ c y (Y i y) (cov σ y (Y i y)))
      (s := Finset.univ) fun i _ ↦ h i

end Frame

variable [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- In vector fields `Yᵢ` forming an orthonormal basis near `x`, the Dirac operator is
`∑ᵢ c(Yᵢ) ∇_{Yᵢ} σ` near `x`. -/
private theorem eventually_diracOperator_eq {ι : Type*} [Fintype ι]
    {Y : ι → Π y : M, TangentSpace I y}
    (hY : ∀ᶠ y in 𝓝 x, Orthonormal ℝ (Y · y) ∧ ⊤ ≤ Submodule.span ℝ (Set.range (Y · y))) :
    ∀ᶠ y in 𝓝 x, cov.diracOperator c σ y =
      (∑ i, fun y : M ↦ c y (Y i y) (cov σ y (Y i y))) y := by
  filter_upwards [hY] with y hy
  rw [cov.diracOperator_eq_sum c σ y (OrthonormalBasis.mk hy.1 hy.2), OrthonormalBasis.coe_mk,
    Finset.sum_apply]

variable [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (covT : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))
  (hcovT : IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) covT)

include hcovT in
/-- The terms of `∇_w (∑ᵢ c(Yᵢ) ∇_{Yᵢ} σ)` which differentiate the frame cancel: writing
`∇ᵀ_w Yᵢ = ∑ⱼ aᵢⱼ Yⱼ`, they are `∑ᵢⱼ aᵢⱼ (c(Yⱼ) ∇_{Yᵢ} σ + c(Yᵢ) ∇_{Yⱼ} σ)`, with `aᵢⱼ`
skew-symmetric and the bracket symmetric. -/
private theorem sum_frame_eq_zero {ι : Type*} [Fintype ι] {Y : ι → Π y : M, TangentSpace I y}
    (hYs : ∀ i, CMDiff ∞ (T% (Y i)))
    (hY : ∀ᶠ y in 𝓝 x, Orthonormal ℝ (Y · y) ∧ ⊤ ≤ Submodule.span ℝ (Set.range (Y · y)))
    (w : TangentSpace I x) :
    ∑ i, (c x (covT (Y i) x w) (cov σ x (Y i x)) + c x (Y i x) (cov σ x (covT (Y i) x w))) =
      0 := by
  classical
  set b := OrthonormalBasis.mk hY.self_of_nhds.1 hY.self_of_nhds.2
  have hb (i : ι) : b i = Y i x := by simp [b]
  -- The connection coefficients `aᵢⱼ = ⟪Yⱼ, ∇ᵀ_w Yᵢ⟫` of the orthonormal frame.
  set a : ι → ι → ℝ := fun i j ↦ ⟪b j, covT (Y i) x w⟫ with ha_def
  have ha (i j : ι) : a i j = -a j i := by
    have hconst : (fun y ↦ ⟪Y i y, Y j y⟫) =ᶠ[𝓝 x] fun _ ↦ if i = j then (1 : ℝ) else 0 := by
      filter_upwards [hY] with y hy
      exact orthonormal_iff_ite.1 hy.1 i j
    have h := hcovT.inner_apply_add_inner_apply_eq_zero_of_eventuallyEq_const
      ((hYs i).mdifferentiable (by simp) x) ((hYs j).mdifferentiable (by simp) x) hconst w
    have hc := real_inner_comm (Y j x) (covT (Y i) x w)
    simp only [ha_def, hb]
    linarith
  have hexp (i : ι) : covT (Y i) x w = ∑ j, a i j • b j := (b.sum_repr' _).symm
  -- Expanding `∇ᵀ_w Yᵢ` in the frame gives a skew-symmetric sum of symmetric terms.
  have hsum : ∑ i, (c x (covT (Y i) x w) (cov σ x (Y i x)) +
      c x (Y i x) (cov σ x (covT (Y i) x w))) =
      ∑ i, ∑ j, a i j • (c x (b j) (cov σ x (b i)) + c x (b i) (cov σ x (b j))) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hexp i, ← hb i]
    simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, smul_add, Finset.sum_add_distrib]
  rw [hsum]
  -- A skew-symmetric sum of symmetric terms vanishes.
  refine Finset.sum_sum_eq_zero_of_diag Finset.univ (fun i _ ↦ ?_) fun i _ j _ _ ↦ ?_
  · rw [show a i i = 0 by linarith [ha i i], zero_smul]
  · rw [ha j i]
    module

variable [T2Space M]

variable [VectorBundle ℝ F V] [ContMDiffCovariantDerivative cov ∞]
  (hσ : CMDiff ∞ (T% σ))
  (hcd : ∀ {v : Π y : M, TangentSpace I y} {s : Π y : M, V y}, MDiffAt (T% v) x →
    MDiffAt (T% s) x → MDiffAt (T% (fun y ↦ c y (v y) (s y))) x)
include hσ hcd

/-- **The Dirac operator of a smooth section is differentiable** wherever the Clifford
multiplication is: if `c(v) s` is differentiable at `x` for all vector fields `v` and sections `s`
differentiable at `x`, then so is `D σ` for every smooth section `σ`. -/
theorem mdifferentiableAt_diracOperator : MDiffAt (T% (cov.diracOperator c σ)) x := by
  obtain ⟨Y, hYs, hY⟩ := TauCeti.exists_contMDiff_orthonormal_frame_nhds (I := I) (F := E)
    (V := fun y : M ↦ TangentSpace I y) (n := ∞) x
  refine (mdifferentiableAt_sum_frame cov c hσ hcd hYs).congr_of_eventuallyEq ?_
  filter_upwards [eventually_diracOperator_eq cov c hY] with y hy
  rw [hy]

variable (hcomp : ∀ {v : Π y : M, TangentSpace I y} {s : Π y : M, V y}, MDiffAt (T% v) x →
    MDiffAt (T% s) x → ∀ w, cov (fun y ↦ c y (v y) (s y)) x w =
      c x (covT v x w) (s x) + c x (v x) (cov s x w))
include hcovT hcomp

/-- In vector fields `Yᵢ` forming an orthonormal basis near `x`,
`∇_w (∑ᵢ c(Yᵢ) ∇_{Yᵢ} σ) = ∑ᵢ c(Yᵢ) ∇²σ(w, Yᵢ)` at `x`. -/
private theorem covariantDerivative_sum_frame {ι : Type*} [Fintype ι]
    {Y : ι → Π y : M, TangentSpace I y} (hYs : ∀ i, CMDiff ∞ (T% (Y i)))
    (hY : ∀ᶠ y in 𝓝 x, Orthonormal ℝ (Y · y) ∧ ⊤ ≤ Submodule.span ℝ (Set.range (Y · y)))
    (w : TangentSpace I x) :
    cov (∑ i, fun y : M ↦ c y (Y i y) (cov σ y (Y i y))) x w =
      ∑ i, c x (Y i x) (cov.secondCovariantDerivative covT σ x w (Y i x)) := by
  have hσ' : CMDiff (∞ + 1) (T% σ) := by simpa using hσ
  have hYd (i : ι) : MDiffAt (T% (Y i)) x := (hYs i).mdifferentiable (by simp) x
  have hsd (i : ι) : MDiffAt (T% (fun y : M ↦ cov σ y (Y i y))) x :=
    (cov.contMDiff_apply (hYs i) hσ').mdifferentiable (by simp) x
  -- `∇_w (∇_{Yᵢ} σ) = ∇²σ(w, Yᵢ) + ∇_{∇ᵀ_w Yᵢ} σ`.
  have h2 (i : ι) : cov (fun y : M ↦ cov σ y (Y i y)) x w =
      cov.secondCovariantDerivative covT σ x w (Y i x) + cov σ x (covT (Y i) x w) := by
    rw [cov.secondCovariantDerivative_apply covT hσ x (hYs i) w, sub_add_cancel]
  rw [TauCeti.Manifold.covariantDerivative_sum cov.isCovariantDerivativeOnUniv (mem_univ x)
    fun i _ ↦ hcd (hYd i) (hsd i), _root_.sum_apply]
  simp only [hcomp (hYd _) (hsd _), h2, map_add]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  convert sum_frame_eq_zero cov c covT hcovT hYs hY w using 2 with i
  abel

/-- **The covariant derivative of the Dirac operator** is the Clifford contraction of the second
covariant derivative in its second slot: for every smooth section `σ` and every orthonormal basis
`eᵢ` of `T_x M`, `∇_w (D σ) = ∑ᵢ c(eᵢ) ∇²σ(w, eᵢ)`. This holds when `∇ᵀ` is metric on all of `M`
and `c` is differentiable and compatible with `∇` and `∇ᵀ`,
`∇_w (c(v) s) = c(∇ᵀ_w v) s + c(v) ∇_w s`, at `x`. -/
theorem covariantDerivative_diracOperator_apply {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (w : TangentSpace I x) :
    cov (cov.diracOperator c σ) x w =
      ∑ i, c x (b i) (cov.secondCovariantDerivative covT σ x w (b i)) := by
  obtain ⟨Y, hYs, hY⟩ := TauCeti.exists_contMDiff_orthonormal_frame_nhds (I := I) (F := E)
    (V := fun y : M ↦ TangentSpace I y) (n := ∞) x
  rw [cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (mdifferentiableAt_diracOperator cov c hσ hcd)
      (mdifferentiableAt_sum_frame cov c hσ hcd hYs) univ_mem
      (eventually_diracOperator_eq cov c hY),
    covariantDerivative_sum_frame cov c covT hcovT hσ hcd hcomp hYs hY w]
  -- Both sums are the contraction of `(p, q) ↦ c(p) ∇²σ(w, q)` with the metric.
  let B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] V x :=
    LinearMap.mk₂ ℝ (fun p q ↦ c x p (cov.secondCovariantDerivative covT σ x w q))
      (fun p p' q ↦ by simp only [map_add, add_apply])
      (fun r p q ↦ by simp only [map_smul, smul_apply])
      (fun p q q' ↦ by simp only [map_add])
      (fun r p q ↦ by simp only [map_smul])
  have hY₀ := hY.self_of_nhds
  simpa [B, map_sum] using congrArg (TensorProduct.lift B)
    ((InnerProductSpace.canonicalCovariantTensor_eq_sum _
      (OrthonormalBasis.mk hY₀.1 hY₀.2)).symm.trans
        (InnerProductSpace.canonicalCovariantTensor_eq_sum _ b))

variable [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] (htor : covT.torsion x = 0)
  (hcl : ∀ (v : TangentSpace I x) (s : V x), c x v (c x v s) = -⟪v, v⟫ • s)
include htor hcl

/-- **The Weitzenböck formula for the Dirac operator**, summed over all ordered pairs. Let `∇ᵀ` be
metric on all of `M` with torsion vanishing at `x` (for instance, the Levi-Civita connection), and
let the Clifford multiplication `c` satisfy `c(v)² = -⟪v, v⟫` at `x` and be differentiable and
compatible with `∇` and `∇ᵀ` there. Then for every smooth section `σ` and every orthonormal basis
`eᵢ` of `T_x M`, `D (D σ) = ∇*∇ σ + (1 / 2) ∑ᵢ ∑ⱼ c(eᵢ) c(eⱼ) R(eᵢ, eⱼ) σ` at `x`, where `R` is
the curvature of `∇`. -/
theorem diracOperator_diracOperator_eq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.diracOperator c (cov.diracOperator c σ) x =
      cov.roughLaplacian covT σ x +
        (2 : ℝ)⁻¹ • ∑ i, ∑ j, c x (b i) (c x (b j) (cov.curvatureTensor x (b i) (b j) (σ x))) := by
  classical
  rw [cov.diracOperator_eq_sum c _ x b, cov.roughLaplacian_eq_sum covT σ x b]
  simp only [covariantDerivative_diracOperator_apply cov c covT hcovT hσ hcd hcomp b, map_sum]
  -- The antisymmetric part of `∇²σ` is the curvature, by the Ricci identity.
  have hric (u v : TangentSpace I x) : cov.secondCovariantDerivative covT σ x u v -
      cov.secondCovariantDerivative covT σ x v u = cov.curvatureTensor x u v (σ x) := by
    rw [cov.secondCovariantDerivative_sub_swap covT hσ x, htor]
    simp
  simp only [← hric, map_sub, Finset.sum_sub_distrib]
  -- The symmetric part contracts to the trace, by the Clifford relation.
  have hsym : ∑ k, ∑ i, c x (b k) (c x (b i) (cov.secondCovariantDerivative covT σ x (b k) (b i))) +
      ∑ k, ∑ i, c x (b k) (c x (b i) (cov.secondCovariantDerivative covT σ x (b i) (b k))) =
      -(2 : ℝ) • ∑ k, cov.secondCovariantDerivative covT σ x (b k) (b k) := by
    conv_lhs => arg 2; rw [Finset.sum_comm]
    simp only [← Finset.sum_add_distrib, (c x).apply_apply_add_swap_eq_neg_two_inner hcl,
      b.inner_eq_ite, mul_ite,
      mul_one, mul_zero, ite_smul, zero_smul, neg_smul, Finset.sum_neg_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, Finset.smul_sum]
  linear_combination (norm := module) (2 : ℝ)⁻¹ • hsym

/-- **The Weitzenböck formula for the Dirac operator.** Let `∇ᵀ` be metric on all of `M` with
torsion vanishing at `x` (for instance, the Levi-Civita connection), and let the Clifford
multiplication `c` satisfy `c(v)² = -⟪v, v⟫` at `x` and be differentiable and compatible with `∇`
and `∇ᵀ` there. Then for every smooth section `σ` and every orthonormal basis `eᵢ` of `T_x M`,
indexed by a linear order, `D (D σ) = ∇*∇ σ + ∑_{i < j} c(eᵢ) c(eⱼ) R(eᵢ, eⱼ) σ` at `x`, where
`R` is the curvature of `∇`. -/
theorem diracOperator_diracOperator_eq_sum_lt {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.diracOperator c (cov.diracOperator c σ) x =
      cov.roughLaplacian covT σ x +
        ∑ i, ∑ j with i < j, c x (b i) (c x (b j) (cov.curvatureTensor x (b i) (b j) (σ x))) := by
  rw [diracOperator_diracOperator_eq cov c covT hcovT hσ hcd hcomp htor hcl b]
  congr 1
  set f : ι → ι → V x := fun i j ↦ c x (b i) (c x (b j) (cov.curvatureTensor x (b i) (b j) (σ x)))
    with hf
  -- `f` vanishes on the diagonal and is symmetric off it.
  have hsymm (i j : ι) (hij : i ≠ j) : f j i = f i j := by
    have h := (c x).apply_apply_add_swap_eq_neg_two_inner hcl (b i) (b j)
      (cov.curvatureTensor x (b i) (b j) (σ x))
    simp only [b.inner_eq_ite, hij, ite_false, mul_zero, neg_zero, zero_smul] at h
    simp only [hf, cov.curvatureTensor_antisymm x (b j) (b i), LinearMap.neg_apply, map_neg]
    linear_combination (norm := module) -h
  -- Fold the sum over all ordered pairs onto the increasing ones.
  rw [← Fintype.sum_prod_type' f,
    TauCeti.sum_univ_prod_eq_sum_lt_add_swap _ fun i ↦ by simp [hf], Finset.sum_filter,
    Fintype.sum_prod_type]
  simp only [Finset.sum_filter, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs with h
  · rw [Prod.fst_swap, Prod.snd_swap, hsymm i j h.ne, ← two_smul ℝ, smul_smul,
      inv_mul_cancel₀ two_ne_zero, one_smul]
  · exact smul_zero _

end CovariantDerivative
