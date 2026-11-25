/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.SecondCovariantDerivative
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Dirac.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian
import TauCeti.Algebra.BigOperators.Finset.OffDiagonal
import TauCeti.Algebra.BigOperators.Finset.Pairs
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

/-!
# The Weitzenböck formula for the square of a Dirac operator

Let `V` be a vector bundle over a Riemannian manifold `M`, with a smooth connection `∇` and a
Clifford multiplication `c x : T_x M → End (V x)`, and let `∇ᵀ` be a connection on the tangent
bundle. The Dirac operator `D σ = ∑ᵢ c(eᵢ) ∇_{eᵢ} σ` is `CovariantDerivative.diracOperator`.
Assume that `∇ᵀ` is compatible with the metric on all of `M`, and, at a point `x`, that `c` is
differentiable and compatible with the two connections: for smooth vector fields `v` and smooth
sections `s`, the section `c(v) s` is differentiable at `x` and
`∇_w (c(v) s) = c(∇ᵀ_w v) s + c(v) ∇_w s`.

Then the covariant derivative of `D σ` at `x` is the Clifford contraction of the second
covariant derivative `∇²σ(u, v) = ∇_u ∇_v σ - ∇_{∇ᵀ_u v} σ`
(`CovariantDerivative.secondCovariantDerivative`) in its second slot:

`∇_w (D σ) = ∑ᵢ c(eᵢ) ∇²σ(w, eᵢ)`

(`CovariantDerivative.covariantDerivative_diracOperator_apply`), for every orthonormal basis
`eᵢ` of `T_x M`. If moreover the torsion of `∇ᵀ` vanishes at `x` (for instance, `∇ᵀ` is the
Levi-Civita connection) and `c` satisfies the Clifford relation `c(v)² = -⟪v, v⟫` at `x`, then
splitting `∑ₖ ∑ᵢ c(eₖ) c(eᵢ) ∇²σ(eₖ, eᵢ)` into its symmetric and antisymmetric parts gives the
**Weitzenböck formula** (the general Bochner–Lichnerowicz–Weitzenböck square formula)

`D (D σ) = ∇*∇ σ + (1 / 2) ∑ᵢ ∑ⱼ c(eᵢ) c(eⱼ) R(eᵢ, eⱼ) σ`

(`CovariantDerivative.diracOperator_diracOperator_eq_roughLaplacian_add`), where `∇*∇` is the
rough Laplacian `CovariantDerivative.roughLaplacian` and `R` is the curvature of `∇`. The
symmetric part is the negative trace of `∇²σ` because `c(eₖ) c(eᵢ) + c(eᵢ) c(eₖ) = -2 δₖᵢ`, and
the antisymmetric part is the curvature by the Ricci identity
(`CovariantDerivative.secondCovariantDerivative_sub_swap`). Since
`c(eⱼ) c(eᵢ) R(eⱼ, eᵢ) = c(eᵢ) c(eⱼ) R(eᵢ, eⱼ)` for `i ≠ j` and the diagonal terms vanish, the
curvature term is the sum `∑_{i < j} c(eᵢ) c(eⱼ) R(eᵢ, eⱼ) σ` over unordered pairs
(`CovariantDerivative.diracOperator_diracOperator_eq_roughLaplacian_add_sum_lt`).

This is the formula for the Dirac operator induced by the connection: adding a term of order
zero to `D` changes its square by terms of order one and zero which do not have this form. Its
curvature term is the one computed by the Lichnerowicz formula `D² = ∇*∇ + Scal / 4` of a spin
manifold, where the curvature of the spin connection contracts to `Scal / 4`
(`TauCeti.FourTensor.sum_sum_inv_two_smul_ι_mul_ι_mul_inv_four_smul_sum_sum_smul_ι_mul_ι`), and by
the Weitzenböck formula `D_A² = ∇_A*∇_A + Scal / 4 + c(F_A⁺) / 2` of Seiberg–Witten theory, where
the curvature of the twisting line contributes the last term. Those computations of the curvature
of an actual spinor bundle are not made here.

The same formula holds in an orthonormal frame `eᵢ` near `x` whose covariant derivatives vanish
at `x`, such as a geodesic frame: there the Clifford multiplications `c(eᵢ)` pass through `∇` at
`x`, and `D² σ = ∑ᵢ ∑ⱼ c(eᵢ) c(eⱼ) ∇²σ(eᵢ, eⱼ)` at `x`
(`CovariantDerivative.diracOperator_diracOperator_eq_sum_sum_secondCovariantDerivative`,
`CovariantDerivative.diracOperator_diracOperator_eq_roughLaplacian_add_of_frame`).

## Main results

* `CovariantDerivative.mdifferentiableAt_diracOperator`: `D σ` is differentiable where `c` is.
* `CovariantDerivative.covariantDerivative_diracOperator_apply`:
  `∇_w (D σ) = ∑ᵢ c(eᵢ) ∇²σ(w, eᵢ)`.
* `CovariantDerivative.diracOperator_diracOperator_eq_roughLaplacian_add`: the Weitzenböck
  formula, in every orthonormal basis.
* `CovariantDerivative.diracOperator_diracOperator_eq_roughLaplacian_add_sum_lt`: the same, with
  the curvature term summed over pairs `i < j`.
* `CovariantDerivative.diracOperator_diracOperator_eq_sum_sum_secondCovariantDerivative`:
  `D² σ = ∑ᵢ ∑ⱼ c(eᵢ) c(eⱼ) ∇²σ(eᵢ, eⱼ)` in an orthonormal frame parallel at the point.
* `CovariantDerivative.diracOperator_diracOperator_eq_roughLaplacian_add_of_frame`: the
  Weitzenböck formula in such a frame, for any connection on the tangent bundle whose torsion
  vanishes at the point.

## Proof

Choose smooth vector fields `Yᵢ` that form an orthonormal basis of each tangent space near `x`
(`TauCeti.exists_nhds_orthonormal_sections`). Near `x`,
`D σ = ∑ᵢ c(Yᵢ) ∇_{Yᵢ} σ`, so the compatibility of `c` gives
`∇_w (D σ) = ∑ᵢ c(Yᵢ) ∇²σ(w, Yᵢ) + ∑ᵢ (c(∇ᵀ_w Yᵢ) ∇_{Yᵢ} σ + c(Yᵢ) ∇_{∇ᵀ_w Yᵢ} σ)`. Writing
`∇ᵀ_w Yᵢ = ∑ⱼ aᵢⱼ Yⱼ`, the last sum is `∑ᵢⱼ aᵢⱼ (c(Yⱼ) ∇_{Yᵢ} σ + c(Yᵢ) ∇_{Yⱼ} σ)`: the
coefficients are skew-symmetric because `∇ᵀ` is metric and the frame is orthonormal, while the
bracket is symmetric, so the sum vanishes.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Chapter II, Theorem 8.2.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 2nd ed., World Scientific, 2007,
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
  {σ : Π y : M, V y}

section ParallelFrame

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [FiniteDimensional ℝ F]
  [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I] [ContMDiffCovariantDerivative cov ∞]
  (covT : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] in
/-- **The square of the Dirac operator in a frame parallel at a point.** Let `e₁, …, eₖ` be
smooth vector fields forming an orthonormal frame near `x`, with vanishing covariant derivatives
`∇ᵀ eᵢ = 0` at `x`. Suppose that each `c(eᵢ)` is parallel at `x` on the section `∇_{eᵢ} σ`,
and that the sections `c(eᵢ) ∇_{eᵢ} σ` are differentiable at `x`. Then for a smooth section `σ`,

`D (D σ) = ∑ᵢ ∑ⱼ c(eᵢ) c(eⱼ) ∇²σ(eᵢ, eⱼ)`

at `x`, where `∇²σ` is the second covariant derivative for `∇` and `∇ᵀ`. -/
theorem diracOperator_diracOperator_eq_sum_sum_secondCovariantDerivative
    (hσ : CMDiff ∞ (T% σ)) {ι : Type*} [Fintype ι] (e : ι → Π y : M, TangentSpace I y)
    (he : ∀ i, CMDiff ∞ (T% (e i))) {x : M}
    (hframe : ∀ᶠ y in 𝓝 x, ∃ b : OrthonormalBasis ι ℝ (TangentSpace I y), ∀ i, b i = e i y)
    (hpar : ∀ i, covT (e i) x = 0)
    (hc : ∀ i u, cov (fun y ↦ c y (e i y) (cov σ y (e i y))) x u =
      c x (e i x) (cov (fun y ↦ cov σ y (e i y)) x u))
    (hdiff : ∀ i, MDiffAt (T% (fun y ↦ c y (e i y) (cov σ y (e i y)))) x) :
    cov.diracOperator c (cov.diracOperator c σ) x =
      ∑ i, ∑ j, c x (e i x) (c x (e j x)
        (cov.secondCovariantDerivative covT σ x (e i x) (e j x))) := by
  -- Near `x` the Dirac operator of `σ` is the frame sum `∑ⱼ c(eⱼ) ∇_{eⱼ} σ`.
  set S : ι → Π y : M, V y := fun j y ↦ c y (e j y) (cov σ y (e j y)) with hS
  have hsum : ∀ᶠ y in 𝓝 x, cov.diracOperator c σ y = (∑ j, S j) y := by
    filter_upwards [hframe] with y ⟨b, hb⟩
    rw [diracOperator_eq_sum cov c σ y b, Finset.sum_apply]
    simp only [hb, hS]
  have hsumdiff : MDiffAt (T% (∑ j, S j)) x := by
    simpa [Finset.sum_apply] using
      MDifferentiableAt.sum_section (s := Finset.univ) fun j _ ↦ hdiff j
  have hDdiff : MDiffAt (T% (cov.diracOperator c σ)) x :=
    hsumdiff.congr_of_eventuallyEq (hsum.mono fun y hy ↦ by simp only [hy])
  -- At `x`, `∇_u (c(eⱼ) ∇_{eⱼ} σ) = c(eⱼ) ∇²σ(u, eⱼ)`, since `∇ᵀ eⱼ = 0` there.
  have hsecond (j : ι) (u : TangentSpace I x) :
      cov.secondCovariantDerivative covT σ x u (e j x) =
        cov (fun y ↦ cov σ y (e j y)) x u := by
    simp [secondCovariantDerivative_apply cov covT hσ x (he j) u, hpar j]
  obtain ⟨b, hb⟩ := hframe.self_of_nhds
  rw [diracOperator_eq_sum cov c _ x b,
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hDdiff hsumdiff univ_mem hsum,
    cov.isCovariantDerivativeOnUniv.sum fun j _ ↦ hdiff j]
  simp only [hb, FunLike.coe_sum, Finset.sum_apply, map_sum, hc, hsecond]

/-- The Clifford contraction of the second covariant derivative in an orthonormal basis `eᵢ` of
`T_x M`: if the torsion of `∇ᵀ` vanishes at `x` and `c(v)² = -⟪v, v⟫` at `x`, then
`∑ᵢ ∑ⱼ c(eᵢ) c(eⱼ) ∇²σ(eᵢ, eⱼ) = ∇*∇ σ + (1 / 2) ∑ᵢ ∑ⱼ c(eᵢ) c(eⱼ) R(eᵢ, eⱼ) σ`. The symmetric
part is the negative trace by the Clifford relation, the antisymmetric part the curvature by the
Ricci identity. -/
private theorem sum_sum_secondCovariantDerivative_eq (hσ : CMDiff ∞ (T% σ)) {x : M}
    (htor : covT.torsion x = 0)
    (hcl : ∀ (v : TangentSpace I x) (s : V x), c x v (c x v s) = -⟪v, v⟫ • s)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    ∑ i, ∑ j, c x (b i) (c x (b j) (cov.secondCovariantDerivative covT σ x (b i) (b j))) =
      cov.roughLaplacian covT σ x +
        (2 : ℝ)⁻¹ • ∑ i, ∑ j, c x (b i) (c x (b j) (cov.curvatureTensor x (b i) (b j) (σ x))) := by
  classical
  rw [cov.roughLaplacian_eq_sum covT σ x b]
  -- The antisymmetric part of `∇²σ` is the curvature, by the Ricci identity.
  have hric (u v : TangentSpace I x) : cov.secondCovariantDerivative covT σ x u v -
      cov.secondCovariantDerivative covT σ x v u = cov.curvatureTensor x u v (σ x) := by
    rw [cov.secondCovariantDerivative_sub_swap covT hσ x, htor]
    simp
  -- The Clifford multiplications by the basis vectors satisfy the Clifford relations.
  have hγ (i j : ι) (s : V x) : c x (b i) (c x (b j) s) + c x (b j) (c x (b i) s) =
      if i = j then -(2 • s) else 0 := by
    rw [(c x).apply_apply_add_swap_eq_neg_two_inner hcl, b.inner_eq_ite]
    split_ifs <;> simp [two_smul]
  -- The symmetric part contracts to the trace, the antisymmetric part to the curvature.
  have h := TauCeti.two_nsmul_sum_sum_apply_apply_eq (fun i ↦ c x (b i)) hγ
    (fun i j ↦ cov.secondCovariantDerivative covT σ x (b i) (b j))
  simp only [hric, ← Nat.cast_smul_eq_nsmul ℝ 2, Nat.cast_ofNat] at h
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  rw [← inv_smul_smul₀ h2 (∑ i, ∑ j, _), h, smul_add, smul_neg, inv_smul_smul₀ h2]

/-- **The Weitzenböck formula in a frame parallel at a point.** Let `∇ᵀ` be a connection on the
tangent bundle whose torsion vanishes at `x`, and `e₁, …, eₖ` smooth vector fields forming an
orthonormal frame near `x`, with `∇ᵀ eᵢ = 0` at `x`. Suppose that Clifford multiplication
satisfies the Clifford relation `c(v)² = -⟪v, v⟫` at `x`, that each `c(eᵢ)` is parallel at `x` on
the section `∇_{eᵢ} σ`, and that the sections `c(eᵢ) ∇_{eᵢ} σ` are differentiable at `x`. Then for
a smooth section `σ`,

`D (D σ) = ∇*∇ σ + (1 / 2) ∑ᵢ ∑ⱼ c(eᵢ) c(eⱼ) R(eᵢ, eⱼ) σ`

at `x`, where `∇*∇` is the rough Laplacian and `R` the curvature of `∇`. -/
theorem diracOperator_diracOperator_eq_roughLaplacian_add_of_frame
    (hσ : CMDiff ∞ (T% σ)) {ι : Type*} [Fintype ι] (e : ι → Π y : M, TangentSpace I y)
    (he : ∀ i, CMDiff ∞ (T% (e i))) {x : M} (htor : covT.torsion x = 0)
    (hframe : ∀ᶠ y in 𝓝 x, ∃ b : OrthonormalBasis ι ℝ (TangentSpace I y), ∀ i, b i = e i y)
    (hpar : ∀ i, covT (e i) x = 0)
    (hcl : ∀ (v : TangentSpace I x) (s : V x), c x v (c x v s) = -⟪v, v⟫ • s)
    (hc : ∀ i u, cov (fun y ↦ c y (e i y) (cov σ y (e i y))) x u =
      c x (e i x) (cov (fun y ↦ cov σ y (e i y)) x u))
    (hdiff : ∀ i, MDiffAt (T% (fun y ↦ c y (e i y) (cov σ y (e i y)))) x) :
    cov.diracOperator c (cov.diracOperator c σ) x =
      cov.roughLaplacian covT σ x +
        (2 : ℝ)⁻¹ • ∑ i, ∑ j, c x (e i x) (c x (e j x)
          (cov.curvatureTensor x (e i x) (e j x) (σ x))) := by
  obtain ⟨b, hb⟩ := hframe.self_of_nhds
  rw [diracOperator_diracOperator_eq_sum_sum_secondCovariantDerivative cov c covT hσ e he hframe
    hpar hc hdiff]
  simp only [← hb]
  exact sum_sum_secondCovariantDerivative_eq cov c covT hσ htor hcl b

end ParallelFrame

variable {x : M}

section Frame

variable [VectorBundle ℝ F V] [IsManifold I ∞ M] [ContMDiffCovariantDerivative cov ∞]
  (hσ : CMDiff ∞ (T% σ))
  (hcd : ∀ {v : Π y : M, TangentSpace I y} {s : Π y : M, V y}, CMDiff ∞ (T% v) →
    CMDiff ∞ (T% s) → MDiffAt (T% (fun y ↦ c y (v y) (s y))) x)
include hσ hcd

/-- The terms `c(Yᵢ) ∇_{Yᵢ} σ` of the Dirac operator in a smooth frame are differentiable. -/
private theorem mdifferentiableAt_sum_frame {ι : Type*} [Fintype ι]
    {Y : ι → Π y : M, TangentSpace I y} (hYs : ∀ i, CMDiff ∞ (T% (Y i))) :
    MDiffAt (T% (∑ i, fun y : M ↦ c y (Y i y) (cov σ y (Y i y)))) x := by
  have hσ' : CMDiff (∞ + 1) (T% σ) := by simpa using hσ
  have h (i : ι) : MDiffAt (T% (fun y : M ↦ c y (Y i y) (cov σ y (Y i y)))) x :=
    hcd (hYs i) (cov.contMDiff_apply (hYs i) hσ')
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
  -- They are skew-symmetric, since `Y` is an orthonormal local frame on an open set around `x`.
  obtain ⟨t, ht, hto, hxt⟩ := eventually_nhds_iff.1 hY
  have hs : IsLocalFrameOn I E ∞ Y t :=
    { linearIndependent := fun hy ↦ (ht _ hy).1.linearIndependent
      generating := fun hy ↦ (ht _ hy).2
      contMDiffOn := fun i ↦ (hYs i).contMDiffOn }
  have ha (i j : ι) : a i j = -a j i := by
    simp only [ha_def, hb, ← hs.coeff_eq_inner hxt (ht x hxt).1]
    exact hs.coeff_covariantDerivative_swap (by simp) hto (fun y hy ↦ (ht y hy).1) hcovT x j i w
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
  (hcd : ∀ {v : Π y : M, TangentSpace I y} {s : Π y : M, V y}, CMDiff ∞ (T% v) →
    CMDiff ∞ (T% s) → MDiffAt (T% (fun y ↦ c y (v y) (s y))) x)
include hσ hcd

/-- **The Dirac operator of a smooth section is differentiable** wherever the Clifford
multiplication is: if `c(v) s` is differentiable at `x` for all smooth vector fields `v` and
smooth sections `s`, then so is `D σ` for every smooth section `σ`. -/
theorem mdifferentiableAt_diracOperator : MDiffAt (T% (cov.diracOperator c σ)) x := by
  obtain ⟨N, hN, -, Y, hY⟩ := TauCeti.exists_nhds_orthonormal_sections (I := I) (F := E)
    (V := fun y : M ↦ TangentSpace I y) (n := ∞) x
  refine (mdifferentiableAt_sum_frame cov c hσ hcd fun i ↦ (Y i).contMDiff).congr_of_eventuallyEq ?_
  filter_upwards [eventually_diracOperator_eq cov c (Filter.eventually_of_mem hN hY)] with y hy
  rw [hy]

variable (hcomp : ∀ {v : Π y : M, TangentSpace I y} {s : Π y : M, V y}, CMDiff ∞ (T% v) →
    CMDiff ∞ (T% s) → ∀ w, cov (fun y ↦ c y (v y) (s y)) x w =
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
  have hss (i : ι) : CMDiff ∞ (T% (fun y : M ↦ cov σ y (Y i y))) := cov.contMDiff_apply (hYs i) hσ'
  -- `∇_w (∇_{Yᵢ} σ) = ∇²σ(w, Yᵢ) + ∇_{∇ᵀ_w Yᵢ} σ`.
  have h2 (i : ι) : cov (fun y : M ↦ cov σ y (Y i y)) x w =
      cov.secondCovariantDerivative covT σ x w (Y i x) + cov σ x (covT (Y i) x w) := by
    rw [cov.secondCovariantDerivative_apply covT hσ x (hYs i) w, sub_add_cancel]
  rw [cov.isCovariantDerivativeOnUniv.sum fun i _ ↦ hcd (hYs i) (hss i), _root_.sum_apply]
  simp only [hcomp (hYs _) (hss _), h2, map_add]
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
  obtain ⟨N, hN, -, e, he⟩ := TauCeti.exists_nhds_orthonormal_sections (I := I) (F := E)
    (V := fun y : M ↦ TangentSpace I y) (n := ∞) x
  set Y : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y := fun i ↦ e i
  have hYs (i) : CMDiff ∞ (T% (Y i)) := (e i).contMDiff
  have hY : ∀ᶠ y in 𝓝 x, Orthonormal ℝ (Y · y) ∧ ⊤ ≤ Submodule.span ℝ (Set.range (Y · y)) :=
    Filter.eventually_of_mem hN he
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
theorem diracOperator_diracOperator_eq_roughLaplacian_add {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.diracOperator c (cov.diracOperator c σ) x =
      cov.roughLaplacian covT σ x +
        (2 : ℝ)⁻¹ • ∑ i, ∑ j, c x (b i) (c x (b j) (cov.curvatureTensor x (b i) (b j) (σ x))) := by
  rw [cov.diracOperator_eq_sum c _ x b]
  simp only [covariantDerivative_diracOperator_apply cov c covT hcovT hσ hcd hcomp b, map_sum]
  exact sum_sum_secondCovariantDerivative_eq cov c covT hσ htor hcl b

/-- **The Weitzenböck formula for the Dirac operator.** Let `∇ᵀ` be metric on all of `M` with
torsion vanishing at `x` (for instance, the Levi-Civita connection), and let the Clifford
multiplication `c` satisfy `c(v)² = -⟪v, v⟫` at `x` and be differentiable and compatible with `∇`
and `∇ᵀ` there. Then for every smooth section `σ` and every orthonormal basis `eᵢ` of `T_x M`,
indexed by a linear order, `D (D σ) = ∇*∇ σ + ∑_{i < j} c(eᵢ) c(eⱼ) R(eᵢ, eⱼ) σ` at `x`, where
`R` is the curvature of `∇`. -/
theorem diracOperator_diracOperator_eq_roughLaplacian_add_sum_lt {ι : Type*} [Fintype ι]
    [LinearOrder ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.diracOperator c (cov.diracOperator c σ) x =
      cov.roughLaplacian covT σ x +
        ∑ i, ∑ j with i < j, c x (b i) (c x (b j) (cov.curvatureTensor x (b i) (b j) (σ x))) := by
  rw [diracOperator_diracOperator_eq_roughLaplacian_add cov c covT hcovT hσ hcd hcomp htor hcl b]
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
