/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Coordinates
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Christoffel
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Geometry.Manifold.MFDeriv.Chart
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Topology.Algebra.Module.BilinearForm
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity

/-!
# Curvature as a function of the second-order jet of a metric

In coordinates, the curvature of a metric at a point is a universal expression in the value and
the first and second derivatives of its coefficients there: polynomial in the derivatives and in
the entries of the inverse Gram matrix. This file writes that expression down and identifies it
with the curvature of the Levi-Civita connection. For a basis `b` of the model space, the
*coordinate jet* of a metric at a point consists of its Gram matrix `g_ij = g(b i, b j)`, the first
derivatives `∂ₖ g_ij` and the second derivatives `∂ₘ ∂ₖ g_ij` of these coefficients in the
directions of `b`. From such a jet we define

* the Christoffel symbols `christoffelOfJet`,
  `Γᵏᵢⱼ = (1/2) Σ_l g^(kl) (∂ᵢ g_jl + ∂ⱼ g_il - ∂_l g_ij)`;
* their derivatives `christoffelDerivOfJet`, obtained by differentiating
  `g(Γ(∂ᵢ, ∂ⱼ), ∂_l) = (∂ᵢ g_jl + ∂ⱼ g_il - ∂_l g_ij) / 2`;
* the curvature coefficients `riemannOfJet`, the `l`-th coordinate of `R(∂ᵢ, ∂ⱼ)∂ₖ`;
* the scalar curvature `scalarCurvatureOfJet`, the contraction `Σⱼₖ g^(jk) Σᵢ Rⁱᵢⱼₖ`.

The scalar curvature of a jet depends continuously on the jet wherever its Gram matrix is
invertible (`ContinuousAt.scalarCurvatureOfJet`). For the Levi-Civita connection of a smooth
metric read in a chart, the Christoffel symbols, their derivatives along the coordinate frame and
the curvature coefficients are those of the coordinate jet of the chart metric, for metrics of any
signature; for a smooth Riemannian metric, so is the scalar curvature
(`Bundle.ContMDiffRiemannianMetric.scalarCurvature_eq_scalarCurvatureOfJet`). Thus scalar
curvature is a continuous second-order differential expression in the metric. In particular, for
a family of metrics whose chart coefficients and their first and second derivatives depend jointly
continuously on a parameter, the scalar curvature is jointly continuous in the parameter and the
point (`Bundle.ContMDiffRiemannianMetric.continuousAt_scalarCurvature_of_continuousAt_chartMetric`).
This is the input for the openness of positive scalar curvature under `C²` perturbations and for
uniform scalar-curvature bounds over compact families of metrics.

The coordinate identifications hold at points of a chart domain whose chart image is an interior
point of the model, hence everywhere on a manifold without boundary. Jets of fields of bilinear
forms are taken through their scalar coefficients `z ↦ G z (b i) (b j)`, so that no iterated
derivative valued in spaces of multilinear maps is needed.

The index and sign conventions are those of
`TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Coordinates`, following
J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 7:
`R(X,Y)Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z`.

## Main definitions and results

* `TauCeti.Manifold.christoffelOfJet`, `TauCeti.Manifold.christoffelDerivOfJet`,
  `TauCeti.Manifold.riemannOfJet` and `TauCeti.Manifold.scalarCurvatureOfJet`: the Christoffel
  symbols, their derivatives, the curvature coefficients and the scalar curvature of a coordinate
  jet.
* `ContinuousAt.scalarCurvatureOfJet`: the scalar curvature of a jet is continuous at jets with
  invertible Gram matrix.
* `TauCeti.Manifold.repr_fderiv_christoffelSecondKind_eq_christoffelDerivOfJet`: the derivatives
  of the Christoffel symbols of a field of symmetric nondegenerate bilinear forms on a vector space.
* `ContMDiffNondegenerateMetric.IsLeviCivitaConnection.mvfderiv_christoffelSymbol` and
  `ContMDiffNondegenerateMetric.IsLeviCivitaConnection.localFrameCoeff_curvatureOperator`, in the
  namespace `TauCeti.Manifold`: the derivatives of the Christoffel symbols and the curvature
  coefficients of a Levi-Civita connection in a chart.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_eq_scalarCurvatureOfJet`: the scalar curvature
  of a smooth Riemannian metric in a chart.
* `Bundle.ContMDiffRiemannianMetric.continuousAt_scalarCurvature_of_continuousAt_chartMetric`:
  joint continuity of scalar curvature along a `C²`-continuous family of metrics.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 5 and 7: the Christoffel symbols and the curvature of a metric in coordinates.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser (1992), Chapter 4.
-/

public section

noncomputable section

open Bundle Filter Module Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

/-! ### Curvature of a coordinate jet -/

section Jet

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **Christoffel symbols of a coordinate jet**. For a metric whose Gram matrix in a basis is
`g` and whose coefficients have first derivatives `dg k i j = ∂ₖ g_ij`, these are
`Γᵏᵢⱼ = (1/2) Σ_l g^(kl) (∂ᵢ g_jl + ∂ⱼ g_il - ∂_l g_ij)`, with `g^(kl)` the inverse of `g`. -/
def christoffelOfJet (g : Matrix ι ι ℝ) (dg : ι → ι → ι → ℝ) (i j k : ι) : ℝ :=
  2⁻¹ * ∑ l, g⁻¹ k l * (dg i j l + dg j i l - dg l i j)

/-- The defining formula of the Christoffel symbols of a coordinate jet. -/
theorem christoffelOfJet_def (g : Matrix ι ι ℝ) (dg : ι → ι → ι → ℝ) (i j k : ι) :
    christoffelOfJet g dg i j k = 2⁻¹ * ∑ l, g⁻¹ k l * (dg i j l + dg j i l - dg l i j) :=
  (rfl)

/-- The **derivatives of the Christoffel symbols of a coordinate jet**. For a metric whose Gram
matrix is `g`, with first derivatives `dg k i j = ∂ₖ g_ij` and second derivatives
`ddg m k i j = ∂ₘ ∂ₖ g_ij`, this is
`∂ₘ Γᵏᵢⱼ = Σ_l g^(kl) ((∂ₘ∂ᵢ g_jl + ∂ₘ∂ⱼ g_il - ∂ₘ∂_l g_ij) / 2 - Σ_q ∂ₘ g_ql Γ^qᵢⱼ)`,
obtained by differentiating `g(Γ(∂ᵢ, ∂ⱼ), ∂_l) = (∂ᵢ g_jl + ∂ⱼ g_il - ∂_l g_ij) / 2`. -/
def christoffelDerivOfJet (g : Matrix ι ι ℝ) (dg : ι → ι → ι → ℝ) (ddg : ι → ι → ι → ι → ℝ)
    (m i j k : ι) : ℝ :=
  ∑ l, g⁻¹ k l * (2⁻¹ * (ddg m i j l + ddg m j i l - ddg m l i j) -
    ∑ q, dg m q l * christoffelOfJet g dg i j q)

/-- The defining formula of the derivatives of the Christoffel symbols of a coordinate jet. -/
theorem christoffelDerivOfJet_def (g : Matrix ι ι ℝ) (dg : ι → ι → ι → ℝ)
    (ddg : ι → ι → ι → ι → ℝ) (m i j k : ι) :
    christoffelDerivOfJet g dg ddg m i j k =
      ∑ l, g⁻¹ k l * (2⁻¹ * (ddg m i j l + ddg m j i l - ddg m l i j) -
        ∑ q, dg m q l * christoffelOfJet g dg i j q) :=
  (rfl)

/-- The **curvature coefficients of a coordinate jet**: the `l`-th coordinate of `R(∂ᵢ, ∂ⱼ)∂ₖ`,
`∂ᵢ Γˡⱼₖ - ∂ⱼ Γˡᵢₖ + Σₘ (Γᵐⱼₖ Γˡᵢₘ - Γᵐᵢₖ Γˡⱼₘ)`, for the Christoffel symbols
`christoffelOfJet` and their derivatives `christoffelDerivOfJet`. -/
def riemannOfJet (g : Matrix ι ι ℝ) (dg : ι → ι → ι → ℝ) (ddg : ι → ι → ι → ι → ℝ)
    (i j k l : ι) : ℝ :=
  christoffelDerivOfJet g dg ddg i j k l - christoffelDerivOfJet g dg ddg j i k l +
    ∑ m, (christoffelOfJet g dg j k m * christoffelOfJet g dg i m l -
      christoffelOfJet g dg i k m * christoffelOfJet g dg j m l)

/-- The defining formula of the curvature coefficients of a coordinate jet. -/
theorem riemannOfJet_def (g : Matrix ι ι ℝ) (dg : ι → ι → ι → ℝ) (ddg : ι → ι → ι → ι → ℝ)
    (i j k l : ι) :
    riemannOfJet g dg ddg i j k l =
      christoffelDerivOfJet g dg ddg i j k l - christoffelDerivOfJet g dg ddg j i k l +
        ∑ m, (christoffelOfJet g dg j k m * christoffelOfJet g dg i m l -
          christoffelOfJet g dg i k m * christoffelOfJet g dg j m l) :=
  (rfl)

/-- The **scalar curvature of a coordinate jet** `(g, ∂g, ∂²g)`: the contraction
`Σⱼₖ g^(jk) Σᵢ Rⁱᵢⱼₖ` of the curvature coefficients `riemannOfJet` against the inverse of the
Gram matrix `g`. -/
def scalarCurvatureOfJet (g : Matrix ι ι ℝ) (dg : ι → ι → ι → ℝ) (ddg : ι → ι → ι → ι → ℝ) :
    ℝ :=
  ∑ j, ∑ k, g⁻¹ j k * ∑ i, riemannOfJet g dg ddg i j k i

/-- The defining formula of the scalar curvature of a coordinate jet. -/
theorem scalarCurvatureOfJet_def (g : Matrix ι ι ℝ) (dg : ι → ι → ι → ℝ)
    (ddg : ι → ι → ι → ι → ℝ) :
    scalarCurvatureOfJet g dg ddg = ∑ j, ∑ k, g⁻¹ j k * ∑ i, riemannOfJet g dg ddg i j k i :=
  (rfl)

end Jet

end TauCeti.Manifold

open TauCeti.Manifold in
/-- **Scalar curvature is continuous in the second-order jet of the metric.** The scalar curvature
of a coordinate jet depends continuously on the jet at every jet whose Gram matrix is invertible. -/
theorem ContinuousAt.scalarCurvatureOfJet {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Type*} [TopologicalSpace X] {g : X → Matrix ι ι ℝ} {dg : X → ι → ι → ι → ℝ}
    {ddg : X → ι → ι → ι → ι → ℝ} {x : X} (hg : ContinuousAt g x) (hdet : (g x).det ≠ 0)
    (hdg : ContinuousAt dg x) (hddg : ContinuousAt ddg x) :
    ContinuousAt (fun y ↦ scalarCurvatureOfJet (g y) (dg y) (ddg y)) x := by
  -- Every term is a finite sum of products of entries of `g⁻¹`, `dg` and `ddg`.
  have hinv (k l : ι) : ContinuousAt (fun y ↦ (g y)⁻¹ k l) x :=
    ((continuous_apply_apply k l).continuousAt.comp (continuousAt_matrix_inv _
      (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet))).comp hg
  have h₁ (i j k : ι) : ContinuousAt (fun y ↦ dg y i j k) x :=
    (by fun_prop : Continuous fun f : ι → ι → ι → ℝ ↦ f i j k).continuousAt.comp hdg
  have h₂ (m i j k : ι) : ContinuousAt (fun y ↦ ddg y m i j k) x :=
    (by fun_prop : Continuous fun f : ι → ι → ι → ι → ℝ ↦ f m i j k).continuousAt.comp hddg
  have hΓ (i j k : ι) : ContinuousAt (fun y ↦ christoffelOfJet (g y) (dg y) i j k) x :=
    continuousAt_const.mul (tendsto_finsetSum _ fun l _ ↦
      (hinv k l).mul (((h₁ i j l).add (h₁ j i l)).sub (h₁ l i j)))
  have hDΓ (m i j k : ι) :
      ContinuousAt (fun y ↦ christoffelDerivOfJet (g y) (dg y) (ddg y) m i j k) x :=
    tendsto_finsetSum _ fun l _ ↦ (hinv k l).mul ((continuousAt_const.mul
      (((h₂ m i j l).add (h₂ m j i l)).sub (h₂ m l i j))).sub
        (tendsto_finsetSum _ fun q _ ↦ (h₁ m q l).mul (hΓ i j q)))
  have hR (i j k l : ι) :
      ContinuousAt (fun y ↦ riemannOfJet (g y) (dg y) (ddg y) i j k l) x :=
    ((hDΓ i j k l).sub (hDΓ j i k l)).add (tendsto_finsetSum _ fun m _ ↦
      ((hΓ j k m).mul (hΓ i m l)).sub ((hΓ i k m).mul (hΓ j m l)))
  exact tendsto_finsetSum _ fun j _ ↦ tendsto_finsetSum _ fun k _ ↦
    (hinv j k).mul (tendsto_finsetSum _ fun i _ ↦ hR i j k i)

namespace TauCeti.Manifold

/-! ### The jet of a field of bilinear forms on a vector space -/

section VectorSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {G : E → E →L[ℝ] E →L[ℝ] ℝ} {z : E}

omit [FiniteDimensional ℝ E] in
/-- At a point where it is differentiable, the derivative of a field of bilinear forms, applied to
two vectors, is the derivative of the corresponding coefficient. -/
private theorem fderiv_apply_apply_eq (hG : DifferentiableAt ℝ G z) (u v w : E) :
    fderiv ℝ G z u v w = fderiv ℝ (fun y ↦ G y v w) z u := by
  rw [fderiv_clm_apply_const_apply (hG.clm_apply (differentiableAt_const v)),
    fderiv_clm_apply_const_apply hG]

/-- In a basis, the Christoffel symbols of the second kind of a field `G` of symmetric
nondegenerate bilinear forms are the Christoffel symbols of its coordinate jet. -/
theorem repr_christoffelSecondKind_eq_christoffelOfJet (b : Basis ι ℝ E)
    (hG : DifferentiableAt ℝ G z) (hsymm : LinearMap.IsSymm (G z).toBilinForm)
    (hnd : (G z).toBilinForm.Nondegenerate) (i j k : ι) :
    b.repr (christoffelSecondKind G z (b i) (b j)) k =
      christoffelOfJet (LinearMap.toMatrix₂ b b (G z).toBilinForm)
        (fun k i j ↦ fderiv ℝ (fun y ↦ G y (b i) (b j)) z (b k)) i j k := by
  rw [repr_christoffelSecondKind hsymm hnd, christoffelOfJet]
  simp only [fderiv_apply_apply_eq hG]

/-- **The derivatives of the Christoffel symbols in a basis.** For a `C²` field `G` of symmetric
nondegenerate bilinear forms near `z`, the `k`-th coordinate of `∂ₘ Γ(b i, b j)` is the derivative
`christoffelDerivOfJet` of the Christoffel symbols of the coordinate jet `(g, ∂g, ∂²g)` of `G` at
`z`. -/
theorem repr_fderiv_christoffelSecondKind_eq_christoffelDerivOfJet (b : Basis ι ℝ E)
    (hG : ContDiffAt ℝ 2 G z) (hsymm : ∀ᶠ y in 𝓝 z, LinearMap.IsSymm (G y).toBilinForm)
    (hnd : ∀ᶠ y in 𝓝 z, (G y).toBilinForm.Nondegenerate) (m i j k : ι) :
    b.repr (fderiv ℝ (christoffelSecondKind G) z (b m) (b i) (b j)) k =
      christoffelDerivOfJet (LinearMap.toMatrix₂ b b (G z).toBilinForm)
        (fun k i j ↦ fderiv ℝ (fun y ↦ G y (b i) (b j)) z (b k))
        (fun m k i j ↦ fderiv ℝ (fun y ↦ fderiv ℝ (fun y' ↦ G y' (b i) (b j)) y (b k)) z (b m))
        m i j k := by
  have hΓ : DifferentiableAt ℝ (christoffelSecondKind G) z :=
    (contDiffAt_christoffelSecondKind (n := 1) (by exact_mod_cast hG) hnd).differentiableAt
      one_ne_zero
  -- On an open neighbourhood of `z`, `G` is `C²` and nondegenerate.
  obtain ⟨U, hU, hUo, hzU⟩ := eventually_nhds_iff.1 ((hG.eventually (by simp)).and hnd)
  have hGd : DifferentiableAt ℝ G z := hG.differentiableAt (by norm_num)
  -- The coefficient derivatives `y ↦ ∂ₖ g_ij(y)` are differentiable at `z`.
  have hcoeff (u v w : E) : DifferentiableAt ℝ (fun y ↦ fderiv ℝ (fun y' ↦ G y' v w) y u) z :=
    ((((hG.clm_apply contDiffAt_const).clm_apply contDiffAt_const).fderiv_right
      (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply (differentiableAt_const u)
  -- Lowering the index of `Γ` gives the Christoffel symbols of the first kind near `z`.
  have hlow (l : ι) : (fun y ↦ G y (christoffelSecondKind G y (b i) (b j)) (b l)) =ᶠ[𝓝 z]
      fun y ↦ 2⁻¹ * (fderiv ℝ (fun y' ↦ G y' (b j) (b l)) y (b i) +
        fderiv ℝ (fun y' ↦ G y' (b i) (b l)) y (b j) -
        fderiv ℝ (fun y' ↦ G y' (b i) (b j)) y (b l)) := by
    filter_upwards [hUo.mem_nhds hzU] with y hy
    have hy' := (hU y hy).1.differentiableAt (by norm_num)
    rw [apply_christoffelSecondKind (hU y hy).2, christoffelFirstKind_apply,
      ← fderiv_apply_apply_eq hy', ← fderiv_apply_apply_eq hy', ← fderiv_apply_apply_eq hy']
    ring
  -- Differentiating that identity in the direction `b m` gives the pairings of `∂ₘ Γ(b i, b j)`.
  have hpair (l : ι) : G z (fderiv ℝ (christoffelSecondKind G) z (b m) (b i) (b j)) (b l) =
      2⁻¹ * (fderiv ℝ (fun y ↦ fderiv ℝ (fun y' ↦ G y' (b j) (b l)) y (b i)) z (b m) +
        fderiv ℝ (fun y ↦ fderiv ℝ (fun y' ↦ G y' (b i) (b l)) y (b j)) z (b m) -
        fderiv ℝ (fun y ↦ fderiv ℝ (fun y' ↦ G y' (b i) (b j)) y (b l)) z (b m)) -
      fderiv ℝ G z (b m) (christoffelSecondKind G z (b i) (b j)) (b l) := by
    have hΓij : DifferentiableAt ℝ (fun y ↦ christoffelSecondKind G y (b i) (b j)) z :=
      (hΓ.clm_apply (differentiableAt_const _)).clm_apply (differentiableAt_const _)
    have h := congrArg (fun L : E →L[ℝ] ℝ ↦ L (b m)) (hlow l).fderiv_eq
    simp only [fderiv_bilin_apply hGd hΓij (differentiableAt_const _), fderiv_const_apply,
      zero_apply, map_zero, add_zero] at h
    rw [fderiv_clm_apply_const_apply (hΓ.clm_apply (differentiableAt_const _)),
      fderiv_clm_apply_const_apply hΓ] at h
    rw [fderiv_const_mul (((hcoeff _ _ _).fun_add (hcoeff _ _ _)).fun_sub (hcoeff _ _ _)),
      fderiv_fun_sub ((hcoeff _ _ _).fun_add (hcoeff _ _ _)) (hcoeff _ _ _),
      fderiv_fun_add (hcoeff _ _ _) (hcoeff _ _ _)] at h
    simp only [smul_apply, add_apply, sub_apply, smul_eq_mul] at h
    linear_combination h
  -- Solve for the coordinates of `∂ₘ Γ(b i, b j)` with the inverse Gram matrix.
  rw [repr_eq_sum_inv_toMatrix₂_mul_apply hnd.self_of_nhds, christoffelDerivOfJet]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [ContinuousLinearMap.isSymm_toBilinForm_iff.1 hsymm.self_of_nhds, hpair]
  congr 2
  conv_lhs => rw [← b.sum_repr (christoffelSecondKind G z (b i) (b j))]
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    smul_eq_mul, repr_christoffelSecondKind_eq_christoffelOfJet b hGd hsymm.self_of_nhds
      hnd.self_of_nhds, fderiv_apply_apply_eq hGd]
  exact Finset.sum_congr rfl fun q _ ↦ mul_comm _ _

end VectorSpace

/-! ### Christoffel symbols and curvature of a Levi-Civita connection in a chart -/

namespace ContMDiffNondegenerateMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : ContMDiffNondegenerateMetric (I := I) (M := M)}
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E) {x₀ y : M}

omit [Fintype ι] [DecidableEq ι] in
/-- Near a point of the chart domain at `x₀` whose chart image is interior, the Christoffel
symbols of a Levi-Civita connection of `g`, in the frame of `b`, are the coordinates of the
Christoffel symbols of the second kind of the chart metric. -/
theorem IsLeviCivitaConnection.christoffelSymbol_eventuallyEq [Finite ι]
    (h : g.IsLeviCivitaConnection cov) (hy : y ∈ (extChartAt I x₀).source)
    (hint : extChartAt I x₀ y ∈ interior (range I)) (i j k : ι) :
    christoffelSymbol I b (trivializationAt E (TangentSpace I) x₀) cov i j k =ᶠ[𝓝 y]
      fun y' ↦ b.repr
        (christoffelSecondKind (g.chartMetric x₀) (extChartAt I x₀ y') (b i) (b j)) k := by
  filter_upwards [(isOpen_extChartAt_source x₀).mem_nhds hy,
    (continuousAt_extChartAt' hy).preimage_mem_nhds (isOpen_interior.mem_nhds hint)]
    with y' hy' hint'
  have := Fintype.ofFinite ι
  rw [← coord_christoffelMap_apply_basis b (cov.isCovariantDerivativeOn (s := _))
    (by simpa using hy') i j k, h.christoffelMap_apply_eq_christoffelSecondKind b hy' hint',
    Basis.coord_apply]

/-- **The derivatives of the Christoffel symbols of a Levi-Civita connection in a chart.** At a
point `y` of the chart domain at `x₀` whose chart image `z` is interior, the derivative of the
Christoffel symbol `Γᵏᵢⱼ` of a Levi-Civita connection of `g` along the `m`-th frame vector is
`christoffelDerivOfJet` of the coordinate jet `(g, ∂g, ∂²g)` of the chart metric at `z`. -/
theorem IsLeviCivitaConnection.mvfderiv_christoffelSymbol (h : g.IsLeviCivitaConnection cov)
    (hy : y ∈ (extChartAt I x₀).source) (hint : extChartAt I x₀ y ∈ interior (range I))
    (m i j k : ι) :
    mvfderiv I (christoffelSymbol I b (trivializationAt E (TangentSpace I) x₀) cov i j k) y
        ((trivializationAt E (TangentSpace I) x₀).localFrame b m y) =
      christoffelDerivOfJet
        (LinearMap.toMatrix₂ b b (g.chartMetric x₀ (extChartAt I x₀ y)).toBilinForm)
        (fun k i j ↦ fderiv ℝ (fun z ↦ g.chartMetric x₀ z (b i) (b j)) (extChartAt I x₀ y) (b k))
        (fun m k i j ↦ fderiv ℝ (fun z ↦ fderiv ℝ (fun z' ↦ g.chartMetric x₀ z' (b i) (b j)) z
          (b k)) (extChartAt I x₀ y) (b m)) m i j k := by
  set e := trivializationAt E (TangentSpace I) x₀
  have hbase : y ∈ e.baseSet := by simpa [e] using hy
  have htarget : (extChartAt I x₀).target ∈ 𝓝 (extChartAt I x₀ y) := by
    rw [← nhdsWithin_eq_nhds.2 (mem_interior_iff_mem_nhds.1 hint)]
    exact extChartAt_target_mem_nhdsWithin' hy
  have hG := g.contDiffAt_chartMetric hy hint
  have hnd : ∀ᶠ z in 𝓝 (extChartAt I x₀ y), (g.chartMetric x₀ z).toBilinForm.Nondegenerate :=
    eventually_of_mem htarget fun _ hz ↦ g.nondegenerate_chartMetric hz
  have hsymm : ∀ᶠ z in 𝓝 (extChartAt I x₀ y), LinearMap.IsSymm (g.chartMetric x₀ z).toBilinForm :=
    eventually_of_mem htarget fun _ hz ↦ g.isSymm_chartMetric hz
  have hΓ : DifferentiableAt ℝ (christoffelSecondKind (g.chartMetric x₀)) (extChartAt I x₀ y) :=
    (contDiffAt_christoffelSecondKind (n := 1) (hG.of_le (by simp)) hnd).differentiableAt
      one_ne_zero
  -- The coordinate function `z ↦ Γᵏᵢⱼ(z)` of the chart metric, and its derivative.
  let L := LinearMap.toContinuousLinearMap (b.coord k)
  have hF : HasFDerivAt (fun z ↦ L (christoffelSecondKind (g.chartMetric x₀) z (b i) (b j)))
      (L.comp (fderiv ℝ (fun z ↦ christoffelSecondKind (g.chartMetric x₀) z (b i) (b j))
        (extChartAt I x₀ y))) (extChartAt I x₀ y) :=
    L.hasFDerivAt.comp _ ((hΓ.clm_apply (differentiableAt_const _)).clm_apply
      (differentiableAt_const _)).hasFDerivAt
  have hφ : mfderiv% (extChartAt I x₀) y (e.localFrame b m y) = b m := by
    rw [← symmL_basis_eq_localFrame b hbase m,
      ← TangentBundle.continuousLinearMapAt_trivializationAt (by simpa using hy)]
    exact e.continuousLinearMapAt_symmL hbase (b m)
  -- Near `y`, the Christoffel symbol is the coordinate function composed with the chart.
  set F := fun z ↦ L (christoffelSecondKind (g.chartMetric x₀) z (b i) (b j))
  have hfun : (fun y' ↦ b.repr
      (christoffelSecondKind (g.chartMetric x₀) (extChartAt I x₀ y') (b i) (b j)) k) =
      F ∘ extChartAt I x₀ := by
    ext y'
    simp [F, L, Basis.coord_apply]
  have hloc : (F ∘ extChartAt I x₀) ∘ (extChartAt I x₀).symm =ᶠ[𝓝 (extChartAt I x₀ y)] F :=
    eventually_of_mem htarget fun z hz ↦ by
      simp only [Function.comp_apply, (extChartAt I x₀).right_inv hz]
  rw [Filter.EventuallyEq.mvfderiv_eq (h.christoffelSymbol_eventuallyEq b hy hint i j k), hfun,
    mvfderiv_apply_eq_mfderiv_apply, TauCeti.mfderiv_eq_fderiv_comp_mfderiv_extChartAt hy
      (hF.differentiableAt.congr_of_eventuallyEq hloc)]
  -- The tangent space of the model is `E` itself, which the generic rewrites cannot see.
  refine ((ContinuousLinearMap.comp_apply _ _ _).trans (congrArg _ hφ)).trans ?_
  have hFb : fderiv ℝ F (extChartAt I x₀ y) (b m) =
      b.repr (fderiv ℝ (christoffelSecondKind (g.chartMetric x₀)) (extChartAt I x₀ y) (b m) (b i)
        (b j)) k := by
    rw [hF.fderiv, ContinuousLinearMap.comp_apply,
      fderiv_clm_apply_const_apply (hΓ.clm_apply (differentiableAt_const _)),
      fderiv_clm_apply_const_apply hΓ]
    simp only [L, LinearMap.coe_toContinuousLinearMap', Basis.coord_apply]
  rw [hloc.fderiv_eq]
  refine hFb.trans ?_
  exact repr_fderiv_christoffelSecondKind_eq_christoffelDerivOfJet b (hG.of_le (by simp)) hsymm
    hnd m i j k

/-- **The curvature of a Levi-Civita connection in a chart.** At a point `y` of the chart domain
at `x₀` whose chart image `z` is interior, the `l`-th coefficient of `R(∂ᵢ, ∂ⱼ)∂ₖ` in the frame of
`b`, for a Levi-Civita connection of `g`, is `riemannOfJet` of the coordinate jet `(g, ∂g, ∂²g)` of
the chart metric at `z`. -/
theorem IsLeviCivitaConnection.localFrameCoeff_curvatureOperator (h : g.IsLeviCivitaConnection cov)
    [ContMDiffCovariantDerivativeOn E 1 cov.toFun
      (trivializationAt E (TangentSpace I) x₀).baseSet]
    (hy : y ∈ (extChartAt I x₀).source) (hint : extChartAt I x₀ y ∈ interior (range I))
    (i j k l : ι) :
    (trivializationAt E (TangentSpace I) x₀).localFrameCoeff I b l y
        (cov.curvatureOperator ((trivializationAt E (TangentSpace I) x₀).localFrame b i)
          ((trivializationAt E (TangentSpace I) x₀).localFrame b j)
          ((trivializationAt E (TangentSpace I) x₀).localFrame b k) y) =
      riemannOfJet
        (LinearMap.toMatrix₂ b b (g.chartMetric x₀ (extChartAt I x₀ y)).toBilinForm)
        (fun k i j ↦ fderiv ℝ (fun z ↦ g.chartMetric x₀ z (b i) (b j)) (extChartAt I x₀ y) (b k))
        (fun m k i j ↦ fderiv ℝ (fun z ↦ fderiv ℝ (fun z' ↦ g.chartMetric x₀ z' (b i) (b j)) z
          (b k)) (extChartAt I x₀ y) (b m)) i j k l := by
  have : IsManifold I (minSmoothness ℝ 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have hΓ (a c d : ι) :
      christoffelSymbol I b (trivializationAt E (TangentSpace I) x₀) cov a c d y =
        christoffelOfJet
          (LinearMap.toMatrix₂ b b (g.chartMetric x₀ (extChartAt I x₀ y)).toBilinForm)
          (fun k i j ↦ fderiv ℝ (fun z ↦ g.chartMetric x₀ z (b i) (b j)) (extChartAt I x₀ y)
            (b k)) a c d := by
    rw [(h.christoffelSymbol_eventuallyEq b hy hint a c d).self_of_nhds]
    exact repr_christoffelSecondKind_eq_christoffelOfJet b
      ((g.contDiffAt_chartMetric hy hint).differentiableAt (by simp))
      (g.isSymm_chartMetric ((extChartAt I x₀).map_source hy))
      (g.nondegenerate_chartMetric ((extChartAt I x₀).map_source hy)) a c d
  rw [CovariantDerivative.localFrameCoeff_curvatureOperator cov b x₀ hy i j k l,
    h.mvfderiv_christoffelSymbol b hy hint i j k l, h.mvfderiv_christoffelSymbol b hy hint j i k l]
  simp only [hΓ, riemannOfJet]

end ContMDiffNondegenerateMetric

end TauCeti.Manifold

/-! ### Scalar curvature of a Riemannian metric in a chart -/

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E) {x₀ y : M}

/-- **Scalar curvature as a second-order expression in the metric.** At a point `y` of the chart
domain at `x₀` whose chart image `z` is interior, the scalar curvature of a smooth Riemannian
metric `g` is `scalarCurvatureOfJet` of the coordinate jet of the chart metric `G` of `g` at `z`,
in any basis `b` of the model: the Gram matrix `G_ij(z)`, the first derivatives `∂ₖ G_ij(z)` and
the second derivatives `∂ₘ ∂ₖ G_ij(z)`. -/
theorem scalarCurvature_eq_scalarCurvatureOfJet (hy : y ∈ (extChartAt I x₀).source)
    (hint : extChartAt I x₀ y ∈ interior (range I)) :
    g.scalarCurvature y = scalarCurvatureOfJet
      (LinearMap.toMatrix₂ b b
        (g.toNondegenerateMetric.chartMetric x₀ (extChartAt I x₀ y)).toBilinForm)
      (fun k i j ↦ fderiv ℝ (fun z ↦ g.toNondegenerateMetric.chartMetric x₀ z (b i) (b j))
        (extChartAt I x₀ y) (b k))
      (fun m k i j ↦ fderiv ℝ (fun z ↦ fderiv ℝ
        (fun z' ↦ g.toNondegenerateMetric.chartMetric x₀ z' (b i) (b j)) z (b k))
        (extChartAt I x₀ y) (b m)) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  set e := trivializationAt E (TangentSpace I) x₀
  have hbase : y ∈ e.baseSet := by simpa [e] using hy
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : ContMDiffCovariantDerivativeOn E 1 (CovariantDerivative.leviCivitaConnection I M).toFun
      e.baseSet :=
    CovariantDerivative.contMDiffCovariantDerivativeOn_leviCivitaConnection (m := ∞) (k := ∞)
      e.open_baseSet (WithTop.coe_le_coe.2 le_top) (WithTop.coe_le_coe.2 le_top)
  have hlc : g.toNondegenerateMetric.IsLeviCivitaConnection
      (CovariantDerivative.leviCivitaConnection I M) :=
    (ContMDiffNondegenerateMetric.isLeviCivitaConnection_iff_of_apply_eq_inner
      fun x v w ↦ (g.toNondegenerateMetric_apply x v w).trans
        (g.inner_riemannianBundle x v w).symm).2
      (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I)
  -- Compute the trace in the basis of `T_y M` given by the frame of `b`.
  set B := e.basisAt b hbase
  have hB (i : ι) : B i = e.localFrame b i y := (e.localFrame_apply_of_mem_baseSet b hbase).symm
  have hgram : Matrix.gram ℝ B = LinearMap.toMatrix₂ b b
      (g.toNondegenerateMetric.chartMetric x₀ (extChartAt I x₀ y)).toBilinForm := by
    ext i j
    rw [Matrix.gram_apply, LinearMap.toMatrix₂_apply, ContinuousLinearMap.toBilinForm_apply,
      ContMDiffNondegenerateMetric.chartMetric_extChartAt_apply _ hy, hB, hB,
      ← symmL_basis_eq_localFrame b hbase, ← symmL_basis_eq_localFrame b hbase,
      e.symmL_apply hbase, e.symmL_apply hbase]
    exact (g.inner_riemannianBundle y _ _).trans (g.toNondegenerateMetric_apply y _ _).symm
  rw [scalarCurvature_def, CovariantDerivative.scalarCurvature_apply,
    TauCeti.bilinFormTrace_eq_sum_inv_gram _ B, hgram, scalarCurvatureOfJet]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  rw [CovariantDerivative.ricciTensor_eq_sum _ y B]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have : IsManifold I (1 + 1) M := IsManifold.of_le (n := ∞) (by simp)
  have : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have hframe (a : ι) : CMDiff[e.baseSet] ∞ (T% (e.localFrame b a)) :=
    e.contMDiffOn_localFrame_baseSet ∞ b a
  rw [hB, hB, hB, CovariantDerivative.curvatureTensor_apply_of_contMDiffOn _ y e.open_baseSet
    hbase (hframe i) (hframe j) (hframe k),
    ← e.localFrameCoeff_apply_of_mem_baseSet (I := I) b hbase,
    hlc.localFrameCoeff_curvatureOperator b hy hint]

/-- **Scalar curvature is continuous along `C²`-continuous families of metrics.** Let `g p` be a
family of smooth Riemannian metrics indexed by a topological space `P`, and `y₀` a point whose
image in its own chart is interior. If the Gram matrix, first and second derivatives of the chart
metrics of `g p` at `y₀`, in a basis `b`, depend continuously on `(p, z)` at `(p₀, z₀)`, where `z₀`
is the chart image of `y₀`, then `(p, y) ↦ Scal(g p)(y)` is continuous at `(p₀, y₀)`. -/
theorem continuousAt_scalarCurvature_of_continuousAt_chartMetric {P : Type*} [TopologicalSpace P]
    (g : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {p₀ : P} {y₀ : M}
    (hint : extChartAt I y₀ y₀ ∈ interior (range I))
    (h₀ : ContinuousAt (fun q : P × E ↦ LinearMap.toMatrix₂ b b
      ((g q.1).toNondegenerateMetric.chartMetric y₀ q.2).toBilinForm) (p₀, extChartAt I y₀ y₀))
    (h₁ : ContinuousAt (fun q : P × E ↦ fun k i j ↦
      fderiv ℝ (fun z ↦ (g q.1).toNondegenerateMetric.chartMetric y₀ z (b i) (b j)) q.2 (b k))
      (p₀, extChartAt I y₀ y₀))
    (h₂ : ContinuousAt (fun q : P × E ↦ fun m k i j ↦ fderiv ℝ (fun z ↦ fderiv ℝ
      (fun z' ↦ (g q.1).toNondegenerateMetric.chartMetric y₀ z' (b i) (b j)) z (b k)) q.2 (b m))
      (p₀, extChartAt I y₀ y₀)) :
    ContinuousAt (fun q : P × M ↦ (g q.1).scalarCurvature q.2) (p₀, y₀) := by
  have hchart : ContinuousAt (fun q : P × M ↦ extChartAt I y₀ q.2) (p₀, y₀) :=
    ContinuousAt.comp (f := Prod.snd) (continuousAt_extChartAt y₀) continuousAt_snd
  have hφ : ContinuousAt (fun q : P × M ↦ (q.1, extChartAt I y₀ q.2)) (p₀, y₀) :=
    continuousAt_fst.prodMk hchart
  have hdet : (LinearMap.toMatrix₂ b b
      ((g p₀).toNondegenerateMetric.chartMetric y₀ (extChartAt I y₀ y₀)).toBilinForm).det ≠ 0 :=
    (LinearMap.nondegenerate_iff_det_ne_zero b).1
      ((g p₀).toNondegenerateMetric.nondegenerate_chartMetric (mem_extChartAt_target y₀))
  set φ := fun q : P × M ↦ (q.1, extChartAt I y₀ q.2)
  have hJ₀ := h₀.comp (f := φ) hφ
  refine (hJ₀.scalarCurvatureOfJet hdet (h₁.comp (f := φ) hφ) (h₂.comp (f := φ) hφ)).congr ?_
  -- Near `(p₀, y₀)`, the point stays in the chart domain with interior chart image.
  filter_upwards [continuousAt_snd.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := I) y₀).mem_nhds (mem_extChartAt_source y₀)),
    hchart.preimage_mem_nhds (isOpen_interior.mem_nhds hint)] with q hq hq'
  exact ((g q.1).scalarCurvature_eq_scalarCurvatureOfJet b hq hq').symm

end Bundle.ContMDiffRiemannianMetric
