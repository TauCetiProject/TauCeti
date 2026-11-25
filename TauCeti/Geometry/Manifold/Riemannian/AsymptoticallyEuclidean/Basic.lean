/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import TauCeti.Analysis.Normed.Module.Ball.Exterior
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace

/-!
# Asymptotically Euclidean ends

An asymptotically Euclidean end of order `t` of a Riemannian manifold `M` is a smooth
parametrization `φ` of an open subset of `M` by the exterior `{x ∈ ℝⁿ : R < ‖x‖}`, `n > 0`, of a
closed ball, injective with invertible differential there, such that the coefficients
`g_ij(x) = g(dφ_x eᵢ, dφ_x eⱼ)` of the pulled-back metric in the standard basis satisfy
`|∂^α (g_ij - δ_ij)| ≤ C ‖x‖^(-t-|α|)` for `|α| ≤ 2`. A manifold is finite-ended
asymptotically Euclidean when finitely many, and at least one, such ends have pairwise disjoint
images whose union has compact complement.

These are the asymptotic structures on which the ADM mass and the Riemannian positive mass
theorem are stated: the mass of an end is the limit of a flux integral of the derivatives of the
coefficients `g_ij` over large coordinate spheres, and it exists when `t > (n - 2) / 2` and the
scalar curvature is integrable. The decay is only a condition on the metric; integrability of the
scalar curvature is a separate hypothesis wherever a mass is asserted.

The definitions are predicates on the parametrization and the radius, so that the values of `φ`
inside the ball carry no data. The size of the derivatives is measured by the operator norm of
`iteratedFDeriv`, which is equivalent to the maximum of the partial derivatives `∂^α` with
`|α| = k`.

## Main definitions

* `TauCeti.pullbackMetricCoeff`: the matrix of coefficients `g(dφ_x eᵢ, dφ_x eⱼ)` of the metric
  pulled back along a map from `EuclideanSpace ℝ (Fin n)`, as a `Matrix.gram`.
* `TauCeti.IsAsymptoticallyEuclideanEnd`: `φ` is an asymptotically Euclidean end of order `t`
  on the exterior of the closed ball of radius `R`.
* `TauCeti.IsFiniteEndedAsymptoticallyEuclidean`: a finite nonempty family of such ends with
  pairwise disjoint images and compact remainder.
* `TauCeti.IsAsymptoticallyEuclideanEnd.toPartialDiffeomorph` and
  `TauCeti.IsAsymptoticallyEuclideanEnd.homeomorphImage`: an end as a partial diffeomorphism (on
  a smooth manifold) or homeomorphism (on a `C¹` manifold) from the exterior of the ball onto its
  open image.
* `TauCeti.IsAsymptoticallyEuclideanEnd.endRadius`: the coordinate radius `‖φ⁻¹(·)‖` on the image
  of an end, taking values in `Set.Ioi R`.

## Main results

* `TauCeti.norm_mfderiv_sq_eq_sum_pullbackMetricCoeff`: the squared length `‖dφ_x v‖²` is the
  quadratic form `Σᵢⱼ g_ij(x) vᵢ vⱼ` of the pulled-back metric coefficients.
* `TauCeti.IsAsymptoticallyEuclideanEnd.isOpen_image_of_subset`: an end maps open subsets of the
  exterior of its ball to open subsets of `M`.
* `TauCeti.IsAsymptoticallyEuclideanEnd.toPartialDiffeomorph_symm_apply_apply`: the inverse of an
  end, as a partial diffeomorphism, undoes the end on the exterior of its ball.
* `TauCeti.IsAsymptoticallyEuclideanEnd.eventually_notMem_image_compl_closedBall`: every point of
  `M` lies outside the image of the exterior of all large balls.
* `TauCeti.IsAsymptoticallyEuclideanEnd.isOpen_image` and
  `TauCeti.IsAsymptoticallyEuclideanEnd.isPathConnected_image`: in dimension at least two, the
  image of an end is open and path-connected.
* `TauCeti.IsAsymptoticallyEuclideanEnd.isProperMap_endRadius`: on a `C¹` manifold, the coordinate
  radius `endRadius` on the image of an end is a proper map into `Set.Ioi R`.
* `TauCeti.isAsymptoticallyEuclideanEnd_comp_iff` and
  `TauCeti.isFiniteEndedAsymptoticallyEuclidean_comp_iff`: both notions are invariant under
  Riemannian isometries.
* `TauCeti.isAsymptoticallyEuclideanEnd_id` and
  `TauCeti.isFiniteEndedAsymptoticallyEuclidean_id`: the identity parametrization of flat
  Euclidean space of positive dimension is an end of every order, and a finite-ended structure
  with one end.
* `TauCeti.not_isAsymptoticallyEuclideanEnd_smul` and
  `TauCeti.not_isAsymptoticallyEuclideanEnd_two_smul`: a non-isometric homothety `x ↦ c • x`
  (`|c| ≠ 1`, in particular `x ↦ 2 • x`) of flat Euclidean space is not an end of any positive
  order, although its coefficients are bounded.

## References

* S. Cecchini, R. Zeidler, *The positive mass theorem and distance estimates in the spin
  setting*, arXiv:2108.11972, Definitions 2.1 and 2.3.
* J. M. Lee, T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §8 and §9.
-/

public section

open Bundle Function Manifold Metric Set Filter
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

/-! ### Pulled-back metric coefficients -/

variable (I) in
/-- The matrix of coefficients `g_ij(x) = g(dφ_x eᵢ, dφ_x eⱼ)` of the Riemannian metric of `M`
pulled back along a map `φ` from Euclidean space, in the standard basis `eᵢ` of
`EuclideanSpace ℝ (Fin n)`: the Gram matrix of the partial derivatives `dφ_x eᵢ`. -/
def pullbackMetricCoeff (φ : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.gram ℝ fun i ↦
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ x (EuclideanSpace.basisFun (Fin n) ℝ i)

/-- The pulled-back metric coefficients are the Gram matrix of the partial derivatives
`dφ_x eᵢ` for the metric of `M`. -/
theorem pullbackMetricCoeff_def (φ : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) :
    pullbackMetricCoeff I φ x = Matrix.gram ℝ fun i ↦
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ x (EuclideanSpace.basisFun (Fin n) ℝ i) :=
  (rfl)

/-- An entry of the pulled-back metric coefficients is the inner product of two partial
derivatives. -/
@[simp]
theorem pullbackMetricCoeff_apply (φ : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff I φ x i j =
      inner ℝ (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ x (EuclideanSpace.basisFun (Fin n) ℝ i))
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ x (EuclideanSpace.basisFun (Fin n) ℝ j)) :=
  (rfl)

/-- The squared length of the image of a vector `v` under the differential of `φ` is the quadratic
form of the pulled-back metric coefficients: `‖dφ_x v‖² = Σᵢⱼ g_ij(x) vᵢ vⱼ`. -/
theorem norm_mfderiv_sq_eq_sum_pullbackMetricCoeff (φ : EuclideanSpace ℝ (Fin n) → M)
    (x v : EuclideanSpace ℝ (Fin n)) :
    ‖mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ x v‖ ^ 2 =
      ∑ i, ∑ j, pullbackMetricCoeff I φ x i j * v i * v j := by
  set L := mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ x
  have hv : L v = ∑ i, v i • L (EuclideanSpace.basisFun (Fin n) ℝ i) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
    exact (map_sum L _ _).trans (Finset.sum_congr rfl fun i _ ↦ map_smul _ _ _)
  rw [← real_inner_self_eq_norm_sq, hv, pullbackMetricCoeff_def,
    ← Matrix.star_dotProduct_gram_mulVec, star_trivial]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- Composing with a local Riemannian isometry does not change the pulled-back metric
coefficients at a point where the parametrization is differentiable. -/
theorem pullbackMetricCoeff_comp {f : M → N} (hf : IsLocalRiemannianIsometry I J f)
    {φ : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hφ : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ x) :
    pullbackMetricCoeff J (f ∘ φ) x = pullbackMetricCoeff I φ x := by
  ext i j
  rw [pullbackMetricCoeff_apply, mfderiv_comp x (hf.mdifferentiableAt (φ x)) hφ]
  exact hf.inner_mfderiv _ _ _

/-- For a map into a real inner product space with its flat metric, the pulled-back metric
coefficients are the Gram matrix of the partial derivatives `∂ᵢφ = Dφ(x) eᵢ`. -/
theorem pullbackMetricCoeff_eq_gram_fderiv {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] (φ : EuclideanSpace ℝ (Fin n) → G) (x : EuclideanSpace ℝ (Fin n)) :
    pullbackMetricCoeff 𝓘(ℝ, G) φ x =
      Matrix.gram ℝ fun i ↦ fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  ext i j
  rw [pullbackMetricCoeff_apply, Matrix.gram_apply, Manifold.inner_tangentSpace_vectorSpace]
  -- Read each partial derivative in `G` as the vector-valued derivative, then as `fderiv`.
  congr 1 <;> exact (NormedSpace.fromTangentSpace_apply _ _).trans
    ((mvfderiv_apply_eq_mfderiv_apply _ _ _).symm.trans (mvfderiv_eq_fderiv_apply _ _ _))

/-- For the flat metric of Euclidean space, the coefficients pulled back along the identity are
the identity matrix. -/
@[simp]
theorem pullbackMetricCoeff_id (x : EuclideanSpace ℝ (Fin n)) :
    pullbackMetricCoeff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) id x = 1 := by
  rw [pullbackMetricCoeff_eq_gram_fderiv, fderiv_id]
  exact Matrix.gram_eq_one_iff_orthonormal.2 (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal

/-- Scaling a map into a real inner product space by `c : ℝ` scales its pulled-back metric
coefficients by `c ^ 2`, without any differentiability hypothesis. -/
theorem pullbackMetricCoeff_const_smul {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] (c : ℝ) (φ : EuclideanSpace ℝ (Fin n) → G)
    (x : EuclideanSpace ℝ (Fin n)) :
    pullbackMetricCoeff 𝓘(ℝ, G) (fun y ↦ c • φ y) x =
      c ^ 2 • pullbackMetricCoeff 𝓘(ℝ, G) φ x := by
  have hd : fderiv ℝ (fun y ↦ c • φ y) x = c • fderiv ℝ φ x := by
    rw [← Pi.smul_def, fderiv_const_smul_field, Pi.smul_apply]
  ext i j
  rw [pullbackMetricCoeff_eq_gram_fderiv, pullbackMetricCoeff_eq_gram_fderiv, hd,
    Matrix.smul_apply, Matrix.gram_apply, Matrix.gram_apply]
  simp only [smul_apply, real_inner_smul_left, real_inner_smul_right, smul_eq_mul]
  ring

/-! ### Asymptotically Euclidean ends -/

variable (I) in
/-- `φ` is an **asymptotically Euclidean end** of order `t` of `M`, parametrized by the exterior
`{x | R < ‖x‖}` of the closed ball of radius `R > 0` in `EuclideanSpace ℝ (Fin n)` with `n > 0`,
so that this exterior is nonempty: on that open set `φ` is smooth and injective with invertible
differential, the pulled-back metric coefficients `g_ij` are `C²`, and for some constant `C` the
derivatives of order `k ≤ 2` of the entries `g_ij - δ_ij` of `g - 1` are bounded by
`C ‖x‖^(-t-k)`.

Only the decay of the metric is asked for; integrability of the scalar curvature, needed for the
mass to exist, is a separate hypothesis. The `C²` regularity of the coefficients is automatic for a
smooth metric, and is asked for since a `RiemannianBundle` alone carries no regularity. The values
of `φ` on the closed ball are irrelevant. -/
structure IsAsymptoticallyEuclideanEnd (t R : ℝ) (φ : EuclideanSpace ℝ (Fin n) → M) : Prop where
  /-- The radius of the excised ball is positive. -/
  radius_pos : 0 < R
  /-- The dimension of the parametrizing space is positive, so the exterior of the ball is
  nonempty. -/
  dim_pos : 0 < n
  /-- The parametrization is smooth on the exterior of the ball. -/
  contMDiffOn : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ φ (closedBall 0 R)ᶜ
  /-- The parametrization is injective on the exterior of the ball. -/
  injOn : InjOn φ (closedBall 0 R)ᶜ
  /-- The differential of the parametrization is invertible on the exterior of the ball. -/
  isInvertible_mfderiv (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ (closedBall 0 R)ᶜ) :
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ x).IsInvertible
  /-- The pulled-back metric coefficients are twice continuously differentiable on the exterior
  of the ball. -/
  contDiffOn_pullbackMetricCoeff (i j : Fin n) :
    ContDiffOn ℝ 2 (pullbackMetricCoeff I φ · i j) (closedBall 0 R)ᶜ
  /-- The derivatives of order `k ≤ 2` of `g_ij - δ_ij` decay like `‖x‖^(-t-k)`. -/
  exists_norm_iteratedFDeriv_le : ∃ C : ℝ, ∀ k ≤ 2, ∀ (i j : Fin n),
    ∀ x ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ, ‖iteratedFDeriv ℝ k
      (fun y ↦ (pullbackMetricCoeff I φ y - 1) i j) x‖ ≤
        C * ‖x‖ ^ (-t - k)

namespace IsAsymptoticallyEuclideanEnd

variable {t R : ℝ} {φ : EuclideanSpace ℝ (Fin n) → M}

/-- An end parametrized by the exterior of a ball is also an end on the exterior of every larger
ball. -/
theorem mono_radius (h : IsAsymptoticallyEuclideanEnd I t R φ) {R' : ℝ} (hR : R ≤ R') :
    IsAsymptoticallyEuclideanEnd I t R' φ := by
  have hsub : (closedBall (0 : EuclideanSpace ℝ (Fin n)) R')ᶜ ⊆ (closedBall 0 R)ᶜ :=
    compl_subset_compl.2 (closedBall_subset_closedBall hR)
  obtain ⟨C, hC⟩ := h.exists_norm_iteratedFDeriv_le
  exact
    { radius_pos := h.radius_pos.trans_le hR
      dim_pos := h.dim_pos
      contMDiffOn := h.contMDiffOn.mono hsub
      injOn := h.injOn.mono hsub
      isInvertible_mfderiv := fun x hx ↦ h.isInvertible_mfderiv x (hsub hx)
      contDiffOn_pullbackMetricCoeff := fun i j ↦ (h.contDiffOn_pullbackMetricCoeff i j).mono hsub
      exists_norm_iteratedFDeriv_le :=
        ⟨C, fun k hk i j x hx ↦ hC k hk i j x (hsub hx)⟩ }

/-- An end of order `t` is an end of every smaller order. -/
theorem mono_order (h : IsAsymptoticallyEuclideanEnd I t R φ) {t' : ℝ} (ht : t' ≤ t) :
    IsAsymptoticallyEuclideanEnd I t' R φ := by
  obtain ⟨C, hC⟩ := h.exists_norm_iteratedFDeriv_le
  refine
    { h with
      exists_norm_iteratedFDeriv_le := ⟨|C| * R ^ (t' - t), fun k hk i j x hx ↦ ?_⟩ }
  have hxR : R < ‖x‖ := by simpa using hx
  have hx0 : 0 < ‖x‖ := h.radius_pos.trans hxR
  -- Split `‖x‖^(-t-k)` as `‖x‖^(t'-t) ‖x‖^(-t'-k)` and bound the first factor by `R^(t'-t)`.
  calc _ ≤ C * ‖x‖ ^ (-t - k) := hC k hk i j x hx
    _ ≤ |C| * (‖x‖ ^ (t' - t) * ‖x‖ ^ (-t' - k)) := by
      rw [← Real.rpow_add hx0, show t' - t + (-t' - k) = -t - k by ring]
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hx0.le _)
    _ ≤ |C| * (R ^ (t' - t) * ‖x‖ ^ (-t' - k)) := by
      gcongr ?_ * (?_ * _)
      exact Real.rpow_le_rpow_of_nonpos h.radius_pos hxR.le (sub_nonpos.2 ht)
    _ = |C| * R ^ (t' - t) * ‖x‖ ^ (-t' - k) := (mul_assoc _ _ _).symm

/-- The metric coefficients of an end are differentiable at infinity. -/
theorem eventually_differentiableAt_pullbackMetricCoeff (h : IsAsymptoticallyEuclideanEnd I t R φ) :
    ∀ᶠ x in Bornology.cobounded _, ∀ i j,
      DifferentiableAt ℝ (fun y ↦ pullbackMetricCoeff I φ y i j) x := by
  filter_upwards [(tendsto_norm_cobounded_atTop.eventually_gt_atTop R)] with x hx i j
  exact ((h.contDiffOn_pullbackMetricCoeff i j).contDiffAt
    (isClosed_closedBall.isOpen_compl.mem_nhds (by simpa using hx))).differentiableAt
      (by norm_num)

/-- The image of an end is nonempty, since the exterior of a ball in positive dimension is. -/
theorem nonempty_image (h : IsAsymptoticallyEuclideanEnd I t R φ) :
    (φ '' (closedBall 0 R)ᶜ).Nonempty := by
  have : Nonempty (Fin n) := ⟨⟨0, h.dim_pos⟩⟩
  obtain ⟨x, hx⟩ := NormedSpace.exists_lt_norm ℝ (EuclideanSpace ℝ (Fin n)) R
  exact ⟨φ x, x, by simpa using hx, rfl⟩

/-- Every point of `M` lies outside the image of the exterior of all large balls: by injectivity
of the end, a point `φ z` of its image is not the image of a point outside the ball of radius
`‖z‖`. -/
theorem eventually_notMem_image_compl_closedBall (h : IsAsymptoticallyEuclideanEnd I t R φ)
    (p : M) : ∀ᶠ a in atTop, p ∉ φ '' (closedBall 0 a)ᶜ := by
  by_cases hp : p ∈ φ '' (closedBall 0 R)ᶜ
  · obtain ⟨z, hz, rfl⟩ := hp
    filter_upwards [eventually_ge_atTop ‖z‖] with a ha ⟨y, hy, hyz⟩
    simp only [mem_compl_iff, mem_closedBall_zero_iff, not_le] at hy hz
    have hyR : y ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ := by
      simpa using hz.trans (ha.trans_lt hy)
    rw [h.injOn hyR (by simpa using hz) hyz] at hy
    linarith
  · filter_upwards [eventually_ge_atTop R] with a ha
    exact fun hpa ↦ hp (image_mono (compl_subset_compl.2 (closedBall_subset_closedBall ha)) hpa)

/-- An end is a local diffeomorphism on the exterior of its ball, by the inverse function
theorem. -/
theorem isLocalDiffeomorphOn [IsManifold I ∞ M] (h : IsAsymptoticallyEuclideanEnd I t R φ) :
    IsLocalDiffeomorphOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ φ (closedBall 0 R)ᶜ := by
  rintro ⟨x, hx⟩
  obtain ⟨e, he⟩ := h.isInvertible_mfderiv x hx
  exact isLocalDiffeomorphAt_of_mfderiv_eq h.contMDiffOn isClosed_closedBall.isOpen_compl hx
    BoundarylessManifold.isInteriorPoint (by simp) he

/-- The image of an open subset of the exterior of the ball of an end is open. -/
theorem isOpen_image_of_subset [IsManifold I ∞ M] (h : IsAsymptoticallyEuclideanEnd I t R φ)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hUR : U ⊆ (closedBall 0 R)ᶜ) :
    IsOpen (φ '' U) :=
  (h.isLocalDiffeomorphOn.isLocalHomeomorphOn.mono hUR).isOpen_image hU

/-- The image of an end is open. -/
theorem isOpen_image [IsManifold I ∞ M] (h : IsAsymptoticallyEuclideanEnd I t R φ) :
    IsOpen (φ '' (closedBall 0 R)ᶜ) :=
  h.isOpen_image_of_subset isClosed_closedBall.isOpen_compl subset_rfl

/-- An end as a diffeomorphism from the exterior of its ball onto its open image. -/
def toPartialDiffeomorph [IsManifold I ∞ M] (h : IsAsymptoticallyEuclideanEnd I t R φ) :
    PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I (EuclideanSpace ℝ (Fin n)) M ∞ :=
  h.isLocalDiffeomorphOn.partialDiffeomorphOfInjOn isClosed_closedBall.isOpen_compl h.injOn

/-- The source of an end, as a partial diffeomorphism, is the exterior of its ball. -/
@[simp]
theorem toPartialDiffeomorph_source [IsManifold I ∞ M]
    (h : IsAsymptoticallyEuclideanEnd I t R φ) :
    h.toPartialDiffeomorph.source = (closedBall 0 R)ᶜ :=
  h.isLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source _ _

/-- The target of an end, as a partial diffeomorphism, is its image. -/
@[simp]
theorem toPartialDiffeomorph_target [IsManifold I ∞ M]
    (h : IsAsymptoticallyEuclideanEnd I t R φ) :
    h.toPartialDiffeomorph.target = φ '' (closedBall 0 R)ᶜ :=
  h.isLocalDiffeomorphOn.partialDiffeomorphOfInjOn_target _ _

/-- An end, as a partial diffeomorphism, evaluates as its parametrization. -/
@[simp]
theorem coe_toPartialDiffeomorph [IsManifold I ∞ M]
    (h : IsAsymptoticallyEuclideanEnd I t R φ) : ⇑h.toPartialDiffeomorph = φ :=
  h.isLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn _ _

/-- The inverse of an end, as a partial diffeomorphism, undoes the end on the exterior of its
ball. -/
theorem toPartialDiffeomorph_symm_apply_apply [IsManifold I ∞ M]
    (h : IsAsymptoticallyEuclideanEnd I t R φ) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (closedBall 0 R)ᶜ) : h.toPartialDiffeomorph.symm (φ y) = y := by
  simpa using h.toPartialDiffeomorph.left_inv (x := y) (by simpa using hy)

private theorem isLocalDiffeomorphOn_one [IsManifold I 1 M]
    (h : IsAsymptoticallyEuclideanEnd I t R φ) :
    IsLocalDiffeomorphOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I 1 φ (closedBall 0 R)ᶜ := by
  rintro ⟨x, hx⟩
  obtain ⟨_, he⟩ := h.isInvertible_mfderiv x hx
  exact isLocalDiffeomorphAt_of_mfderiv_eq (h.contMDiffOn.of_le (by simp))
    isClosed_closedBall.isOpen_compl hx BoundarylessManifold.isInteriorPoint le_rfl he

/-- On a `C¹` manifold, an end restricts to a homeomorphism from the coordinate exterior
`(closedBall 0 R)ᶜ` onto its image `φ '' (closedBall 0 R)ᶜ`. -/
def homeomorphImage [IsManifold I 1 M] (h : IsAsymptoticallyEuclideanEnd I t R φ) :
    ((closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ : Set (EuclideanSpace ℝ (Fin n))) ≃ₜ
      (φ '' (closedBall 0 R)ᶜ) :=
  (h.isLocalDiffeomorphOn_one.partialDiffeomorphOfInjOn isClosed_closedBall.isOpen_compl
    h.injOn).toOpenPartialHomeomorph.homeomorphOfImageSubsetSource
    (by simp) (by simp)

/-- Forward evaluation of `TauCeti.IsAsymptoticallyEuclideanEnd.homeomorphImage`. -/
@[simp]
theorem coe_homeomorphImage_apply [IsManifold I 1 M]
    (h : IsAsymptoticallyEuclideanEnd I t R φ)
    (x : ((closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ : Set (EuclideanSpace ℝ (Fin n)))) :
    (h.homeomorphImage x : M) = φ x.val := by
  simp [homeomorphImage]

/-- Inverse evaluation of `TauCeti.IsAsymptoticallyEuclideanEnd.homeomorphImage`. -/
@[simp]
theorem coe_homeomorphImage_symm_apply [IsManifold I 1 M]
    (h : IsAsymptoticallyEuclideanEnd I t R φ) (p : φ '' (closedBall 0 R)ᶜ) :
    (h.homeomorphImage.symm p : EuclideanSpace ℝ (Fin n)) =
      invFunOn φ (closedBall 0 R)ᶜ p.val := by
  simp [homeomorphImage]

/-- On a `C¹` manifold, the coordinate radius `‖φ⁻¹(p)‖` on the image of an asymptotically
Euclidean end, taking values in `Set.Ioi R`. -/
def endRadius [IsManifold I 1 M] (h : IsAsymptoticallyEuclideanEnd I t R φ)
    (p : φ '' (closedBall 0 R)ᶜ) : Ioi R :=
  ⟨‖(h.homeomorphImage.symm p).val‖,
    not_le.mp (mem_closedBall_zero_iff.not.mp (h.homeomorphImage.symm p).property)⟩

/-- Coercion of `TauCeti.IsAsymptoticallyEuclideanEnd.endRadius` to `ℝ`. Not tagged `@[simp]` so
that `coe_endRadius_image_mk` simplifies `(h.endRadius ⟨φ x, _⟩ : ℝ)` directly to `‖x‖` without
unfolding to `invFunOn`. -/
theorem coe_endRadius [IsManifold I 1 M] (h : IsAsymptoticallyEuclideanEnd I t R φ)
    (p : φ '' (closedBall 0 R)ᶜ) :
    (h.endRadius p : ℝ) = ‖invFunOn φ (closedBall 0 R)ᶜ p.val‖ :=
  congrArg norm (h.coe_homeomorphImage_symm_apply p)

/-- Evaluating `h.endRadius` at `φ x` for `x ∈ (closedBall 0 R)ᶜ` recovers `‖x‖`. -/
@[simp]
theorem coe_endRadius_image_mk [IsManifold I 1 M] (h : IsAsymptoticallyEuclideanEnd I t R φ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ (closedBall 0 R)ᶜ) :
    (h.endRadius ⟨φ x, mem_image_of_mem φ hx⟩ : ℝ) = ‖x‖ := by
  rw [coe_endRadius, h.injOn.leftInvOn_invFunOn hx]

/-- **Properness of the end radius.** On a `C¹` manifold, the coordinate radius
`h.endRadius : φ '' (closedBall 0 R)ᶜ → Set.Ioi R` is a proper map. -/
theorem isProperMap_endRadius [IsManifold I 1 M] (h : IsAsymptoticallyEuclideanEnd I t R φ) :
    IsProperMap h.endRadius := by
  have hnorm : IsProperMap (norm : EuclideanSpace ℝ (Fin n) → ℝ) := by
    simpa only [dist_zero] using isProperMap_dist (0 : EuclideanSpace ℝ (Fin n))
  have heq : h.endRadius =
      ((Ioi R).restrictPreimage (norm : EuclideanSpace ℝ (Fin n) → ℝ) ∘
        Homeomorph.setCongr (by ext y; simp)) ∘ h.homeomorphImage.symm := by
    ext p
    simp [endRadius, Set.restrictPreimage, Homeomorph.setCongr]
  exact heq ▸ ((hnorm.restrictPreimage (Ioi R)).comp (Homeomorph.setCongr _).isProperMap).comp
    h.homeomorphImage.symm.isProperMap

/-- In dimension at least two the image of an end is path-connected, as the image of the
path-connected exterior of a ball. -/
theorem isPathConnected_image (h : IsAsymptoticallyEuclideanEnd I t R φ) (hn : 1 < n) :
    IsPathConnected (φ '' (closedBall 0 R)ᶜ) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast hn
  exact (isPathConnected_compl_closedBall hrank 0 R).image' h.contMDiffOn.continuousOn

/-- Composing an end with a local Riemannian isometry that is injective on its image gives an end
of the same order. -/
theorem comp {f : M → N} (hf : IsLocalRiemannianIsometry I J f)
    (hinj : InjOn f (φ '' (closedBall 0 R)ᶜ)) (h : IsAsymptoticallyEuclideanEnd I t R φ) :
    IsAsymptoticallyEuclideanEnd J t R (f ∘ φ) := by
  have hopen : IsOpen (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ :=
    isClosed_closedBall.isOpen_compl
  have hdiff (x) (hx : x ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ) :
      MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ x :=
    (h.contMDiffOn.contMDiffAt (hopen.mem_nhds hx)).mdifferentiableAt (by simp)
  -- The coefficients of `f ∘ φ` and of `φ` agree on the open exterior, hence near each of its
  -- points.
  have hcoeff : EqOn (pullbackMetricCoeff J (f ∘ φ)) (pullbackMetricCoeff I φ) (closedBall 0 R)ᶜ :=
    fun x hx ↦ pullbackMetricCoeff_comp hf (hdiff x hx)
  obtain ⟨C, hC⟩ := h.exists_norm_iteratedFDeriv_le
  refine
    { radius_pos := h.radius_pos
      dim_pos := h.dim_pos
      contMDiffOn := hf.contMDiff.comp_contMDiffOn h.contMDiffOn
      injOn := hinj.comp h.injOn (mapsTo_image _ _)
      isInvertible_mfderiv := fun x hx ↦ ?_
      contDiffOn_pullbackMetricCoeff := fun i j ↦
        (h.contDiffOn_pullbackMetricCoeff i j).congr fun _ hy ↦
          congrArg (fun A : Matrix (Fin n) (Fin n) ℝ ↦ A i j) (hcoeff hy)
      exists_norm_iteratedFDeriv_le := ⟨C, fun k hk i j x hx ↦ ?_⟩ }
  · rw [mfderiv_comp x (hf.mdifferentiableAt (φ x)) (hdiff x hx)]
    exact (hf.isInvertible_mfderiv (φ x)).comp (h.isInvertible_mfderiv x hx)
  · have hev : (fun y ↦ (pullbackMetricCoeff J (f ∘ φ) y - 1) i j) =ᶠ[𝓝 x]
        fun y ↦ (pullbackMetricCoeff I φ y - 1) i j := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact congrArg (fun A : Matrix (Fin n) (Fin n) ℝ ↦ (A - 1) i j) (hcoeff hy)
    rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
    exact hC k hk i j x hx

end IsAsymptoticallyEuclideanEnd

/-- Composing with a Riemannian isometry neither creates nor destroys asymptotically Euclidean
ends. -/
theorem isAsymptoticallyEuclideanEnd_comp_iff (Φ : RiemannianIsometry I J M N) {t R : ℝ}
    {φ : EuclideanSpace ℝ (Fin n) → M} :
    IsAsymptoticallyEuclideanEnd J t R (Φ ∘ φ) ↔ IsAsymptoticallyEuclideanEnd I t R φ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp Φ.isLocalRiemannianIsometry Φ.injective.injOn⟩
  have h' := h.comp Φ.symm.isLocalRiemannianIsometry Φ.symm.injective.injOn
  rwa [← comp_assoc, Φ.symm_comp_self, id_comp] at h'

/-- The identity parametrization of flat Euclidean space is an asymptotically Euclidean end of
every order on the exterior of every ball, in positive dimension: its coefficients are exactly
`δ_ij`. -/
theorem isAsymptoticallyEuclideanEnd_id (hn : 0 < n) (t : ℝ) {R : ℝ} (hR : 0 < R) :
    IsAsymptoticallyEuclideanEnd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) t R
      (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) where
  radius_pos := hR
  dim_pos := hn
  contMDiffOn := contMDiffOn_id
  injOn := injOn_id _
  isInvertible_mfderiv x _ := by
    rw [mfderiv_id]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  contDiffOn_pullbackMetricCoeff i j := by
    simpa only [pullbackMetricCoeff_id] using contDiffOn_const
  exists_norm_iteratedFDeriv_le := ⟨0, fun k _ i j x _ ↦ by
    simp only [pullbackMetricCoeff_id, sub_self, Matrix.zero_apply, zero_mul]
    rw [← Pi.zero_def, iteratedFDeriv_zero]
    simp⟩

/-- A non-isometric homothety `x ↦ c • x` (`|c| ≠ 1`) of flat Euclidean space is not an
asymptotically Euclidean end of any positive order: its pulled-back coefficients `c ^ 2 δ_ij` have
`g_ii - 1 = c ^ 2 - 1 ≠ 0`, which does not decay. -/
theorem not_isAsymptoticallyEuclideanEnd_smul {t : ℝ} (ht : 0 < t) {c : ℝ} (hc : |c| ≠ 1)
    (R : ℝ) :
    ¬ IsAsymptoticallyEuclideanEnd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) t R
      (fun y : EuclideanSpace ℝ (Fin n) ↦ c • y) := by
  intro h
  obtain ⟨C, hC⟩ := h.exists_norm_iteratedFDeriv_le
  let i : Fin n := ⟨0, h.dim_pos⟩
  have hd_pos : 0 < |c ^ 2 - 1| := by
    rw [abs_pos, sub_ne_zero, ne_eq, sq_eq_one_iff]
    rintro (rfl | rfl) <;> simp at hc
  -- For large `s`, the point `s • eᵢ` lies outside the ball and `C s^(-t) < |c ^ 2 - 1|`.
  obtain ⟨s, hsR, hs0, hsC⟩ := (eventually_gt_atTop R).and ((eventually_gt_atTop 0).and
    (((tendsto_rpow_neg_atTop ht).const_mul C).eventually
      (gt_mem_nhds (by simpa only [mul_zero] using hd_pos)))) |>.exists
  have hnorm : ‖s • EuclideanSpace.basisFun (Fin n) ℝ i‖ = s := by
    rw [norm_smul, (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.left i, mul_one,
      Real.norm_of_nonneg hs0.le]
  have h0 := hC 0 (by norm_num) i i (s • EuclideanSpace.basisFun (Fin n) ℝ i)
    (by rwa [mem_compl_iff, mem_closedBall_zero_iff, not_le, hnorm])
  have hcoeff : pullbackMetricCoeff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (fun y : EuclideanSpace ℝ (Fin n) ↦ c • y)
      (s • EuclideanSpace.basisFun (Fin n) ℝ i) i i = c ^ 2 := by
    simpa using congrArg (fun A : Matrix (Fin n) (Fin n) ℝ ↦ A i i)
      (pullbackMetricCoeff_const_smul c (id : EuclideanSpace ℝ (Fin n) → _)
        (s • EuclideanSpace.basisFun (Fin n) ℝ i))
  simp only [norm_iteratedFDeriv_zero, Matrix.sub_apply, hcoeff, Matrix.one_apply, ↓reduceIte,
    Real.norm_eq_abs, hnorm, Nat.cast_zero, sub_zero] at h0
  exact (not_lt_of_ge h0) hsC

/-- The dilation `x ↦ 2 • x` of flat Euclidean space is not an asymptotically Euclidean end of
any positive order: its coefficients `4 δ_ij` are bounded, but `g_ii - 1 = 3` does not
decay. -/
theorem not_isAsymptoticallyEuclideanEnd_two_smul {t : ℝ} (ht : 0 < t) (R : ℝ) :
    ¬ IsAsymptoticallyEuclideanEnd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) t R
      (fun y : EuclideanSpace ℝ (Fin n) ↦ (2 : ℝ) • y) :=
  not_isAsymptoticallyEuclideanEnd_smul ht (by norm_num) R

/-! ### Finite-ended asymptotically Euclidean manifolds -/

variable (I) in
/-- `M` is **finite-ended asymptotically Euclidean** of order `t` with the ends `φ e`, indexed by
a finite nonempty type, on the exteriors of the balls of radii `R e`: each `φ e` is an
asymptotically Euclidean end of order `t`, their images are pairwise disjoint, and the complement
of the union of their images is compact. -/
structure IsFiniteEndedAsymptoticallyEuclidean {ι : Type*} (t : ℝ) (R : ι → ℝ)
    (φ : ι → EuclideanSpace ℝ (Fin n) → M) : Prop where
  /-- There are finitely many ends. -/
  finite : Finite ι
  /-- There is at least one end. -/
  nonempty : Nonempty ι
  /-- Each parametrization is an asymptotically Euclidean end of order `t`. -/
  isAsymptoticallyEuclideanEnd (e : ι) : IsAsymptoticallyEuclideanEnd I t (R e) (φ e)
  /-- The images of distinct ends are disjoint. -/
  pairwise_disjoint :
    Pairwise fun e e' ↦ Disjoint (φ e '' (closedBall 0 (R e))ᶜ) (φ e' '' (closedBall 0 (R e'))ᶜ)
  /-- The complement of the union of the images of the ends is compact. -/
  isCompact_compl_iUnion : IsCompact (⋃ e, φ e '' (closedBall 0 (R e))ᶜ)ᶜ

namespace IsFiniteEndedAsymptoticallyEuclidean

variable {ι : Type*} {t : ℝ} {R : ι → ℝ} {φ : ι → EuclideanSpace ℝ (Fin n) → M}

/-- A finite-ended structure of order `t` is one of every smaller order. -/
theorem mono_order (h : IsFiniteEndedAsymptoticallyEuclidean I t R φ) {t' : ℝ} (ht : t' ≤ t) :
    IsFiniteEndedAsymptoticallyEuclidean I t' R φ :=
  { h with
    isAsymptoticallyEuclideanEnd := fun e ↦ (h.isAsymptoticallyEuclideanEnd e).mono_order ht }

/-- Composing every end with a Riemannian isometry gives a finite-ended structure of the same
order on the target. -/
theorem comp (Φ : RiemannianIsometry I J M N) (h : IsFiniteEndedAsymptoticallyEuclidean I t R φ) :
    IsFiniteEndedAsymptoticallyEuclidean J t R (fun e ↦ Φ ∘ φ e) where
  finite := h.finite
  nonempty := h.nonempty
  isAsymptoticallyEuclideanEnd e := (isAsymptoticallyEuclideanEnd_comp_iff Φ).2
    (h.isAsymptoticallyEuclideanEnd e)
  pairwise_disjoint e e' hee' := by
    simp only [image_comp]
    exact (disjoint_image_iff (EquivLike.injective Φ)).2 (h.pairwise_disjoint hee')
  isCompact_compl_iUnion := by
    rw [show (⋃ e, (Φ ∘ φ e) '' (closedBall 0 (R e))ᶜ) =
        Φ '' ⋃ e, φ e '' (closedBall 0 (R e))ᶜ by simp only [image_comp, image_iUnion],
      ← image_compl_eq (EquivLike.bijective Φ)]
    exact h.isCompact_compl_iUnion.image Φ.mdifferentiable.continuous

end IsFiniteEndedAsymptoticallyEuclidean

/-- Composing every end with a Riemannian isometry neither creates nor destroys finite-ended
asymptotically Euclidean structures. -/
theorem isFiniteEndedAsymptoticallyEuclidean_comp_iff (Φ : RiemannianIsometry I J M N) {ι : Type*}
    {t : ℝ} {R : ι → ℝ} {φ : ι → EuclideanSpace ℝ (Fin n) → M} :
    IsFiniteEndedAsymptoticallyEuclidean J t R (fun e ↦ Φ ∘ φ e) ↔
      IsFiniteEndedAsymptoticallyEuclidean I t R φ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp Φ⟩
  have h' := h.comp Φ.symm
  simp only [← comp_assoc, Φ.symm_comp_self, id_comp] at h'
  exact h'

/-- Flat Euclidean space of positive dimension, with the identity parametrization of the exterior
of a ball of positive radius as its only end, is finite-ended asymptotically Euclidean of every
order. -/
theorem isFiniteEndedAsymptoticallyEuclidean_id (hn : 0 < n) (t : ℝ) {R : ℝ} (hR : 0 < R) :
    IsFiniteEndedAsymptoticallyEuclidean 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) t (fun _ : Unit ↦ R)
      (fun _ ↦ (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))) where
  finite := inferInstance
  nonempty := inferInstance
  isAsymptoticallyEuclideanEnd _ := isAsymptoticallyEuclideanEnd_id hn t hR
  pairwise_disjoint e e' hee' := (hee' (Subsingleton.elim e e')).elim
  isCompact_compl_iUnion := by
    simpa only [iUnion_const, image_id, compl_compl] using isCompact_closedBall 0 R

end TauCeti
