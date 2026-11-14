/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Topology.Maps.Proper.Basic

import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import TauCeti.Analysis.Normed.Module.Ball.Exterior
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Opens
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace

/-!
# Asymptotically Euclidean ends and finite-ended structures

An *asymptotically Euclidean (AE) end* of order `t` on a Riemannian `n`-manifold `M` is a smooth
injective parametrization of an open subset of `M` by the coordinate exterior
`{x ∈ ℝⁿ : R < ‖x‖}` of a closed ball (`0 < R`), with bijective differential on that exterior, in
which the pullback metric coefficients `g_ij(x) = ⟨dφ_x e_i, dφ_x e_j⟩` decay to `δ_ij` at rate
`‖x‖ ^ (-t)` together with their first two Euclidean derivatives at rates `‖x‖ ^ (-t - 1)` and
`‖x‖ ^ (-t - 2)`. Following Lee–Parker and decoupling the analytic hypotheses of Cecchini–Zeidler,
integrability of the scalar curvature on the end is kept separate from `AsymptoticallyEuclideanEnd`
so that coordinate flux computations and geometric constructions apply without curvature
integrability assumptions.

An end stores its parametrization on the open submanifold `exteriorOpen n radius`, making
`AsymptoticallyEuclideanEnd` extensional (`@[ext]`). Its coordinate metric coefficients
`AsymptoticallyEuclideanEnd.metricCoeff` extend canonically by `0` on `{x : ‖x‖ ≤ radius}` and
agree near every exterior point with `pullbackMetricCoeff φ` for any ambient extension `φ : ℝⁿ → M`.
A *finite-ended asymptotically Euclidean structure* `FiniteEndedAE n M t` is a finite nonempty
family of pairwise disjoint AE ends whose union has compact complement in `M`.

## Main definitions

* `TauCeti.exteriorOpen`: the open submanifold `{x ∈ ℝⁿ : R < ‖x‖}` of `EuclideanSpace ℝ (Fin n)`.
* `TauCeti.pullbackMetricCoeff` and `TauCeti.exteriorMetricCoeff`: coordinate metric coefficients
  `g_ij` for ambient maps `ℝⁿ → M` and exterior maps `exteriorOpen n R → M`.
* `TauCeti.AsymptoticallyEuclideanEnd`: an AE end of `M` of order `t`, with constructors `ofFun`
  and `ofIsManifold`, order monotonicity `ofLE`, and radius restriction `restrictRadius`.
* `TauCeti.AsymptoticallyEuclideanEnd.diffeomorphImage` and `endRadius`: on a smooth manifold `M`,
  the smooth diffeomorphism onto the open image of an AE end and its proper coordinate radius.
* `TauCeti.FiniteEndedAE`: a finite nonempty family of pairwise disjoint AE ends with compact
  complement, witnessed on flat space by `FiniteEndedAE.euclideanSpace`.

## Main results

* `TauCeti.AsymptoticallyEuclideanEnd.isPathConnected_image` and `isConnected_image`: for `2 ≤ n`,
  the image of an AE end is path-connected and connected.
* `TauCeti.AsymptoticallyEuclideanEnd.isProperMap_endRadius` and `isCompact_image_annulus`:
  properness of the coordinate radius and compactness of closed coordinate annuli in `M`.
* `TauCeti.not_exists_asymptoticallyEuclideanEnd_smul`: for `1 ≤ n`, `0 < t`, and `|c| ≠ 1`, the
  rescaled parametrization `x ↦ c • x` of flat `ℝⁿ` is not an AE end of order `t`.

## References

* S. Cecchini, R. Zeidler, *Scalar and mean curvature comparison via the Dirac operator*,
  Geom. Topol. 28 (2024), 1167–1212, §2 (Definitions 2.1 and 2.3).
* J. M. Lee, T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. (N.S.) 17 (1987), 37–91,
  §§8–9.
-/

public section

noncomputable section

open Set Function Filter Metric TopologicalSpace Bundle
open scoped Topology Manifold ContDiff RealInnerProductSpace

namespace TauCeti

/-! ### Coordinate exteriors -/

/-- The open exterior `{x ∈ ℝⁿ : R < ‖x‖}` of the closed coordinate ball of radius `R`, viewed as
an open submanifold of `EuclideanSpace ℝ (Fin n)`. -/
def exteriorOpen (n : ℕ) (R : ℝ) : Opens (EuclideanSpace ℝ (Fin n)) :=
  ⟨{x | R < ‖x‖}, isOpen_lt continuous_const continuous_norm⟩

@[simp] theorem coe_exteriorOpen (n : ℕ) (R : ℝ) :
    (exteriorOpen n R : Set (EuclideanSpace ℝ (Fin n))) = {x | R < ‖x‖} := (rfl)

@[simp] theorem mem_exteriorOpen {n : ℕ} {R : ℝ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ exteriorOpen n R ↔ R < ‖x‖ := Iff.rfl

/-- The exterior `exteriorOpen n R` is the complement of the closed ball of radius `R` at `0`. -/
theorem coe_exteriorOpen_eq_compl_closedBall (n : ℕ) (R : ℝ) :
    (exteriorOpen n R : Set (EuclideanSpace ℝ (Fin n))) = (closedBall 0 R)ᶜ := by
  ext x; simp [dist_zero_right]

/-- Every point of `exteriorOpen n R` for `0 ≤ R` is nonzero. -/
theorem exteriorOpen_coe_ne_zero {n : ℕ} {R : ℝ} (hR : 0 ≤ R) (x : exteriorOpen n R) :
    (x : EuclideanSpace ℝ (Fin n)) ≠ 0 :=
  norm_pos_iff.mp (hR.trans_lt (mem_exteriorOpen.mp x.2))

/-- In positive dimension, `exteriorOpen n R` is nonempty for every `R`. -/
theorem exteriorOpen_nonempty {n : ℕ} (hn : 1 ≤ n) (R : ℝ) :
    (exteriorOpen n R : Set (EuclideanSpace ℝ (Fin n))).Nonempty := by
  let r := max R 0 + 1
  have hr0 : 0 < r := by positivity
  let e₀ : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hn⟩ 1
  have he₀ : ‖e₀‖ = 1 := by simp [e₀]
  refine ⟨r • e₀, mem_exteriorOpen.mpr ?_⟩
  rw [norm_smul, Real.norm_of_nonneg hr0.le, he₀, mul_one]
  exact lt_of_le_of_lt (le_max_left R 0) (lt_add_one _)

/-- In dimension at least `2`, `exteriorOpen n R` is path-connected. -/
theorem isPathConnected_exteriorOpen {n : ℕ} (hn : 2 ≤ n) (R : ℝ) :
    IsPathConnected (exteriorOpen n R : Set (EuclideanSpace ℝ (Fin n))) := by
  rw [coe_exteriorOpen_eq_compl_closedBall]
  refine isPathConnected_compl_closedBall ?_ 0 R
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  exact_mod_cast hn

/-- In dimension at least `2`, `exteriorOpen n R` is connected. -/
theorem isConnected_exteriorOpen {n : ℕ} (hn : 2 ≤ n) (R : ℝ) :
    IsConnected (exteriorOpen n R : Set (EuclideanSpace ℝ (Fin n))) :=
  (isPathConnected_exteriorOpen hn R).isConnected

/-- The coordinate norm map `x ↦ ⟨‖x‖, ...⟩` from `exteriorOpen n R` to `Set.Ioi R` is proper. -/
theorem isProperMap_exteriorOpen_norm {n : ℕ} {R : ℝ} :
    IsProperMap (fun x : exteriorOpen n R =>
      (⟨‖(x : EuclideanSpace ℝ (Fin n))‖, mem_exteriorOpen.mp x.2⟩ : Ioi R)) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨by fun_prop, fun K hK => ?_⟩
  set K' : Set ℝ := Subtype.val '' K
  have hK' : IsCompact K' := hK.image continuous_subtype_val
  have hK'_sub : K' ⊆ Ioi R := by rintro _ ⟨r, -, rfl⟩; exact r.2
  set A : Set (EuclideanSpace ℝ (Fin n)) := norm ⁻¹' K'
  have hA_bdd : Bornology.IsBounded A := by
    obtain ⟨B, hB⟩ := hK'.isBounded.subset_closedBall 0
    rw [isBounded_iff_subset_closedBall 0]
    exact ⟨B, fun x hx => mem_closedBall_zero_iff.mpr
      ((le_abs_self ‖x‖).trans (mem_closedBall_zero_iff.mp (hB hx)))⟩
  have hA_compact : IsCompact A :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hK'.isClosed.preimage continuous_norm, hA_bdd⟩
  let liftA : A → exteriorOpen n R := fun x => ⟨x.1, mem_exteriorOpen.mpr (hK'_sub x.2)⟩
  have hrange : range liftA =
      (fun x : exteriorOpen n R =>
        (⟨‖(x : EuclideanSpace ℝ (Fin n))‖, mem_exteriorOpen.mp x.2⟩ : Ioi R)) ⁻¹' K := by
    ext x
    simp only [mem_range, mem_preimage, liftA, A, K']
    constructor
    · rintro ⟨⟨y, hy⟩, hxy⟩
      obtain rfl : y = x.1 := congrArg Subtype.val hxy
      obtain ⟨r, hrK, hrval⟩ := hy
      exact (Subtype.ext hrval : r = ⟨‖(x : EuclideanSpace ℝ (Fin n))‖, _⟩) ▸ hrK
    · intro hxK
      exact ⟨⟨x.1, ⟨⟨‖(x : EuclideanSpace ℝ (Fin n))‖, mem_exteriorOpen.mp x.2⟩, hxK, rfl⟩⟩, rfl⟩
  rw [← hrange]
  have : CompactSpace A := isCompact_iff_compactSpace.mp hA_compact
  exact isCompact_range (by fun_prop)

/-! ### Pullback metric coefficients -/

section MetricCoeff

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)]

/-- The coefficients `g_ij(x) = ⟨dφ_x e_i, dφ_x e_j⟩` of the Riemannian metric of `M` pulled back
along a map `φ : ℝⁿ → M`, evaluated on the standard orthonormal basis of `ℝⁿ`. -/
def pullbackMetricCoeff (φ : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) : ℝ :=
  ⟪mfderiv (𝓡 n) (𝓡 n) φ x (EuclideanSpace.basisFun (Fin n) ℝ i),
    mfderiv (𝓡 n) (𝓡 n) φ x (EuclideanSpace.basisFun (Fin n) ℝ j)⟫

theorem pullbackMetricCoeff_def (φ : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff φ x i j =
      ⟪mfderiv (𝓡 n) (𝓡 n) φ x (EuclideanSpace.basisFun (Fin n) ℝ i),
        mfderiv (𝓡 n) (𝓡 n) φ x (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ := (rfl)

/-- Pullback metric coefficients are symmetric in `i` and `j`. -/
theorem pullbackMetricCoeff_symm (φ : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff φ x i j = pullbackMetricCoeff φ x j i :=
  real_inner_comm _ _

/-- Diagonal pullback metric coefficients equal the squared norm of the pushed-forward coordinate
vector. -/
theorem pullbackMetricCoeff_diag (φ : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    pullbackMetricCoeff φ x i i =
      ‖mfderiv (𝓡 n) (𝓡 n) φ x (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2 :=
  real_inner_self_eq_norm_sq _

/-- Diagonal pullback metric coefficients are nonnegative. -/
theorem pullbackMetricCoeff_diag_nonneg (φ : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    0 ≤ pullbackMetricCoeff φ x i i := by
  rw [pullbackMetricCoeff_diag]; positivity

/-- At a point where `mfderiv` is injective, every diagonal metric coefficient is strictly
positive. -/
theorem pullbackMetricCoeff_diag_pos {φ : EuclideanSpace ℝ (Fin n) → M}
    {x : EuclideanSpace ℝ (Fin n)} (hinj : Injective (mfderiv (𝓡 n) (𝓡 n) φ x)) (i : Fin n) :
    0 < pullbackMetricCoeff φ x i i := by
  rw [pullbackMetricCoeff_diag]
  refine sq_pos_of_pos (norm_pos_iff.mpr fun h0 => ?_)
  exact (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.ne_zero i
    (hinj (h0.trans (map_zero _).symm))

/-- The Riemannian metric coefficients of a map `φ : exteriorOpen n R → M` defined on the exterior
`{x ∈ ℝⁿ : R < ‖x‖}`, extended by `0` on `{x : ‖x‖ ≤ R}`. -/
def exteriorMetricCoeff {R : ℝ} (φ : exteriorOpen n R → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) : ℝ :=
  if hx : R < ‖x‖ then
    ⟪mfderiv (𝓡 n) (𝓡 n) φ ⟨x, mem_exteriorOpen.mpr hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ i),
      mfderiv (𝓡 n) (𝓡 n) φ ⟨x, mem_exteriorOpen.mpr hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ j)⟫
  else 0

theorem exteriorMetricCoeff_def {R : ℝ} (φ : exteriorOpen n R → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    exteriorMetricCoeff φ x i j =
      if hx : R < ‖x‖ then
        ⟪mfderiv (𝓡 n) (𝓡 n) φ ⟨x, mem_exteriorOpen.mpr hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ i),
          mfderiv (𝓡 n) (𝓡 n) φ ⟨x, mem_exteriorOpen.mpr hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ j)⟫
      else 0 := (rfl)

theorem exteriorMetricCoeff_of_lt {R : ℝ} (φ : exteriorOpen n R → M)
    {x : EuclideanSpace ℝ (Fin n)} (hx : R < ‖x‖) (i j : Fin n) :
    exteriorMetricCoeff φ x i j =
      ⟪mfderiv (𝓡 n) (𝓡 n) φ ⟨x, mem_exteriorOpen.mpr hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ i),
        mfderiv (𝓡 n) (𝓡 n) φ ⟨x, mem_exteriorOpen.mpr hx⟩
          (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ :=
  dite_eq_left_of_eq_true (eq_true hx)

@[simp] theorem exteriorMetricCoeff_of_le {R : ℝ} (φ : exteriorOpen n R → M)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ R) (i j : Fin n) :
    exteriorMetricCoeff φ x i j = 0 :=
  dite_eq_right_of_eq_false (eq_false (not_lt.mpr hx))

/-- Exterior metric coefficients are symmetric in `i` and `j`. -/
theorem exteriorMetricCoeff_symm {R : ℝ} (φ : exteriorOpen n R → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    exteriorMetricCoeff φ x i j = exteriorMetricCoeff φ x j i := by
  by_cases hx : R < ‖x‖
  · rw [exteriorMetricCoeff_of_lt _ hx, exteriorMetricCoeff_of_lt _ hx, real_inner_comm]
  · rw [exteriorMetricCoeff_of_le _ (not_lt.mp hx), exteriorMetricCoeff_of_le _ (not_lt.mp hx)]

/-- Restricting an ambient map `φ : ℝⁿ → M` to `exteriorOpen n R` gives the same metric
coefficients at every point of `{x : R < ‖x‖}`. -/
@[simp] theorem exteriorMetricCoeff_comp_subtype_of_lt {R : ℝ} (φ : EuclideanSpace ℝ (Fin n) → M)
    {x : EuclideanSpace ℝ (Fin n)} (hx : R < ‖x‖) (i j : Fin n) :
    exteriorMetricCoeff (φ ∘ (Subtype.val : exteriorOpen n R → EuclideanSpace ℝ (Fin n))) x i j =
      pullbackMetricCoeff φ x i j := by
  rw [exteriorMetricCoeff_of_lt _ hx, pullbackMetricCoeff_def]
  exact congrArg₂ (inner ℝ)
    (TauCeti.Manifold.mfderiv_comp_subtype_val_apply (U := exteriorOpen n R) _)
    (TauCeti.Manifold.mfderiv_comp_subtype_val_apply (U := exteriorOpen n R) _)

/-- Near any point `x` with `R < ‖x‖`, `exteriorMetricCoeff (φ ∘ Subtype.val)` and
`pullbackMetricCoeff φ` agree on a neighbourhood of `x`. -/
theorem eventuallyEq_exteriorMetricCoeff_comp_subtype {R : ℝ} (φ : EuclideanSpace ℝ (Fin n) → M)
    {x : EuclideanSpace ℝ (Fin n)} (hx : R < ‖x‖) (i j : Fin n) :
    (fun y =>
      exteriorMetricCoeff (φ ∘ (Subtype.val : exteriorOpen n R → EuclideanSpace ℝ (Fin n))) y i j)
      =ᶠ[𝓝 x] (fun y => pullbackMetricCoeff φ y i j) := by
  filter_upwards [(exteriorOpen n R).isOpen.mem_nhds (mem_exteriorOpen.mpr hx)] with y hy
  exact exteriorMetricCoeff_comp_subtype_of_lt φ (mem_exteriorOpen.mp hy) i j

end MetricCoeff

section EuclideanMetricCoeff

/-- On flat `EuclideanSpace ℝ (Fin n)` with its standard Riemannian metric, `pullbackMetricCoeff`
agrees with the Euclidean inner product of Fréchet derivatives. -/
theorem pullbackMetricCoeff_euclideanSpace {n : ℕ}
    (φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff φ x i j =
      ⟪fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ i),
        fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ := by
  rw [pullbackMetricCoeff_def, TauCeti.Manifold.inner_tangentSpace_vectorSpace]
  have h (v : TangentSpace (𝓡 n) x) :
      NormedSpace.fromTangentSpace (φ x) (mfderiv (𝓡 n) (𝓡 n) φ x v) = fderiv ℝ φ x v := by
    rw [NormedSpace.fromTangentSpace_apply, ← mvfderiv_apply_eq_mfderiv_apply,
      TauCeti.mvfderiv_eq_fderiv_apply]
  exact congrArg₂ (inner ℝ) (h _) (h _)

/-- On flat `EuclideanSpace ℝ (Fin n)`, the identity map has Kronecker-delta metric coefficients
`δ_ij`. -/
@[simp] theorem pullbackMetricCoeff_id {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x i j =
      if i = j then 1 else 0 := by
  rw [pullbackMetricCoeff_euclideanSpace, fderiv_id, ContinuousLinearMap.id_apply]
  exact orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal i j

/-- On flat `EuclideanSpace ℝ (Fin n)`, scaling `y ↦ c • y` has constant metric coefficients
`c ^ 2 δ_ij`. -/
theorem pullbackMetricCoeff_const_smul {n : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (i j : Fin n) :
    pullbackMetricCoeff (fun y : EuclideanSpace ℝ (Fin n) => c • y) x i j =
      if i = j then c ^ 2 else 0 := by
  have hd : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => c • y) x =
      c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) :=
    ((hasFDerivAt_id x).const_smul c).fderiv
  rw [pullbackMetricCoeff_euclideanSpace, hd]
  simp only [smul_apply, ContinuousLinearMap.id_apply, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real]
  rw [orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal i j]
  split_ifs <;> ring

/-- Every linear isometry equivalence of `EuclideanSpace ℝ (Fin n)` has Kronecker-delta pullback
metric coefficients `δ_ij`. -/
@[simp] theorem pullbackMetricCoeff_linearIsometryEquiv {n : ℕ}
    (O : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff (O : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x i j =
      if i = j then 1 else 0 := by
  have hd : fderiv ℝ (O : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x =
      O.toContinuousLinearEquiv.toContinuousLinearMap :=
    O.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.fderiv
  rw [pullbackMetricCoeff_euclideanSpace, hd]
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    O.inner_map_map]
  exact orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal i j

end EuclideanMetricCoeff

/-! ### Asymptotically Euclidean ends -/

/-- An *asymptotically Euclidean end* of `M` of order `t`: a smooth injective parametrization
`param : exteriorOpen n radius → M` of an open subset of `M` by `{x ∈ ℝⁿ : radius < ‖x‖}`
(`0 < radius`), with bijective differential everywhere on that exterior, whose metric coefficients
`g_ij` decay to `δ_ij` at rate `‖x‖ ^ (-t)` along with their first and second Euclidean derivatives
at rates `‖x‖ ^ (-t - 1)` and `‖x‖ ^ (-t - 2)` (Cecchini–Zeidler, Definition 2.1, without the
scalar-curvature integrability clause). -/
@[ext]
structure AsymptoticallyEuclideanEnd (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] (t : ℝ) where
  /-- The radius of the excised coordinate ball. -/
  radius : ℝ
  /-- The excision radius is strictly positive. -/
  radius_pos : 0 < radius
  /-- The end parametrization defined on the open exterior `{x ∈ ℝⁿ : radius < ‖x‖}`. -/
  param : exteriorOpen n radius → M
  /-- Smoothness of the parametrization on the exterior. -/
  contMDiff : ContMDiff (𝓡 n) (𝓡 n) ∞ param
  /-- Injectivity of the parametrization on the exterior. -/
  injective : Injective param
  /-- Openness of the end image in `M`. -/
  isOpen_range : IsOpen (range param)
  /-- Bijectivity of the differential at every point of the exterior. -/
  mfderiv_bijective : ∀ x : exteriorOpen n radius, Bijective (mfderiv (𝓡 n) (𝓡 n) param x)
  /-- Asymptotic Euclidean decay up to second derivatives of the metric coefficients. -/
  decay : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), radius < ‖x‖ → ∀ i j : Fin n,
    |exteriorMetricCoeff param x i j - if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) ∧
    ‖fderiv ℝ (fun y => exteriorMetricCoeff param y i j) x‖ ≤ C * ‖x‖ ^ (-t - 1) ∧
    ‖fderiv ℝ (fderiv ℝ (fun y => exteriorMetricCoeff param y i j)) x‖ ≤ C * ‖x‖ ^ (-t - 2)

namespace AsymptoticallyEuclideanEnd

section Basic

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] {t : ℝ}
  (E : AsymptoticallyEuclideanEnd n M t)

/-- Pointwise extensionality for `AsymptoticallyEuclideanEnd` in terms of ambient points `x ∈ ℝⁿ`
with `radius < ‖x‖`. -/
theorem ext_iff_forall {E₁ E₂ : AsymptoticallyEuclideanEnd n M t} :
    E₁ = E₂ ↔ ∃ hR : E₁.radius = E₂.radius,
      ∀ (x : EuclideanSpace ℝ (Fin n)) (hx : E₁.radius < ‖x‖),
        E₁.param ⟨x, mem_exteriorOpen.mpr hx⟩ =
          E₂.param ⟨x, mem_exteriorOpen.mpr (hR ▸ hx)⟩ := by
  refine ⟨by rintro rfl; exact ⟨rfl, fun _ _ => rfl⟩, fun ⟨hR, hφ⟩ => ?_⟩
  rcases E₁ with ⟨R₁, hR₁, φ₁, _, _, _, _, _⟩
  rcases E₂ with ⟨R₂, hR₂, φ₂, _, _, _, _, _⟩
  dsimp only at hR hφ; subst hR
  suffices φ₁ = φ₂ by subst this; rfl
  exact funext fun ⟨x, hx⟩ => hφ x (mem_exteriorOpen.mp hx)

/-- The coordinate metric coefficients `g_ij : ℝⁿ → ℝ` of an end `E`, equal to
`⟨d(E.param)_x e_i, d(E.param)_x e_j⟩` for `E.radius < ‖x‖` and `0` otherwise. -/
def metricCoeff (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) : ℝ :=
  exteriorMetricCoeff E.param x i j

theorem metricCoeff_def (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    E.metricCoeff x i j = exteriorMetricCoeff E.param x i j := (rfl)

theorem metricCoeff_of_lt {x : EuclideanSpace ℝ (Fin n)} (hx : E.radius < ‖x‖)
    (i j : Fin n) :
    E.metricCoeff x i j =
      ⟪mfderiv (𝓡 n) (𝓡 n) E.param ⟨x, mem_exteriorOpen.mpr hx⟩
          (EuclideanSpace.basisFun (Fin n) ℝ i),
        mfderiv (𝓡 n) (𝓡 n) E.param ⟨x, mem_exteriorOpen.mpr hx⟩
          (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ :=
  exteriorMetricCoeff_of_lt E.param hx i j

@[simp] theorem metricCoeff_of_le {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ E.radius)
    (i j : Fin n) :
    E.metricCoeff x i j = 0 :=
  exteriorMetricCoeff_of_le E.param hx i j

/-- Symmetry of the metric coefficients of an end. -/
theorem metricCoeff_symm (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    E.metricCoeff x i j = E.metricCoeff x j i :=
  exteriorMetricCoeff_symm E.param x i j

/-- Every diagonal metric coefficient of an end is strictly positive on `{x : E.radius < ‖x‖}`. -/
theorem metricCoeff_diag_pos {x : EuclideanSpace ℝ (Fin n)} (hx : E.radius < ‖x‖) (i : Fin n) :
    0 < E.metricCoeff x i i := by
  rw [E.metricCoeff_of_lt hx, real_inner_self_eq_norm_sq]
  refine sq_pos_of_pos (norm_pos_iff.mpr fun h0 => ?_)
  exact (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.ne_zero i
    ((E.mfderiv_bijective ⟨x, mem_exteriorOpen.mpr hx⟩).1 (h0.trans (map_zero _).symm))

/-- If an ambient map `φ : ℝⁿ → M` agrees with `E.param` on `{x : E.radius < ‖x‖}`, then
`E.metricCoeff` agrees with `pullbackMetricCoeff φ` on a neighbourhood of every exterior point. -/
theorem eventuallyEq_metricCoeff_pullbackMetricCoeff {φ : EuclideanSpace ℝ (Fin n) → M}
    (hφ : ∀ (y : EuclideanSpace ℝ (Fin n)) (hy : E.radius < ‖y‖),
      E.param ⟨y, mem_exteriorOpen.mpr hy⟩ = φ y)
    {x : EuclideanSpace ℝ (Fin n)} (hx : E.radius < ‖x‖) (i j : Fin n) :
    (fun y => E.metricCoeff y i j) =ᶠ[𝓝 x] (fun y => pullbackMetricCoeff φ y i j) := by
  have heq : E.param = φ ∘ (Subtype.val : exteriorOpen n E.radius → EuclideanSpace ℝ (Fin n)) :=
    funext fun ⟨y, hy⟩ => hφ y (mem_exteriorOpen.mp hy)
  simpa only [metricCoeff_def, heq] using eventuallyEq_exteriorMetricCoeff_comp_subtype φ hx i j

/-- Pointwise agreement of `E.metricCoeff` and `pullbackMetricCoeff φ` on `{x : E.radius < ‖x‖}`
for any ambient extension `φ` of `E.param`. -/
theorem metricCoeff_eq_pullbackMetricCoeff {φ : EuclideanSpace ℝ (Fin n) → M}
    (hφ : ∀ (y : EuclideanSpace ℝ (Fin n)) (hy : E.radius < ‖y‖),
      E.param ⟨y, mem_exteriorOpen.mpr hy⟩ = φ y)
    {x : EuclideanSpace ℝ (Fin n)} (hx : E.radius < ‖x‖) (i j : Fin n) :
    E.metricCoeff x i j = pullbackMetricCoeff φ x i j :=
  (E.eventuallyEq_metricCoeff_pullbackMetricCoeff hφ hx i j).self_of_nhds

/-- The image of the end in `M`. -/
def image : Set M := range E.param

theorem image_def : E.image = range E.param := (rfl)

/-- Membership in `E.image` means being of the form `E.param ⟨x, ...⟩` for some `x` with
`E.radius < ‖x‖`. -/
theorem mem_image_iff {p : M} :
    p ∈ E.image ↔ ∃ (x : EuclideanSpace ℝ (Fin n)) (hx : E.radius < ‖x‖),
      E.param ⟨x, mem_exteriorOpen.mpr hx⟩ = p := by
  rw [image_def, mem_range]
  exact ⟨fun ⟨⟨x, hx⟩, hp⟩ => ⟨x, mem_exteriorOpen.mp hx, hp⟩,
    fun ⟨x, hx, hp⟩ => ⟨⟨x, mem_exteriorOpen.mpr hx⟩, hp⟩⟩

/-- The image of an AE end is open in `M`. -/
theorem isOpen_image : IsOpen E.image := E.isOpen_range

/-- The image of an AE end packaged as an element of `TopologicalSpace.Opens M`. -/
def openImage : Opens M := ⟨E.image, E.isOpen_image⟩

@[simp] theorem coe_openImage : (E.openImage : Set M) = E.image := (rfl)

@[simp] theorem mem_openImage_iff {p : M} : p ∈ E.openImage ↔ p ∈ E.image := Iff.rfl

theorem mem_openImage_param (x : exteriorOpen n E.radius) : E.param x ∈ E.openImage := ⟨x, rfl⟩

/-- In positive dimension, the image of an AE end is nonempty. -/
theorem image_nonempty (hn : 1 ≤ n) : E.image.Nonempty := by
  obtain ⟨x, hx⟩ := exteriorOpen_nonempty hn E.radius
  exact ⟨E.param ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩

/-- In dimension at least `2`, the image of an AE end is path-connected. -/
theorem isPathConnected_image (hn : 2 ≤ n) : IsPathConnected E.image := by
  have : PathConnectedSpace (exteriorOpen n E.radius) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_exteriorOpen hn E.radius)
  exact isPathConnected_range E.contMDiff.continuous

/-- In dimension at least `2`, the image of an AE end is connected. -/
theorem isConnected_image (hn : 2 ≤ n) : IsConnected E.image :=
  (E.isPathConnected_image hn).isConnected

/-- **Smart constructor from an ambient map.** Any map `φ : ℝⁿ → M` that is smooth, injective, open
onto its image, has bijective differential on `{x : R < ‖x‖}`, and satisfies the `C²` decay bounds
for `pullbackMetricCoeff φ` there defines an `AsymptoticallyEuclideanEnd`. -/
def ofFun {R : ℝ} (hR : 0 < R) (φ : EuclideanSpace ℝ (Fin n) → M)
    (hφ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ φ {x | R < ‖x‖})
    (hinj : InjOn φ {x | R < ‖x‖})
    (hopen : IsOpen (φ '' {x | R < ‖x‖}))
    (hbij : ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ → Bijective (mfderiv (𝓡 n) (𝓡 n) φ x))
    (hdecay : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ → ∀ i j : Fin n,
      |pullbackMetricCoeff φ x i j - if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) ∧
      ‖fderiv ℝ (fun y => pullbackMetricCoeff φ y i j) x‖ ≤ C * ‖x‖ ^ (-t - 1) ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => pullbackMetricCoeff φ y i j)) x‖ ≤ C * ‖x‖ ^ (-t - 2)) :
    AsymptoticallyEuclideanEnd n M t where
  radius := R
  radius_pos := hR
  param := φ ∘ Subtype.val
  contMDiff := hφ.comp_contMDiff contMDiff_subtype_val fun x => mem_exteriorOpen.mp x.2
  injective x₁ x₂ h := Subtype.ext (hinj (mem_exteriorOpen.mp x₁.2) (mem_exteriorOpen.mp x₂.2) h)
  isOpen_range := by rw [range_comp, Subtype.range_coe_subtype]; exact hopen
  mfderiv_bijective x := by
    have heq : mfderiv (𝓡 n) (𝓡 n) (φ ∘ (Subtype.val : exteriorOpen n R → _)) x =
        mfderiv (𝓡 n) (𝓡 n) φ x.1 :=
      ContinuousLinearMap.ext
        (TauCeti.Manifold.mfderiv_comp_subtype_val_apply (U := exteriorOpen n R))
    rw [heq]; exact hbij x.1 (mem_exteriorOpen.mp x.2)
  decay := by
    obtain ⟨C, hC⟩ := hdecay
    refine ⟨C, fun x hx i j => ?_⟩
    have hev := eventuallyEq_exteriorMetricCoeff_comp_subtype φ hx i j
    rw [exteriorMetricCoeff_comp_subtype_of_lt φ hx i j, hev.fderiv_eq,
      (hev.fderiv (𝕜 := ℝ)).fderiv_eq]
    exact hC x hx i j

@[simp] theorem ofFun_radius {R : ℝ} (hR : 0 < R) (φ : EuclideanSpace ℝ (Fin n) → M)
    (hφ) (hinj) (hopen) (hbij) (hdecay) :
    (ofFun (t := t) hR φ hφ hinj hopen hbij hdecay).radius = R := (rfl)

@[simp] theorem ofFun_param_apply {R : ℝ} (hR : 0 < R) (φ : EuclideanSpace ℝ (Fin n) → M)
    (hφ) (hinj) (hopen) (hbij) (hdecay)
    (x : exteriorOpen n (ofFun (t := t) hR φ hφ hinj hopen hbij hdecay).radius) :
    (ofFun (t := t) hR φ hφ hinj hopen hbij hdecay).param x = φ x.1 := (rfl)

@[simp] theorem ofFun_image {R : ℝ} (hR : 0 < R) (φ : EuclideanSpace ℝ (Fin n) → M)
    (hφ) (hinj) (hopen) (hbij) (hdecay) :
    (ofFun (t := t) hR φ hφ hinj hopen hbij hdecay).image = φ '' {x | R < ‖x‖} := by
  rw [ofFun, image_def, range_comp, Subtype.range_coe_subtype]; rfl

@[simp] theorem ofFun_metricCoeff_of_lt {R : ℝ} (hR : 0 < R) (φ : EuclideanSpace ℝ (Fin n) → M)
    (hφ) (hinj) (hopen) (hbij) (hdecay) {x : EuclideanSpace ℝ (Fin n)} (hx : R < ‖x‖)
    (i j : Fin n) :
    (ofFun (t := t) hR φ hφ hinj hopen hbij hdecay).metricCoeff x i j =
      pullbackMetricCoeff φ x i j :=
  exteriorMetricCoeff_comp_subtype_of_lt φ hx i j

/-- **Monotonicity in the decay order.** Every AE end of order `t₂` is also an AE end of any lower
order `t₁ ≤ t₂`, with the same excision radius and parametrization. -/
def ofLE {t₁ t₂ : ℝ} (E : AsymptoticallyEuclideanEnd n M t₂) (ht : t₁ ≤ t₂) :
    AsymptoticallyEuclideanEnd n M t₁ where
  radius := E.radius
  radius_pos := E.radius_pos
  param := E.param
  contMDiff := E.contMDiff
  injective := E.injective
  isOpen_range := E.isOpen_range
  mfderiv_bijective := E.mfderiv_bijective
  decay := by
    obtain ⟨C, hC⟩ := E.decay
    refine ⟨max C 0 * E.radius ^ (t₁ - t₂), fun x hx i j => ?_⟩
    have hx_pos : 0 < ‖x‖ := E.radius_pos.trans hx
    have hscale (k : ℝ) : C * ‖x‖ ^ (-t₂ - k) ≤
        (max C 0 * E.radius ^ (t₁ - t₂)) * ‖x‖ ^ (-t₁ - k) := by
      have hrpow : ‖x‖ ^ (t₁ - t₂) ≤ E.radius ^ (t₁ - t₂) :=
        Real.rpow_le_rpow_of_nonpos E.radius_pos hx.le (by linarith)
      have hsplit : ‖x‖ ^ (-t₂ - k) = ‖x‖ ^ (t₁ - t₂) * ‖x‖ ^ (-t₁ - k) := by
        rw [← Real.rpow_add hx_pos]; congr 1; ring
      calc
        C * ‖x‖ ^ (-t₂ - k) ≤ max C 0 * ‖x‖ ^ (-t₂ - k) :=
          mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg hx_pos.le _)
        _ = max C 0 * (‖x‖ ^ (t₁ - t₂) * ‖x‖ ^ (-t₁ - k)) := by rw [hsplit]
        _ ≤ max C 0 * (E.radius ^ (t₁ - t₂) * ‖x‖ ^ (-t₁ - k)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hrpow (Real.rpow_nonneg hx_pos.le _)) (le_max_right C 0)
        _ = (max C 0 * E.radius ^ (t₁ - t₂)) * ‖x‖ ^ (-t₁ - k) := (mul_assoc _ _ _).symm
    obtain ⟨h₀, h₁, h₂⟩ := hC x hx i j
    exact ⟨h₀.trans (by simpa only [sub_zero] using hscale 0),
      h₁.trans (hscale 1), h₂.trans (hscale 2)⟩

@[simp] theorem ofLE_radius {t₁ t₂ : ℝ} (E : AsymptoticallyEuclideanEnd n M t₂) (ht : t₁ ≤ t₂) :
    (E.ofLE ht).radius = E.radius := (rfl)

@[simp] theorem ofLE_param_apply {t₁ t₂ : ℝ} (E : AsymptoticallyEuclideanEnd n M t₂)
    (ht : t₁ ≤ t₂) (x : exteriorOpen n (E.ofLE ht).radius) :
    (E.ofLE ht).param x =
      E.param ⟨x.1, mem_exteriorOpen.mpr (by simpa [ofLE_radius] using mem_exteriorOpen.mp x.2)⟩ :=
  (rfl)

@[simp] theorem ofLE_image {t₁ t₂ : ℝ} (E : AsymptoticallyEuclideanEnd n M t₂) (ht : t₁ ≤ t₂) :
    (E.ofLE ht).image = E.image := (rfl)

@[simp] theorem ofLE_metricCoeff {t₁ t₂ : ℝ} (E : AsymptoticallyEuclideanEnd n M t₂)
    (ht : t₁ ≤ t₂) : (E.ofLE ht).metricCoeff = E.metricCoeff := (rfl)

private theorem mfderiv_comp_inc {R' : ℝ} (hR' : E.radius ≤ R') (z : exteriorOpen n R')
    (v : TangentSpace (𝓡 n) z) :
    mfderiv (𝓡 n) (𝓡 n)
      (E.param ∘ fun w : exteriorOpen n R' =>
        (⟨w.1, mem_exteriorOpen.mpr (hR'.trans_lt (mem_exteriorOpen.mp w.2))⟩ :
          exteriorOpen n E.radius)) z v =
      mfderiv (𝓡 n) (𝓡 n) E.param
        ⟨z.1, mem_exteriorOpen.mpr (hR'.trans_lt (mem_exteriorOpen.mp z.2))⟩ v := by
  let inc : exteriorOpen n R' → exteriorOpen n E.radius :=
    fun w => ⟨w.1, mem_exteriorOpen.mpr (hR'.trans_lt (mem_exteriorOpen.mp w.2))⟩
  have hinc_smooth : ContMDiff (𝓡 n) (𝓡 n) ∞ inc :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff (exteriorOpen n E.radius) _).mp contMDiff_subtype_val
  have hsub : mfderiv (𝓡 n) (𝓡 n) ((Subtype.val : exteriorOpen n E.radius → _) ∘ inc) z v =
      mfderiv (𝓡 n) (𝓡 n) inc z v :=
    TauCeti.Manifold.mfderiv_subtype_val_comp_apply v
  have hsub' : (Subtype.val : exteriorOpen n E.radius → _) ∘ inc =
      (Subtype.val : exteriorOpen n R' → _) := rfl
  rw [hsub', Manifold.mfderiv_subtype_val] at hsub
  rw [mfderiv_comp z (E.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    (hinc_smooth.contMDiffAt.mdifferentiableAt (by simp)), ContinuousLinearMap.comp_apply,
    ← hsub, ContinuousLinearEquiv.coe_coe, Manifold.tangentSpaceOpenEquiv_apply]

private theorem exteriorMetricCoeff_comp_inc {R' : ℝ} (hR' : E.radius ≤ R')
    {x : EuclideanSpace ℝ (Fin n)} (hx : R' < ‖x‖) (i j : Fin n) :
    exteriorMetricCoeff
      (E.param ∘ fun z : exteriorOpen n R' =>
        (⟨z.1, mem_exteriorOpen.mpr (hR'.trans_lt (mem_exteriorOpen.mp z.2))⟩ :
          exteriorOpen n E.radius)) x i j =
      exteriorMetricCoeff E.param x i j := by
  have hyE : E.radius < ‖x‖ := hR'.trans_lt hx
  rw [exteriorMetricCoeff_of_lt _ hx, exteriorMetricCoeff_of_lt _ hyE]
  exact congrArg₂ (inner ℝ) (E.mfderiv_comp_inc hR' ⟨x, mem_exteriorOpen.mpr hx⟩ _)
    (E.mfderiv_comp_inc hR' ⟨x, mem_exteriorOpen.mpr hx⟩ _)

end Basic

/-! ### Diffeomorphism onto the open image and properness of the end radius -/

section SmoothManifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] {t : ℝ}

/-- **Smart constructor on a smooth manifold.** On a smooth `n`-manifold `M`, a smooth injective
map `φ : exteriorOpen n R → M` with injective differential everywhere on the exterior and `C²`
asymptotic Euclidean decay defines an `AsymptoticallyEuclideanEnd`. -/
def ofIsManifold {R : ℝ} (hR : 0 < R) (φ : exteriorOpen n R → M)
    (hφ : ContMDiff (𝓡 n) (𝓡 n) ∞ φ) (hinj : Injective φ)
    (hmf : ∀ x : exteriorOpen n R, Injective (mfderiv (𝓡 n) (𝓡 n) φ x))
    (hdecay : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ → ∀ i j : Fin n,
      |exteriorMetricCoeff φ x i j - if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) ∧
      ‖fderiv ℝ (fun y => exteriorMetricCoeff φ y i j) x‖ ≤ C * ‖x‖ ^ (-t - 1) ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => exteriorMetricCoeff φ y i j)) x‖ ≤ C * ‖x‖ ^ (-t - 2)) :
    AsymptoticallyEuclideanEnd n M t where
  radius := R
  radius_pos := hR
  param := φ
  contMDiff := hφ
  injective := hinj
  isOpen_range := by
    have hloc : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ φ := fun x =>
      isLocalDiffeomorphAt_of_injective_mfderiv hφ.contMDiffOn isOpen_univ (mem_univ x)
        BoundarylessManifold.isInteriorPoint (by simp) (hmf x) rfl
    rw [← image_univ]
    exact hloc.isLocalHomeomorph.isOpenMap univ isOpen_univ
  mfderiv_bijective x := by
    have : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
      inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
    have : FiniteDimensional ℝ (TangentSpace (𝓡 n) (φ x)) :=
      inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
    exact ⟨hmf x, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp (hmf x)⟩
  decay := hdecay

@[simp] theorem ofIsManifold_radius {R : ℝ} (hR : 0 < R) (φ : exteriorOpen n R → M)
    (hφ) (hinj) (hmf) (hdecay) :
    (ofIsManifold (t := t) hR φ hφ hinj hmf hdecay).radius = R := (rfl)

@[simp] theorem ofIsManifold_param_apply {R : ℝ} (hR : 0 < R) (φ : exteriorOpen n R → M)
    (hφ) (hinj) (hmf) (hdecay)
    (x : exteriorOpen n (ofIsManifold (t := t) hR φ hφ hinj hmf hdecay).radius) :
    (ofIsManifold (t := t) hR φ hφ hinj hmf hdecay).param x = φ ⟨x.1,
      mem_exteriorOpen.mpr (by simpa [ofIsManifold_radius] using mem_exteriorOpen.mp x.2)⟩ := (rfl)

@[simp] theorem ofIsManifold_image {R : ℝ} (hR : 0 < R) (φ : exteriorOpen n R → M)
    (hφ) (hinj) (hmf) (hdecay) :
    (ofIsManifold (t := t) hR φ hφ hinj hmf hdecay).image = range φ := (rfl)

@[simp] theorem ofIsManifold_metricCoeff {R : ℝ} (hR : 0 < R) (φ : exteriorOpen n R → M)
    (hφ) (hinj) (hmf) (hdecay) :
    (ofIsManifold (t := t) hR φ hφ hinj hmf hdecay).metricCoeff = exteriorMetricCoeff φ := (rfl)

variable (E : AsymptoticallyEuclideanEnd n M t)

/-- On a smooth manifold `M`, the parametrization of an AE end is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ E.param := fun x =>
  isLocalDiffeomorphAt_of_injective_mfderiv E.contMDiff.contMDiffOn isOpen_univ (mem_univ x)
    BoundarylessManifold.isInteriorPoint (by simp) (E.mfderiv_bijective x).1 rfl

/-- On a smooth manifold `M`, an AE end parametrizes its open image by a smooth diffeomorphism
`exteriorOpen n E.radius ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ E.openImage`. -/
def diffeomorphImage : exteriorOpen n E.radius ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ E.openImage where
  toEquiv := Equiv.ofInjective E.param E.injective
  contMDiff_toFun := (TauCeti.ContMDiff.subtypeVal_comp_iff E.openImage _).mp E.contMDiff
  contMDiff_invFun y := by
    let e : exteriorOpen n E.radius ≃ E.openImage := Equiv.ofInjective E.param E.injective
    let h := E.isLocalDiffeomorph (e.symm y)
    have hy : E.param (e.symm y) = (y : M) := congrArg Subtype.val (e.apply_symm_apply y)
    have hmem : (y : M) ∈ h.localInverse.source := hy ▸ h.localInverse_mem_source
    have hinv : ContMDiffAt (𝓡 n) (𝓡 n) ∞ h.localInverse (y : M) :=
      hy ▸ h.contMDiffAt_localInverse
    have hsub : Subtype.val ⁻¹' h.localInverse.source ∈ 𝓝 y :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds
        (h.localInverse.open_source.mem_nhds hmem)
    refine (hinv.comp y contMDiff_subtype_val.contMDiffAt).congr_of_eventuallyEq ?_
    filter_upwards [hsub] with z hz
    exact E.injective ((congrArg Subtype.val (e.apply_symm_apply z)).trans
      (h.localInverse_right_inv hz).symm)

@[simp] theorem coe_diffeomorphImage_apply (x : exteriorOpen n E.radius) :
    (E.diffeomorphImage x : M) = E.param x := (rfl)

@[simp] theorem diffeomorphImage_symm_param (x : exteriorOpen n E.radius) :
    E.diffeomorphImage.symm ⟨E.param x, E.mem_openImage_param x⟩ = x :=
  (Equiv.ofInjective E.param E.injective).symm_apply_apply x

@[simp] theorem param_diffeomorphImage_symm (y : E.openImage) :
    E.param (E.diffeomorphImage.symm y) = (y : M) :=
  congrArg Subtype.val ((Equiv.ofInjective E.param E.injective).apply_symm_apply y)

/-- **Shrinking an AE end to a larger excision radius.** Restricting an AE end `E` on a smooth
manifold `M` from `E.radius` to any `R' ≥ E.radius` gives an AE end of the same order `t`. -/
def restrictRadius {R' : ℝ} (hR' : E.radius ≤ R') : AsymptoticallyEuclideanEnd n M t :=
  let inc : exteriorOpen n R' → exteriorOpen n E.radius :=
    fun x => ⟨x.1, mem_exteriorOpen.mpr (hR'.trans_lt (mem_exteriorOpen.mp x.2))⟩
  have hinc_open : IsOpen (range inc) := by
    have hr : range inc = Subtype.val ⁻¹' (exteriorOpen n R' : Set (EuclideanSpace ℝ (Fin n))) := by
      ext y; exact ⟨by rintro ⟨z, rfl⟩; exact z.2, fun hy => ⟨⟨y.1, hy⟩, rfl⟩⟩
    rw [hr]; exact (exteriorOpen n R').isOpen.preimage continuous_subtype_val
  have hinc_smooth : ContMDiff (𝓡 n) (𝓡 n) ∞ inc :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff (exteriorOpen n E.radius) _).mp contMDiff_subtype_val
  { radius := R'
    radius_pos := E.radius_pos.trans_le hR'
    param := E.param ∘ inc
    contMDiff := E.contMDiff.comp hinc_smooth
    injective := fun _ _ h =>
      Subtype.ext (congrArg (Subtype.val : exteriorOpen n E.radius → _) (E.injective h))
    isOpen_range := by
      rw [range_comp]
      exact E.isLocalDiffeomorph.isLocalHomeomorph.isOpenMap _ hinc_open
    mfderiv_bijective := fun x => by
      have heq : mfderiv (𝓡 n) (𝓡 n) (E.param ∘ inc) x = mfderiv (𝓡 n) (𝓡 n) E.param (inc x) :=
        ContinuousLinearMap.ext (E.mfderiv_comp_inc hR' x)
      rw [heq]; exact E.mfderiv_bijective (inc x)
    decay := by
      obtain ⟨C, hC⟩ := E.decay
      refine ⟨C, fun x hx i j => ?_⟩
      have hev : (fun y => exteriorMetricCoeff (E.param ∘ inc) y i j) =ᶠ[𝓝 x]
          (fun y => exteriorMetricCoeff E.param y i j) := by
        filter_upwards [(exteriorOpen n R').isOpen.mem_nhds (mem_exteriorOpen.mpr hx)] with y hy
        exact E.exteriorMetricCoeff_comp_inc hR' (mem_exteriorOpen.mp hy) i j
      have hx0 : exteriorMetricCoeff (E.param ∘ inc) x i j = exteriorMetricCoeff E.param x i j :=
        hev.self_of_nhds
      rw [hx0, hev.fderiv_eq, (hev.fderiv (𝕜 := ℝ)).fderiv_eq]
      exact hC x (hR'.trans_lt hx) i j }

@[simp] theorem restrictRadius_radius {R' : ℝ} (hR' : E.radius ≤ R') :
    (E.restrictRadius hR').radius = R' := (rfl)

@[simp] theorem restrictRadius_param_apply {R' : ℝ} (hR' : E.radius ≤ R')
    (x : exteriorOpen n (E.restrictRadius hR').radius) :
    (E.restrictRadius hR').param x = E.param ⟨x.1, mem_exteriorOpen.mpr
      (hR'.trans_lt (by simpa [restrictRadius_radius] using mem_exteriorOpen.mp x.2))⟩ := (rfl)

@[simp] theorem restrictRadius_metricCoeff_of_lt {R' : ℝ} (hR' : E.radius ≤ R')
    {x : EuclideanSpace ℝ (Fin n)} (hx : R' < ‖x‖) (i j : Fin n) :
    (E.restrictRadius hR').metricCoeff x i j = E.metricCoeff x i j :=
  E.exteriorMetricCoeff_comp_inc hR' hx i j

/-- The coordinate radius `‖φ⁻¹(·)‖ : E.openImage → Set.Ioi E.radius` on the open image of an AE
end. -/
def endRadius (y : E.openImage) : Ioi E.radius :=
  ⟨‖(E.diffeomorphImage.symm y : EuclideanSpace ℝ (Fin n))‖,
    mem_exteriorOpen.mp (E.diffeomorphImage.symm y).2⟩

@[simp] theorem coe_endRadius (y : E.openImage) :
    (E.endRadius y : ℝ) = ‖(E.diffeomorphImage.symm y : EuclideanSpace ℝ (Fin n))‖ := (rfl)

theorem coe_endRadius_param (x : exteriorOpen n E.radius) :
    (E.endRadius ⟨E.param x, E.mem_openImage_param x⟩ : ℝ) =
      ‖(x : EuclideanSpace ℝ (Fin n))‖ := by
  simp

/-- The real-valued coordinate radius `y ↦ (E.endRadius y : ℝ)` is smooth on `E.openImage`. -/
theorem contMDiff_coe_endRadius :
    ContMDiff (𝓡 n) 𝓘(ℝ) ∞ (fun y : E.openImage => (E.endRadius y : ℝ)) := by
  intro y
  have hne : (E.diffeomorphImage.symm y : EuclideanSpace ℝ (Fin n)) ≠ 0 :=
    exteriorOpen_coe_ne_zero E.radius_pos.le _
  change ContMDiffAt (𝓡 n) 𝓘(ℝ) ∞
    (norm ∘ fun z : E.openImage => (E.diffeomorphImage.symm z : EuclideanSpace ℝ (Fin n))) y
  exact ((contDiffAt_norm ℝ hne).contMDiffAt).comp y
    (contMDiff_subtype_val.comp E.diffeomorphImage.symm.contMDiff).contMDiffAt

/-- **Properness of the end radius.** On a smooth manifold `M`, the coordinate radius
`E.endRadius : E.openImage → Set.Ioi E.radius` is a proper map. -/
theorem isProperMap_endRadius : IsProperMap E.endRadius := by
  have heq : E.endRadius =
      (fun x : exteriorOpen n E.radius =>
        (⟨‖(x : EuclideanSpace ℝ (Fin n))‖, mem_exteriorOpen.mp x.2⟩ : Ioi E.radius)) ∘
        E.diffeomorphImage.toHomeomorph.symm := rfl
  rw [heq]
  exact isProperMap_exteriorOpen_norm.comp E.diffeomorphImage.toHomeomorph.symm.isProperMap

/-- Every closed coordinate annulus `{E.param x : r₁ ≤ ‖x‖ ≤ r₂}` with `E.radius < r₁` is compact
in `M`. -/
theorem isCompact_image_annulus {r₁ r₂ : ℝ} (hr₁ : E.radius < r₁) :
    IsCompact (E.param '' {x : exteriorOpen n E.radius |
      r₁ ≤ ‖(x : EuclideanSpace ℝ (Fin n))‖ ∧ ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ r₂}) := by
  have hsub : Icc r₁ r₂ ⊆ Ioi E.radius := fun r hr' => hr₁.trans_le hr'.1
  let liftIcc : Icc r₁ r₂ → Ioi E.radius := fun r => ⟨r.1, hsub r.2⟩
  have : CompactSpace (Icc r₁ r₂) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hK : IsCompact (range liftIcc) := isCompact_range (by fun_prop)
  convert (E.isProperMap_endRadius.isCompact_preimage hK).image continuous_subtype_val using 1
  ext p
  simp only [mem_image, mem_preimage, mem_range, liftIcc]
  constructor
  · rintro ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
    exact ⟨⟨E.param x, E.mem_openImage_param x⟩,
      ⟨⟨‖(x : EuclideanSpace ℝ (Fin n))‖, hx₁, hx₂⟩, Subtype.ext (by simp)⟩, rfl⟩
  · rintro ⟨y, ⟨⟨r, hr₁', hr₂'⟩, hyr⟩, rfl⟩
    refine ⟨E.diffeomorphImage.symm y, ?_, E.param_diffeomorphImage_symm y⟩
    have hval : ‖(E.diffeomorphImage.symm y : EuclideanSpace ℝ (Fin n))‖ = r :=
      (congrArg Subtype.val hyr).symm
    change r₁ ≤ ‖(E.diffeomorphImage.symm y : EuclideanSpace ℝ (Fin n))‖ ∧
      ‖(E.diffeomorphImage.symm y : EuclideanSpace ℝ (Fin n))‖ ≤ r₂
    rw [hval]; exact ⟨hr₁', hr₂'⟩

end SmoothManifold

end AsymptoticallyEuclideanEnd

/-! ### Finite-ended asymptotically Euclidean structures -/

/-- A *finite-ended asymptotically Euclidean structure* of order `t` on `M`: a finite nonempty
family of AE ends of order `t` with pairwise disjoint images whose union has compact complement in
`M` (Cecchini–Zeidler, Definition 2.3, without boundary). -/
@[ext]
structure FiniteEndedAE (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] (t : ℝ) where
  /-- The number of ends. -/
  numEnds : ℕ
  /-- Nonemptiness of the family of ends, ruling out closed manifolds. -/
  numEnds_pos : 0 < numEnds
  /-- The indexed family of AE ends. -/
  ends : Fin numEnds → AsymptoticallyEuclideanEnd n M t
  /-- Distinct ends have disjoint images in `M`. -/
  pairwise_disjoint : Pairwise fun a b => Disjoint (ends a).image (ends b).image
  /-- The complement of the union of the end images is compact in `M`. -/
  isCompact_compl : IsCompact (⋃ a, (ends a).image)ᶜ

namespace FiniteEndedAE

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] {t : ℝ}
  (A : FiniteEndedAE n M t)

/-- Extensionality for `FiniteEndedAE` across equal end counts. -/
theorem ext_iff_forall {A₁ A₂ : FiniteEndedAE n M t} :
    A₁ = A₂ ↔ ∃ h : A₁.numEnds = A₂.numEnds,
      ∀ a : Fin A₁.numEnds, A₁.ends a = A₂.ends (a.cast h) := by
  refine ⟨by rintro rfl; exact ⟨rfl, fun _ => rfl⟩, fun ⟨h, hends⟩ => ?_⟩
  rcases A₁ with ⟨m₁, hm₁, e₁, _, _⟩; rcases A₂ with ⟨m₂, hm₂, e₂, _, _⟩
  dsimp only at h hends; subst h
  suffices e₁ = e₂ by subst this; rfl
  exact funext hends

instance : Nonempty (Fin A.numEnds) := ⟨⟨0, A.numEnds_pos⟩⟩

/-- The union of the images of all ends in `A`. -/
def endsUnion : Set M := ⋃ a, (A.ends a).image

theorem endsUnion_def : A.endsUnion = ⋃ a, (A.ends a).image := (rfl)

/-- The union of all end images is open in `M`. -/
theorem isOpen_endsUnion : IsOpen A.endsUnion := isOpen_iUnion fun a => (A.ends a).isOpen_image

/-- The compact core of `M` outside the union of the ends. -/
def compactCore : Set M := A.endsUnionᶜ

theorem compactCore_def : A.compactCore = A.endsUnionᶜ := (rfl)

/-- The compact core is closed in `M`. -/
theorem isClosed_compactCore : IsClosed A.compactCore := A.isOpen_endsUnion.isClosed_compl

/-- The compact core is compact in `M`. -/
theorem isCompact_compactCore : IsCompact A.compactCore := A.isCompact_compl

/-- **Monotonicity in the decay order** for finite-ended AE structures. -/
def ofLE {t₁ t₂ : ℝ} (A : FiniteEndedAE n M t₂) (ht : t₁ ≤ t₂) : FiniteEndedAE n M t₁ :=
  ⟨A.numEnds, A.numEnds_pos, fun a => (A.ends a).ofLE ht, A.pairwise_disjoint, A.isCompact_compl⟩

@[simp] theorem ofLE_numEnds {t₁ t₂ : ℝ} (A : FiniteEndedAE n M t₂) (ht : t₁ ≤ t₂) :
    (A.ofLE ht).numEnds = A.numEnds := (rfl)

@[simp] theorem ofLE_ends {t₁ t₂ : ℝ} (A : FiniteEndedAE n M t₂) (ht : t₁ ≤ t₂)
    (a : Fin (A.ofLE ht).numEnds) :
    (A.ofLE ht).ends a = (A.ends (a.cast (A.ofLE_numEnds ht))).ofLE ht := (rfl)

end FiniteEndedAE

/-! ### Euclidean witnesses and scaling obstruction -/

/-- **Flat Euclidean space as an AE end.** For every `R > 0` and every decay order `t : ℝ`, the
identity parametrization of `{x ∈ ℝⁿ : R < ‖x‖}` is an asymptotically Euclidean end of flat
`EuclideanSpace ℝ (Fin n)`. -/
def AsymptoticallyEuclideanEnd.euclideanId (n : ℕ) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    AsymptoticallyEuclideanEnd n (EuclideanSpace ℝ (Fin n)) t :=
  AsymptoticallyEuclideanEnd.ofFun hR id contMDiffOn_id (Set.injOn_id {x | R < ‖x‖})
    (by simpa only [image_id] using isOpen_lt continuous_const continuous_norm)
    (fun x _ => by simpa [mfderiv_id] using Function.bijective_id)
    ⟨0, fun x _ i j => by
      have hd1 : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
          pullbackMetricCoeff id y i j) = 0 := by simp [pullbackMetricCoeff_id]
      rw [pullbackMetricCoeff_id, sub_self, abs_zero, zero_mul, hd1]
      refine ⟨le_rfl, ?_, ?_⟩
      · rw [Pi.zero_apply, norm_zero, zero_mul]
      · rw [show (0 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) =
            fun _ => 0 from rfl, fderiv_const_apply, zero_mul]
        exact (norm_zero (E :=
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).le⟩

@[simp] theorem AsymptoticallyEuclideanEnd.euclideanId_radius (n : ℕ) {R : ℝ} (hR : 0 < R)
    (t : ℝ) : (AsymptoticallyEuclideanEnd.euclideanId n hR t).radius = R := (rfl)

@[simp] theorem AsymptoticallyEuclideanEnd.euclideanId_param_apply (n : ℕ) {R : ℝ} (hR : 0 < R)
    (t : ℝ) (x : exteriorOpen n (AsymptoticallyEuclideanEnd.euclideanId n hR t).radius) :
    (AsymptoticallyEuclideanEnd.euclideanId n hR t).param x = x.1 := (rfl)

@[simp] theorem AsymptoticallyEuclideanEnd.euclideanId_image (n : ℕ) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    (AsymptoticallyEuclideanEnd.euclideanId n hR t).image = {x | R < ‖x‖} := by
  rw [euclideanId, ofFun_image, image_id]

@[simp] theorem AsymptoticallyEuclideanEnd.euclideanId_metricCoeff_of_lt (n : ℕ) {R : ℝ}
    (hR : 0 < R) (t : ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx : R < ‖x‖) (i j : Fin n) :
    (AsymptoticallyEuclideanEnd.euclideanId n hR t).metricCoeff x i j =
      if i = j then 1 else 0 := by
  rw [euclideanId, ofFun_metricCoeff_of_lt _ _ _ _ _ _ _ hx, pullbackMetricCoeff_id]

/-- **Flat Euclidean space is finite-ended AE of every order.** Excising `closedBall 0 1` gives a
single AE end of flat `EuclideanSpace ℝ (Fin n)` with compact complement. -/
def FiniteEndedAE.euclideanSpace (n : ℕ) (t : ℝ) :
    FiniteEndedAE n (EuclideanSpace ℝ (Fin n)) t where
  numEnds := 1
  numEnds_pos := Nat.one_pos
  ends _ := AsymptoticallyEuclideanEnd.euclideanId n zero_lt_one t
  pairwise_disjoint a b hab := False.elim (hab (Subsingleton.elim a b))
  isCompact_compl := by
    have hu : (⋃ _ : Fin 1, (AsymptoticallyEuclideanEnd.euclideanId n zero_lt_one t).image)ᶜ =
        closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      ext x; simp [dist_zero_right]
    rw [hu]; exact isCompact_closedBall 0 1

@[simp] theorem FiniteEndedAE.euclideanSpace_numEnds (n : ℕ) (t : ℝ) :
    (FiniteEndedAE.euclideanSpace n t).numEnds = 1 := (rfl)

@[simp] theorem FiniteEndedAE.euclideanSpace_ends (n : ℕ) (t : ℝ)
    (a : Fin (FiniteEndedAE.euclideanSpace n t).numEnds) :
    (FiniteEndedAE.euclideanSpace n t).ends a =
      AsymptoticallyEuclideanEnd.euclideanId n zero_lt_one t := (rfl)

/-- **Non-unit scaling is not asymptotically Euclidean.** In dimension `n ≥ 1`, for any `t > 0` and
any `c : ℝ` with `|c| ≠ 1` (in particular `c = 2`, where `g_ij - δ_ij = 3 δ_ij`), no
`AsymptoticallyEuclideanEnd` of flat `EuclideanSpace ℝ (Fin n)` of order `t` has parametrization
`x ↦ c • x`. -/
theorem not_exists_asymptoticallyEuclideanEnd_smul {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 < t)
    {c : ℝ} (hc : |c| ≠ 1) :
    ¬ ∃ E : AsymptoticallyEuclideanEnd n (EuclideanSpace ℝ (Fin n)) t,
      ∀ x : exteriorOpen n E.radius, E.param x = c • (x : EuclideanSpace ℝ (Fin n)) := by
  rintro ⟨E, hE⟩
  obtain ⟨C, hC⟩ := E.decay
  let i₀ : Fin n := ⟨0, hn⟩
  let e₀ : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i₀ 1
  have he₀ : ‖e₀‖ = 1 := by simp [e₀]
  have hgap : 0 < |c ^ 2 - 1| := by
    rw [abs_pos, sub_ne_zero]; intro hc2; apply hc; nlinarith [abs_nonneg c, sq_abs c]
  have htend : Tendsto (fun r : ℝ => C * r ^ (-t)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop ht).const_mul C
  obtain ⟨r, hr_bound, hrR⟩ :=
    ((htend.eventually (gt_mem_nhds hgap)).and (eventually_gt_atTop E.radius)).exists
  have hr_pos : 0 < r := E.radius_pos.trans hrR
  have hnorm : ‖r • e₀‖ = r := by rw [norm_smul, Real.norm_of_nonneg hr_pos.le, he₀, mul_one]
  have hxr : E.radius < ‖r • e₀‖ := hnorm.symm ▸ hrR
  have hcoeff : E.metricCoeff (r • e₀) i₀ i₀ = c ^ 2 := by
    rw [E.metricCoeff_eq_pullbackMetricCoeff (φ := fun y => c • y)
      (fun y hy => hE ⟨y, mem_exteriorOpen.mpr hy⟩) hxr i₀ i₀, pullbackMetricCoeff_const_smul]
    simp only [↓reduceIte]
  have hle := (hC (r • e₀) hxr i₀ i₀).1
  simp only [← E.metricCoeff_def, hcoeff, ↓reduceIte, hnorm] at hle
  exact not_lt_of_ge hle hr_bound

end TauCeti
