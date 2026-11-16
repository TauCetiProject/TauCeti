/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.Analysis.Normed.Module.Ball.Exterior
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Asymptotically Euclidean ends

An **asymptotically Euclidean end** of order `t` of a Riemannian manifold `M` (modeled on any
`I : ModelWithCorners ℝ E H`, boundaryless or with boundary) is a smooth injective parametrization
`φ : {x ∈ ℝⁿ | R < ‖x‖} → M` (`R > 0`) with bijective differential everywhere, whose pulled-back
metric coefficients `g_ij(x) = ⟪dφ_x e_i, dφ_x e_j⟫` are `C²` on `{R < ‖x‖}` and satisfy
`|g_ij(x) - δ_ij| ≤ C ‖x‖ ^ (-t)`, `‖D(g_ij)(x)‖ ≤ C ‖x‖ ^ (-t - 1)`, and
`‖D²(g_ij)(x)‖ ≤ C ‖x‖ ^ (-t - 2)` for all `‖x‖ > R` and `i, j : Fin n`.

`AsymptoticallyEuclideanEnd` stores its parametrization on `exteriorBall _ radius` and extends
`openPullbackMetricCoeff` by `0` outside, so `fderiv` acts directly on `ℝⁿ → ℝ` and agrees locally
with any global extension `pullbackMetricCoeff I ψ`. Recording `C²` regularity on the exterior
domain ensures the `fderiv` bounds control genuine derivatives rather than Mathlib's default zero
derivative; `mkOfIsContMDiff` discharges this field automatically for `C²` metrics on `C¹`
manifolds.

## Main definitions

* `TauCeti.pullbackMetricCoeff`, `TauCeti.openPullbackMetricCoeff`: pulled-back metric coefficients
  for total maps `ℝⁿ → M` and maps on open subsets `U ⊆ ℝⁿ`.
* `TauCeti.AsymptoticallyEuclideanEnd`, `TauCeti.AsymptoticallyEuclideanEnd.mkOfIsContMDiff`,
  `TauCeti.AsymptoticallyEuclideanEnd.ofTotal`,
  `TauCeti.AsymptoticallyEuclideanEnd.partialDiffeomorph`: ends, constructors, and partial
  diffeomorphism packaging.

## Main results

* `TauCeti.AsymptoticallyEuclideanEnd.contDiffOn_two_metricCoeff`,
  `TauCeti.AsymptoticallyEuclideanEnd.contDiffOn_metricCoeff`: `C²` and ambient `C^m` (`m ≤ ∞`)
  regularity of the pulled-back metric coefficients.
* `TauCeti.AsymptoticallyEuclideanEnd.isOpen_range`,
  `TauCeti.AsymptoticallyEuclideanEnd.isConnected_range`,
  `TauCeti.AsymptoticallyEuclideanEnd.riemannianJacobian_partialDiffeomorph`: openness,
  connectedness, and Jacobian formula.
* `TauCeti.AsymptoticallyEuclideanEnd.restrictRadius`, `TauCeti.AsymptoticallyEuclideanEnd.ofLe`,
  `TauCeti.AsymptoticallyEuclideanEnd.transRiemannianIsometry`,
  `TauCeti.AsymptoticallyEuclideanEnd.euclidean`: functoriality and flat Euclidean model.
* `TauCeti.not_exists_decay_pullbackMetricCoeff_smul`,
  `TauCeti.AsymptoticallyEuclideanEnd.toFun_ne_smul`: non-isometric dilations fail decay.

## References

* R. Bartnik, *The mass of an asymptotically flat manifold*, Comm. Pure Appl. Math. 39 (1986),
  661–693.
* S. Cecchini and R. Zeidler, *The positive mass theorem and distance estimates in the spin
  setting*, Trans. Amer. Math. Soc. 377 (2024), 5271–5288, Definition 2.1 (arXiv:2108.11972v2).
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Sections 8 and 9.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Manifold Matrix RealInnerProductSpace Topology

namespace TauCeti

/-! ### Pulled-back metric coefficients -/

section PullbackMetricCoeff

variable {n : ℕ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- Helper: the manifold derivative of `y ↦ a • y` on a real normed space acts by `a • ·` under
`NormedSpace.fromTangentSpace`. -/
private theorem mfderiv_const_smul_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : ℝ) (x v : F) :
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun y : F ↦ a • y) x ((NormedSpace.fromTangentSpace x).symm v) =
      a • (NormedSpace.fromTangentSpace (a • x)).symm v := by
  apply (NormedSpace.fromTangentSpace (a • x)).injective
  rw [map_smul, ContinuousLinearEquiv.apply_symm_apply, ← mvfderiv_apply_eq_mfderiv_apply]
  change mvfderiv 𝓘(ℝ, F) (a • id) x _ = a • v
  simp [mvfderiv_const_smul_field, mvfderiv_eq_fderiv]

/-- The pulled-back metric coefficients `g_ij(x) = ⟪dφ_x e_i, dφ_x e_j⟫` of a total map
`φ : ℝⁿ → M` in the standard orthonormal basis of `ℝⁿ`. -/
def pullbackMetricCoeff (I : ModelWithCorners ℝ E H)
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (φ : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) : ℝ :=
  inner ℝ (mfderiv (𝓡 n) I φ x (EuclideanSpace.basisFun (Fin n) ℝ i))
    (mfderiv (𝓡 n) I φ x (EuclideanSpace.basisFun (Fin n) ℝ j))

/-- Unfolding lemma for `pullbackMetricCoeff`. -/
theorem pullbackMetricCoeff_def (φ : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff I φ x i j =
      inner ℝ (mfderiv (𝓡 n) I φ x (EuclideanSpace.basisFun (Fin n) ℝ i))
        (mfderiv (𝓡 n) I φ x (EuclideanSpace.basisFun (Fin n) ℝ j)) := by rfl

/-- Symmetry of the pulled-back metric coefficients of a total map. -/
theorem pullbackMetricCoeff_symm (φ : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff I φ x i j = pullbackMetricCoeff I φ x j i := real_inner_comm _ _

/-- The pulled-back metric coefficients of `id` on `EuclideanSpace ℝ (Fin n)` are `δ_ij`. -/
@[simp]
theorem pullbackMetricCoeff_id (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff (𝓡 n) (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) x i j =
      if i = j then 1 else 0 := by
  let v (k : Fin n) : TangentSpace (𝓡 n) x :=
    (NormedSpace.fromTangentSpace x).symm (EuclideanSpace.basisFun (Fin n) ℝ k)
  change inner ℝ (mfderiv (𝓡 n) (𝓡 n) id x (v i)) (mfderiv (𝓡 n) (𝓡 n) id x (v j)) = _
  rw [mfderiv_id, ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply,
    TauCeti.Manifold.inner_tangentSpace_vectorSpace, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  exact orthonormal_iff_ite.1 (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal i j

/-- Precomposing `φ : ℝⁿ → M` with a nonzero scalar dilation `y ↦ a • y` multiplies its
pulled-back metric coefficients at `x` by `a ^ 2`, evaluated at `a • x`. -/
theorem pullbackMetricCoeff_comp_smul (φ : EuclideanSpace ℝ (Fin n) → M) {a : ℝ} (ha : a ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff I (fun y ↦ φ (a • y)) x i j =
      a ^ 2 * pullbackMetricCoeff I φ (a • x) i j := by
  let A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    Units.mk0 a ha • ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))
  have hA : (⇑A.toDiffeomorph : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) = (a • ·) :=
    funext fun y ↦ by simp [A]
  have hderiv (k : Fin n) :
      mfderiv (𝓡 n) I (fun y ↦ φ (a • y)) x (EuclideanSpace.basisFun (Fin n) ℝ k) =
        a • mfderiv (𝓡 n) I φ (a • x) (EuclideanSpace.basisFun (Fin n) ℝ k) := by
    have hcomp := DFunLike.congr_fun
      (A.toDiffeomorph.mfderiv_comp_diffeomorph (K := I) (hn := by simp) (f := φ) (x := x))
      ((NormedSpace.fromTangentSpace x).symm (EuclideanSpace.basisFun (Fin n) ℝ k))
    change mfderiv (𝓡 n) I (φ ∘ ⇑A.toDiffeomorph) x _ =
      mfderiv (𝓡 n) I φ (⇑A.toDiffeomorph x) (mfderiv (𝓡 n) (𝓡 n) ⇑A.toDiffeomorph x _) at hcomp
    rw [hA, mfderiv_const_smul_apply, map_smul] at hcomp; exact hcomp
  rw [pullbackMetricCoeff, pullbackMetricCoeff, hderiv i, hderiv j, real_inner_smul_left,
    real_inner_smul_right]; ring

/-- The pulled-back metric coefficients of `y ↦ a • y` on `EuclideanSpace ℝ (Fin n)` are
`a ^ 2 * δ_ij`. -/
theorem pullbackMetricCoeff_smul (a : ℝ) (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff (𝓡 n) (fun y : EuclideanSpace ℝ (Fin n) ↦ a • y) x i j =
      if i = j then a ^ 2 else 0 := by
  have hderiv (k : Fin n) :
      mfderiv (𝓡 n) (𝓡 n) (fun y : EuclideanSpace ℝ (Fin n) ↦ a • y) x
          (EuclideanSpace.basisFun (Fin n) ℝ k) =
        a • (NormedSpace.fromTangentSpace (a • x)).symm (EuclideanSpace.basisFun (Fin n) ℝ k) :=
    mfderiv_const_smul_apply a x _
  rw [pullbackMetricCoeff, hderiv i, hderiv j, TauCeti.Manifold.inner_tangentSpace_vectorSpace,
    map_smul, map_smul, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply, real_inner_smul_left, real_inner_smul_right,
    orthonormal_iff_ite.1 (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal i j]
  split_ifs <;> ring

/-- The pulled-back metric coefficients of a `C^k` map `φ : ℝⁿ → M` on an open set `s` into a
`C^m` Riemannian manifold (`m + 1 ≤ k`) are `C^m` on `s`. -/
theorem contDiffOn_pullbackMetricCoeff [IsManifold I 1 M] {m k : ℕ∞ω}
    [IsContMDiffRiemannianBundle I m E (fun x : M ↦ TangentSpace I x)]
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : IsOpen s)
    {φ : EuclideanSpace ℝ (Fin n) → M} (hφ : ContMDiffOn (𝓡 n) I k φ s)
    (hmk : m + 1 ≤ k) (i j : Fin n) :
    ContDiffOn ℝ m (fun x ↦ pullbackMetricCoeff I φ x i j) s :=
  hφ.contDiffOn_inner_mfderiv hmk hs
    (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)

/-- The pulled-back metric coefficients of `φ : U → M` on an open subset `U ⊆ ℝⁿ`, extended by `0`
outside `U`. Since `U` is open, derivatives on `U` agree with any global extension of `φ`. -/
def openPullbackMetricCoeff (I : ModelWithCorners ℝ E H)
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {U : Opens (EuclideanSpace ℝ (Fin n))} (φ : U → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) : ℝ := by
  classical
  exact if hx : x ∈ U then
    inner ℝ (mfderiv (𝓡 n) I φ ⟨x, hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ i))
      (mfderiv (𝓡 n) I φ ⟨x, hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ j))
  else 0

section OpenPullback

variable {U : Opens (EuclideanSpace ℝ (Fin n))}

/-- Evaluation of `openPullbackMetricCoeff` at a point inside `U`. -/
theorem openPullbackMetricCoeff_of_mem (φ : U → M) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    (i j : Fin n) :
    openPullbackMetricCoeff I φ x i j = inner ℝ
      (mfderiv (𝓡 n) I φ ⟨x, hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ i))
      (mfderiv (𝓡 n) I φ ⟨x, hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
  classical simp [openPullbackMetricCoeff, hx]

/-- Outside the open domain `U`, `openPullbackMetricCoeff` vanishes by definition. -/
theorem openPullbackMetricCoeff_of_notMem (φ : U → M) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ U)
    (i j : Fin n) : openPullbackMetricCoeff I φ x i j = 0 := by
  classical simp [openPullbackMetricCoeff, hx]

/-- Symmetry of the pulled-back metric coefficients on an open subset. -/
theorem openPullbackMetricCoeff_symm (φ : U → M) (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    openPullbackMetricCoeff I φ x i j = openPullbackMetricCoeff I φ x j i := by
  by_cases hx : x ∈ U
  · rw [openPullbackMetricCoeff_of_mem _ hx, openPullbackMetricCoeff_of_mem _ hx, real_inner_comm]
  · rw [openPullbackMetricCoeff_of_notMem _ hx, openPullbackMetricCoeff_of_notMem _ hx]

/-- If a total map `ψ : ℝⁿ → M` agrees with `φ : U → M` on `U`, then their pulled-back metric
coefficients agree on `U`. -/
theorem openPullbackMetricCoeff_eq_pullbackMetricCoeff_of_eqOn {φ : U → M}
    {ψ : EuclideanSpace ℝ (Fin n) → M} (h : ∀ x : U, ψ x = φ x)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) (i j : Fin n) :
    openPullbackMetricCoeff I φ x i j = pullbackMetricCoeff I ψ x i j := by
  have hcomp : φ = ψ ∘ (Subtype.val : U → EuclideanSpace ℝ (Fin n)) := funext fun y ↦ (h y).symm
  subst hcomp
  have hderiv (k : Fin n) :
      mfderiv (𝓡 n) I (ψ ∘ (Subtype.val : U → _)) ⟨x, hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ k) =
        mfderiv (𝓡 n) I ψ x (EuclideanSpace.basisFun (Fin n) ℝ k) :=
    TauCeti.Manifold.mfderiv_comp_subtype_val_apply (I := I) (J := 𝓡 n) (U := U) (f := ψ)
      (x := ⟨x, hx⟩) _
  rw [openPullbackMetricCoeff_of_mem _ hx, pullbackMetricCoeff, hderiv i, hderiv j]

/-- Near any point of `U`, `openPullbackMetricCoeff I φ` agrees with `pullbackMetricCoeff I ψ`
for any global extension `ψ` of `φ`. -/
theorem openPullbackMetricCoeff_eventuallyEq_pullbackMetricCoeff {φ : U → M}
    {ψ : EuclideanSpace ℝ (Fin n) → M} (h : ∀ x : U, ψ x = φ x)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) (i j : Fin n) :
    (fun y ↦ openPullbackMetricCoeff I φ y i j) =ᶠ[𝓝 x]
      (fun y ↦ pullbackMetricCoeff I ψ y i j) :=
  eventually_of_mem (U.isOpen.mem_nhds hx) fun _ hy ↦
    openPullbackMetricCoeff_eq_pullbackMetricCoeff_of_eqOn h hy i j

/-- Restricting `φ : U → M` to a smaller open subset `V ≤ U` preserves `openPullbackMetricCoeff`
on `V`. -/
theorem openPullbackMetricCoeff_comp_inclusion {V : Opens (EuclideanSpace ℝ (Fin n))} (hVU : V ≤ U)
    (φ : U → M) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ V) (i j : Fin n) :
    openPullbackMetricCoeff I (φ ∘ Opens.inclusion hVU) x i j =
      openPullbackMetricCoeff I φ x i j := by
  let ψ : EuclideanSpace ℝ (Fin n) → M := Subtype.val.extend φ (fun _ ↦ φ ⟨x, hVU hx⟩)
  have hψU : ∀ y : U, ψ y = φ y := Subtype.val_injective.extend_apply φ _
  rw [openPullbackMetricCoeff_eq_pullbackMetricCoeff_of_eqOn (φ := φ ∘ Opens.inclusion hVU)
      (fun y ↦ hψU (Opens.inclusion hVU y)) hx,
    openPullbackMetricCoeff_eq_pullbackMetricCoeff_of_eqOn hψU (hVU hx)]

/-- On an open subset `U ⊆ ℝⁿ`, the pulled-back metric coefficients of `Subtype.val : U → ℝⁿ` are
the Kronecker delta `δ_ij`. -/
theorem openPullbackMetricCoeff_subtype_val {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    (i j : Fin n) :
    openPullbackMetricCoeff (𝓡 n) (Subtype.val : U → EuclideanSpace ℝ (Fin n)) x i j =
      if i = j then 1 else 0 :=
  (openPullbackMetricCoeff_eq_pullbackMetricCoeff_of_eqOn (ψ := id) (fun _ ↦ rfl) hx i j).trans
    (pullbackMetricCoeff_id x i j)

/-- The pulled-back metric coefficients of a `C^k` map `φ : U → M` into a `C^m` Riemannian
manifold (`m + 1 ≤ k`) are `C^m` on `U`. -/
theorem contDiffOn_openPullbackMetricCoeff [IsManifold I 1 M] {m k : ℕ∞ω}
    [IsContMDiffRiemannianBundle I m E (fun x : M ↦ TangentSpace I x)]
    {φ : U → M} (hφ : ContMDiff (𝓡 n) I k φ) (hmk : m + 1 ≤ k) (i j : Fin n) :
    ContDiffOn ℝ m (fun x ↦ openPullbackMetricCoeff I φ x i j) (U : Set _) := by
  rcases Set.eq_empty_or_nonempty (U : Set (EuclideanSpace ℝ (Fin n))) with hU | ⟨x₀, hx₀⟩
  · exact hU ▸ contDiffOn_empty
  · let ψ : EuclideanSpace ℝ (Fin n) → M := Subtype.val.extend φ (fun _ ↦ φ ⟨x₀, hx₀⟩)
    have hψ : ContMDiffOn (𝓡 n) I k ψ (U : Set _) := fun y hy ↦
      ((hφ.contMDiffAt (x := ⟨y, hy⟩)).extend_subtypeVal _).contMDiffWithinAt
    exact (contDiffOn_pullbackMetricCoeff U.isOpen hψ hmk i j).congr fun _ hy ↦
      openPullbackMetricCoeff_eq_pullbackMetricCoeff_of_eqOn
        (Subtype.val_injective.extend_apply φ _) hy i j

end OpenPullback

section IsometryPullback

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

/-- Postcomposing `φ : ℝⁿ → M` with a Riemannian isometry preserves its pulled-back metric
coefficients. -/
@[simp]
theorem pullbackMetricCoeff_riemannianIsometry_comp (φ : EuclideanSpace ℝ (Fin n) → M)
    (Φ : RiemannianIsometry I J M N) :
    pullbackMetricCoeff J (Φ ∘ φ) = pullbackMetricCoeff I φ := by
  funext x i j
  have hderiv (k : Fin n) :
      mfderiv (𝓡 n) J (Φ ∘ φ) x (EuclideanSpace.basisFun (Fin n) ℝ k) =
        mfderiv I J Φ (φ x) (mfderiv (𝓡 n) I φ x (EuclideanSpace.basisFun (Fin n) ℝ k)) := by
    have h := Φ.toDiffeomorph.mfderiv_diffeomorph_comp (K := 𝓡 n) (hn := by simp) (f := φ) (x := x)
    rw [RiemannianIsometry.coe_toDiffeomorph] at h
    exact (DFunLike.congr_fun h _).trans (ContinuousLinearMap.comp_apply _ _ _)
  rw [pullbackMetricCoeff, pullbackMetricCoeff, hderiv i, hderiv j, Φ.inner_mfderiv]

/-- Postcomposing `φ : U → M` with a Riemannian isometry preserves its pulled-back metric
coefficients. -/
@[simp]
theorem openPullbackMetricCoeff_riemannianIsometry_comp {U : Opens (EuclideanSpace ℝ (Fin n))}
    (φ : U → M) (Φ : RiemannianIsometry I J M N) :
    openPullbackMetricCoeff J (Φ ∘ φ) = openPullbackMetricCoeff I φ := by
  funext x i j
  by_cases hx : x ∈ U
  · let ψ : EuclideanSpace ℝ (Fin n) → M := Subtype.val.extend φ (fun _ ↦ φ ⟨x, hx⟩)
    have hψ : ∀ y : U, ψ y = φ y := Subtype.val_injective.extend_apply φ _
    rw [openPullbackMetricCoeff_eq_pullbackMetricCoeff_of_eqOn (φ := Φ ∘ φ) (ψ := Φ ∘ ψ)
          (fun y ↦ congrArg Φ (hψ y)) hx,
      openPullbackMetricCoeff_eq_pullbackMetricCoeff_of_eqOn hψ hx,
      pullbackMetricCoeff_riemannianIsometry_comp]
  · rw [openPullbackMetricCoeff_of_notMem _ hx, openPullbackMetricCoeff_of_notMem _ hx]

end IsometryPullback

end PullbackMetricCoeff

/-! ### Asymptotically Euclidean ends -/

/-- An **asymptotically Euclidean end** of order `t` of a Riemannian manifold `M` with model `I`:
a smooth injective parametrization of an open subset of `M` by
`exteriorBall (EuclideanSpace ℝ (Fin n)) radius` (`0 < radius`) with bijective differential
everywhere, whose pulled-back metric coefficients are `C²` on the exterior domain and satisfy the
second-order decay bounds `|∂^α (g_ij - δ_ij)| ≤ C ‖x‖ ^ (-t - |α|)` for `|α| ≤ 2`. -/
structure AsymptoticallyEuclideanEnd (n : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] (t : ℝ) where
  /-- The radius of the excised coordinate ball. -/
  radius : ℝ
  /-- The excised radius is positive. -/
  radius_pos : 0 < radius
  /-- The end parametrization on the open exterior `{x | radius < ‖x‖}`. -/
  toFun : exteriorBall (EuclideanSpace ℝ (Fin n)) radius → M
  /-- Smoothness of the end parametrization. -/
  contMDiff : ContMDiff (𝓡 n) I ∞ toFun
  /-- Injectivity of the end parametrization. -/
  injective : Function.Injective toFun
  /-- Bijectivity of the differential at every point of the end. -/
  mfderiv_bijective : ∀ x : exteriorBall (EuclideanSpace ℝ (Fin n)) radius,
    Function.Bijective (mfderiv (𝓡 n) I toFun x)
  /-- `C²` regularity of the pulled-back metric coefficients on the exterior domain. -/
  contDiffOn_openPullbackMetricCoeff : ∀ i j : Fin n,
    ContDiffOn ℝ 2 (fun y ↦ openPullbackMetricCoeff I toFun y i j)
      (exteriorBall (EuclideanSpace ℝ (Fin n)) radius : Set (EuclideanSpace ℝ (Fin n)))
  /-- Second-order asymptotically Euclidean decay of the pulled-back metric coefficients. -/
  decay : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), radius < ‖x‖ → ∀ i j : Fin n,
    |openPullbackMetricCoeff I toFun x i j - if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) ∧
    ‖fderiv ℝ (fun y ↦ openPullbackMetricCoeff I toFun y i j) x‖ ≤
      C * ‖x‖ ^ (-t - 1) ∧
    ‖fderiv ℝ (fderiv ℝ (fun y ↦ openPullbackMetricCoeff I toFun y i j)) x‖ ≤
      C * ‖x‖ ^ (-t - 2)

namespace AsymptoticallyEuclideanEnd

variable {n : ℕ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {t : ℝ}

/-- Two asymptotically Euclidean ends are equal if they have the same excised radius and agree
pointwise on their common exterior domain. -/
@[ext (iff := false)]
theorem ext {e₁ e₂ : AsymptoticallyEuclideanEnd n I M t}
    (hr : e₁.radius = e₂.radius)
    (hf : ∀ (x : EuclideanSpace ℝ (Fin n)) (h₁ : e₁.radius < ‖x‖) (h₂ : e₂.radius < ‖x‖),
      e₁.toFun ⟨x, mem_exteriorBall.2 h₁⟩ = e₂.toFun ⟨x, mem_exteriorBall.2 h₂⟩) :
    e₁ = e₂ := by
  cases e₁; cases e₂; dsimp only at hr hf; subst hr; congr 1
  funext ⟨x, hx⟩; exact hf x (mem_exteriorBall.1 hx) (mem_exteriorBall.1 hx)

variable (e : AsymptoticallyEuclideanEnd n I M t)

/-- The pulled-back metric coefficients of an end, extended by `0` on `closedBall 0 e.radius`. -/
def metricCoeff : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ :=
  openPullbackMetricCoeff I e.toFun

/-- Unfolding lemma for `metricCoeff` in terms of `openPullbackMetricCoeff`. -/
theorem metricCoeff_eq_openPullbackMetricCoeff :
    e.metricCoeff = openPullbackMetricCoeff I e.toFun := by rfl

/-- Evaluation of `e.metricCoeff` on `exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius`. -/
theorem metricCoeff_of_mem {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius) (i j : Fin n) :
    e.metricCoeff x i j = inner ℝ
      (mfderiv (𝓡 n) I e.toFun ⟨x, hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ i))
      (mfderiv (𝓡 n) I e.toFun ⟨x, hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
  exact openPullbackMetricCoeff_of_mem e.toFun hx i j

/-- Outside `exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius`, `e.metricCoeff` vanishes. -/
theorem metricCoeff_of_notMem {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∉ exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius) (i j : Fin n) :
    e.metricCoeff x i j = 0 := by exact openPullbackMetricCoeff_of_notMem e.toFun hx i j

/-- The pulled-back metric matrix of an asymptotically Euclidean end at `x`. -/
def metricMatrix (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (e.metricCoeff x)

/-- Symmetry of the pulled-back metric coefficients of an end. -/
theorem metricCoeff_symm (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    e.metricCoeff x i j = e.metricCoeff x j i := by exact openPullbackMetricCoeff_symm e.toFun x i j

@[simp]
theorem metricMatrix_apply (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    e.metricMatrix x i j = e.metricCoeff x i j := by rfl

@[simp]
theorem metricMatrix_transpose (x : EuclideanSpace ℝ (Fin n)) :
    (e.metricMatrix x)ᵀ = e.metricMatrix x := by ext i j; exact e.metricCoeff_symm x j i

/-- For any global map `ψ : ℝⁿ → M` agreeing with `e.toFun` on the exterior ball, `e.metricCoeff`
agrees with `pullbackMetricCoeff I ψ` on `{e.radius < ‖x‖}`. -/
theorem metricCoeff_eq_pullbackMetricCoeff_of_eqOn {ψ : EuclideanSpace ℝ (Fin n) → M}
    (h : ∀ x : exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius, ψ x = e.toFun x)
    {x : EuclideanSpace ℝ (Fin n)} (hx : e.radius < ‖x‖) (i j : Fin n) :
    e.metricCoeff x i j = pullbackMetricCoeff I ψ x i j := by
  exact openPullbackMetricCoeff_eq_pullbackMetricCoeff_of_eqOn h (mem_exteriorBall.2 hx) i j

/-- Near any point of `exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius`, `e.metricCoeff` agrees
with `pullbackMetricCoeff I ψ` for any global extension `ψ` of `e.toFun`. -/
theorem metricCoeff_eventuallyEq_pullbackMetricCoeff {ψ : EuclideanSpace ℝ (Fin n) → M}
    (h : ∀ x : exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius, ψ x = e.toFun x)
    {x : EuclideanSpace ℝ (Fin n)} (hx : e.radius < ‖x‖) (i j : Fin n) :
    (fun y ↦ e.metricCoeff y i j) =ᶠ[𝓝 x] (fun y ↦ pullbackMetricCoeff I ψ y i j) := by
  exact openPullbackMetricCoeff_eventuallyEq_pullbackMetricCoeff h (mem_exteriorBall.2 hx) i j

/-- The pulled-back metric coefficients of an end are `C²` on its exterior domain. -/
theorem contDiffOn_two_metricCoeff (i j : Fin n) :
    ContDiffOn ℝ 2 (fun x ↦ e.metricCoeff x i j)
      (exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius : Set (EuclideanSpace ℝ (Fin n))) := by
  exact e.contDiffOn_openPullbackMetricCoeff i j

/-- The pulled-back metric coefficients of an end are `C^m` on the exterior domain whenever the
manifold is `C¹` and the metric is `C^m` with `m ≤ ∞`. -/
theorem contDiffOn_metricCoeff [IsManifold I 1 M] {m : ℕ∞ω} (hm : m ≤ ∞)
    [IsContMDiffRiemannianBundle I m E (fun x : M ↦ TangentSpace I x)] (i j : Fin n) :
    ContDiffOn ℝ m (fun x ↦ e.metricCoeff x i j)
      (exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius : Set (EuclideanSpace ℝ (Fin n))) := by
  refine TauCeti.contDiffOn_openPullbackMetricCoeff e.contMDiff ?_ i j
  cases m with | top => exact absurd hm (by decide) | coe _ => exact WithTop.coe_le_coe.2 le_top

/-! #### Constructors -/

section MkOfIsContMDiff

variable [IsManifold I 1 M]
  [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]
  {R : ℝ} (hR : 0 < R) (φ : exteriorBall (EuclideanSpace ℝ (Fin n)) R → M)
  (hdiff : ContMDiff (𝓡 n) I ∞ φ) (hinj : Function.Injective φ)
  (hbij : ∀ x : exteriorBall (EuclideanSpace ℝ (Fin n)) R,
    Function.Bijective (mfderiv (𝓡 n) I φ x))
  (hdecay : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ → ∀ i j : Fin n,
    |openPullbackMetricCoeff I φ x i j - if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) ∧
    ‖fderiv ℝ (fun y ↦ openPullbackMetricCoeff I φ y i j) x‖ ≤ C * ‖x‖ ^ (-t - 1) ∧
    ‖fderiv ℝ (fderiv ℝ (fun y ↦ openPullbackMetricCoeff I φ y i j)) x‖ ≤ C * ‖x‖ ^ (-t - 2))

/-- Construct an asymptotically Euclidean end on a `C¹` manifold with a `C²` Riemannian metric,
discharging `C²` regularity of the pulled-back metric coefficients automatically. -/
def mkOfIsContMDiff : AsymptoticallyEuclideanEnd n I M t where
  radius := R; radius_pos := hR; toFun := φ; contMDiff := hdiff; injective := hinj
  mfderiv_bijective := hbij; decay := hdecay
  contDiffOn_openPullbackMetricCoeff i j :=
    TauCeti.contDiffOn_openPullbackMetricCoeff hdiff (by simp) i j

@[simp]
theorem radius_mkOfIsContMDiff : (mkOfIsContMDiff hR φ hdiff hinj hbij hdecay).radius = R := by rfl

@[simp]
theorem toFun_mkOfIsContMDiff
    (x : exteriorBall (EuclideanSpace ℝ (Fin n))
      (mkOfIsContMDiff hR φ hdiff hinj hbij hdecay).radius) :
    (mkOfIsContMDiff hR φ hdiff hinj hbij hdecay).toFun x =
      φ ⟨x.1, by simpa only [radius_mkOfIsContMDiff] using x.2⟩ := by rfl

@[simp]
theorem range_mkOfIsContMDiff :
    Set.range (mkOfIsContMDiff hR φ hdiff hinj hbij hdecay).toFun = Set.range φ := by rfl

@[simp]
theorem metricCoeff_mkOfIsContMDiff :
    (mkOfIsContMDiff hR φ hdiff hinj hbij hdecay).metricCoeff = openPullbackMetricCoeff I φ := by
  rfl

@[simp]
theorem metricMatrix_mkOfIsContMDiff (x : EuclideanSpace ℝ (Fin n)) :
    (mkOfIsContMDiff hR φ hdiff hinj hbij hdecay).metricMatrix x =
      Matrix.of (openPullbackMetricCoeff I φ x) := by rfl

end MkOfIsContMDiff

section OfTotal

variable {R : ℝ} (hR : 0 < R) (ψ : EuclideanSpace ℝ (Fin n) → M)
  (hdiff : ContMDiffOn (𝓡 n) I ∞ ψ {x | R < ‖x‖}) (hinj : InjOn ψ {x | R < ‖x‖})
  (hbij : ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ → Function.Bijective (mfderiv (𝓡 n) I ψ x))
  (hmetric : ∀ i j : Fin n,
    ContDiffOn ℝ 2 (fun y ↦ pullbackMetricCoeff I ψ y i j) {x | R < ‖x‖})
  (hdecay : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ → ∀ i j : Fin n,
    |pullbackMetricCoeff I ψ x i j - if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) ∧
    ‖fderiv ℝ (fun y ↦ pullbackMetricCoeff I ψ y i j) x‖ ≤ C * ‖x‖ ^ (-t - 1) ∧
    ‖fderiv ℝ (fderiv ℝ (fun y ↦ pullbackMetricCoeff I ψ y i j)) x‖ ≤ C * ‖x‖ ^ (-t - 2))

/-- Construct an asymptotically Euclidean end from a total map `ψ : ℝⁿ → M` satisfying the
smooth embedding, `C²` metric regularity, and decay conditions on `{x | R < ‖x‖}`. -/
def ofTotal : AsymptoticallyEuclideanEnd n I M t where
  radius := R; radius_pos := hR; toFun := ψ ∘ Subtype.val
  contMDiff x := (contMDiffAt_subtype_iff (I := 𝓡 n) (I' := I)
    (U := exteriorBall (EuclideanSpace ℝ (Fin n)) R) (f := ψ) (x := x)).2
    (hdiff.contMDiffAt (coe_exteriorBall (E := EuclideanSpace ℝ (Fin n)) R ▸
      (exteriorBall (EuclideanSpace ℝ (Fin n)) R).isOpen.mem_nhds x.2))
  injective x y hxy := Subtype.ext (hinj (mem_exteriorBall.1 x.2) (mem_exteriorBall.1 y.2) hxy)
  mfderiv_bijective x := by
    have hψ : MDifferentiableAt (𝓡 n) I ψ x.1 := (hdiff.contMDiffAt
      (coe_exteriorBall (E := EuclideanSpace ℝ (Fin n)) R ▸
        (exteriorBall (EuclideanSpace ℝ (Fin n)) R).isOpen.mem_nhds x.2)).mdifferentiableAt
          (by simp)
    rw [mfderiv_comp x hψ (contMDiff_subtype_val.mdifferentiableAt one_ne_zero),
      TauCeti.Manifold.mfderiv_subtype_val]
    exact (hbij x.1 (mem_exteriorBall.1 x.2)).comp
      (TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓡 n) x).bijective
  contDiffOn_openPullbackMetricCoeff i j :=
    ((coe_exteriorBall (E := EuclideanSpace ℝ (Fin n)) R).symm ▸ hmetric i j).congr fun _ hy ↦
      openPullbackMetricCoeff_eq_pullbackMetricCoeff_of_eqOn (fun _ ↦ rfl) hy i j
  decay := by
    obtain ⟨C, hC⟩ := hdecay
    refine ⟨C, fun x hx i j ↦ ?_⟩
    have hev : (fun y ↦ openPullbackMetricCoeff I
        (ψ ∘ (Subtype.val : exteriorBall (EuclideanSpace ℝ (Fin n)) R → _)) y i j) =ᶠ[𝓝 x]
        (fun y ↦ pullbackMetricCoeff I ψ y i j) :=
      openPullbackMetricCoeff_eventuallyEq_pullbackMetricCoeff (fun _ ↦ rfl)
        (mem_exteriorBall.2 hx) i j
    have h0 := hev.self_of_nhds; dsimp only at h0
    rw [h0, hev.fderiv_eq, hev.fderiv.fderiv_eq]; exact hC x hx i j

@[simp]
theorem radius_ofTotal : (ofTotal hR ψ hdiff hinj hbij hmetric hdecay).radius = R := by rfl

@[simp]
theorem toFun_ofTotal (x : exteriorBall (EuclideanSpace ℝ (Fin n))
    (ofTotal hR ψ hdiff hinj hbij hmetric hdecay).radius) :
    (ofTotal hR ψ hdiff hinj hbij hmetric hdecay).toFun x = ψ x.1 := by rfl

@[simp]
theorem range_ofTotal :
    Set.range (ofTotal hR ψ hdiff hinj hbij hmetric hdecay).toFun = ψ '' {x | R < ‖x‖} := by
  change Set.range (ψ ∘ (Subtype.val : exteriorBall (EuclideanSpace ℝ (Fin n)) R → _)) = _
  rw [Set.range_comp, Subtype.range_coe, coe_exteriorBall]

/-- The pulled-back metric coefficients of `ofTotal` equal `pullbackMetricCoeff I ψ` on
`{x | R < ‖x‖}`. -/
theorem metricCoeff_ofTotal {x : EuclideanSpace ℝ (Fin n)} (hx : R < ‖x‖) (i j : Fin n) :
    (ofTotal hR ψ hdiff hinj hbij hmetric hdecay).metricCoeff x i j =
      pullbackMetricCoeff I ψ x i j := by
  exact openPullbackMetricCoeff_eq_pullbackMetricCoeff_of_eqOn (fun _ ↦ rfl)
    (mem_exteriorBall.2 hx) i j

/-- The pulled-back metric matrix of `ofTotal` equals `Matrix.of (pullbackMetricCoeff I ψ x)` on
`{x | R < ‖x‖}`. -/
theorem metricMatrix_ofTotal {x : EuclideanSpace ℝ (Fin n)} (hx : R < ‖x‖) :
    (ofTotal hR ψ hdiff hinj hbij hmetric hdecay).metricMatrix x =
      Matrix.of (pullbackMetricCoeff I ψ x) := by
  ext i j; exact metricCoeff_ofTotal hR ψ hdiff hinj hbij hmetric hdecay hx i j

end OfTotal

/-! #### Topological and diffeomorphic properties -/

/-- An end parametrization is a `C^k` local diffeomorphism for every `1 ≤ k ≤ ∞`. -/
theorem isLocalDiffeomorph {k : ℕ∞ω} (hk1 : 1 ≤ k) (hk : k ≤ ∞) [IsManifold I k M] :
    IsLocalDiffeomorph (𝓡 n) I k e.toFun := fun x ↦
  isLocalDiffeomorphAt_of_mfderiv_eq (e.contMDiff.of_le hk).contMDiffOn isOpen_univ (mem_univ x)
    BoundarylessManifold.isInteriorPoint hk1
    (e := (LinearEquiv.ofBijective (mfderiv (𝓡 n) I e.toFun x).toLinearMap
      (e.mfderiv_bijective x)).toContinuousLinearEquiv) (by ext v; rfl)

/-- The range of an asymptotically Euclidean end is open in `M`. -/
theorem isOpen_range [IsManifold I 1 M] : IsOpen (Set.range e.toFun) :=
  (e.isLocalDiffeomorph le_rfl (by simp)).isLocalHomeomorph.isOpenMap.isOpen_range

/-- For `2 ≤ n`, the range of an asymptotically Euclidean end is connected. -/
theorem isConnected_range (hn : 2 ≤ n) : IsConnected (Set.range e.toFun) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [← finrank_eq_rank, finrank_euclideanSpace_fin]; exact_mod_cast (by omega : 1 < n)
  have : ConnectedSpace (exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius) :=
    Subtype.connectedSpace (isConnected_exteriorBall hrank e.radius)
  exact _root_.isConnected_range e.contMDiff.continuous

/-- For `1 ≤ n`, the manifold carrying an asymptotically Euclidean end is nonempty. -/
protected theorem nonempty (hn : 1 ≤ n) (e : AsymptoticallyEuclideanEnd n I M t) : Nonempty M := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨x, hx⟩ := nonempty_exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius
  exact ⟨e.toFun ⟨x, hx⟩⟩

section PartialDiffeomorph

variable [Nonempty M]

/-- Auxiliary total extension of `e.toFun` to `ℝⁿ` agreeing with `e.toFun` on the exterior
ball. -/
private def extendFun : EuclideanSpace ℝ (Fin n) → M :=
  Subtype.val.extend e.toFun (fun _ ↦ Classical.arbitrary M)

private theorem extendFun_apply (x : exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius) :
    e.extendFun x.1 = e.toFun x := by exact Subtype.val_injective.extend_apply e.toFun _ x

private theorem injOn_extendFun :
    Set.InjOn e.extendFun (exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius : Set _) :=
  fun x hx y hy hxy ↦ by
    rw [e.extendFun_apply ⟨x, hx⟩, e.extendFun_apply ⟨y, hy⟩] at hxy
    exact congrArg Subtype.val (e.injective hxy)

private theorem isLocalDiffeomorphOn_extendFun {k : ℕ∞ω} (hk1 : 1 ≤ k) (hk : k ≤ ∞)
    [IsManifold I k M] :
    IsLocalDiffeomorphOn (𝓡 n) I k e.extendFun
      (exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius : Set _) := by
  rintro ⟨x, hx⟩
  have hψ : ContMDiffOn (𝓡 n) I k e.extendFun
      (exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius : Set _) := fun y hy ↦ by
    dsimp only [extendFun]
    exact (((e.contMDiff.of_le hk).contMDiffAt (x := ⟨y, hy⟩)).extend_subtypeVal
      (fun _ ↦ Classical.arbitrary M)).contMDiffWithinAt
  have hmdiff : MDifferentiableAt (𝓡 n) I e.extendFun x :=
    (hψ.contMDiffAt ((exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius).isOpen.mem_nhds
      hx)).mdifferentiableAt (by rintro rfl; exact absurd hk1 (by simp))
  -- Transport bijectivity of `mfderiv e.toFun ⟨x, hx⟩` across `tangentSpaceOpenEquiv`.
  have hcomp : ⇑(mfderiv (𝓡 n) I e.extendFun x) =
      ⇑(mfderiv (𝓡 n) I e.toFun ⟨x, hx⟩) ∘
        ⇑(TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓡 n) ⟨x, hx⟩).symm := by
    have heq : e.toFun = e.extendFun ∘ Subtype.val := funext fun y ↦ (e.extendFun_apply y).symm
    ext v
    have h := DFunLike.congr_fun
      (mfderiv_comp ⟨x, hx⟩ hmdiff (contMDiff_subtype_val.mdifferentiableAt one_ne_zero))
      ((TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓡 n) ⟨x, hx⟩).symm v)
    rw [← heq, TauCeti.Manifold.mfderiv_subtype_val] at h
    exact (h.trans (congrArg (mfderiv (𝓡 n) I e.extendFun x)
      ((TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓡 n) ⟨x, hx⟩).apply_symm_apply v))).symm
  have hbij : Function.Bijective (mfderiv (𝓡 n) I e.extendFun x) :=
    hcomp ▸ (e.mfderiv_bijective ⟨x, hx⟩).comp
      (TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓡 n) ⟨x, hx⟩).symm.bijective
  exact isLocalDiffeomorphAt_of_mfderiv_eq hψ
    (exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius).isOpen hx
    BoundarylessManifold.isInteriorPoint hk1
    (e := (LinearEquiv.ofBijective (mfderiv (𝓡 n) I e.extendFun x).toLinearMap
      hbij).toContinuousLinearEquiv) (by ext v; rfl)

/-- An asymptotically Euclidean end packaged as a `C^k` partial diffeomorphism from `ℝⁿ` to `M`
with source `exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius` and target `Set.range e.toFun`. -/
def partialDiffeomorph {k : ℕ∞ω} (hk1 : 1 ≤ k) (hk : k ≤ ∞) [IsManifold I k M] :
    PartialDiffeomorph (𝓡 n) I (EuclideanSpace ℝ (Fin n)) M k :=
  (e.isLocalDiffeomorphOn_extendFun hk1 hk).partialDiffeomorphOfInjOn
    (exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius).isOpen e.injOn_extendFun

variable {k : ℕ∞ω} (hk1 : 1 ≤ k) (hk : k ≤ ∞) [IsManifold I k M]

@[simp]
theorem partialDiffeomorph_source :
    (e.partialDiffeomorph hk1 hk).source =
      (exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius : Set _) := by
  exact IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source _ _ _

@[simp]
theorem partialDiffeomorph_target : (e.partialDiffeomorph hk1 hk).target = Set.range e.toFun := by
  rw [partialDiffeomorph, IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_target, Set.image_eq_range]
  exact congrArg Set.range (funext e.extendFun_apply)

/-- On `exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius`, `e.partialDiffeomorph` agrees with
`e.toFun`. -/
@[simp]
theorem partialDiffeomorph_apply (x : exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius) :
    e.partialDiffeomorph hk1 hk x.1 = e.toFun x := by
  rw [partialDiffeomorph, IsLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn]
  exact e.extendFun_apply x

/-- The inverse of `e.partialDiffeomorph` sends `e.toFun x` back to `x.1`. -/
@[simp]
theorem partialDiffeomorph_symm_apply_toFun
    (x : exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius) :
    (e.partialDiffeomorph hk1 hk).toPartialEquiv.symm (e.toFun x) = x.1 := by
  rw [← e.partialDiffeomorph_apply hk1 hk x]
  exact (e.partialDiffeomorph hk1 hk).left_inv (by rw [partialDiffeomorph_source]; exact x.2)

/-- On `exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius`, `e.partialDiffeomorph` agrees with
`e.toFun`. -/
theorem partialDiffeomorph_apply_of_mem {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius) :
    e.partialDiffeomorph hk1 hk x = e.toFun ⟨x, hx⟩ := e.partialDiffeomorph_apply hk1 hk ⟨x, hx⟩

/-- At every point of the end, the Riemannian Jacobian of `e.partialDiffeomorph` in the standard
basis of `ℝⁿ` is `√(det (e.metricMatrix x))`. -/
theorem riemannianJacobian_partialDiffeomorph {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius) :
    riemannianJacobian (I := I) (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (e.partialDiffeomorph hk1 hk) x = Real.sqrt (e.metricMatrix x).det := by
  rw [riemannianJacobian_eq_sqrt_det_gram]; congr 2; ext i j
  rw [Matrix.gram_apply, OrthonormalBasis.coe_toBasis, metricMatrix_apply]
  exact (e.metricCoeff_eq_pullbackMetricCoeff_of_eqOn
    (fun y ↦ e.partialDiffeomorph_apply hk1 hk y) (mem_exteriorBall.1 hx) i j).symm

end PartialDiffeomorph

/-! #### Functoriality -/

section RestrictRadius

variable {R' : ℝ} (hR' : e.radius ≤ R')

/-- Restrict an asymptotically Euclidean end to a larger excised radius `R' ≥ e.radius`. -/
def restrictRadius : AsymptoticallyEuclideanEnd n I M t where
  radius := R'; radius_pos := e.radius_pos.trans_le hR'
  toFun := e.toFun ∘ Opens.inclusion (exteriorBall_anti hR')
  contMDiff := e.contMDiff.comp (contMDiff_inclusion (exteriorBall_anti hR'))
  injective := e.injective.comp (Set.inclusion_injective (exteriorBall_anti hR'))
  mfderiv_bijective x := by
    let inc := Opens.inclusion (exteriorBall_anti (E := EuclideanSpace ℝ (Fin n)) hR')
    have hinc : MDifferentiableAt (𝓡 n) (𝓡 n) inc x :=
      (contMDiff_inclusion (exteriorBall_anti hR')).mdifferentiableAt one_ne_zero
    -- Deduce bijectivity of `mfderiv inc x` from `mfderiv_subtype_val`.
    have hcomp : ⇑(mfderiv (𝓡 n) (𝓡 n) inc x) =
        ⇑(TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓡 n) (inc x)).symm ∘
          ⇑(TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓡 n) x) := by
      ext v
      have h := DFunLike.congr_fun
        (mfderiv_comp x (contMDiff_subtype_val.mdifferentiableAt one_ne_zero) hinc) v
      change mfderiv (𝓡 n) (𝓡 n) Subtype.val x v = _ at h
      rw [TauCeti.Manifold.mfderiv_subtype_val, TauCeti.Manifold.mfderiv_subtype_val] at h
      exact ((TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓡 n) (inc x)).symm_apply_apply
        _).symm.trans (congrArg _ h.symm)
    rw [mfderiv_comp x (e.contMDiff.mdifferentiable (by simp) _) hinc]
    exact (e.mfderiv_bijective (inc x)).comp (hcomp ▸
      (TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓡 n) (inc x)).symm.bijective.comp
        (TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓡 n) x).bijective)
  contDiffOn_openPullbackMetricCoeff i j :=
    ((e.contDiffOn_openPullbackMetricCoeff i j).mono (exteriorBall_anti hR')).congr fun _ hy ↦
      openPullbackMetricCoeff_comp_inclusion (exteriorBall_anti hR') e.toFun hy i j
  decay := by
    obtain ⟨C, hC⟩ := e.decay
    refine ⟨C, fun x hx i j ↦ ?_⟩
    have hev : (fun y ↦ openPullbackMetricCoeff I
        (e.toFun ∘ Opens.inclusion (exteriorBall_anti hR')) y i j) =ᶠ[𝓝 x]
        (fun y ↦ e.metricCoeff y i j) := eventually_of_mem
      ((exteriorBall (EuclideanSpace ℝ (Fin n)) R').isOpen.mem_nhds (mem_exteriorBall.2 hx))
      fun _ hy ↦ openPullbackMetricCoeff_comp_inclusion (exteriorBall_anti hR') e.toFun hy i j
    have h0 := hev.self_of_nhds; dsimp only at h0
    rw [h0, hev.fderiv_eq, hev.fderiv.fderiv_eq]; exact hC x (hR'.trans_lt hx) i j

@[simp]
theorem radius_restrictRadius : (e.restrictRadius hR').radius = R' := by rfl

@[simp]
theorem toFun_restrictRadius
    (x : exteriorBall (EuclideanSpace ℝ (Fin n)) (e.restrictRadius hR').radius) :
    (e.restrictRadius hR').toFun x = e.toFun ⟨x.1, mem_exteriorBall.2
      ((hR'.trans_eq (radius_restrictRadius e hR').symm).trans_lt (mem_exteriorBall.1 x.2))⟩ := by
  rfl

/-- The range of `e.restrictRadius hR'` is the image under `e.toFun` of `{R' < ‖x‖}`. -/
@[simp]
theorem range_restrictRadius :
    Set.range (e.restrictRadius hR').toFun =
      e.toFun '' {x : exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius | R' < ‖x.1‖} := by
  ext y; simp only [Set.mem_range, Set.mem_image, Set.mem_ofPred_eq]
  exact ⟨fun ⟨x, hx⟩ ↦ ⟨Opens.inclusion (exteriorBall_anti hR') x, mem_exteriorBall.1 x.2, hx⟩,
    fun ⟨x, hx, hxy⟩ ↦ ⟨⟨x.1, mem_exteriorBall.2 hx⟩, hxy⟩⟩

/-- Restricting the excised radius shrinks the range of the end. -/
theorem range_restrictRadius_subset :
    Set.range (e.restrictRadius hR').toFun ⊆ Set.range e.toFun := by
  change Set.range (e.toFun ∘ Opens.inclusion (exteriorBall_anti hR')) ⊆ Set.range e.toFun
  exact Set.range_comp_subset_range _ _

/-- Restricting the excised radius preserves `metricCoeff` on the smaller exterior domain. -/
theorem metricCoeff_restrictRadius {x : EuclideanSpace ℝ (Fin n)} (hx : R' < ‖x‖) (i j : Fin n) :
    (e.restrictRadius hR').metricCoeff x i j = e.metricCoeff x i j := by
  exact openPullbackMetricCoeff_comp_inclusion (exteriorBall_anti hR') e.toFun
    (mem_exteriorBall.2 hx) i j

/-- Restricting the excised radius preserves `metricMatrix` on the smaller exterior domain. -/
theorem metricMatrix_restrictRadius {x : EuclideanSpace ℝ (Fin n)} (hx : R' < ‖x‖) :
    (e.restrictRadius hR').metricMatrix x = e.metricMatrix x := by
  ext i j; exact e.metricCoeff_restrictRadius hR' hx i j

end RestrictRadius

section OfLe

variable {t' : ℝ} (ht : t' ≤ t)

/-- An asymptotically Euclidean end of order `t` is also an end of every smaller order `t' ≤ t`. -/
def ofLe : AsymptoticallyEuclideanEnd n I M t' where
  radius := e.radius; radius_pos := e.radius_pos; toFun := e.toFun; contMDiff := e.contMDiff
  injective := e.injective; mfderiv_bijective := e.mfderiv_bijective
  contDiffOn_openPullbackMetricCoeff := e.contDiffOn_openPullbackMetricCoeff
  decay := by
    obtain ⟨C, hC⟩ := e.decay
    refine ⟨max C 0 * e.radius ^ (t' - t), fun x hx i j ↦ ?_⟩
    have hx0 : 0 < ‖x‖ := e.radius_pos.trans hx
    have hpow := Real.rpow_le_rpow_of_nonpos e.radius_pos hx.le (sub_nonpos.2 ht)
    have hbound (a s : ℝ) (ha : a ≤ C * ‖x‖ ^ (-t - s)) :
        a ≤ max C 0 * e.radius ^ (t' - t) * ‖x‖ ^ (-t' - s) := by
      have h2 : ‖x‖ ^ (-t - s) = ‖x‖ ^ (t' - t) * ‖x‖ ^ (-t' - s) := by
        rw [← Real.rpow_add hx0]; congr 1; ring
      calc a ≤ max C 0 * ‖x‖ ^ (-t - s) :=
            ha.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg hx0.le _))
        _ = max C 0 * ‖x‖ ^ (t' - t) * ‖x‖ ^ (-t' - s) := by rw [h2, mul_assoc]
        _ ≤ max C 0 * e.radius ^ (t' - t) * ‖x‖ ^ (-t' - s) := by gcongr
    obtain ⟨h0, h1, h2⟩ := hC x hx i j
    exact ⟨by simpa only [sub_zero] using hbound _ 0 (by simpa only [sub_zero] using h0),
      hbound _ 1 h1, hbound _ 2 h2⟩

@[simp]
theorem radius_ofLe : (e.ofLe ht).radius = e.radius := by rfl

@[simp]
theorem toFun_ofLe (x : exteriorBall (EuclideanSpace ℝ (Fin n)) (e.ofLe ht).radius) :
    (e.ofLe ht).toFun x = e.toFun ⟨x.1, radius_ofLe e ht ▸ x.2⟩ := by rfl

@[simp]
theorem range_ofLe : Set.range (e.ofLe ht).toFun = Set.range e.toFun := by rfl

@[simp]
theorem metricCoeff_ofLe : (e.ofLe ht).metricCoeff = e.metricCoeff := by rfl

@[simp]
theorem metricMatrix_ofLe (x : EuclideanSpace ℝ (Fin n)) :
    (e.ofLe ht).metricMatrix x = e.metricMatrix x := by rfl

end OfLe

section TransRiemannianIsometry

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] (Φ : RiemannianIsometry I J M N)

/-- Push an asymptotically Euclidean end forward along a smooth Riemannian isometry. -/
def transRiemannianIsometry : AsymptoticallyEuclideanEnd n J N t where
  radius := e.radius; radius_pos := e.radius_pos; toFun := Φ ∘ e.toFun
  contMDiff := Φ.toDiffeomorph.contMDiff.comp e.contMDiff
  injective := Φ.injective.comp e.injective
  mfderiv_bijective x := by
    rw [mfderiv_comp x (Φ.mdifferentiableAt _) (e.contMDiff.mdifferentiable (by simp) x)]
    exact (Φ.toDiffeomorph.isInvertible_mfderiv (by simp)).bijective.comp (e.mfderiv_bijective x)
  contDiffOn_openPullbackMetricCoeff i j := by
    simpa only [openPullbackMetricCoeff_riemannianIsometry_comp] using
      e.contDiffOn_openPullbackMetricCoeff i j
  decay := by simpa only [openPullbackMetricCoeff_riemannianIsometry_comp] using e.decay

@[simp]
theorem radius_transRiemannianIsometry :
    (e.transRiemannianIsometry Φ).radius = e.radius := by rfl

@[simp]
theorem toFun_transRiemannianIsometry
    (x : exteriorBall (EuclideanSpace ℝ (Fin n)) (e.transRiemannianIsometry Φ).radius) :
    (e.transRiemannianIsometry Φ).toFun x =
      Φ (e.toFun ⟨x.1, radius_transRiemannianIsometry e Φ ▸ x.2⟩) := by rfl

/-- Pushing an end forward along a Riemannian isometry `Φ` maps its range by `Φ`. -/
@[simp]
theorem range_transRiemannianIsometry :
    Set.range (e.transRiemannianIsometry Φ).toFun = Φ '' Set.range e.toFun := by
  exact Set.range_comp Φ e.toFun

@[simp]
theorem metricCoeff_transRiemannianIsometry :
    (e.transRiemannianIsometry Φ).metricCoeff = e.metricCoeff := by
  exact openPullbackMetricCoeff_riemannianIsometry_comp e.toFun Φ

@[simp]
theorem metricMatrix_transRiemannianIsometry (x : EuclideanSpace ℝ (Fin n)) :
    (e.transRiemannianIsometry Φ).metricMatrix x = e.metricMatrix x := by
  ext i j; rw [metricMatrix_apply, metricMatrix_apply, metricCoeff_transRiemannianIsometry]

end TransRiemannianIsometry

/-! #### Flat Euclidean space -/

section Euclidean

variable (n : ℕ) {R : ℝ} (hR : 0 < R) (t : ℝ)

/-- The standard asymptotically Euclidean end on flat `EuclideanSpace ℝ (Fin n)` with excised
radius `R > 0`, of any order `t : ℝ`. -/
def euclidean : AsymptoticallyEuclideanEnd n (𝓡 n) (EuclideanSpace ℝ (Fin n)) t where
  radius := R; radius_pos := hR; toFun := Subtype.val
  contMDiff := contMDiff_subtype_val; injective := Subtype.val_injective
  mfderiv_bijective x := by
    rw [TauCeti.Manifold.mfderiv_subtype_val]
    exact (TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓡 n) x).bijective
  contDiffOn_openPullbackMetricCoeff i j :=
    (contDiffOn_const (c := if i = j then (1 : ℝ) else 0)).congr fun _ hy ↦
      openPullbackMetricCoeff_subtype_val hy i j
  decay := by
    refine ⟨0, fun x hx i j ↦ ?_⟩
    have hev : (fun y ↦ openPullbackMetricCoeff (𝓡 n)
          (Subtype.val : exteriorBall (EuclideanSpace ℝ (Fin n)) R → _) y i j) =ᶠ[𝓝 x]
        fun _ ↦ if i = j then (1 : ℝ) else 0 := eventually_of_mem
      ((exteriorBall (EuclideanSpace ℝ (Fin n)) R).isOpen.mem_nhds (mem_exteriorBall.2 hx))
      fun _ hy ↦ openPullbackMetricCoeff_subtype_val hy i j
    have hev1 : fderiv ℝ (fun y ↦ openPullbackMetricCoeff (𝓡 n)
          (Subtype.val : exteriorBall (EuclideanSpace ℝ (Fin n)) R → _) y i j) =ᶠ[𝓝 x]
        fun _ ↦ (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := by
      filter_upwards [hev.fderiv (𝕜 := ℝ)] with y hy; rw [hy, fderiv_const_apply]
    simp only [hev.self_of_nhds, hev.fderiv_eq, hev1.fderiv_eq, fderiv_const_apply, sub_self,
      abs_zero, zero_mul, ContinuousLinearMap.opNorm_zero, le_refl, and_self]

@[simp]
theorem radius_euclidean : (euclidean n hR t).radius = R := by rfl

@[simp]
theorem toFun_euclidean (x : exteriorBall (EuclideanSpace ℝ (Fin n)) (euclidean n hR t).radius) :
    (euclidean n hR t).toFun x = x.1 := by rfl

/-- The range of the standard flat Euclidean end is the exterior ball. -/
@[simp]
theorem range_euclidean :
    Set.range (euclidean n hR t).toFun =
      (exteriorBall (EuclideanSpace ℝ (Fin n)) R : Set (EuclideanSpace ℝ (Fin n))) := by
  exact Subtype.range_coe

/-- On `{x | R < ‖x‖}`, the pulled-back metric coefficients of `euclidean` are `δ_ij`. -/
theorem metricCoeff_euclidean {x : EuclideanSpace ℝ (Fin n)} (hx : R < ‖x‖) (i j : Fin n) :
    (euclidean n hR t).metricCoeff x i j = if i = j then 1 else 0 := by
  exact openPullbackMetricCoeff_subtype_val (mem_exteriorBall.2 hx) i j

/-- On `{x | R < ‖x‖}`, the pulled-back metric matrix of `euclidean` is the identity matrix. -/
theorem metricMatrix_euclidean {x : EuclideanSpace ℝ (Fin n)} (hx : R < ‖x‖) :
    (euclidean n hR t).metricMatrix x = 1 := by
  ext i j; rw [metricMatrix_apply, metricCoeff_euclidean n hR t hx i j, Matrix.one_apply]

end Euclidean

end AsymptoticallyEuclideanEnd

/-! ### Negative control: non-isometric dilations fail asymptotic decay -/

/-- A non-isometric dilation `x ↦ a • x` (`|a| ≠ 1`) on `ℝⁿ` (`1 ≤ n`) pulls the Euclidean metric
back to `a ^ 2 • δ_ij`, so its diagonal deviation `|a ^ 2 - 1| > 0` fails decay for `t > 0`. -/
theorem not_exists_decay_pullbackMetricCoeff_smul {n : ℕ} (hn : 1 ≤ n) {a R t : ℝ}
    (ha : |a| ≠ 1) (ht : 0 < t) :
    ¬ ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ → ∀ i j : Fin n,
      |pullbackMetricCoeff (𝓡 n) (fun y : EuclideanSpace ℝ (Fin n) ↦ a • y) x i j -
        if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) := by
  rintro ⟨C, hC⟩
  let i₀ : Fin n := ⟨0, hn⟩
  have hgap : 0 < |a ^ 2 - 1| :=
    abs_pos.2 (sub_ne_zero.2 fun h ↦ ha (by rw [← sq_abs] at h; nlinarith [abs_nonneg a]))
  have htend : Tendsto (fun r : ℝ ↦ C * r ^ (-t)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop ht).const_mul C
  obtain ⟨r, hrR, hrgap⟩ :=
    ((eventually_gt_atTop (max R 0)).and (htend.eventually (Iio_mem_nhds hgap))).exists
  have hnorm : ‖r • EuclideanSpace.basisFun (Fin n) ℝ i₀‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg ((le_max_right R 0).trans_lt hrR).le,
      (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.1 i₀, mul_one]
  have hbound := hC (r • EuclideanSpace.basisFun (Fin n) ℝ i₀)
    (hnorm.symm ▸ (le_max_left R 0).trans_lt hrR) i₀ i₀
  rw [pullbackMetricCoeff_smul, hnorm] at hbound
  exact not_lt_of_ge (by simpa only [↓reduceIte] using hbound) hrgap

/-- No asymptotically Euclidean end of positive order on flat `ℝⁿ` (`1 ≤ n`) can be given by a
non-isometric dilation `x ↦ a • x` (`|a| ≠ 1`). -/
theorem AsymptoticallyEuclideanEnd.toFun_ne_smul {n : ℕ} (hn : 1 ≤ n) {a t : ℝ} (ha : |a| ≠ 1)
    (ht : 0 < t) (e : AsymptoticallyEuclideanEnd n (𝓡 n) (EuclideanSpace ℝ (Fin n)) t) :
    ¬ ∀ x : exteriorBall (EuclideanSpace ℝ (Fin n)) e.radius,
      e.toFun x = a • (x : EuclideanSpace ℝ (Fin n)) := fun h ↦
  not_exists_decay_pullbackMetricCoeff_smul hn (R := e.radius) ha ht <| by
    obtain ⟨C, hC⟩ := e.decay
    refine ⟨C, fun x hx i j ↦ ?_⟩
    rw [← e.metricCoeff_eq_pullbackMetricCoeff_of_eqOn (fun y ↦ (h y).symm) hx i j]
    exact (hC x hx i j).1

end TauCeti

end
