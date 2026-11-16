/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.MFDeriv.Opens
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Asymptotically Euclidean ends

An **asymptotically Euclidean end** of order `t` of an `n`-dimensional Riemannian manifold `M` is
a smooth injective parametrization `φ : {x ∈ ℝⁿ | R < ‖x‖} → M` (`R > 0`) whose differential is
bijective at every point (hence a diffeomorphism onto its open image), such that the pulled-back
metric coefficients `g_ij(x) = ⟪dφ_x e_i, dφ_x e_j⟫` satisfy the second-order decay bounds

`|g_ij(x) - δ_ij| ≤ C ‖x‖ ^ (-t)`,
`‖D(g_ij)(x)‖ ≤ C ‖x‖ ^ (-t - 1)`,
`‖D²(g_ij)(x)‖ ≤ C ‖x‖ ^ (-t - 2)`

for all `‖x‖ > R` and all `i, j : Fin n`.

## Design notes

`AsymptoticallyEuclideanEnd` stores its parametrization as a map `exteriorBall n radius → M` on
the open exterior `exteriorBall n radius` rather than a total map `ℝⁿ → M`, so no unused values
on the excised ball `closedBall 0 radius` enter the structure. Its metric coefficients
`openPullbackMetricCoeff` are extended by `0` outside the open domain so that `fderiv` and
iterated `fderiv` act directly on `EuclideanSpace ℝ (Fin n) → ℝ` and agree at every interior
point with those of any global extension `pullbackMetricCoeff ψ`. Openness of the range is
derived from smoothness and bijectivity of the differential via the inverse function theorem
rather than stored as a redundant field.

## Main definitions

* `TauCeti.exteriorBall`: the open exterior `{x ∈ ℝⁿ | R < ‖x‖}` of the closed ball of radius
  `R`.
* `TauCeti.pullbackMetricCoeff` and `TauCeti.openPullbackMetricCoeff`: pulled-back metric
  coefficients of a total map `ℝⁿ → M` or a map on an open subset `U ⊆ ℝⁿ`.
* `TauCeti.AsymptoticallyEuclideanEnd`: an asymptotically Euclidean end of order `t`.
* `TauCeti.AsymptoticallyEuclideanEnd.partialDiffeomorph`: an end packaged as a `C^k` partial
  diffeomorphism from `ℝⁿ` to `M`.

## Main results

* `TauCeti.isPathConnected_exteriorBall`, `TauCeti.isConnected_exteriorBall`: for `2 ≤ n`, the
  exterior of every closed ball is path-connected and connected.
* `TauCeti.AsymptoticallyEuclideanEnd.isOpen_range`,
  `TauCeti.AsymptoticallyEuclideanEnd.isConnected_range`,
  `TauCeti.AsymptoticallyEuclideanEnd.riemannianJacobian_partialDiffeomorph`: topological,
  diffeomorphic, and Jacobian properties of an end.
* `TauCeti.AsymptoticallyEuclideanEnd.restrictRadius`,
  `TauCeti.AsymptoticallyEuclideanEnd.ofLe`,
  `TauCeti.AsymptoticallyEuclideanEnd.compRiemannianIsometry`: functoriality under shrinking the
  end, weakening the decay order, and pushing forward along a Riemannian isometry.
* `TauCeti.AsymptoticallyEuclideanEnd.euclidean`: flat Euclidean space is asymptotically Euclidean
  of every order.
* `TauCeti.not_exists_decay_pullbackMetricCoeff_smul`,
  `TauCeti.AsymptoticallyEuclideanEnd.toFun_ne_smul`: every non-isometric dilation `x ↦ a • x`
  (`|a| ≠ 1`) on `ℝⁿ` (`1 ≤ n`) fails the asymptotically Euclidean decay condition for every
  `t > 0`.

## References

* R. Bartnik, *The mass of an asymptotically flat manifold*, Comm. Pure Appl. Math. 39 (1986),
  661–693.
* S. Cecchini and R. Zeidler, *The positive mass theorem and distance estimates in the spin
  setting*, Ann. Global Anal. Geom. 63 (2023), Definition 2.1 and Definition 2.3.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Sections 8 and 9.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Manifold Matrix RealInnerProductSpace Topology

namespace TauCeti

/-! ### Exterior of a closed ball -/

section ExteriorBall

/-- The open exterior `{x ∈ ℝⁿ | R < ‖x‖}` of the closed ball of radius `R` around `0`. -/
def exteriorBall (n : ℕ) (R : ℝ) : Opens (EuclideanSpace ℝ (Fin n)) :=
  ⟨(closedBall 0 R)ᶜ, isClosed_closedBall.isOpen_compl⟩

@[simp]
theorem mem_exteriorBall {n : ℕ} {R : ℝ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ exteriorBall n R ↔ R < ‖x‖ := by
  simp [exteriorBall, mem_closedBall, dist_zero_right]

/-- The underlying set of `exteriorBall n R` is `{x | R < ‖x‖}`. -/
theorem coe_exteriorBall (n : ℕ) (R : ℝ) :
    (exteriorBall n R : Set (EuclideanSpace ℝ (Fin n))) = {x | R < ‖x‖} := by
  ext x
  exact mem_exteriorBall

/-- Increasing the excised radius shrinks the exterior ball. -/
theorem exteriorBall_anti {n : ℕ} {R₁ R₂ : ℝ} (h : R₁ ≤ R₂) :
    exteriorBall n R₂ ≤ exteriorBall n R₁ := fun _ hx ↦
  mem_exteriorBall.2 (h.trans_lt (mem_exteriorBall.1 hx))

/-- For `1 ≤ n`, the exterior of any closed ball in `ℝⁿ` is nonempty. -/
theorem nonempty_exteriorBall {n : ℕ} (hn : 1 ≤ n) (R : ℝ) :
    (exteriorBall n R : Set (EuclideanSpace ℝ (Fin n))).Nonempty := by
  let i₀ : Fin n := ⟨0, hn⟩
  refine ⟨(max R 0 + 1) • EuclideanSpace.basisFun (Fin n) ℝ i₀, mem_exteriorBall.2 ?_⟩
  have hpos : 0 < max R 0 + 1 := by positivity
  rw [norm_smul, Real.norm_of_nonneg hpos.le,
    (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.1 i₀, mul_one]
  linarith [le_max_left R 0]

/-- For `2 ≤ n`, the exterior of any closed ball in `ℝⁿ` is path-connected. -/
theorem isPathConnected_exteriorBall {n : ℕ} (hn : 2 ≤ n) (R : ℝ) :
    IsPathConnected (exteriorBall n R : Set (EuclideanSpace ℝ (Fin n))) := by
  rcases lt_or_ge R 0 with hR | hR
  · have huniv : (exteriorBall n R : Set (EuclideanSpace ℝ (Fin n))) = univ := by
      ext x
      simp [mem_exteriorBall, hR.trans_le (norm_nonneg x)]
    rw [huniv]
    exact isPathConnected_univ
  · have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
      rw [← finrank_eq_rank, finrank_euclideanSpace_fin]
      exact_mod_cast (by omega : 1 < n)
    have hprod : IsPathConnected (Ioi R ×ˢ sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
      (convex_Ioi R).isPathConnected nonempty_Ioi |>.prod
        (isPathConnected_sphere hrank 0 zero_le_one)
    have himage : (fun p : ℝ × EuclideanSpace ℝ (Fin n) ↦ p.1 • p.2) ''
        (Ioi R ×ˢ sphere (0 : EuclideanSpace ℝ (Fin n)) 1) =
        (exteriorBall n R : Set (EuclideanSpace ℝ (Fin n))) := by
      ext x
      constructor
      · rintro ⟨⟨r, u⟩, ⟨hr, hu⟩, rfl⟩
        rw [SetLike.mem_coe, mem_exteriorBall, norm_smul,
          Real.norm_of_nonneg (hR.trans_lt hr).le, mem_sphere_zero_iff_norm.1 hu, mul_one]
        exact hr
      · intro hx
        have hRx : R < ‖x‖ := mem_exteriorBall.1 hx
        have hx0 : 0 < ‖x‖ := hR.trans_lt hRx
        refine ⟨(‖x‖, ‖x‖⁻¹ • x), ⟨hRx, ?_⟩, smul_inv_smul₀ hx0.ne' x⟩
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hx0.le),
          inv_mul_cancel₀ hx0.ne']
    rw [← himage]
    exact hprod.image (continuous_fst.smul continuous_snd)

/-- For `2 ≤ n`, the exterior of any closed ball in `ℝⁿ` is connected. -/
theorem isConnected_exteriorBall {n : ℕ} (hn : 2 ≤ n) (R : ℝ) :
    IsConnected (exteriorBall n R : Set (EuclideanSpace ℝ (Fin n))) :=
  (isPathConnected_exteriorBall hn R).isConnected

end ExteriorBall

/-! ### Pulled-back metric coefficients -/

section PullbackMetricCoeff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)]

/-- The pulled-back metric coefficients `g_ij(x) = ⟪dφ_x e_i, dφ_x e_j⟫` of a total map
`φ : ℝⁿ → M` in the standard orthonormal basis of `ℝⁿ`. -/
def pullbackMetricCoeff (φ : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) : ℝ :=
  inner ℝ (mfderiv (𝓡 n) (𝓡 n) φ x (EuclideanSpace.basisFun (Fin n) ℝ i))
    (mfderiv (𝓡 n) (𝓡 n) φ x (EuclideanSpace.basisFun (Fin n) ℝ j))

/-- Unfolding lemma for `pullbackMetricCoeff`. -/
theorem pullbackMetricCoeff_def (φ : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff φ x i j =
      inner ℝ (mfderiv (𝓡 n) (𝓡 n) φ x (EuclideanSpace.basisFun (Fin n) ℝ i))
        (mfderiv (𝓡 n) (𝓡 n) φ x (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
  rfl

/-- Symmetry of the pulled-back metric coefficients of a total map. -/
theorem pullbackMetricCoeff_symm (φ : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    pullbackMetricCoeff φ x i j = pullbackMetricCoeff φ x j i :=
  real_inner_comm _ _

/-- The pulled-back metric coefficients of a map `φ : U → M` on an open subset `U ⊆ ℝⁿ`,
extended by `0` outside `U`. Because `U` is open, all derivatives at points of `U` agree with
those of any global extension of `φ`. -/
def openPullbackMetricCoeff {U : Opens (EuclideanSpace ℝ (Fin n))} (φ : U → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) : ℝ := by
  classical
  exact if hx : x ∈ U then
    inner ℝ (mfderiv (𝓡 n) (𝓡 n) φ ⟨x, hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ i))
      (mfderiv (𝓡 n) (𝓡 n) φ ⟨x, hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ j))
  else 0

/-- Evaluation of `openPullbackMetricCoeff` at a point inside the open domain `U`. -/
theorem openPullbackMetricCoeff_of_mem {U : Opens (EuclideanSpace ℝ (Fin n))} (φ : U → M)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) (i j : Fin n) :
    openPullbackMetricCoeff φ x i j =
      inner ℝ (mfderiv (𝓡 n) (𝓡 n) φ ⟨x, hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ i))
        (mfderiv (𝓡 n) (𝓡 n) φ ⟨x, hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
  classical
  simp [openPullbackMetricCoeff, hx]

/-- Outside the open domain `U`, `openPullbackMetricCoeff` vanishes by definition. -/
theorem openPullbackMetricCoeff_of_notMem {U : Opens (EuclideanSpace ℝ (Fin n))} (φ : U → M)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ U) (i j : Fin n) :
    openPullbackMetricCoeff φ x i j = 0 := by
  classical
  simp [openPullbackMetricCoeff, hx]

/-- Symmetry of the pulled-back metric coefficients on an open subset. -/
theorem openPullbackMetricCoeff_symm {U : Opens (EuclideanSpace ℝ (Fin n))} (φ : U → M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    openPullbackMetricCoeff φ x i j = openPullbackMetricCoeff φ x j i := by
  by_cases hx : x ∈ U
  · rw [openPullbackMetricCoeff_of_mem _ hx, openPullbackMetricCoeff_of_mem _ hx, real_inner_comm]
  · rw [openPullbackMetricCoeff_of_notMem _ hx, openPullbackMetricCoeff_of_notMem _ hx]

/-- If a total map `ψ : ℝⁿ → M` agrees with `φ : U → M` on the open set `U`, then their
pulled-back metric coefficients agree on `U`. -/
theorem openPullbackMetricCoeff_eq_pullbackMetricCoeff_of_eqOn
    {U : Opens (EuclideanSpace ℝ (Fin n))} {φ : U → M} {ψ : EuclideanSpace ℝ (Fin n) → M}
    (h : ∀ x : U, ψ x = φ x) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) (i j : Fin n) :
    openPullbackMetricCoeff φ x i j = pullbackMetricCoeff ψ x i j := by
  have hcomp : φ = ψ ∘ (Subtype.val : U → EuclideanSpace ℝ (Fin n)) :=
    funext fun y ↦ (h y).symm
  subst hcomp
  have hderiv (k : Fin n) :
      mfderiv (𝓡 n) (𝓡 n) (ψ ∘ (Subtype.val : U → _)) ⟨x, hx⟩
          (EuclideanSpace.basisFun (Fin n) ℝ k) =
        mfderiv (𝓡 n) (𝓡 n) ψ x (EuclideanSpace.basisFun (Fin n) ℝ k) :=
    TauCeti.Manifold.mfderiv_comp_subtype_val_apply (I := 𝓡 n) (J := 𝓡 n) (U := U) (f := ψ)
      (x := ⟨x, hx⟩) (EuclideanSpace.basisFun (Fin n) ℝ k)
  rw [openPullbackMetricCoeff_of_mem _ hx, pullbackMetricCoeff, hderiv i, hderiv j]

/-- Near any point of `U`, `openPullbackMetricCoeff φ` agrees with `pullbackMetricCoeff ψ` for any
global extension `ψ` of `φ`. -/
theorem openPullbackMetricCoeff_eventuallyEq_pullbackMetricCoeff
    {U : Opens (EuclideanSpace ℝ (Fin n))} {φ : U → M} {ψ : EuclideanSpace ℝ (Fin n) → M}
    (h : ∀ x : U, ψ x = φ x) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) (i j : Fin n) :
    (fun y ↦ openPullbackMetricCoeff φ y i j) =ᶠ[𝓝 x]
      (fun y ↦ pullbackMetricCoeff ψ y i j) :=
  eventually_of_mem (U.isOpen.mem_nhds hx) fun _ hy ↦
    openPullbackMetricCoeff_eq_pullbackMetricCoeff_of_eqOn h hy i j

/-- Restricting a map `φ : U → M` to a smaller open subset `V ≤ U` preserves its pulled-back
metric coefficients on `V`. -/
theorem openPullbackMetricCoeff_comp_inclusion {U V : Opens (EuclideanSpace ℝ (Fin n))}
    (hVU : V ≤ U) (φ : U → M) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ V) (i j : Fin n) :
    openPullbackMetricCoeff (φ ∘ Opens.inclusion hVU) x i j =
      openPullbackMetricCoeff φ x i j := by
  classical
  let ψ : EuclideanSpace ℝ (Fin n) → M :=
    fun y ↦ if hy : y ∈ U then φ ⟨y, hy⟩ else φ ⟨x, hVU hx⟩
  have hψU : ∀ y : U, ψ y = φ y := fun y ↦ by simp [ψ, y.2]
  have hψV : ∀ y : V, ψ y = (φ ∘ Opens.inclusion hVU) y := fun y ↦ by simp [ψ, hVU y.2]
  rw [openPullbackMetricCoeff_eq_pullbackMetricCoeff_of_eqOn hψV hx,
    openPullbackMetricCoeff_eq_pullbackMetricCoeff_of_eqOn hψU (hVU hx)]

/-- Postcomposing a differentiable map `φ : U → M` with a Riemannian isometry preserves its
pulled-back metric coefficients. -/
theorem openPullbackMetricCoeff_comp_riemannianIsometry {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [RiemannianBundle (fun y : N ↦ TangentSpace (𝓡 n) y)]
    {U : Opens (EuclideanSpace ℝ (Fin n))} {φ : U → M}
    (hφ : MDifferentiable (𝓡 n) (𝓡 n) φ) (Φ : RiemannianIsometry (𝓡 n) (𝓡 n) M N) :
    openPullbackMetricCoeff (Φ ∘ φ) = openPullbackMetricCoeff φ := by
  funext x i j
  by_cases hx : x ∈ U
  · have hderiv (k : Fin n) :
        mfderiv (𝓡 n) (𝓡 n) (Φ ∘ φ) ⟨x, hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ k) =
          mfderiv (𝓡 n) (𝓡 n) Φ (φ ⟨x, hx⟩)
            (mfderiv (𝓡 n) (𝓡 n) φ ⟨x, hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ k)) :=
      mfderiv_comp_apply (I := 𝓡 n) (I' := 𝓡 n) (I'' := 𝓡 n) ⟨x, hx⟩
        (Φ.mdifferentiableAt _) (hφ _) (EuclideanSpace.basisFun (Fin n) ℝ k)
    rw [openPullbackMetricCoeff_of_mem _ hx, openPullbackMetricCoeff_of_mem _ hx,
      hderiv i, hderiv j, Φ.inner_mfderiv]
  · rw [openPullbackMetricCoeff_of_notMem _ hx, openPullbackMetricCoeff_of_notMem _ hx]

/-- On an open subset `U ⊆ ℝⁿ`, the pulled-back metric coefficients of the canonical inclusion
`Subtype.val : U → ℝⁿ` are the Kronecker delta `δ_ij`. -/
theorem openPullbackMetricCoeff_subtype_val {U : Opens (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) (i j : Fin n) :
    openPullbackMetricCoeff (Subtype.val : U → EuclideanSpace ℝ (Fin n)) x i j =
      if i = j then 1 else 0 := by
  have hderiv (k : Fin n) :
      mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⟨x, hx⟩
        (EuclideanSpace.basisFun (Fin n) ℝ k) = EuclideanSpace.basisFun (Fin n) ℝ k := by
    rw [TauCeti.Manifold.mfderiv_subtype_val]
    exact TauCeti.Manifold.tangentSpaceOpenEquiv_apply (I := 𝓡 n) ⟨x, hx⟩
      (EuclideanSpace.basisFun (Fin n) ℝ k)
  rw [openPullbackMetricCoeff_of_mem _ hx, hderiv i, hderiv j]
  exact orthonormal_iff_ite.1 (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal i j

/-- The pulled-back metric coefficients of a `C^k` map `φ : U → M` into a `C^m` Riemannian
manifold (`m + 1 ≤ k`) are `C^m` on `U`. -/
theorem contDiffOn_openPullbackMetricCoeff [IsManifold (𝓡 n) 1 M] {m k : ℕ∞ω}
    [IsContMDiffRiemannianBundle (𝓡 n) m (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x)]
    {U : Opens (EuclideanSpace ℝ (Fin n))} {φ : U → M} (hφ : ContMDiff (𝓡 n) (𝓡 n) k φ)
    (hmk : m + 1 ≤ k) (i j : Fin n) :
    ContDiffOn ℝ m (fun x ↦ openPullbackMetricCoeff φ x i j) (U : Set _) := by
  rcases Set.eq_empty_or_nonempty (U : Set (EuclideanSpace ℝ (Fin n))) with hU | ⟨x₀, hx₀⟩
  · rw [hU]
    exact contDiffOn_empty
  · classical
    let ψ : EuclideanSpace ℝ (Fin n) → M := fun y ↦
      if hy : y ∈ U then φ ⟨y, hy⟩ else φ ⟨x₀, hx₀⟩
    have hψU : ∀ y : U, ψ y = φ y := fun y ↦ by simp [ψ, y.2]
    have hψ : ContMDiffOn (𝓡 n) (𝓡 n) k ψ (U : Set _) := fun y hy ↦ by
      have heq : (fun z : U ↦ ψ z) = φ := funext hψU
      have hsub : ContMDiffAt (𝓡 n) (𝓡 n) k ψ y :=
        (contMDiffAt_subtype_iff (I := 𝓡 n) (I' := 𝓡 n) (U := U) (f := ψ)
          (x := ⟨y, hy⟩)).1 (heq.symm ▸ hφ.contMDiffAt)
      exact hsub.contMDiffWithinAt
    have hcont := hψ.contDiffOn_inner_mfderiv hmk U.isOpen
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)
    exact hcont.congr fun y hy ↦
      openPullbackMetricCoeff_eq_pullbackMetricCoeff_of_eqOn hψU hy i j

end PullbackMetricCoeff

/-! ### Asymptotically Euclidean ends -/

/-- An **asymptotically Euclidean end** of order `t` of an `n`-dimensional Riemannian manifold
`M`: a smooth injective parametrization of an open subset of `M` by `exteriorBall n radius`
(`0 < radius`) with bijective differential everywhere, whose pulled-back metric coefficients
satisfy the second-order decay bounds `|∂^α (g_ij - δ_ij)| ≤ C ‖x‖ ^ (-t - |α|)` for `|α| ≤ 2`. -/
structure AsymptoticallyEuclideanEnd (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] (t : ℝ) where
  /-- The radius of the excised coordinate ball. -/
  radius : ℝ
  /-- The excised radius is positive. -/
  radius_pos : 0 < radius
  /-- The end parametrization on the open exterior `{x | radius < ‖x‖}`. -/
  toFun : exteriorBall n radius → M
  /-- Smoothness of the end parametrization. -/
  contMDiff : ContMDiff (𝓡 n) (𝓡 n) ∞ toFun
  /-- Injectivity of the end parametrization. -/
  injective : Function.Injective toFun
  /-- Bijectivity of the differential at every point of the end. -/
  mfderiv_bijective : ∀ x : exteriorBall n radius,
    Function.Bijective (mfderiv (𝓡 n) (𝓡 n) toFun x)
  /-- Second-order asymptotically Euclidean decay of the pulled-back metric coefficients. -/
  decay : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), radius < ‖x‖ → ∀ i j : Fin n,
    |openPullbackMetricCoeff toFun x i j - if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) ∧
    ‖fderiv ℝ (fun y ↦ openPullbackMetricCoeff toFun y i j) x‖ ≤
      C * ‖x‖ ^ (-t - 1) ∧
    ‖fderiv ℝ (fderiv ℝ (fun y ↦ openPullbackMetricCoeff toFun y i j)) x‖ ≤
      C * ‖x‖ ^ (-t - 2)

namespace AsymptoticallyEuclideanEnd

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] {t : ℝ}

/-- Two asymptotically Euclidean ends are equal if they have the same excised radius and agree
pointwise on their common exterior domain. -/
@[ext (iff := false)]
theorem ext {e₁ e₂ : AsymptoticallyEuclideanEnd n M t}
    (hr : e₁.radius = e₂.radius)
    (hf : ∀ (x : EuclideanSpace ℝ (Fin n)) (h₁ : e₁.radius < ‖x‖)
      (h₂ : e₂.radius < ‖x‖),
      e₁.toFun ⟨x, mem_exteriorBall.2 h₁⟩ = e₂.toFun ⟨x, mem_exteriorBall.2 h₂⟩) :
    e₁ = e₂ := by
  cases e₁
  cases e₂
  dsimp only at hr hf
  subst hr
  congr 1
  funext ⟨x, hx⟩
  exact hf x (mem_exteriorBall.1 hx) (mem_exteriorBall.1 hx)

/-- The pulled-back metric coefficients of an asymptotically Euclidean end, extended by `0` on
`closedBall 0 e.radius`. -/
def metricCoeff (e : AsymptoticallyEuclideanEnd n M t) :
    EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ :=
  openPullbackMetricCoeff e.toFun

/-- Unfolding lemma for `metricCoeff` in terms of `openPullbackMetricCoeff`. -/
theorem metricCoeff_eq_openPullbackMetricCoeff (e : AsymptoticallyEuclideanEnd n M t) :
    e.metricCoeff = openPullbackMetricCoeff e.toFun := by
  rfl

/-- Evaluation of `e.metricCoeff` at a point in `exteriorBall n e.radius`. -/
theorem metricCoeff_of_mem (e : AsymptoticallyEuclideanEnd n M t)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ exteriorBall n e.radius) (i j : Fin n) :
    e.metricCoeff x i j =
      inner ℝ
        (mfderiv (𝓡 n) (𝓡 n) e.toFun ⟨x, hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ i))
        (mfderiv (𝓡 n) (𝓡 n) e.toFun ⟨x, hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ j)) :=
  openPullbackMetricCoeff_of_mem e.toFun hx i j

/-- Outside `exteriorBall n e.radius`, `e.metricCoeff` vanishes by definition. -/
theorem metricCoeff_of_notMem (e : AsymptoticallyEuclideanEnd n M t)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ exteriorBall n e.radius) (i j : Fin n) :
    e.metricCoeff x i j = 0 :=
  openPullbackMetricCoeff_of_notMem e.toFun hx i j

/-- The pulled-back metric matrix of an asymptotically Euclidean end at `x`. -/
def metricMatrix (e : AsymptoticallyEuclideanEnd n M t) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (e.metricCoeff x)

/-- Symmetry of the pulled-back metric coefficients of an end. -/
theorem metricCoeff_symm (e : AsymptoticallyEuclideanEnd n M t)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    e.metricCoeff x i j = e.metricCoeff x j i :=
  openPullbackMetricCoeff_symm e.toFun x i j

@[simp]
theorem metricMatrix_apply (e : AsymptoticallyEuclideanEnd n M t)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    e.metricMatrix x i j = e.metricCoeff x i j := by
  rfl

@[simp]
theorem metricMatrix_transpose (e : AsymptoticallyEuclideanEnd n M t)
    (x : EuclideanSpace ℝ (Fin n)) :
    (e.metricMatrix x)ᵀ = e.metricMatrix x := by
  ext i j
  exact e.metricCoeff_symm x j i

/-- For any global map `ψ : ℝⁿ → M` agreeing with `e.toFun` on `exteriorBall n e.radius`,
`e.metricCoeff` agrees with `pullbackMetricCoeff ψ` on `exteriorBall n e.radius`. -/
theorem metricCoeff_eq_pullbackMetricCoeff_of_eqOn (e : AsymptoticallyEuclideanEnd n M t)
    {ψ : EuclideanSpace ℝ (Fin n) → M} (h : ∀ x : exteriorBall n e.radius, ψ x = e.toFun x)
    {x : EuclideanSpace ℝ (Fin n)} (hx : e.radius < ‖x‖) (i j : Fin n) :
    e.metricCoeff x i j = pullbackMetricCoeff ψ x i j :=
  openPullbackMetricCoeff_eq_pullbackMetricCoeff_of_eqOn h (mem_exteriorBall.2 hx) i j

/-- Near any point of `exteriorBall n e.radius`, `e.metricCoeff` agrees with
`pullbackMetricCoeff ψ` for any global extension `ψ` of `e.toFun`. -/
theorem metricCoeff_eventuallyEq_pullbackMetricCoeff (e : AsymptoticallyEuclideanEnd n M t)
    {ψ : EuclideanSpace ℝ (Fin n) → M} (h : ∀ x : exteriorBall n e.radius, ψ x = e.toFun x)
    {x : EuclideanSpace ℝ (Fin n)} (hx : e.radius < ‖x‖) (i j : Fin n) :
    (fun y ↦ e.metricCoeff y i j) =ᶠ[𝓝 x] (fun y ↦ pullbackMetricCoeff ψ y i j) :=
  openPullbackMetricCoeff_eventuallyEq_pullbackMetricCoeff h (mem_exteriorBall.2 hx) i j

/-- Construct an asymptotically Euclidean end from a total map `ψ : ℝⁿ → M` satisfying the
smooth embedding and decay conditions on `{x | R < ‖x‖}`. -/
def ofTotal {R : ℝ} (hR : 0 < R) (ψ : EuclideanSpace ℝ (Fin n) → M)
    (hdiff : ContMDiffOn (𝓡 n) (𝓡 n) ∞ ψ {x | R < ‖x‖})
    (hinj : InjOn ψ {x | R < ‖x‖})
    (hbij : ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ →
      Function.Bijective (mfderiv (𝓡 n) (𝓡 n) ψ x))
    (hdecay : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ → ∀ i j : Fin n,
      |pullbackMetricCoeff ψ x i j - if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) ∧
      ‖fderiv ℝ (fun y ↦ pullbackMetricCoeff ψ y i j) x‖ ≤ C * ‖x‖ ^ (-t - 1) ∧
      ‖fderiv ℝ (fderiv ℝ (fun y ↦ pullbackMetricCoeff ψ y i j)) x‖ ≤
        C * ‖x‖ ^ (-t - 2)) :
    AsymptoticallyEuclideanEnd n M t where
  radius := R
  radius_pos := hR
  toFun := ψ ∘ Subtype.val
  contMDiff := fun x ↦ by
    have hmem : {y : EuclideanSpace ℝ (Fin n) | R < ‖y‖} ∈
        𝓝 (x : EuclideanSpace ℝ (Fin n)) := by
      rw [← coe_exteriorBall n R]
      exact (exteriorBall n R).isOpen.mem_nhds x.2
    exact (contMDiffAt_subtype_iff (I := 𝓡 n) (I' := 𝓡 n) (U := exteriorBall n R)
      (f := ψ) (x := x)).2 (hdiff.contMDiffAt hmem)
  injective := fun x y hxy ↦
    Subtype.ext (hinj (mem_exteriorBall.1 x.2) (mem_exteriorBall.1 y.2) hxy)
  mfderiv_bijective := fun x ↦ by
    have h := hbij x.1 (mem_exteriorBall.1 x.2)
    have hfun : ⇑(mfderiv (𝓡 n) (𝓡 n) (ψ ∘ (Subtype.val : exteriorBall n R → _)) x) =
        ⇑(mfderiv (𝓡 n) (𝓡 n) ψ x.1) := funext fun v ↦
      TauCeti.Manifold.mfderiv_comp_subtype_val_apply (I := 𝓡 n) (J := 𝓡 n) (x := x) v
    rwa [hfun]
  decay := by
    obtain ⟨C, hC⟩ := hdecay
    refine ⟨C, fun x hx i j ↦ ?_⟩
    have hev : (fun y ↦
          openPullbackMetricCoeff (ψ ∘ (Subtype.val : exteriorBall n R → _)) y i j) =ᶠ[𝓝 x]
        (fun y ↦ pullbackMetricCoeff ψ y i j) :=
      openPullbackMetricCoeff_eventuallyEq_pullbackMetricCoeff (fun _ ↦ rfl)
        (mem_exteriorBall.2 hx) i j
    have h0 : openPullbackMetricCoeff (ψ ∘ (Subtype.val : exteriorBall n R → _)) x i j =
        pullbackMetricCoeff ψ x i j := hev.self_of_nhds
    rw [h0, hev.fderiv_eq, hev.fderiv.fderiv_eq]
    exact hC x hx i j

@[simp]
theorem radius_ofTotal {R : ℝ} (hR : 0 < R) (ψ : EuclideanSpace ℝ (Fin n) → M)
    (hdiff : ContMDiffOn (𝓡 n) (𝓡 n) ∞ ψ {x | R < ‖x‖})
    (hinj : InjOn ψ {x | R < ‖x‖})
    (hbij : ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ →
      Function.Bijective (mfderiv (𝓡 n) (𝓡 n) ψ x))
    (hdecay : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ → ∀ i j : Fin n,
      |pullbackMetricCoeff ψ x i j - if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) ∧
      ‖fderiv ℝ (fun y ↦ pullbackMetricCoeff ψ y i j) x‖ ≤ C * ‖x‖ ^ (-t - 1) ∧
      ‖fderiv ℝ (fderiv ℝ (fun y ↦ pullbackMetricCoeff ψ y i j)) x‖ ≤
        C * ‖x‖ ^ (-t - 2)) :
    (ofTotal (t := t) hR ψ hdiff hinj hbij hdecay).radius = R := by
  rfl

@[simp]
theorem toFun_ofTotal {R : ℝ} (hR : 0 < R) (ψ : EuclideanSpace ℝ (Fin n) → M)
    (hdiff : ContMDiffOn (𝓡 n) (𝓡 n) ∞ ψ {x | R < ‖x‖})
    (hinj : InjOn ψ {x | R < ‖x‖})
    (hbij : ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ →
      Function.Bijective (mfderiv (𝓡 n) (𝓡 n) ψ x))
    (hdecay : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ → ∀ i j : Fin n,
      |pullbackMetricCoeff ψ x i j - if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) ∧
      ‖fderiv ℝ (fun y ↦ pullbackMetricCoeff ψ y i j) x‖ ≤ C * ‖x‖ ^ (-t - 1) ∧
      ‖fderiv ℝ (fderiv ℝ (fun y ↦ pullbackMetricCoeff ψ y i j)) x‖ ≤
        C * ‖x‖ ^ (-t - 2))
    (x : exteriorBall n (ofTotal (t := t) hR ψ hdiff hinj hbij hdecay).radius) :
    (ofTotal (t := t) hR ψ hdiff hinj hbij hdecay).toFun x = ψ x.1 := by
  rfl

/-- The pulled-back metric coefficients of `ofTotal` agree with `pullbackMetricCoeff ψ` on
`{x | R < ‖x‖}`. -/
theorem metricCoeff_ofTotal {R : ℝ} (hR : 0 < R) (ψ : EuclideanSpace ℝ (Fin n) → M)
    (hdiff : ContMDiffOn (𝓡 n) (𝓡 n) ∞ ψ {x | R < ‖x‖})
    (hinj : InjOn ψ {x | R < ‖x‖})
    (hbij : ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ →
      Function.Bijective (mfderiv (𝓡 n) (𝓡 n) ψ x))
    (hdecay : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ → ∀ i j : Fin n,
      |pullbackMetricCoeff ψ x i j - if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) ∧
      ‖fderiv ℝ (fun y ↦ pullbackMetricCoeff ψ y i j) x‖ ≤ C * ‖x‖ ^ (-t - 1) ∧
      ‖fderiv ℝ (fderiv ℝ (fun y ↦ pullbackMetricCoeff ψ y i j)) x‖ ≤
        C * ‖x‖ ^ (-t - 2))
    {x : EuclideanSpace ℝ (Fin n)} (hx : R < ‖x‖) (i j : Fin n) :
    (ofTotal (t := t) hR ψ hdiff hinj hbij hdecay).metricCoeff x i j =
      pullbackMetricCoeff ψ x i j :=
  openPullbackMetricCoeff_eq_pullbackMetricCoeff_of_eqOn (fun _ ↦ rfl) (mem_exteriorBall.2 hx) i j

/-- The pulled-back metric coefficients of an end are `C^m` on the exterior domain whenever the
manifold is `C¹` and the metric is `C^m` with `m ≤ ∞`. -/
theorem contDiffOn_metricCoeff [IsManifold (𝓡 n) 1 M] {m : ℕ∞ω} (hm : m ≤ ∞)
    [IsContMDiffRiemannianBundle (𝓡 n) m (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x)]
    (e : AsymptoticallyEuclideanEnd n M t) (i j : Fin n) :
    ContDiffOn ℝ m (fun x ↦ e.metricCoeff x i j) (exteriorBall n e.radius : Set _) := by
  have hm1 : m + 1 ≤ ∞ := by
    cases m with
    | top => exact absurd hm (by decide)
    | coe a => exact WithTop.coe_le_coe.2 le_top
  exact contDiffOn_openPullbackMetricCoeff e.contMDiff hm1 i j

/-- An end parametrization is a `C^k` local diffeomorphism for every `1 ≤ k ≤ ∞`. -/
theorem isLocalDiffeomorph {k : ℕ∞ω} (hk1 : 1 ≤ k) (hk : k ≤ ∞) [IsManifold (𝓡 n) k M]
    (e : AsymptoticallyEuclideanEnd n M t) :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) k e.toFun := fun x ↦
  isLocalDiffeomorphAt_of_injective_mfderiv (e.contMDiff.of_le hk).contMDiffOn isOpen_univ
    (mem_univ x) BoundarylessManifold.isInteriorPoint hk1 (e.mfderiv_bijective x).1 rfl

/-- The range of an asymptotically Euclidean end is open in `M`. -/
theorem isOpen_range [IsManifold (𝓡 n) 1 M] (e : AsymptoticallyEuclideanEnd n M t) :
    IsOpen (Set.range e.toFun) :=
  (e.isLocalDiffeomorph le_rfl (by simp)).isLocalHomeomorph.isOpenMap.isOpen_range

/-- For `2 ≤ n`, the range of an asymptotically Euclidean end is connected. -/
theorem isConnected_range (hn : 2 ≤ n) (e : AsymptoticallyEuclideanEnd n M t) :
    IsConnected (Set.range e.toFun) := by
  have : ConnectedSpace (exteriorBall n e.radius) :=
    Subtype.connectedSpace (isConnected_exteriorBall hn e.radius)
  exact _root_.isConnected_range e.contMDiff.continuous

/-- For `1 ≤ n`, the manifold carrying an asymptotically Euclidean end is nonempty. -/
theorem nonempty_of_pos (hn : 1 ≤ n) (e : AsymptoticallyEuclideanEnd n M t) : Nonempty M := by
  obtain ⟨x, hx⟩ := nonempty_exteriorBall hn e.radius
  exact ⟨e.toFun ⟨x, hx⟩⟩

open Classical in
/-- Auxiliary total extension of `e.toFun` to `ℝⁿ` agreeing with `e.toFun` on the exterior
ball. -/
private def extendFun [Nonempty M] (e : AsymptoticallyEuclideanEnd n M t) :
    EuclideanSpace ℝ (Fin n) → M :=
  fun x ↦
    if hx : x ∈ exteriorBall n e.radius then e.toFun ⟨x, hx⟩ else Classical.arbitrary M

private theorem isLocalDiffeomorphOn_extendFun [Nonempty M] {k : ℕ∞ω} (hk1 : 1 ≤ k)
    (hk : k ≤ ∞) [IsManifold (𝓡 n) k M] (e : AsymptoticallyEuclideanEnd n M t) :
    IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) k e.extendFun (exteriorBall n e.radius : Set _) := by
  rintro ⟨x, hx⟩
  have hψU : ∀ z : exteriorBall n e.radius, e.extendFun z = e.toFun z := fun z ↦ by
    simp only [extendFun, z.2, ↓reduceDIte]
  have hψ : ContMDiffOn (𝓡 n) (𝓡 n) k e.extendFun (exteriorBall n e.radius : Set _) :=
    fun y hy ↦ by
      have heq : (fun z : exteriorBall n e.radius ↦ e.extendFun z) = e.toFun := funext hψU
      exact ((contMDiffAt_subtype_iff (I := 𝓡 n) (I' := 𝓡 n) (U := exteriorBall n e.radius)
        (f := e.extendFun) (x := ⟨y, hy⟩)).1 (heq.symm ▸ (e.contMDiff.of_le hk).contMDiffAt))
          |>.contMDiffWithinAt
  have hinj : Function.Injective (mfderiv (𝓡 n) (𝓡 n) e.extendFun x) := by
    have heq : e.extendFun ∘ (Subtype.val : exteriorBall n e.radius → _) = e.toFun :=
      funext hψU
    have h := (e.mfderiv_bijective ⟨x, hx⟩).1
    rw [← heq] at h
    have hfun : ⇑(mfderiv (𝓡 n) (𝓡 n)
          (e.extendFun ∘ (Subtype.val : exteriorBall n e.radius → _)) ⟨x, hx⟩) =
        ⇑(mfderiv (𝓡 n) (𝓡 n) e.extendFun x) := funext fun v ↦
      TauCeti.Manifold.mfderiv_comp_subtype_val_apply (I := 𝓡 n) (J := 𝓡 n) (x := ⟨x, hx⟩) v
    rwa [hfun] at h
  exact isLocalDiffeomorphAt_of_injective_mfderiv hψ (exteriorBall n e.radius).isOpen hx
    BoundarylessManifold.isInteriorPoint hk1 hinj rfl

private theorem injOn_extendFun [Nonempty M] (e : AsymptoticallyEuclideanEnd n M t) :
    Set.InjOn e.extendFun (exteriorBall n e.radius : Set _) := fun x hx y hy hxy ↦ by
  rw [SetLike.mem_coe] at hx hy
  simp only [extendFun, hx, hy, ↓reduceDIte] at hxy
  exact congrArg Subtype.val (e.injective hxy)

/-- An asymptotically Euclidean end packaged as a `C^k` partial diffeomorphism from `ℝⁿ` to `M`
with source `exteriorBall n e.radius` and target `Set.range e.toFun`. -/
def partialDiffeomorph [Nonempty M] {k : ℕ∞ω} (hk1 : 1 ≤ k) (hk : k ≤ ∞)
    [IsManifold (𝓡 n) k M] (e : AsymptoticallyEuclideanEnd n M t) :
    PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M k :=
  (e.isLocalDiffeomorphOn_extendFun hk1 hk).partialDiffeomorphOfInjOn
    (exteriorBall n e.radius).isOpen e.injOn_extendFun

@[simp]
theorem partialDiffeomorph_source [Nonempty M] {k : ℕ∞ω} (hk1 : 1 ≤ k) (hk : k ≤ ∞)
    [IsManifold (𝓡 n) k M] (e : AsymptoticallyEuclideanEnd n M t) :
    (e.partialDiffeomorph hk1 hk).source = (exteriorBall n e.radius : Set _) := by
  rw [partialDiffeomorph, IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source]

@[simp]
theorem partialDiffeomorph_target [Nonempty M] {k : ℕ∞ω} (hk1 : 1 ≤ k) (hk : k ≤ ∞)
    [IsManifold (𝓡 n) k M] (e : AsymptoticallyEuclideanEnd n M t) :
    (e.partialDiffeomorph hk1 hk).target = Set.range e.toFun := by
  rw [partialDiffeomorph, IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_target]
  ext y
  simp only [mem_image, mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe] at hx
    exact ⟨⟨x, hx⟩, by simp only [extendFun, hx, ↓reduceDIte]⟩
  · rintro ⟨⟨x, hx⟩, rfl⟩
    exact ⟨x, hx, by simp only [extendFun, hx, ↓reduceDIte]⟩

/-- On `exteriorBall n e.radius`, `e.partialDiffeomorph` agrees with `e.toFun`. -/
theorem partialDiffeomorph_apply_of_mem [Nonempty M] {k : ℕ∞ω} (hk1 : 1 ≤ k) (hk : k ≤ ∞)
    [IsManifold (𝓡 n) k M] (e : AsymptoticallyEuclideanEnd n M t)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ exteriorBall n e.radius) :
    e.partialDiffeomorph hk1 hk x = e.toFun ⟨x, hx⟩ := by
  rw [partialDiffeomorph, IsLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn]
  simp only [extendFun, hx, ↓reduceDIte]

/-- At every point of the end, the Riemannian Jacobian of `e.partialDiffeomorph` in the standard
basis of `ℝⁿ` is `√(det (e.metricMatrix x))`. -/
theorem riemannianJacobian_partialDiffeomorph [Nonempty M] {k : ℕ∞ω} (hk1 : 1 ≤ k)
    (hk : k ≤ ∞) [IsManifold (𝓡 n) k M] (e : AsymptoticallyEuclideanEnd n M t)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ exteriorBall n e.radius) :
    riemannianJacobian (I := 𝓡 n) (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (e.partialDiffeomorph hk1 hk) x = Real.sqrt (e.metricMatrix x).det := by
  rw [riemannianJacobian_eq_sqrt_det_gram]
  congr 2
  ext i j
  rw [Matrix.gram_apply, OrthonormalBasis.coe_toBasis, metricMatrix_apply]
  exact (e.metricCoeff_eq_pullbackMetricCoeff_of_eqOn
    (fun y ↦ e.partialDiffeomorph_apply_of_mem hk1 hk y.2) (mem_exteriorBall.1 hx) i j).symm

/-! #### Functoriality -/

/-- Restrict an asymptotically Euclidean end to a larger excised radius `R' ≥ e.radius`. -/
def restrictRadius (e : AsymptoticallyEuclideanEnd n M t) {R' : ℝ} (hR' : e.radius ≤ R') :
    AsymptoticallyEuclideanEnd n M t where
  radius := R'
  radius_pos := e.radius_pos.trans_le hR'
  toFun := e.toFun ∘ Opens.inclusion (exteriorBall_anti hR')
  contMDiff := e.contMDiff.comp <|
    (TauCeti.ContMDiff.subtypeVal_comp_iff (exteriorBall n e.radius)
      (Opens.inclusion (exteriorBall_anti hR'))).1 contMDiff_subtype_val
  injective := e.injective.comp fun _ _ h ↦
    Subtype.ext (congrArg (Subtype.val : exteriorBall n e.radius → _) h)
  mfderiv_bijective := fun x ↦ by
    have hinc_diff : ContMDiff (𝓡 n) (𝓡 n) ∞ (Opens.inclusion (exteriorBall_anti hR')) :=
      (TauCeti.ContMDiff.subtypeVal_comp_iff (exteriorBall n e.radius)
        (Opens.inclusion (exteriorBall_anti hR'))).1 contMDiff_subtype_val
    have hinc_bij : Function.Bijective
        (mfderiv (𝓡 n) (𝓡 n) (Opens.inclusion (exteriorBall_anti hR')) x) :=
      ⟨fun u v huv ↦ by
          rw [TauCeti.Manifold.mfderiv_inclusion_apply,
            TauCeti.Manifold.mfderiv_inclusion_apply] at huv
          exact huv,
        fun v ↦ ⟨v, TauCeti.Manifold.mfderiv_inclusion_apply (exteriorBall_anti hR') x v⟩⟩
    rw [mfderiv_comp x (e.contMDiff.mdifferentiable (by simp) _)
      (hinc_diff.mdifferentiable (by simp) x)]
    exact (e.mfderiv_bijective (Opens.inclusion (exteriorBall_anti hR') x)).comp hinc_bij
  decay := by
    obtain ⟨C, hC⟩ := e.decay
    refine ⟨C, fun x hx i j ↦ ?_⟩
    have hx' : e.radius < ‖x‖ := hR'.trans_lt hx
    have hev : (fun y ↦ openPullbackMetricCoeff
        (e.toFun ∘ Opens.inclusion (exteriorBall_anti hR')) y i j) =ᶠ[𝓝 x]
        (fun y ↦ e.metricCoeff y i j) :=
      eventually_of_mem ((exteriorBall n R').isOpen.mem_nhds (mem_exteriorBall.2 hx)) fun y hy ↦
        openPullbackMetricCoeff_comp_inclusion (exteriorBall_anti hR') e.toFun hy i j
    have h0 :
        openPullbackMetricCoeff (e.toFun ∘ Opens.inclusion (exteriorBall_anti hR')) x i j =
          e.metricCoeff x i j := hev.self_of_nhds
    rw [h0, hev.fderiv_eq, hev.fderiv.fderiv_eq]
    exact hC x hx' i j

@[simp]
theorem radius_restrictRadius (e : AsymptoticallyEuclideanEnd n M t) {R' : ℝ}
    (hR' : e.radius ≤ R') : (e.restrictRadius hR').radius = R' := by
  rfl

@[simp]
theorem toFun_restrictRadius (e : AsymptoticallyEuclideanEnd n M t) {R' : ℝ}
    (hR' : e.radius ≤ R') (x : exteriorBall n (e.restrictRadius hR').radius) :
    (e.restrictRadius hR').toFun x =
      e.toFun ⟨x.1, mem_exteriorBall.2
        ((hR'.trans_eq (radius_restrictRadius e hR').symm).trans_lt
          (mem_exteriorBall.1 x.2))⟩ := by
  rfl

/-- Restricting the excised radius preserves the pulled-back metric coefficients on the smaller
exterior domain. -/
theorem metricCoeff_restrictRadius (e : AsymptoticallyEuclideanEnd n M t) {R' : ℝ}
    (hR' : e.radius ≤ R') {x : EuclideanSpace ℝ (Fin n)} (hx : R' < ‖x‖) (i j : Fin n) :
    (e.restrictRadius hR').metricCoeff x i j = e.metricCoeff x i j :=
  openPullbackMetricCoeff_comp_inclusion (exteriorBall_anti hR') e.toFun
    (mem_exteriorBall.2 hx) i j

/-- An asymptotically Euclidean end of order `t` is also an end of every smaller order
`t' ≤ t`. -/
def ofLe (e : AsymptoticallyEuclideanEnd n M t) {t' : ℝ} (ht : t' ≤ t) :
    AsymptoticallyEuclideanEnd n M t' where
  radius := e.radius
  radius_pos := e.radius_pos
  toFun := e.toFun
  contMDiff := e.contMDiff
  injective := e.injective
  mfderiv_bijective := e.mfderiv_bijective
  decay := by
    obtain ⟨C, hC⟩ := e.decay
    refine ⟨max C 0 * e.radius ^ (t' - t), fun x hx i j ↦ ?_⟩
    have hx0 : 0 < ‖x‖ := e.radius_pos.trans hx
    have hpow : ‖x‖ ^ (t' - t) ≤ e.radius ^ (t' - t) :=
      Real.rpow_le_rpow_of_nonpos e.radius_pos hx.le (sub_nonpos.2 ht)
    have hbound (a : ℝ) (s : ℝ) (ha : a ≤ C * ‖x‖ ^ (-t - s)) :
        a ≤ max C 0 * e.radius ^ (t' - t) * ‖x‖ ^ (-t' - s) := by
      have h1 : C * ‖x‖ ^ (-t - s) ≤ max C 0 * ‖x‖ ^ (-t - s) :=
        mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg hx0.le _)
      have h2 : ‖x‖ ^ (-t - s) = ‖x‖ ^ (t' - t) * ‖x‖ ^ (-t' - s) := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring
      have h3 : max C 0 * (‖x‖ ^ (t' - t) * ‖x‖ ^ (-t' - s)) ≤
          max C 0 * (e.radius ^ (t' - t) * ‖x‖ ^ (-t' - s)) := by
        gcongr
      exact ha.trans (h1.trans (by rw [h2]; linarith [h3]))
    obtain ⟨h0, h1, h2⟩ := hC x hx i j
    refine ⟨?_, hbound _ 1 h1, hbound _ 2 h2⟩
    simpa only [sub_zero] using hbound _ 0 (by simpa only [sub_zero] using h0)

@[simp]
theorem radius_ofLe (e : AsymptoticallyEuclideanEnd n M t) {t' : ℝ} (ht : t' ≤ t) :
    (e.ofLe ht).radius = e.radius := by
  rfl

@[simp]
theorem toFun_ofLe (e : AsymptoticallyEuclideanEnd n M t) {t' : ℝ} (ht : t' ≤ t)
    (x : exteriorBall n (e.ofLe ht).radius) :
    (e.ofLe ht).toFun x = e.toFun ⟨x.1, radius_ofLe e ht ▸ x.2⟩ := by
  rfl

@[simp]
theorem range_ofLe (e : AsymptoticallyEuclideanEnd n M t) {t' : ℝ} (ht : t' ≤ t) :
    Set.range (e.ofLe ht).toFun = Set.range e.toFun := by
  rfl

@[simp]
theorem metricCoeff_ofLe (e : AsymptoticallyEuclideanEnd n M t) {t' : ℝ} (ht : t' ≤ t) :
    (e.ofLe ht).metricCoeff = e.metricCoeff := by
  rfl

/-- Push an asymptotically Euclidean end forward along a smooth Riemannian isometry. -/
def compRiemannianIsometry {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [RiemannianBundle (fun y : N ↦ TangentSpace (𝓡 n) y)]
    (e : AsymptoticallyEuclideanEnd n M t) (Φ : RiemannianIsometry (𝓡 n) (𝓡 n) M N) :
    AsymptoticallyEuclideanEnd n N t where
  radius := e.radius
  radius_pos := e.radius_pos
  toFun := Φ ∘ e.toFun
  contMDiff := Φ.toDiffeomorph.contMDiff.comp e.contMDiff
  injective := Φ.injective.comp e.injective
  mfderiv_bijective := fun x ↦ by
    rw [mfderiv_comp x (Φ.mdifferentiableAt _) (e.contMDiff.mdifferentiable (by simp) x)]
    have hΦ : Function.Bijective (mfderiv (𝓡 n) (𝓡 n) Φ (e.toFun x)) :=
      ⟨Function.LeftInverse.injective
          (g := mfderiv (𝓡 n) (𝓡 n) Φ.toDiffeomorph.symm (Φ (e.toFun x))) fun v ↦ by
            simpa only [RiemannianIsometry.coe_toDiffeomorph] using
              Φ.toDiffeomorph.mfderiv_symm_apply_mfderiv_apply (by simp) (e.toFun x) v,
       Function.RightInverse.surjective
          (g := mfderiv (𝓡 n) (𝓡 n) Φ.toDiffeomorph.symm (Φ (e.toFun x))) fun v ↦ by
            simpa only [RiemannianIsometry.coe_toDiffeomorph] using
              Φ.toDiffeomorph.mfderiv_apply_mfderiv_symm_apply (by simp) (e.toFun x) v⟩
    exact hΦ.comp (e.mfderiv_bijective x)
  decay := by
    rw [openPullbackMetricCoeff_comp_riemannianIsometry (e.contMDiff.mdifferentiable (by simp)) Φ]
    exact e.decay

@[simp]
theorem radius_compRiemannianIsometry {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [RiemannianBundle (fun y : N ↦ TangentSpace (𝓡 n) y)]
    (e : AsymptoticallyEuclideanEnd n M t) (Φ : RiemannianIsometry (𝓡 n) (𝓡 n) M N) :
    (e.compRiemannianIsometry Φ).radius = e.radius := by
  rfl

@[simp]
theorem toFun_compRiemannianIsometry {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [RiemannianBundle (fun y : N ↦ TangentSpace (𝓡 n) y)]
    (e : AsymptoticallyEuclideanEnd n M t) (Φ : RiemannianIsometry (𝓡 n) (𝓡 n) M N)
    (x : exteriorBall n (e.compRiemannianIsometry Φ).radius) :
    (e.compRiemannianIsometry Φ).toFun x =
      Φ (e.toFun ⟨x.1, radius_compRiemannianIsometry e Φ ▸ x.2⟩) := by
  rfl

/-- Pushing an end forward along a Riemannian isometry `Φ` maps its range by `Φ`. -/
theorem range_compRiemannianIsometry {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [RiemannianBundle (fun y : N ↦ TangentSpace (𝓡 n) y)]
    (e : AsymptoticallyEuclideanEnd n M t) (Φ : RiemannianIsometry (𝓡 n) (𝓡 n) M N) :
    Set.range (e.compRiemannianIsometry Φ).toFun = Φ '' Set.range e.toFun :=
  Set.range_comp Φ e.toFun

@[simp]
theorem metricCoeff_compRiemannianIsometry {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [RiemannianBundle (fun y : N ↦ TangentSpace (𝓡 n) y)]
    (e : AsymptoticallyEuclideanEnd n M t) (Φ : RiemannianIsometry (𝓡 n) (𝓡 n) M N) :
    (e.compRiemannianIsometry Φ).metricCoeff = e.metricCoeff :=
  openPullbackMetricCoeff_comp_riemannianIsometry (e.contMDiff.mdifferentiable (by simp)) Φ

/-! #### Flat Euclidean space -/

/-- The standard asymptotically Euclidean end on flat `EuclideanSpace ℝ (Fin n)` with excised
radius `R > 0`, of any order `t : ℝ`. -/
def euclidean (n : ℕ) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    AsymptoticallyEuclideanEnd n (EuclideanSpace ℝ (Fin n)) t where
  radius := R
  radius_pos := hR
  toFun := Subtype.val
  contMDiff := contMDiff_subtype_val
  injective := Subtype.val_injective
  mfderiv_bijective := fun x ↦ by
    rw [TauCeti.Manifold.mfderiv_subtype_val]
    exact (TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓡 n) x).bijective
  decay := by
    refine ⟨0, fun x hx i j ↦ ?_⟩
    have hev : (fun y ↦ openPullbackMetricCoeff
          (Subtype.val : exteriorBall n R → EuclideanSpace ℝ (Fin n)) y i j) =ᶠ[𝓝 x]
        fun _ ↦ if i = j then (1 : ℝ) else 0 :=
      eventually_of_mem ((exteriorBall n R).isOpen.mem_nhds (mem_exteriorBall.2 hx))
        fun y hy ↦ openPullbackMetricCoeff_subtype_val hy i j
    have h1 : fderiv ℝ (fun y ↦ openPullbackMetricCoeff
        (Subtype.val : exteriorBall n R → EuclideanSpace ℝ (Fin n)) y i j) x = 0 := by
      rw [hev.fderiv_eq, fderiv_const_apply]
    have h2 : fderiv ℝ (fderiv ℝ (fun y ↦ openPullbackMetricCoeff
        (Subtype.val : exteriorBall n R → EuclideanSpace ℝ (Fin n)) y i j)) x = 0 := by
      have hev1 : fderiv ℝ (fun y ↦ openPullbackMetricCoeff
          (Subtype.val : exteriorBall n R → EuclideanSpace ℝ (Fin n)) y i j) =ᶠ[𝓝 x]
          fun _ ↦ (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := by
        filter_upwards [hev.fderiv (𝕜 := ℝ)] with y hy
        rw [hy, fderiv_const_apply]
      rw [hev1.fderiv_eq, fderiv_const_apply]
    simp only [openPullbackMetricCoeff_subtype_val (mem_exteriorBall.2 hx), h1, h2, sub_self,
      abs_zero, zero_mul, ContinuousLinearMap.opNorm_zero, le_refl, and_self]

@[simp]
theorem radius_euclidean (n : ℕ) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    (euclidean n hR t).radius = R := by
  rfl

@[simp]
theorem toFun_euclidean (n : ℕ) {R : ℝ} (hR : 0 < R) (t : ℝ)
    (x : exteriorBall n (euclidean n hR t).radius) :
    (euclidean n hR t).toFun x = x.1 := by
  rfl

/-- The range of the standard flat Euclidean end is the exterior ball. -/
theorem range_euclidean (n : ℕ) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    Set.range (euclidean n hR t).toFun = (exteriorBall n R : Set (EuclideanSpace ℝ (Fin n))) :=
  Subtype.range_coe

/-- On `{x | R < ‖x‖}`, the pulled-back metric coefficients of `euclidean` are `δ_ij`. -/
theorem metricCoeff_euclidean (n : ℕ) {R : ℝ} (hR : 0 < R) (t : ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : R < ‖x‖) (i j : Fin n) :
    (euclidean n hR t).metricCoeff x i j = if i = j then 1 else 0 :=
  openPullbackMetricCoeff_subtype_val (mem_exteriorBall.2 hx) i j

end AsymptoticallyEuclideanEnd

/-! ### Negative control: non-isometric dilations fail asymptotic decay -/

/-- A non-isometric dilation `x ↦ a • x` (`|a| ≠ 1`) on `EuclideanSpace ℝ (Fin n)` (`1 ≤ n`) pulls
the Euclidean metric back to `a ^ 2 • δ_ij`, so its diagonal deviation from `δ_ij` is constantly
`|a ^ 2 - 1| > 0` and fails the asymptotically Euclidean decay condition for every `t > 0`. -/
theorem not_exists_decay_pullbackMetricCoeff_smul {n : ℕ} (hn : 1 ≤ n) {a R t : ℝ}
    (ha : |a| ≠ 1) (ht : 0 < t) :
    ¬ ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ → ∀ i j : Fin n,
      |pullbackMetricCoeff (fun y : EuclideanSpace ℝ (Fin n) ↦ a • y) x i j -
        if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) := by
  rintro ⟨C, hC⟩
  let i₀ : Fin n := ⟨0, hn⟩
  have hcoeff (x : EuclideanSpace ℝ (Fin n)) :
      pullbackMetricCoeff (fun y : EuclideanSpace ℝ (Fin n) ↦ a • y) x i₀ i₀ = a ^ 2 := by
    let v : TangentSpace (𝓡 n) (a • x) := EuclideanSpace.basisFun (Fin n) ℝ i₀
    have hderiv : mfderiv (𝓡 n) (𝓡 n) (fun y : EuclideanSpace ℝ (Fin n) ↦ a • y) x
        (EuclideanSpace.basisFun (Fin n) ℝ i₀) = a • v := by
      let L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
        a • ContinuousLinearMap.id ℝ _
      have hL : (fun y : EuclideanSpace ℝ (Fin n) ↦ a • y) = ⇑L := funext fun _ ↦ rfl
      have hf : mfderiv (𝓡 n) (𝓡 n) (⇑L) x = L :=
        (L.hasFDerivAt (x := x)).hasMFDerivAt.mfderiv
      rw [hL]
      exact DFunLike.congr_fun hf (EuclideanSpace.basisFun (Fin n) ℝ i₀)
    have hunit : inner ℝ v v = 1 :=
      (orthonormal_iff_ite.1 (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal i₀ i₀).trans
        (by simp)
    rw [pullbackMetricCoeff, hderiv, real_inner_smul_left, real_inner_smul_right, hunit]
    ring
  have hgap : 0 < |a ^ 2 - 1| := by
    refine abs_pos.2 (sub_ne_zero.2 fun h ↦ ha ?_)
    rw [← sq_abs] at h
    nlinarith [abs_nonneg a]
  have htend : Tendsto (fun r : ℝ ↦ C * r ^ (-t)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop ht).const_mul C
  obtain ⟨r, hrR, hrgap⟩ :=
    ((eventually_gt_atTop (max R 0)).and (htend.eventually (Iio_mem_nhds hgap))).exists
  have hr_pos : 0 < r := (le_max_right R 0).trans_lt hrR
  have hnorm : ‖r • EuclideanSpace.basisFun (Fin n) ℝ i₀‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg hr_pos.le,
      (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.1 i₀, mul_one]
  have hbound := hC (r • EuclideanSpace.basisFun (Fin n) ℝ i₀)
    (hnorm.symm ▸ (le_max_left R 0).trans_lt hrR) i₀ i₀
  rw [hcoeff, hnorm] at hbound
  simp only [↓reduceIte] at hbound
  exact not_lt_of_ge hbound hrgap

/-- No asymptotically Euclidean end of positive order on flat `ℝⁿ` (`1 ≤ n`) can be given by a
non-isometric dilation `x ↦ a • x` (`|a| ≠ 1`). -/
theorem AsymptoticallyEuclideanEnd.toFun_ne_smul {n : ℕ} (hn : 1 ≤ n) {a t : ℝ} (ha : |a| ≠ 1)
    (ht : 0 < t) (e : AsymptoticallyEuclideanEnd n (EuclideanSpace ℝ (Fin n)) t) :
    ¬ ∀ x : exteriorBall n e.radius,
      e.toFun x = a • (x : EuclideanSpace ℝ (Fin n)) := by
  intro h
  refine not_exists_decay_pullbackMetricCoeff_smul hn (R := e.radius) ha ht ?_
  obtain ⟨C, hC⟩ := e.decay
  refine ⟨C, fun x hx i j ↦ ?_⟩
  have hmc := e.metricCoeff_eq_pullbackMetricCoeff_of_eqOn (fun y ↦ (h y).symm) hx i j
  rw [← hmc]
  exact (hC x hx i j).1

end TauCeti

end
