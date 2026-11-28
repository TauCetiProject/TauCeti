/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem.Boundary.Chart
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import TauCeti.Geometry.Manifold.Riemannian.Boundary.Flux
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Integration
import TauCeti.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The divergence theorem on a Riemannian manifold with boundary

On a `C²` manifold `M` with boundary modeled on `EuclideanHalfSpace (n + 1)` (`𝓡∂ (n + 1)`),
carrying a `C¹` Riemannian metric, the divergence of a compactly supported `C¹` vector field `X`
integrates to its outward normal flux across the boundary:
`∫ x, div X x ∂V = ∫ x : ∂M, inner ℝ (X x) (N x) ∂S`,
where `V = TauCeti.riemannianVolume (𝓡∂ (n + 1)) M` is the ambient Riemannian volume measure,
`S = TauCeti.halfSpaceBoundaryVolume` is the Riemannian volume measure of the induced boundary
metric `TauCeti.halfSpaceBoundaryMetric`, and `N = TauCeti.outwardUnitNormal` is the
unique outward-pointing unit normal along `∂M`. No orientability assumption is imposed on `M`, and
every dimension `n ≥ 0` is included (`n = 0` gives counting measure on the boundary).

Substituting `f X` and `f grad g` yields boundary integration by parts and Green's identities:
* `∫ f div X dV = -∫ df(X) dV + ∫_{∂M} f ⟪X, N⟫ dS`,
* `∫ f Δg dV = -∫ ⟪grad f, grad g⟫ dV + ∫_{∂M} f ⟪grad g, N⟫ dS`,
* `∫ (f Δg - (Δf) g) dV = ∫_{∂M} (f ⟪grad g, N⟫ - g ⟪grad f, N⟫) dS`.

## Main results

* `TauCeti.Manifold.integral_divergence_eq_boundaryFlux`: the Riemannian divergence theorem on a
  manifold with boundary without orientability assumptions.
* `TauCeti.Manifold.integral_mul_divergence_eq_boundaryFlux`,
  `TauCeti.Manifold.integral_mul_divergence_eq_boundaryFlux_of_hasCompactSupport_right`:
  integration by parts for the divergence with boundary term.
* `TauCeti.Manifold.integral_laplaceBeltrami_eq_boundaryFlux`,
  `TauCeti.Manifold.integral_mul_laplaceBeltrami_eq_boundaryFlux`,
  `TauCeti.Manifold.integral_mul_laplaceBeltrami_eq_boundaryFlux_of_hasCompactSupport_right`,
  `TauCeti.Manifold.integral_mul_laplaceBeltrami_sub_eq_boundaryFlux`: Green's identities.
* `TauCeti.Manifold.integral_divergence_eq_zero_of_isEmpty_boundary`,
  `TauCeti.Manifold.integral_divergence_eq_tsum_boundaryFlux`,
  `TauCeti.Manifold.integral_divergence_eq_sum_boundaryFlux`: empty-boundary and `n = 0` cases.
* `TauCeti.integrable_divergence_and_boundaryFlux` and
  `TauCeti.integral_divergence_eq_boundaryFlux`: convenience versions for compact `M` or compactly
  supported `X`, and any vector field `N` along `∂M` satisfying the outward unit normal property.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Proposition
  15.33, Theorem 16.32, and Proposition 16.34.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (the Riemannian density and divergence on manifolds with boundary).
-/

public section

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Riemannian.Tensor Set
open scoped ContDiff Manifold Matrix Topology

namespace TauCeti.Manifold

/-! ### Global divergence theorem and Green's identities with boundary -/

section Global

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) 2 M] [T2Space M] [LindelofSpace M] [MeasurableSpace M]
  [BorelSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

local instance instIsManifoldAddOneGlobalBoundary : IsManifold (𝓡∂ (n + 1)) (1 + 1) M := by
  rw [one_add_one_eq_two]; infer_instance

/-- **The Riemannian divergence theorem** on a manifold with boundary: for a compactly supported
`C¹` vector field `X` on a `C²` Hausdorff Lindelöf manifold `M` modeled on `𝓡∂ (n + 1)` with a
`C¹` Riemannian metric, the integral of `div X` against the Riemannian volume equals the integral
of the outward normal flux `inner ℝ (X x) (N x)` against the induced boundary Riemannian volume,
with no orientability assumption and in every dimension `n ≥ 0`. -/
theorem integral_divergence_eq_boundaryFlux {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X))
    (hc : HasCompactSupport (β := EuclideanSpace ℝ (Fin (n + 1))) X) :
    (∫ x, divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      ∫ x : (𝓡∂ (n + 1)).boundary M, inner ℝ (X (x : M)) (outwardUnitNormal x)
        ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  classical
  have hclosed_bdry := (𝓡∂ (n + 1)).isClosed_boundary (M := M) (by norm_num : (2 : ℕ∞ω) ≠ 0)
  let U : M → Set M := fun i ↦ (chartAt (EuclideanHalfSpace (n + 1)) i).source ∩
    if i ∈ (𝓡∂ (n + 1)).boundary M then univ else ((𝓡∂ (n + 1)).boundary M)ᶜ
  obtain ⟨ι, _, c, Y, hY, hK, hsub, hsum⟩ :=
    hc.exists_subordinate_vectorField_sum (𝓡∂ (n + 1)) hX (U := U) fun x _ ↦ Filter.inter_mem
      (chart_source_mem_nhds (EuclideanHalfSpace (n + 1)) x)
      (by
        split_ifs with hx
        exacts [Filter.univ_mem, hclosed_bdry.isOpen_compl.mem_nhds hx])
  have hdiv (x : M) : divergence (𝓡∂ (n + 1)) X x = ∑ i, divergence (𝓡∂ (n + 1)) (Y i) x := by
    rw [← divergence_finsetSum (𝓡∂ (n + 1)) Finset.univ Y x fun i _ ↦
      (hY i x).mdifferentiableAt one_ne_zero]
    exact congrArg (divergence (𝓡∂ (n + 1)) · x) (funext hsum)
  rw [integral_congr_ae (Filter.Eventually.of_forall hdiv),
    integral_finsetSum _ fun i _ ↦ integrable_divergence (hY i) (hK i),
    integral_congr_ae (Filter.Eventually.of_forall fun x : (𝓡∂ (n + 1)).boundary M ↦
      (congrArg (inner ℝ · (outwardUnitNormal x)) (hsum (x : M))).trans (sum_inner _ _ _)),
    integral_finsetSum _ fun i _ ↦ TauCeti.integrable_boundaryFlux (hY i).continuous (hK i)]
  refine Finset.sum_congr rfl fun i _ ↦
    integral_divergence_eq_boundaryFlux_of_tsupport_subset_chart (hY i) (hK i)
      (fun _ hx ↦ (hsub i hx).1) ?_
  by_cases hi : c i ∈ (𝓡∂ (n + 1)).boundary M
  · exact Or.inl hi
  · exact Or.inr (disjoint_left.2 fun _ hx ↦ by simpa [hi] using (hsub i hx).2)

/-- When the boundary of `M` is empty, `TauCeti.Manifold.integral_divergence_eq_boundaryFlux`
recovers vanishing of the integral of the divergence. -/
theorem integral_divergence_eq_zero_of_isEmpty_boundary [IsEmpty ((𝓡∂ (n + 1)).boundary M)]
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X))
    (hc : HasCompactSupport (β := EuclideanSpace ℝ (Fin (n + 1))) X) :
    ∫ x, divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M = 0 := by
  rw [integral_divergence_eq_boundaryFlux hX hc, integral_of_isEmpty]

/-- **Integration by parts for the divergence** on a manifold with boundary, when `f` has compact
support: `∫ f div X dV = -∫ df(X) dV + ∫_{∂M} f ⟪X, N⟫ dS`. -/
theorem integral_mul_divergence_eq_boundaryFlux {f : M → ℝ}
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x} (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) 1 f)
    (hfc : HasCompactSupport f) (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X)) :
    (∫ x, f x * divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      -(∫ x, mvfderiv (𝓡∂ (n + 1)) f x (X x) ∂riemannianVolume (𝓡∂ (n + 1)) M) +
        ∫ x : (𝓡∂ (n + 1)).boundary M,
          f (x : M) * inner ℝ (X (x : M)) (outwardUnitNormal x)
          ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  rw [integral_mul_divergence_eq_integral_divergence_smul_sub_of_hasCompactSupport_left hf hfc hX,
    integral_divergence_eq_boundaryFlux (X := fun x ↦ f x • X x) (hf.smul_section hX)
      (hfc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_left _ _))]
  simp_rw [real_inner_smul_left]; ring

/-- **Integration by parts for the divergence** on a manifold with boundary, when `X` has compact
support: `∫ f div X dV = -∫ df(X) dV + ∫_{∂M} f ⟪X, N⟫ dS`. -/
theorem integral_mul_divergence_eq_boundaryFlux_of_hasCompactSupport_right {f : M → ℝ}
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x} (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) 1 f)
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent 1 (T% X))
    (hXc : HasCompactSupport (β := EuclideanSpace ℝ (Fin (n + 1))) X) :
    (∫ x, f x * divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      -(∫ x, mvfderiv (𝓡∂ (n + 1)) f x (X x) ∂riemannianVolume (𝓡∂ (n + 1)) M) +
        ∫ x : (𝓡∂ (n + 1)).boundary M,
          f (x : M) * inner ℝ (X (x : M)) (outwardUnitNormal x)
          ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  rw [integral_mul_divergence_eq_integral_divergence_smul_sub_of_hasCompactSupport_right hf hX hXc,
    integral_divergence_eq_boundaryFlux (X := fun x ↦ f x • X x) (hf.smul_section hX)
      (hXc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_right _ _))]
  simp_rw [real_inner_smul_left]; ring

/-- For a compactly supported `C²` function `f` on a manifold with boundary, the integral of its
Laplace–Beltrami operator `Δf` equals the boundary integral of its outward normal derivative
`inner ℝ (grad f) N`. -/
theorem integral_laplaceBeltrami_eq_boundaryFlux {f : M → ℝ}
    (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) 2 f) (hfc : HasCompactSupport f) :
    (∫ x, laplaceBeltrami (𝓡∂ (n + 1)) f x ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      ∫ x : (𝓡∂ (n + 1)).boundary M,
        inner ℝ (mgradient (𝓡∂ (n + 1)) f (x : M)) (outwardUnitNormal x)
        ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  simp only [laplaceBeltrami_def]
  exact integral_divergence_eq_boundaryFlux
    (contMDiff_mgradient (n := 1) (by rwa [one_add_one_eq_two])) (hfc.mgradient (𝓡∂ (n + 1)))

/-- **Green's first identity** on a manifold with boundary, when `f` has compact support: for a
compactly supported `C¹` function `f` and a `C²` function `g`,
`∫ f Δg dV = -∫ ⟪grad f, grad g⟫ dV + ∫_{∂M} f ⟪grad g, N⟫ dS`. -/
theorem integral_mul_laplaceBeltrami_eq_boundaryFlux {f g : M → ℝ}
    (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) 1 f) (hfc : HasCompactSupport f)
    (hg : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) 2 g) :
    (∫ x, f x * laplaceBeltrami (𝓡∂ (n + 1)) g x ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      -(∫ x, inner ℝ (mgradient (𝓡∂ (n + 1)) f x) (mgradient (𝓡∂ (n + 1)) g x)
          ∂riemannianVolume (𝓡∂ (n + 1)) M) +
        ∫ x : (𝓡∂ (n + 1)).boundary M,
          f (x : M) * inner ℝ (mgradient (𝓡∂ (n + 1)) g (x : M)) (outwardUnitNormal x)
          ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  simp_rw [laplaceBeltrami_def]
  rw [integral_mul_divergence_eq_boundaryFlux hf hfc
    (contMDiff_mgradient (n := 1) (by rwa [one_add_one_eq_two]))]
  congr 2; exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦
    (inner_mgradient (I := 𝓡∂ (n + 1)) (f := f) (x := x) _).symm)

/-- **Green's first identity** on a manifold with boundary, when `g` has compact support: for a
`C¹` function `f` and a compactly supported `C²` function `g`,
`∫ f Δg dV = -∫ ⟪grad f, grad g⟫ dV + ∫_{∂M} f ⟪grad g, N⟫ dS`. -/
theorem integral_mul_laplaceBeltrami_eq_boundaryFlux_of_hasCompactSupport_right {f g : M → ℝ}
    (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) 1 f)
    (hg : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) 2 g) (hgc : HasCompactSupport g) :
    (∫ x, f x * laplaceBeltrami (𝓡∂ (n + 1)) g x ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      -(∫ x, inner ℝ (mgradient (𝓡∂ (n + 1)) f x) (mgradient (𝓡∂ (n + 1)) g x)
          ∂riemannianVolume (𝓡∂ (n + 1)) M) +
        ∫ x : (𝓡∂ (n + 1)).boundary M,
          f (x : M) * inner ℝ (mgradient (𝓡∂ (n + 1)) g (x : M)) (outwardUnitNormal x)
          ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  simp_rw [laplaceBeltrami_def]
  rw [integral_mul_divergence_eq_boundaryFlux_of_hasCompactSupport_right hf
    (contMDiff_mgradient (n := 1) (by rwa [one_add_one_eq_two])) (hgc.mgradient (𝓡∂ (n + 1)))]
  congr 2; exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦
    (inner_mgradient (I := 𝓡∂ (n + 1)) (f := f) (x := x) _).symm)

/-- **Green's second identity** on a manifold with boundary [Lee, Proposition 16.34(b)]: for a
compactly supported `C²` function `f` and a `C²` function `g`,
`∫ (f Δg - (Δf) g) dV = ∫_{∂M} (f ⟪grad g, N⟫ - g ⟪grad f, N⟫) dS`. -/
theorem integral_mul_laplaceBeltrami_sub_eq_boundaryFlux {f g : M → ℝ}
    (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) 2 f) (hfc : HasCompactSupport f)
    (hg : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) 2 g) :
    (∫ x, (f x * laplaceBeltrami (𝓡∂ (n + 1)) g x - laplaceBeltrami (𝓡∂ (n + 1)) f x * g x)
        ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      ∫ x : (𝓡∂ (n + 1)).boundary M,
        (f (x : M) * inner ℝ (mgradient (𝓡∂ (n + 1)) g (x : M)) (outwardUnitNormal x) -
          g (x : M) * inner ℝ (mgradient (𝓡∂ (n + 1)) f (x : M)) (outwardUnitNormal x))
        ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  have hf1 := hf.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)
  have hg1 := hg.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)
  have hint_fΔg : Integrable (fun x ↦ f x * laplaceBeltrami (𝓡∂ (n + 1)) g x) _ :=
    (hf1.continuous.mul (continuous_laplaceBeltrami hg)).integrable_of_hasCompactSupport
      (μ := riemannianVolume (𝓡∂ (n + 1)) M) hfc.mul_right
  have hint_Δfg : Integrable (fun x ↦ laplaceBeltrami (𝓡∂ (n + 1)) f x * g x) _ :=
    ((continuous_laplaceBeltrami hf).mul hg1.continuous).integrable_of_hasCompactSupport
      (μ := riemannianVolume (𝓡∂ (n + 1)) M) (hfc.laplaceBeltrami (𝓡∂ (n + 1))).mul_right
  have hbdry_f := (TauCeti.integrable_boundaryFlux
      (X := fun x ↦ f x • mgradient (𝓡∂ (n + 1)) g x)
      (hf1.smul_section (contMDiff_mgradient (n := 1) (by rwa [one_add_one_eq_two]))).continuous
      (hfc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_left _ _))).congr
    (Filter.Eventually.of_forall fun _ ↦ real_inner_smul_left _ _ _)
  have hbdry_g := (TauCeti.integrable_boundaryFlux
      (X := fun x ↦ g x • mgradient (𝓡∂ (n + 1)) f x)
      (hg1.smul_section (contMDiff_mgradient (n := 1) (by rwa [one_add_one_eq_two]))).continuous
      ((hfc.mgradient (𝓡∂ (n + 1))).of_isClosed_subset (isClosed_tsupport _)
        (tsupport_smul_subset_right _ _))).congr
    (Filter.Eventually.of_forall fun _ ↦ real_inner_smul_left _ _ _)
  rw [integral_sub hint_fΔg hint_Δfg, integral_sub hbdry_f hbdry_g,
    integral_mul_laplaceBeltrami_eq_boundaryFlux hf1 hfc hg]
  simp_rw [mul_comm (laplaceBeltrami (𝓡∂ (n + 1)) f _),
    integral_mul_laplaceBeltrami_eq_boundaryFlux_of_hasCompactSupport_right hg1 hf hfc,
    real_inner_comm (mgradient (𝓡∂ (n + 1)) g _)]; ring

end Global

/-! ### One-dimensional specialization (`n = 0`) -/

section OneDim

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
  [IsManifold (𝓡∂ 1) 2 M] [T2Space M] [LindelofSpace M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ 1) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ 1) 1 (EuclideanSpace ℝ (Fin 1))
    (fun x : M ↦ TangentSpace (𝓡∂ 1) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 1)) (fun x : M ↦ TangentSpace (𝓡∂ 1) x)]

/-- On a one-dimensional Riemannian manifold with boundary (`n = 0`), the integral of `div X` is
the series of outward normal fluxes `inner ℝ (X x) (N x)` over all boundary points, because
`halfSpaceBoundaryVolume` is counting measure. -/
theorem integral_divergence_eq_tsum_boundaryFlux {X : (x : M) → TangentSpace (𝓡∂ 1) x}
    (hX : ContMDiff (𝓡∂ 1) (𝓡∂ 1).tangent 1 (T% X))
    (hc : HasCompactSupport (β := EuclideanSpace ℝ (Fin 1)) X) :
    (∫ x, divergence (𝓡∂ 1) X x ∂riemannianVolume (𝓡∂ 1) M) =
      ∑' x : (𝓡∂ 1).boundary M, inner ℝ (X (x : M)) (outwardUnitNormal x) := by
  have hint : Integrable
      (fun x : (𝓡∂ 1).boundary M ↦ inner ℝ (X (x : M)) (outwardUnitNormal x)) Measure.count :=
    halfSpaceBoundaryVolume_zero_eq_count (M := M) ▸
      TauCeti.integrable_boundaryFlux (n := 0) hX.continuous hc
  rw [integral_divergence_eq_boundaryFlux (n := 0) hX hc,
    halfSpaceBoundaryVolume_zero_eq_count, MeasureTheory.integral_count_eq_tsum hint]

/-- On a one-dimensional Riemannian manifold with finite boundary (`n = 0`), the integral of
`div X` is the finite sum of outward normal fluxes `inner ℝ (X x) (N x)` at the boundary
endpoints. -/
theorem integral_divergence_eq_sum_boundaryFlux [Fintype ((𝓡∂ 1).boundary M)]
    {X : (x : M) → TangentSpace (𝓡∂ 1) x} (hX : ContMDiff (𝓡∂ 1) (𝓡∂ 1).tangent 1 (T% X))
    (hc : HasCompactSupport (β := EuclideanSpace ℝ (Fin 1)) X) :
    (∫ x, divergence (𝓡∂ 1) X x ∂riemannianVolume (𝓡∂ 1) M) =
      ∑ x : (𝓡∂ 1).boundary M, inner ℝ (X (x : M)) (outwardUnitNormal x) := by
  rw [integral_divergence_eq_tsum_boundaryFlux hX hc, tsum_fintype]

end OneDim

end TauCeti.Manifold

namespace TauCeti

/-! ### Convenience API -/

private theorem hasCompactSupport_of_isCompact_univ_or_exists_compact {n : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hSupport : IsCompact (univ : Set M) ∨ ∃ K : Set M, IsCompact K ∧ ∀ x ∉ K, X x = 0) :
    HasCompactSupport (β := EuclideanSpace ℝ (Fin (n + 1))) X :=
  hSupport.elim (fun h ↦ have : CompactSpace M := ⟨h⟩; .of_compactSpace _)
    fun ⟨_, hK, hz⟩ ↦ .intro hK hz

section ConvenienceAPI

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) 2 M] [T2Space M] [LindelofSpace M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- **Integrability of the divergence and outward boundary flux** under either compactness of `M`
or compact support of `X`, for any boundary vector field `N` satisfying the outward unit normal
characterization. -/
theorem integrable_divergence_and_boundaryFlux {k : ℕ∞ω}
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent k (T% X))
    (hSupport : IsCompact (univ : Set M) ∨ ∃ K : Set M, IsCompact K ∧ ∀ x ∉ K, X x = 0)
    {N : (x : (𝓡∂ (n + 1)).boundary M) → TangentSpace (𝓡∂ (n + 1)) (x : M)}
    (hN : ∀ x, ‖N x‖ = 1 ∧ IsOutwardPointing (x : M) (N x) ∧
      ∀ w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x,
        inner ℝ (N x) (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) Subtype.val x w) = 0)
    (hk : 1 ≤ k := by simp) :
    Integrable (Manifold.divergence (𝓡∂ (n + 1)) X) (riemannianVolume (𝓡∂ (n + 1)) M) ∧
      Integrable (fun x : (𝓡∂ (n + 1)).boundary M ↦ inner ℝ (X (x : M)) (N x))
        (halfSpaceBoundaryVolume (n := n) (M := M)) := by
  obtain rfl : N = outwardUnitNormal :=
    funext fun x ↦ eq_outwardUnitNormal_iff.2 ⟨(hN x).1, (hN x).2.1, (hN x).2.2⟩
  have hc := hasCompactSupport_of_isCompact_univ_or_exists_compact hSupport
  exact ⟨Manifold.integrable_divergence (hX.of_le hk) hc,
    integrable_boundaryFlux (hX.of_le hk).continuous hc⟩

/-- **The Riemannian divergence theorem with boundary** [Lee, Theorem 16.32]: on a `C²`
Hausdorff Lindelöf manifold `M` modeled on `𝓡∂ (n + 1)` with a `C¹` Riemannian metric (and no
orientability assumption), `∫_M div X dV = ∫_{∂M} ⟪X, N⟫ dS` whenever `M` is compact or `X` is
compactly supported, for any field `N` along `∂M` of unit norm, pointing outward, and orthogonal
to the boundary tangent space. -/
theorem integral_divergence_eq_boundaryFlux {k : ℕ∞ω} {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent k (T% X))
    (hSupport : IsCompact (univ : Set M) ∨ ∃ K : Set M, IsCompact K ∧ ∀ x ∉ K, X x = 0)
    {N : (x : (𝓡∂ (n + 1)).boundary M) → TangentSpace (𝓡∂ (n + 1)) (x : M)}
    (hN : ∀ x, ‖N x‖ = 1 ∧ IsOutwardPointing (x : M) (N x) ∧
      ∀ w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x,
        inner ℝ (N x) (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) Subtype.val x w) = 0)
    (hk : 1 ≤ k := by simp) :
    (∫ x, Manifold.divergence (𝓡∂ (n + 1)) X x ∂riemannianVolume (𝓡∂ (n + 1)) M) =
      ∫ x : (𝓡∂ (n + 1)).boundary M, inner ℝ (X (x : M)) (N x)
        ∂halfSpaceBoundaryVolume (n := n) (M := M) := by
  obtain rfl : N = outwardUnitNormal :=
    funext fun x ↦ eq_outwardUnitNormal_iff.2 ⟨(hN x).1, (hN x).2.1, (hN x).2.2⟩
  exact Manifold.integral_divergence_eq_boundaryFlux (hX.of_le hk)
    (hasCompactSupport_of_isCompact_univ_or_exists_compact hSupport)

end ConvenienceAPI

end TauCeti
