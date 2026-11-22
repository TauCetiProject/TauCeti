/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.Distribution
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Section
import TauCeti.Geometry.Manifold.VectorBundle.ConstantRank
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence

/-!
# Orthogonal and complementary distributions

For a `C^n` Riemannian metric on a manifold `M` modelled on a finite-dimensional real space, the
orthogonal complements `(D x)ᗮ` of a `C^n` distribution `D` of rank `k` form a `C^n` distribution
of rank `dim M - k` (`TauCeti.IsContMDiffDistribution.orthogonal`). Near a point, take a local
frame `X₁, …, X_k` of `D`. Then `(D y)ᗮ` is the kernel of the bundle map

`v ↦ (⟪X₁ y, v⟫, …, ⟪X_k y, v⟫)`

from the tangent bundle to the trivial bundle with fibre `ℝᵏ`. This bundle map is `C^n` and has
constant rank `k`, so its kernels have `C^n` local frames
(`TauCeti.exists_isSubbundleFrameOn_ker`).

As a Hausdorff σ-compact manifold carries a smooth Riemannian metric
(`TauCeti.nonempty_contMDiffRiemannianMetric`), every smooth distribution `D` of rank `k` on it has
a smooth complement: a distribution `D'` of rank `dim M - k`, of the same regularity, with
`T_x M = D x ⊕ D' x` at every point (`TauCeti.IsContMDiffDistribution.exists_isCompl`).

Such complements are used to split the tangent bundle along a distribution, for instance to model
the dual of the kernel bundle of a presymplectic form as an annihilator subbundle of the cotangent
bundle.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 10 (orthogonal complements of subbundles) and Chapter 13 (existence of
  Riemannian metrics).
-/

public section

noncomputable section

open Bundle Module Set
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} {k : ℕ} {D : Π x : M, Submodule ℝ (TangentSpace I x)}

section Orthogonal

variable [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The bundle map `v ↦ (⟪X₁ y, v⟫, …, ⟪X_k y, v⟫)` into the trivial bundle with fibre `ℝᵏ`
is `C^n` where the vector fields `X i` are. -/
private theorem contMDiffOn_pi_innerSL [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    {X : Fin k → Π y : M, TangentSpace I y} {U : Set M} (hX : ∀ i, CMDiff[U] n (T% (X i))) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] (Fin k → ℝ))) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] (Fin k → ℝ))
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] Trivial M (Fin k → ℝ) y) y
        (ContinuousLinearMap.pi fun i ↦ innerSL ℝ (X i y))) U := by
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  intro x₀ hx₀
  let e := trivializationAt E (TangentSpace I) x₀
  rw [contMDiffWithinAt_hom_bundle]
  refine ⟨contMDiffWithinAt_id, ?_⟩
  -- The trivialization of the trivial bundle is the identity, so in coordinates the bundle map
  -- is `u ↦ (⟪X i y, e⁻¹ u⟫)ᵢ`.
  simp only [ContinuousLinearMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
    Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_comp]
  refine (contMDiffWithinAt_inter' (mem_nhdsWithin_of_mem_nhds
    (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E _ x₀)))).mp ?_
  refine contMDiffWithinAt_clm_apply.mpr fun u ↦ contMDiffWithinAt_pi_module_iff.mpr fun i ↦ ?_
  have hs := (Manifold.contMDiffOn_symm_baseSet (I := I) (n := n) (e := e) u).mono
    (inter_subset_right : U ∩ e.baseSet ⊆ e.baseSet)
  have hXi := (hX i).mono (inter_subset_left : U ∩ e.baseSet ⊆ U)
  -- The inner products are those of a `C^n` family of bilinear forms `g`.
  obtain ⟨g, hg, hgi⟩ := IsContMDiffRiemannianBundle.exists_contMDiff (IB := I) (n := n)
    (F := E) (E := fun x : M ↦ TangentSpace I x)
  have hx₀' : x₀ ∈ U ∩ e.baseSet := ⟨hx₀, mem_baseSet_trivializationAt E _ x₀⟩
  exact ((hg.contMDiffAt (x := x₀)).contMDiffWithinAt.clm_bundle_apply₂_trivial (hXi x₀ hx₀')
    (hs x₀ hx₀')).congr
    (fun y hy ↦ by simp [hgi, e, e.symmL_apply hy.2]) (by simp [hgi, e, e.symmL_apply hx₀'.2])

/-- **Orthogonal complements of distributions.** For a `C^n` Riemannian metric on a `C^(n + 1)`
manifold modelled on a finite-dimensional real space, the orthogonal complements `(D x)ᗮ` of a
`C^n` distribution `D` of rank `k` form a `C^n` distribution of rank `dim M - k`. -/
theorem IsContMDiffDistribution.orthogonal [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (hD : IsContMDiffDistribution I n k D) :
    IsContMDiffDistribution I n (finrank ℝ E - k) fun x ↦ (D x)ᗮ := by
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  refine isContMDiffDistribution_iff.mpr fun x₀ ↦ ?_
  obtain ⟨U, hU, hx₀U, X, hX⟩ := isContMDiffDistribution_iff.mp hD x₀
  -- On `U`, `(D y)ᗮ` is the kernel of the bundle map `v ↦ (⟪X₁ y, v⟫, …, ⟪X_k y, v⟫)`.
  let φ (y : M) : TangentSpace I y →L[ℝ] Trivial M (Fin k → ℝ) y :=
    ContinuousLinearMap.pi fun i ↦ innerSL ℝ (X i y)
  have hker {y : M} (hy : y ∈ U) : (φ y).ker = (D y)ᗮ := by
    ext v
    rw [← hX.span_eq hy]
    conv_rhs => rw [← Submodule.span_singleton_le_iff_mem, ← Submodule.isOrtho_iff_le,
      Submodule.isOrtho_comm, Submodule.isOrtho_span]
    simp [φ, funext_iff]
  -- By rank–nullity, the bundle map has rank `k` on `U`.
  have hr (y : M) (hy : y ∈ U) : finrank ℝ (φ y).range = k := by
    have : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
    have h₁ :=
      LinearMap.finrank_range_add_finrank_ker (φ y : TangentSpace I y →ₗ[ℝ] Fin k → ℝ)
    have h₂ := Submodule.finrank_add_finrank_orthogonal (D y)
    have hk : finrank ℝ (D y) = k := by simpa using hX.isSubbundleFrameOn.finrank_eq hy
    rw [hker hy] at h₁
    omega
  obtain ⟨V, hVU, hV, hx₀V, Y, hY, hYn⟩ :=
    exists_isSubbundleFrameOn_ker hU (contMDiffOn_pi_innerSL hX.contMDiffOn) hr hx₀U
  exact ⟨V, hV, hx₀V, Y,
    ⟨hYn, hY.linearIndependent, fun hy ↦ (hY.span_eq hy).trans (hker (hVU hy))⟩⟩

end Orthogonal

/-- **Complementary distributions.** On a Hausdorff σ-compact manifold modelled on a
finite-dimensional real space, every `C^n` distribution `D` of rank `k` has a `C^n` complementary
distribution of rank `dim M - k`: a `C^n` distribution `D'` with `D x` and `D' x` complementary
subspaces of `T_x M` at every point `x`. -/
theorem IsContMDiffDistribution.exists_isCompl [T2Space M] [SigmaCompactSpace M]
    [IsManifold I ∞ M] [ENat.LEInfty n] (hD : IsContMDiffDistribution I n k D) :
    ∃ D' : Π x : M, Submodule ℝ (TangentSpace I x),
      IsContMDiffDistribution I n (finrank ℝ E - k) D' ∧ ∀ x, IsCompl (D x) (D' x) := by
  -- `∞ + 1` is definitionally `∞` in `WithTop ℕ∞`, so the smooth structure is reused as is.
  have : IsManifold I (∞ + 1) M := ‹IsManifold I ∞ M›
  have : IsManifold I (n + 1) M :=
    IsManifold.of_le (n := ∞) (by simpa using (ENat.LEInfty.out : n ≤ ∞))
  let : ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := I) (n := ⊤) (F := E)
    (E := fun x : M ↦ TangentSpace I x)
  -- The complement is the orthogonal complement for `g`.
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    Bundle.instIsContMDiffRiemannianBundle g
  refine ⟨_, hD.orthogonal, fun x ↦ ?_⟩
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  exact (D x).isCompl_orthogonal

end TauCeti
