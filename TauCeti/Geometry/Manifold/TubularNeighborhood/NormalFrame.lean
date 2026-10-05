/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Euclidean

/-!
# Local frames of the Euclidean normal bundle

For a `C^(n+1)` immersion into a finite-dimensional real inner product space, orthogonal
projection onto the normal space is `C^n`. Projecting a basis of one normal fibre onto the
nearby normal fibres gives a local frame, with the prescribed value at the original point.
These ambient-vector-valued frames provide coordinates for constructing the smooth normal
bundle before any vector-bundle structure on that family has been installed.

The normal bundle is the one used in the Euclidean tubular-neighbourhood theorem. As in
`ContDiffAt.starProjection_orthogonal_range`, the pointwise normal-projection result allows a
complete, possibly infinite-dimensional ambient space. Neither compactness nor injectivity of
the underlying map is required.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), the normal-bundle construction preceding Theorem 6.24.
-/

public section

open Set Function Filter Topology Module
open scoped Manifold ContDiff InnerProductSpace

namespace TauCeti

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞} [IsManifold I (n + 1) M] {f : M → V}

section Projection

variable [CompleteSpace V]

/-- Orthogonal projection onto the normal fibre of a `C^(n+1)` map is `C^n` at every point
where its differential is injective. -/
theorem contMDiffAt_normalSubspace_starProjection
    {x : M} (hf : ContMDiffAt I 𝓘(ℝ, V) (n + 1) f x)
    (himm : Injective (mfderiv I 𝓘(ℝ, V) f x)) :
    ContMDiffAt I 𝓘(ℝ, V →L[ℝ] V) n
      (fun y => (normalSubspace I f y).starProjection) x := by
  have h1 : (1 : WithTop ℕ∞) ≤ n + 1 := le_add_of_nonneg_left zero_le
  have hn : n ≤ n + 1 := le_add_of_nonneg_right (by simp)
  have : IsManifold I 1 M := IsManifold.of_le h1
  have : IsManifold I n M := IsManifold.of_le hn
  set e := extChartAt I x
  set g : E → V := f ∘ e.symm
  have hg : ContDiffAt ℝ (n + 1) g (e x) := by
    simpa only [I.range_eq_univ, contDiffWithinAt_univ] using
      (contMDiffAt_iff_source.mp hf).contDiffWithinAt
  have hdiff : DifferentiableAt ℝ g (e x) := hg.differentiableAt (by simp)
  have hx : x ∈ e.source := mem_extChartAt_source x
  have hQ : ContDiffAt ℝ n (fun u => (fderiv ℝ g u).rangeᗮ.starProjection) (e x) :=
    hg.fderiv_right_succ.starProjection_orthogonal_range
      (fderiv_comp_extChartAt_symm_injective hx hdiff himm)
  have hcomp := hQ.contMDiffAt.comp x (contMDiffAt_extChartAt (I := I) (n := n))
  refine hcomp.congr_of_eventuallyEq ?_
  have hgd : ∀ᶠ u in 𝓝 (e x), DifferentiableAt ℝ g u :=
    ((hg.of_le h1).eventually (by norm_num)).mono fun u hu => hu.differentiableAt one_ne_zero
  filter_upwards [(isOpen_extChartAt_source x).mem_nhds hx,
    (continuousAt_extChartAt x).tendsto hgd] with y hy hdy
  simp only [normalSubspace_eq_of_mem_source hy hdy, Function.comp_apply, g, e]

/-- For a `C^(n+1)` immersion, the family of orthogonal normal projections is `C^n`. -/
theorem contMDiff_normalSubspace_starProjection
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) :
    ContMDiff I 𝓘(ℝ, V →L[ℝ] V) n (fun x => (normalSubspace I f x).starProjection) :=
  fun x => contMDiffAt_normalSubspace_starProjection (hf x) (himm x)

end Projection

variable [FiniteDimensional ℝ V]

/-- Any basis of one normal fibre of a `C^(n+1)` immersion extends to a `C^n` local normal
frame. The frame vectors are the orthogonal projections of the prescribed basis; their values
at the original point are unchanged. At every point of the open neighbourhood they form a
basis of the full normal space, including when the codimension is zero. -/
theorem exists_contMDiffOn_normalFrame {ι : Type*}
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (x₀ : M) (b : Basis ι ℝ (normalSubspace I f x₀)) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧
      (∀ i, ContMDiffOn I 𝓘(ℝ, V) n
        (fun x => (normalSubspace I f x).starProjection (b i)) U) ∧
      ∀ x ∈ U, ∃ bx : Basis ι ℝ (normalSubspace I f x),
        ∀ i, (bx i : V) = (normalSubspace I f x).starProjection (b i) := by
  classical
  have := Module.Finite.finite_basis b
  let := Fintype.ofFinite ι
  let s : M → ι → V := fun x i => (normalSubspace I f x).starProjection (b i)
  have hs : ∀ i, ContMDiff I 𝓘(ℝ, V) n (fun x => s x i) := fun i =>
    (contMDiff_normalSubspace_starProjection hf himm).clm_apply contMDiff_const
  have hs₀ : ∀ i, s x₀ i = (b i : V) := fun i =>
    Submodule.starProjection_eq_self_iff.mpr (b i).property
  have hli₀ : LinearIndependent ℝ (s x₀) := by
    simpa only [funext hs₀, Function.comp_def, Submodule.subtype_apply] using
      b.linearIndependent.map' (normalSubspace I f x₀).subtype
        (Submodule.ker_subtype _)
  let U : Set M := {x | LinearIndependent ℝ (s x)}
  have hU : IsOpen U := isOpen_setOfPred_linearIndependent.preimage
    (continuous_pi fun i => (hs i).continuous)
  refine ⟨U, hU, hli₀, fun i => (hs i).contMDiffOn, ?_⟩
  intro x hx
  let v : ι → normalSubspace I f x := fun i =>
    ⟨s x i, Submodule.starProjection_apply_mem _ _⟩
  have hli : LinearIndependent ℝ v := (hx : LinearIndependent ℝ (s x)).of_comp
    (normalSubspace I f x).subtype
  have hdim : Fintype.card ι = Module.finrank ℝ (normalSubspace I f x) := by
    rw [← Module.finrank_eq_card_basis b]
    exact (finrank_normalSubspace (himm x₀)).trans (finrank_normalSubspace (himm x)).symm
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' v hli hdim, ?_⟩
  intro i
  simp only [coe_basisOfLinearIndependentOfCardEqFinrank']
  rfl

end TauCeti
