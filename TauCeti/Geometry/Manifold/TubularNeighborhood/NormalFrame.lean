/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Euclidean
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Local frames of the Euclidean normal bundle

For a `C^(n+1)` immersion into a finite-dimensional real inner product space, orthogonal
projection onto the normal space is `C^n`. Projecting a basis of one normal fibre onto the
nearby normal fibres gives a local frame, with the prescribed value at the original point.
Pulled back along a smooth retraction `r` onto the immersed manifold, the normal projection
`q ↦ P_N(r q)` is again smooth, and when the displacement `q - f (r q)` is normal, the differential
of `f ∘ r` at a point of the image is the orthogonal projection onto the tangent space.
These ambient-vector-valued frames provide coordinates for constructing the smooth normal
bundle before any vector-bundle structure on that family has been installed.

The normal bundle is the one used in the Euclidean tubular-neighbourhood theorem. As in
`ContDiffAt.starProjection_orthogonal_range`, the pointwise normal-projection result allows a
possibly infinite-dimensional ambient space, which need not be complete. Neither compactness nor
injectivity of the underlying map is required.

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

section Retraction

variable {r : V → M}

/-- The orthogonal projection onto the normal space of an immersion `f` at `r q` is `C^n` in `q`
at a point where `r` is `C^n`, when `f` is `C^(n + 1)` at `r q`. -/
theorem contDiffAt_starProjection_normalSubspace_comp {q : V}
    (hf : ContMDiffAt I 𝓘(ℝ, V) (n + 1) f (r q))
    (himm : Injective (mfderiv I 𝓘(ℝ, V) f (r q))) (hr : ContMDiffAt 𝓘(ℝ, V) I n r q) :
    ContDiffAt ℝ n (fun q ↦ (normalSubspace I f (r q)).starProjection) q :=
  contMDiffAt_iff_contDiffAt.mp ((contMDiffAt_normalSubspace_starProjection hf himm).comp q hr)

/-- At a point `f x` whose base point `x` is fixed by the retraction `r`, the orthogonal projection
onto the normal space of an immersion `f` at `r q` is `C^n` in `q` at `f x`, when `f` is `C^(n + 1)`
at `x` and `r` is `C^n` at `f x`. -/
theorem contDiffAt_starProjection_normalSubspace_comp_of_retract
    {x : M} (hf : ContMDiffAt I 𝓘(ℝ, V) (n + 1) f x) (himm : Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hr : ContMDiffAt 𝓘(ℝ, V) I n r (f x)) (hrx : r (f x) = x) :
    ContDiffAt ℝ n (fun q ↦ (normalSubspace I f (r q)).starProjection) (f x) :=
  contDiffAt_starProjection_normalSubspace_comp (by rwa [hrx]) (by rwa [hrx]) hr

/-- Let `r` be a `C^n` retraction, `n ≥ 1`, onto a map `f` near `f x`, with normal displacement,
where `f` is `C^(n + 1)` and immersive at `x`. Then the differential of `f ∘ r` at `f x` is the
orthogonal projection onto the tangent space of the immersed manifold at `f x`. -/
theorem hasFDerivAt_comp_of_eventually_sub_mem_normalSubspace
    {x : M} (hf : ContMDiffAt I 𝓘(ℝ, V) (n + 1) f x) (hn : 1 ≤ n)
    (himm : Injective (mfderiv I 𝓘(ℝ, V) f x)) (hr : ContMDiffAt 𝓘(ℝ, V) I n r (f x))
    (hrx : r (f x) = x)
    (hnormal : ∀ᶠ q in 𝓝 (f x), q - f (r q) ∈ normalSubspace I f (r q)) :
    HasFDerivAt (f ∘ r) (normalSubspace I f x)ᗮ.starProjection (f x) := by
  have hn0 : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  have hfx : MDifferentiableAt I 𝓘(ℝ, V) f (r (f x)) := by
    rw [hrx]
    exact hf.mdifferentiableAt (by simp)
  have hrd : MDifferentiableAt 𝓘(ℝ, V) I r (f x) := hr.mdifferentiableAt hn0
  have hg : DifferentiableAt ℝ (f ∘ r) (f x) :=
    mdifferentiableAt_iff_differentiableAt.mp (hfx.comp _ hrd)
  have hN :=
    (contDiffAt_starProjection_normalSubspace_comp_of_retract hf himm hr hrx).differentiableAt hn0
  set D := fderiv ℝ (f ∘ r) (f x)
  -- `D` takes values in the tangent space, since it factors through the differential of `f`.
  have hrange (h : V) : D h ∈ (normalSubspace I f x)ᗮ := by
    have hD : D h = mfderiv I 𝓘(ℝ, V) f (r (f x)) (mfderiv 𝓘(ℝ, V) I r (f x) h) :=
      (mvfderiv_eq_fderiv_apply (f ∘ r) (f x) h).symm.trans
        ((mvfderiv_apply_eq_mfderiv_apply (f ∘ r) (f x) h).trans
          (mfderiv_comp_apply (f x) hfx hrd h))
    have : D h ∈ (normalSubspace I f (r (f x)))ᗮ := fun u hu ↦ by
      rw [hD]
      exact mem_normalSubspace_iff.mp hu _
    rwa [hrx] at this
  -- Differentiating `P_N(r q) (q - f (r q)) = q - f (r q)` shows that `h - D h` is normal.
  have hzero : (fun q ↦ (normalSubspace I f (r q)).starProjection (q - (f ∘ r) q) -
      (q - (f ∘ r) q)) =ᶠ[𝓝 (f x)] fun _ ↦ 0 := by
    filter_upwards [hnormal] with q hq
    rw [Function.comp_apply, Submodule.starProjection_eq_self_iff.mpr hq, sub_self]
  have hderiv := ((hN.hasFDerivAt.clm_apply ((hasFDerivAt_id _).sub hg.hasFDerivAt)).sub
    ((hasFDerivAt_id _).sub hg.hasFDerivAt)).unique
    ((hasFDerivAt_const 0 (f x)).congr_of_eventuallyEq hzero)
  have hnormalD (h : V) : h - D h ∈ normalSubspace I f x := by
    -- Evaluated at `h`, the derivative is `P_N(x) (h - D h) + N' h (f x - (f ∘ r) (f x)) -
    -- (h - D h)`, where `N' h` is the derivative of `q ↦ P_N(r q)` along `h`. The middle term
    -- vanishes, since `(f ∘ r) (f x) = f x`.
    have hev : (normalSubspace I f (r (f x))).starProjection (h - D h) +
        fderiv ℝ (fun q ↦ (normalSubspace I f (r q)).starProjection) (f x) h
          (f x - (f ∘ r) (f x)) - (h - D h) = 0 :=
      DFunLike.congr_fun hderiv h
    have hP : (normalSubspace I f x).starProjection (h - D h) = h - D h := by
      rwa [Function.comp_apply, hrx, sub_self, map_zero, add_zero, sub_eq_zero] at hev
    exact Submodule.starProjection_eq_self_iff.mp hP
  refine hg.hasFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun h ↦ ?_)
  calc D h = (normalSubspace I f x)ᗮ.starProjection (D h) +
        (normalSubspace I f x)ᗮ.starProjection (h - D h) := by
        rw [Submodule.starProjection_eq_self_iff.mpr (hrange h),
          (Submodule.starProjection_apply_eq_zero_iff _).mpr
            (Submodule.le_orthogonal_orthogonal _ (hnormalD h)), add_zero]
    _ = (normalSubspace I f x)ᗮ.starProjection h := by rw [← map_add, add_sub_cancel]

end Retraction

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
  obtain ⟨U, hUli, hU, hx₀U⟩ := mem_nhds_iff.mp <|
    eventually_linearIndependent_starProjection_apply (b := fun i => (b i : V))
      (contMDiff_normalSubspace_starProjection hf himm).continuous.continuousAt
      (b.linearIndependent.map' (normalSubspace I f x₀).subtype (Submodule.ker_subtype _))
      fun i => (b i).property
  refine ⟨U, hU, hx₀U, fun i => (hs i).contMDiffOn, ?_⟩
  intro x hx
  let v : ι → normalSubspace I f x := fun i =>
    ⟨s x i, Submodule.starProjection_apply_mem _ _⟩
  have hli : LinearIndependent ℝ v := (hUli hx : LinearIndependent ℝ (s x)).of_comp
    (normalSubspace I f x).subtype
  have hdim : Fintype.card ι = Module.finrank ℝ (normalSubspace I f x) := by
    rw [← Module.finrank_eq_card_basis b]
    exact (finrank_normalSubspace (himm x₀)).trans (finrank_normalSubspace (himm x)).symm
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' v hli hdim, ?_⟩
  intro i
  simp only [coe_basisOfLinearIndependentOfCardEqFinrank']
  rfl

end TauCeti
