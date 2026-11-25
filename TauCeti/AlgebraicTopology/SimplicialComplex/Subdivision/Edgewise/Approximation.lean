/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Edgewise.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization

import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Edgewise.Fatness
import TauCeti.Analysis.Convex.Interpolation

/-!
# Uniform approximation in values on edgewise subdivisions

For a continuous map on a closed simplex, the secant maps on its edgewise subdivisions
approximate the original map uniformly in value. One subdivision order works simultaneously
for every face and every point of each face. No differentiability or lower bound on the
fatness of the faces is required.

The comparison is stated in barycentric coordinates: the original map is evaluated at the
barycentre of the subdivision vertices, and its secant map uses the same weights on their
images. This is the zeroth-order part of secant approximation in smooth triangulation.

## References

* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966),
  Chapter II, Section 9 (secant approximations) and Theorems 10.5–10.6.
* H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*, Ann. of Math. 43
  (1942), 580–582.
-/

public section

open AbstractSimplicialComplex PreAbstractSimplicialComplex Filter

/-- The secant maps of a continuous map on a closed simplex approximate it uniformly in
value on all faces of sufficiently fine edgewise subdivisions. Here `p` places the vertices
of a subdivision face in the original simplex, and `q` is their barycentre with weights `x`.
The ambient complex and its vertex type need not be finite. -/
theorem Continuous.eventually_norm_sum_smul_sub_lt_edgewiseSubdivision
    {ι E : Type*} [LinearOrder ι] [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {σ : Finset ι} {g : StandardSimplex σ → E} (hg : Continuous g)
    (K : PreAbstractSimplicialComplex ι) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ ρ ∈ K.edgewiseSubdivision k, ∀ p : ρ → StandardSimplex σ,
      (∀ a, (p a : ι →₀ ℝ) = TauCeti.edgewisePoint a.val.val) →
      ∀ (x : StandardSimplex ρ) (q : StandardSimplex σ),
        (∀ i : σ, q.val i = ∑ a : ρ, x.val a • (p a).val i) →
        ‖(∑ a : ρ, x.val a • g (p a)) - g q‖ < ε := by
  -- Read the compact simplex in its finite-dimensional coordinate space.
  let e := (Finset.standardSimplexHomeomorph σ).trans
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ σ).toHomeomorph
  let f := g ∘ e.symm
  have := e.compactSpace
  have hf : UniformContinuous f :=
    CompactSpace.uniformContinuous_of_continuous (hg.comp e.symm.continuous)
  obtain ⟨δ, hδ, happrox⟩ := hf.exists_pos_forall_norm_sum_smul_sub_lt hε
  obtain ⟨N, hN⟩ := exists_nat_gt δ⁻¹
  filter_upwards [eventually_ge_atTop N] with k hk ρ hρ p hp x q hq
  have hkδ : δ⁻¹ < k := hN.trans_le (Nat.cast_le.mpr hk)
  have hweights : ∑ a : ρ, x.val a = 1 := by
    simpa [Finsupp.sum_fintype] using (Finset.standardSimplexHomeomorph ρ x).total
  have he (y : StandardSimplex σ) (i : σ) : (e y).val i = y.val i := by
    simp [e]
  have hdist (a b : ρ) : ‖(e (p a)).val - (e (p b)).val‖ ≤ δ := by
    have heq (y : StandardSimplex σ) : (e y).val = fun i : σ => y.val i := funext (he y)
    simp only [heq, hp]
    exact (norm_edgewisePoint_sub_edgewisePoint_le hρ a.property b.property σ).trans
      (inv_lt_of_inv_lt₀ hδ hkδ).le
  have hq' : (e q).val = ∑ a : ρ, x.val a • (e (p a)).val := by
    ext i
    simpa only [Finset.sum_apply, Pi.smul_apply, he] using hq i
  simpa only [f, Function.comp_apply, Homeomorph.symm_apply_apply] using
    happrox (fun a => e (p a)) (fun a => x.val a)
      (fun a => StandardSimplex.nonneg x a) hweights hdist (e q) hq'

/-- A continuous map on a closed simplex varies arbitrarily little on all faces of sufficiently
fine edgewise subdivisions. Here `p` places the vertices of a subdivision face in the original
simplex, and `q` and `r` are their barycentres with weights `x` and `y`. The ambient complex and
its vertex type need not be finite. -/
theorem Continuous.eventually_norm_sub_lt_of_mem_edgewiseSubdivision
    {ι E : Type*} [LinearOrder ι] [SeminormedAddCommGroup E]
    {σ : Finset ι} {g : StandardSimplex σ → E} (hg : Continuous g)
    (K : PreAbstractSimplicialComplex ι) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ ρ ∈ K.edgewiseSubdivision k, ∀ p : ρ → StandardSimplex σ,
      (∀ a, (p a : ι →₀ ℝ) = TauCeti.edgewisePoint a.val.val) →
      ∀ (x y : StandardSimplex ρ) (q r : StandardSimplex σ),
        (∀ i : σ, q.val i = ∑ a : ρ, x.val a • (p a).val i) →
        (∀ i : σ, r.val i = ∑ a : ρ, y.val a • (p a).val i) → ‖g q - g r‖ < ε := by
  -- Read the compact simplex in its finite-dimensional coordinate space, where `g` is uniformly
  -- continuous.
  let e := (Finset.standardSimplexHomeomorph σ).trans
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ σ).toHomeomorph
  have := e.compactSpace
  obtain ⟨η, hη, hgη⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous (hg.comp e.symm.continuous)) ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt η⁻¹
  filter_upwards [eventually_ge_atTop N] with k hk ρ hρ p hp x y q r hq hr
  have hkη : (k : ℝ)⁻¹ < η := inv_lt_of_inv_lt₀ hη (hN.trans_le (Nat.cast_le.mpr hk))
  have he (z : StandardSimplex σ) : (e z).val = fun i : σ => z.val i := by
    ext i
    simp [e]
  -- Both `e q` and `e r` lie in the convex hull of the points `e (p a)`, which has the diameter
  -- of that finite set, at most `1 / k`.
  set v : ρ → σ → ℝ := fun a => (e (p a)).val
  have hmem (w : StandardSimplex ρ) (s : StandardSimplex σ)
      (hs : ∀ i : σ, s.val i = ∑ a : ρ, w.val a • (p a).val i) :
      (e s).val ∈ convexHull ℝ (Set.range v) := by
    have hweights : ∑ a : ρ, w.val a = 1 := by
      simpa [Finsupp.sum_fintype] using (Finset.standardSimplexHomeomorph ρ w).total
    have hs' : (e s).val = ∑ a : ρ, w.val a • v a := by
      ext i
      simpa only [Finset.sum_apply, Pi.smul_apply, he, v] using hs i
    rw [hs']
    exact (convex_convexHull ℝ _).sum_mem (fun a _ => StandardSimplex.nonneg w a) hweights
      fun a _ => subset_convexHull ℝ _ (Set.mem_range_self a)
  have hdist : dist (e q) (e r) < η := by
    rw [Subtype.dist_eq]
    refine (Metric.dist_le_diam_of_mem (isBounded_convexHull.mpr (Set.finite_range v).isBounded)
      (hmem x q hq) (hmem y r hr)).trans_lt (lt_of_le_of_lt ?_ hkη)
    rw [convexHull_diam]
    refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    simpa only [dist_eq_norm, v, he, hp] using
      norm_edgewisePoint_sub_edgewisePoint_le hρ a.property b.property σ
  simpa only [Function.comp_apply, Homeomorph.symm_apply_apply, dist_eq_norm] using hgη hdist
