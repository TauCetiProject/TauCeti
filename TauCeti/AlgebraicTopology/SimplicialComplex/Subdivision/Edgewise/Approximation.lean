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
      (∀ a, (p a : ι →₀ ℝ) = TauCeti.edgewisePoint a.1.1) →
      ∀ (x : StandardSimplex ρ) (q : StandardSimplex σ),
        (∀ i : σ, q.1 i = ∑ a : ρ, x.1 a • (p a).1 i) →
        ‖(∑ a : ρ, x.1 a • g (p a)) - g q‖ < ε := by
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
  have hweights : ∑ a : ρ, x.1 a = 1 := by
    simpa [Finsupp.sum_fintype] using (Finset.standardSimplexHomeomorph ρ x).total
  have he (y : StandardSimplex σ) (i : σ) : (e y).1 i = y.1 i := by
    simp [e]
  have hdist (a b : ρ) : ‖(e (p a)).1 - (e (p b)).1‖ ≤ δ := by
    have heq (y : StandardSimplex σ) : (e y).1 = fun i : σ => y.1 i := funext (he y)
    simp only [heq, hp]
    exact (norm_edgewisePoint_sub_edgewisePoint_le hρ a.2 b.2 σ).trans
      (inv_lt_of_inv_lt₀ hδ hkδ).le
  have hq' : (e q).1 = ∑ a : ρ, x.1 a • (e (p a)).1 := by
    ext i
    simpa only [Finset.sum_apply, Pi.smul_apply, he] using hq i
  simpa only [f, Function.comp_apply, Homeomorph.symm_apply_apply] using
    happrox (fun a => e (p a)) (fun a => x.1 a)
      (fun a => StandardSimplex.nonneg x a) hweights hdist (e q) hq'
