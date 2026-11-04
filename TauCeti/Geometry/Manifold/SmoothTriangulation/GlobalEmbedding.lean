/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.Edgewise
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Basic
import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite
import TauCeti.Topology.MetricSpace.LocalToGlobalInjectivity

/-!
# From starwise injectivity to global secant embeddings

For a continuous embedding of a finite complex into a real normed space, its secant maps on
sufficiently fine edgewise subdivisions are closed embeddings as soon as they are injective
on the inverse images of the original open vertex stars.

The patches here are fixed stars of the original complex, not individual simplices of the
subdivision. Thus the local hypothesis must also exclude collisions across adjacent simplices.
Uniform convergence of the secant maps then excludes all remaining collisions, between points
not contained in a common star. This is the local-to-global step in secant approximation;
it does not establish starwise injectivity or the existence of a smooth triangulation.

## References

* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966),
  Chapter II, Section 9 (secant approximation), and Theorems 10.5–10.6.
* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
-/

public section

open Set Function AbstractSimplicialComplex Filter

namespace Continuous

variable {ι : Type*} [LinearOrder ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : AbstractSimplicialComplex ι} {f : Realization K → E}

/-- On every sufficiently fine edgewise subdivision of a finite complex, the secant map of a
continuous injection is a closed embedding if it is injective on the inverse image of each
open vertex star of the original complex. In particular, local injectivity is required across
subdivided faces, not merely on each face separately. -/
theorem eventually_isClosedEmbedding_secantMap_edgewiseSubdivision_of_injOn_openStar
    (hf : Continuous f) (hinj : Injective f) (hK : K.faces.Finite) :
    ∀ᶠ k in atTop,
      (∀ v, InjOn ((K.edgewiseSubdivision k).secantMap
          (f ∘ edgewiseSubdivisionRealizationMap K k))
        (edgewiseSubdivisionRealizationMap K k ⁻¹' K.openStarRealization v)) →
      Topology.IsClosedEmbedding ((K.edgewiseSubdivision k).secantMap
        (f ∘ edgewiseSubdivisionRealizationMap K k)) := by
  let : CompactSpace (Realization K) := K.compactSpace_realization_of_finite_faces hK
  obtain ⟨ε, hε, hglobal⟩ := hf.exists_pos_forall_injective_of_injOn_cover hinj
    K.openStarRealization K.isOpen_openStarRealization K.iUnion_openStarRealization
  filter_upwards [eventually_ne_atTop 0,
    hf.eventually_norm_secantMap_sub_lt_edgewiseSubdivision hK hε] with k hk hclose hstar
  let e := edgewiseSubdivisionRealizationHomeomorph K hk
  let s := (K.edgewiseSubdivision k).secantMap (f ∘ edgewiseSubdivisionRealizationMap K k)
  -- Transport the approximating map to the fixed realization, where the open-star cover lives.
  have hmap (x : Realization (K.edgewiseSubdivision k)) :
      edgewiseSubdivisionRealizationMap K k x = e x :=
    (edgewiseSubdivisionRealizationHomeomorph_apply hk x).symm
  have hmap_symm (x : Realization K) :
      edgewiseSubdivisionRealizationMap K k (e.symm x) = x :=
    (hmap _).trans (e.apply_symm_apply x)
  have hnear : ∀ x, dist ((s ∘ e.symm) x) (f x) < ε := by
    intro x
    have h := hclose (e.symm x)
    rw [hmap_symm x] at h
    simpa only [comp_apply, dist_eq_norm] using h
  have hinj_fixed : Injective (s ∘ e.symm) := by
    refine hglobal _ hnear fun v x hx y hy hxy ↦ ?_
    apply e.symm.injective
    exact hstar v (by simpa only [mem_preimage, hmap_symm] using hx)
      (by simpa only [mem_preimage, hmap_symm] using hy) hxy
  have hinj_secant : Injective s := by
    intro x y hxy
    apply e.injective
    apply hinj_fixed
    simpa only [comp_apply, e.symm_apply_apply] using hxy
  let : CompactSpace (Realization (K.edgewiseSubdivision k)) := e.symm.compactSpace
  exact (continuous_secantMap _).isClosedEmbedding hinj_secant

end Continuous
