/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.LeviForm
public import TauCeti.Topology.LocallyFinite

/-!
# Global perturbation tolerances for strong pseudoconvexity

Strong `q`-pseudoconvexity on a complex manifold survives sufficiently small changes of the real
second derivatives in holomorphic charts. On a noncompact manifold there need not be a uniform
positive tolerance. Given a locally finite closed family subordinate to holomorphic charts, we
construct one positive continuous tolerance on the manifold which works simultaneously in every
chosen chart on its assigned closed set. A perturbation need only satisfy the bound in one of
these charts at each point.

The construction uses the openness of Levi positivity on a complex positive subspace and a
partition of unity to minorize the chartwise tolerances from
`TauCeti.exists_continuousOn_pos_forall_isStronglyPseudoconvexAt`. It does not require a globally
chosen positive subbundle, and it does not compare Hessians in preferred charts whose centres vary.
The final theorem retains the actual manifold Morse-index bound at critical points of the
perturbed function.
These are quantitative perturbation statements; no topology on a space of smooth maps is defined
here.

## Main results

* `TauCeti.exists_continuous_pos_forall_isManifoldStronglyPseudoconvexAt`: a simultaneous
  tolerance for an arbitrary locally finite closed chart family.
* `exists_locallyFinite_isClosed_forall_isManifoldStronglyPseudoconvexAt_and_manifoldMorseIndex_le`:
  construct the closed refinement and tolerance from any holomorphic chart cover;
  controlled perturbations retain strong
  `q`-pseudoconvexity and the real Morse-index bound at critical points.

## References

* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
* M. Hirsch, *Differential Topology*, Chapter 2, Section 1 (varying chartwise tolerances).
-/

public section

open Filter Function Set Topology
open scoped Manifold

namespace TauCeti

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) 2 M] [NormalSpace M] [ParacompactSpace M]

/-- A strongly `q`-pseudoconvex real `C²` function admits a single positive continuous perturbation
tolerance for all charts in any locally finite closed chart family. At a point of an assigned
closed set, controlling the second derivative in that chart suffices; the perturbing function
needs only real `C²` regularity at that point. The closed sets need not cover the manifold. -/
theorem exists_continuous_pos_forall_isManifoldStronglyPseudoconvexAt
    (q : ℕ) {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2 f)
    (hpos : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x)
    (e : ι → OpenPartialHomeomorph M E)
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) 2 M)
    {K : ι → Set M} (hK : ∀ i, IsClosed (K i)) (hlf : LocallyFinite K)
    (hKe : ∀ i, K i ⊆ (e i).source) :
    ∃ ε : C(M, ℝ), (∀ x, 0 < ε x) ∧
      ∀ (g : M → ℝ) (i : ι) (x : M), x ∈ K i →
        ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 g x →
        ‖fderiv ℝ (fderiv ℝ (g ∘ (e i).symm)) (e i x) -
          fderiv ℝ (fderiv ℝ (f ∘ (e i).symm)) (e i x)‖ < ε x →
        IsManifoldStronglyPseudoconvexAt E q g x := by
  -- Work in fixed charts, where the second derivative is continuous on the entire target.
  have hcoord (i : ι) : ContDiffOn ℝ 2 (f ∘ (e i).symm) (e i).target := by
    exact (hf.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.maximalAtlas_subset_restrictScalars ℝ (he i)))).contDiffOn
  have hsecond (i : ι) : ContinuousOn
      (fun y ↦ fderiv ℝ (fderiv ℝ (f ∘ (e i).symm)) y) (e i).target := by
    have hfirst : ContDiffOn ℝ 1 (fderiv ℝ (f ∘ (e i).symm)) (e i).target :=
      (hcoord i).fderiv_of_isOpen (e i).open_target (by norm_num)
    exact hfirst.continuousOn_fderiv_of_isOpen (e i).open_target (by norm_num)
  have hcoordpos (i : ι) (y : E) (hy : y ∈ (e i).target) :
      IsStronglyPseudoconvexAt q (f ∘ (e i).symm) y := by
    have hx := (e i).map_target hy
    have h := (isManifoldStronglyPseudoconvexAt_iff_of_mem_maximalAtlas
      (he i) hx (hf.contMDiffAt : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f ((e i).symm y))).mp
        (hpos ((e i).symm y))
    simpa only [(e i).right_inv hy] using h
  choose δ hδcont hδpos hδ using fun i ↦
    exists_continuousOn_pos_forall_isStronglyPseudoconvexAt q (hsecond i) (hcoordpos i)
  -- Pull the chartwise tolerances back to their closed sets and minorize them simultaneously.
  have hcont (i : ι) : ContinuousOn (fun x ↦ δ i (e i x)) (K i) :=
    (hδcont i).comp ((e i).continuousOn.mono (hKe i))
      (fun x hx ↦ (e i).map_source (hKe i hx))
  obtain ⟨ε, hεpos, hεδ⟩ := hlf.exists_continuous_pos_lt hK hcont
    (fun i x hx ↦ hδpos i (e i x) ((e i).map_source (hKe i hx)))
  refine ⟨ε, hεpos, fun g i x hx hg hclose ↦ ?_⟩
  apply (isManifoldStronglyPseudoconvexAt_iff_of_mem_maximalAtlas
    (he i) (hKe i hx) hg).mpr
  exact hδ i (g ∘ (e i).symm) (e i x) ((e i).map_source (hKe i hx))
    (hclose.trans (hεδ i x hx))

/-- Every holomorphic chart cover admits a locally finite closed refinement and a positive
continuous tolerance preserving strong `q`-pseudoconvexity of a real `C²` function. Any real `C²`
perturbation satisfying the coordinate second-derivative bounds retains the real Morse-index
bound at its critical points. No properness or nondegeneracy is asserted. -/
theorem
  exists_locallyFinite_isClosed_forall_isManifoldStronglyPseudoconvexAt_and_manifoldMorseIndex_le
    (q : ℕ) {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2 f)
    (hpos : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x)
    (e : ι → OpenPartialHomeomorph M E)
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) 2 M)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source) :
    ∃ (K : ι → Set M) (ε : C(M, ℝ)),
      LocallyFinite K ∧ (∀ i, IsClosed (K i)) ∧ (∀ i, K i ⊆ (e i).source) ∧
      (∀ x, ∃ i, x ∈ K i) ∧ (∀ x, 0 < ε x) ∧
      ∀ (g : M → ℝ), ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2 g →
        (∀ i, ∀ x ∈ K i,
          ‖fderiv ℝ (fderiv ℝ (g ∘ (e i).symm)) (e i x) -
            fderiv ℝ (fderiv ℝ (f ∘ (e i).symm)) (e i x)‖ < ε x) →
        ∀ x, IsManifoldStronglyPseudoconvexAt E q g x ∧
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) g x = 0 →
            manifoldMorseIndex 𝓘(ℝ, E) g x ≤ Module.finrank ℂ E + q) := by
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun i ↦ (e i).source) (fun i ↦ (e i).open_source)
    (fun x _ ↦ mem_iUnion.mpr (hcover x))
  let K (i : ι) := tsupport (ρ i)
  have hK (i : ι) : IsClosed (K i) := isClosed_tsupport _
  have hKcover (x : M) : ∃ i, x ∈ K i := by
    obtain ⟨i, hi⟩ := ρ.exists_pos (mem_univ x)
    exact ⟨i, subset_closure (mem_support.mpr hi.ne')⟩
  obtain ⟨ε, hε, hpert⟩ := exists_continuous_pos_forall_isManifoldStronglyPseudoconvexAt
    q hf hpos e he hK ρ.locallyFinite_tsupport hρ
  refine ⟨K, ε, ρ.locallyFinite_tsupport, hK, hρ, hKcover, hε, fun g hg hclose x ↦ ?_⟩
  obtain ⟨i, hi⟩ := hKcover x
  have h := hpert g i x hi hg.contMDiffAt (hclose i x hi)
  exact ⟨h, h.manifoldMorseIndex_le hg.contMDiffAt⟩

end TauCeti
