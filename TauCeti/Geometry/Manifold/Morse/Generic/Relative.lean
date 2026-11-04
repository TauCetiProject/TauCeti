/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Generic.Basic

/-!
# Relative Morse approximation on compact sets

A smooth function which is already Morse near the intersection of a compact set with a closed
set can be made Morse on the compact set without changing it near the closed set. The perturbation
has compact support in the complement of the closed set and can be chosen in any weak Whitney
neighbourhood. This is
the local relative step used when treating successively larger compact regions of a manifold.
No global Morse approximation or convergence of infinitely many perturbations is asserted.

The proof applies compactly supported local Morse approximation away from a smaller
neighbourhood of the protected set, preserving nondegeneracy on the remaining compact region.

## References

* M. Hirsch, *Differential Topology*, Chapter 6, Section 1.
* V. Guillemin and A. Pollack, *Differential Topology*, Chapter 1, Section 7.
-/

public section

open Filter Set
open scoped Manifold Topology ContDiff TauCeti.ManifoldWeakWhitney

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]

/-- **Relative compact Morse approximation.** If `f` is Morse on an open neighbourhood `V` of
`K ∩ C`, where `K` is compact and `C` is closed, it admits arbitrarily small weak Whitney
perturbations which are Morse on `K` and whose difference from `f` has compact support disjoint
from `C`. Consequently the perturbed function agrees with `f` on a neighbourhood of all of `C`,
not only on `C` itself. Neither `C` nor `V` is required to be compact. -/
theorem _root_.ContMDiffMap.exists_isMorseOn_hasCompactSupport_sub_compl
    (f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) {K C V : Set M} (hK : IsCompact K) (hC : IsClosed C)
    (hV : IsOpen V) (hKCV : K ∩ C ⊆ V) (hfV : IsMorseOn I f V)
    {𝒰 : Set C^∞⟮I, M; 𝓘(ℝ), ℝ⟯} (h𝒰 : 𝒰 ∈ 𝓝 f) :
    ∃ g ∈ 𝒰, IsMorseOn I g K ∧ HasCompactSupport (fun y ↦ g y - f y) ∧
      tsupport (fun y ↦ g y - f y) ⊆ Cᶜ := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨O, hO, hKCO, hOV⟩ := (hK.inter_right hC).exists_isOpen_closure_subset
    (hV.mem_nhdsSet.mpr hKCV)
  have hKO : K \ O ⊆ Cᶜ := by
    intro x hx hxC
    exact hx.2 (hKCO ⟨hx.1, hxC⟩)
  obtain ⟨g, hg, hgm, hgc, hgs⟩ := f.exists_isMorseOn_union_hasCompactSupport_sub
    (hK.diff hO) hC.isOpen_compl hKO (hK.inter_right isClosed_closure)
    (hfV.mono (inter_subset_right.trans hOV)) h𝒰
  refine ⟨g, hg, hgm.mono ?_, hgc, hgs⟩
  intro x hx
  by_cases hxO : x ∈ O
  · exact Or.inl ⟨hx, subset_closure hxO⟩
  · exact Or.inr ⟨hx, hxO⟩

end TauCeti
