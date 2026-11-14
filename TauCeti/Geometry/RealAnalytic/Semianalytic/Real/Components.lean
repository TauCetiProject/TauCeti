/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAnalytic.Semianalytic.Real.Basic
public import TauCeti.Topology.ConnectedComponents

/-!
# Components of semianalytic subsets of the real line

The local three-cell normal form gives a finite cover by preconnected semianalytic sets in
an arbitrarily small interval about every ambient point. Hence the distinct nonempty
components form a locally finite family in the ambient line, including at frontier points
outside the set. Only finitely many components meet any compact set. Independently of
semianalyticity of the original set, each real-line component is preconnected and therefore
semianalytic.

The finiteness arguments use `Set.Finite.image_connectedComponentIn_sUnion` and
`TauCeti.locallyFinite_connectedComponentIn_iff`; no closedness or boundedness of the original
set is needed. These results provide the component calculus for one-dimensional local
semianalytic decompositions.

## References

S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore
di Pisa (3) 18 (1964), 449–474, §1.
-/

public section

open Filter Set Topology

namespace TauCeti

private theorem real_sign_cell {a x b : ℝ} (hx : x ∈ Ioo a b) (ε : SignType) :
    IsPreconnected (Ioo a b ∩ {y | SignType.sign (y - x) = ε}) ∧
      IsSemianalytic (Ioo a b ∩ {y | SignType.sign (y - x) = ε}) := by
  rcases ε with _ | _ | _
  · have heq : Ioo a b ∩ {y | SignType.sign (y - x) = 0} = {x} := by
      ext y
      simp only [mem_inter_iff, mem_ofPred_eq, sign_eq_zero_iff, sub_eq_zero, mem_singleton_iff]
      exact ⟨And.right, fun h => h.symm ▸ ⟨hx, rfl⟩⟩
    rw [SignType.zero_eq_zero, heq]
    exact ⟨isPreconnected_singleton, isSemianalytic_singleton x⟩
  · have heq : Ioo a b ∩ {y | SignType.sign (y - x) = -1} = Ioo a x := by
      ext y
      simp only [mem_inter_iff, mem_ofPred_eq, sign_eq_neg_one_iff, sub_neg, mem_Ioo]
      grind
    rw [SignType.neg_eq_neg_one, heq]
    exact ⟨isPreconnected_Ioo, isSemianalytic_Ioo a x⟩
  · have heq : Ioo a b ∩ {y | SignType.sign (y - x) = 1} = Ioo x b := by
      ext y
      simp only [mem_inter_iff, mem_ofPred_eq, sign_eq_one_iff, sub_pos, mem_Ioo]
      grind
    rw [SignType.pos_eq_one, heq]
    exact ⟨isPreconnected_Ioo, isSemianalytic_Ioo x b⟩

/-- Near an ambient point where a subset of the real line is semianalytic, its restriction
has a finite cover by preconnected semianalytic sets. The interval can be chosen in any
prescribed neighborhood. Empty sets and centers outside the set are allowed. -/
theorem SemianalyticAt.exists_Ioo_finite_isPreconnected_cover {s V : Set ℝ} {x : ℝ}
    (hs : SemianalyticAt s x) (hV : V ∈ 𝓝 x) :
    ∃ a b, x ∈ Ioo a b ∧ Ioo a b ⊆ V ∧ ∃ 𝒞 : Set (Set ℝ), 𝒞.Finite ∧
      (∀ t ∈ 𝒞, IsPreconnected t ∧ IsSemianalytic t) ∧ ⋃₀ 𝒞 = s ∩ Ioo a b := by
  obtain ⟨a, b, hx, hV, C, hmem⟩ := hs.exists_Ioo_mem_iff_sign_mem hV
  let cell : SignType → Set ℝ := fun ε => Ioo a b ∩ {y | SignType.sign (y - x) = ε}
  refine ⟨a, b, hx, hV, cell '' C, C.toFinite.image cell, ?_, ?_⟩
  · rintro t ⟨ε, _, rfl⟩
    exact real_sign_cell hx ε
  · ext y
    simp only [mem_sUnion, mem_image, exists_exists_and_eq_and, cell, mem_inter_iff,
      mem_ofPred_eq]
    exact ⟨fun ⟨_, hε, hy, heq⟩ => ⟨(hmem y hy).2 (heq ▸ hε), hy⟩,
      fun ⟨hys, hy⟩ => ⟨_, (hmem y hy).1 hys, hy, rfl⟩⟩

/-- Only finitely many global components meet a sufficiently small interval near an ambient
semianalytic real point, whether or not that point belongs to the set. -/
theorem SemianalyticAt.exists_Ioo_finite_image_connectedComponentIn {s V : Set ℝ} {x : ℝ}
    (hs : SemianalyticAt s x) (hV : V ∈ 𝓝 x) :
    ∃ a b, x ∈ Ioo a b ∧ Ioo a b ⊆ V ∧
      (_root_.connectedComponentIn s '' (s ∩ Ioo a b)).Finite := by
  obtain ⟨a, b, hx, hV, 𝒞, h𝒞, hc, hcover⟩ := hs.exists_Ioo_finite_isPreconnected_cover hV
  refine ⟨a, b, hx, hV, ?_⟩
  rw [← hcover]
  exact h𝒞.image_connectedComponentIn_sUnion (fun t ht => (hc t ht).1)
    (hcover ▸ inter_subset_left)

/-- Every connected component of any subset of the real line is semianalytic. A point outside
the set gives the empty component. -/
theorem isSemianalytic_connectedComponentIn_real (s : Set ℝ) (y : ℝ) :
    IsSemianalytic (_root_.connectedComponentIn s y) :=
  isPreconnected_connectedComponentIn.isSemianalytic

/-- The distinct nonempty connected components of a semianalytic subset of the real line
form a locally finite family in the ambient line. Indexing by distinct sets avoids repetitions
from different points of the same component. -/
theorem IsSemianalytic.locallyFinite_connectedComponentIn_real {s : Set ℝ}
    (hs : IsSemianalytic s) :
    LocallyFinite (fun C : (_root_.connectedComponentIn s '' s) => (C : Set ℝ)) := by
  refine locallyFinite_connectedComponentIn_iff.2 fun x => ?_
  obtain ⟨a, b, hx, _, hfin⟩ :=
    (hs.semianalyticAt x).exists_Ioo_finite_image_connectedComponentIn (V := univ) univ_mem
  exact ⟨Ioo a b, Ioo_mem_nhds hx.1 hx.2, hfin⟩

/-- Only finitely many global connected components of a semianalytic subset of the real
line meet a given compact set. The components themselves need not be bounded or closed. -/
theorem IsSemianalytic.finite_image_connectedComponentIn_inter_real {s K : Set ℝ}
    (hs : IsSemianalytic s) (hK : IsCompact K) :
    (_root_.connectedComponentIn s '' (s ∩ K)).Finite :=
  hs.locallyFinite_connectedComponentIn_real.finite_image_connectedComponentIn_inter hK

end TauCeti
