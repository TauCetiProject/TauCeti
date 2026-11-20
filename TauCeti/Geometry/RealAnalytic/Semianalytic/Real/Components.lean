/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAnalytic.Semianalytic.Real
import TauCeti.Topology.ConnectedComponents

/-!
# Components of semianalytic subsets of the real line

The local three-cell normal form gives a finite cover by preconnected semianalytic sets in
an arbitrarily small interval about every ambient point, including frontier points outside
the set. Only finitely many global components meet that interval. Independently of
semianalyticity of the original set, each real-line component is preconnected and therefore
semianalytic.

## References

S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore
di Pisa (3) 18 (1964), 449–474, §1.
-/

public section

open Filter Set Topology

namespace TauCeti

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
    have hp : IsPreconnected (cell ε) :=
      (ordConnected_Ioo.inter (ordConnected_singleton.preimage_mono
        (f := fun y => SignType.sign (y - x))
        fun _ _ h => SignType.sign.mono (sub_le_sub_right h x))).isPreconnected
    exact ⟨hp, hp.isSemianalytic⟩
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
@[simp]
theorem isSemianalytic_connectedComponentIn_real (s : Set ℝ) (y : ℝ) :
    IsSemianalytic (_root_.connectedComponentIn s y) :=
  isPreconnected_connectedComponentIn.isSemianalytic

end TauCeti
