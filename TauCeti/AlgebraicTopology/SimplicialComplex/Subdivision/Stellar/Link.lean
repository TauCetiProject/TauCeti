/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Basic

/-!
# Links of old faces after stellar subdivision

Starring `σ` at `v` changes the link of a face `τ` avoiding `v` by starring its old link
at `σ \ τ`. This includes faces meeting `σ`: their links are starred at the complementary
part of `σ`, rather than at `σ` itself. If `τ` contains `σ`, it is removed and both sides
of the formula are void, since starring the empty set gives the void complex.

These link identities transfer sphere-or-ball link conditions at surviving old vertices when
the starring vertex is unused in their old links, and preserve void links in dimension zero.
The complementary new-vertex link is the boundary of the closed star, computed in
`Subdivision.Stellar.Basic`.

## References

* G. Cunningham, D. Zach, S. Friedl,
  *Formalizing Abstract Simplicial Complexes & Stellar Subdivisions in Lean* (2026),
  [Theorem 3.9 in the preprint](https://arxiv.org/html/2607.10216v1#S3.Thmtheorem9)
  (Theorem 19 in the published version), and the associated
  [`not-gary/pachner` formalization](https://github.com/not-gary/pachner),
  `stellarSubdivision_anticomm_link` in `Pachner/Results/StellarSubdivAnticommLink.lean`.
  `link_stellarSubdivision_of_notMem` extends their link–stellar-subdivision identity
  to arbitrary precomplexes and sets avoiding the starring vertex.
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2 and 3 (stellar subdivision and links).
* W. B. R. Lickorish, *Simplicial moves on complexes and manifolds*, Geom. Topol. Monogr. 2
  (1999), 299–320.
-/

public section

open Finset

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι}
  {σ τ : Finset ι} {v w : ι} {n : ℕ}

/-- The link of a face avoiding the starring vertex is the stellar subdivision of its old link
at the part of the starred set outside that face. No face or freshness hypotheses are required;
in particular, a removed face has void link on both sides. -/
@[simp]
theorem link_stellarSubdivision_of_notMem (hvτ : v ∉ τ) :
    link (stellarSubdivision K σ v) τ = stellarSubdivision (link K τ) (σ \ τ) v := by
  refine SetLike.ext fun ω => ?_
  have hsub (ρ : Finset ι) : σ ⊆ ρ ∪ τ ↔ σ \ τ ⊆ ρ := sdiff_le_iff'.symm
  have hunion (ρ : Finset ι) : (ρ ∪ (σ \ τ)) ∪ τ = (ρ ∪ τ) ∪ σ := by
    simp only [union_assoc, sdiff_union_self_eq_union, union_comm σ τ]
  by_cases hvω : v ∈ ω
  · have herase : (ω ∪ τ).erase v = ω.erase v ∪ τ := by
      rw [erase_union_distrib, erase_eq_of_notMem hvτ]
    simp only [mem_link_nonempty, mem_stellarSubdivision_iff, mem_union, hvτ, hvω,
      true_or, false_or, not_true_eq_false, false_and, true_and, herase, hsub, hunion]
    constructor
    · rintro ⟨-, hdis, havoid, hface⟩
      have hne : (σ \ τ).Nonempty := Finset.nonempty_of_ne_empty fun h =>
        havoid (h ▸ empty_subset _)
      refine ⟨havoid, hne.mono subset_union_right, ?_, hface⟩
      exact disjoint_union_left.mpr
        ⟨hdis.mono_left (erase_subset v ω), sdiff_disjoint⟩
    · rintro ⟨havoid, -, hdis, hface⟩
      refine ⟨⟨v, hvω⟩, ?_, havoid, hface⟩
      have hdis' := (disjoint_union_left.mp hdis).1
      rw [← insert_erase hvω, disjoint_insert_left]
      exact ⟨hvτ, hdis'⟩
  · have hvunion : v ∉ ω ∪ τ := by simp [hvω, hvτ]
    simp only [mem_link_nonempty, mem_stellarSubdivision_iff_of_notMem hvunion,
      mem_stellarSubdivision_iff_of_notMem hvω, hsub]
    tauto

/-- If the starring vertex is unused in the old link and the starred set has a vertex outside
`τ`, its links before and after starring are stellar equivalent. This applies to every set
avoiding the starring vertex, not only to surviving faces. -/
theorem stellarEquivalent_link_stellarSubdivision_of_notMem
    (hv : ({v} : Finset ι) ∉ link K τ) (hvτ : v ∉ τ)
    (hne : (σ \ τ).Nonempty) :
    StellarEquivalent (link K τ) (link (stellarSubdivision K σ v) τ) := by
  rw [link_stellarSubdivision_of_notMem hvτ]
  by_cases hrem : σ \ τ ∈ link K τ
  · exact stellarEquivalent_stellarSubdivision hrem hv
  · rw [stellarSubdivision_eq_self_of_notMem hv hne hrem]

/-- A surviving old vertex of a zero-dimensional combinatorial manifold still has void link
after stellar subdivision. -/
theorem IsCombinatorialManifold.link_stellarSubdivision_eq_bot
    (hK : IsCombinatorialManifold K 0) (hwv : w ≠ v)
    (hw : ({w} : Finset ι) ∈ stellarSubdivision K σ v) :
    link (stellarSubdivision K σ v) {w} = ⊥ := by
  have hvw : v ∉ ({w} : Finset ι) := by simpa [eq_comm] using hwv
  obtain ⟨hwK, havoid⟩ := (mem_stellarSubdivision_iff_of_notMem hvw).mp hw
  have hlink := isCombinatorialManifold_zero_iff.mp hK hwK
  have hvlink : ({v} : Finset ι) ∉ link K {w} := by
    rw [hlink]
    exact Set.notMem_empty _
  have he := stellarEquivalent_link_stellarSubdivision_of_notMem
    hvlink hvw (sdiff_nonempty.mpr havoid)
  apply dimension_eq_bot_iff.mp
  rw [he.dimension_eq, hlink, dimension_bot]

/-- Every surviving old vertex of a positive-dimensional combinatorial manifold retains its
sphere-or-ball link condition under stellar subdivision when the starring vertex is unused in
its old link. The condition at the new vertex is separate: its link is the boundary of the
starred closed star. -/
theorem IsCombinatorialManifold.isCombinatorialSphere_or_isCombinatorialBall_link_stellarSubdivision
    (hK : IsCombinatorialManifold K (n + 1)) (hvlink : ({v} : Finset ι) ∉ link K {w})
    (hwv : w ≠ v)
    (hw : ({w} : Finset ι) ∈ stellarSubdivision K σ v) :
    IsCombinatorialSphere (link (stellarSubdivision K σ v) {w}) n ∨
      IsCombinatorialBall (link (stellarSubdivision K σ v) {w}) n := by
  have hvw : v ∉ ({w} : Finset ι) := by simpa [eq_comm] using hwv
  obtain ⟨hwK, havoid⟩ := (mem_stellarSubdivision_iff_of_notMem hvw).mp hw
  have he := (stellarEquivalent_link_stellarSubdivision_of_notMem
    hvlink hvw (sdiff_nonempty.mpr havoid)).symm.stellarEquivalentUpToRelabeling
  exact (isCombinatorialManifold_succ_iff.mp hK hwK).imp
    (IsCombinatorialSphere.of_stellarEquivalentUpToRelabeling he)
    (IsCombinatorialBall.of_stellarEquivalentUpToRelabeling he)

end PreAbstractSimplicialComplex
