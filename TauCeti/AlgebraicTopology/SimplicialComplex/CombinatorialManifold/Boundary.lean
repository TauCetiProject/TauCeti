/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Link
import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Homotopy
import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Pure
import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.ZeroDimensional
import TauCeti.AlgebraicTopology.SimplicialComplex.Join.Combinatorial
import TauCeti.AlgebraicTopology.SimplicialComplex.Join.Star
import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Link

/-!
# The boundary of a combinatorial manifold

In a combinatorial `(n + 1)`-manifold `K`, every vertex link is either a combinatorial `n`-sphere
(an interior vertex) or a combinatorial `n`-ball (a boundary vertex), and the two cases are
mutually exclusive (`IsCombinatorialSphere.not_isCombinatorialBall`). More generally, the link of
every non-maximal face `σ ∈ K` is a combinatorial `(n + 1 - σ.card)`-sphere or ball
(`IsCombinatorialManifold.isCombinatorialSphere_or_isCombinatorialBall_link`), and spherical links
propagate upward along face inclusions (`isCombinatorialSphere_link_of_subset`). Consequently the
faces of `K` with ball links form a downward-closed subcomplex — the **combinatorial boundary**
`K.combinatorialBoundary` — whose vertices are precisely the vertices of `K` with ball links.

To avoid bundling a manifold proof into the subcomplex type, `K.combinatorialBoundary` is defined
totally on any `PreAbstractSimplicialComplex` as the faces `σ ∈ K` all of whose nonempty subsets
have combinatorial ball links in `K`. On a combinatorial manifold, upward propagation of spherical
links collapses this universal quantifier to the single link condition at `σ` itself
(`IsCombinatorialManifold.mem_combinatorialBoundary_iff`).

Starring a face `σ ∈ K` of a combinatorial manifold leaves `K.combinatorialBoundary` unchanged when
`σ ∉ K.combinatorialBoundary`, and stars `K.combinatorialBoundary` at `σ` when
`σ ∈ K.combinatorialBoundary`. Thus intrinsic stellar equivalence on combinatorial manifolds induces
intrinsic stellar equivalence of their boundaries. Applied to the standard models
`(simplex V).combinatorialBoundary = simplexBoundary V` and
`(simplexBoundary V).combinatorialBoundary = ⊥`, this shows that the boundary of a combinatorial
`(n + 1)`-ball is a combinatorial `n`-sphere and the boundary of a combinatorial `n`-sphere is void.
Finally, for any boundary face `σ ∈ K.combinatorialBoundary` of a combinatorial manifold `K`,
`link K.combinatorialBoundary σ = (link K σ).combinatorialBoundary`; specializing to vertices proves
that the boundary of a combinatorial `(n + 1)`-manifold is a closed combinatorial `n`-manifold
(`IsCombinatorialManifold K.combinatorialBoundary n` and
`K.combinatorialBoundary.combinatorialBoundary = ⊥`).

## Main definitions

* `PreAbstractSimplicialComplex.combinatorialBoundary`: the subcomplex of faces `σ ∈ K` whose
  nonempty subsets all have combinatorial ball links in `K`.

## Main results

* `PreAbstractSimplicialComplex.IsCombinatorialManifold.mem_combinatorialBoundary_iff`: on a
  combinatorial `n`-manifold, `σ ∈ K.combinatorialBoundary` iff `σ ∈ K`, `σ.card ≤ n`, and
  `IsCombinatorialBall (link K σ) (n - σ.card)`.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold.singleton_mem_combinatorialBoundary_iff`:
  the vertices of `K.combinatorialBoundary` in a combinatorial `(n + 1)`-manifold are precisely the
  vertices of `K` whose links are combinatorial `n`-balls.
* `PreAbstractSimplicialComplex.combinatorialBoundary_simplex` and
  `PreAbstractSimplicialComplex.combinatorialBoundary_simplexBoundary`: the combinatorial boundaries
  of `simplex V` and `simplexBoundary V` are `simplexBoundary V` and `⊥`.
* `IsCombinatorialManifold.combinatorialBoundary_stellarSubdivision_of_notMem` and
  `IsCombinatorialManifold.combinatorialBoundary_stellarSubdivision_of_mem`: effect of a stellar
  subdivision on `combinatorialBoundary`.
* `IsCombinatorialManifold.stellarEquivalentUpToRelabeling_combinatorialBoundary`:
  intrinsic stellar equivalence of combinatorial manifolds induces intrinsic stellar equivalence of
  their boundaries.
* `PreAbstractSimplicialComplex.IsCombinatorialSphere.combinatorialBoundary_eq_bot`: every
  combinatorial `n`-sphere has void boundary.
* `PreAbstractSimplicialComplex.IsCombinatorialBall.isCombinatorialSphere_combinatorialBoundary`:
  the boundary of a combinatorial `(n + 1)`-ball is a combinatorial `n`-sphere.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold.link_combinatorialBoundary`: for
  `σ ∈ K.combinatorialBoundary`,
  `link K.combinatorialBoundary σ = (link K σ).combinatorialBoundary`.
* `IsCombinatorialManifold.isCombinatorialManifold_combinatorialBoundary`:
  the boundary of a combinatorial `(n + 1)`-manifold is a combinatorial `n`-manifold.
* `IsCombinatorialManifold.combinatorialBoundary_combinatorialBoundary`:
  the boundary of a combinatorial manifold has void boundary (`∂(∂K) = ⊥`).

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2 and 3.
* W. B. R. Lickorish, *Simplicial moves on complexes and manifolds*, Geom. Topol. Monogr. 2
  (1999), 299–320, §3.
-/

public section

open Finset TauCeti

namespace PreAbstractSimplicialComplex

section Basic

variable {ι : Type*} [DecidableEq ι] {K L : PreAbstractSimplicialComplex ι}
  {V σ τ : Finset ι} {v : ι} {n m : ℕ}

/-- The **combinatorial boundary** of a precomplex `K` consists of the faces `σ ∈ K` all of whose
nonempty subsets have combinatorial ball links in `K`.

On a combinatorial `n`-manifold (`IsCombinatorialManifold.mem_combinatorialBoundary_iff`), upward
propagation of spherical links makes the subset quantifier redundant: `σ` lies in
`K.combinatorialBoundary` if and only if `σ ∈ K`, `σ.card ≤ n`, and `link K σ` is a combinatorial
`(n - σ.card)`-ball. Quantifying over nonempty subsets ensures downward closure on arbitrary
precomplexes without bundling a manifold hypothesis. -/
def combinatorialBoundary (K : PreAbstractSimplicialComplex ι) :
    PreAbstractSimplicialComplex ι where
  faces := {σ | σ ∈ K ∧ ∀ ⦃τ⦄, τ.Nonempty → τ ⊆ σ → ∃ m, IsCombinatorialBall (link K τ) m}
  isRelLowerSet_faces := fun {_} hσ =>
    ⟨(K.isRelLowerSet_faces hσ.1).1,
      fun {_} hρσ hρne => ⟨(K.isRelLowerSet_faces hσ.1).2 hρσ hρne,
        fun _ hτne hτρ => hσ.2 hτne (hτρ.trans hρσ)⟩⟩

/-- Membership in `K.combinatorialBoundary`. -/
theorem mem_combinatorialBoundary :
    σ ∈ K.combinatorialBoundary ↔
      σ ∈ K ∧ ∀ ⦃τ⦄, τ.Nonempty → τ ⊆ σ → ∃ m, IsCombinatorialBall (link K τ) m :=
  (Iff.rfl)

/-- The combinatorial boundary is a subcomplex of `K`. -/
theorem combinatorialBoundary_le : K.combinatorialBoundary ≤ K :=
  fun _ h => (mem_combinatorialBoundary.mp h).1

/-- The void complex has void combinatorial boundary. -/
@[simp]
theorem combinatorialBoundary_bot :
    (⊥ : PreAbstractSimplicialComplex ι).combinatorialBoundary = ⊥ :=
  bot_unique combinatorialBoundary_le

/-- A vertex `{v}` belongs to `K.combinatorialBoundary` if and only if `{v} ∈ K` and `link K {v}`
is a combinatorial ball of some dimension. -/
@[simp]
theorem singleton_mem_combinatorialBoundary :
    ({v} : Finset ι) ∈ K.combinatorialBoundary ↔
      ({v} : Finset ι) ∈ K ∧ ∃ m, IsCombinatorialBall (link K {v}) m := by
  rw [mem_combinatorialBoundary]
  refine ⟨fun ⟨hv, h⟩ => ⟨hv, h (singleton_nonempty v) Subset.rfl⟩, fun ⟨hv, hm⟩ => ⟨hv, ?_⟩⟩
  intro τ hτne hτv
  obtain rfl := hτne.subset_singleton_iff.mp hτv
  exact hm

/-- Injective vertex relabeling commutes with `combinatorialBoundary`. -/
@[simp]
theorem map_combinatorialBoundary {κ : Type*} [DecidableEq κ] (f : ι → κ)
    (hf : Function.Injective f) :
    K.combinatorialBoundary.map f = (K.map f).combinatorialBoundary := by
  refine SetLike.ext fun ω => ?_
  rw [mem_map_iff, mem_combinatorialBoundary, mem_map_iff]
  constructor
  · rintro ⟨σ, hσB, rfl⟩
    obtain ⟨hσK, hball⟩ := mem_combinatorialBoundary.mp hσB
    refine ⟨⟨σ, hσK, rfl⟩, fun τ' hτ'ne hτ'sub => ?_⟩
    let τ : Finset ι := {x ∈ σ | f x ∈ τ'}
    have hτimg : τ.image f = τ' := by
      ext y
      simp only [τ, mem_image, mem_filter]
      constructor
      · rintro ⟨x, ⟨_, hx⟩, rfl⟩
        exact hx
      · intro hy
        obtain ⟨x, hxσ, rfl⟩ := mem_image.mp (hτ'sub hy)
        exact ⟨x, ⟨hxσ, hy⟩, rfl⟩
    have hτne : τ.Nonempty := image_nonempty.mp (hτimg.symm ▸ hτ'ne)
    obtain ⟨m, hm⟩ := hball hτne (filter_subset _ σ)
    refine ⟨m, ?_⟩
    rw [← hτimg, ← map_link f hf]
    exact hm.map f hf
  · rintro ⟨⟨σ, hσK, rfl⟩, hball⟩
    refine ⟨σ, mem_combinatorialBoundary.mpr ⟨hσK, fun τ hτne hτσ => ?_⟩, rfl⟩
    obtain ⟨m, hm⟩ := hball (hτne.image f) (image_mono f hτσ)
    rw [← map_link f hf, isCombinatorialBall_map_iff f hf] at hm
    exact ⟨m, hm⟩

end Basic

section ManifoldCharacterization

variable {ι : Type*} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι}
  {V σ : Finset ι} {v : ι} {n m : ℕ}

/-- Every `0`-dimensional combinatorial manifold has void boundary, as all its vertex links are
void. -/
@[simp]
theorem IsCombinatorialManifold.combinatorialBoundary_zero (hK : IsCombinatorialManifold K 0) :
    K.combinatorialBoundary = ⊥ := by
  refine eq_bot_iff.mpr fun σ hσ => ?_
  obtain ⟨hσK, hsub⟩ := mem_combinatorialBoundary.mp hσ
  obtain ⟨v, hv⟩ := (K.isRelLowerSet_faces hσK).1
  obtain ⟨m, hm⟩ := hsub (singleton_nonempty v) (singleton_subset_iff.mpr hv)
  exact hm.ne_bot (isCombinatorialManifold_zero_iff.mp hK (singleton_mem_of_mem hσK hv))

private theorem card_le_and_dim_eq_of_ball_link (hK : IsCombinatorialManifold K n)
    (hσ : σ ∈ K) (hb : IsCombinatorialBall (link K σ) m) :
    σ.card ≤ n ∧ m = n - σ.card := by
  have hle_succ : σ.card ≤ n + 1 := hK.isPure.card_le hσ
  have hne_top : σ.card ≠ n + 1 := fun htop =>
    hb.ne_bot ((hK.link_eq_bot_iff hσ).mpr htop)
  have hcard : σ.card ≤ n := by omega
  have hdim := hb.dimension_eq.symm.trans (hK.dimension_link hσ hcard)
  exact ⟨hcard, by exact_mod_cast hdim⟩

/-- On a combinatorial `n`-manifold, a face `σ` belongs to `K.combinatorialBoundary` if and only if
`σ ∈ K`, `σ.card ≤ n`, and `link K σ` is a combinatorial `(n - σ.card)`-ball. -/
theorem IsCombinatorialManifold.mem_combinatorialBoundary_iff (hK : IsCombinatorialManifold K n) :
    σ ∈ K.combinatorialBoundary ↔
      σ ∈ K ∧ σ.card ≤ n ∧ IsCombinatorialBall (link K σ) (n - σ.card) := by
  rw [mem_combinatorialBoundary]
  constructor
  · rintro ⟨hσ, hsub⟩
    obtain ⟨m, hm⟩ := hsub (K.isRelLowerSet_faces hσ).1 Subset.rfl
    obtain ⟨hcard, rfl⟩ := card_le_and_dim_eq_of_ball_link hK hσ hm
    exact ⟨hσ, hcard, hm⟩
  · rintro ⟨hσ, hcard, hb⟩
    refine ⟨hσ, fun τ hτne hτσ => ?_⟩
    have hτK : τ ∈ K := (K.isRelLowerSet_faces hσ).2 hτσ hτne
    have hτcard : τ.card ≤ n := (card_le_card hτσ).trans hcard
    rcases hK.isCombinatorialSphere_or_isCombinatorialBall_link hτK hτcard with hs | hbτ
    · exact ((isCombinatorialSphere_link_of_subset hτσ hσ hcard hs).not_isCombinatorialBall
        hb).elim
    · exact ⟨n - τ.card, hbτ⟩

/-- On a combinatorial `n`-manifold, `σ ∈ K.combinatorialBoundary` if and only if `σ ∈ K` and
`link K σ` is a combinatorial ball of some dimension. -/
theorem IsCombinatorialManifold.mem_combinatorialBoundary_iff_exists
    (hK : IsCombinatorialManifold K n) :
    σ ∈ K.combinatorialBoundary ↔ σ ∈ K ∧ ∃ m, IsCombinatorialBall (link K σ) m := by
  rw [hK.mem_combinatorialBoundary_iff]
  refine ⟨fun ⟨hσ, _, hb⟩ => ⟨hσ, n - σ.card, hb⟩, fun ⟨hσ, m, hb⟩ => ?_⟩
  obtain ⟨hcard, rfl⟩ := card_le_and_dim_eq_of_ball_link hK hσ hb
  exact ⟨hσ, hcard, hb⟩

/-- In a combinatorial `(n + 1)`-manifold, `{v}` is a boundary vertex if and only if `{v} ∈ K` and
`link K {v}` is a combinatorial `n`-ball. -/
theorem IsCombinatorialManifold.singleton_mem_combinatorialBoundary_iff
    (hK : IsCombinatorialManifold K (n + 1)) :
    ({v} : Finset ι) ∈ K.combinatorialBoundary ↔
      ({v} : Finset ι) ∈ K ∧ IsCombinatorialBall (link K {v}) n := by
  rw [hK.mem_combinatorialBoundary_iff, card_singleton, Nat.add_sub_cancel]
  exact ⟨fun ⟨hv, _, hb⟩ => ⟨hv, hb⟩, fun ⟨hv, hb⟩ => ⟨hv, Nat.le_add_left 1 n, hb⟩⟩

/-- A codimension-1 face (`σ.card = n + 1`) of a combinatorial `(n + 1)`-manifold lies in
`K.combinatorialBoundary` if and only if it is a face of a unique top-dimensional simplex of `K`,
that is, `(link K σ).faces.encard = 1`. -/
theorem IsCombinatorialManifold.mem_combinatorialBoundary_iff_encard_link_eq_one
    (hK : IsCombinatorialManifold K (n + 1)) (hσ : σ ∈ K) (hcard : σ.card = n + 1) :
    σ ∈ K.combinatorialBoundary ↔ (link K σ).faces.encard = 1 := by
  rw [hK.mem_combinatorialBoundary_iff, hcard, Nat.sub_self, isCombinatorialBall_zero_iff]
  have hdim : dimension (link K σ) ≤ 0 := by
    rw [hK.dimension_link hσ (le_of_eq hcard), hcard, Nat.sub_self]
    rfl
  constructor
  · rintro ⟨-, -, w, hw⟩
    rw [hw, faces_simplex_singleton, Set.encard_singleton]
  · intro henc
    obtain ⟨ρ, hfaces⟩ := Set.encard_eq_one.mp henc
    have hρ : ρ ∈ (link K σ).faces := hfaces.symm ▸ Set.mem_singleton ρ
    obtain ⟨w, rfl⟩ := dimension_le_zero_iff.mp hdim ρ hρ
    refine ⟨hσ, le_rfl, w, PreAbstractSimplicialComplex.ext ?_⟩
    rw [faces_simplex_singleton]
    exact hfaces

/-- A codimension-1 face (`σ.card = n + 1`) of a combinatorial `(n + 1)`-manifold is an interior
face (`σ ∉ K.combinatorialBoundary`) if and only if it is a face of two top-dimensional simplices
of `K`, that is, `(link K σ).faces.encard = 2`. -/
theorem IsCombinatorialManifold.notMem_combinatorialBoundary_iff_encard_link_eq_two
    (hK : IsCombinatorialManifold K (n + 1)) (hσ : σ ∈ K) (hcard : σ.card = n + 1) :
    σ ∉ K.combinatorialBoundary ↔ (link K σ).faces.encard = 2 := by
  have hlink := hK.isCombinatorialSphere_or_isCombinatorialBall_link hσ (le_of_eq hcard)
  rw [hcard, Nat.sub_self, isCombinatorialSphere_zero_iff, isCombinatorialBall_zero_iff] at hlink
  rw [hK.mem_combinatorialBoundary_iff_encard_link_eq_one hσ hcard]
  rcases hlink with ⟨a, b, hab, heq⟩ | ⟨w, hw⟩
  · rw [heq, faces_simplexBoundary_pair hab, Set.encard_pair (by simpa using hab)]
    decide
  · rw [hw, faces_simplex_singleton, Set.encard_singleton]
    decide

/-- The combinatorial boundary of any standard simplex `simplex V` is `simplexBoundary V`
(including when `V` is empty or a singleton). -/
@[simp]
theorem combinatorialBoundary_simplex (V : Finset ι) :
    (simplex V).combinatorialBoundary = simplexBoundary V := by
  by_cases hVne : V.Nonempty
  · have hpos : 1 ≤ V.card := card_pos.mpr hVne
    cases hcard : V.card with
    | zero => omega
    | succ k =>
      have hM : IsCombinatorialManifold (simplex V) k :=
        isCombinatorialManifold_simplex (by omega)
      cases k with
      | zero =>
        obtain ⟨v, rfl⟩ := card_eq_one.mp hcard
        rw [hM.combinatorialBoundary_zero, simplexBoundary_singleton]
      | succ m =>
        refine SetLike.ext fun σ => ?_
        rw [hM.mem_combinatorialBoundary_iff, mem_simplexBoundary, mem_simplex]
        constructor
        · rintro ⟨⟨hne, hsub⟩, hle, -⟩
          refine ⟨hne, Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩⟩
          rintro rfl
          omega
        · rintro ⟨hne, hssub⟩
          have hlt : σ.card < m + 2 := hcard ▸ card_lt_card hssub
          have hle : σ.card ≤ m + 1 := by omega
          exact ⟨⟨hne, hssub.subset⟩, hle, isCombinatorialBall_link_simplex hcard hssub.subset hle⟩
  · rw [not_nonempty_iff_eq_empty.mp hVne, simplex_empty, simplexBoundary_empty,
      combinatorialBoundary_bot]

/-- The combinatorial boundary of any standard simplex boundary `simplexBoundary V` is void. -/
@[simp]
theorem combinatorialBoundary_simplexBoundary (V : Finset ι) :
    (simplexBoundary V).combinatorialBoundary = ⊥ := by
  by_cases h2 : 2 ≤ V.card
  · have hM : IsCombinatorialManifold (simplexBoundary V) (V.card - 2) :=
      isCombinatorialManifold_simplexBoundary (by omega)
    refine eq_bot_iff.mpr fun σ hσ => ?_
    obtain ⟨hσB, hle, hb⟩ := hM.mem_combinatorialBoundary_iff.mp hσ
    have hs := isCombinatorialSphere_link_simplexBoundary (n := V.card - 2) (by omega)
      (mem_simplexBoundary.mp hσB).2.subset hle
    exact hs.not_isCombinatorialBall hb
  · have h01 : V.card = 0 ∨ V.card = 1 := by omega
    rcases h01 with h0 | h1
    · rw [card_eq_zero.mp h0, simplexBoundary_empty, combinatorialBoundary_bot]
    · obtain ⟨v, rfl⟩ := card_eq_one.mp h1
      rw [simplexBoundary_singleton, combinatorialBoundary_bot]

/-- For a boundary face `σ ∈ K.combinatorialBoundary` of a combinatorial `n`-manifold `K`, its link
inside `K.combinatorialBoundary` equals the combinatorial boundary of `link K σ`. -/
theorem IsCombinatorialManifold.link_combinatorialBoundary (hK : IsCombinatorialManifold K n)
    (hσ : σ ∈ K.combinatorialBoundary) :
    link K.combinatorialBoundary σ = (link K σ).combinatorialBoundary := by
  obtain ⟨_, hσcard, hb⟩ := hK.mem_combinatorialBoundary_iff.mp hσ
  have hlinkM : IsCombinatorialManifold (link K σ) (n - σ.card) := hb.isCombinatorialManifold
  refine SetLike.ext fun ρ => ?_
  rw [mem_link_nonempty, hK.mem_combinatorialBoundary_iff,
    hlinkM.mem_combinatorialBoundary_iff, mem_link_nonempty]
  constructor
  · rintro ⟨hne, hdis, hρσK, hcard, hball⟩
    have hcard_union : (ρ ∪ σ).card = ρ.card + σ.card := card_union_of_disjoint hdis
    have hlink_eq : link (link K σ) ρ = link K (ρ ∪ σ) := by
      rw [link_link hdis.symm, union_comm]
    have hdim_eq : n - σ.card - ρ.card = n - (ρ ∪ σ).card := by omega
    exact ⟨⟨hne, hdis, hρσK⟩, by omega, by rwa [hlink_eq, hdim_eq]⟩
  · rintro ⟨⟨hne, hdis, hρσK⟩, hcard, hball⟩
    have hcard_union : (ρ ∪ σ).card = ρ.card + σ.card := card_union_of_disjoint hdis
    have hlink_eq : link (link K σ) ρ = link K (ρ ∪ σ) := by
      rw [link_link hdis.symm, union_comm]
    have hdim_eq : n - σ.card - ρ.card = n - (ρ ∪ σ).card := by omega
    exact ⟨hne, hdis, hρσK, by omega, by rwa [← hlink_eq, ← hdim_eq]⟩

end ManifoldCharacterization

section StellarInvariance

variable {ι : Type*} [DecidableEq ι] {K L : PreAbstractSimplicialComplex ι}
  {σ : Finset ι} {v : ι} {n : ℕ}

private theorem insert_mem_combinatorialBoundary_stellarSubdivision_iff {m : ℕ} {ω : Finset ι}
    (hK : IsCombinatorialManifold K (m + 1)) (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K)
    (hvω : v ∉ ω) :
    insert v ω ∈ (stellarSubdivision K σ v).combinatorialBoundary ↔
      ¬ σ ⊆ ω ∧ ω ∪ σ ∈ K.combinatorialBoundary := by
  have hsubM := hK.stellarSubdivision hσ hv
  rw [hsubM.mem_combinatorialBoundary_iff_exists, insert_mem_stellarSubdivision_iff hvω,
    and_assoc, hK.mem_combinatorialBoundary_iff]
  refine and_congr_right fun hnot => and_congr_right fun hface => ?_
  have hjoin (k : ℕ) : IsCombinatorialBall (link (stellarSubdivision K σ v) (insert v ω)) k ↔
      IsCombinatorialBall (join (simplexBoundary (σ \ ω)) (link K (ω ∪ σ))) k := by
    rw [link_stellarSubdivision_insert hv hvω,
      ← isCombinatorialBall_map_iff _ (partitionEmbedding (· ∈ σ)).injective,
      map_link_closedStar_inf_deletion_eq_join hσ hnot hface]
  simp only [hjoin]
  have hsdiff_pos : 1 ≤ (σ \ ω).card := card_pos.mpr (sdiff_nonempty.mpr hnot)
  constructor
  · rintro ⟨k, hball⟩
    have hle_top : (ω ∪ σ).card ≤ m + 2 := hK.isPure.card_le hface
    by_cases htop : (ω ∪ σ).card = m + 2
    · rw [(hK.link_eq_bot_iff hface).mpr htop, join_bot,
        isCombinatorialBall_map_iff _ Sum.inl_injective] at hball
      by_cases h1 : (σ \ ω).card = 1
      · obtain ⟨x, hx⟩ := card_eq_one.mp h1
        rw [hx, simplexBoundary_singleton] at hball
        exact (hball.ne_bot rfl).elim
      · exact ((isCombinatorialSphere_simplexBoundary (V := σ \ ω)
          (n := (σ \ ω).card - 2) (by omega)).not_isCombinatorialBall hball).elim
    · have hle : (ω ∪ σ).card ≤ m + 1 := by omega
      rcases hK.isCombinatorialSphere_or_isCombinatorialBall_link hface hle with hs | hb
      · by_cases h1 : (σ \ ω).card = 1
        · obtain ⟨x, hx⟩ := card_eq_one.mp h1
          rw [hx, simplexBoundary_singleton, bot_join,
            isCombinatorialBall_map_iff _ Sum.inr_injective] at hball
          exact (hs.not_isCombinatorialBall hball).elim
        · have hbdry := isCombinatorialSphere_simplexBoundary (V := σ \ ω)
            (n := (σ \ ω).card - 2) (by omega)
          exact ((hbdry.join hs).not_isCombinatorialBall hball).elim
      · exact ⟨hle, hb⟩
  · rintro ⟨_, hb⟩
    by_cases h1 : (σ \ ω).card = 1
    · obtain ⟨x, hx⟩ := card_eq_one.mp h1
      refine ⟨m + 1 - (ω ∪ σ).card, ?_⟩
      rw [hx, simplexBoundary_singleton, bot_join]
      exact hb.map _ Sum.inr_injective
    · have hbdry := isCombinatorialSphere_simplexBoundary (V := σ \ ω)
        (n := (σ \ ω).card - 2) (by omega)
      exact ⟨_, hbdry.join_ball hb⟩

private theorem notMem_mem_combinatorialBoundary_stellarSubdivision_iff {m : ℕ} {τ : Finset ι}
    (hK : IsCombinatorialManifold K (m + 1)) (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K)
    (hvτ : v ∉ τ) :
    τ ∈ (stellarSubdivision K σ v).combinatorialBoundary ↔
      τ ∈ K.combinatorialBoundary ∧ ¬ σ ⊆ τ := by
  have hsubM := hK.stellarSubdivision hσ hv
  rw [hsubM.mem_combinatorialBoundary_iff_exists, mem_stellarSubdivision_iff_of_notMem hvτ,
    hK.mem_combinatorialBoundary_iff_exists]
  constructor
  · rintro ⟨⟨hτK, hnot⟩, k, hb⟩
    have he := (stellarEquivalent_link_stellarSubdivision_of_notMem
      (fun h => hv (link_le h)) hvτ (sdiff_nonempty.mpr hnot)).stellarEquivalentUpToRelabeling
    exact ⟨⟨hτK, k, IsCombinatorialBall.of_stellarEquivalentUpToRelabeling he hb⟩, hnot⟩
  · rintro ⟨⟨hτK, k, hb⟩, hnot⟩
    have he := (stellarEquivalent_link_stellarSubdivision_of_notMem
      (fun h => hv (link_le h)) hvτ (sdiff_nonempty.mpr hnot)).symm.stellarEquivalentUpToRelabeling
    exact ⟨⟨hτK, hnot⟩, k, IsCombinatorialBall.of_stellarEquivalentUpToRelabeling he hb⟩

/-- Starring an interior face (`σ ∉ K.combinatorialBoundary`) of a combinatorial `n`-manifold at a
fresh vertex `{v} ∉ K` leaves the combinatorial boundary unchanged. -/
theorem IsCombinatorialManifold.combinatorialBoundary_stellarSubdivision_of_notMem
    (hK : IsCombinatorialManifold K n) (hσ : σ ∈ K) (hσnot : σ ∉ K.combinatorialBoundary)
    (hv : ({v} : Finset ι) ∉ K) :
    (K.stellarSubdivision σ v).combinatorialBoundary = K.combinatorialBoundary := by
  cases n with
  | zero =>
    rw [(hK.stellarSubdivision hσ hv).combinatorialBoundary_zero, hK.combinatorialBoundary_zero]
  | succ m =>
    have hσne : σ.Nonempty := (K.isRelLowerSet_faces hσ).1
    refine SetLike.ext fun τ => ?_
    by_cases hvτ : v ∈ τ
    · have hτeq : insert v (τ.erase v) = τ := insert_erase hvτ
      rw [← hτeq, insert_mem_combinatorialBoundary_stellarSubdivision_iff hK hσ hv
        (notMem_erase v τ)]
      refine ⟨fun ⟨_, hmem⟩ => ?_, fun hmem => ?_⟩
      · exact (hσnot ((K.combinatorialBoundary.isRelLowerSet_faces hmem).2
          subset_union_right hσne)).elim
      · exact (notMem_of_singleton_notMem hv (combinatorialBoundary_le hmem)
          (mem_insert_self v _)).elim
    · rw [notMem_mem_combinatorialBoundary_stellarSubdivision_iff hK hσ hv hvτ]
      exact ⟨And.left, fun hmem => ⟨hmem, fun hsub =>
        hσnot ((K.combinatorialBoundary.isRelLowerSet_faces hmem).2 hsub hσne)⟩⟩

/-- Starring a boundary face (`σ ∈ K.combinatorialBoundary`) of a combinatorial `n`-manifold at a
fresh vertex `{v} ∉ K` stars the combinatorial boundary at `σ`. -/
theorem IsCombinatorialManifold.combinatorialBoundary_stellarSubdivision_of_mem
    (hK : IsCombinatorialManifold K n) (hσ : σ ∈ K.combinatorialBoundary)
    (hv : ({v} : Finset ι) ∉ K) :
    (K.stellarSubdivision σ v).combinatorialBoundary =
      K.combinatorialBoundary.stellarSubdivision σ v := by
  cases n with
  | zero =>
    rw [hK.combinatorialBoundary_zero] at hσ
    exact hσ.elim
  | succ m =>
    have hσK : σ ∈ K := combinatorialBoundary_le hσ
    refine SetLike.ext fun τ => ?_
    by_cases hvτ : v ∈ τ
    · have hτeq : insert v (τ.erase v) = τ := insert_erase hvτ
      rw [← hτeq, insert_mem_combinatorialBoundary_stellarSubdivision_iff hK hσK hv
        (notMem_erase v τ), insert_mem_stellarSubdivision_iff (notMem_erase v τ)]
    · rw [notMem_mem_combinatorialBoundary_stellarSubdivision_iff hK hσK hv hvτ,
        mem_stellarSubdivision_iff_of_notMem hvτ]

/-- Same-type stellar equivalence between combinatorial `n`-manifolds induces a same-type stellar
equivalence between their combinatorial boundaries. -/
theorem IsCombinatorialManifold.stellarEquivalent_combinatorialBoundary
    (hK : IsCombinatorialManifold K n) (he : StellarEquivalent K L) :
    StellarEquivalent K.combinatorialBoundary L.combinatorialBoundary := by
  suffices hboth : (IsCombinatorialManifold K n ↔ IsCombinatorialManifold L n) ∧
      (IsCombinatorialManifold K n →
        StellarEquivalent K.combinatorialBoundary L.combinatorialBoundary) from hboth.2 hK
  refine he.induction_on
    (P := fun A B => (IsCombinatorialManifold A n ↔ IsCombinatorialManifold B n) ∧
      (IsCombinatorialManifold A n →
        StellarEquivalent A.combinatorialBoundary B.combinatorialBoundary))
    ?_ (fun _ => ⟨Iff.rfl, fun _ => .refl _⟩)
    (fun _ _ ih => ⟨ih.1.symm, fun hB => (ih.2 (ih.1.mpr hB)).symm⟩)
    (fun _ _ _ ih₁ ih₂ => ⟨ih₁.1.trans ih₂.1,
      fun hA => (ih₁.2 hA).trans (ih₂.2 (ih₁.1.mp hA))⟩)
  intro A B hmove
  obtain ⟨σ, v, hσ, hv, rfl⟩ := isStellarMove_iff.mp hmove
  refine ⟨(isCombinatorialManifold_stellarSubdivision_iff hσ hv).symm, fun hA => ?_⟩
  by_cases hσB : σ ∈ A.combinatorialBoundary
  · rw [hA.combinatorialBoundary_stellarSubdivision_of_mem hσB hv]
    exact stellarEquivalent_stellarSubdivision hσB (fun h => hv (combinatorialBoundary_le h))
  · rw [hA.combinatorialBoundary_stellarSubdivision_of_notMem hσ hσB hv]

end StellarInvariance

section MainTheorems

variable {ι : Type*} [DecidableEq ι] {K L : PreAbstractSimplicialComplex ι}
  {v : ι} {n : ℕ}

/-- Intrinsic stellar equivalence between combinatorial `n`-manifolds induces an intrinsic stellar
equivalence between their combinatorial boundaries. -/
theorem IsCombinatorialManifold.stellarEquivalentUpToRelabeling_combinatorialBoundary
    (hK : IsCombinatorialManifold K n) (he : StellarEquivalentUpToRelabeling K L) :
    StellarEquivalentUpToRelabeling K.combinatorialBoundary L.combinatorialBoundary := by
  suffices hboth : (IsCombinatorialManifold K n ↔ IsCombinatorialManifold L n) ∧
      (IsCombinatorialManifold K n →
        StellarEquivalentUpToRelabeling K.combinatorialBoundary L.combinatorialBoundary) from
    hboth.2 hK
  refine he.induction_on
    (P := fun A B => (IsCombinatorialManifold A n ↔ IsCombinatorialManifold B n) ∧
      (IsCombinatorialManifold A n →
        StellarEquivalentUpToRelabeling A.combinatorialBoundary B.combinatorialBoundary))
    ?_ (fun _ => ⟨Iff.rfl, fun _ => .refl _⟩)
    (fun _ _ ih => ⟨ih.1.symm, fun hB => (ih.2 (ih.1.mpr hB)).symm⟩)
    (fun _ _ _ ih₁ ih₂ => ⟨ih₁.1.trans ih₂.1,
      fun hA => (ih₁.2 hA).trans (ih₂.2 (ih₁.1.mp hA))⟩)
  intro A B f g hfg
  have hiff : IsCombinatorialManifold A n ↔ IsCombinatorialManifold B n :=
    (isCombinatorialManifold_map_iff f f.injective).symm.trans
      (hfg.isCombinatorialManifold_iff.trans (isCombinatorialManifold_map_iff g g.injective))
  refine ⟨hiff, fun hA => ?_⟩
  apply StellarEquivalentUpToRelabeling.of_common_relabeling f g
  rw [map_combinatorialBoundary f f.injective, map_combinatorialBoundary g g.injective]
  exact (hA.map f f.injective).stellarEquivalent_combinatorialBoundary hfg

/-- Every combinatorial `n`-sphere has void combinatorial boundary. -/
theorem IsCombinatorialSphere.combinatorialBoundary_eq_bot (h : IsCombinatorialSphere K n) :
    K.combinatorialBoundary = ⊥ := by
  obtain ⟨V, _, he⟩ := isCombinatorialSphere_iff.mp h
  have heB := h.isCombinatorialManifold.stellarEquivalentUpToRelabeling_combinatorialBoundary he
  rw [combinatorialBoundary_simplexBoundary] at heB
  exact Classical.byContradiction fun hne => heB.ne_bot_iff.mp hne rfl

/-- Every combinatorial `0`-ball has void combinatorial boundary. -/
@[simp]
theorem IsCombinatorialBall.combinatorialBoundary_zero (h : IsCombinatorialBall K 0) :
    K.combinatorialBoundary = ⊥ :=
  h.isCombinatorialManifold.combinatorialBoundary_zero

/-- The combinatorial boundary of every combinatorial `(n + 1)`-ball is a combinatorial
`n`-sphere. -/
theorem IsCombinatorialBall.isCombinatorialSphere_combinatorialBoundary
    (h : IsCombinatorialBall K (n + 1)) :
    IsCombinatorialSphere K.combinatorialBoundary n := by
  obtain ⟨V, hV, he⟩ := isCombinatorialBall_iff.mp h
  have heB := h.isCombinatorialManifold.stellarEquivalentUpToRelabeling_combinatorialBoundary he
  rw [combinatorialBoundary_simplex] at heB
  exact isCombinatorialSphere_iff.mpr ⟨V, hV, heB⟩

/-- In a combinatorial `(n + 2)`-manifold `K`, the link inside `K.combinatorialBoundary` of every
boundary vertex `{v} ∈ K.combinatorialBoundary` is a combinatorial `n`-sphere. -/
theorem IsCombinatorialManifold.isCombinatorialSphere_link_combinatorialBoundary
    (hK : IsCombinatorialManifold K (n + 2)) (hv : ({v} : Finset ι) ∈ K.combinatorialBoundary) :
    IsCombinatorialSphere (link K.combinatorialBoundary {v}) n := by
  obtain ⟨_, hb⟩ := hK.singleton_mem_combinatorialBoundary_iff.mp hv
  rw [hK.link_combinatorialBoundary hv]
  exact hb.isCombinatorialSphere_combinatorialBoundary

/-- The combinatorial boundary of every combinatorial `(n + 1)`-manifold is a combinatorial
`n`-manifold. -/
theorem IsCombinatorialManifold.isCombinatorialManifold_combinatorialBoundary
    (hK : IsCombinatorialManifold K (n + 1)) :
    IsCombinatorialManifold K.combinatorialBoundary n := by
  cases n with
  | zero =>
    refine isCombinatorialManifold_zero_iff.mpr fun v hv => ?_
    obtain ⟨_, hb⟩ := hK.singleton_mem_combinatorialBoundary_iff.mp hv
    rw [hK.link_combinatorialBoundary hv, hb.combinatorialBoundary_zero]
  | succ m =>
    exact isCombinatorialManifold_succ_iff.mpr fun _ hv =>
      Or.inl (hK.isCombinatorialSphere_link_combinatorialBoundary hv)

/-- A combinatorial `(n + 1)`-manifold has void combinatorial boundary (is closed) if and only if
every vertex link is a combinatorial `n`-sphere. -/
theorem IsCombinatorialManifold.combinatorialBoundary_eq_bot_iff
    (hK : IsCombinatorialManifold K (n + 1)) :
    K.combinatorialBoundary = ⊥ ↔
      ∀ ⦃v : ι⦄, ({v} : Finset ι) ∈ K → IsCombinatorialSphere (link K {v}) n := by
  constructor
  · intro hbot v hv
    rcases isCombinatorialManifold_succ_iff.mp hK hv with hs | hb
    · exact hs
    · have hmem : ({v} : Finset ι) ∈ K.combinatorialBoundary :=
        hK.singleton_mem_combinatorialBoundary_iff.mpr ⟨hv, hb⟩
      rw [hbot] at hmem
      exact hmem.elim
  · intro hs
    refine eq_bot_iff.mpr fun σ hσ => ?_
    obtain ⟨v, hv⟩ := (K.combinatorialBoundary.isRelLowerSet_faces hσ).1
    have hvB : ({v} : Finset ι) ∈ K.combinatorialBoundary := singleton_mem_of_mem hσ hv
    obtain ⟨hvK, hb⟩ := hK.singleton_mem_combinatorialBoundary_iff.mp hvB
    exact (hs hvK).not_isCombinatorialBall hb

/-- The combinatorial boundary of a combinatorial `n`-manifold has void combinatorial boundary
(`∂(∂K) = ⊥`). -/
theorem IsCombinatorialManifold.combinatorialBoundary_combinatorialBoundary
    (hK : IsCombinatorialManifold K n) :
    K.combinatorialBoundary.combinatorialBoundary = ⊥ := by
  cases n with
  | zero =>
    rw [hK.combinatorialBoundary_zero, combinatorialBoundary_bot]
  | succ m =>
    cases m with
    | zero =>
      exact hK.isCombinatorialManifold_combinatorialBoundary.combinatorialBoundary_zero
    | succ k =>
      exact hK.isCombinatorialManifold_combinatorialBoundary.combinatorialBoundary_eq_bot_iff.mpr
        fun _ hv => hK.isCombinatorialSphere_link_combinatorialBoundary hv

end MainTheorems

end PreAbstractSimplicialComplex
