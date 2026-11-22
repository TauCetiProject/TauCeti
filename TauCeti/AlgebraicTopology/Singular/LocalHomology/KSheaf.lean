/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.KSheaf
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Compact
public import TauCeti.Topology.Sets.Compacts

/-!
# The orientation K-sheaf of a manifold

For a space `M`, the local homology groups `Hₖ(M, M ∖ K)` along the compact subsets `K` of `M`,
with the restriction maps `Hₖ(M, M ∖ K) ⟶ Hₖ(M, M ∖ K')` for `K' ⊆ K`, form a K-presheaf on `M`
(`TauCeti.localHomologyKPresheaf`), in the sense of Mathlib's `TopCat.KPresheaf`. For a
topological manifold `M` of dimension `n`, Hausdorff and modelled on a real normed space of
dimension `n`, the K-presheaf `K ↦ Hₙ(M, M ∖ K)` is a K-sheaf
(`TauCeti.isKSheaf_localHomologyKPresheaf`). This is the orientation sheaf `o_M` of `M`: with
integer coefficients, its value `Hₙ(M, M ∖ {x}) ≅ ℤ` at a point is the group of local orientations
at `x`, and its sections along a compact set `K` are the families of local orientations at the
points of `K` that vary continuously. In Pardon's construction of virtual fundamental classes it is
the coefficient sheaf of the duality between local homology along closed sets and compactly
supported Čech cohomology.

The three K-sheaf axioms are proved as follows.

* **The empty set.** `Hₖ(M, M) = 0` (`TauCeti.isZero_localHomology_empty`).
* **Unions.** For compact `K₁` and `K₂`, the relative Mayer–Vietoris sequence of the open sets
  `M ∖ K₁` and `M ∖ K₂` makes the square of restrictions from `Hₖ(M, M ∖ (K₁ ∪ K₂))` to
  `Hₖ(M, M ∖ (K₁ ∩ K₂))` a pullback square as soon as `Hₖ₊₁(M, M ∖ (K₁ ∩ K₂)) = 0`
  (`TauCeti.isPullback_localHomologyKPresheaf_map`). On an `n`-manifold this holds for `k = n`,
  since the local homology of a compact set vanishes above the dimension
  (`TauCeti.isZero_localHomology_of_isCompact`).
* **Continuity.** On a locally compact Hausdorff space, `Hₖ(M, M ∖ K)` is the colimit of the groups
  `Hₖ(M, M ∖ L)` over the compact neighbourhoods `L` of `K`, for coefficients whose filtered
  colimits are exact (`TauCeti.localHomologyKPresheaf.isColimitCoconeOfCompacts`). A singular
  simplex of `M ∖ K` has compact image, which misses some compact neighbourhood of `K`; so the
  subspaces `M ∖ L` exhaust `M ∖ K` in the sense of compact supports
  (`TauCeti.isColimitComplPairCocone`).

The empty set and continuity axioms hold in every degree. The union axiom fails in general below
the dimension: if two closed arcs `K₁` and `K₂` cover the circle `S¹`, then `H₀(S¹, S¹ ∖ Kᵢ) = 0`
while `H₀(S¹, S¹ ∖ (K₁ ∪ K₂)) = H₀(S¹)` is not zero.

## Main definitions and results

* `TauCeti.localHomologyKPresheaf R M k`: the K-presheaf `K ↦ Hₖ(M, M ∖ K)` of `M`, with
  coefficients `R`.
* `TauCeti.isPullback_localHomologyKPresheaf_map`: the union axiom, when `Hₖ₊₁` vanishes along the
  intersection.
* `TauCeti.localHomologyKPresheaf.isColimitCoconeOfCompacts`: the continuity axiom.
* `TauCeti.isKSheaf_localHomologyKPresheaf_of_isZero`: on a locally compact Hausdorff space, the
  local homology K-presheaf in degree `k` is a K-sheaf when `Hₖ₊₁` vanishes along compact sets.
* `TauCeti.isKSheaf_localHomologyKPresheaf`: in the dimension of a manifold, the local homology
  K-presheaf is a K-sheaf.
* `TauCeti.orientationKSheaf`: the orientation K-sheaf of a manifold, as an object of
  `TopCat.KSheaf`.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Appendix A.1 (K-sheaves) and
  Definition A.6.2 (the orientation sheaf).
* A. Hatcher, *Algebraic Topology*, Section 3.3, Lemma 3.27.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Set Topology TopologicalSpace

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  (M : Type w) [TopologicalSpace M]

/-- The **local homology K-presheaf** `K ↦ Hₖ(M, M ∖ K)` of a space `M`, with coefficients `R`,
whose restriction maps are the maps `Hₖ(M, M ∖ K) ⟶ Hₖ(M, M ∖ K')` for `K' ⊆ K` induced by the
identity of `M` (`TauCeti.localHomologyRestriction`). -/
-- The body is exposed so that the values are definitionally the local homology groups: the
-- statement of `localHomologyKPresheaf_map`, a map between values, typechecks only then.
@[expose]
def localHomologyKPresheaf (k : ℕ) : TopCat.KPresheaf A (TopCat.of M) where
  obj K := localHomology R (K.unop : Set M) k
  map h := localHomologyRestriction R (leOfHom h.unop) k
  map_id _ := localHomologyRestriction_refl R _ k
  map_comp _ _ := (localHomologyRestriction_comp R _ _ k).symm

@[simp]
lemma localHomologyKPresheaf_obj (k : ℕ) (K : (Compacts (TopCat.of M))ᵒᵖ) :
    (localHomologyKPresheaf R M k).obj K = localHomology R (K.unop : Set M) k :=
  (rfl)

@[simp]
lemma localHomologyKPresheaf_map (k : ℕ) {K L : (Compacts (TopCat.of M))ᵒᵖ} (h : K ⟶ L) :
    (localHomologyKPresheaf R M k).map h = localHomologyRestriction R (leOfHom h.unop) k :=
  (rfl)

variable {M}

/-- **The union axiom for local homology.** Let `K₁ = K₂ ∩ K₃` and `K₄ = K₂ ∪ K₃` for compact
subsets of a Hausdorff space. If `Hₖ₊₁(M, M ∖ K₁)` vanishes, the square of restriction maps from
`Hₖ(M, M ∖ K₄)` through `Hₖ(M, M ∖ K₂)` and `Hₖ(M, M ∖ K₃)` to `Hₖ(M, M ∖ K₁)` is a pullback
square. -/
theorem isPullback_localHomologyKPresheaf_map [T2Space M] {k : ℕ}
    {K₁ K₂ K₃ K₄ : Compacts (TopCat.of M)} (sq : Lattice.BicartSq K₁ K₂ K₃ K₄)
    (h : IsZero (localHomology R (K₁ : Set M) (k + 1))) :
    IsPullback ((localHomologyKPresheaf R M k).map (opHomOfLE sq.le₂₄))
      ((localHomologyKPresheaf R M k).map (opHomOfLE sq.le₃₄))
      ((localHomologyKPresheaf R M k).map (opHomOfLE sq.le₁₂))
      ((localHomologyKPresheaf R M k).map (opHomOfLE sq.le₁₃)) := by
  obtain ⟨rfl, rfl⟩ := sq
  -- The coercions of `K₂ ⊓ K₃` and `K₂ ⊔ K₃` to sets are definitionally `↑K₂ ∩ ↑K₃` and
  -- `↑K₂ ∪ ↑K₃` (`Compacts.coe_inf`, `Compacts.coe_sup`).
  exact isPullback_localHomologyRestriction K₂.isCompact.isClosed K₃.isCompact.isClosed h

section LocallyCompact

variable [T2Space M] [LocallyCompactSpace M]

variable [HasFilteredColimitsOfSize.{w, w} A] [AB5OfSize.{w, w} A]

/-- **The continuity axiom for local homology.** On a locally compact Hausdorff space, for
coefficients in an abelian category whose filtered colimits are exact, `Hₖ(M, M ∖ K)` is the
colimit of the groups `Hₖ(M, M ∖ L)` over the compact neighbourhoods `L` of `K`, through the
restriction maps. -/
def localHomologyKPresheaf.isColimitCoconeOfCompacts (k : ℕ) (K : Compacts (TopCat.of M)) :
    IsColimit ((localHomologyKPresheaf R M k).coconeOfCompacts K) := by
  -- Relative homology of the pairs `(M, M ∖ L)` over the compact neighbourhoods `L` of `K`, since
  -- a compact subset of `M ∖ K` misses some compact neighbourhood of `K`.
  have hL : ∀ ⦃L L' : (K.compactNhds)ᵒᵖ⦄, (L ⟶ L') → (L'.unop.val : Set M) ⊆ L.unop.val :=
    fun _ _ h ↦ leOfHom h.unop
  have hc := isColimitComplPairCocone hL
    (fun L ↦ Compacts.subset_of_mem_compactNhds L.unop.property) R k
    fun T hT hTK ↦
      let ⟨L, hLK, hLT⟩ := K.exists_mem_compactNhds_disjoint hT.isClosed hTK.symm
      ⟨op ⟨L, hLK⟩, hLT.symm⟩
  rw [TopPair.singularHomologyFunctor_eq_toSSetPair_comp] at hc
  -- The diagram and the cocone of `hc` are those of the K-presheaf, with components the local
  -- homology groups and the restriction maps.
  let α : complPairDiagram hL ⋙ TopPair.toSSetPair ⋙ SSetPair.homologyFunctor R k ≅
      (Set.mono_coe K.compactNhds).functor.op ⋙ localHomologyKPresheaf R M k :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) fun h ↦ (Category.comp_id _).trans
      ((localHomologyRestriction_def R (hL h) k).symm.trans (Category.id_comp _).symm)
  refine IsColimit.precomposeHomEquiv α _ (hc.ofIsoColimit (Cocone.ext (Iso.refl _) fun L ↦ ?_))
  -- Both legs are the restriction map from a compact neighbourhood of `K` to `K`.
  exact (Category.comp_id _).trans ((localHomologyRestriction_def R
    (Compacts.subset_of_mem_compactNhds L.unop.property) k).symm.trans (Category.id_comp _).symm)

/-- On a locally compact Hausdorff space, for coefficients in an abelian category whose filtered
colimits are exact, the local homology K-presheaf `K ↦ Hₖ(M, M ∖ K)` is a K-sheaf as soon as
`Hₖ₊₁(M, M ∖ K)` vanishes for every compact `K`. -/
theorem isKSheaf_localHomologyKPresheaf_of_isZero {k : ℕ}
    (h : ∀ K : Compacts (TopCat.of M), IsZero (localHomology R (K : Set M) (k + 1))) :
    (localHomologyKPresheaf R M k).IsKSheaf where
  nonempty_isTerminal := ⟨(isZero_localHomology_empty R k).isTerminal⟩
  isPullback sq := isPullback_localHomologyKPresheaf_map R sq (h _)
  nonempty_isColimit_coconeOfCompacts K :=
    ⟨localHomologyKPresheaf.isColimitCoconeOfCompacts R k K⟩

end LocallyCompact

section Manifold

variable {Λ : Type w} [Ring Λ] (N : ModuleCat.{w} Λ) (M : Type w) [TopologicalSpace M] [T2Space M]
  {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]

/-- **The orientation K-sheaf.** For a Hausdorff space `M` modelled on a real normed space `E` of
finite dimension `n`, a topological `n`-manifold without boundary, the local homology K-presheaf
`K ↦ Hₙ(M, M ∖ K)` with coefficients in a module is a K-sheaf. -/
theorem isKSheaf_localHomologyKPresheaf {n : ℕ} (hn : Module.finrank ℝ E = n) :
    (localHomologyKPresheaf N M n).IsKSheaf :=
  have := ChartedSpace.locallyCompactSpace E M
  isKSheaf_localHomologyKPresheaf_of_isZero N fun K ↦
    isZero_localHomology_of_isCompact N hn K.isCompact (Nat.lt_succ_self n)

variable (E) in
/-- The **orientation K-sheaf** `K ↦ Hₙ(M, M ∖ K)` of a Hausdorff space `M` modelled on a real
normed space `E` of finite dimension `n`, with coefficients in a module `N`. -/
def orientationKSheaf : TopCat.KSheaf (ModuleCat.{w} Λ) (TopCat.of M) :=
  ⟨localHomologyKPresheaf N M (Module.finrank ℝ E), isKSheaf_localHomologyKPresheaf N M rfl⟩

variable (E) in
@[simp]
lemma orientationKSheaf_obj :
    (orientationKSheaf N M E).obj = localHomologyKPresheaf N M (Module.finrank ℝ E) :=
  (rfl)

end Manifold

end TauCeti
