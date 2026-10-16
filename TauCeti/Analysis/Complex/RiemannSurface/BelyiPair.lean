/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.MonodromyTriple
public import TauCeti.Analysis.Complex.RiemannSurface.PowerMap

import TauCeti.Data.Set.Restrict

/-!
# Analytic Belyi pairs

An **analytic Belyi pair** `(X, β)` is a compact connected Riemann surface `X` together with a
nonconstant holomorphic map `β : X → ℙ¹(ℂ)` to the Riemann sphere `OnePoint ℂ` whose branch values
lie in `{0, 1, ∞}`; `β` is then a *Belyi map*. Equivalently, `β` is a covering map over the
complement of `{0, 1, ∞}` (`TauCeti.AnalyticBelyiPair.isCoveringMapOn`, and the constructor
`TauCeti.AnalyticBelyiPair.ofIsCoveringMapOn`), since a finite holomorphic map of a compact
surface is a covering exactly away from its branch values.

Restricting `β` over the thrice-punctured sphere `ℂ ∖ {0, 1}` gives a finite covering map
`TauCeti.AnalyticBelyiPair.restrict`, of degree the degree of `β`. Its monodromy triple, for any
numbering of the fibre over the basepoint `1/2`, is a permutation triple of that degree, and its
isomorphism class `TauCeti.AnalyticBelyiPair.isoClass` does not depend on the numbering. This is
the combinatorial datum attached to the pair, the one through which analytic Belyi pairs are
compared with permutation triples and dessins d'enfants.

The basic examples live on the sphere itself: for `n ≠ 0`, the power map `z ↦ z ^ n` is a Belyi
map of degree `n`, ramified of index `n` over `0` and `∞` and unramified over `1`
(`TauCeti.AnalyticBelyiPair.pow`). For `n = 1` this is the trivial pair, the identity of the
sphere.

## Main declarations

* `TauCeti.AnalyticBelyiPair`: the carrier, a compact connected Riemann surface with a finite
  holomorphic map to the sphere whose branch values lie in `{0, 1, ∞}`.
* `TauCeti.AnalyticBelyiPair.ofIsCoveringMapOn`: a nonconstant holomorphic map to the sphere that
  is a covering map over the complement of `{0, 1, ∞}` is a Belyi map.
* `TauCeti.AnalyticBelyiPair.ncard_preimage_singleton`: the fibres of `β` away from `{0, 1, ∞}`
  have as many points as the degree.
* `TauCeti.AnalyticBelyiPair.restrict`, `TauCeti.AnalyticBelyiPair.isCoveringMap_restrict`: the
  restriction of `β` over `ℂ ∖ {0, 1}` is a covering map, with
  `TauCeti.AnalyticBelyiPair.ncard_restrict_preimage_singleton` points in each fibre.
* `TauCeti.AnalyticBelyiPair.isoClass`, `TauCeti.AnalyticBelyiPair.isoClass_eq`: the isomorphism
  class of the monodromy triple, computed by any numbering of the fibre over `1/2`.
* `TauCeti.AnalyticBelyiPair.pow`: the power map `z ↦ z ^ n` of the sphere, of degree `n`
  (`TauCeti.RiemannSurface.degree_onePointMap_pow`).

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  Chapter 3 (Belyi functions and Belyi pairs) and §4.3 (the monodromy of a Belyi pair).
* L. Schneps, *Dessins d'enfants on the Riemann sphere*, in *The Grothendieck Theory of Dessins
  d'Enfants*, London Mathematical Society Lecture Note Series 200, Cambridge University Press,
  1994.
-/

public noncomputable section

open Function OnePoint Set Topology

open scoped Manifold

universe u

namespace TauCeti

open RiemannSurface ThricePuncturedSphere

open scoped ContDiff in
/-- An **analytic Belyi pair**: a compact connected Riemann surface `X`, carried by the unbundled
instances on its type, together with a finite holomorphic map `β : X → OnePoint ℂ` to the Riemann
sphere, the **Belyi map**, all of whose branch values lie in `{0, 1, ∞}`.

On a compact connected surface every nonconstant holomorphic map is finite, so `β` is just a
nonconstant holomorphic map (`TauCeti.AnalyticBelyiPair.ofIsCoveringMapOn` builds a pair from
these data). The condition on the branch values says that `β` is a covering map over the
complement of `{0, 1, ∞}` (`TauCeti.AnalyticBelyiPair.isCoveringMapOn`). -/
structure AnalyticBelyiPair : Type (u + 1) where
  /-- The Riemann surface of the pair. -/
  X : Type u
  [instTopologicalSpace : TopologicalSpace X]
  [instChartedSpace : ChartedSpace ℂ X]
  [instIsManifold : IsManifold 𝓘(ℂ) ω X]
  [instT2Space : T2Space X]
  [instCompactSpace : CompactSpace X]
  [instConnectedSpace : ConnectedSpace X]
  /-- The Belyi map of the pair. -/
  β : FiniteHolomorphicMap X (OnePoint ℂ)
  /-- The Belyi map is unramified over every point other than `0`, `1` and `∞`. -/
  branchValues_subset :
    β.branchValues ⊆ {((0 : ℂ) : OnePoint ℂ), ((1 : ℂ) : OnePoint ℂ), (∞ : OnePoint ℂ)}

attribute [instance] AnalyticBelyiPair.instTopologicalSpace AnalyticBelyiPair.instChartedSpace
  AnalyticBelyiPair.instIsManifold AnalyticBelyiPair.instT2Space
  AnalyticBelyiPair.instCompactSpace AnalyticBelyiPair.instConnectedSpace

namespace AnalyticBelyiPair

variable (P : AnalyticBelyiPair.{u})

/-! ### Belyi maps as coverings -/

/-- The Belyi map of an analytic Belyi pair is a covering map over the complement of
`{0, 1, ∞}`. -/
theorem isCoveringMapOn :
    IsCoveringMapOn P.β ({((0 : ℂ) : OnePoint ℂ), ((1 : ℂ) : OnePoint ℂ), ∞}ᶜ) :=
  (P.β.isCoveringMapOn_iff _).2 (compl_subset_compl.2 P.branchValues_subset)

open scoped ContDiff in
/-- An analytic Belyi pair from a nonconstant holomorphic map `f` from a compact connected Riemann
surface to the sphere which is a covering map over the complement of `{0, 1, ∞}`. -/
-- The body is exposed so that the surface of the pair is `X` by definition.
@[expose]
def ofIsCoveringMapOn (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [T2Space X] [CompactSpace X] [ConnectedSpace X] {f : X → OnePoint ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hne : ∃ x x', f x ≠ f x')
    (hcov : IsCoveringMapOn f
      ({((0 : ℂ) : OnePoint ℂ), ((1 : ℂ) : OnePoint ℂ), (∞ : OnePoint ℂ)}ᶜ)) :
    AnalyticBelyiPair.{u} where
  X := X
  β := .ofMDifferentiable hf hne
  branchValues_subset := compl_subset_compl.1 <|
    ((FiniteHolomorphicMap.ofMDifferentiable hf hne).isCoveringMapOn_iff _).1 <| by
      rwa [FiniteHolomorphicMap.coe_ofMDifferentiable]

open scoped ContDiff in
@[simp]
theorem coe_β_ofIsCoveringMapOn (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [T2Space X] [CompactSpace X] [ConnectedSpace X] {f : X → OnePoint ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hne : ∃ x x', f x ≠ f x')
    (hcov : IsCoveringMapOn f
      ({((0 : ℂ) : OnePoint ℂ), ((1 : ℂ) : OnePoint ℂ), (∞ : OnePoint ℂ)}ᶜ)) :
    ⇑(ofIsCoveringMapOn X hf hne hcov).β = f :=
  FiniteHolomorphicMap.coe_ofMDifferentiable hf hne

/-- Away from `{0, 1, ∞}`, every fibre of the Belyi map has as many points as its degree. -/
theorem ncard_preimage_singleton {y : OnePoint ℂ}
    (hy : y ∉ ({((0 : ℂ) : OnePoint ℂ), ((1 : ℂ) : OnePoint ℂ), ∞} : Set (OnePoint ℂ))) :
    (P.β ⁻¹' {y}).ncard = degree P.β := by
  rw [ncard_eq_toFinset_card _ (P.β.finite_fiber y)]
  exact (P.β.card_fiber_eq_degree_iff y).2 fun h ↦ hy (P.branchValues_subset h)

/-! ### The cover of the thrice-punctured sphere -/

/-- The Belyi map restricted to the points of `X` over the thrice-punctured sphere `ℂ ∖ {0, 1}`,
as a map to `ℂ ∖ {0, 1}`: this is the finite cover of the thrice-punctured sphere attached to the
pair (`TauCeti.AnalyticBelyiPair.isCoveringMap_restrict`). -/
def restrict : P.β ⁻¹' range toOnePoint → ThricePuncturedSphere :=
  isOpenEmbedding_toOnePoint.isEmbedding.toHomeomorph.symm ∘
    (range toOnePoint).restrictPreimage P.β

/-- The restricted Belyi map agrees with the Belyi map, read in the Riemann sphere. -/
@[simp]
theorem coe_restrict_apply (x : P.β ⁻¹' range toOnePoint) :
    (((P.restrict x : ThricePuncturedSphere) : ℂ) : OnePoint ℂ) = P.β x := by
  have h : isOpenEmbedding_toOnePoint.isEmbedding.toHomeomorph (P.restrict x) =
      (range toOnePoint).restrictPreimage P.β x :=
    Homeomorph.apply_symm_apply _ _
  simpa using congrArg Subtype.val h

/-- **The cover attached to an analytic Belyi pair.** The Belyi map restricted over the
thrice-punctured sphere `ℂ ∖ {0, 1}` is a covering map. -/
theorem isCoveringMap_restrict : IsCoveringMap P.restrict :=
  have h : IsCoveringMapOn P.β (range toOnePoint) := range_toOnePoint ▸ P.isCoveringMapOn
  h.isCoveringMap_restrictPreimage.homeomorph_comp _

/-- The points of `X` over a point `z` of `ℂ ∖ {0, 1}` are the fibre of the Belyi map over `z`. -/
theorem image_val_restrict_preimage_singleton (z : ThricePuncturedSphere) :
    (↑) '' (P.restrict ⁻¹' {z}) = P.β ⁻¹' {toOnePoint z} := by
  simp only [restrict, preimage_comp, Homeomorph.preimage_symm, image_singleton,
    Set.image_val_preimage_restrictPreimage]
  rw [Topology.IsEmbedding.toHomeomorph_apply_coe]

/-- Every fibre of the cover of `ℂ ∖ {0, 1}` attached to an analytic Belyi pair is finite. -/
theorem finite_restrict_preimage_singleton (z : ThricePuncturedSphere) :
    (P.restrict ⁻¹' {z}).Finite :=
  (finite_image_iff Subtype.val_injective.injOn).1 <|
    P.image_val_restrict_preimage_singleton z ▸ P.β.finite_fiber _

/-- The cover of `ℂ ∖ {0, 1}` attached to an analytic Belyi pair has as many sheets as the degree
of the Belyi map. -/
theorem ncard_restrict_preimage_singleton (z : ThricePuncturedSphere) :
    (P.restrict ⁻¹' {z}).ncard = degree P.β := by
  rw [restrict, preimage_comp, Homeomorph.preimage_symm, image_singleton,
    TauCeti.ncard_fiber_restrictPreimage, Topology.IsEmbedding.toHomeomorph_apply_coe]
  refine P.ncard_preimage_singleton ?_
  rw [← mem_compl_iff, ← range_toOnePoint]
  exact mem_range_self z

/-- Every fibre of the cover of `ℂ ∖ {0, 1}` attached to an analytic Belyi pair can be numbered by
`Fin (degree P.β)`. -/
theorem nonempty_restrict_preimage_singleton_equiv (z : ThricePuncturedSphere) :
    Nonempty (P.restrict ⁻¹' {z} ≃ Fin (degree P.β)) := by
  have := (P.finite_restrict_preimage_singleton z).to_subtype
  rw [← P.ncard_restrict_preimage_singleton z, ← Nat.card_coe_set_eq]
  exact ⟨Finite.equivFin _⟩

/-! ### The monodromy triple -/

/-- **The permutation triple of an analytic Belyi pair**, up to isomorphism: the isomorphism class
of the monodromy triple of the cover of `ℂ ∖ {0, 1}` attached to the pair. It is computed by any
numbering of the fibre over `1/2` (`TauCeti.AnalyticBelyiPair.isoClass_eq`). -/
def isoClass : PermutationTriple.IsoClass (degree P.β) :=
  .mk (P.isCoveringMap_restrict.monodromyTriple
    (P.nonempty_restrict_preimage_singleton_equiv basePt).some)

/-- The permutation triple of an analytic Belyi pair is the class of the monodromy triple for any
numbering of the fibre over `1/2`. -/
theorem isoClass_eq (ν : P.restrict ⁻¹' {basePt} ≃ Fin (degree P.β)) :
    P.isoClass = .mk (P.isCoveringMap_restrict.monodromyTriple ν) :=
  P.isCoveringMap_restrict.isoClass_monodromyTriple_eq _ _

/-! ### The power maps -/

/-- **The power maps are Belyi maps.** For `n ≠ 0`, the Riemann sphere with the power map
`z ↦ z ^ n` is an analytic Belyi pair; it is ramified of index `n` over `0` and `∞` and
unramified elsewhere. For `n = 1` it is the trivial pair, the identity of the sphere. -/
-- The body is exposed so that the surface of the pair is `OnePoint ℂ` by definition.
@[expose]
def pow {n : ℕ} (hn : n ≠ 0) : AnalyticBelyiPair.{0} where
  X := OnePoint ℂ
  β := .spherePow hn
  branchValues_subset := (FiniteHolomorphicMap.branchValues_spherePow_subset hn).trans <| by
    simp [insert_subset_iff]

@[simp]
theorem coe_β_pow {n : ℕ} (hn : n ≠ 0) : ⇑(pow hn).β = OnePoint.map fun z : ℂ ↦ z ^ n :=
  FiniteHolomorphicMap.coe_spherePow hn

end AnalyticBelyiPair

end TauCeti
