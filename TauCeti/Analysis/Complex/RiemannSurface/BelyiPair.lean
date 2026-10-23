/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.MonodromyTriple
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.TopBranchedCover
public import TauCeti.Analysis.Complex.RiemannSurface.ChebyshevMap
public import TauCeti.Analysis.Complex.RiemannSurface.LocalNormalForm
public import TauCeti.Analysis.Complex.RiemannSurface.PowerMap
public import TauCeti.Combinatorics.PermutationTriple.IsoClass
public import TauCeti.Combinatorics.PermutationTriple.Regular

import TauCeti.AlgebraicTopology.ThricePuncturedSphere.Deck
import TauCeti.AlgebraicTopology.ThricePuncturedSphere.RestrictOver
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.GroupTheory.GroupAction.Free

/-!
# Analytic Belyi pairs

An **analytic Belyi pair** `(X, β)` is a compact connected Riemann surface `X` together with a
nonconstant holomorphic map `β : X → ℙ¹(ℂ)` to the Riemann sphere `OnePoint ℂ` whose branch values
lie in `{0, 1, ∞}`; `β` is then a *Belyi map*. Equivalently, `β` is a covering map over the
complement of `{0, 1, ∞}` (`TauCeti.AnalyticBelyiPair.isCoveringMapOn`, and the constructor
`TauCeti.AnalyticBelyiPair.ofIsCoveringMapOn`), since a finite holomorphic map of a compact
surface is a covering exactly away from its branch values.

Restricting `β` over the thrice-punctured sphere `ℂ ∖ {0, 1}` gives a finite covering map
`TauCeti.AnalyticBelyiPair.restrict`, of degree the degree of `β`. Its total space, the surface
`X` with the finitely many points over `0`, `1` and `∞` removed, is path connected. Its monodromy
triple, for any numbering of the fibre over the basepoint `1/2`, is therefore a connected
permutation triple of that degree, and its isomorphism class
`TauCeti.AnalyticBelyiPair.connectedIsoClass` does not depend on the numbering. This is
the combinatorial datum attached to the pair, the one through which analytic Belyi pairs are
compared with permutation triples and dessins d'enfants.

An isomorphism of analytic Belyi pairs is a biholomorphism of their surfaces over the sphere
(`TauCeti.AnalyticBelyiPair.Iso`). It restricts to an isomorphism of the attached covers of
`ℂ ∖ {0, 1}`, so isomorphic pairs have the same degree and isomorphic monodromy triples, and the
permutation triple is a well-defined function of the isomorphism class of a pair of degree `n`
(`TauCeti.AnalyticBelyiPair.toIsoClass`). This is the map from analytic Belyi pairs to permutation
triples through which the analytic Riemann existence theorem for three-point covers compares the
two classifications.

An isomorphism of pairs is determined by the image of a single point over `ℂ ∖ {0, 1}`
(`TauCeti.AnalyticBelyiPair.Iso.eq_of_apply_eq`): its restriction is a lift through the connected
cover attached to the target, and the points over `ℂ ∖ {0, 1}` are dense in the surface. Hence
there are at most as many isomorphisms `P ≅ Q` as the degree of `Q`, and the automorphisms of a
pair form a finite group whose order divides its degree.

This group is the deck group of the pair in each of its guises. Since every homeomorphism over the
sphere is holomorphic (see below), the automorphisms of a pair are the deck transformations of its
Belyi map (`TauCeti.AnalyticBelyiPair.isoMulEquivDeck`). These restrict to the deck
transformations of the attached cover of `ℂ ∖ {0, 1}`, and those are the automorphisms of its
monodromy triple. So the automorphism group of a pair is the automorphism group of its monodromy
triple, for any numbering of the fibre over `1/2`
(`TauCeti.AnalyticBelyiPair.isoMulEquivAutomorphismGroup`), and a pair has as many automorphisms
as its degree exactly when its triple is regular.

Forgetting the complex structure turns a pair of degree `n` into a topological branched cover
of degree `n` (`TauCeti.AnalyticBelyiPair.toTopBranchedCover`). The topological local degree is
the analytic local multiplicity, and isomorphisms of pairs give isomorphisms of their underlying
topological branched covers. Consequently this construction descends to isomorphism classes.

Conversely, the complex structure of a pair is determined by its Belyi map: every continuous map
over the sphere between analytic Belyi pairs is holomorphic
(`TauCeti.AnalyticBelyiPair.mdifferentiable_of_β`). Away from the points over `0`, `1` and
`∞` it lifts the Belyi map of the source through the Belyi map of the target, which is a local
biholomorphism there; the finitely many remaining points are removable singularities. Hence a
homeomorphism over the sphere is an isomorphism of pairs
(`TauCeti.AnalyticBelyiPair.Iso.ofHomeomorph`), and the passage to topological branched covers is
injective on isomorphism classes
(`TauCeti.AnalyticBelyiPair.toTopBranchedCoverIsoClass_injective`).

A morphism of analytic Belyi pairs `P → Q` is a holomorphic map of surfaces over the sphere
(`TauCeti.AnalyticBelyiPair.Hom`); as for isomorphisms, every continuous map over the sphere is
one. A morphism is a finite holomorphic map, hence surjective, and the degrees multiply along it,
so the degree of `Q` divides that of `P`. A morphism between pairs of the same degree has degree
one, so it is an isomorphism (`TauCeti.AnalyticBelyiPair.Hom.toIso`). A morphism restricts to a
map of the attached covers of `ℂ ∖ {0, 1}`, and so it intertwines the monodromy triples on the
fibres over `1/2`.

The basic examples live on the sphere itself: for `n ≠ 0`, the power map `z ↦ z ^ n` is a Belyi
map of degree `n`, ramified of index `n` over `0` and `∞` and unramified over `1`
(`TauCeti.AnalyticBelyiPair.pow`). For `n = 1` this is the trivial pair, the identity of the
sphere. It is terminal: the Belyi map of a pair is its unique morphism to the trivial pair
(`TauCeti.AnalyticBelyiPair.homPowOne`). A pair of degree one is trivial, its Belyi map being a
biholomorphism onto the sphere, so all pairs of degree one are isomorphic
(`TauCeti.AnalyticBelyiPair.isoOfDegreeEqOne`). The polynomial `z ↦ 4z(1 - z)` is a Belyi map
of degree `2`, unramified over `0` and ramified of index `2` over `1` and `∞`, so that its
ramification partitions over `0`, `1` and `∞` are `[1, 1]`, `[2]` and `[2]`
(`TauCeti.AnalyticBelyiPair.chebyshev`).

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
* `TauCeti.AnalyticBelyiPair.instPathConnectedSpacePreimageRange`: the total space of this cover
  is path connected.
* `TauCeti.AnalyticBelyiPair.isoClass`, `TauCeti.AnalyticBelyiPair.isoClass_eq`: the isomorphism
  class of the monodromy triple, computed by any numbering of the fibre over `1/2`.
* `TauCeti.AnalyticBelyiPair.connectedIsoClass`, `TauCeti.AnalyticBelyiPair.connectedIsoClass_eq`:
  the same class among connected triples (`TauCeti.AnalyticBelyiPair.isConnected_isoClass`).
* `TauCeti.AnalyticBelyiPair.Iso`: isomorphisms of analytic Belyi pairs, with
  `TauCeti.AnalyticBelyiPair.Iso.restrict` the isomorphism of the attached covers of `ℂ ∖ {0, 1}`.
* `TauCeti.AnalyticBelyiPair.Iso.degree_eq` and
  `TauCeti.AnalyticBelyiPair.Iso.isoClass_monodromyTriple_eq`: isomorphic pairs have the same
  degree and isomorphic monodromy triples.
* `TauCeti.AnalyticBelyiPair.isoSetoid`, `TauCeti.AnalyticBelyiPair.toIsoClass`: isomorphism of
  pairs of degree `n`, and the permutation triple of an isomorphism class of such pairs.
* `TauCeti.AnalyticBelyiPair.Iso.eq_of_apply_eq`: an isomorphism of pairs is determined by the
  image of one point over `ℂ ∖ {0, 1}`.
* `TauCeti.AnalyticBelyiPair.Iso.natCard_le_degree`: there are finitely many isomorphisms of
  pairs `P ≅ Q`, at most the degree of `Q`.
* `TauCeti.AnalyticBelyiPair.Iso.natCard_dvd_degree`: the order of the automorphism group
  `P.Iso P` divides the degree of `P`.
* `TauCeti.AnalyticBelyiPair.isoMulEquivDeck`: the automorphisms of a pair are the deck
  transformations of its Belyi map.
* `TauCeti.AnalyticBelyiPair.isoMulEquivAutomorphismGroup`: the automorphism group of a pair is
  the automorphism group of its monodromy triple.
* `TauCeti.AnalyticBelyiPair.isRegular_monodromyTriple_iff_natCard_iso`: the monodromy triple is
  regular exactly when the pair has as many automorphisms as its degree.
* `TauCeti.AnalyticBelyiPair.toTopBranchedCover`: the underlying topological branched cover, whose
  ramification partitions are formed by the local multiplicities of the Belyi map
  (`TauCeti.AnalyticBelyiPair.parts_ramificationPartition_toTopBranchedCover`) and whose unbranched
  part has the monodromy of the pair
  (`TauCeti.AnalyticBelyiPair.isoClass_monodromyTriple_toTopBranchedCover`).
* `TauCeti.AnalyticBelyiPair.toTopBranchedCoverIsoClass`: the induced map on isomorphism classes.
* `TauCeti.AnalyticBelyiPair.mdifferentiable_of_β`: a continuous map over the sphere between
  analytic Belyi pairs is holomorphic.
* `TauCeti.AnalyticBelyiPair.Iso.ofHomeomorph`: a homeomorphism over the sphere is an isomorphism
  of analytic Belyi pairs.
* `TauCeti.AnalyticBelyiPair.toTopBranchedCoverIsoClass_injective`: analytic Belyi pairs with
  isomorphic underlying topological branched covers are isomorphic.
* `TauCeti.AnalyticBelyiPair.pow`: the power map `z ↦ z ^ n` of the sphere, of degree `n`
  (`TauCeti.AnalyticBelyiPair.degree_β_pow`), unramified over `1`
  (`TauCeti.AnalyticBelyiPair.one_notMem_branchValues_β_pow`).
* `TauCeti.AnalyticBelyiPair.Hom`: morphisms of analytic Belyi pairs, with
  `TauCeti.AnalyticBelyiPair.Hom.ofContinuous`, `TauCeti.AnalyticBelyiPair.Hom.surjective`,
  `TauCeti.AnalyticBelyiPair.Hom.degree_β_eq_mul_degree` (degrees multiply),
  `TauCeti.AnalyticBelyiPair.Hom.toIso` (a morphism between pairs of the same degree is an
  isomorphism) and `TauCeti.AnalyticBelyiPair.Hom.semiconj_component_monodromyTriple` (a morphism
  intertwines the monodromy triples).
* `TauCeti.AnalyticBelyiPair.homPowOne`: the Belyi map, as the unique morphism to the trivial pair.
* `TauCeti.AnalyticBelyiPair.isoOfDegreeEqOne`,
  `TauCeti.AnalyticBelyiPair.degree_β_eq_one_iff_nonempty_iso`: pairs of degree one are isomorphic
  to each other and to the trivial pair.
* `TauCeti.AnalyticBelyiPair.chebyshev`: the map `z ↦ 4z(1 - z)` of the sphere, of degree `2`
  (`TauCeti.AnalyticBelyiPair.degree_β_chebyshev`), with branch values `1` and `∞`
  (`TauCeti.AnalyticBelyiPair.branchValues_β_chebyshev`); its fibres and local multiplicities
  over `0`, `1` and `∞` are `TauCeti.RiemannSurface.preimage_onePointMap_four_mul_mul_one_sub_zero`
  and its companions in `TauCeti.Analysis.Complex.RiemannSurface.ChebyshevMap`.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer 1981,
  §8, Theorem 8.5 (uniqueness of the extension of an unbranched covering across a finite set).
* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §2.7 (the monodromy and the covering group of a morphism), Chapter 3 (Belyi functions and Belyi
  pairs) and §4.3 (the monodromy of a Belyi pair).
* L. Schneps, *Dessins d'enfants on the Riemann sphere*, in *The Grothendieck Theory of Dessins
  d'Enfants*, London Mathematical Society Lecture Note Series 200, Cambridge University Press,
  1994.
-/

public noncomputable section

open Function OnePoint Set Topology

open scoped Manifold

universe u v w w'

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

/-! ### The underlying topological branched cover -/

/-- A Belyi map is locally the power map whose exponent is its analytic local multiplicity. -/
theorem isLocalPowerAt_localMultiplicity (P : AnalyticBelyiPair.{u}) (z : P.X) :
    IsLocalPowerAt P.β z (localMultiplicity P.β z) :=
  RiemannSurface.isLocalPowerAt_localMultiplicity
    (.of_forall fun y ↦ P.β.holomorphic y) (P.β.not_eventuallyConst z)

/-- **The topological branched cover underlying an analytic Belyi pair.** The supplied equality
records the degree in the index. Its local power models are the holomorphic local normal forms,
and its topological local degree agrees with analytic local multiplicity
(`TauCeti.AnalyticBelyiPair.localDegree_toTopBranchedCover`). -/
-- The body is exposed so that the total space of the branched cover is `P.X` by definition.
@[expose]
def toTopBranchedCover (P : AnalyticBelyiPair.{u}) {n : ℕ}
    (hdegree : degree P.β = n) : TopBranchedCover n where
  Z := P.X
  instSecondCountableTopology := ChartedSpace.secondCountable_of_sigmaCompact ℂ P.X
  π := ⟨P.β, P.β.holomorphic.continuous⟩
  surjective := P.β.surjective
  isCoveringMapOn := by
    convert P.isCoveringMapOn using 1
    ext y
    simp only [mem_compl_iff, mem_marked, mem_insert_iff, mem_singleton_iff]
  natCard_preimage_singleton y hy := by
    rw [Nat.card_coe_set_eq, ← hdegree]
    apply P.ncard_preimage_singleton
    intro hy'
    apply hy
    rw [mem_marked]
    simpa only [mem_insert_iff, mem_singleton_iff] using hy'
  exists_isLocalPowerAt_of_mem_marked z _ :=
    ⟨localMultiplicity P.β z, P.isLocalPowerAt_localMultiplicity z⟩

/-- The projection of the topological branched cover underlying a pair is its Belyi map. -/
@[simp]
theorem toTopBranchedCover_π_apply (P : AnalyticBelyiPair.{u}) {n : ℕ}
    (hdegree : degree P.β = n) (z : P.X) :
    (P.toTopBranchedCover hdegree).π z = P.β z :=
  rfl

/-- The topological local degree underlying an analytic Belyi pair is the analytic local
multiplicity of its Belyi map. -/
@[simp]
theorem localDegree_toTopBranchedCover (P : AnalyticBelyiPair.{u}) {n : ℕ}
    (hdegree : degree P.β = n) (z : P.X) :
    (P.toTopBranchedCover hdegree).localDegree z = localMultiplicity P.β z :=
  (P.toTopBranchedCover hdegree).localDegree_eq_iff.2 (P.isLocalPowerAt_localMultiplicity z)

/-- The ramification partition over `y` of the topological branched cover underlying a pair is
formed by the analytic local multiplicities of its Belyi map at the points over `y`. -/
theorem parts_ramificationPartition_toTopBranchedCover (P : AnalyticBelyiPair.{u}) {n : ℕ}
    (hdegree : degree P.β = n) (y : OnePoint ℂ) :
    ((P.toTopBranchedCover hdegree).ramificationPartition y).parts =
      (P.β.finite_fiber y).toFinset.val.map (localMultiplicity P.β) := by
  rw [TopBranchedCover.parts_ramificationPartition]
  -- The fibres of `(P.toTopBranchedCover hdegree).π` are those of `P.β` by definition
  -- (`TauCeti.AnalyticBelyiPair.toTopBranchedCover_π_apply` is `rfl`).
  exact Multiset.map_congr rfl fun z _ ↦ P.localDegree_toTopBranchedCover hdegree z

/-! ### Maps over the sphere are holomorphic -/

/-- **A continuous map over the sphere between analytic Belyi pairs is holomorphic.** Away from
the points over `0`, `1` and `∞`, `f` lifts the Belyi map of `P` through that of `Q`, which is a
local biholomorphism there; the finitely many points over `0`, `1` and `∞` are removable
singularities. So the complex structure of a pair is determined by its Belyi map. -/
theorem mdifferentiable_of_β {P : AnalyticBelyiPair.{u}} {Q : AnalyticBelyiPair.{v}}
    {f : P.X → Q.X} (hf : Continuous f) (hβ : ∀ x, Q.β (f x) = P.β x) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  have hP : ∀ y, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) P.β y := P.β.holomorphic
  have hQ : ∀ y, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) Q.β y := Q.β.holomorphic
  have hβ_comp : Q.β ∘ f = P.β := funext hβ
  -- Off the marked fibres, `Q.β` has multiplicity one at `f x`, so it is injective near `f x`.
  have hunb : ∀ x, P.β x ∉ marked → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x := fun x hx ↦ by
    have hfx : Q.β (f x) ∉ Q.β.branchValues := fun h ↦ hx <| by
      simpa only [mem_marked, mem_insert_iff, mem_singleton_iff, hβ] using
        Q.branchValues_subset h
    refine mdifferentiableAt_of_comp_of_injOn hf.continuousAt (.of_forall hQ)
      ((localMultiplicity_eq_one_iff (.of_forall hQ)).1
        ((Q.β.notMem_branchValues_iff _).1 hfx _ rfl)) (.of_forall fun y ↦ ?_)
    rw [hβ_comp]
    exact hP y
  intro x
  by_cases hx : P.β x ∈ marked
  · -- The marked fibres are finite, so the other points near `x` are unmarked.
    refine mdifferentiableAt_of_continuousAt_of_eventually_nhdsNE hf.continuousAt ?_
    have hfin : (P.β ⁻¹' marked).Finite := finite_marked.preimage' fun y _ ↦ P.β.finite_fiber y
    filter_upwards [nhdsWithin_le_nhds <|
      (hfin.sdiff (t := {x})).isClosed.isOpen_compl.mem_nhds (by simp), self_mem_nhdsWithin]
      with y hy hyx
    exact hunb y fun h ↦ hy ⟨h, hyx⟩
  · exact hunb x hx

/-! ### The cover of the thrice-punctured sphere -/

/-- The Belyi map restricted to the points of `X` over the thrice-punctured sphere `ℂ ∖ {0, 1}`,
as a map to `ℂ ∖ {0, 1}`: this is the finite cover of the thrice-punctured sphere attached to the
pair (`TauCeti.AnalyticBelyiPair.isCoveringMap_restrict`). -/
def restrict : P.β ⁻¹' range toOnePoint → ThricePuncturedSphere :=
  restrictOver P.β

/-- The restricted Belyi map agrees with the Belyi map, read in the Riemann sphere. -/
@[simp]
theorem coe_restrict_apply (x : P.β ⁻¹' range toOnePoint) :
    (((P.restrict x : ThricePuncturedSphere) : ℂ) : OnePoint ℂ) = P.β x :=
  coe_restrictOver_apply P.β x

/-- **The cover attached to an analytic Belyi pair.** The Belyi map restricted over the
thrice-punctured sphere `ℂ ∖ {0, 1}` is a covering map. -/
theorem isCoveringMap_restrict : IsCoveringMap P.restrict :=
  isCoveringMap_restrictOver <| by
    convert P.isCoveringMapOn using 1
    ext w
    simp only [mem_compl_iff, mem_marked, mem_insert_iff, mem_singleton_iff]

/-- The unbranched cover of the topological branched cover underlying a pair is the cover of
`ℂ ∖ {0, 1}` attached to the pair. -/
@[simp]
theorem restrict_toTopBranchedCover {n : ℕ} (hdegree : degree P.β = n) :
    (P.toTopBranchedCover hdegree).restrict = P.restrict :=
  -- Both total spaces are the points of `X` off the marked fibres, since the projection of
  -- `P.toTopBranchedCover hdegree` coerces to `P.β` by definition.
  funext fun z ↦ Subtype.ext <| OnePoint.coe_injective <|
    ((P.toTopBranchedCover hdegree).coe_restrict_apply z).trans (P.coe_restrict_apply z).symm

/-- The points of `X` over a point `z` of `ℂ ∖ {0, 1}` are the fibre of the Belyi map over `z`. -/
theorem image_val_restrict_preimage_singleton (z : ThricePuncturedSphere) :
    (↑) '' (P.restrict ⁻¹' {z}) = P.β ⁻¹' {toOnePoint z} :=
  image_val_restrictOver_preimage_singleton P.β z

/-- Every fibre of the cover of `ℂ ∖ {0, 1}` attached to an analytic Belyi pair is finite. -/
theorem finite_restrict_preimage_singleton (z : ThricePuncturedSphere) :
    (P.restrict ⁻¹' {z}).Finite :=
  finite_restrictOver_preimage_singleton P.β (P.β.finite_fiber _)

/-- The cover of `ℂ ∖ {0, 1}` attached to an analytic Belyi pair has as many sheets as the degree
of the Belyi map. -/
theorem ncard_restrict_preimage_singleton (z : ThricePuncturedSphere) :
    (P.restrict ⁻¹' {z}).ncard = degree P.β := by
  rw [restrict, ncard_restrictOver_preimage_singleton]
  refine P.ncard_preimage_singleton ?_
  have hz : toOnePoint z ∈ markedᶜ := by
    rw [← range_toOnePoint]
    exact mem_range_self z
  simpa only [mem_compl_iff, mem_marked, mem_insert_iff, mem_singleton_iff] using hz

/-- A numbering of a fibre of the cover of `ℂ ∖ {0, 1}` attached to an analytic Belyi pair by
`Fin n` determines the degree of the pair: it is `n`. -/
theorem degree_β_eq_of_restrict_preimage_singleton_equiv {z : ThricePuncturedSphere} {n : ℕ}
    (ν : P.restrict ⁻¹' {z} ≃ Fin n) : degree P.β = n := by
  rw [← P.ncard_restrict_preimage_singleton z, ← Nat.card_coe_set_eq, Nat.card_congr ν,
    Nat.card_fin]

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

/-- The cover of `ℂ ∖ {0, 1}` attached to a pair and the unbranched part of the topological branched
cover underlying the pair have isomorphic monodromy triples, whatever the numberings of their
fibres. -/
theorem isoClass_monodromyTriple_toTopBranchedCover {n : ℕ} (hdegree : degree P.β = n)
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n)
    (ν' : (P.toTopBranchedCover hdegree).restrict ⁻¹' {basePt} ≃ Fin n) :
    PermutationTriple.IsoClass.mk
        ((P.toTopBranchedCover hdegree).isCoveringMap_restrict.monodromyTriple ν') =
      PermutationTriple.IsoClass.mk (P.isCoveringMap_restrict.monodromyTriple ν) :=
  -- Both covers have total space the points of `X` off the marked fibres, since the projection of
  -- `P.toTopBranchedCover hdegree` is `P.β` by definition, and both projections are `P.β`.
  P.isCoveringMap_restrict.isoClass_monodromyTriple_eq_of_homeomorph ν
    (P.toTopBranchedCover hdegree).isCoveringMap_restrict ν' (Homeomorph.refl _) <|
    P.restrict_toTopBranchedCover hdegree

/-! ### Connectedness of the cover -/

/-- **The cover attached to an analytic Belyi pair is path connected.** Its total space is the
connected surface `X` with the finitely many points over `0`, `1` and `∞` removed. -/
instance instPathConnectedSpacePreimageRange :
    PathConnectedSpace (P.β ⁻¹' range toOnePoint) :=
  -- The projection of `P.toTopBranchedCover rfl` is `⟨P.β, _⟩`, whose coercion is `P.β` by
  -- definition (`TauCeti.AnalyticBelyiPair.toTopBranchedCover_π_apply` is `rfl`), so the two
  -- preimages are the same subtype.
  (P.toTopBranchedCover rfl).instPathConnectedSpacePreimageRange

/-- The permutation triple of an analytic Belyi pair is connected. -/
theorem isConnected_isoClass : P.isoClass.IsConnected := by
  rw [P.isoClass_eq (P.nonempty_restrict_preimage_singleton_equiv basePt).some,
    PermutationTriple.IsoClass.isConnected_mk]
  exact P.isCoveringMap_restrict.isConnected_monodromyTriple _

/-- **The connected permutation triple of an analytic Belyi pair**, up to isomorphism: the class
`TauCeti.AnalyticBelyiPair.isoClass`, as a class of connected triples. It is computed by any
numbering of the fibre over `1/2` (`TauCeti.AnalyticBelyiPair.connectedIsoClass_eq`). -/
def connectedIsoClass : ConnectedIsoClass (degree P.β) :=
  .mk ⟨P.isCoveringMap_restrict.monodromyTriple
      (P.nonempty_restrict_preimage_singleton_equiv basePt).some,
    P.isCoveringMap_restrict.isConnected_monodromyTriple _⟩

/-- Forgetting connectedness, the connected permutation triple of a pair is its permutation
triple. -/
@[simp]
theorem forget_connectedIsoClass : P.connectedIsoClass.forget = P.isoClass := by
  rw [connectedIsoClass, ConnectedIsoClass.forget_mk, P.isoClass_eq]

/-- The connected permutation triple of an analytic Belyi pair is the class of the monodromy
triple for any numbering of the fibre over `1/2`. -/
theorem connectedIsoClass_eq (ν : P.restrict ⁻¹' {basePt} ≃ Fin (degree P.β)) :
    P.connectedIsoClass = .mk ⟨P.isCoveringMap_restrict.monodromyTriple ν,
      P.isCoveringMap_restrict.isConnected_monodromyTriple ν⟩ :=
  ConnectedIsoClass.forget_injective <| by
    rw [forget_connectedIsoClass, ConnectedIsoClass.forget_mk, P.isoClass_eq ν]

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

/-- The power map `z ↦ z ^ n` of the sphere is a Belyi map of degree `n`. -/
theorem degree_β_pow {n : ℕ} (hn : n ≠ 0) : degree (pow hn).β = n :=
  (congrArg degree (coe_β_pow hn)).trans (degree_onePointMap_pow hn)

/-- The power map `z ↦ z ^ n` is unramified over `1`. -/
theorem one_notMem_branchValues_β_pow {n : ℕ} (hn : n ≠ 0) :
    ((1 : ℂ) : OnePoint ℂ) ∉ (pow hn).β.branchValues := fun h ↦ by
  -- `(pow hn).β` is `spherePow hn` by definition.
  simpa using FiniteHolomorphicMap.branchValues_spherePow_subset hn h

end AnalyticBelyiPair

/-- **The map `z ↦ 4z(1 - z)` is a Belyi map.** The Riemann sphere with the map `z ↦ 4z(1 - z)`,
sending `∞` to `∞`, is an analytic Belyi pair of degree `2`. It is unramified over `0`, whose
preimages are `0` and `1`, and ramified of index `2` over `1`, at `1/2`, and over `∞`, at `∞`, so
its ramification partitions over `0`, `1` and `∞` are `[1, 1]`, `[2]` and `[2]`. The map is
`z ↦ (1 - T₂(1 - 2z)) / 2` for the Chebyshev polynomial `T₂ = 2x² - 1`. -/
-- The body is exposed so that the surface of the pair is `OnePoint ℂ` by definition.
@[expose]
def AnalyticBelyiPair.chebyshev : AnalyticBelyiPair.{0} where
  X := OnePoint ℂ
  β := .spherePolynomial RiemannSurface.natDegree_four_mul_X_mul_one_sub_X_pos
  branchValues_subset := by
    rw [RiemannSurface.branchValues_spherePolynomial_four_mul_X_mul_one_sub_X]
    simp

namespace AnalyticBelyiPair

/-- The Belyi map of `chebyshev` is the map `z ↦ 4z(1 - z)` of the sphere. -/
@[simp]
theorem coe_β_chebyshev : ⇑chebyshev.β = OnePoint.map fun z : ℂ ↦ 4 * z * (1 - z) :=
  (FiniteHolomorphicMap.coe_spherePolynomial _).trans
    RiemannSurface.onePointMap_eval_four_mul_X_mul_one_sub_X

/-- The Belyi map `z ↦ 4z(1 - z)` has degree `2`. -/
theorem degree_β_chebyshev : degree chebyshev.β = 2 :=
  -- The surface of `chebyshev` is `OnePoint ℂ` by definition, so `coe_β_chebyshev` applies.
  (congrArg degree coe_β_chebyshev).trans degree_onePointMap_four_mul_mul_one_sub

/-- The branch values of `z ↦ 4z(1 - z)` are exactly `1` and `∞`: it is unramified over `0`. -/
@[simp]
theorem branchValues_β_chebyshev : chebyshev.β.branchValues = {((1 : ℂ) : OnePoint ℂ), ∞} :=
  -- `chebyshev.β` is the polynomial map of `4X(1 - X)` by definition.
  RiemannSurface.branchValues_spherePolynomial_four_mul_X_mul_one_sub_X

end AnalyticBelyiPair

/-! ### Isomorphisms of analytic Belyi pairs -/

open scoped ContDiff in
/-- An **isomorphism of analytic Belyi pairs** `P ≅ Q`: a biholomorphism of the Riemann surfaces
`P.X ≃ Q.X` lying over the Riemann sphere, that is, carrying the Belyi map of `Q` back to the
Belyi map of `P`. -/
structure AnalyticBelyiPair.Iso (P Q : AnalyticBelyiPair.{u}) : Type u where
  /-- The underlying biholomorphism of Riemann surfaces. -/
  toDiffeomorph : P.X ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ Q.X
  /-- The biholomorphism lies over the Riemann sphere. -/
  β_toDiffeomorph : ∀ x, Q.β (toDiffeomorph x) = P.β x

namespace AnalyticBelyiPair.Iso

variable {P Q R : AnalyticBelyiPair.{u}}

instance : EquivLike (P.Iso Q) P.X Q.X where
  coe e := e.toDiffeomorph
  inv e := e.toDiffeomorph.symm
  left_inv e := e.toDiffeomorph.symm_apply_apply
  right_inv e := e.toDiffeomorph.apply_symm_apply
  coe_injective' e e' h _ := by
    obtain ⟨f, _⟩ := e
    obtain ⟨f', _⟩ := e'
    congr
    exact Diffeomorph.coeFn_injective h

@[simp]
theorem coe_toDiffeomorph (e : P.Iso Q) : ⇑e.toDiffeomorph = e :=
  (rfl)

@[ext]
theorem ext {e e' : P.Iso Q} (h : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

/-- An isomorphism of analytic Belyi pairs lies over the Riemann sphere. -/
@[simp]
theorem β_apply (e : P.Iso Q) (x : P.X) : Q.β (e x) = P.β x :=
  e.β_toDiffeomorph x

/-- An isomorphism of analytic Belyi pairs lies over the Riemann sphere. -/
theorem β_comp (e : P.Iso Q) : Q.β ∘ e = P.β :=
  funext e.β_apply

/-- The identity isomorphism of an analytic Belyi pair. -/
@[refl]
protected def refl (P : AnalyticBelyiPair.{u}) : P.Iso P where
  toDiffeomorph := .refl _ _ _
  β_toDiffeomorph _ := rfl

/-- The inverse of an isomorphism of analytic Belyi pairs. -/
@[symm]
protected def symm (e : P.Iso Q) : Q.Iso P where
  toDiffeomorph := e.toDiffeomorph.symm
  β_toDiffeomorph y := by
    rw [← e.β_toDiffeomorph, Diffeomorph.apply_symm_apply]

/-- The composite of two isomorphisms of analytic Belyi pairs. -/
@[trans]
protected def trans (e : P.Iso Q) (e' : Q.Iso R) : P.Iso R where
  toDiffeomorph := e.toDiffeomorph.trans e'.toDiffeomorph
  β_toDiffeomorph x := by
    simp

@[simp]
theorem refl_apply (x : P.X) : Iso.refl P x = x :=
  (rfl)

@[simp]
theorem trans_apply (e : P.Iso Q) (e' : Q.Iso R) (x : P.X) : e.trans e' x = e' (e x) :=
  (rfl)

@[simp]
theorem symm_apply_apply (e : P.Iso Q) (x : P.X) : e.symm (e x) = x :=
  e.toDiffeomorph.symm_apply_apply x

@[simp]
theorem apply_symm_apply (e : P.Iso Q) (y : Q.X) : e (e.symm y) = y :=
  e.toDiffeomorph.apply_symm_apply y

@[simp]
theorem symm_symm (e : P.Iso Q) : e.symm.symm = e :=
  ext fun _ ↦ rfl

theorem trans_assoc (e : P.Iso Q) (e' : Q.Iso R) {S : AnalyticBelyiPair.{u}} (e'' : R.Iso S) :
    (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  ext fun _ ↦ by simp

@[simp]
theorem trans_refl (e : P.Iso Q) : e.trans (.refl Q) = e :=
  ext fun _ ↦ by simp

@[simp]
theorem refl_trans (e : P.Iso Q) : (Iso.refl P).trans e = e :=
  ext fun _ ↦ by simp

@[simp]
theorem self_trans_symm (e : P.Iso Q) : e.trans e.symm = .refl P :=
  ext fun _ ↦ by simp

@[simp]
theorem symm_trans_self (e : P.Iso Q) : e.symm.trans e = .refl Q :=
  ext fun _ ↦ by simp

/-- The homeomorphism of Riemann surfaces underlying an isomorphism of analytic Belyi pairs. -/
def toHomeomorph (e : P.Iso Q) : P.X ≃ₜ Q.X :=
  e.toDiffeomorph.toHomeomorph

@[simp]
theorem coe_toHomeomorph (e : P.Iso Q) : ⇑e.toHomeomorph = e :=
  (rfl)

/-- **A homeomorphism over the sphere is an isomorphism of analytic Belyi pairs**: it is
holomorphic by `TauCeti.AnalyticBelyiPair.mdifferentiable_of_β`, hence so is its inverse. -/
def ofHomeomorph (e : P.X ≃ₜ Q.X) (he : ∀ x, Q.β (e x) = P.β x) : P.Iso Q where
  toDiffeomorph :=
    have hf := mdifferentiable_of_β e.continuous he
    { toEquiv := (e.isHomeomorph.homeomorph e).toEquiv
      contMDiff_toFun := hf.contMDiff
      contMDiff_invFun := (e.isHomeomorph.mdifferentiable_symm hf).contMDiff }
  β_toDiffeomorph := he

@[simp]
theorem coe_ofHomeomorph (e : P.X ≃ₜ Q.X) (he : ∀ x, Q.β (e x) = P.β x) :
    ⇑(ofHomeomorph e he) = e :=
  (rfl)

/-- The isomorphism of covers of `ℂ ∖ {0, 1}` underlying an isomorphism of analytic Belyi pairs:
its restriction to the points over the thrice-punctured sphere, which commutes with the restricted
Belyi maps (`TauCeti.AnalyticBelyiPair.Iso.restrict_restrict`). -/
def restrict (e : P.Iso Q) : P.β ⁻¹' range toOnePoint ≃ₜ Q.β ⁻¹' range toOnePoint :=
  e.toHomeomorph.subtype fun x ↦ by simp

@[simp]
theorem coe_restrict_apply (e : P.Iso Q) (x : P.β ⁻¹' range toOnePoint) :
    (e.restrict x : Q.X) = e x :=
  (rfl)

/-- The restriction of an isomorphism of analytic Belyi pairs is a map of covers over
`ℂ ∖ {0, 1}`. -/
@[simp]
theorem restrict_restrict (e : P.Iso Q) (x : P.β ⁻¹' range toOnePoint) :
    Q.restrict (e.restrict x) = P.restrict x := by
  apply isOpenEmbedding_toOnePoint.injective
  simp only [toOnePoint_apply, coe_restrict_apply, AnalyticBelyiPair.coe_restrict_apply, β_apply]

/-- The restriction of an isomorphism of analytic Belyi pairs is a map of covers over
`ℂ ∖ {0, 1}`. -/
theorem restrict_comp_restrict (e : P.Iso Q) : Q.restrict ∘ e.restrict = P.restrict :=
  funext e.restrict_restrict

/-- **Isomorphic analytic Belyi pairs have the same degree.** -/
theorem degree_eq (e : P.Iso Q) : degree P.β = degree Q.β := by
  rw [← P.ncard_restrict_preimage_singleton basePt, ← Q.ncard_restrict_preimage_singleton basePt,
    ← e.restrict_comp_restrict, preimage_comp, ncard_preimage_of_injective_subset_range
      e.restrict.injective (by simp [e.restrict.surjective.range_eq])]

/-- An isomorphism of analytic Belyi pairs is an isomorphism of their underlying topological
branched covers. -/
def toTopBranchedCover (e : P.Iso Q) {n : ℕ} (hP : degree P.β = n)
    (hQ : degree Q.β = n) :
    TopBranchedCover.Iso (P.toTopBranchedCover hP) (Q.toTopBranchedCover hQ) where
  toHomeomorph := e.toHomeomorph
  π_apply := e.β_apply

/-- The homeomorphism underlying the induced isomorphism of topological branched covers is the
homeomorphism underlying the isomorphism of analytic Belyi pairs. -/
@[simp]
theorem toTopBranchedCover_toHomeomorph (e : P.Iso Q) {n : ℕ} (hP : degree P.β = n)
    (hQ : degree Q.β = n) :
    (e.toTopBranchedCover hP hQ).toHomeomorph = e.toHomeomorph := (rfl)

/-- **Isomorphic analytic Belyi pairs have isomorphic monodromy triples**, whatever the
numberings of the fibres over `1/2`. -/
theorem isoClass_monodromyTriple_eq {n : ℕ} (e : P.Iso Q) (ν : P.restrict ⁻¹' {basePt} ≃ Fin n)
    (ν' : Q.restrict ⁻¹' {basePt} ≃ Fin n) :
    PermutationTriple.IsoClass.mk (Q.isCoveringMap_restrict.monodromyTriple ν') =
      PermutationTriple.IsoClass.mk (P.isCoveringMap_restrict.monodromyTriple ν) :=
  P.isCoveringMap_restrict.isoClass_monodromyTriple_eq_of_homeomorph ν
    Q.isCoveringMap_restrict ν' e.restrict e.restrict_comp_restrict

/-! ### Rigidity and finiteness of isomorphisms -/

/-- **An isomorphism of analytic Belyi pairs is determined by the image of one point** over
`ℂ ∖ {0, 1}`. -/
theorem eq_of_apply_eq {e e' : P.Iso Q} (x : P.β ⁻¹' range toOnePoint) (h : e x = e' x) :
    e = e' := by
  -- The restrictions are lifts of the same map through the connected cover attached to `Q`, and
  -- the points over `ℂ ∖ {0, 1}` are dense in `P.X`.
  have hres : ⇑e.restrict = e'.restrict :=
    Q.isCoveringMap_restrict.eq_of_comp_eq e.restrict.continuous e'.restrict.continuous
      (by rw [e.restrict_comp_restrict, e'.restrict_comp_restrict]) x (Subtype.ext h)
  have hQ := e.degree_eq.symm
  -- The unbranched part of `P.toTopBranchedCover rfl` is `P.β ⁻¹' range toOnePoint` by
  -- definition, since its projection coerces to `P.β`; so `hres` applies to its points.
  have h : (e.toTopBranchedCover rfl hQ).restrict = (e'.toTopBranchedCover rfl hQ).restrict :=
    Homeomorph.ext fun y ↦ Subtype.ext <| by
      simp only [TopBranchedCover.Iso.coe_restrict_apply, toTopBranchedCover_toHomeomorph]
      exact congrArg Subtype.val (congrFun hres y)
  have h' := congrArg TopBranchedCover.Iso.toHomeomorph (TopBranchedCover.Iso.restrict_injective h)
  rw [toTopBranchedCover_toHomeomorph, toTopBranchedCover_toHomeomorph] at h'
  exact ext fun y ↦ DFunLike.congr_fun h' y

/-- Evaluation at a point of the fibre over `1/2` embeds the isomorphisms `P ≅ Q` into the fibre
of `Q` over `1/2`. -/
private theorem exists_injective_restrict_preimage_basePt :
    ∃ f : P.Iso Q → Q.restrict ⁻¹' {basePt}, Injective f := by
  obtain ⟨x, hx⟩ : (P.restrict ⁻¹' {basePt}).Nonempty := by
    rw [← ncard_pos (P.finite_restrict_preimage_singleton basePt),
      P.ncard_restrict_preimage_singleton]
    exact degree_pos (f := P.β)
  refine ⟨fun e ↦ ⟨e.restrict x, by simpa using hx⟩, fun e e' h ↦ eq_of_apply_eq x ?_⟩
  simpa using congrArg (fun y : Q.restrict ⁻¹' {basePt} ↦ (y : Q.X)) h

/-- There are only finitely many isomorphisms between two analytic Belyi pairs. -/
instance : Finite (P.Iso Q) :=
  have := (Q.finite_restrict_preimage_singleton basePt).to_subtype
  let ⟨_, hf⟩ := exists_injective_restrict_preimage_basePt (P := P) (Q := Q)
  .of_injective _ hf

/-- **There are at most as many isomorphisms between two analytic Belyi pairs as the degree.** -/
theorem natCard_le_degree : Nat.card (P.Iso Q) ≤ degree Q.β := by
  have := (Q.finite_restrict_preimage_singleton basePt).to_subtype
  obtain ⟨f, hf⟩ := exists_injective_restrict_preimage_basePt (P := P) (Q := Q)
  rw [← Q.ncard_restrict_preimage_singleton basePt, ← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective f hf

/-! ### The automorphism group -/

/-- **The automorphism group of an analytic Belyi pair**: its automorphisms form a group under
composition, `e * e'` being `e'` followed by `e`. It is finite, with order dividing the degree
(`TauCeti.AnalyticBelyiPair.Iso.natCard_dvd_degree`). -/
instance : Group (P.Iso P) where
  mul e e' := e'.trans e
  one := .refl P
  inv := Iso.symm
  mul_assoc e e' e'' := (trans_assoc e'' e' e).symm
  one_mul := trans_refl
  mul_one := refl_trans
  inv_mul_cancel := self_trans_symm

theorem one_def : (1 : P.Iso P) = .refl P :=
  (rfl)

theorem mul_def (e e' : P.Iso P) : e * e' = e'.trans e :=
  (rfl)

theorem inv_def (e : P.Iso P) : e⁻¹ = e.symm :=
  (rfl)

@[simp]
theorem one_apply (x : P.X) : (1 : P.Iso P) x = x :=
  (rfl)

@[simp]
theorem mul_apply (e e' : P.Iso P) (x : P.X) : (e * e') x = e (e' x) :=
  (rfl)

@[simp]
theorem inv_apply (e : P.Iso P) (x : P.X) : e⁻¹ x = e.symm x :=
  (rfl)

/-- Automorphisms of an analytic Belyi pair act on every fibre of its restricted cover by
evaluation. -/
instance instMulActionRestrictFiber (P : AnalyticBelyiPair.{u}) (b : ThricePuncturedSphere) :
    MulAction (P.Iso P) (P.restrict ⁻¹' {b}) where
  smul e x := ⟨e.restrict x, by simpa only [Set.mem_preimage, Set.mem_singleton_iff,
    restrict_restrict] using x.2⟩
  one_smul x := by
    apply Subtype.ext
    apply Subtype.ext
    exact (coe_restrict_apply (1 : P.Iso P) x).trans (one_apply (P := P) (x : P.X))
  mul_smul e e' x := by
    apply Subtype.ext
    apply Subtype.ext
    exact (coe_restrict_apply (e * e') x).trans <| (mul_apply e e' x).trans <|
      (congrArg e (coe_restrict_apply e' x).symm).trans (coe_restrict_apply e (e'.restrict x)).symm

/-- On underlying points, the action on a fibre of the restricted cover is evaluation of the
automorphism. -/
@[simp]
theorem coe_smul (b : ThricePuncturedSphere) (e : P.Iso P) (x : P.restrict ⁻¹' {b}) :
    ((e • x : P.restrict ⁻¹' {b}) : P.X) = e x :=
  coe_restrict_apply e x

/-- The action of the automorphism group of an analytic Belyi pair on every fibre of its
restricted cover is free. -/
instance instIsCancelSMulRestrictFiber (P : AnalyticBelyiPair.{u}) (b : ThricePuncturedSphere) :
    IsCancelSMul (P.Iso P) (P.restrict ⁻¹' {b}) where
  right_cancel' e e' x h := eq_of_apply_eq x <| by
    simpa only [coe_smul] using congrArg (fun y : P.restrict ⁻¹' {b} ↦ (y : P.X)) h

/-- **The order of the automorphism group of an analytic Belyi pair divides its degree.** -/
theorem natCard_dvd_degree : Nat.card (P.Iso P) ∣ degree P.β := by
  have := (P.finite_restrict_preimage_singleton basePt).to_subtype
  rw [← P.ncard_restrict_preimage_singleton basePt, ← Nat.card_coe_set_eq]
  exact MulAction.natCard_dvd_natCard_of_isCancelSMul

end AnalyticBelyiPair.Iso

/-! ### Automorphisms, deck transformations and the monodromy triple -/

namespace AnalyticBelyiPair

section Deck

variable (P : AnalyticBelyiPair.{u})

/-- **The automorphisms of an analytic Belyi pair are the deck transformations of its Belyi
map**, the homeomorphisms of the surface over the sphere: these are automatically biholomorphic
(`TauCeti.AnalyticBelyiPair.Iso.ofHomeomorph`). -/
def isoMulEquivDeck : P.Iso P ≃* deck P.β where
  toFun e := ⟨e.toHomeomorph, deck.mem_iff.2 e.β_comp⟩
  invFun φ := .ofHomeomorph φ.1 (congrFun φ.2)
  left_inv e := Iso.ext fun _ ↦ by simp
  right_inv φ := Subtype.ext <| Homeomorph.ext fun _ ↦ by simp
  map_mul' _ _ := rfl

/-- The deck transformation of an automorphism of a pair is the automorphism. -/
@[simp]
theorem coe_isoMulEquivDeck_apply (e : P.Iso P) : ⇑(P.isoMulEquivDeck e : P.X ≃ₜ P.X) = e :=
  e.coe_toHomeomorph

/-- The automorphism of a pair given by a deck transformation of its Belyi map is the deck
transformation. -/
@[simp]
theorem coe_isoMulEquivDeck_symm_apply (φ : deck P.β) :
    ⇑(P.isoMulEquivDeck.symm φ) = (φ : P.X ≃ₜ P.X) :=
  Iso.coe_ofHomeomorph _ _

end Deck

section AutomorphismGroup

variable (P : AnalyticBelyiPair.{u}) {n : ℕ} (ν : P.restrict ⁻¹' {basePt} ≃ Fin n)

/-- **The automorphism group of an analytic Belyi pair is the automorphism group of its monodromy
triple**, for any numbering `ν` of the fibre over `1/2`. An automorphism goes to the permutation it
induces on the labels (`TauCeti.AnalyticBelyiPair.coe_isoMulEquivAutomorphismGroup_apply`). It is
the composite of three identifications: automorphisms of the pair are the deck transformations of
the Belyi map, these restrict to the deck transformations of the cover of `ℂ ∖ {0, 1}` attached to
the pair (`TauCeti.TopBranchedCover.deckMulEquivDeckRestrict`), and those are the automorphisms of
its monodromy triple (`IsCoveringMap.deckMulEquivAutomorphismGroup`). -/
noncomputable def isoMulEquivAutomorphismGroup :
    P.Iso P ≃* (P.isCoveringMap_restrict.monodromyTriple ν).automorphismGroup :=
  P.isoMulEquivDeck.trans <|
    (Deck.conjMulEquiv (Homeomorph.refl P.X) (P.toTopBranchedCover_π_apply rfl)).trans <|
    (P.toTopBranchedCover rfl).deckMulEquivDeckRestrict.trans <|
    (MulEquiv.subgroupCongr (congrArg deck (P.restrict_toTopBranchedCover rfl))).trans <|
      P.isCoveringMap_restrict.deckMulEquivAutomorphismGroup ν

/-- The automorphism of the monodromy triple attached to an automorphism `e` of a pair sends the
label `i` to the label of the image under `e` of the point labelled `i`. -/
@[simp]
theorem coe_isoMulEquivAutomorphismGroup_apply (e : P.Iso P) (i : Fin n) :
    (P.isoMulEquivAutomorphismGroup ν e : Equiv.Perm (Fin n)) i = ν (e • ν.symm i) := by
  refine (IsCoveringMap.coe_deckMulEquivAutomorphismGroup_apply _ _ _ i).trans
    (congrArg ν (Subtype.ext (Subtype.ext ?_)))
  -- Evaluate the composite one identification at a time.
  exact (congrArg Subtype.val (deck.fiber_smul_coe _ (ν.symm i))).trans <|
    (TopBranchedCover.coe_deckMulEquivDeckRestrict_apply _ _ _).trans <|
    (Deck.conjMulEquiv_apply_coe _ _ _ _).trans <|
      (congrFun (P.coe_isoMulEquivDeck_apply e) _).trans (Iso.coe_smul _ e _).symm

/-- The automorphism of a pair attached to an automorphism `τ` of its monodromy triple sends the
point labelled `i` to the point labelled `τ i`. -/
@[simp]
theorem isoMulEquivAutomorphismGroup_symm_smul
    (τ : (P.isCoveringMap_restrict.monodromyTriple ν).automorphismGroup) (i : Fin n) :
    (P.isoMulEquivAutomorphismGroup ν).symm τ • ν.symm i =
      ν.symm ((τ : Equiv.Perm (Fin n)) i) := by
  rw [← ν.symm_apply_apply ((P.isoMulEquivAutomorphismGroup ν).symm τ • ν.symm i),
    ← coe_isoMulEquivAutomorphismGroup_apply, MulEquiv.apply_symm_apply]

variable {P} in
/-- **The monodromy triple of an analytic Belyi pair is regular exactly when the pair has as many
automorphisms as its degree**, the number `n` of points of the fibre over `1/2`. -/
theorem isRegular_monodromyTriple_iff_natCard_iso :
    (P.isCoveringMap_restrict.monodromyTriple ν).IsRegular ↔ Nat.card (P.Iso P) = n := by
  rw [PermutationTriple.isRegular_iff_card_automorphismGroup,
    and_iff_right (P.isCoveringMap_restrict.isConnected_monodromyTriple ν),
    Nat.card_congr (P.isoMulEquivAutomorphismGroup ν).toEquiv]

end AutomorphismGroup

end AnalyticBelyiPair

/-! ### Isomorphism classes of analytic Belyi pairs -/

namespace AnalyticBelyiPair

/-- Isomorphism of analytic Belyi pairs of degree `n`, as an equivalence relation. -/
def isoSetoid (n : ℕ) : Setoid {P : AnalyticBelyiPair.{u} // degree P.β = n} where
  r P Q := Nonempty (P.1.Iso Q.1)
  iseqv := ⟨fun P ↦ ⟨Iso.refl P.1⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ ↦ ⟨e.trans e'⟩⟩

theorem isoSetoid_r {n : ℕ} {P Q : {P : AnalyticBelyiPair.{u} // degree P.β = n}} :
    (isoSetoid n).r P Q ↔ Nonempty (P.1.Iso Q.1) :=
  Iff.rfl

/-- **The permutation triple of an isomorphism class of analytic Belyi pairs** of degree `n`: the
isomorphism class of the monodromy triple of any representative, for any numbering of its fibre
over `1/2` (`TauCeti.AnalyticBelyiPair.toIsoClass_mk`). It is well defined because isomorphic
pairs have isomorphic monodromy triples
(`TauCeti.AnalyticBelyiPair.Iso.isoClass_monodromyTriple_eq`). -/
def toIsoClass (n : ℕ) : Quotient (isoSetoid.{u} n) → PermutationTriple.IsoClass n :=
  Quotient.lift
    (fun P ↦ .mk (P.1.isCoveringMap_restrict.monodromyTriple
      ((P.1.nonempty_restrict_preimage_singleton_equiv basePt).some.trans (finCongr P.2))))
    fun _ _ ⟨e⟩ ↦ (e.isoClass_monodromyTriple_eq _ _).symm

/-- **The topological branched cover of an isomorphism class of analytic Belyi pairs.** This is
the analytic-to-topological map in the classification of Belyi pairs: it forgets the complex
structure and retains the same map to the sphere. -/
def toTopBranchedCoverIsoClass (n : ℕ) :
    Quotient (isoSetoid.{u} n) → TopBranchedCover.IsoClass n :=
  Quotient.lift
    (fun P ↦ TopBranchedCover.IsoClass.mk (P.1.toTopBranchedCover P.2))
    fun _ _ ⟨e⟩ ↦ TopBranchedCover.IsoClass.mk_eq_mk_iff.2
      ⟨e.toTopBranchedCover _ _⟩

/-- The topological branched-cover class of a pair is represented by its underlying topological
branched cover. -/
@[simp]
theorem toTopBranchedCoverIsoClass_mk {n : ℕ}
    (P : {P : AnalyticBelyiPair.{u} // degree P.β = n}) :
    toTopBranchedCoverIsoClass n ⟦P⟧ =
      TopBranchedCover.IsoClass.mk (P.1.toTopBranchedCover P.2) := (rfl)

/-- **Analytic Belyi pairs are determined by their underlying topological branched covers**: two
analytic Belyi pairs of degree `n` whose topological branched covers are isomorphic are isomorphic,
since a homeomorphism over the sphere is holomorphic (`TauCeti.AnalyticBelyiPair.Iso.ofHomeomorph`).
-/
theorem toTopBranchedCoverIsoClass_injective (n : ℕ) :
    Injective (toTopBranchedCoverIsoClass.{u} n) := by
  rintro ⟨P⟩ ⟨Q⟩ h
  obtain ⟨e⟩ := TopBranchedCover.IsoClass.mk_eq_mk_iff.1 h
  exact Quotient.sound ⟨.ofHomeomorph e.toHomeomorph e.π_apply⟩

/-- The permutation triple of the class of an analytic Belyi pair of degree `n` is the class of
its monodromy triple, for any numbering of the fibre over `1/2`. -/
theorem toIsoClass_mk {n : ℕ} (P : {P : AnalyticBelyiPair.{u} // degree P.β = n})
    (ν : P.1.restrict ⁻¹' {basePt} ≃ Fin n) :
    toIsoClass n ⟦P⟧ = .mk (P.1.isCoveringMap_restrict.monodromyTriple ν) := by
  rw [toIsoClass, Quotient.lift_mk]
  exact P.1.isCoveringMap_restrict.isoClass_monodromyTriple_eq _ _

end AnalyticBelyiPair

/-! ### Morphisms of analytic Belyi pairs -/

/-- A **morphism of analytic Belyi pairs** `P → Q`: a holomorphic map of Riemann surfaces
`P.X → Q.X` lying over the Riemann sphere, that is, carrying the Belyi map of `Q` back to the
Belyi map of `P`. Every continuous map over the sphere is one
(`TauCeti.AnalyticBelyiPair.Hom.ofContinuous`). -/
structure AnalyticBelyiPair.Hom (P : AnalyticBelyiPair.{u}) (Q : AnalyticBelyiPair.{v}) :
    Type (max u v) where
  /-- The underlying map of Riemann surfaces. -/
  toFun : P.X → Q.X
  /-- The map is holomorphic. -/
  holomorphic : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) toFun
  /-- The map lies over the Riemann sphere. -/
  β_toFun : ∀ x, Q.β (toFun x) = P.β x

namespace AnalyticBelyiPair.Hom

variable {P : AnalyticBelyiPair.{u}} {Q : AnalyticBelyiPair.{v}} {R : AnalyticBelyiPair.{w}}

instance : FunLike (P.Hom Q) P.X Q.X where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr

@[simp]
theorem toFun_eq_coe (f : P.Hom Q) : f.toFun = f :=
  (rfl)

@[ext]
theorem ext {f g : P.Hom Q} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- A morphism of analytic Belyi pairs lies over the Riemann sphere. -/
@[simp]
theorem β_apply (f : P.Hom Q) (x : P.X) : Q.β (f x) = P.β x :=
  f.β_toFun x

/-- A morphism of analytic Belyi pairs lies over the Riemann sphere. -/
theorem β_comp (f : P.Hom Q) : Q.β ∘ f = P.β :=
  funext f.β_apply

/-- A morphism of analytic Belyi pairs is holomorphic. -/
protected theorem mdifferentiable (f : P.Hom Q) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f :=
  f.holomorphic

/-- A morphism of analytic Belyi pairs is continuous. -/
@[continuity, fun_prop]
protected theorem continuous (f : P.Hom Q) : Continuous f :=
  f.holomorphic.continuous

/-- **A continuous map over the sphere is a morphism of analytic Belyi pairs**: it is holomorphic
by `TauCeti.AnalyticBelyiPair.mdifferentiable_of_β`. -/
def ofContinuous {f : P.X → Q.X} (hf : Continuous f) (hβ : ∀ x, Q.β (f x) = P.β x) :
    P.Hom Q where
  toFun := f
  holomorphic := mdifferentiable_of_β hf hβ
  β_toFun := hβ

@[simp]
theorem coe_ofContinuous {f : P.X → Q.X} (hf : Continuous f) (hβ : ∀ x, Q.β (f x) = P.β x) :
    ⇑(ofContinuous hf hβ) = f :=
  (rfl)

/-- The identity morphism of an analytic Belyi pair. -/
protected def id (P : AnalyticBelyiPair.{u}) : P.Hom P where
  toFun := id
  holomorphic := mdifferentiable_id
  β_toFun _ := rfl

@[simp]
theorem coe_id : ⇑(Hom.id P) = id :=
  (rfl)

/-- The composite of two morphisms of analytic Belyi pairs. -/
def comp (g : Q.Hom R) (f : P.Hom Q) : P.Hom R where
  toFun := g ∘ f
  holomorphic := g.holomorphic.comp f.holomorphic
  β_toFun x := by simp

@[simp]
theorem coe_comp (g : Q.Hom R) (f : P.Hom Q) : ⇑(g.comp f) = g ∘ f :=
  (rfl)

theorem comp_apply (g : Q.Hom R) (f : P.Hom Q) (x : P.X) : g.comp f x = g (f x) :=
  (rfl)

@[simp]
theorem comp_id (f : P.Hom Q) : f.comp (.id P) = f :=
  (rfl)

@[simp]
theorem id_comp (f : P.Hom Q) : (Hom.id Q).comp f = f :=
  (rfl)

theorem comp_assoc {S : AnalyticBelyiPair.{w'}} (h : R.Hom S) (g : Q.Hom R) (f : P.Hom Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  (rfl)

/-- The finite holomorphic map underlying a morphism of analytic Belyi pairs: it takes two
distinct values because the Belyi map of the source does. -/
def toFiniteHolomorphicMap (f : P.Hom Q) : FiniteHolomorphicMap P.X Q.X :=
  .ofMDifferentiable f.holomorphic <|
    let ⟨x, x', h⟩ := P.β.nonconstant
    ⟨x, x', fun hf ↦ h (by rw [← f.β_apply x, ← f.β_apply x']; exact congrArg Q.β hf)⟩

@[simp]
theorem coe_toFiniteHolomorphicMap (f : P.Hom Q) : ⇑f.toFiniteHolomorphicMap = f :=
  FiniteHolomorphicMap.coe_ofMDifferentiable _ _

/-- **A morphism of analytic Belyi pairs is surjective.** -/
theorem surjective (f : P.Hom Q) : Surjective f := by
  simpa using f.toFiniteHolomorphicMap.surjective

/-- **Degrees multiply along a morphism of analytic Belyi pairs**: the degree of the Belyi map of
the source is the degree of the Belyi map of the target times the degree of the morphism. -/
theorem degree_β_eq_mul_degree (f : P.Hom Q) : degree P.β = degree Q.β * degree f := by
  have h := degree_comp Q.β f.toFiniteHolomorphicMap
  rwa [FiniteHolomorphicMap.coe_comp, coe_toFiniteHolomorphicMap, f.β_comp] at h

/-- The degree of the target of a morphism of analytic Belyi pairs divides the degree of the
source. -/
theorem degree_β_dvd (f : P.Hom Q) : degree Q.β ∣ degree P.β :=
  Dvd.intro _ f.degree_β_eq_mul_degree.symm

/-- A morphism of analytic Belyi pairs has degree one exactly when its source and target have the
same degree. -/
theorem degree_eq_one_iff (f : P.Hom Q) : degree f = 1 ↔ degree P.β = degree Q.β := by
  rw [f.degree_β_eq_mul_degree, Nat.mul_eq_left (degree_pos Q.β).ne']

/-- **A morphism between analytic Belyi pairs of the same degree is an isomorphism**: it has
degree one (`TauCeti.AnalyticBelyiPair.Hom.degree_eq_one_iff`), so it is a biholomorphism. -/
def toIso {P Q : AnalyticBelyiPair.{u}} (f : P.Hom Q) (h : degree P.β = degree Q.β) :
    P.Iso Q where
  toDiffeomorph := biholomorphOfDegreeEqOne f.toFiniteHolomorphicMap <| by
    rw [coe_toFiniteHolomorphicMap, f.degree_eq_one_iff]
    exact h
  β_toDiffeomorph x := by
    rw [biholomorphOfDegreeEqOne_toFun, coe_toFiniteHolomorphicMap, f.β_apply]

@[simp]
theorem coe_toIso {P Q : AnalyticBelyiPair.{u}} (f : P.Hom Q) (h : degree P.β = degree Q.β) :
    ⇑(f.toIso h) = f :=
  (biholomorphOfDegreeEqOne_toFun _ _).trans f.coe_toFiniteHolomorphicMap

/-- The map of covers of `ℂ ∖ {0, 1}` underlying a morphism of analytic Belyi pairs: its
restriction to the points over the thrice-punctured sphere, which commutes with the restricted
Belyi maps (`TauCeti.AnalyticBelyiPair.Hom.restrict_restrict`). -/
def restrict (f : P.Hom Q) : C(P.β ⁻¹' range toOnePoint, Q.β ⁻¹' range toOnePoint) :=
  have hf : MapsTo f (P.β ⁻¹' range toOnePoint) (Q.β ⁻¹' range toOnePoint) := fun x hx ↦ by
    rwa [mem_preimage, f.β_apply]
  ⟨hf.restrict f _ _, Continuous.restrict hf f.continuous⟩

@[simp]
theorem coe_restrict_apply (f : P.Hom Q) (x : P.β ⁻¹' range toOnePoint) :
    (f.restrict x : Q.X) = f x :=
  (rfl)

/-- The restriction of a morphism of analytic Belyi pairs is a map of covers over
`ℂ ∖ {0, 1}`. -/
@[simp]
theorem restrict_restrict (f : P.Hom Q) (x : P.β ⁻¹' range toOnePoint) :
    Q.restrict (f.restrict x) = P.restrict x := by
  apply isOpenEmbedding_toOnePoint.injective
  simp only [toOnePoint_apply, AnalyticBelyiPair.coe_restrict_apply, coe_restrict_apply, β_apply]

/-- The restriction of a morphism of analytic Belyi pairs is a map of covers over
`ℂ ∖ {0, 1}`. -/
theorem restrict_comp_restrict (f : P.Hom Q) : Q.restrict ∘ f.restrict = P.restrict :=
  funext f.restrict_restrict

/-- **A morphism of analytic Belyi pairs intertwines the monodromy triples.** Read through
numberings `ν` and `ν'` of the fibres over `1/2`, the map a morphism `f : P → Q` induces between
these fibres carries `σ0`, `σ1` and `σinf` of the monodromy triple of `P` to those of `Q`. -/
theorem semiconj_component_monodromyTriple {n m : ℕ} (f : P.Hom Q)
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) (ν' : Q.restrict ⁻¹' {basePt} ≃ Fin m) (j : Fin 3) :
    Semiconj (ν' ∘ fiberMap f.restrict f.restrict_comp_restrict basePt ∘ ν.symm)
      ((P.isCoveringMap_restrict.monodromyTriple ν).component j)
      ((Q.isCoveringMap_restrict.monodromyTriple ν').component j) :=
  P.isCoveringMap_restrict.semiconj_component_monodromyTriple ν Q.isCoveringMap_restrict ν'
    f.restrict f.restrict_comp_restrict j

/-- **Morphisms into a pair of degree one are unique**: the Belyi map of the target is then
injective, and every morphism lies over it. -/
theorem subsingleton_of_degree_eq_one (hQ : degree Q.β = 1) : Subsingleton (P.Hom Q) := by
  have hinj : Injective Q.β := by
    simpa using (biholomorphOfDegreeEqOne Q.β hQ).injective
  exact ⟨fun f g ↦ ext fun x ↦ hinj (by rw [f.β_apply, g.β_apply])⟩

end AnalyticBelyiPair.Hom

namespace AnalyticBelyiPair.Iso

variable {P Q : AnalyticBelyiPair.{u}}

/-- The morphism of analytic Belyi pairs underlying an isomorphism. -/
def toHom (e : P.Iso Q) : P.Hom Q where
  toFun := e
  holomorphic := e.toDiffeomorph.mdifferentiable (by simp)
  β_toFun := e.β_apply

@[simp]
theorem coe_toHom (e : P.Iso Q) : ⇑e.toHom = e :=
  (rfl)

@[simp]
theorem toHom_refl (P : AnalyticBelyiPair.{u}) : (Iso.refl P).toHom = Hom.id P :=
  Hom.ext fun _ ↦ rfl

@[simp]
theorem toHom_trans {R : AnalyticBelyiPair.{u}} (e : P.Iso Q) (e' : Q.Iso R) :
    (e.trans e').toHom = e'.toHom.comp e.toHom :=
  Hom.ext fun _ ↦ rfl

end AnalyticBelyiPair.Iso

/-- The isomorphism given by a morphism between pairs of the same degree has that morphism as its
underlying morphism. -/
@[simp]
theorem AnalyticBelyiPair.Hom.toHom_toIso {P Q : AnalyticBelyiPair.{u}} (f : P.Hom Q)
    (h : degree P.β = degree Q.β) : (f.toIso h).toHom = f :=
  ext fun x ↦ by simp

/-- The isomorphism given by the morphism underlying an isomorphism is that isomorphism. -/
@[simp]
theorem AnalyticBelyiPair.Iso.toIso_toHom {P Q : AnalyticBelyiPair.{u}} (e : P.Iso Q)
    (h : degree P.β = degree Q.β) : e.toHom.toIso h = e :=
  ext fun x ↦ by simp

/-! ### The trivial pair and pairs of degree one -/

namespace AnalyticBelyiPair

/-- The Belyi map of an analytic Belyi pair, as its morphism to the trivial pair
`pow one_ne_zero`, the identity of the sphere. It is the unique such morphism, so the trivial pair
is terminal. -/
def homPowOne (P : AnalyticBelyiPair.{u}) : P.Hom (pow one_ne_zero) where
  toFun := P.β
  holomorphic := P.β.holomorphic
  β_toFun x := by
    simp only [coe_β_pow, pow_one]
    exact congrFun OnePoint.map_id _

@[simp]
theorem coe_homPowOne (P : AnalyticBelyiPair.{u}) : ⇑P.homPowOne = P.β :=
  (rfl)

/-- **The trivial pair is terminal**: the Belyi map is the unique morphism from an analytic Belyi
pair to the trivial pair, the identity of the sphere. -/
instance (P : AnalyticBelyiPair.{u}) : Unique (P.Hom (pow one_ne_zero)) where
  default := P.homPowOne
  uniq f :=
    have := Hom.subsingleton_of_degree_eq_one (P := P) (degree_β_pow one_ne_zero)
    Subsingleton.elim f _

/-- **Analytic Belyi pairs of degree one are isomorphic**: each Belyi map is then a biholomorphism
onto the sphere. -/
def isoOfDegreeEqOne {P Q : AnalyticBelyiPair.{u}} (hP : degree P.β = 1)
    (hQ : degree Q.β = 1) : P.Iso Q where
  toDiffeomorph := (biholomorphOfDegreeEqOne P.β hP).trans (biholomorphOfDegreeEqOne Q.β hQ).symm
  β_toDiffeomorph x := by
    have h := (biholomorphOfDegreeEqOne Q.β hQ).apply_symm_apply (P.β x)
    rw [biholomorphOfDegreeEqOne_toFun] at h
    simpa only [Diffeomorph.coe_trans, comp_apply, biholomorphOfDegreeEqOne_toFun] using h

/-- **An analytic Belyi pair has degree one exactly when it is trivial**, that is, isomorphic to
the identity of the sphere. -/
theorem degree_β_eq_one_iff_nonempty_iso {P : AnalyticBelyiPair.{0}} :
    degree P.β = 1 ↔ Nonempty (P.Iso (pow one_ne_zero)) :=
  ⟨fun h ↦ ⟨isoOfDegreeEqOne h (degree_β_pow one_ne_zero)⟩,
    fun ⟨e⟩ ↦ e.degree_eq.trans (degree_β_pow one_ne_zero)⟩

/-- There is at most one isomorphism class of analytic Belyi pairs of degree one. -/
instance : Subsingleton (Quotient (isoSetoid.{u} 1)) :=
  ⟨Quotient.ind₂ fun P Q ↦ Quotient.sound (isoSetoid_r.2 ⟨isoOfDegreeEqOne P.2 Q.2⟩)⟩

/-- The class of the trivial pair is the only isomorphism class of analytic Belyi pairs of degree
one. -/
instance : Unique (Quotient (isoSetoid.{0} 1)) where
  default := ⟦⟨pow one_ne_zero, degree_β_pow one_ne_zero⟩⟧
  uniq _ := Subsingleton.elim _ _

end AnalyticBelyiPair

end TauCeti
