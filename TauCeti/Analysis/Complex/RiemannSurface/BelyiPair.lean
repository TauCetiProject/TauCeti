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

An isomorphism of analytic Belyi pairs is a biholomorphism of their surfaces over the sphere
(`TauCeti.AnalyticBelyiPair.Iso`). It restricts to an isomorphism of the attached covers of
`ℂ ∖ {0, 1}`, so isomorphic pairs have the same degree and isomorphic monodromy triples, and the
permutation triple is a well-defined function of the isomorphism class of a pair of degree `n`
(`TauCeti.AnalyticBelyiPair.toIsoClass`). This is the map from analytic Belyi pairs to permutation
triples through which the analytic Riemann existence theorem for three-point covers compares the
two classifications.

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
* `TauCeti.AnalyticBelyiPair.Iso`: isomorphisms of analytic Belyi pairs, with
  `TauCeti.AnalyticBelyiPair.Iso.restrict` the isomorphism of the attached covers of `ℂ ∖ {0, 1}`.
* `TauCeti.AnalyticBelyiPair.Iso.degree_eq` and
  `TauCeti.AnalyticBelyiPair.Iso.isoClass_monodromyTriple_eq`: isomorphic pairs have the same
  degree and isomorphic monodromy triples.
* `TauCeti.AnalyticBelyiPair.isoSetoid`, `TauCeti.AnalyticBelyiPair.toIsoClass`: isomorphism of
  pairs of degree `n`, and the permutation triple of an isomorphism class of such pairs.
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

/-- The homeomorphism of Riemann surfaces underlying an isomorphism of analytic Belyi pairs. -/
def toHomeomorph (e : P.Iso Q) : P.X ≃ₜ Q.X :=
  e.toDiffeomorph.toHomeomorph

@[simp]
theorem coe_toHomeomorph (e : P.Iso Q) : ⇑e.toHomeomorph = e :=
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

/-- **Isomorphic analytic Belyi pairs have isomorphic monodromy triples**, whatever the
numberings of the fibres over `1/2`. -/
theorem isoClass_monodromyTriple_eq {n : ℕ} (e : P.Iso Q) (ν : P.restrict ⁻¹' {basePt} ≃ Fin n)
    (ν' : Q.restrict ⁻¹' {basePt} ≃ Fin n) :
    PermutationTriple.IsoClass.mk (Q.isCoveringMap_restrict.monodromyTriple ν') =
      PermutationTriple.IsoClass.mk (P.isCoveringMap_restrict.monodromyTriple ν) :=
  P.isCoveringMap_restrict.isoClass_monodromyTriple_eq_of_homeomorph ν
    Q.isCoveringMap_restrict ν' e.restrict e.restrict_comp_restrict

end AnalyticBelyiPair.Iso

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

/-- The permutation triple of the class of an analytic Belyi pair of degree `n` is the class of
its monodromy triple, for any numbering of the fibre over `1/2`. -/
theorem toIsoClass_mk {n : ℕ} (P : {P : AnalyticBelyiPair.{u} // degree P.β = n})
    (ν : P.1.restrict ⁻¹' {basePt} ≃ Fin n) :
    toIsoClass n ⟦P⟧ = .mk (P.1.isCoveringMap_restrict.monodromyTriple ν) := by
  rw [toIsoClass, Quotient.lift_mk]
  exact P.1.isCoveringMap_restrict.isoClass_monodromyTriple_eq _ _

end AnalyticBelyiPair

end TauCeti
