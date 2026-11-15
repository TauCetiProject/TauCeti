/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.EulerClass

/-!
# Thom pairs and Euler classes under fibrewise isomorphisms

Let `E' → B'` and `E → B` be real vector bundles, `g : B' → B` a continuous map, and
`φ b' : E'_{b'} ≃ E_{g b'}` a family of continuous linear equivalences of fibres whose total-space
map `v ↦ (g (π v), φ (π v) v)` is continuous: a bundle map covering `g` which is an isomorphism on
every fibre. Being linear and injective on the fibres, it carries nonzero vectors to nonzero
vectors, so it is a map of Thom pairs `(E', E'₀) ⟶ (E, E₀)` (`TauCeti.thomPairMapOfFiberwise`).
On the fibre over `b'` it is the isomorphism of fibre pairs induced by `φ b'`
(`TauCeti.fiberThomPairMap_comp_thomPairMapOfFiberwise`), it covers `g`
(`TauCeti.thomPairMapOfFiberwise_fst_comp_thomPairProj`), and it carries the zero section over
`g` to the zero section (`TauCeti.zeroSectionHom_comp_thomPairMapOfFiberwise_fst`).

Hence it pulls Thom classes of `E` back to Thom classes of `E'`
(`TauCeti.IsThomClass.thomPairMapOfFiberwise`), and it intertwines the Euler class maps
`Hⁿ(E, E₀) ⟶ Hⁿ(B)` and `Hⁿ(E', E'₀) ⟶ Hⁿ(B')` with pullback along `g`
(`TauCeti.eulerClass_thomPairMapOfFiberwise`). Over the identity of the base, for an isomorphism of
vector bundles over `B`, the Euler class of the pulled-back class is the Euler class of the
original one (`TauCeti.eulerClass_thomPairMapOfFiberwise_id`).

The pullback map of Thom pairs (`TauCeti.pullbackThomPairMap`) is the case where every `φ b'` is
the identity of `E_{g b'}`. The oriented statements, for the integral Thom and Euler classes of
oriented bundles, are in `TauCeti.Topology.VectorBundle.Orientation.FiberwiseEquiv`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §3 (bundle maps) and §9, Property 9.1 (naturality of the Euler class under
  orientation-preserving bundle maps).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Module

universe w v u

namespace TauCeti

section Map

variable {B : Type w} [TopologicalSpace B] {F : Type*} {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] {B' : Type w} [TopologicalSpace B'] {F' : Type*}
  {E' : B' → Type w} [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommMonoid (E' b)]
  [∀ b, Module ℝ (E' b)] [∀ b, TopologicalSpace (E' b)] {g : C(B', B)}
  {φ : ∀ b', E' b' ≃L[ℝ] E (g b')}

/-- **The map of Thom pairs of a fibrewise isomorphism.** A family of continuous linear
equivalences `φ b' : E'_{b'} ≃ E_{g b'}` over a continuous map `g : B' → B`, whose total-space map
`v ↦ (g (π v), φ (π v) v)` is continuous, as a map `(E', E'₀) ⟶ (E, E₀)` of Thom pairs: a linear
equivalence carries nonzero vectors to nonzero vectors. -/
def thomPairMapOfFiberwise
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.2)) :
    thomPair F' E' ⟶ thomPair F E :=
  TopPair.ofSubsetMap (TopCat.ofHom ⟨_, hφ⟩) fun v hv ↦
    mem_zeroSectionCompl.2 ((φ v.proj).map_ne_zero_iff.2 (mem_zeroSectionCompl.1 hv))

@[simp]
theorem thomPairMapOfFiberwise_fst_apply
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.2))
    (v : TotalSpace F' E') :
    TopPair.Hom.fst (thomPairMapOfFiberwise hφ) v = TotalSpace.mk' F (g v.proj) (φ v.proj v.2) :=
  TopPair.ofSubsetMap_fst_apply (X := TopCat.of (TotalSpace F' E')) _ _ v

variable [TopologicalSpace F] [TopologicalSpace F'] [FiberBundle F E] [FiberBundle F' E']

/-- On the fibre over `b'`, the map of Thom pairs of a fibrewise isomorphism `φ` is the isomorphism
of fibre pairs `(E'_{b'}, E'_{b'} ∖ {0}) ≅ (E_{g b'}, E_{g b'} ∖ {0})` induced by `φ b'`. -/
theorem fiberThomPairMap_comp_thomPairMapOfFiberwise
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.2))
    (b' : B') :
    fiberThomPairMap F' E' b' ≫ thomPairMapOfFiberwise hφ =
      (φ b').complZeroPairIso.hom ≫ fiberThomPairMap F E (g b') := by
  refine TopPair.hom_ext_of_fst _ (TopCat.ext fun (x : E' b') ↦ ?_)
  -- Both sides send `x : E'_{b'}` to `(g b', φ b' x)`. The carriers of the pairs agree with the
  -- fibres and the total spaces only up to unfolding, so first split each composite into its
  -- evaluations.
  change TopPair.Hom.fst (thomPairMapOfFiberwise hφ)
      (TopPair.Hom.fst (fiberThomPairMap F' E' b') x) =
    TopPair.Hom.fst (fiberThomPairMap F E (g b')) (TopPair.Hom.fst (φ b').complZeroPairIso.hom x)
  simp only [fiberThomPairMap_fst_apply, thomPairMapOfFiberwise_fst_apply,
    ContinuousLinearEquiv.complZeroPairIso_hom_fst_apply]
  -- `TotalSpace.mk'` is `TotalSpace.mk` with the fibre made explicit.
  rfl

/-- The map of Thom pairs of a fibrewise isomorphism over `g` covers `g`. -/
theorem thomPairMapOfFiberwise_fst_comp_thomPairProj
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.2)) :
    TopPair.Hom.fst (thomPairMapOfFiberwise hφ) ≫ thomPairProj F E =
      thomPairProj F' E' ≫ TopCat.ofHom g :=
  TopCat.ext fun v ↦ (thomPairProj_apply F E _).trans <|
    (congrArg TotalSpace.proj (thomPairMapOfFiberwise_fst_apply hφ v)).trans
      (congrArg g (thomPairProj_apply F' E' v).symm)

end Map

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] {R : C}
  {k : Type*} [Ring k] [Linear k C] {M : C}

section ThomClass

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] {B' : Type w}
  [TopologicalSpace B'] {E' : B' → Type w} [TopologicalSpace (TotalSpace F E')]
  [∀ b, AddCommMonoid (E' b)] [∀ b, Module ℝ (E' b)] [∀ b, TopologicalSpace (E' b)]
  [FiberBundle F E'] {g : C(B', B)} {φ : ∀ b', E' b' ≃L[ℝ] E (g b')}

/-- **Thom classes pull back along fibrewise isomorphisms.** The pull-back of a Thom class of `E`
along the map of Thom pairs of a fibrewise isomorphism `E'_{b'} ≃ E_{g b'}` over `g` is a Thom
class of `E'`. -/
theorem IsThomClass.thomPairMapOfFiberwise
    {u : (thomPair F E).singularCohomology R k M (finrank ℝ F)} (hu : IsThomClass F E u)
    (hφ : Continuous fun v : TotalSpace F E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.2)) :
    IsThomClass F E' (TopPair.singularCohomologyMap (TauCeti.thomPairMapOfFiberwise hφ) _ u) :=
  hu.singularCohomologyMap _ g (fun b' ↦ (φ b').complZeroPairIso)
    (fiberThomPairMap_comp_thomPairMapOfFiberwise hφ)

end ThomClass

section EulerClass

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {B' : Type w} [TopologicalSpace B'] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {E' : B' → Type w} [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommMonoid (E' b)]
  [∀ b, Module ℝ (E' b)] [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E'] [VectorBundle ℝ F' E']

/-- A fibrewise isomorphism `φ` over `g` carries the zero section of `E'` to the zero section of
`E` over `g`, since every `φ b'` is linear. -/
theorem zeroSectionHom_comp_thomPairMapOfFiberwise_fst {g : C(B', B)}
    {φ : ∀ b', E' b' ≃L[ℝ] E (g b')}
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.2)) :
    zeroSectionHom F' E' ≫ TopPair.Hom.fst (thomPairMapOfFiberwise hφ) =
      TopCat.ofHom g ≫ zeroSectionHom F E :=
  TopCat.ext fun b' ↦ by
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, zeroSectionHom_apply,
      zeroSectionHom_apply, thomPairMapOfFiberwise_fst_apply]
    exact congrArg (TotalSpace.mk' F (g b')) (map_zero (φ b'))

/-- **Naturality of the Euler class under fibrewise isomorphisms.** For a fibrewise isomorphism
`E'_{b'} ≃ E_{g b'}` over `g : B' → B`, pulling a relative class back along the map of Thom pairs
and then taking its Euler class gives the pull-back along `g` of its Euler class. -/
theorem eulerClass_thomPairMapOfFiberwise {g : C(B', B)} {φ : ∀ b', E' b' ≃L[ℝ] E (g b')}
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.2))
    (n : ℕ) :
    TopPair.singularCohomologyMap (thomPairMapOfFiberwise hφ) n ≫ eulerClass R k M F' E' n =
      eulerClass R k M F E n ≫ TopCat.singularCohomologyMap (TopCat.ofHom g) n :=
  eulerClass_naturality F E _ _ (zeroSectionHom_comp_thomPairMapOfFiberwise_fst hφ) n

/-- **Isomorphic bundles have the same Euler classes.** For a fibrewise isomorphism `E'_b ≃ E_b`
of vector bundles over the same base, covering the identity, pulling a relative class back along
the map of Thom pairs does not change its Euler class. -/
theorem eulerClass_thomPairMapOfFiberwise_id {E' : B → Type w}
    [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommMonoid (E' b)] [∀ b, Module ℝ (E' b)]
    [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E'] [VectorBundle ℝ F' E']
    {φ : ∀ b, E' b ≃L[ℝ] E b}
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F v.proj (φ v.proj v.2)) (n : ℕ) :
    TopPair.singularCohomologyMap (thomPairMapOfFiberwise (g := ContinuousMap.id B) hφ) n ≫
      eulerClass R k M F' E' n = eulerClass R k M F E n := by
  rw [eulerClass_thomPairMapOfFiberwise (g := ContinuousMap.id B) hφ n]
  exact (congrArg (eulerClass R k M F E n ≫ ·) (TopCat.singularCohomologyMap_id _ n)).trans
    (Category.comp_id _)

end EulerClass

end TauCeti
