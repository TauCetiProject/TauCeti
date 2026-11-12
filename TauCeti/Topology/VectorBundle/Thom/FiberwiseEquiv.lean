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
(`TauCeti.IsThomClass.thomPairMapOfFiberwise`). Over the identity of the base, a relative class
of `E` is a Thom class exactly when its pull-back to `E'` is one
(`TauCeti.isThomClass_singularCohomologyMap_thomPairMapOfFiberwise_iff`), and when the
total-space map of the fibrewise inverse is continuous as well, the maps of Thom pairs of `φ` and of
its inverse form an isomorphism of Thom pairs (`TauCeti.thomPairIsoOfFiberwise`). The map of Thom
pairs also intertwines the Euler class maps `Hⁿ(E, E₀) ⟶ Hⁿ(B)` and `Hⁿ(E', E'₀) ⟶ Hⁿ(B')`
with pullback along `g` (`TauCeti.eulerClass_thomPairMapOfFiberwise`). Over the identity of the
base, for an isomorphism of vector bundles over `B`, the Euler class of the pulled-back class is the
Euler class of the original one (`TauCeti.eulerClass_thomPairMapOfFiberwise_id`).

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

section Iso

variable {B : Type w} [TopologicalSpace B] {F : Type*} {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] {F' : Type*} {E' : B → Type w}
  [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommMonoid (E' b)] [∀ b, Module ℝ (E' b)]
  [∀ b, TopologicalSpace (E' b)] {φ : ∀ b, E' b ≃L[ℝ] E b}

/-- **The isomorphism of Thom pairs of a bundle isomorphism.** A family of continuous linear
equivalences `φ b : E'_b ≃ E_b` over the same base whose total-space map and its inverse
`v ↦ (π v, (φ (π v))⁻¹ v)` are both continuous, as an isomorphism `(E', E'₀) ≅ (E, E₀)` of Thom
pairs. Its two directions are the maps of Thom pairs of `φ` and of its fibrewise inverse. -/
def thomPairIsoOfFiberwise
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F v.proj (φ v.proj v.2))
    (hφ' : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F' v.proj ((φ v.proj).symm v.2)) :
    thomPair F' E' ≅ thomPair F E :=
  TopPair.ofSubsetIso
    { toFun v := TotalSpace.mk' F v.proj (φ v.proj v.2)
      invFun v := TotalSpace.mk' F' v.proj ((φ v.proj).symm v.2)
      left_inv v := congrArg (TotalSpace.mk' F' v.proj) ((φ v.proj).symm_apply_apply v.2)
      right_inv v := congrArg (TotalSpace.mk' F v.proj) ((φ v.proj).apply_symm_apply v.2)
      continuous_toFun := hφ
      continuous_invFun := hφ' }
    fun v ↦ mem_zeroSectionCompl.trans ((φ v.proj).map_ne_zero_iff.symm.trans
      (mem_zeroSectionCompl (v := TotalSpace.mk' F v.proj (φ v.proj v.2))).symm)

variable (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F v.proj (φ v.proj v.2))
  (hφ' : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F' v.proj ((φ v.proj).symm v.2))

@[simp]
theorem thomPairIsoOfFiberwise_hom :
    (thomPairIsoOfFiberwise hφ hφ').hom = thomPairMapOfFiberwise (g := ContinuousMap.id B) hφ := by
  rw [thomPairIsoOfFiberwise, TopPair.ofSubsetIso_hom]
  -- Both maps send `v` to `(π v, φ (π v) v)`; compare them on the total space.
  refine TopPair.hom_ext_of_fst _ (TopCat.ext fun v ↦ ?_)
  exact (TopPair.ofSubsetMap_fst_apply (X := TopCat.of (TotalSpace F' E')) _ _ v).trans
    (thomPairMapOfFiberwise_fst_apply (g := ContinuousMap.id B) hφ v).symm

@[simp]
theorem thomPairIsoOfFiberwise_inv :
    (thomPairIsoOfFiberwise hφ hφ').inv =
      thomPairMapOfFiberwise (g := ContinuousMap.id B) (φ := fun b ↦ (φ b).symm) hφ' := by
  rw [thomPairIsoOfFiberwise, TopPair.ofSubsetIso_inv]
  -- Both maps send `v` to `(π v, (φ (π v))⁻¹ v)`; compare them on the total space.
  refine TopPair.hom_ext_of_fst _ (TopCat.ext fun v ↦ ?_)
  exact (TopPair.ofSubsetMap_fst_apply (X := TopCat.of (TotalSpace F E)) _ _ v).trans
    (thomPairMapOfFiberwise_fst_apply (g := ContinuousMap.id B) (φ := fun b ↦ (φ b).symm) hφ'
      v).symm

end Iso

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

/-- **Thom classes are invariant under bundle isomorphisms.** For a fibrewise isomorphism
`φ b : E'_b ≃ E_b` over the same base with continuous total-space map, a relative class of `E` is a
Thom class exactly when its pull-back along the map of Thom pairs of `φ` is a Thom class of `E'`.
No continuity of the inverse total-space map is needed: on each fibre, `φ b` induces a linear
isomorphism in cohomology, which reflects generators as well as preserving them. -/
theorem isThomClass_singularCohomologyMap_thomPairMapOfFiberwise_iff {E' : B → Type w}
    [TopologicalSpace (TotalSpace F E')] [∀ b, AddCommMonoid (E' b)] [∀ b, Module ℝ (E' b)]
    [∀ b, TopologicalSpace (E' b)] [FiberBundle F E'] {φ : ∀ b, E' b ≃L[ℝ] E b}
    (hφ : Continuous fun v : TotalSpace F E' ↦ TotalSpace.mk' F v.proj (φ v.proj v.2))
    {u : (thomPair F E).singularCohomology R k M (finrank ℝ F)} :
    IsThomClass F E'
        (TopPair.singularCohomologyMap (thomPairMapOfFiberwise (g := ContinuousMap.id B) hφ) _ u) ↔
      IsThomClass F E u := by
  refine ⟨fun hu ↦ ?_, fun hu ↦ hu.thomPairMapOfFiberwise hφ⟩
  obtain ⟨hF, hu⟩ := isThomClass_iff.1 hu
  refine isThomClass_iff.2 ⟨hF, fun b ↦ ?_⟩
  have hψ : fiberThomPairMap F E' b ≫ thomPairMapOfFiberwise (g := ContinuousMap.id B) hφ =
      (φ b).complZeroPairIso.hom ≫ fiberThomPairMap F E b :=
    fiberThomPairMap_comp_thomPairMapOfFiberwise hφ b
  have h := hu b
  rw [← ConcreteCategory.comp_apply, ← TopPair.singularCohomologyMap_comp, hψ,
    TopPair.singularCohomologyMap_comp, ConcreteCategory.comp_apply] at h
  -- The isomorphism of fibre pairs induced by `φ b` gives an isomorphism `e` in cohomology, with
  -- forward map `TopPair.singularCohomologyMap (φ b).complZeroPairIso.hom`, which reflects
  -- generators.
  let e := Iso.mk (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (φ b).complZeroPairIso.hom (finrank ℝ F))
    (TopPair.singularCohomologyMap (φ b).complZeroPairIso.inv _)
    (by rw [← TopPair.singularCohomologyMap_comp, Iso.inv_hom_id, TopPair.singularCohomologyMap_id])
    (by rw [← TopPair.singularCohomologyMap_comp, Iso.hom_inv_id, TopPair.singularCohomologyMap_id])
  rw [← Submodule.map_eq_top_iff (e := e.toLinearEquiv), ← Submodule.span_image_linearEquiv,
    Set.image_singleton, Iso.toLinearEquiv_apply]
  simpa only [e] using h

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
