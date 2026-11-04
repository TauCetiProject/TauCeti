/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Covering
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.Topology.Covering.Quotient
public import TauCeti.RepresentationTheory.Rep.CoinvariantsTensor

/-!
# Local coefficient systems associated to representations

Let `p : E ⟶ B` be the quotient covering map of an action of a group `G` on `E`, in the sense of
Mathlib's `IsQuotientCoveringMap`, and let `k` be a commutative ring. The group `G` permutes each
fibre of `p`, and covering-space monodromy commutes with this action
(`IsQuotientCoveringMap.monodromy_smul`). So the free modules `k[p⁻¹ x]` on the fibres form a
functor from the fundamental groupoid of `B` to representations of `G`
(`IsQuotientCoveringMap.permutationRepFunctor`); forgetting the action gives the permutation local
system `IsCoveringMap.permutationLocalSystem`.

For a representation `A` of `G`, composing with `(A ⊗ -)_G` gives the local coefficient system on
`B` associated to `A` (`IsQuotientCoveringMap.associatedLocalSystem`). Its fibre over `x` is
`(A ⊗ k[p⁻¹ x])_G`; since `G` acts simply transitively on `p⁻¹ x`, a choice of point in the fibre
identifies it with `A`. This is the system of local coefficients of the bundle `E ×_G A` over `B`.

The construction is functorial in the cover as well. Let `q : F ⟶ C` be the quotient covering
map of an action of a group `H`, `f : E ⟶ F` a map equivariant along `φ : G →* H` lying over
`b : B ⟶ C`, and `α : A ⟶ Res(φ)(A')` a compatible morphism of representations. Then `f`
carries the fibre of `p` over `x` into the fibre of `q` over `b x`, compatibly with monodromy
(`IsCoveringMap.coe_monodromy_map`), and induces a morphism from the local system associated to
`A` to the pullback along `b` of the local system associated to `A'`
(`IsQuotientCoveringMap.associatedLocalSystemPullbackMap`), sending the class of `a ⊗ e` to the
class of `α a ⊗ f e`.

## Main definitions

* `IsQuotientCoveringMap.fiberRepresentation`: the permutation representation on the free module
  on a fibre.
* `IsQuotientCoveringMap.permutationRepFunctor`: these representations as a functor on the
  fundamental groupoid of the base.
* `IsQuotientCoveringMap.associatedLocalSystem`: the local coefficient system associated to a
  representation.
* `IsQuotientCoveringMap.associatedLocalSystemMap`: the morphism of associated local systems
  induced by a morphism of representations.
* `IsQuotientCoveringMap.associatedLocalSystemPullbackMap`: the morphism of associated local
  systems induced by an equivariant map of quotient covers and a compatible morphism of
  representations.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H.
-/

public section

noncomputable section

open CategoryTheory TauCeti

universe u

namespace IsQuotientCoveringMap

variable {E B : TopCat.{u}} {p : E ⟶ B} {G : Type u} [Group G] [MulAction G E]
  (hG : IsQuotientCoveringMap p G)

/-- Monodromy of a quotient covering commutes with the action of the group on its fibres. -/
theorem monodromy_smul {x y : B} (γ : Path.Homotopic.Quotient x y) (g : G) (e : p ⁻¹' {x}) :
    letI := hG.mulActionFiber x
    letI := hG.mulActionFiber y
    hG.isCoveringMap.monodromy γ (g • e) = g • hG.isCoveringMap.monodromy γ e := by
  let := hG.mulActionFiber x
  let := hG.mulActionFiber y
  have := hG.toContinuousConstSMul
  have hf : ⇑p ∘ (g • · : E → E) = p := funext fun _ ↦ hG.map_smul g
  have hfiber (z : B) (u : p ⁻¹' {z}) :
      Function.fiberMap (⟨(g • · : E → E), continuous_const_smul g⟩ : C(E, E)) hf z u =
        letI := hG.mulActionFiber z; g • u :=
    Subtype.ext (Function.fiberMap_apply_coe _ hf z u)
  simpa only [hfiber] using (hG.isCoveringMap.fiberMap_monodromy hG.isCoveringMap
    ⟨(g • · : E → E), continuous_const_smul g⟩ hf γ e).symm

section Permutation

variable (k : Type u) [Ring k]

/-- The permutation representation of `G` on the free `k`-module on the fibre of `p` over `b`. -/
def fiberRepresentation (b : B) : Representation k G (p ⁻¹' {b} →₀ k) :=
  letI := hG.mulActionFiber b
  { toFun g := Finsupp.lmapDomain k k (g • ·)
    map_one' := by ext; simp
    map_mul' g h := by ext; simp [mul_smul] }

/-- An element of `G` moves a basis vector of the free module on a fibre to the basis vector of
the translated point. -/
@[simp]
theorem fiberRepresentation_single (b : B) (g : G) (e : p ⁻¹' {b}) (r : k) :
    letI := hG.mulActionFiber b
    hG.fiberRepresentation k b g (Finsupp.single e r) = Finsupp.single (g • e) r := by
  simp [fiberRepresentation]

/-- The permutation representations of `G` on the free `k`-modules on the fibres of `p`, as a
functor on the fundamental groupoid of `B`. A path class acts by the linear extension of
monodromy, as in the permutation local system `IsCoveringMap.permutationLocalSystem`; this
commutes with the action of `G` (`IsQuotientCoveringMap.monodromy_smul`). -/
-- The body is exposed so that the representation over `x` is `fiberRepresentation` by
-- definition, as `IsQuotientCoveringMap.associatedLocalSystem_obj` and its consumers rely on.
@[expose] def permutationRepFunctor : FundamentalGroupoid B ⥤ Rep.{u} k G where
  obj x := Rep.of (hG.fiberRepresentation k x.as)
  map γ := Rep.ofHom
    { toLinearMap := Finsupp.lmapDomain k k (hG.isCoveringMap.monodromy γ)
      isIntertwining' g := Finsupp.lhom_ext fun e r ↦ by simp [monodromy_smul] }
  map_id x := Rep.hom_ext (Representation.IntertwiningMap.ext
    (congrArg ModuleCat.Hom.hom ((hG.isCoveringMap.permutationLocalSystem k).map_id x)))
  map_comp γ δ := Rep.hom_ext (Representation.IntertwiningMap.ext
    (congrArg ModuleCat.Hom.hom ((hG.isCoveringMap.permutationLocalSystem k).map_comp γ δ)))

/-- The representation over `x` is the permutation representation on the fibre over `x`. -/
theorem permutationRepFunctor_obj (x : FundamentalGroupoid B) :
    (hG.permutationRepFunctor k).obj x = Rep.of (hG.fiberRepresentation k x.as) :=
  (rfl)

/-- A path class acts on the permutation representations by the linear extension of
monodromy. -/
@[simp]
theorem permutationRepFunctor_map_hom_apply {x y : FundamentalGroupoid B} (γ : x ⟶ y)
    (v : p ⁻¹' {x.as} →₀ k) :
    ((hG.permutationRepFunctor k).map γ).hom v =
      Finsupp.lmapDomain k k (hG.isCoveringMap.monodromy γ) v :=
  (rfl)

end Permutation

variable (k : Type u) [CommRing k] (A : Rep.{u} k G)

/-- **The local coefficient system associated to a representation**: for a representation `A` of
`G`, the local coefficient system on `B` whose fibre over `x` is `(A ⊗ k[p⁻¹ x])_G`, the
coinvariants of `A` tensored with the permutation representation on the fibre over `x`, with
transport induced by monodromy. It is the system of local coefficients of the bundle `E ×_G A`
over `B`. -/
-- The body is exposed so that its fibres are `(A ⊗ k[p⁻¹ x])_G` by definition; the comparison of
-- twisted chains with coinvariant chains is stated on elements of these fibres.
@[expose] def associatedLocalSystem : LocalCoefficientSystem k B :=
  hG.permutationRepFunctor k ⋙ (Rep.coinvariantsTensor k G).obj A

/-- The fibre of the associated local system over `x` is `(A ⊗ k[p⁻¹ x])_G`. -/
theorem associatedLocalSystem_obj (x : FundamentalGroupoid B) :
    (hG.associatedLocalSystem k A).obj x =
      ((Rep.coinvariantsTensor k G).obj A).obj (Rep.of (hG.fiberRepresentation k x.as)) :=
  (rfl)

/-- Transport in the associated local system moves the class of `a ⊗ v` to the class of
`a ⊗ γ_* v`, where `γ_*` is the linear extension of monodromy. -/
-- Not a simp lemma: `simp` unfolds `Rep.coinvariantsTensorMk` on the left-hand side first.
theorem associatedLocalSystem_map_coinvariantsTensorMk {x y : FundamentalGroupoid B} (γ : x ⟶ y)
    (a : A) (v : p ⁻¹' {x.as} →₀ k) :
    ((hG.associatedLocalSystem k A).map γ).hom
        (Rep.coinvariantsTensorMk A (Rep.of (hG.fiberRepresentation k x.as)) a v) =
      Rep.coinvariantsTensorMk A (Rep.of (hG.fiberRepresentation k y.as)) a
        (Finsupp.lmapDomain k k (hG.isCoveringMap.monodromy γ) v) :=
  (rfl)

section CoefficientMap

variable {A} {A' A'' : Rep.{u} k G}

/-- The morphism of associated local coefficient systems induced by a morphism of
representations `f : A ⟶ A'`: on the fibre over `x` it is the map `(A ⊗ k[p⁻¹ x])_G ⟶
(A' ⊗ k[p⁻¹ x])_G` induced by `f`. -/
def associatedLocalSystemMap (f : A ⟶ A') :
    hG.associatedLocalSystem k A ⟶ hG.associatedLocalSystem k A' :=
  Functor.whiskerLeft (hG.permutationRepFunctor k) ((Rep.coinvariantsTensor k G).map f)

/-- The morphism of associated local systems induced by `f` sends the class of `a ⊗ v` to the
class of `f a ⊗ v`. -/
-- Not a simp lemma: `simp` unfolds `Rep.coinvariantsTensorMk` on the left-hand side first.
theorem associatedLocalSystemMap_app_coinvariantsTensorMk (f : A ⟶ A')
    (x : FundamentalGroupoid B) (a : A) (v : p ⁻¹' {x.as} →₀ k) :
    ((hG.associatedLocalSystemMap k f).app x).hom
        (Rep.coinvariantsTensorMk A (Rep.of (hG.fiberRepresentation k x.as)) a v) =
      Rep.coinvariantsTensorMk A' (Rep.of (hG.fiberRepresentation k x.as)) (f.hom a) v :=
  (rfl)

/-- The identity of a representation induces the identity of its associated local system. -/
@[simp]
theorem associatedLocalSystemMap_id : hG.associatedLocalSystemMap k (𝟙 A) = 𝟙 _ :=
  NatTrans.ext <| funext fun _ ↦ NatTrans.congr_app ((Rep.coinvariantsTensor k G).map_id A) _

/-- The morphism of associated local systems induced by a composite is the composite. -/
@[simp, reassoc]
theorem associatedLocalSystemMap_comp (f : A ⟶ A') (f' : A' ⟶ A'') :
    hG.associatedLocalSystemMap k (f ≫ f') =
      hG.associatedLocalSystemMap k f ≫ hG.associatedLocalSystemMap k f' :=
  NatTrans.ext <| funext fun _ ↦ NatTrans.congr_app ((Rep.coinvariantsTensor k G).map_comp f f') _

/-- The associated local coefficient system, functorially in the representation.
Reducibility lets coefficient maps use their original source and target types without transports. -/
abbrev associatedLocalSystemFunctor : Rep.{u} k G ⥤ LocalCoefficientSystem.{u, u, u} k B where
  obj := hG.associatedLocalSystem k
  map := hG.associatedLocalSystemMap k
  map_id _ := hG.associatedLocalSystemMap_id k
  map_comp _ _ := hG.associatedLocalSystemMap_comp k _ _

/-- The associated-system functor has the existing associated local system as its object. -/
@[simp]
lemma associatedLocalSystemFunctor_obj (A : Rep.{u} k G) :
    (hG.associatedLocalSystemFunctor k).obj A = hG.associatedLocalSystem k A :=
  (rfl)

/-- The associated-system functor acts by the existing coefficient maps. -/
@[simp]
lemma associatedLocalSystemFunctor_map {A A' : Rep.{u} k G} (f : A ⟶ A') :
    (hG.associatedLocalSystemFunctor k).map f = hG.associatedLocalSystemMap k f :=
  (rfl)

end CoefficientMap

section Map

variable {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
  (hH : IsQuotientCoveringMap q H) {φ : G →* H} (f : E ⟶ F)
  (hf : ∀ g x, f (g • x) = φ g • f x) (b : B ⟶ C) (hb : p ≫ b = f ≫ q) {A} {A' : Rep.{u} k H}

include hb in
/-- A map of total spaces lying over a map of bases sends the fibre over `x` into the fibre over
`b x`. -/
lemma map_mem_fiber (x : B) (e : p ⁻¹' {x}) : f e ∈ q ⁻¹' {b x} := by
  have h : b (p e) = q (f e) := ConcreteCategory.congr_hom hb e
  have he : p e = x := e.2
  exact h.symm.trans (congrArg b he)

include hf in
/-- The map of permutation representations `k[p⁻¹ x] ⟶ Res(φ)(k[q⁻¹ (b x)])` induced by an
equivariant map of total spaces lying over `b`. -/
private def fiberRepresentationMap (x : B) :
    Rep.of (hG.fiberRepresentation k x) ⟶
      Rep.res φ (Rep.of (hH.fiberRepresentation k (b x))) :=
  Rep.ofHom
    { toLinearMap := Finsupp.lmapDomain k k fun e ↦ ⟨f e, map_mem_fiber f b hb x e⟩
      isIntertwining' g := Finsupp.lhom_ext fun e r ↦ by
        let := hG.mulActionFiber x
        let := hH.mulActionFiber (b x)
        simp only [LinearMap.comp_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
          MonoidHom.comp_apply, fiberRepresentation_single]
        exact congrArg (Finsupp.single · r) (Subtype.ext (hf g e)) }

include hf in
/-- The maps of permutation representations induced by `f` commute with monodromy. -/
private lemma fiberRepresentationMap_naturality {x y : FundamentalGroupoid B} (γ : x ⟶ y) :
    (hG.permutationRepFunctor k).map γ ≫ fiberRepresentationMap hG k hH f hf b hb y.as =
      fiberRepresentationMap hG k hH f hf b hb x.as ≫
        (Rep.resFunctor φ).map
          ((hH.permutationRepFunctor k).map ((FundamentalGroupoid.map b.hom).map γ)) := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (Finsupp.lhom_ext fun e r ↦ ?_))
  -- The fibres of the permutation functors are the permutation representations only up to
  -- unfolding, so the composites are evaluated by stating their components explicitly.
  change (fiberRepresentationMap hG k hH f hf b hb y.as).hom.toLinearMap
      (Finsupp.lmapDomain k k (hG.isCoveringMap.monodromy γ) (Finsupp.single e r)) =
    Finsupp.lmapDomain k k (hH.isCoveringMap.monodromy (Path.Homotopic.Quotient.map γ b.hom))
      ((fiberRepresentationMap hG k hH f hf b hb x.as).hom.toLinearMap (Finsupp.single e r))
  simp only [fiberRepresentationMap, Rep.hom_ofHom, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]
  -- The image under `f` of the lift of `γ` through `e` is the lift of `b ∘ γ` through `f e`.
  exact congrArg (Finsupp.single · r) (Subtype.ext (hG.isCoveringMap.coe_monodromy_map
    hH.isCoveringMap (g := f.hom) (f := b.hom)
    (funext fun z ↦ (ConcreteCategory.congr_hom hb z).symm) γ e _ rfl).symm)

/-- **The morphism of associated local systems along an equivariant map of quotient covers**: for
quotient covers `p : E ⟶ B` and `q : F ⟶ C` of actions of `G` and `H`, a map `f : E ⟶ F`
equivariant along `φ : G →* H` and lying over `b : B ⟶ C`, and a compatible map of
representations `α : A ⟶ Res(φ)(A')`, the morphism from the local system on `B` associated to `A`
to the pullback along `b` of the local system on `C` associated to `A'`. On the fibre over `x` it
sends the class of `a ⊗ e` to the class of `α a ⊗ f e`. -/
def associatedLocalSystemPullbackMap (α : A ⟶ Rep.res φ A') :
    hG.associatedLocalSystem k A ⟶
      (LocalCoefficientSystem.pullback b.hom).obj (hH.associatedLocalSystem k A') where
  app x := φ.coinvariantsTensorMap α (fiberRepresentationMap hG k hH f hf b hb x.as)
  naturality _ _ γ :=
    φ.coinvariantsTensorMap_naturality α _ _ _ _
      (fiberRepresentationMap_naturality hG k hH f hf b hb γ).symm

/-- The morphism of associated local systems along `f` sends the class of `a ⊗ e` to the class of
`α a ⊗ f e`. -/
theorem associatedLocalSystemPullbackMap_app_coinvariantsTensorMk_single (α : A ⟶ Rep.res φ A')
    (x : FundamentalGroupoid B) (a : A) (e : p ⁻¹' {x.as}) (e' : q ⁻¹' {b x.as})
    (he : f e = e') (r : k) :
    ((hG.associatedLocalSystemPullbackMap k hH f hf b hb α).app x).hom
        (Rep.coinvariantsTensorMk A (Rep.of (hG.fiberRepresentation k x.as)) a
          (Finsupp.single e r)) =
      Rep.coinvariantsTensorMk A' (Rep.of (hH.fiberRepresentation k (b x.as))) (α.hom a)
        (Finsupp.single e' r) := by
  obtain rfl : e' = ⟨f e, map_mem_fiber f b hb x.as e⟩ := Subtype.ext he.symm
  exact (φ.coinvariantsTensorMap_mk α _ a _).trans (congrArg _ (Finsupp.mapDomain_single ..))

end Map

end IsQuotientCoveringMap
