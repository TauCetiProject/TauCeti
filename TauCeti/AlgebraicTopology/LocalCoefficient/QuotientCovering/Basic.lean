/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Covering
public import TauCeti.RepresentationTheory.Rep.CoinvariantsTensor
public import TauCeti.Topology.Category.TopCat.Fiber
public import Mathlib.Topology.Covering.Quotient

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

An equivariant map of quotient covers over a map of bases, together with a coefficient map
compatible with the group homomorphism, induces a map to the pullback of the target associated
local system (`IsQuotientCoveringMap.associatedLocalSystemMapOver`). It applies the coefficient
map to the tensor factor and the covering map to the sheet.

## Main definitions

* `IsQuotientCoveringMap.fiberRepresentation`: the permutation representation on the free module
  on a fibre.
* `IsQuotientCoveringMap.fiberRepresentationIsoLeftRegular`: a choice of sheet identifies the
  fibre representation with the left regular representation.
* `IsQuotientCoveringMap.permutationRepFunctor`: these representations as a functor on the
  fundamental groupoid of the base.
* `IsQuotientCoveringMap.permutationRepMap`: the map of permutation-representation functors
  induced by an equivariant map of quotient covers.
* `IsQuotientCoveringMap.associatedLocalSystem`: the local coefficient system associated to a
  representation.
* `IsQuotientCoveringMap.associatedLocalSystemMap`: the morphism of associated local systems
  induced by a morphism of representations.
* `IsQuotientCoveringMap.associatedLocalSystemMapOver`: the map of associated local systems over
  a map of bases, induced by an equivariant cover map and a compatible coefficient map.

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

end Permutation

section Regular

variable (k : Type u) [Ring k]

/-- A choice of sheet identifies the permutation representation on a fibre with the regular
representation. -/
def fiberRepresentationIsoLeftRegular {x : B} (e : p ⁻¹' {x}) :
    Rep.of (hG.fiberRepresentation k x) ≅ Rep.leftRegular k G := by
  letI := hG.mulActionFiber x
  refine Rep.mkIso (.mk (Finsupp.domLCongr (hG.fiberEquivGroup e) ≪≫ₗ
    (MonoidAlgebra.coeffLinearEquiv k).symm) fun g ↦ ?_)
  ext e' r
  have he : hG.fiberEquivGroup e (g • e') = g * hG.fiberEquivGroup e e' := by
    apply (hG.fiberEquivGroup_eq_iff e _ _).2
    simp only [coe_mulActionFiber_smul, mul_smul, fiberEquivGroup_smul_self]
  simp [fiberRepresentation_single, he]

/-- The chosen-sheet identification sends the basis vector at `e'` to the group element
carrying the chosen sheet to `e'`. -/
-- Match before simplification changes the implicit representation carriers.
@[simp↓]
lemma fiberRepresentationIsoLeftRegular_hom_single {x : B} (e e' : p ⁻¹' {x})
    (r : k) :
    (fiberRepresentationIsoLeftRegular hG k e).hom.hom (Finsupp.single e' r) =
      MonoidAlgebra.single (hG.fiberEquivGroup e e') r := by
  simp [fiberRepresentationIsoLeftRegular]

end Regular

section Permutation

variable (k : Type u) [Ring k]

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

section ChangeOfGroups

variable {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
  (hH : IsQuotientCoveringMap q H) {φ : G →* H}
  (f : E ⟶ F) (hf : ∀ g x, f (g • x) = φ g • f x)
  (b : B ⟶ C) (hb : p ≫ b = f ≫ q)

/-- An equivariant map of quotient covers induces a morphism between their permutation
representation functors, restricting the target action along the group homomorphism. -/
def permutationRepMap :
    hG.permutationRepFunctor k ⟶
      FundamentalGroupoid.map b.hom ⋙ hH.permutationRepFunctor k ⋙ Rep.resFunctor φ where
  app x := Rep.ofHom
    { toLinearMap := Finsupp.lmapDomain k k ((CommSq.mk hb.symm).fiberMap x.as)
      isIntertwining' g := Finsupp.lhom_ext fun e r ↦ by
        let := hG.mulActionFiber x.as
        let := hH.mulActionFiber (b x.as)
        -- The restricted action is presented through `Rep.res`, so expose the two actions.
        change Finsupp.lmapDomain k k _
            (hG.fiberRepresentation k x.as g (Finsupp.single e r)) =
          hH.fiberRepresentation k (b x.as) (φ g)
            (Finsupp.lmapDomain k k _ (Finsupp.single e r))
        rw [fiberRepresentation_single]
        simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
        rw [fiberRepresentation_single]
        congr 1
        apply Subtype.ext
        -- Expose the fibre actions on the ambient space so the fibre-map coercion lemma matches.
        change ((CommSq.mk hb.symm).fiberMap x.as (g • e) : F) =
          φ g • ((CommSq.mk hb.symm).fiberMap x.as e : F)
        rw [CommSq.fiberMap_apply_coe, CommSq.fiberMap_apply_coe]
        exact hf g e }
  naturality x y γ := by
    have hm : (CommSq.mk hb.symm).fiberMap y.as ∘ hG.isCoveringMap.monodromy γ =
        hH.isCoveringMap.monodromy (γ.map b.hom) ∘ (CommSq.mk hb.symm).fiberMap x.as := by
      funext e
      apply Subtype.ext
      -- Expose function composition under the subtype coercion to apply the fibre-map lemma.
      change ((CommSq.mk hb.symm).fiberMap y.as (hG.isCoveringMap.monodromy γ e) : F) = _
      rw [CommSq.fiberMap_apply_coe]
      exact (hG.isCoveringMap.coe_monodromy_map hH.isCoveringMap
        (g := f.hom) (f := b.hom)
        (funext fun z ↦ (congrArg (fun t : E ⟶ C ↦ t z) hb).symm) γ e
        ((CommSq.mk hb.symm).fiberMap x.as e)
        (CommSq.fiberMap_apply_coe _ _ _).symm).symm
    -- Term mode identifies the restricted representation carriers without rewriting their indices.
    exact Rep.hom_ext (Representation.IntertwiningMap.ext
      ((Finsupp.lmapDomain_comp k k _ ((CommSq.mk hb.symm).fiberMap y.as)).symm.trans
        ((congrArg (Finsupp.lmapDomain k k) hm).trans
          (Finsupp.lmapDomain_comp k k ((CommSq.mk hb.symm).fiberMap x.as) _))))

/-- The map of permutation representations sends the sheet `e` to the sheet `f e`. -/
-- Match before simplification changes the presentation of the restricted representation.
@[simp↓]
theorem permutationRepMap_app_hom_single (x : FundamentalGroupoid B)
    (e : p ⁻¹' {x.as}) (r : k) :
    ((hG.permutationRepMap k hH f hf b hb).app x).hom (Finsupp.single e r) =
      Finsupp.single ((CommSq.mk hb.symm).fiberMap x.as e) r :=
  Finsupp.mapDomain_single

end ChangeOfGroups

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

section ChangeOfGroups

variable {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
  (hH : IsQuotientCoveringMap q H) {φ : G →* H}
  (f : E ⟶ F) (hf : ∀ g x, f (g • x) = φ g • f x)
  (b : B ⟶ C) (hb : p ≫ b = f ≫ q)

variable {D : Rep.{u} k H} (ξ : A ⟶ Rep.res φ D)

/-- A map of quotient covers equivariant along `φ`, together with a compatible coefficient map
`ξ`, induces a map from the associated local system to the pullback of the target system.
On fibres it sends `⟦a ⊗ e⟧` to `⟦ξ a ⊗ f e⟧`. -/
def associatedLocalSystemMapOver :
    hG.associatedLocalSystem k A ⟶
      (LocalCoefficientSystem.pullback b.hom).obj (hH.associatedLocalSystem k D) where
  app x := φ.coinvariantsTensorMap ξ ((hG.permutationRepMap k hH f hf b hb).app x)
  naturality _ _ γ :=
    φ.coinvariantsTensorMap_naturality ξ _ _
      ((hG.permutationRepFunctor k).map γ)
      ((hH.permutationRepFunctor k).map ((FundamentalGroupoid.map b.hom).map γ))
      ((hG.permutationRepMap k hH f hf b hb).naturality γ).symm

/-- On a tensor class at a sheet, the map of associated local systems applies `ξ` to the
coefficient and `f` to the sheet. -/
@[simp↓]
theorem associatedLocalSystemMapOver_app_mk_single (x : FundamentalGroupoid B) (a : A)
    (e : p ⁻¹' {x.as}) (r : k) :
    ((hG.associatedLocalSystemMapOver k hH f hf b hb ξ).app x).hom
        (Rep.coinvariantsTensorMk A ((hG.permutationRepFunctor k).obj x) a
          (Finsupp.single e r)) =
      Rep.coinvariantsTensorMk D ((hH.permutationRepFunctor k).obj
        ((FundamentalGroupoid.map b.hom).obj x)) (ξ.hom a)
        (Finsupp.single ((CommSq.mk hb.symm).fiberMap x.as e) r) := by
  exact (φ.coinvariantsTensorMap_mk ξ
    ((hG.permutationRepMap k hH f hf b hb).app x) a (Finsupp.single e r)).trans
    (congrArg (Rep.coinvariantsTensorMk D
      ((hH.permutationRepFunctor k).obj ((FundamentalGroupoid.map b.hom).obj x)) (ξ.hom a))
      (hG.permutationRepMap_app_hom_single k hH f hf b hb x e r))

end ChangeOfGroups

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

end IsQuotientCoveringMap
