/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Covering
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import TauCeti.Topology.Covering.Quotient

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
`(A ⊗ k[p⁻¹ x])_G`; since `G` acts simply transitively on `p⁻¹ x`, a choice of point `e` in the
fibre identifies it with `A`, naturally in `A`
(`IsQuotientCoveringMap.coinvariantsTensorFiberLinearEquiv`): the class of `a ⊗ e` corresponds to
`a`. This is the system of local coefficients of the bundle `E ×_G A` over `B`.

The construction is an additive functor from representations of `G` to local coefficient systems
on `B` (`IsQuotientCoveringMap.associatedLocalSystemFunctor`). Since every fibre is a copy of `A`,
it is exact: a short exact sequence of representations gives a short exact sequence of local
systems (`IsQuotientCoveringMap.shortExact_map_associatedLocalSystemFunctor`), so a coefficient
sequence of representations has a long exact sequence in twisted homology.

## Main definitions

* `IsQuotientCoveringMap.fiberRepresentation`: the permutation representation on the free module
  on a fibre.
* `IsQuotientCoveringMap.permutationRepFunctor`: these representations as a functor on the
  fundamental groupoid of the base.
* `IsQuotientCoveringMap.associatedLocalSystem`: the local coefficient system associated to a
  representation.
* `IsQuotientCoveringMap.associatedLocalSystemMap`: the morphism of associated local systems
  induced by a morphism of representations.
* `IsQuotientCoveringMap.coinvariantsTensorFiberLinearEquiv`,
  `IsQuotientCoveringMap.coinvariantsTensorFiberIso`: a point of the fibre identifies the fibre
  `(A ⊗ k[p⁻¹ x])_G` of the associated local system with `A`, naturally in `A`.
* `IsQuotientCoveringMap.associatedLocalSystemFunctor`: the associated local systems as a functor
  of the representation.

## Main results

* `IsQuotientCoveringMap.shortExact_map_associatedLocalSystemFunctor`: the associated local
  systems of a short exact sequence of representations form a short exact sequence.

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

section Fiber

variable {k} {b : B} (e : p ⁻¹' {b})

/-- The bilinear map `A × k[p⁻¹ b] → A` sending `(a, e')` to `ρ(g)⁻¹ a`, where `g` is the element
of `G` carrying `e` to `e'`. -/
private def fiberTensorToRep (A : Rep.{u} k G) : A →ₗ[k] (p ⁻¹' {b} →₀ k) →ₗ[k] A :=
  (Finsupp.linearCombination k fun e' ↦ A.ρ (hG.fiberEquivGroup e e')⁻¹).flip

/-- **A point of the fibre identifies the fibre of the associated local system with the
representation**: for a point `e` over `b`, the linear equivalence `(A ⊗ k[p⁻¹ b])_G ≃ₗ[k] A`
sending the class of `a ⊗ e'` to `ρ(g)⁻¹ a`, where `g • e = e'`. Its inverse sends `a` to the class
of `a ⊗ e`. -/
def coinvariantsTensorFiberLinearEquiv (A : Rep.{u} k G) :
    ((Rep.coinvariantsTensor k G).obj A).obj (Rep.of (hG.fiberRepresentation k b)) ≃ₗ[k] A :=
  LinearEquiv.ofLinearMap
    (Representation.Coinvariants.lift _ (TensorProduct.lift (fiberTensorToRep hG e A))
      fun g ↦ TensorProduct.ext <| LinearMap.ext fun a ↦ Finsupp.lhom_ext fun e' r ↦ by
        let := hG.mulActionFiber b
        simp [fiberTensorToRep])
    ((Rep.coinvariantsTensorMk A (Rep.of (hG.fiberRepresentation k b))).flip
      (Finsupp.single e 1))
    (LinearMap.ext fun a ↦ by simp [fiberTensorToRep])
    (Representation.Coinvariants.hom_ext <| TensorProduct.ext <| LinearMap.ext fun a ↦
      Finsupp.lhom_ext' fun e' ↦ LinearMap.ext_ring <| by
        -- The class of `a ⊗ e'` is that of `ρ(g)⁻¹ a ⊗ e`, where `g • e = e'`.
        let := hG.mulActionFiber b
        have he' : hG.fiberEquivGroup e e' • e = e' := Subtype.ext (hG.fiberEquivGroup_smul_self e)
        simp [fiberTensorToRep, he'])

/-- The fibre identification sends the class of `a ⊗ r e'` to `r • ρ(g)⁻¹ a`, where `g • e = e'`. -/
-- Not a simp lemma: `simp` unfolds `Rep.coinvariantsTensorMk` on the left-hand side first.
theorem coinvariantsTensorFiberLinearEquiv_coinvariantsTensorMk (A : Rep.{u} k G) (a : A)
    (e' : p ⁻¹' {b}) (r : k) :
    hG.coinvariantsTensorFiberLinearEquiv e A
        (Rep.coinvariantsTensorMk A (Rep.of (hG.fiberRepresentation k b)) a (Finsupp.single e' r)) =
      r • A.ρ (hG.fiberEquivGroup e e')⁻¹ a := by
  simp [coinvariantsTensorFiberLinearEquiv, fiberTensorToRep]

/-- The inverse fibre identification sends `a` to the class of `a ⊗ e`. -/
-- Not a simp lemma: `simp` first rewrites the type of the equivalence on the left-hand side.
theorem coinvariantsTensorFiberLinearEquiv_symm_apply (A : Rep.{u} k G) (a : A) :
    (hG.coinvariantsTensorFiberLinearEquiv e A).symm a =
      Rep.coinvariantsTensorMk A (Rep.of (hG.fiberRepresentation k b)) a (Finsupp.single e 1) :=
  (rfl)

variable (k) in
/-- The fibre identification `(A ⊗ k[p⁻¹ b])_G ≅ A` determined by a point `e` over `b`, as a
natural isomorphism from the functor `(- ⊗ k[p⁻¹ b])_G` to the forgetful functor. -/
def coinvariantsTensorFiberIso :
    (Rep.coinvariantsTensor k G).flip.obj (Rep.of (hG.fiberRepresentation k b)) ≅
      forget₂ (Rep.{u} k G) (ModuleCat.{u} k) :=
  NatIso.ofComponents (fun A ↦ (hG.coinvariantsTensorFiberLinearEquiv e A).toModuleIso)
    fun f ↦ Rep.coinvariantsTensor_hom_ext (LinearMap.ext fun a ↦ Finsupp.lhom_ext fun e' r ↦
      -- Both sides send the class of `a ⊗ r e'` to `r • ρ(g)⁻¹ (f a)`, where `g • e = e'`: the
      -- functor `(- ⊗ k[p⁻¹ b])_G` sends it to the class of `f a ⊗ r e'` by definition.
      (hG.coinvariantsTensorFiberLinearEquiv_coinvariantsTensorMk e _ (f.hom a) e' r).trans <|
        (congrArg (r • ·) (Rep.hom_comm_apply f _ a).symm).trans <| (map_smul f.hom r _).symm.trans
          (congrArg f.hom
            (hG.coinvariantsTensorFiberLinearEquiv_coinvariantsTensorMk e _ a e' r).symm))

end Fiber

/-- **The local coefficient systems associated to representations, as a functor**: it sends a
representation `A` to `IsQuotientCoveringMap.associatedLocalSystem k A` and a morphism of
representations to `IsQuotientCoveringMap.associatedLocalSystemMap`. -/
-- The body is exposed so that its objects and maps are `associatedLocalSystem` and
-- `associatedLocalSystemMap` by definition, which the coefficient sequences of twisted chains
-- built from it rely on.
@[expose] def associatedLocalSystemFunctor : Rep.{u} k G ⥤ LocalCoefficientSystem k B :=
  Rep.coinvariantsTensor k G ⋙ (Functor.whiskeringLeft _ _ _).obj (hG.permutationRepFunctor k)

/-- The associated local system functor sends a representation to its associated local system. -/
@[simp]
theorem associatedLocalSystemFunctor_obj (A : Rep.{u} k G) :
    (hG.associatedLocalSystemFunctor k).obj A = hG.associatedLocalSystem k A :=
  (rfl)

/-- The associated local system functor sends a morphism of representations to the induced
morphism of associated local systems. -/
@[simp]
theorem associatedLocalSystemFunctor_map (f : A ⟶ A') :
    (hG.associatedLocalSystemFunctor k).map f = hG.associatedLocalSystemMap k f :=
  (rfl)

/-- The associated local system functor is additive: on each fibre it is `(- ⊗ k[p⁻¹ x])_G`. -/
instance instAdditiveAssociatedLocalSystemFunctor : (hG.associatedLocalSystemFunctor k).Additive :=
  inferInstanceAs (Rep.coinvariantsTensor k G ⋙ _).Additive

/-- **Associated local systems preserve short exact sequences**: a short exact sequence
`0 ⟶ A₁ ⟶ A₂ ⟶ A₃ ⟶ 0` of representations of `G` gives a short exact sequence of the associated
local coefficient systems on `B`. Over each point the sequence of fibres is a copy of the given
one, by `IsQuotientCoveringMap.coinvariantsTensorFiberIso`. -/
theorem shortExact_map_associatedLocalSystemFunctor {S : ShortComplex (Rep.{u} k G)}
    (hS : S.ShortExact) : (S.map (hG.associatedLocalSystemFunctor k)).ShortExact := by
  have hJ : JointlyReflectIsomorphisms
      (fun x : FundamentalGroupoid B ↦ (evaluation _ (ModuleCat.{u} k)).obj x) :=
    ⟨fun f h ↦ (NatTrans.isIso_iff_isIso_app f).2 h⟩
  refine (hJ.shortExact_iff _).2 fun x ↦ ?_
  obtain ⟨e, he⟩ := hG.surjective x.as
  exact ShortComplex.shortExact_of_iso
    (S.mapNatIso (hG.coinvariantsTensorFiberIso k (b := x.as) ⟨e, he⟩).symm)
    (hS.map_of_exact _)

end IsQuotientCoveringMap
