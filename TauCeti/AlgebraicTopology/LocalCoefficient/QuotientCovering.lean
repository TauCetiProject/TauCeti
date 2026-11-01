/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Covering
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.Topology.Covering.Quotient
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

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

Choosing a sheet identifies each associated fibre with the coefficient module, naturally in
the representation (`associatedLocalSystemFiberIso`). The construction uses Mathlib's
`IsQuotientCoveringMap.fiberEquivGroup` and
`Representation.coinvariantsTprodLeftRegularLEquiv`. Consequently
`associatedLocalSystemFunctor` preserves finite limits, finite colimits, and short exact
sequences, without any flatness hypothesis on the coefficients.

## Main definitions

* `IsQuotientCoveringMap.fiberRepresentation`: the permutation representation on the free module
  on a fibre.
* `IsQuotientCoveringMap.permutationRepFunctor`: these representations as a functor on the
  fundamental groupoid of the base.
* `IsQuotientCoveringMap.associatedLocalSystem`: the local coefficient system associated to a
  representation.
* `IsQuotientCoveringMap.associatedLocalSystemFunctor`: the exact functor from representations
  to associated local coefficient systems.
* `IsQuotientCoveringMap.associatedLocalSystemFiberIso`: a chosen sheet identifies each associated
  fibre with the original coefficient module, naturally in that module.
* `IsQuotientCoveringMap.associatedLocalSystemMap`: the morphism of associated local systems
  induced by a morphism of representations.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti

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

/-- Associated local systems, as a functor of the coefficient representation. -/
abbrev associatedLocalSystemFunctor : Rep.{u} k G ⥤ LocalCoefficientSystem k B where
  obj := hG.associatedLocalSystem k
  map := hG.associatedLocalSystemMap k
  map_id _ := hG.associatedLocalSystemMap_id k
  map_comp := hG.associatedLocalSystemMap_comp k

/-- Choosing a sheet identifies the permutation representation on the fibre with the regular
representation. -/
def fiberRepresentationIsoLeftRegular (b : B) (e : p ⁻¹' {b}) :
    Rep.of (hG.fiberRepresentation k b) ≅ Rep.of (Representation.leftRegular k G) := by
  letI := hG.mulActionFiber b
  refine Rep.mkIso
    { __ := (Finsupp.domLCongr (hG.fiberEquivGroup e) :
          (p ⁻¹' {b} →₀ k) ≃ₗ[k] (G →₀ k)).trans
        (MonoidAlgebra.coeffLinearEquiv k).symm
      isIntertwining' := fun g ↦ ?_ }
  refine Finsupp.lhom_ext fun e' r ↦ ?_
  have heq : hG.fiberEquivGroup e (g • e') = g * hG.fiberEquivGroup e e' := by
    apply (hG.fiberEquivGroup_eq_iff _ _ _).2
    rw [mul_smul, hG.fiberEquivGroup_smul_self]
    rfl
  -- Write the intertwined maps on basis vectors across the monoid-algebra carrier.
  change (MonoidAlgebra.coeffLinearEquiv k).symm
      (Finsupp.domLCongr (hG.fiberEquivGroup e)
        (hG.fiberRepresentation k b g (Finsupp.single e' r))) =
    Representation.leftRegular k G g ((MonoidAlgebra.coeffLinearEquiv k).symm
      ((Finsupp.domLCongr (hG.fiberEquivGroup e) :
            (p ⁻¹' {b} →₀ k) ≃ₗ[k] (G →₀ k)) (Finsupp.single e' r)))
  simp [heq]

/-- The chosen-sheet identification sends the basis vector at `e'` to the group element
carrying the chosen sheet to `e'`. -/
-- Kept as a named equation: ordinary importing simp does not match through this carrier.
lemma fiberRepresentationIsoLeftRegular_hom_single (b : B) (e e' : p ⁻¹' {b}) (r : k) :
    (hG.fiberRepresentationIsoLeftRegular k b e).hom.hom (Finsupp.single e' r) =
      MonoidAlgebra.single (hG.fiberEquivGroup e e') r := by
  -- The regular representation uses the monoid-algebra carrier, rather than `G →₀ k`.
  change (MonoidAlgebra.coeffLinearEquiv k).symm
      ((Finsupp.domLCongr (hG.fiberEquivGroup e) :
        (p ⁻¹' {b} →₀ k) ≃ₗ[k] (G →₀ k)) (Finsupp.single e' r)) = _
  simp

/-- A chosen sheet identifies an associated fibre with the underlying coefficient module. -/
def associatedLocalSystemFiberIso (A : Rep.{u} k G) (x : FundamentalGroupoid B)
    (e : p ⁻¹' {x.as}) :
    (hG.associatedLocalSystem k A).obj x ≅ (forget₂ (Rep k G) (ModuleCat k)).obj A :=
  ((Rep.coinvariantsTensor k G).obj A).mapIso (hG.fiberRepresentationIsoLeftRegular k x.as e) ≪≫
    (Representation.coinvariantsTprodLeftRegularLEquiv A.ρ).toModuleIso

/-- The fibre identification evaluates a coinvariant tensor by transporting the coefficient
back to the chosen sheet. -/
-- Kept as a named equation: simp normalizes `coinvariantsTensorMk` before matching it.
lemma associatedLocalSystemFiberIso_hom_mk_single (A : Rep.{u} k G)
    (x : FundamentalGroupoid B) (e e' : p ⁻¹' {x.as}) (a : A) (r : k) :
    (hG.associatedLocalSystemFiberIso k A x e).hom.hom
        (Rep.coinvariantsTensorMk A (Rep.of (hG.fiberRepresentation k x.as)) a
          (Finsupp.single e' r)) = r • A.ρ (hG.fiberEquivGroup e e')⁻¹ a := by
  -- Express the functorial map on coinvariants before using the regular-representation equation.
  change Representation.ofCoinvariantsTprodLeftRegular A.ρ
      (Representation.Coinvariants.mk _ (a ⊗ₜ[k]
        (hG.fiberRepresentationIsoLeftRegular k x.as e).hom.hom (Finsupp.single e' r))) = _
  rw [hG.fiberRepresentationIsoLeftRegular_hom_single,
    Representation.ofCoinvariantsTprodLeftRegular_mk_tmul_single]

/-- At the chosen sheet, the fibre identification recovers the original coefficient. -/
lemma associatedLocalSystemFiberIso_hom_mk_self (A : Rep.{u} k G)
    (x : FundamentalGroupoid B) (e : p ⁻¹' {x.as}) (a : A) :
    (hG.associatedLocalSystemFiberIso k A x e).hom.hom
        (Rep.coinvariantsTensorMk A (Rep.of (hG.fiberRepresentation k x.as)) a
          (Finsupp.single e 1)) = a := by
  rw [hG.associatedLocalSystemFiberIso_hom_mk_single]
  simp

/-- The fibre identification is natural in every coefficient representation. -/
@[reassoc]
lemma associatedLocalSystemFiberIso_hom_naturality {A A' : Rep.{u} k G} (f : A ⟶ A')
    (x : FundamentalGroupoid B) (e : p ⁻¹' {x.as}) :
    (hG.associatedLocalSystemMap k f).app x ≫ (hG.associatedLocalSystemFiberIso k A' x e).hom =
      (hG.associatedLocalSystemFiberIso k A x e).hom ≫
        (forget₂ (Rep k G) (ModuleCat k)).map f := by
  refine Rep.coinvariantsTensor_hom_ext (LinearMap.ext fun a ↦ Finsupp.lhom_ext fun e' r ↦ ?_)
  -- Present the source using the explicit fibre representation so the public equations match.
  change ((hG.associatedLocalSystemFiberIso k A' x e).hom).hom
      (((hG.associatedLocalSystemMap k f).app x).hom
        (Rep.coinvariantsTensorMk A (Rep.of (hG.fiberRepresentation k x.as)) a
          (Finsupp.single e' r))) =
    f.hom (((hG.associatedLocalSystemFiberIso k A x e).hom).hom
      (Rep.coinvariantsTensorMk A (Rep.of (hG.fiberRepresentation k x.as)) a
        (Finsupp.single e' r)))
  rw [hG.associatedLocalSystemMap_app_coinvariantsTensorMk]
  rw [hG.associatedLocalSystemFiberIso_hom_mk_single,
    hG.associatedLocalSystemFiberIso_hom_mk_single, map_smul]
  exact congrArg (r • ·) (LinearMap.congr_fun (f.hom.isIntertwining' _) a).symm

private def associatedLocalSystemFunctorEvalIso (x : FundamentalGroupoid B)
    (e : p ⁻¹' {x.as}) :
    hG.associatedLocalSystemFunctor k ⋙
        (evaluation (FundamentalGroupoid B) (ModuleCat k)).obj x ≅
      forget₂ (Rep k G) (ModuleCat k) :=
  NatIso.ofComponents (fun A ↦ hG.associatedLocalSystemFiberIso k A x e)
    (fun f ↦ hG.associatedLocalSystemFiberIso_hom_naturality k f x e)

/-- Forming the local system associated to a quotient covering preserves finite limits. -/
instance associatedLocalSystemFunctorPreservesFiniteLimits :
    PreservesFiniteLimits (hG.associatedLocalSystemFunctor k) where
  preservesFiniteLimits J _ _ :=
    preservesLimitsOfShape_of_evaluation _ J fun x ↦ by
      obtain ⟨e, he⟩ := hG.surjective x.as
      exact preservesLimitsOfShape_of_natIso
        (hG.associatedLocalSystemFunctorEvalIso k x ⟨e, he⟩).symm

/-- Forming the local system associated to a quotient covering preserves finite colimits. -/
instance associatedLocalSystemFunctorPreservesFiniteColimits :
    PreservesFiniteColimits (hG.associatedLocalSystemFunctor k) where
  preservesFiniteColimits J _ _ :=
    preservesColimitsOfShape_of_evaluation _ J fun x ↦ by
      obtain ⟨e, he⟩ := hG.surjective x.as
      exact preservesColimitsOfShape_of_natIso
        (hG.associatedLocalSystemFunctorEvalIso k x ⟨e, he⟩).symm

end IsQuotientCoveringMap
