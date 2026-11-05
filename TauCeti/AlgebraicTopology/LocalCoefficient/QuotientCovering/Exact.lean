/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Basic
public import TauCeti.RepresentationTheory.Rep.CoinvariantsTensor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Exactness of associated local coefficient systems

For a quotient covering `p : E ⟶ B` by a group `G`, choosing a sheet over `x` identifies
the fibre of the local system associated to a representation `A` with the underlying
module of `A`. The identification sends `⟦a ⊗ [g • e]⟧` to `A.ρ g⁻¹ a`, and is natural
in `A`. It uses Mathlib's `Representation.coinvariantsTprodLeftRegularLEquiv` after
identifying the fibre torsor with `G`. The tensor-coinvariant equivalence is Mathlib's
construction by Amelia Livingston. In particular the fibres are projective when the underlying
module of `A` is projective over `k`
(`IsQuotientCoveringMap.projective_associatedLocalSystem_obj`).

Consequently `IsQuotientCoveringMap.associatedLocalSystemFunctor` preserves small limits
and small colimits. In particular, a short exact sequence of representations gives a
short exact sequence of local systems, without any flatness assumption. This supplies
the coefficient sequences for comparing twisted singular homology with group homology.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H.
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Sections II.4 and III.1.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti

universe u

namespace IsQuotientCoveringMap

variable {E B : TopCat.{u}} {p : E ⟶ B} {G : Type u} [Group G] [MulAction G E]
  (hG : IsQuotientCoveringMap p G) (k : Type u) [CommRing k]

/-- A choice of sheet identifies the fibre of the associated local system with the
underlying coefficient module. -/
def associatedLocalSystemFiberIso (A : Rep.{u} k G) {x : FundamentalGroupoid B}
    (e : p ⁻¹' {x.as}) :
    (hG.associatedLocalSystem k A).obj x ≅ ModuleCat.of k A :=
  ((Rep.coinvariantsTensor k G).obj A).mapIso
      (fiberRepresentationIsoLeftRegular hG k e) ≪≫
    (Representation.coinvariantsTprodLeftRegularLEquiv A.ρ).toModuleIso

/-- In sheet coordinates the class of `a ⊗ r[e']` is `r • A.ρ g⁻¹ a`,
where `e' = g • e`. -/
@[simp↓]
lemma associatedLocalSystemFiberIso_hom_coinvariantsTensorMk (A : Rep.{u} k G)
    {x : FundamentalGroupoid B}
    (e e' : p ⁻¹' {x.as}) (a : A) (r : k) :
    (hG.associatedLocalSystemFiberIso k A e).hom.hom
        (Rep.coinvariantsTensorMk A (Rep.of (hG.fiberRepresentation k x.as)) a
          (Finsupp.single e' r)) =
      r • A.ρ (hG.fiberEquivGroup e e')⁻¹ a := by
  -- Normalize the implicit fibre object and its instances, so the isomorphism's source
  -- matches the tensor class when rewriting the composite and the functor map.
  dsimp +instances only [associatedLocalSystemFiberIso, associatedLocalSystem,
    permutationRepFunctor, Functor.comp_obj]
  rw [Iso.trans_hom, ModuleCat.hom_comp, LinearMap.comp_apply, Functor.mapIso_hom,
    Rep.coinvariantsTensor_obj_map_coinvariantsTensorMk,
    fiberRepresentationIsoLeftRegular_hom_single]
  simp [Rep.coinvariantsTensorMk]

/-- The inverse fibre identification sends `a` to the tensor class using the chosen sheet. -/
-- Match before simplification changes the implicit fibre carrier.
@[simp↓]
lemma associatedLocalSystemFiberIso_inv_apply (A : Rep.{u} k G)
    {x : FundamentalGroupoid B} (e : p ⁻¹' {x.as}) (a : A) :
    (hG.associatedLocalSystemFiberIso k A e).inv.hom a =
      Rep.coinvariantsTensorMk A (Rep.of (hG.fiberRepresentation k x.as)) a
        (Finsupp.single e 1) := by
  apply (ModuleCat.mono_iff_injective (hG.associatedLocalSystemFiberIso k A e).hom).mp
    inferInstance
  simp

/-- The fibre identification is natural in the coefficient representation. -/
@[reassoc]
lemma associatedLocalSystemFiberIso_hom_naturality {A A' : Rep.{u} k G} (f : A ⟶ A')
    {x : FundamentalGroupoid B} (e : p ⁻¹' {x.as}) :
    (hG.associatedLocalSystemMap k f).app x ≫ (hG.associatedLocalSystemFiberIso k A' e).hom =
      (hG.associatedLocalSystemFiberIso k A e).hom ≫
        (forget₂ (Rep k G) (ModuleCat k)).map f := by
  apply (cancel_epi (hG.associatedLocalSystemFiberIso k A e).inv).1
  ext a
  simp only [Iso.inv_hom_id_assoc, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [associatedLocalSystemFiberIso_inv_apply,
    associatedLocalSystemMap_app_coinvariantsTensorMk,
    associatedLocalSystemFiberIso_hom_coinvariantsTensorMk]
  simp

/-- The fibres of the local system associated to a representation are projective as soon as its
underlying module is projective over `k`, being isomorphic to it. -/
instance projective_associatedLocalSystem_obj (A : Rep.{u} k G) [Module.Projective k A]
    (x : FundamentalGroupoid B) : Projective ((hG.associatedLocalSystem k A).obj x) :=
  have ⟨e, he⟩ := hG.surjective x.as
  Projective.of_iso (hG.associatedLocalSystemFiberIso k A ⟨e, he⟩).symm inferInstance

/-- Evaluation of associated local systems at a point is naturally isomorphic to forgetting
the action, after choosing a sheet over that point. -/
def associatedLocalSystemEvaluationIso {x : FundamentalGroupoid B} (e : p ⁻¹' {x.as}) :
    hG.associatedLocalSystemFunctor k ⋙
        (evaluation (FundamentalGroupoid B) (ModuleCat k)).obj x ≅
      forget₂ (Rep.{u} k G) (ModuleCat k) :=
  NatIso.ofComponents (fun A ↦ hG.associatedLocalSystemFiberIso k A e)
    (fun f ↦ hG.associatedLocalSystemFiberIso_hom_naturality k f e)

/-- The component of the evaluation identification is the chosen fibre identification. -/
@[simp]
lemma associatedLocalSystemEvaluationIso_hom_app {x : FundamentalGroupoid B}
    (e : p ⁻¹' {x.as}) (A : Rep.{u} k G) :
    (hG.associatedLocalSystemEvaluationIso k e).hom.app A =
      (hG.associatedLocalSystemFiberIso k A e).hom :=
  (rfl)

/-- The inverse evaluation identification uses the inverse fibre identification. -/
@[simp]
lemma associatedLocalSystemEvaluationIso_inv_app {x : FundamentalGroupoid B}
    (e : p ⁻¹' {x.as}) (A : Rep.{u} k G) :
    (hG.associatedLocalSystemEvaluationIso k e).inv.app A =
      (hG.associatedLocalSystemFiberIso k A e).inv :=
  (rfl)

/-- Associated local coefficient systems form an additive functor of the representation. -/
instance additive_associatedLocalSystemFunctor : (hG.associatedLocalSystemFunctor k).Additive where
  map_add {X Y} {f g} := by
    apply NatTrans.ext
    funext x
    obtain ⟨e, he⟩ := hG.surjective x.as
    have := Functor.additive_of_iso (hG.associatedLocalSystemEvaluationIso k ⟨e, he⟩).symm
    exact (hG.associatedLocalSystemFunctor k ⋙
      (evaluation (FundamentalGroupoid B) (ModuleCat k)).obj x).map_add

/-- Associated local coefficient systems preserve small limits. -/
instance : PreservesLimitsOfSize.{u, u} (hG.associatedLocalSystemFunctor k) where
  preservesLimitsOfShape {J} _ :=
    preservesLimitsOfShape_of_evaluation _ J fun x ↦ by
      obtain ⟨e, he⟩ := hG.surjective x.as
      exact preservesLimitsOfShape_of_natIso
        (hG.associatedLocalSystemEvaluationIso k ⟨e, he⟩).symm

/-- Associated local coefficient systems preserve small colimits. -/
instance : PreservesColimitsOfSize.{u, u} (hG.associatedLocalSystemFunctor k) where
  preservesColimitsOfShape {J} _ :=
    preservesColimitsOfShape_of_evaluation _ J fun x ↦ by
      obtain ⟨e, he⟩ := hG.surjective x.as
      exact preservesColimitsOfShape_of_natIso
        (hG.associatedLocalSystemEvaluationIso k ⟨e, he⟩).symm

/-- A short exact sequence of representations gives a short exact sequence of associated
local coefficient systems, without flatness assumptions on the representations. -/
lemma shortExact_associatedLocalSystem {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) :
    (S.map (hG.associatedLocalSystemFunctor k)).ShortExact :=
  hS.map_of_exact _

end IsQuotientCoveringMap
