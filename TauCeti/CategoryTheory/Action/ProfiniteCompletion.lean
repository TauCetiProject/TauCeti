/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Galois.Examples
public import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
public import TauCeti.Topology.Algebra.Group.Profinite.Completion

/-!
# Profinite completion and finite group actions

The action of an abstract group `G` on a finite set extends uniquely and continuously to the
profinite completion of `G`. These extensions are natural in the finite `G`-set, and together
exhibit the profinite completion as the fundamental group of the forgetful fibre functor from
finite `G`-sets.

## Main declarations

* `TauCeti.ProfiniteCompletion.continuousActionHom`: the continuous permutation representation
  extending a finite `G`-action.
* `TauCeti.ProfiniteCompletion.etaFn_smul`: the extended action restricts to the original action
  along the canonical map from `G`.
* `TauCeti.ProfiniteCompletion.instIsFundamentalGroup`: the profinite completion is a fundamental
  group of the forgetful functor on finite `G`-sets.
* `TauCeti.ProfiniteCompletion.autForgetFiniteActionMulEquiv`: the resulting canonical
  isomorphism with the automorphism group of the forgetful functor.

The construction uses Mathlib's profinite completion and its universal property.
-/

public section
noncomputable section

open CategoryTheory
open scoped CategoryTheory.PreGaloisCategory
open CategoryTheory.Limits

universe u

namespace TauCeti.ProfiniteCompletion

variable (G : Type u) [Group G]

/-- The continuous permutation representation of the profinite completion extending a finite
`G`-action. -/
def continuousActionHom (A : Action FintypeCat.{u} G) :
    ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) ⟶
      ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Equiv.Perm A.V)) :=
  ProfiniteGrp.ProfiniteCompletion.lift
    (P := ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Equiv.Perm A.V)))
    (GrpCat.ofHom (MulAction.toPermHom G A.V))

/-- The permutation representation of the profinite completion extending a finite `G`-action. -/
def actionHom (A : Action FintypeCat.{u} G) :
    ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →* Equiv.Perm A.V := by
  let f := (continuousActionHom G A).hom.toMonoidHom
  -- `ofFiniteGrp` hides its discrete underlying permutation group.
  change ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →* Equiv.Perm A.V at f
  exact f

/-- The extended continuous representation restricts along the canonical morphism `G → Ĝ` to the
original permutation representation. -/
@[simp]
theorem continuousActionHom_eta (A : Action FintypeCat.{u} G) :
    ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of G) ≫
        (forget₂ ProfiniteGrp GrpCat).map (continuousActionHom G A) =
      GrpCat.ofHom (MulAction.toPermHom G A.V) :=
  ProfiniteGrp.ProfiniteCompletion.lift_eta _

/-- The canonical action of the profinite completion of `G` on a finite `G`-set. -/
@[instance_reducible]
def mulAction (A : Action FintypeCat.{u} G) : MulAction
    (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)) A.V where
  smul g x := actionHom G A g x
  one_smul x := by
    -- Expose the action's defining permutation so that the homomorphism law applies.
    change actionHom G A 1 x = x
    rw [map_one (actionHom G A)]
    rfl
  mul_smul g h x := by
    -- Expose the action's defining permutation so that the homomorphism law applies.
    change actionHom G A (g * h) x = actionHom G A g (actionHom G A h x)
    rw [map_mul (actionHom G A) g h]
    rfl

/-- The profinite completion acts on every finite `G`-set. -/
instance instMulAction (A : Action FintypeCat.{u} G) : MulAction
    (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)) A.V :=
  mulAction G A

/-- The profinite-completion action, in the exact form expected by the forgetful functor. -/
instance instMulActionForgetObj (A : Action FintypeCat.{u} G) : MulAction
    (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G))
    ((Action.forget FintypeCat G).obj A) :=
  mulAction G A

/-- The extended permutation representation restricts along `G → Ĝ` to the original one. -/
@[simp]
theorem actionHom_etaFn (A : Action FintypeCat.{u} G) (g : G) :
    actionHom G A (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) =
      MulAction.toPermHom G A.V g := by
  have h := ConcreteCategory.congr_hom (continuousActionHom_eta G A) g
  -- `continuousActionHom_eta` presents the restriction as a composite of bundled group
  -- homomorphisms.
  change actionHom G A (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) =
    MulAction.toPermHom G A.V g at h
  exact h

/-- The extended action restricts along the canonical map `G → Ĝ` to the original action. -/
@[simp]
theorem etaFn_smul (A : Action FintypeCat.{u} G) (g : G) (x : A.V) :
    ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g • x = g • x := by
  -- Unfold only the registered action, leaving the completion construction opaque.
  change actionHom G A (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) x = g • x
  rw [actionHom_etaFn]
  rfl

/-- The restriction formula for the action carried by the forgetful functor. -/
@[simp]
theorem etaFn_smul_forget (A : Action FintypeCat.{u} G) (g : G)
    (x : (Action.forget FintypeCat G).obj A) :
    ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g • x =
      ConcreteCategory.hom (A.ρ g) x := by
  -- `Action.forget` hides the underlying finite type and hence the registered action.
  change actionHom G A (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) x =
    ConcreteCategory.hom (A.ρ g) x
  rw [actionHom_etaFn]
  rfl

/-- The extended permutation representation is continuous, the finite permutation group carrying
the discrete topology. -/
theorem continuous_actionHom (A : Action FintypeCat.{u} G) :
    @Continuous (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G))
      (Equiv.Perm A.V) inferInstance ⊥ (actionHom G A) :=
  -- `ofFiniteGrp` hides its discrete underlying permutation group.
  (continuousActionHom G A).hom.continuous_toFun

/-- The extended action on a finite `G`-set is continuous when the set has the discrete
topology. -/
theorem continuousSMul (A : Action FintypeCat.{u} G) :
    @ContinuousSMul
      (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)) A.V
      inferInstance inferInstance ⊥ := by
  let _ : TopologicalSpace A.V := ⊥
  let _ : DiscreteTopology A.V := ⟨rfl⟩
  let _ : TopologicalSpace (Equiv.Perm A.V) := ⊥
  let _ : DiscreteTopology (Equiv.Perm A.V) := ⟨rfl⟩
  refine ⟨?_⟩
  -- The class projection does not unfold the deliberately reducible action instance.
  change Continuous fun p :
    ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) × A.V =>
      actionHom G A p.1 p.2
  have hf : Continuous (actionHom G A) := continuous_actionHom G A
  have heval : Continuous (fun p : Equiv.Perm A.V × A.V => p.1 p.2) :=
    continuous_of_discreteTopology
  exact heval.comp (hf.prodMap (continuous_id : Continuous (id : A.V → A.V)))

/-- The profinite-completion actions on finite `G`-sets are natural in equivariant maps. -/
instance instIsNaturalSMul : CategoryTheory.PreGaloisCategory.IsNaturalSMul
    (Action.forget FintypeCat.{u} G)
    (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)) where
  naturality g {A B} f x := by
    let _ : TopologicalSpace A.V := ⊥
    let _ : DiscreteTopology A.V := ⟨rfl⟩
    let _ : TopologicalSpace B.V := ⊥
    let _ : DiscreteTopology B.V := ⟨rfl⟩
    let hA := continuousSMul G A
    let hB := continuousSMul G B
    have hAx : Continuous (fun a :
        ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) => a • x) :=
      hA.continuous_smul.comp (continuous_id.prodMk continuous_const)
    have hBx : Continuous (fun a :
        ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) => a • f.hom x) :=
      hB.continuous_smul.comp (continuous_id.prodMk continuous_const)
    have hfun :
        (fun a : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) => f.hom (a • x)) =
          (fun a => a • f.hom x) :=
      (ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of G)).equalizer
        (continuous_of_discreteTopology.comp hAx) hBx (funext fun a => by
          -- Reveal both extended actions beneath `Action.forget` before using equivariance.
          change f.hom (actionHom G A
            (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) a) x) =
            actionHom G B (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) a) (f.hom x)
          rw [actionHom_etaFn, actionHom_etaFn]
          exact ConcreteCategory.congr_hom (f.comm a) x)
    exact congrFun hfun g

/-- On a connected finite `G`-set, the profinite-completion action is transitive. -/
theorem isPretransitive_of_isConnected (A : Action FintypeCat.{u} G)
    [CategoryTheory.PreGaloisCategory.IsConnected A] :
    MulAction.IsPretransitive
      (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)) A.V where
  exists_smul_eq x y := by
    let _ := CategoryTheory.FintypeCat.Action.pretransitive_of_isConnected G A
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
    exact ⟨ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g, by
      rw [etaFn_smul]
      exact hg⟩

/-- On the finite quotient by `H`, acting on the identity coset reads the `H`-coordinate of
an element of the profinite completion. -/
theorem actionHom_one_quotient (H : FiniteIndexNormalSubgroup G)
    (g : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)) :
    let A : Action FintypeCat.{u} G := G ⧸ₐ H.toSubgroup
    actionHom G A g (1 : G ⧸ H.toSubgroup) = coordinateHom G H g := by
  let A : Action FintypeCat.{u} G := G ⧸ₐ H.toSubgroup
  let _ : TopologicalSpace (G ⧸ H.toSubgroup) := ⊥
  let _ : DiscreteTopology (G ⧸ H.toSubgroup) := ⟨rfl⟩
  let _ : TopologicalSpace A.V := ⊥
  let _ : DiscreteTopology A.V := ⟨rfl⟩
  let _ : TopologicalSpace (Equiv.Perm A.V) := ⊥
  let _ : DiscreteTopology (Equiv.Perm A.V) := ⟨rfl⟩
  have hl : Continuous (fun z :
      ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) =>
        actionHom G A z (1 : G ⧸ H.toSubgroup)) := by
    have hf : Continuous (actionHom G A) := continuous_actionHom G A
    have heval : Continuous (fun e : Equiv.Perm A.V =>
        e (1 : G ⧸ H.toSubgroup)) := continuous_of_discreteTopology
    exact heval.comp hf
  have hr : Continuous (fun z :
      ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) => coordinateHom G H z) :=
    continuous_coordinateHom G H
  have hfun := (ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of G)).equalizer
    hl hr (funext fun a => by
      simp only [Function.comp_apply]
      -- Reveal the extended action on the dense canonical image.
      change actionHom G A (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) a)
          (1 : G ⧸ H.toSubgroup) =
        coordinateHom G H (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) a)
      rw [actionHom_etaFn, coordinateHom_etaFn]
      exact mul_one (QuotientGroup.mk a : G ⧸ H.toSubgroup))
  exact congrFun hfun g

/-- An element of the profinite completion acting trivially on every finite `G`-set is the
identity. The regular actions on the finite quotients detect all coordinates of the limit. -/
theorem eq_one_of_forall_smul_eq
    (g : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G))
    (h : ∀ (A : Action FintypeCat.{u} G)
      (x : (Action.forget FintypeCat G).obj A), g • x = x) :
    g = 1 := by
  apply ProfiniteGrp.limit_ext
  intro H
  -- `limit_ext` presents the coordinate as a bundled cone projection.
  change coordinateHom G H g = 1
  let A : Action FintypeCat.{u} G := G ⧸ₐ H.toSubgroup
  have hg := h A (1 : G ⧸ H.toSubgroup)
  -- Reveal the finite-quotient action beneath the forgetful functor.
  change actionHom G A g (1 : G ⧸ H.toSubgroup) =
    (1 : G ⧸ H.toSubgroup) at hg
  rw [actionHom_one_quotient] at hg
  exact hg

/-- The profinite completion of `G` is a fundamental group of the forgetful fibre functor on
finite `G`-sets. -/
instance instIsFundamentalGroup : CategoryTheory.PreGaloisCategory.IsFundamentalGroup
    (Action.forget FintypeCat.{u} G)
    (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)) where
  naturality := CategoryTheory.PreGaloisCategory.IsNaturalSMul.naturality
  transitive_of_isGalois A := isPretransitive_of_isConnected G A
  continuous_smul A := continuousSMul G A
  non_trivial' g h := eq_one_of_forall_smul_eq G g h

/-- The profinite completion of `G` is canonically isomorphic to the automorphism group of the
forgetful fibre functor on finite `G`-sets. -/
noncomputable def autForgetFiniteActionMulEquiv :
    ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) ≃*
      Aut (Action.forget FintypeCat.{u} G) :=
  CategoryTheory.PreGaloisCategory.toAutMulEquiv
    (Action.forget FintypeCat.{u} G)
    (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G))

/-- Under `autForgetFiniteActionMulEquiv`, an element of the profinite completion acts on every
finite `G`-set by its extended action. -/
@[simp]
theorem autForgetFiniteActionMulEquiv_hom_app_apply
    (g : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G))
    (A : Action FintypeCat.{u} G) (x : (Action.forget FintypeCat G).obj A) :
    (autForgetFiniteActionMulEquiv G g).hom.app A x = g • x := by
  -- Reveal the `toAut` homomorphism packaged by `toAutMulEquiv`.
  change (CategoryTheory.PreGaloisCategory.toAut
    (Action.forget FintypeCat.{u} G)
    (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)) g).hom.app A x = _
  rw [CategoryTheory.PreGaloisCategory.toAut_hom_app_apply]

/-- The canonical isomorphism with the automorphism group of the forgetful functor is a
homeomorphism. -/
theorem autForgetFiniteActionMulEquiv_isHomeomorph :
    IsHomeomorph (autForgetFiniteActionMulEquiv G) :=
  CategoryTheory.PreGaloisCategory.toAutMulEquiv_isHomeomorph _ _

end TauCeti.ProfiniteCompletion
