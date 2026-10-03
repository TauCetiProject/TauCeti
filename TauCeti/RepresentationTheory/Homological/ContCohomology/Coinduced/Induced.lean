/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.FiniteIndex
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Functor

/-!
# Smooth discrete induction from an open subgroup

For an open subgroup of a compact group, Mathlib's algebraic induced representation has a
continuous action on its discrete carrier. The finite-index comparison identifies it with
algebraic coinduction, and hence with locally constant topological coinduction. In particular,
this comparison allows continuous Shapiro's lemma to be stated on genuine induced coefficients.

The underlying carrier is Mathlib's `Representation.IndV`, and the representation is exactly
`Representation.ind`. The construction transports continuity through Amelia Livingston's
`Rep.indCoindIso` in `Mathlib.RepresentationTheory.FiniteIndex`; it does not introduce another
algebraic induction model. The coefficient universe contains both the group and ring universes,
as required by the pinned finite-index comparison. The group and ring universes remain
independent, while the coefficient carrier lies in their join.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass
-- Use the same existing decision procedure in public signatures and private proofs.
-- A private helper instance is unavailable when Lean elaborates an exported signature.
attribute [local instance 10000] Classical.decRel

variable (R : Type v) [CommRing R] [TopologicalSpace R]
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (U : OpenSubgroup G)
  (A : SmoothDiscreteTopRep.{v, u, max u v} R U.toSubgroup)

local instance : U.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient

private noncomputable def indCoindLinearEquiv :
    Representation.IndV U.toSubgroup.subtype
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) ≃ₗ[R]
      Representation.coindV U.toSubgroup.subtype
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) :=
  ((forget₂ (Rep R G) (ModuleCat R)).mapIso
    (Rep.indCoindIso.{u, v, u}
      (Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)))).toLinearEquiv

/-- Algebraic induction from an open subgroup, with its discrete topology and continuous
actions. Its carrier is Mathlib's tensor-product coinvariant module `Representation.IndV`. -/
noncomputable abbrev algebraicIndDiscreteRep : DiscreteRep.{v, u, max u v} R G := by
  let e := ((forget₂ (Rep R G) (ModuleCat R)).mapIso
    (Rep.indCoindIso.{u, v, u}
      (Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)))).toLinearEquiv
  let B := algebraicCoindDiscreteRep R G U A
  letI := B.topologicalSpace
  letI := B.discreteTopology
  letI := B.distribMulAction
  letI := B.smulCommClass
  letI := B.continuousSMulRing
  letI := B.continuousSMul
  let V := Representation.IndV U.toSubgroup.subtype
    (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)
  letI : TopologicalSpace V := ⊥
  letI : DiscreteTopology V := ⟨rfl⟩
  letI : DistribMulAction G V := e.toAddEquiv.distribMulAction G
  letI : SMulCommClass G R V := ⟨fun g r x ↦ by
    -- `Equiv.smul_def` uses the equivalence's function fields, while linearity is stated
    -- through `LinearEquiv`. Identify those fields before applying its scalar law.
    change e.symm (g • e (r • x)) = r • e.symm (g • e x)
    rw [e.map_smul, smul_comm, e.symm.map_smul]⟩
  let h : V ≃ₜ B.V :=
    { toEquiv := e.toEquiv
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  letI : ContinuousSMul R V :=
    h.isInducing.continuousSMul continuous_id fun {r x} => by exact e.map_smul r x
  letI : ContinuousSMul G V :=
    h.isInducing.continuousSMul continuous_id fun {g x} => by
      rw [e.toEquiv.smul_def g x]
      exact e.apply_symm_apply _
  exact { V := V }

/-- The continuous induced representation carries Mathlib's genuine induction action. -/
@[simp]
theorem algebraicIndDiscreteRep_ρ :
    (algebraicIndDiscreteRep R G U A).ρ =
      Representation.ind U.toSubgroup.subtype
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  let e := indCoindLinearEquiv R G U A
  apply e.injective
  -- The action on the discrete carrier is transported through `e`; its target action is
  -- identified by the public coinduction equation before using Mathlib's intertwining law.
  change e (e.symm ((algebraicCoindDiscreteRep R G U A).ρ g (e x))) = _
  rw [e.apply_symm_apply, algebraicCoindDiscreteRep_ρ]
  exact (Rep.hom_comm_apply (Rep.indCoindIso.{u, v, u}
    (Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V))).hom g x).symm

/-- Algebraic induction from an open subgroup, regarded as a smooth discrete representation. -/
noncomputable abbrev algebraicIndAsSmooth :
    SmoothDiscreteTopRep.{v, u, max u v} R G :=
  (toSmoothDiscrete R G).obj (algebraicIndDiscreteRep R G U A)

private noncomputable def discreteIndCoindIso :
    algebraicIndDiscreteRep R G U A ≅ algebraicCoindDiscreteRep R G U A where
  hom :=
    { toLinearMap := (indCoindLinearEquiv R G U A).toLinearMap
      isIntertwining' := fun g ↦ LinearMap.ext fun x ↦ by
        rw [algebraicIndDiscreteRep_ρ, algebraicCoindDiscreteRep_ρ]
        exact Rep.hom_comm_apply (Rep.indCoindIso.{u, v, u}
          (Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V))).hom g x }
  inv :=
    { toLinearMap := (indCoindLinearEquiv R G U A).symm.toLinearMap
      isIntertwining' := fun g ↦ LinearMap.ext fun x ↦ by
        rw [algebraicIndDiscreteRep_ρ, algebraicCoindDiscreteRep_ρ]
        exact Rep.hom_comm_apply (Rep.indCoindIso.{u, v, u}
          (Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V))).inv g x }
  hom_inv_id := Representation.IntertwiningMap.ext
    (LinearMap.ext (indCoindLinearEquiv R G U A).symm_apply_apply)
  inv_hom_id := Representation.IntertwiningMap.ext
    (LinearMap.ext (indCoindLinearEquiv R G U A).apply_symm_apply)

/-- Smooth discrete induction and algebraic coinduction agree for an open subgroup, through
Mathlib's finite-index comparison. -/
noncomputable def algebraicIndCoindIso :
    algebraicIndAsSmooth R G U A ≅ algebraicCoindAsSmooth R G U A :=
  (toSmoothDiscrete R G).mapIso (discreteIndCoindIso R G U A)

/-- The smooth-discrete comparison acts by Mathlib's finite-index comparison. -/
@[simp]
theorem algebraicIndCoindIso_hom_apply
    (x : Representation.IndV U.toSubgroup.subtype
      (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)) :
    ((algebraicIndCoindIso R G U A).hom.hom.hom x) =
      (Rep.indCoindIso.{u, v, u}
        (Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V))).hom.hom x := by
  rw [algebraicIndCoindIso, Functor.mapIso_hom, toSmoothDiscrete_map_hom_apply]
  rfl

/-- The inverse smooth-discrete comparison acts by Mathlib's finite-index inverse. -/
@[simp]
theorem algebraicIndCoindIso_inv_apply
    (f : Representation.coindV U.toSubgroup.subtype
      (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)) :
    ((algebraicIndCoindIso R G U A).inv.hom.hom f) =
      (Rep.indCoindIso.{u, v, u}
        (Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V))).inv.hom f := by
  rw [algebraicIndCoindIso, Functor.mapIso_inv, toSmoothDiscrete_map_hom_apply]
  rfl

/-- Algebraic induction from an open subgroup agrees with locally constant topological
coinduction. This assertion requires openness; it is not asserted for infinite-index closed
subgroups. -/
noncomputable def topologicalIndCoindIso :
    algebraicIndAsSmooth R G U A ≅ coindTopRep R G U.toSubgroup A :=
  (algebraicIndCoindIso R G U A).trans (topologicalCoindIsoAlgebraic R G U A).symm

/-- Composing the topological comparison with the topological/algebraic coinduction
comparison recovers Mathlib's finite-index comparison on smooth discrete coefficients. -/
@[reassoc]
theorem topologicalIndCoindIso_hom_comp_topologicalCoindIsoAlgebraic :
    (topologicalIndCoindIso R G U A).hom.hom ≫
      (topologicalCoindIsoAlgebraic R G U A).hom.hom =
        (algebraicIndCoindIso R G U A).hom.hom := by
  have h : (topologicalIndCoindIso R G U A).hom ≫
      (topologicalCoindIsoAlgebraic R G U A).hom = (algebraicIndCoindIso R G U A).hom := by
    simp [topologicalIndCoindIso]
  exact congrArg (fun f ↦ f.hom) h

/-- The induced-coefficient Shapiro counit is finite-index comparison followed by evaluation
at `1`, after restriction to the subgroup. -/
noncomputable def algebraicIndCounit :
    TopRep.res U.toSubgroup.subtype (algebraicIndAsSmooth R G U A).obj ⟶ A.obj :=
  (TopRep.resFunctor U.toSubgroup.subtype).map (algebraicIndCoindIso R G U A).hom.hom ≫
    TopRep.ofHom (algebraicCoindCounit R G U A)

/-- The induced counit is the restricted finite-index comparison followed by algebraic
coinduction's evaluation counit. -/
theorem algebraicIndCounit_def :
    algebraicIndCounit R G U A =
      (TopRep.resFunctor U.toSubgroup.subtype).map (algebraicIndCoindIso R G U A).hom.hom ≫
        TopRep.ofHom (algebraicCoindCounit R G U A) := (rfl)

/-- The induced counit evaluates the finite-index comparison at `1`. -/
@[simp]
theorem algebraicIndCounit_apply
    (x : Representation.IndV U.toSubgroup.subtype
      (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)) :
    (dsimp% only ((algebraicIndCounit R G U A).hom x)) =
      ((Rep.indCoindIso.{u, v, u}
        (Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V))).hom.hom x).1 1 := by
  -- Restriction and categorical composition retain their bundled map wrappers. Reduce just
  -- those wrappers before applying the public comparison and evaluation equations.
  change algebraicCoindCounit R G U A ((algebraicIndCoindIso R G U A).hom.hom.hom x) = _
  exact (algebraicCoindCounit_apply R G U A _).trans
    (congrArg (fun f ↦ f.1 1) (algebraicIndCoindIso_hom_apply R G U A x))

/-- Evaluation of the induced counit on the generator `⟦1 ⊗ a⟧` returns `a`. This fixes the
normalization of induced Shapiro even when the coefficient action is nontrivial. -/
theorem algebraicIndCounit_mk_one (a : A.obj.V) :
    (algebraicIndCounit R G U A).hom
        (Representation.IndV.mk U.toSubgroup.subtype
          (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) 1 a) = a := by
  rw [algebraicIndCounit_apply]
  -- The comparison's linear-map equation does not rewrite the intertwining-map coercion.
  -- Identify that coercion, then compute the canonical generator through `indToCoindAux`.
  change ((Rep.indCoindIso.{u, v, u}
    (Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V))).hom.hom.toLinearMap
    (Representation.IndV.mk U.toSubgroup.subtype
      (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) 1 a)).1 1 = a
  rw [Rep.indCoindIso_hom_hom_toLinearMap]
  simp only [Rep.indToCoind, Representation.IndV.mk, LinearMap.comp_apply,
    Representation.Coinvariants.lift_mk, TensorProduct.mk_apply, TensorProduct.lift.tmul,
    LinearEquiv.coe_coe,
    MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single,
    Finsupp.linearCombination_single, one_smul]
  exact Rep.indToCoindAux_self
    (A := Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)) (1 : G) a

variable {A}
  {B : SmoothDiscreteTopRep.{v, u, max u v} R U.toSubgroup}

private def coefficientMap (f : A ⟶ B) :
    Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) ⟶
      Rep.of (Representation.ofDistribMulAction R U.toSubgroup B.obj.V) :=
  Rep.ofHom
    { toLinearMap := f.hom.hom.toContinuousLinearMap.toLinearMap
      isIntertwining' := fun g ↦ LinearMap.ext fun x ↦ f.hom.hom.isIntertwining g x }

/-- The morphism on smooth discrete induced representations induced by a coefficient
morphism, on the same underlying module as Mathlib's `Rep.indMap`. -/
noncomputable def algebraicIndMap (f : A ⟶ B) :
    algebraicIndAsSmooth R G U A ⟶ algebraicIndAsSmooth R G U B := by
  letI := (algebraicIndDiscreteRep R G U A).topologicalSpace
  letI := (algebraicIndDiscreteRep R G U B).topologicalSpace
  letI := (algebraicIndDiscreteRep R G U A).discreteTopology
  letI := (algebraicIndDiscreteRep R G U B).discreteTopology
  letI := (algebraicIndDiscreteRep R G U A).continuousSMulRing
  letI := (algebraicIndDiscreteRep R G U B).continuousSMulRing
  exact ObjectProperty.homMk (TopRep.ofHom
    { toContinuousLinearMap :=
        ⟨(Rep.indMap U.toSubgroup.subtype (coefficientMap R G U f)).hom.toLinearMap,
          continuous_of_discreteTopology⟩
      isIntertwining' := fun g ↦ by
        apply ContinuousLinearMap.ext
        intro x
        -- The dictionary keeps the underlying carrier and action; identify its action
        -- with the discrete representation before using the native induction equation.
        change (Rep.indMap U.toSubgroup.subtype (coefficientMap R G U f)).hom
          ((algebraicIndDiscreteRep R G U A).ρ g x) =
            (algebraicIndDiscreteRep R G U B).ρ g
              ((Rep.indMap U.toSubgroup.subtype (coefficientMap R G U f)).hom x)
        rw [algebraicIndDiscreteRep_ρ, algebraicIndDiscreteRep_ρ]
        exact Rep.hom_comm_apply (Rep.indMap U.toSubgroup.subtype
          (coefficientMap R G U f)) g x })

/-- The induced coefficient morphism sends `⟦g ⊗ a⟧` to `⟦g ⊗ f(a)⟧`. -/
theorem algebraicIndMap_mk (f : A ⟶ B) (g : G) (a : A.obj.V) :
    (algebraicIndMap R G U f).hom.hom
      (Representation.IndV.mk U.toSubgroup.subtype
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) g a) =
      Representation.IndV.mk U.toSubgroup.subtype
        (Representation.ofDistribMulAction R U.toSubgroup B.obj.V) g (f.hom.hom a) := by
  -- The public map is bundled in two categories; unfold its construction only here to
  -- compute on the canonical tensor generators using Mathlib's induction map.
  change (Rep.indMap U.toSubgroup.subtype (coefficientMap R G U f)).hom
    (Representation.IndV.mk U.toSubgroup.subtype
      (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) g a) = _
  simp [Rep.indMap, coefficientMap, ContIntertwiningMap.toContinuousLinearMap_apply]

/-- Induction on smooth discrete coefficients preserves the identity morphism. -/
@[simp]
theorem algebraicIndMap_id :
    algebraicIndMap R G U (𝟙 A) = 𝟙 (algebraicIndAsSmooth R G U A) := by
  apply ObjectProperty.hom_ext
  apply TopRep.hom_ext
  apply ContIntertwiningMap.toIntertwiningMap_injective
  apply Representation.IntertwiningMap.ext
  apply Representation.IndV.hom_ext
  intro g
  ext a
  -- Extensionality produces a composition of underlying linear maps. Their applications
  -- are the bundled applications characterized by the public generator equation.
  change (algebraicIndMap R G U (𝟙 A)).hom.hom
    (Representation.IndV.mk U.toSubgroup.subtype
      (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) g a) =
      Representation.IndV.mk U.toSubgroup.subtype
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) g a
  simpa only [ObjectProperty.FullSubcategory.id_hom, TopRep.hom_id,
    ContIntertwiningMap.id_apply] using algebraicIndMap_mk R G U (𝟙 A) g a

/-- Induction on smooth discrete coefficients preserves composition. -/
@[reassoc]
theorem algebraicIndMap_comp
    {C : SmoothDiscreteTopRep.{v, u, max u v} R U.toSubgroup}
    (f : A ⟶ B) (g : B ⟶ C) :
    algebraicIndMap R G U (f ≫ g) =
      algebraicIndMap R G U f ≫ algebraicIndMap R G U g := by
  apply ObjectProperty.hom_ext
  apply TopRep.hom_ext
  apply ContIntertwiningMap.toIntertwiningMap_injective
  apply Representation.IntertwiningMap.ext
  apply Representation.IndV.hom_ext
  intro x
  ext a
  -- As for identity, remove just the linear-map projection wrappers introduced by
  -- extensionality, and use the public formula on the native tensor generators.
  change (algebraicIndMap R G U (f ≫ g)).hom.hom
    (Representation.IndV.mk U.toSubgroup.subtype
      (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) x a) =
      (algebraicIndMap R G U g).hom.hom ((algebraicIndMap R G U f).hom.hom
        (Representation.IndV.mk U.toSubgroup.subtype
          (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) x a))
  simp only [algebraicIndMap_mk, ObjectProperty.FullSubcategory.comp_hom,
    TopRep.hom_comp]
  rfl

/-- The evaluation counit on induced coefficients is natural in the original coefficients. -/
@[reassoc]
theorem algebraicIndCounit_naturality (f : A ⟶ B) :
    (TopRep.resFunctor U.toSubgroup.subtype).map (algebraicIndMap R G U f).hom ≫
        algebraicIndCounit R G U B = algebraicIndCounit R G U A ≫ f.hom := by
  ext x
  let a := Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)
  let b := Rep.of (Representation.ofDistribMulAction R U.toSubgroup B.obj.V)
  have h := (Rep.indCoindNatIso.{u, v, u} R U.toSubgroup).hom.naturality
    (coefficientMap R G U f)
  have h' := congrArg (fun m : Rep.ind U.toSubgroup.subtype a ⟶
      Rep.coind U.toSubgroup.subtype b ↦ (m.hom x).1 1) h
  -- Restriction and composition introduce only map wrappers, and the two counit equations
  -- turn their values into the native finite-index naturality square at `1`.
  change algebraicCoindCounit R G U B
    ((algebraicIndCoindIso R G U B).hom.hom.hom
      ((Rep.indMap U.toSubgroup.subtype (coefficientMap R G U f)).hom x)) =
    f.hom.hom (algebraicCoindCounit R G U A
      ((algebraicIndCoindIso R G U A).hom.hom.hom x))
  let y := (Rep.indMap U.toSubgroup.subtype (coefficientMap R G U f)).hom x
  have heq := (algebraicCoindCounit_apply R G U B
    ((algebraicIndCoindIso R G U B).hom.hom.hom y)).trans
    (congrArg (fun z ↦ z.1 1) (algebraicIndCoindIso_hom_apply R G U B y))
  rw [heq]
  have heq' := (algebraicCoindCounit_apply R G U A
    ((algebraicIndCoindIso R G U A).hom.hom.hom x)).trans
    (congrArg (fun z ↦ z.1 1) (algebraicIndCoindIso_hom_apply R G U A x))
  rw [heq']
  -- Mathlib's naturality is stated as an equality of bundled representation morphisms;
  -- identify its value at `1` with the pointwise coinduced map before using it.
  change ((Rep.indCoindIso.{u, v, u} b).hom.hom
    ((Rep.indMap U.toSubgroup.subtype (coefficientMap R G U f)).hom x)).1 1 =
      (coefficientMap R G U f).hom (((Rep.indCoindIso.{u, v, u} a).hom.hom x).1 1) at h'
  exact h'

end TauCeti
