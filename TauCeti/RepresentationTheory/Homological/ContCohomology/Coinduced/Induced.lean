/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.FiniteIndex
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
independent, while the coefficient carrier may lie in any larger universe.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v w

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass
-- Use the same existing decision procedure in public signatures and private proofs.
-- A private helper instance is unavailable when Lean elaborates an exported signature.
attribute [local instance 10000] Classical.decRel

variable (R : Type v) [CommRing R] [TopologicalSpace R]
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (U : OpenSubgroup G)
  (A : SmoothDiscreteTopRep.{v, u, max u v w} R U.toSubgroup)

local instance : U.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient

/-- Algebraic induction from an open subgroup, with discrete topology and continuous
scalar and group actions transported along Mathlib's finite-index comparison. -/
noncomputable abbrev algebraicIndDiscreteRep : DiscreteRep.{v, u, max u v w} R G := by
  let B := Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)
  let C := algebraicCoindDiscreteRep R G U A
  letI : TopologicalSpace (Rep.coind U.toSubgroup.subtype B) := C.topologicalSpace
  letI : DiscreteTopology (Rep.coind U.toSubgroup.subtype B) := C.discreteTopology
  letI : DistribMulAction G (Rep.coind U.toSubgroup.subtype B) := C.distribMulAction
  letI : SMulCommClass G R (Rep.coind U.toSubgroup.subtype B) := C.smulCommClass
  letI : ContinuousSMul R (Rep.coind U.toSubgroup.subtype B) := C.continuousSMulRing
  letI : ContinuousSMul G (Rep.coind U.toSubgroup.subtype B) := C.continuousSMul
  let eRep := Representation.equivOfIso (Rep.indCoindIso.{max u w, v, u} B)
  let e := eRep.toLinearEquiv
  let V := Representation.IndV U.toSubgroup.subtype B.ρ
  letI : TopologicalSpace V := ⊥
  letI : DiscreteTopology V := ⟨rfl⟩
  let ρ := Representation.ind U.toSubgroup.subtype B.ρ
  letI : DistribMulAction G V := DistribMulAction.compHom V ρ
  letI : SMulCommClass G R V := ⟨fun g r x ↦ (ρ g).map_smul r x⟩
  let h : V ≃ₜ C.V :=
    { toEquiv := e.toEquiv
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  letI : ContinuousSMul R V :=
    h.isInducing.continuousSMul continuous_id fun {r x} ↦ e.map_smul r x
  letI : ContinuousSMul G V :=
    h.isInducing.continuousSMul continuous_id fun {g x} ↦ by
      exact (eRep.toIntertwiningMap.isIntertwining _ _ g x).trans
          (LinearMap.congr_fun (DFunLike.congr_fun (algebraicCoindDiscreteRep_ρ R G U A) g)
            (e x)).symm
  exact { V := V }

/-- The smooth discrete induced representation carries Mathlib's algebraic induced action. -/
@[simp]
theorem algebraicIndDiscreteRep_ρ :
    (algebraicIndDiscreteRep.{u, v, w} R G U A).ρ =
      Representation.ind U.toSubgroup.subtype
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) := (rfl)

/-- Algebraic induction from an open subgroup, regarded as a smooth discrete topological
representation on its tensor-coinvariant carrier. -/
noncomputable abbrev algebraicIndAsSmooth : SmoothDiscreteTopRep.{v, u, max u v w} R G :=
  (toSmoothDiscrete R G).obj (algebraicIndDiscreteRep.{u, v, w} R G U A)

/-- Mathlib's finite-index comparison as an isomorphism of discrete representations. -/
private noncomputable def discreteIndCoindIso :
    algebraicIndDiscreteRep.{u, v, w} R G U A ≅ algebraicCoindDiscreteRep R G U A := by
  let B := Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)
  let e := Representation.equivOfIso (Rep.indCoindIso.{max u w, v, u} B)
  refine
    { hom := { toLinearMap := Rep.indToCoind B, isIntertwining' := ?_ }
      inv := { toLinearMap := Rep.coindToInd B, isIntertwining' := ?_ }
      hom_inv_id := Representation.IntertwiningMap.ext (Rep.indToCoind_coindToInd B)
      inv_hom_id := Representation.IntertwiningMap.ext (Rep.coindToInd_indToCoind B) }
  · intro g
    rw [algebraicIndDiscreteRep_ρ, algebraicCoindDiscreteRep_ρ]
    rw [← Rep.indCoindIso_hom_hom_toLinearMap.{max u w, v, u} B]
    exact e.toIntertwiningMap.isIntertwining' g
  · intro g
    rw [algebraicIndDiscreteRep_ρ, algebraicCoindDiscreteRep_ρ]
    exact e.symm.toIntertwiningMap.isIntertwining' g

/-- Smooth discrete induction and algebraic coinduction agree for an open subgroup, through
Mathlib's finite-index comparison. -/
noncomputable def algebraicIndCoindIso :
    algebraicIndAsSmooth.{u, v, w} R G U A ≅ algebraicCoindAsSmooth R G U A :=
  (toSmoothDiscrete R G).mapIso (discreteIndCoindIso.{u, v, w} R G U A)

/-- The smooth-discrete comparison acts by Mathlib's finite-index comparison. -/
@[simp]
theorem algebraicIndCoindIso_hom_apply
    (x : Representation.IndV U.toSubgroup.subtype
      (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)) :
    ((algebraicIndCoindIso.{u, v, w} R G U A).hom.hom.hom x) =
      (Rep.indCoindIso.{max u w, v, u}
        (Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V))).hom.hom x := by
  rw [algebraicIndCoindIso, Functor.mapIso_hom, toSmoothDiscrete_map_hom_apply]
  exact (LinearMap.congr_fun (Rep.indCoindIso_hom_hom_toLinearMap.{max u w, v, u}
    (Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V))) x).symm

/-- The inverse smooth-discrete comparison acts by Mathlib's finite-index inverse. -/
@[simp]
theorem algebraicIndCoindIso_inv_apply
    (f : Representation.coindV U.toSubgroup.subtype
      (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)) :
    ((algebraicIndCoindIso.{u, v, w} R G U A).inv.hom.hom f) =
      (Rep.indCoindIso.{max u w, v, u}
        (Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V))).inv.hom f := by
  rw [algebraicIndCoindIso, Functor.mapIso_inv, toSmoothDiscrete_map_hom_apply]
  exact (LinearMap.congr_fun (Rep.indCoindIso_inv_hom_toLinearMap.{max u w, v, u}
    (Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V))) f).symm

/-- On a tensor generator, the comparison is the equivariant function supported on its
right coset, with value `a` at `g`. -/
-- Use this auxiliary-function formula for explicit rewriting: `simp` already rewrites the
-- comparison through `algebraicIndCoindIso_hom_apply`, and the formula exposes decidability.
theorem algebraicIndCoindIso_hom_mk_apply (g h : G) (a : A.obj.V) :
    (dsimp% only [Representation.IndV.mk, LinearMap.coe_comp,
      Function.comp_apply, TensorProduct.mk_apply]
      ((algebraicIndCoindIso.{u, v, w} R G U A).hom.hom.hom
      (Representation.IndV.mk U.toSubgroup.subtype
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) g a)).1 h) =
      Rep.indToCoindAux (Rep.of
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)) g a h := by
  rw [algebraicIndCoindIso_hom_apply]
  exact congrFun (indToCoind_mk
    (A := Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)) g a) h

/-- Algebraic induction from an open subgroup agrees with locally constant topological
coinduction. This assertion requires openness; it is not asserted for infinite-index closed
subgroups. -/
noncomputable def topologicalIndCoindIso :
    algebraicIndAsSmooth.{u, v, w} R G U A ≅ coindTopRep R G U.toSubgroup A :=
  (algebraicIndCoindIso.{u, v, w} R G U A).trans (topologicalCoindIsoAlgebraic R G U A).symm

/-- Composing the topological comparison with the topological/algebraic coinduction
comparison recovers Mathlib's finite-index comparison on smooth discrete coefficients. -/
@[reassoc]
theorem topologicalIndCoindIso_hom_comp_topologicalCoindIsoAlgebraic :
    (topologicalIndCoindIso.{u, v, w} R G U A).hom.hom ≫
      (topologicalCoindIsoAlgebraic R G U A).hom.hom =
        (algebraicIndCoindIso.{u, v, w} R G U A).hom.hom := by
  have h : (topologicalIndCoindIso.{u, v, w} R G U A).hom ≫
      (topologicalCoindIsoAlgebraic R G U A).hom =
        (algebraicIndCoindIso.{u, v, w} R G U A).hom := by
    simp [topologicalIndCoindIso]
  exact congrArg (fun f ↦ f.hom) h

/-- The locally constant comparison sends a tensor generator to the equivariant function
supported on its right coset. -/
-- Name the `DiscreteCoind` carrier before applying its function coercion: the smooth-discrete
-- dictionary presents the codomain as a bundled `TopRep`, as in the coinduction comparison API.
-- Keep this auxiliary-function formula out of `simp`: it introduces a chosen decidability
-- instance and shadows the direct normalization below.
theorem topologicalIndCoindIso_hom_mk_apply (g h : G) (a : A.obj.V) :
    (show DiscreteCoind G U.toSubgroup A.obj.V from
      (topologicalIndCoindIso.{u, v, w} R G U A).hom.hom.hom
      (Representation.IndV.mk U.toSubgroup.subtype
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) g a)) h =
      Rep.indToCoindAux (Rep.of
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)) g a h := by
  -- The composite comparison acts by function composition on the underlying carriers.
  -- Its second factor leaves all values unchanged, so use the two public computation lemmas.
  exact (topologicalCoindIsoAlgebraic_inv_hom_hom_apply_coe R G U A
    ((algebraicIndCoindIso.{u, v, w} R G U A).hom.hom.hom
      (Representation.IndV.mk U.toSubgroup.subtype
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) g a)) h).trans
          (algebraicIndCoindIso_hom_mk_apply.{u, v, w} R G U A g h a)

/-- The tensor generator at `g` maps to a locally constant function taking value `a` at `g`.
This computation avoids exposing the decidability instance in Mathlib's auxiliary function. -/
@[simp]
theorem topologicalIndCoindIso_hom_mk_self (g : G) (a : A.obj.V) :
    -- Normalize the generator and name the locally constant carrier, as above.
    (dsimp% only [Representation.IndV.mk, LinearMap.coe_comp,
      Function.comp_apply, TensorProduct.mk_apply] (show DiscreteCoind G U.toSubgroup A.obj.V from
      (topologicalIndCoindIso.{u, v, w} R G U A).hom.hom.hom
        (Representation.IndV.mk U.toSubgroup.subtype
          (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) g a)) g) = a := by
  exact (topologicalIndCoindIso_hom_mk_apply.{u, v, w} R G U A g g a).trans
    (Rep.indToCoindAux_self (A := Rep.of
      (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)) g a)

/-- The induced-coefficient Shapiro counit is finite-index comparison followed by evaluation
at `1`, after restriction to the subgroup. -/
noncomputable def algebraicIndCounit :
    TopRep.res U.toSubgroup.subtype (algebraicIndAsSmooth.{u, v, w} R G U A).obj ⟶ A.obj :=
  (TopRep.resFunctor U.toSubgroup.subtype).map (algebraicIndCoindIso.{u, v, w} R G U A).hom.hom ≫
    TopRep.ofHom (algebraicCoindCounit R G U A)

/-- The induced counit is the restricted finite-index comparison followed by algebraic
coinduction's evaluation counit. -/
theorem algebraicIndCounit_def :
    algebraicIndCounit.{u, v, w} R G U A =
      (TopRep.resFunctor U.toSubgroup.subtype).map
        (algebraicIndCoindIso.{u, v, w} R G U A).hom.hom ≫
        TopRep.ofHom (algebraicCoindCounit R G U A) := (rfl)

/-- The induced counit evaluates the finite-index comparison at `1`. -/
@[simp]
theorem algebraicIndCounit_apply
    (x : Representation.IndV U.toSubgroup.subtype
      (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)) :
    (dsimp% only ((algebraicIndCounit.{u, v, w} R G U A).hom x)) =
      ((Rep.indCoindIso.{max u w, v, u}
        (Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V))).hom.hom x).1 1 := by
  -- Restriction and categorical composition retain their bundled map wrappers. Reduce just
  -- those wrappers before applying the public comparison and evaluation equations.
  change algebraicCoindCounit R G U A ((algebraicIndCoindIso.{u, v, w} R G U A).hom.hom.hom x) = _
  exact (algebraicCoindCounit_apply R G U A _).trans
    (congrArg (fun f ↦ f.1 1) (algebraicIndCoindIso_hom_apply.{u, v, w} R G U A x))

/-- Evaluation of the induced counit on the generator `⟦1 ⊗ a⟧` returns `a`. This fixes the
normalization of induced Shapiro even when the coefficient action is nontrivial. -/
-- Use this generator equation for explicit rewriting: `simp` already rewrites the counit
-- through `algebraicIndCounit_apply`, so this equation is not in simp normal form.
theorem algebraicIndCounit_mk_one (a : A.obj.V) :
    (algebraicIndCounit.{u, v, w} R G U A).hom
        (Representation.IndV.mk U.toSubgroup.subtype
          (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) 1 a) = a := by
  -- As in `algebraicIndCounit_apply`, reduce the restriction and composition wrappers to
  -- apply the coinduction counit's evaluation API and the comparison's generator formula.
  change algebraicCoindCounit R G U A ((algebraicIndCoindIso.{u, v, w} R G U A).hom.hom.hom
    (Representation.IndV.mk U.toSubgroup.subtype
      (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) 1 a)) = a
  exact (algebraicCoindCounit_apply R G U A _).trans
    ((algebraicIndCoindIso_hom_mk_apply.{u, v, w} R G U A 1 1 a).trans
      (Rep.indToCoindAux_self
        (A := Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)) (1 : G) a))

variable {A}
  {B : SmoothDiscreteTopRep.{v, u, max u v w} R U.toSubgroup}

private def coefficientMap (f : A ⟶ B) :
    Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) ⟶
      Rep.of (Representation.ofDistribMulAction R U.toSubgroup B.obj.V) :=
  Rep.ofHom
    { toLinearMap := f.hom.hom.toContinuousLinearMap.toLinearMap
      isIntertwining' := fun g ↦ LinearMap.ext fun x ↦ f.hom.hom.isIntertwining g x }

/-- The morphism on smooth discrete induced representations induced by a coefficient
morphism, on the same underlying module as Mathlib's `Rep.indMap`. -/
noncomputable def algebraicIndMap (f : A ⟶ B) :
    algebraicIndAsSmooth.{u, v, w} R G U A ⟶ algebraicIndAsSmooth.{u, v, w} R G U B := by
  letI := (algebraicIndDiscreteRep.{u, v, w} R G U A).topologicalSpace
  letI := (algebraicIndDiscreteRep.{u, v, w} R G U B).topologicalSpace
  letI := (algebraicIndDiscreteRep.{u, v, w} R G U A).discreteTopology
  letI := (algebraicIndDiscreteRep.{u, v, w} R G U B).discreteTopology
  letI := (algebraicIndDiscreteRep.{u, v, w} R G U A).continuousSMulRing
  letI := (algebraicIndDiscreteRep.{u, v, w} R G U B).continuousSMulRing
  exact ObjectProperty.homMk (TopRep.ofHom
    { toContinuousLinearMap :=
        ⟨(Rep.indMap U.toSubgroup.subtype (coefficientMap.{u, v, w} R G U f)).hom.toLinearMap,
          continuous_of_discreteTopology⟩
      isIntertwining' := fun g ↦ by
        apply ContinuousLinearMap.ext
        intro x
        -- The dictionary keeps the underlying carrier and action; identify its action
        -- with the discrete representation before using the native induction equation.
        change (Rep.indMap U.toSubgroup.subtype (coefficientMap.{u, v, w} R G U f)).hom
          ((algebraicIndDiscreteRep.{u, v, w} R G U A).ρ g x) =
            (algebraicIndDiscreteRep.{u, v, w} R G U B).ρ g
              ((Rep.indMap U.toSubgroup.subtype (coefficientMap.{u, v, w} R G U f)).hom x)
        rw [algebraicIndDiscreteRep_ρ, algebraicIndDiscreteRep_ρ]
        exact Rep.hom_comm_apply (Rep.indMap U.toSubgroup.subtype
          (coefficientMap.{u, v, w} R G U f)) g x })

/-- The induced coefficient morphism sends `⟦g ⊗ a⟧` to `⟦g ⊗ f(a)⟧`. -/
@[simp]
theorem algebraicIndMap_mk (f : A ⟶ B) (g : G) (a : A.obj.V) :
    (dsimp% only [Representation.IndV.mk, LinearMap.coe_comp,
      Function.comp_apply, TensorProduct.mk_apply] (algebraicIndMap.{u, v, w} R G U f).hom.hom
      (Representation.IndV.mk U.toSubgroup.subtype
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) g a)) =
      (dsimp% only [Representation.IndV.mk, LinearMap.coe_comp,
        Function.comp_apply, TensorProduct.mk_apply] Representation.IndV.mk U.toSubgroup.subtype
        (Representation.ofDistribMulAction R U.toSubgroup B.obj.V) g (f.hom.hom a)) := by
  -- The public map is bundled in two categories; unfold its construction only here to
  -- compute on the canonical tensor generators using Mathlib's induction map.
  change (Rep.indMap U.toSubgroup.subtype (coefficientMap.{u, v, w} R G U f)).hom
    (Representation.IndV.mk U.toSubgroup.subtype
      (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) g a) = _
  simp [Rep.indMap, coefficientMap, ContIntertwiningMap.toContinuousLinearMap_apply]

/-- Induction on smooth discrete coefficients preserves the identity morphism. -/
@[simp]
theorem algebraicIndMap_id :
    algebraicIndMap.{u, v, w} R G U (𝟙 A) = 𝟙 (algebraicIndAsSmooth.{u, v, w} R G U A) := by
  apply ObjectProperty.hom_ext
  apply TopRep.hom_ext
  apply ContIntertwiningMap.toIntertwiningMap_injective
  apply Representation.IntertwiningMap.ext
  apply Representation.IndV.hom_ext
  intro g
  ext a
  -- Extensionality produces a composition of underlying linear maps. Their applications
  -- are the bundled applications characterized by the public generator equation.
  change (algebraicIndMap.{u, v, w} R G U (𝟙 A)).hom.hom
    (Representation.IndV.mk U.toSubgroup.subtype
      (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) g a) =
      Representation.IndV.mk U.toSubgroup.subtype
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) g a
  dsimp only [Representation.IndV.mk, LinearMap.coe_comp,
    Function.comp_apply, TensorProduct.mk_apply]
  rw [algebraicIndMap_mk]
  rfl

/-- Induction on smooth discrete coefficients preserves composition. -/
@[reassoc]
theorem algebraicIndMap_comp
    {C : SmoothDiscreteTopRep.{v, u, max u v w} R U.toSubgroup}
    (f : A ⟶ B) (g : B ⟶ C) :
    algebraicIndMap.{u, v, w} R G U (f ≫ g) =
      algebraicIndMap.{u, v, w} R G U f ≫ algebraicIndMap.{u, v, w} R G U g := by
  apply ObjectProperty.hom_ext
  apply TopRep.hom_ext
  apply ContIntertwiningMap.toIntertwiningMap_injective
  apply Representation.IntertwiningMap.ext
  apply Representation.IndV.hom_ext
  intro x
  ext a
  -- As for identity, remove just the linear-map projection wrappers introduced by
  -- extensionality, and use the public formula on the native tensor generators.
  change (algebraicIndMap.{u, v, w} R G U (f ≫ g)).hom.hom
    (Representation.IndV.mk U.toSubgroup.subtype
      (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) x a) =
      (algebraicIndMap.{u, v, w} R G U g).hom.hom ((algebraicIndMap.{u, v, w} R G U f).hom.hom
        (Representation.IndV.mk U.toSubgroup.subtype
          (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) x a))
  dsimp only [Representation.IndV.mk, LinearMap.coe_comp,
    Function.comp_apply, TensorProduct.mk_apply]
  simp only [algebraicIndMap_mk, ObjectProperty.FullSubcategory.comp_hom,
    TopRep.hom_comp]
  rfl

/-- The evaluation counit on induced coefficients is natural in the original coefficients. -/
@[reassoc]
theorem algebraicIndCounit_naturality (f : A ⟶ B) :
    (TopRep.resFunctor U.toSubgroup.subtype).map (algebraicIndMap.{u, v, w} R G U f).hom ≫
        algebraicIndCounit.{u, v, w} R G U B = algebraicIndCounit.{u, v, w} R G U A ≫ f.hom := by
  ext x
  let a := Rep.of (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)
  let b := Rep.of (Representation.ofDistribMulAction R U.toSubgroup B.obj.V)
  have h := (Rep.indCoindNatIso.{max u w, v, u} R U.toSubgroup).hom.naturality
    (coefficientMap.{u, v, w} R G U f)
  have h' := congrArg (fun m : Rep.ind U.toSubgroup.subtype a ⟶
      Rep.coind U.toSubgroup.subtype b ↦ (m.hom x).1 1) h
  -- Restriction and composition introduce only map wrappers, and the two counit equations
  -- turn their values into the native finite-index naturality square at `1`.
  change algebraicCoindCounit R G U B
    ((algebraicIndCoindIso.{u, v, w} R G U B).hom.hom.hom
      ((Rep.indMap U.toSubgroup.subtype (coefficientMap.{u, v, w} R G U f)).hom x)) =
    f.hom.hom (algebraicCoindCounit R G U A
      ((algebraicIndCoindIso.{u, v, w} R G U A).hom.hom.hom x))
  let y := (Rep.indMap U.toSubgroup.subtype (coefficientMap.{u, v, w} R G U f)).hom x
  have heq := (algebraicCoindCounit_apply R G U B
    ((algebraicIndCoindIso.{u, v, w} R G U B).hom.hom.hom y)).trans
    (congrArg (fun z ↦ z.1 1) (algebraicIndCoindIso_hom_apply.{u, v, w} R G U B y))
  rw [heq]
  have heq' := (algebraicCoindCounit_apply R G U A
    ((algebraicIndCoindIso.{u, v, w} R G U A).hom.hom.hom x)).trans
    (congrArg (fun z ↦ z.1 1) (algebraicIndCoindIso_hom_apply.{u, v, w} R G U A x))
  rw [heq']
  -- Mathlib's naturality is stated as an equality of bundled representation morphisms;
  -- identify its value at `1` with the pointwise coinduced map before using it.
  change ((Rep.indCoindIso.{max u w, v, u} b).hom.hom
    ((Rep.indMap U.toSubgroup.subtype (coefficientMap.{u, v, w} R G U f)).hom x)).1 1 =
      (coefficientMap.{u, v, w} R G U f).hom
        (((Rep.indCoindIso.{max u w, v, u} a).hom.hom x).1 1) at h'
  exact h'

end TauCeti
