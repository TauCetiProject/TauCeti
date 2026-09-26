/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import Mathlib.RepresentationTheory.Coinduced
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Discrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete

import all TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Discrete
import TauCeti.RepresentationTheory.Continuous.TopRep

/-!
# Coinduction as a functor of smooth discrete representations

For a compact topological group `G` and a subgroup `U`, this file packages the discrete coinduced
module `TauCeti.DiscreteCoind` in the categorical language of smooth discrete representations,
and compares it with Mathlib's algebraic coinduction `Representation.coind`. The unbundled module
`TauCeti.coind` is transported to the categorical language through the smooth-discrete dictionary
(`TauCeti.toSmoothDiscrete`, `TauCeti.ofSmoothDiscrete`).

## Main definitions

* `TauCeti.coindDiscreteFunctor`: coinduction from discrete `U`-representations to discrete
  `G`-representations, with objects `TauCeti.coindDiscreteRep`;
* `TauCeti.coindFunctor`: coinduction from smooth discrete `U`-representations to smooth discrete
  `G`-representations, with objects `TauCeti.coindTopRep`;
* `TauCeti.coindCounit` and `TauCeti.coindCounitNatTrans`: evaluation at `1` as the counit of
  coinduction, objectwise and natural in the coefficient representation;
* `TauCeti.coindTraceHom`: for finite-index `U`, the trace as a morphism of smooth discrete
  `G`-representations;
* `TauCeti.discreteCoindEquivAlgebraic`: for an open subgroup `U`, the linear equivalence between
  locally constant coinduction and Mathlib's `Representation.coindV`.

## Main results

* `TauCeti.isLocallyConstant_representationCoindV`: for an open subgroup, every algebraically
  coinduced function is automatically locally constant;
* `TauCeti.topologicalCoindIsoAlgebraic`: for an open subgroup, `TauCeti.coindTopRep` is
  isomorphic to Mathlib's `Representation.coind` regarded as a smooth discrete representation
  (`TauCeti.algebraicCoindAsSmooth`), by the identity on underlying functions.
-/

public section

namespace TauCeti

section Bundled

open CategoryTheory

universe u v w

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

local instance instDiscreteTopologyOfSmoothDiscreteCoind
    {R : Type u} [Ring R] [TopologicalSpace R] {G : Type v} [Monoid G] [TopologicalSpace G]
    (A : SmoothDiscreteTopRep.{u, v, w} R G) : DiscreteTopology A.obj.V :=
  A.property.discreteTopology

local instance instContinuousSMulOfSmoothDiscreteCoind
    {R : Type u} [Ring R] [TopologicalSpace R] {G : Type v} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (A : SmoothDiscreteTopRep.{u, v, w} R G) :
    ContinuousSMul G A.obj.V := A.property.continuousSMul

variable (R : Type u) [Ring R] [TopologicalSpace R]
  (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (U : Subgroup G)

/-- The locally constant coinduced module, bundled as a discrete representation of `G`. -/
noncomputable abbrev coindDiscreteRep (A : DiscreteRep.{u, v, w} R U) :
    DiscreteRep.{u, v, max v w} R G where
  V := DiscreteCoind G U A.V
  smulCommClass := DiscreteCoind.instSMulCommClass
  continuousSMulRing := DiscreteCoind.instContinuousSMulScalar

/-- Coinduction from discrete `U`-representations to discrete `G`-representations. -/
noncomputable def coindDiscreteFunctor :
    DiscreteRep.{u, v, w} R U ⥤ DiscreteRep.{u, v, max v w} R G where
  obj := coindDiscreteRep R G U
  map {A B} f :=
    (DiscreteCoind.map f.toLinearMap
      (DiscreteRep.equivariant f)).intertwiningMap_of_isIntertwiningMap _ _ fun g a => by
        apply DiscreteCoind.ext
        intro x
        rfl
  map_id A := Representation.IntertwiningMap.ext (LinearMap.ext fun a =>
    DiscreteCoind.ext fun g => by rfl)
  map_comp f f' := Representation.IntertwiningMap.ext (LinearMap.ext fun a =>
    DiscreteCoind.ext fun g => by rfl)

private theorem coindDiscreteFunctor_obj_impl (A : DiscreteRep.{u, v, w} R U) :
    (coindDiscreteFunctor R G U).obj A = coindDiscreteRep R G U A := rfl

/-- The object part of discrete coinduction is the locally constant coinduced representation. -/
@[simp]
theorem coindDiscreteFunctor_obj (A : DiscreteRep.{u, v, w} R U) :
    (coindDiscreteFunctor R G U).obj A = coindDiscreteRep R G U A :=
  coindDiscreteFunctor_obj_impl R G U A

private theorem coindDiscreteFunctor_map_apply_impl {A B : DiscreteRep.{u, v, w} R U}
    (f : A ⟶ B) (a : DiscreteCoind G U A.V) (g : G) :
    ((eqToHom (coindDiscreteFunctor_obj R G U A).symm ≫
      (coindDiscreteFunctor R G U).map f ≫
      eqToHom (coindDiscreteFunctor_obj R G U B)).toLinearMap a) g =
        f.toLinearMap (a g) := by
  -- `coindDiscreteFunctor` is defined objectwise as `coindDiscreteRep`, so both object equalities
  -- are `rfl` and the `eqToHom` transports around the functor map are identities. No categorical
  -- lemma discharges a transport along a proof of a definitional equality without unfolding the
  -- functor, so that one reduction is made here, in a private lemma, and the public statement is
  -- derived from it; what is left is the underlying map, computed by `DiscreteCoind.map_apply`.
  change DiscreteCoind.map f.toLinearMap (DiscreteRep.equivariant f) a g = _
  exact DiscreteCoind.map_apply f.toLinearMap _ a g

-- `simp` reduces the `abbrev` carrier `(coindDiscreteRep R G U B).V` and the fields of the `abbrev`
-- `TopRep.res` in implicit type arguments before it looks a term up, so the `simp` lemmas below
-- that evaluate on them state their left-hand sides through `dsimp% only`, as in #8315.
/-- Discrete coinduction maps act pointwise on their locally constant functions. The explicit
object transports identify the opaque functor's objects with `coindDiscreteRep`. -/
@[simp]
theorem coindDiscreteFunctor_map_apply {A B : DiscreteRep.{u, v, w} R U}
    (f : A ⟶ B) (a : DiscreteCoind G U A.V) (g : G) :
    (dsimp% only ((show ((coindDiscreteFunctor R G U).obj B).ρ.IntertwiningMap
        (coindDiscreteRep R G U B).ρ from
        eqToHom (coindDiscreteFunctor_obj R G U B))
      ((show ((coindDiscreteFunctor R G U).obj A).ρ.IntertwiningMap
          ((coindDiscreteFunctor R G U).obj B).ρ from
          (coindDiscreteFunctor R G U).map f)
        ((show (coindDiscreteRep R G U A).ρ.IntertwiningMap
            ((coindDiscreteFunctor R G U).obj A).ρ from
            eqToHom (coindDiscreteFunctor_obj R G U A).symm) a)) g)) =
        f.toLinearMap (a g) :=
  by
    simpa only [DiscreteRep.comp_toLinearMap, LinearMap.coe_comp,
      Representation.IntertwiningMap.coe_toLinearMap, Function.comp_apply] using
        coindDiscreteFunctor_map_apply_impl R G U f a g

/-- The locally constant coinduced module, bundled as a smooth discrete representation of `G`. -/
noncomputable abbrev coindTopRep (A : SmoothDiscreteTopRep.{u, v, w} R U) :
    SmoothDiscreteTopRep.{u, v, max v w} R G :=
  (toSmoothDiscrete R G).obj (coindDiscreteRep R G U ((ofSmoothDiscrete R U).obj A))

/-- Evaluation at `1` as the coinduction counit, from the restriction of the coinduced
representation to its coefficient representation. -/
noncomputable def coindCounit (A : SmoothDiscreteTopRep.{u, v, w} R U) :
    ContIntertwiningMap (TopRep.res (U.subtype : U →* G) (coindTopRep R G U A).obj).ρ
      A.obj.ρ where
  toContinuousLinearMap :=
    ⟨DiscreteCoind.evalLinear (R := R) G U A.obj.V, continuous_of_discreteTopology⟩
  isIntertwining' u := by
    ext f
    exact DiscreteCoind.eval_smul u f

private theorem coindCounit_apply_impl (A : SmoothDiscreteTopRep.{u, v, w} R U)
    (f : DiscreteCoind G U A.obj.V) : coindCounit R G U A f = f 1 := rfl

-- `dsimp% only` on the left-hand side: see the comment on `coindDiscreteFunctor_map_apply`.
/-- The counit of coinduction evaluates a coinduced function at the identity. -/
@[simp]
theorem coindCounit_apply (A : SmoothDiscreteTopRep.{u, v, w} R U)
    (f : DiscreteCoind G U A.obj.V) : (dsimp% only (coindCounit R G U A f)) = f 1 :=
  coindCounit_apply_impl R G U A f

/-- The trace packaged as a morphism of smooth discrete `G`-representations for a finite-index
subgroup `U`. -/
noncomputable def coindTraceHom [U.FiniteIndex]
    (A : SmoothDiscreteTopRep.{u, v, max v w} R G) :
    (coindTopRep R G U
      (⟨TopRep.res (U.subtype : U →* G) A.obj,
        A.property.res continuous_subtype_val⟩ : SmoothDiscreteTopRep R U)).obj ⟶ A.obj := by
  letI : DiscreteTopology A.obj.V := A.property.discreteTopology
  letI : ContinuousSMul G A.obj.V := A.property.continuousSMul
  let X := coindTopRep R G U
    (⟨TopRep.res (U.subtype : U →* G) A.obj,
      A.property.res continuous_subtype_val⟩ : SmoothDiscreteTopRep R U)
  letI : DiscreteTopology X.obj.V := X.property.discreteTopology
  exact CategoryTheory.ConcreteCategory.ofHom
    { toContinuousLinearMap :=
        ⟨DiscreteCoind.traceLinear (R := R) G U A.obj.V, continuous_of_discreteTopology⟩
      isIntertwining' g := by
        ext f
        exact map_smul (DiscreteCoind.trace G U A.obj.V) g f }

@[simp]
theorem coindTraceHom_apply [U.FiniteIndex]
    (A : SmoothDiscreteTopRep.{u, v, max v w} R G) (f : DiscreteCoind G U A.obj.V) :
    coindTraceHom R G U A f = DiscreteCoind.trace G U A.obj.V f := by
  -- Remove the categorical and continuous-linear-map wrappers; the remaining computation is
  -- exactly the public computation lemma for `DiscreteCoind.traceLinear`.
  change DiscreteCoind.traceLinear (R := R) G U A.obj.V f = _
  exact DiscreteCoind.traceLinear_apply f

/-- Coinduction from smooth discrete `U`-representations to smooth discrete
`G`-representations. -/
noncomputable def coindFunctor :
    SmoothDiscreteTopRep.{u, v, w} R U ⥤ SmoothDiscreteTopRep.{u, v, max v w} R G :=
  ofSmoothDiscrete R U ⋙ coindDiscreteFunctor R G U ⋙ toSmoothDiscrete R G

/-- The object part of smooth discrete coinduction is the bundled locally constant coinduced
representation. -/
@[simp]
theorem coindFunctor_obj (A : SmoothDiscreteTopRep.{u, v, w} R U) :
    (coindFunctor R G U).obj A = coindTopRep R G U A :=
  congrArg (toSmoothDiscrete R G).obj
    (coindDiscreteFunctor_obj R G U ((ofSmoothDiscrete R U).obj A))

private theorem coindFunctor_map_apply_impl {A B : SmoothDiscreteTopRep.{u, v, w} R U}
    (f : A ⟶ B) (a : DiscreteCoind G U A.obj.V) (g : G) :
    (show DiscreteCoind G U B.obj.V from
      (eqToHom (coindFunctor_obj R G U A).symm ≫ (coindFunctor R G U).map f ≫
        eqToHom (coindFunctor_obj R G U B)).hom.hom a) g = f.hom.hom (a g) := by
  -- Display the three constituent functor maps so their public computation lemmas apply.
  change (show DiscreteCoind G U B.obj.V from
    ((toSmoothDiscrete R G).map
      ((coindDiscreteFunctor R G U).map ((ofSmoothDiscrete R U).map f))).hom.hom a) g = _
  have htop := toSmoothDiscrete_map_hom_apply (R := R) (G := G)
    ((coindDiscreteFunctor R G U).map ((ofSmoothDiscrete R U).map f)) a
  -- The dictionary lemma returns an equality in the underlying carrier; identifying that carrier
  -- with `DiscreteCoind` makes point evaluation at `g` well typed.
  have htop' := congrArg (fun b => (show DiscreteCoind G U B.obj.V from b) g) htop
  have h := coindDiscreteFunctor_map_apply R G U ((ofSmoothDiscrete R U).map f) a g
  have h' := h.trans
    (ofSmoothDiscrete_map_toLinearMap_apply (R := R) (G := U) f (a g))
  exact htop'.trans h'

/-- Smooth discrete coinduction maps act pointwise on their locally constant functions. The
object transports identify the opaque composite functor's objects with `coindTopRep`. -/
@[simp]
theorem coindFunctor_map_apply {A B : SmoothDiscreteTopRep.{u, v, w} R U}
    (f : A ⟶ B) (a : DiscreteCoind G U A.obj.V) (g : G) :
    (show DiscreteCoind G U B.obj.V from
      (((eqToHom (congrArg
          (fun X : SmoothDiscreteTopRep.{u, v, max v w} R G => X.obj)
          (coindFunctor_obj R G U B))).hom.comp
        ((coindFunctor R G U).map f).hom.hom).comp
          (eqToHom (congrArg
            (fun X : SmoothDiscreteTopRep.{u, v, max v w} R G => X.obj)
            (coindFunctor_obj R G U A).symm)).hom) a) g = f.hom.hom (a g) := by
  simpa only [CategoryTheory.ObjectProperty.FullSubcategory.comp_hom,
    CategoryTheory.ObjectProperty.eqToHom_hom, TopRep.hom_comp] using
      coindFunctor_map_apply_impl R G U f a g

private noncomputable def coindCounitApp (A : SmoothDiscreteTopRep.{u, v, max v w} R U) :
    (coindFunctor.{u, v, max v w} R G U ⋙ smoothDiscreteResFunctor R G U).obj A ⟶ (𝟭 _).obj A :=
  ObjectProperty.homMk
    (eqToHom (congrArg (fun X : SmoothDiscreteTopRep.{u, v, max v w} R U ↦ X.obj)
        ((congrArg (smoothDiscreteResFunctor R G U).obj (coindFunctor_obj R G U A)).trans
          (smoothDiscreteResFunctor_obj R G U (coindTopRep R G U A)))) ≫
      TopRep.ofHom (coindCounit R G U A))

omit [IsTopologicalGroup G] [CompactSpace G] in
private theorem smoothDiscreteResFunctor_map_hom_apply_eq_cast
    {X Y : SmoothDiscreteTopRep.{u, v, w} R G} (φ : X ⟶ Y)
    (hX : ((smoothDiscreteResFunctor R G U).obj X).obj.V = X.obj.V)
    (hY : ((smoothDiscreteResFunctor R G U).obj Y).obj.V = Y.obj.V)
    (a : ((smoothDiscreteResFunctor R G U).obj X).obj) :
    ((smoothDiscreteResFunctor R G U).map φ).hom.hom a = cast hY.symm (φ.hom.hom (cast hX a)) := by
  -- `rw`, not `simp`, for the transport lemma: `simp` makes no progress, since the goal is not
  -- type-correct at the transparency it checks implicit arguments with (the restricted object
  -- carries a continuity proof for `Subtype.val` where one for `U.subtype` is expected).
  rw [← smoothDiscreteResFunctor_map_apply R G U φ (cast hX a),
    TopRep.eqToHom_hom_comp_comp_eqToHom_hom_apply]
  simp only [cast_cast, cast_eq]

private theorem coindCounit_cast_naturality {A B : SmoothDiscreteTopRep.{u, v, max v w} R U}
    (f : A ⟶ B) (hA : ((smoothDiscreteResFunctor R G U).obj ((coindFunctor R G U).obj A)).obj.V =
      (TopRep.res (U.subtype : U →* G) (coindTopRep R G U A).obj).V)
    (hB : ((smoothDiscreteResFunctor R G U).obj ((coindFunctor R G U).obj B)).obj.V =
      (TopRep.res (U.subtype : U →* G) (coindTopRep R G U B).obj).V)
    (a : ((smoothDiscreteResFunctor R G U).obj ((coindFunctor R G U).obj A)).obj) :
    coindCounit R G U B
        (cast hB (((smoothDiscreteResFunctor R G U).map ((coindFunctor R G U).map f)).hom.hom a)) =
      f.hom.hom (coindCounit R G U A (cast hA a)) := by
  -- The restricted map is the coinduced map conjugated by casts. The carrier equations come from
  -- `smoothDiscreteResFunctor_obj`: the carrier of `TopRep.res` is the original one by definition.
  rw [smoothDiscreteResFunctor_map_hom_apply_eq_cast R G U _
    (congrArg (·.obj.V) (smoothDiscreteResFunctor_obj R G U _))
    (congrArg (·.obj.V) (smoothDiscreteResFunctor_obj R G U _)), cast_cast]
  -- `coindFunctor_map_apply` takes an element of `DiscreteCoind G U A.obj.V`. The ascription
  -- types the transported element by the carrier of `coindTopRep`, which unfolds to it, so that
  -- the transports in `h` stay type-correct when rewritten into casts. `dsimp only` removes the
  -- `have` that the lemma's `show … from` elaborates to.
  have h := coindFunctor_map_apply R G U f (cast hA a : (coindTopRep R G U A).obj.V) 1
  dsimp only at h
  -- After the rewrites `h` is the goal up to unfolding `coindCounit`, which evaluates at `1` by
  -- definition (`coindCounit_apply_impl` is `rfl`): its argument lies in the carrier of the
  -- restriction of `coindTopRep`, which unfolds to `DiscreteCoind`.
  rwa [TopRep.eqToHom_hom_comp_comp_eqToHom_hom_apply, cast_cast] at h

private theorem coindCounitApp_naturality {A B : SmoothDiscreteTopRep.{u, v, max v w} R U}
    (f : A ⟶ B) :
    (coindFunctor.{u, v, max v w} R G U ⋙ smoothDiscreteResFunctor R G U).map f ≫
        coindCounitApp R G U B =
      coindCounitApp R G U A ≫ (𝟭 (SmoothDiscreteTopRep.{u, v, max v w} R U)).map f := by
  ext a
  -- Both functors are opaque here, so their objects are identified with `coindTopRep` and
  -- `TopRep.res` only through the public object lemmas. Every transport along those equations
  -- is a cast of carriers, and the two public map computations close the square pointwise.
  dsimp only [coindCounitApp, Functor.comp_map, Functor.id_map,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, TopRep.hom_comp,
    TopRep.hom_ofHom, ContIntertwiningMap.toContinuousLinearMap_comp,
    ContinuousLinearMap.comp_apply, ContIntertwiningMap.toContinuousLinearMap_apply]
  rw [TopRep.eqToHom_hom_apply, TopRep.eqToHom_hom_apply]
  -- `(… :)` elaborates the lemma before unifying it with the goal; propagating the goal into its
  -- carrier equations first is about ten times slower.
  exact (coindCounit_cast_naturality R G U f _ _ a :)

/-- Evaluation at `1`, natural in the smooth discrete coefficient representation. -/
noncomputable def coindCounitNatTrans :
    coindFunctor.{u, v, max v w} R G U ⋙ smoothDiscreteResFunctor R G U ⟶
      𝟭 (SmoothDiscreteTopRep.{u, v, max v w} R U) where
  app := coindCounitApp R G U
  -- `(… :)` elaborates the lemma before unifying it with the field's type; propagating that type
  -- into it first is about ten times slower.
  naturality _ _ f := (coindCounitApp_naturality R G U f :)

private theorem coindCounitNatTrans_app_hom_impl (A : SmoothDiscreteTopRep.{u, v, max v w} R U) :
    ((coindCounitNatTrans R G U).app A).hom =
      eqToHom (congrArg (fun X : SmoothDiscreteTopRep.{u, v, max v w} R U ↦ X.obj)
        ((congrArg (smoothDiscreteResFunctor R G U).obj (coindFunctor_obj R G U A)).trans
          (smoothDiscreteResFunctor_obj R G U (coindTopRep R G U A)))) ≫
        TopRep.ofHom (coindCounit R G U A) := rfl

-- A pre-lemma (`simp↓`): otherwise `Functor.comp_obj` and `Functor.id_obj` rewrite the implicit
-- source and target of the component first, and the left-hand side no longer matches. `dsimp%` does
-- not help here, since it also rewrites the dependent implicit arguments that `simp` leaves alone.
/-- The components of the coinduction counit evaluate at `1`. The object transport identifies the
restricted opaque coinduced object with the restriction of `coindTopRep`. -/
@[simp↓]
theorem coindCounitNatTrans_app_apply (A : SmoothDiscreteTopRep.{u, v, max v w} R U)
    (f : DiscreteCoind G U A.obj.V) :
    (show ContIntertwiningMap ((coindTopRep R G U A).obj.ρ.restrict U.subtype) A.obj.ρ from
      ((coindCounitNatTrans R G U).app A).hom.hom.comp
        (eqToHom (congrArg (fun X : SmoothDiscreteTopRep.{u, v, max v w} R U ↦ X.obj)
          ((congrArg (smoothDiscreteResFunctor R G U).obj (coindFunctor_obj R G U A)).trans
            (smoothDiscreteResFunctor_obj R G U (coindTopRep R G U A))).symm)).hom) f =
      f 1 := by
  rw [← TopRep.hom_comp, coindCounitNatTrans_app_hom_impl, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, TopRep.hom_ofHom, coindCounit_apply]

end Bundled

section AlgebraicComparison

open CategoryTheory
open scoped Pointwise

universe u v w

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

section LocallyConstant

variable (R : Type u) [Semiring R]
  (G : Type v) [Group G] [TopologicalSpace G] [ContinuousMul G]

/-- An algebraically coinduced function from an open subgroup is locally constant when the
coefficient action is continuous and the coefficient space is discrete. -/
theorem isLocallyConstant_representationCoindV (U : OpenSubgroup G)
    {A : Type w} [AddCommMonoid A] [Module R A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction U.toSubgroup A] [SMulCommClass U.toSubgroup R A]
    [ContinuousSMul U.toSubgroup A]
    (f : Representation.coindV U.toSubgroup.subtype
      (Representation.ofDistribMulAction R U.toSubgroup A)) :
    IsLocallyConstant f.1 := by
  -- Around `g`, the function is determined by the orbit map on `U * g`; shrinking `U` to the
  -- open stabilizer of `f g` makes it constant there.
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  let V : Set U := MulAction.stabilizer U (f.1 g)
  have hV : IsOpen V := stabilizer_isOpen U (f.1 g)
  refine ⟨(Subtype.val '' V) * {g},
    (U.isOpen.isOpenMap_subtype_val V hV).mul_right, ?_, ?_⟩
  · refine ⟨(1 : G), ?_, g, Set.mem_singleton g, one_mul g⟩
    exact ⟨(1 : U.toSubgroup), Subgroup.one_mem _, rfl⟩
  · intro x hx
    obtain ⟨_, ⟨u, hu, rfl⟩, z, hz, rfl⟩ := hx
    have : z = g := Set.mem_singleton_iff.mp hz
    subst z
    exact (f.2 u g).trans (MulAction.mem_stabilizer_iff.mp hu)

end LocallyConstant

variable (R : Type u) [Ring R] [TopologicalSpace R]
  (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : OpenSubgroup G)
  (A : SmoothDiscreteTopRep.{u, v, w} R U.toSubgroup)

local instance : DiscreteTopology A.obj.V := A.property.discreteTopology
local instance : ContinuousSMul U.toSubgroup A.obj.V := A.property.continuousSMul
local instance : SMulCommClass U.toSubgroup R A.obj.V := TopRep.smulCommClass A.obj
local instance : SMulCommClass G R (DiscreteCoind G U.toSubgroup A.obj.V) :=
  DiscreteCoind.instSMulCommClass (G := G) (U := U.toSubgroup) (A := A.obj.V)

/-- For an open subgroup, locally constant coinduction is linearly equivalent to Mathlib's
algebraic `Representation.coindV`, which carries the action `Representation.coind`. Both
directions preserve the underlying function on `G`.

Openness is used only in the inverse direction: it makes every algebraically coinduced function
locally constant. -/
noncomputable def discreteCoindEquivAlgebraic :
    DiscreteCoind G U.toSubgroup A.obj.V ≃ₗ[R]
      Representation.coindV U.toSubgroup.subtype
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) where
  toFun f := ⟨f, fun u g ↦ DiscreteCoind.apply_mul f u g⟩
  invFun f := DiscreteCoind.mk G U.toSubgroup A.obj.V f.1
    (isLocallyConstant_representationCoindV R G U f) fun u g ↦ by
      simpa using f.2 u g
  left_inv f := DiscreteCoind.ext fun _ ↦ rfl
  right_inv f := Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The comparison sends a locally constant coinduced function to the same underlying
algebraically coinduced function. -/
@[simp]
theorem discreteCoindEquivAlgebraic_apply (f : DiscreteCoind G U.toSubgroup A.obj.V) (g : G) :
    (discreteCoindEquivAlgebraic R G U A f).1 g = f g := (rfl)

/-- The inverse comparison sends an algebraically coinduced function to the same underlying
function, now equipped with its automatic local constancy. -/
@[simp]
theorem discreteCoindEquivAlgebraic_symm_apply
    (f : Representation.coindV U.toSubgroup.subtype
      (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)) (g : G) :
    (discreteCoindEquivAlgebraic R G U A).symm f g = f.1 g := (rfl)

/-- The locally constant/algebraic coinduction comparison intertwines the right-translation
actions of `G`. -/
@[simp]
theorem discreteCoindEquivAlgebraic_smul (g : G)
    (f : DiscreteCoind G U.toSubgroup A.obj.V) :
    discreteCoindEquivAlgebraic R G U A (g • f) =
      Representation.coind U.toSubgroup.subtype
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) g
        (discreteCoindEquivAlgebraic R G U A f) := by
  apply Subtype.ext
  funext x
  simp only [Representation.coind_apply, discreteCoindEquivAlgebraic_apply,
    DiscreteCoind.coe_smul]
  -- The membership proof inside Mathlib's `coind_apply` blocks `LinearMap.restrict_coe_apply`,
  -- so the remaining right translation `f (x * g)` is closed definitionally.
  rfl

variable [CompactSpace G]

/-- Mathlib's algebraic coinduction, equipped with the discrete topology and the continuous
actions transported from locally constant coinduction. -/
noncomputable abbrev algebraicCoindDiscreteRep : DiscreteRep.{u, v, max v w} R G := by
  let e := discreteCoindEquivAlgebraic R G U A
  let V := Representation.coindV U.toSubgroup.subtype
    (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)
  letI : TopologicalSpace
      V := ⊥
  letI : DiscreteTopology V := ⟨rfl⟩
  letI : DistribMulAction G V := e.symm.toAddEquiv.distribMulAction G
  letI : SMulCommClass G R V := ⟨fun g r f ↦ by
    apply Subtype.ext
    funext x
    rfl⟩
  -- Both actions on `V` are transported along the single map `e.symm`, a homeomorphism because
  -- both sides are discrete. Each continuity statement is therefore one instance of
  -- `Topology.IsInducing.continuousSMul` along `e.symm`, acting as the identity on scalars.
  let h : V ≃ₜ DiscreteCoind G U.toSubgroup A.obj.V :=
    { toEquiv := e.symm.toEquiv
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  letI : ContinuousSMul R V :=
    -- `by exact` defers `LinearEquiv.map_smul` until instance synthesis has fixed which scalar
    -- action on `DiscreteCoind` the transport is taken along.
    h.isInducing.continuousSMul continuous_id fun {r f} => by exact e.symm.map_smul r f
  letI : ContinuousSMul G V :=
    h.isInducing.continuousSMul continuous_id fun {g f} => by
      rw [e.symm.toEquiv.smul_def g f]
      exact e.symm_apply_apply _
  exact { V := V }

/-- The representation carried by `algebraicCoindDiscreteRep` is Mathlib's
`Representation.coind`, not merely an abstractly isomorphic action. -/
@[simp]
theorem algebraicCoindDiscreteRep_ρ :
    (algebraicCoindDiscreteRep R G U A).ρ =
      Representation.coind U.toSubgroup.subtype
        (Representation.ofDistribMulAction R U.toSubgroup A.obj.V) := by
  ext g f : 2
  -- The action is transported along `e.symm` for `e := discreteCoindEquivAlgebraic`, so
  -- `g • f = e (g • e.symm f)` by `Equiv.smul_def`; `discreteCoindEquivAlgebraic_smul`
  -- computes the right-hand side.
  refine ((discreteCoindEquivAlgebraic R G U A).symm.toEquiv.smul_def g f).trans ?_
  simp

/-- Algebraic coinduction from an open subgroup, regarded as a smooth discrete topological
representation. -/
noncomputable abbrev algebraicCoindAsSmooth : SmoothDiscreteTopRep.{u, v, max v w} R G :=
  (toSmoothDiscrete R G).obj (algebraicCoindDiscreteRep R G U A)

/-- The discrete representation isomorphism underlying the topological/algebraic comparison. -/
private noncomputable def discreteCoindIsoAlgebraic :
    coindDiscreteRep R G U.toSubgroup ((ofSmoothDiscrete R U.toSubgroup).obj A) ≅
      algebraicCoindDiscreteRep R G U A where
  hom := (discreteCoindEquivAlgebraic R G U A).toLinearMap.intertwiningMap_of_isIntertwiningMap
    _ _ fun g f ↦ discreteCoindEquivAlgebraic_smul R G U A g f
  inv :=
    { toLinearMap := (discreteCoindEquivAlgebraic R G U A).symm.toLinearMap
      isIntertwining' :=
        (discreteCoindEquivAlgebraic R G U A).isIntertwining_symm_isIntertwining fun g ↦
          LinearMap.ext (discreteCoindEquivAlgebraic_smul R G U A g) }
  hom_inv_id := Representation.IntertwiningMap.ext
    (LinearMap.ext (discreteCoindEquivAlgebraic R G U A).symm_apply_apply)
  inv_hom_id := Representation.IntertwiningMap.ext
    (LinearMap.ext (discreteCoindEquivAlgebraic R G U A).apply_symm_apply)

/-- Locally constant topological coinduction from an open subgroup agrees with Mathlib's
algebraic coinduction. The isomorphism is the identity on the underlying equivariant functions. -/
noncomputable def topologicalCoindIsoAlgebraic :
    coindTopRep R G U.toSubgroup A ≅ algebraicCoindAsSmooth R G U A := by
  exact (toSmoothDiscrete R G).mapIso (discreteCoindIsoAlgebraic R G U A)

private theorem topologicalCoindIsoAlgebraic_hom_hom_hom_apply_coe_impl
    (f : DiscreteCoind G U.toSubgroup A.obj.V) (g : G) :
    ((topologicalCoindIsoAlgebraic R G U A).hom.hom.hom f).1 g =
      (discreteCoindEquivAlgebraic R G U A f).1 g := by
  rw [topologicalCoindIsoAlgebraic, Functor.mapIso_hom]
  have h := toSmoothDiscrete_map_hom_apply
    (R := R) (G := G) (discreteCoindIsoAlgebraic R G U A).hom f
  exact congrArg (fun b ↦ b.1 g) h

-- The codomain carrier `(coindTopRep R G U.toSubgroup A).obj.V` is `DiscreteCoind` only up to
-- unfolding the `toSmoothDiscrete` dictionary, and no lemma can rewrite a type; the `show`
-- names that carrier so that evaluation at `g` elaborates, exactly as in
-- `coindFunctor_map_apply_impl`.
private theorem topologicalCoindIsoAlgebraic_inv_hom_hom_apply_coe_impl
    (f : Representation.coindV U.toSubgroup.subtype
      (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)) (g : G) :
    (show DiscreteCoind G U.toSubgroup A.obj.V from
      (topologicalCoindIsoAlgebraic R G U A).inv.hom.hom f) g =
        (discreteCoindEquivAlgebraic R G U A).symm f g := by
  rw [topologicalCoindIsoAlgebraic, Functor.mapIso_inv]
  have h := toSmoothDiscrete_map_hom_apply
    (R := R) (G := G) (discreteCoindIsoAlgebraic R G U A).inv f
  -- The dictionary lemma is an equality in the unfolded carrier; view it in `DiscreteCoind` to
  -- evaluate at `g`.
  exact congrArg (fun b ↦ (show DiscreteCoind G U.toSubgroup A.obj.V from b) g) h

/-- The forward map of the topological/algebraic comparison leaves every value unchanged. -/
@[simp]
theorem topologicalCoindIsoAlgebraic_hom_hom_hom_apply_coe
    (f : DiscreteCoind G U.toSubgroup A.obj.V) (g : G) :
    ((topologicalCoindIsoAlgebraic R G U A).hom.hom.hom f).1 g = f g :=
  (topologicalCoindIsoAlgebraic_hom_hom_hom_apply_coe_impl R G U A f g).trans
    (discreteCoindEquivAlgebraic_apply R G U A f g)

/-- The inverse map of the topological/algebraic comparison leaves every value unchanged. -/
@[simp]
theorem topologicalCoindIsoAlgebraic_inv_hom_hom_apply_coe
    (f : Representation.coindV U.toSubgroup.subtype
      (Representation.ofDistribMulAction R U.toSubgroup A.obj.V)) (g : G) :
    -- `show` names the `DiscreteCoind` carrier, as in the auxiliary lemma above.
    (show DiscreteCoind G U.toSubgroup A.obj.V from
      (topologicalCoindIsoAlgebraic R G U A).inv.hom.hom f) g = f.1 g :=
  (topologicalCoindIsoAlgebraic_inv_hom_hom_apply_coe_impl R G U A f g).trans
    (discreteCoindEquivAlgebraic_symm_apply R G U A f g)

end AlgebraicComparison

end TauCeti
