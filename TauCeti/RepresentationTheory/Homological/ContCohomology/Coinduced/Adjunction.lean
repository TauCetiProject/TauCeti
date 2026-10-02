/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Functor

import all TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Functor
import all TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Discrete
import all TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete

/-!
# Continuous Frobenius reciprocity

Locally constant coinduction is right adjoint to restriction on smooth discrete representations
of a compact topological group. A morphism from a restricted representation to `A` extends by
`m ↦ (g ↦ f (g • m))`; its inverse is restriction followed by evaluation at `1`.
No openness or closedness assumption on the subgroup is needed. Compactness ensures that
coinduction carries a continuous action when given the discrete topology.

The construction uses the orbit-map unit `DiscreteCoind.unit`, the pointwise coefficient map
`DiscreteCoind.map`, and the evaluation counit `coindCounitNatTrans`. The hom-set equivalence is
additive, natural in both coefficients, and identifies the previously defined counit with the
counit of the adjunction. Over a commutative coefficient ring it is linear.

The algebraic model is Mathlib's `Rep.resCoindHomEquiv` and `Rep.resCoindAdjunction`.
For the continuous version see Ribes–Zalesskii, *Profinite Groups*, second edition, §6.10.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

section Ring

variable (R : Type u) [Ring R] [TopologicalSpace R]
  (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (U : Subgroup G)

local instance (X : SmoothDiscreteTopRep.{u, v, max v w} R G) : DiscreteTopology X.obj.V :=
  X.property.discreteTopology

local instance (X : SmoothDiscreteTopRep.{u, v, max v w} R G) : ContinuousSMul G X.obj.V :=
  X.property.continuousSMul

variable (M : SmoothDiscreteTopRep.{u, v, max v w} R G)
  (A : SmoothDiscreteTopRep.{u, v, max v w} R U)

/-- Extend a morphism on the restricted representation by applying it to orbit maps.
At `m` its value is the coinduced function `g ↦ f (g • m)`. -/
noncomputable def smoothDiscreteResCoindToHom
    (f : smoothDiscreteResTopRep U M ⟶ A) : M ⟶ coindTopRep R G U A := by
  let f' := (ofSmoothDiscrete R U).map f
  let L : M.obj.V →ₗ[R] DiscreteCoind G U A.obj.V :=
    { toFun m := DiscreteCoind.map f'.toLinearMap (DiscreteRep.equivariant f')
        (DiscreteCoind.unit G U M.obj.V m)
      map_add' m n := by
        rw [map_add]
        exact map_add _ _ _
      map_smul' r m := by
        apply DiscreteCoind.ext
        intro g
        -- The dictionary changes the action instances, so pointwise rewriting cannot match
        -- the coinduction computation lemma at instance transparency. Reduce the wrappers.
        change f'.toLinearMap (g • (r • m)) = r • f'.toLinearMap (g • m)
        rw [smul_comm]
        exact map_smul f'.toLinearMap r _ }
  exact ObjectProperty.homMk (TopRep.ofHom
    { toContinuousLinearMap := ⟨L, continuous_of_discreteTopology⟩
      isIntertwining' g := by
        ext m x
        -- The categorical dictionary transports the right-translation action unchanged.
        change f'.toLinearMap (x • (g • m)) = f'.toLinearMap ((x * g) • m)
        rw [mul_smul] })

/-- The adjunct evaluates on an orbit map. -/
@[simp]
theorem smoothDiscreteResCoindToHom_apply
    (f : smoothDiscreteResTopRep U M ⟶ A) (m : M.obj.V) (g : G) :
    (dsimp% only (show DiscreteCoind G U A.obj.V from
      (smoothDiscreteResCoindToHom R G U M A f).hom.hom m) g) = f.hom.hom (g • m) := by
  -- Remove the full-subcategory and continuous-linear-map wrappers around the construction.
  change ((ofSmoothDiscrete R U).map f).toLinearMap (g • m) = _
  exact ofSmoothDiscrete_map_toLinearMap_apply R U f (g • m)

/-- Continuous Frobenius reciprocity, as an additive equivalence of hom sets.
The inverse is restriction followed by the evaluation counit. -/
noncomputable def smoothDiscreteResCoindHomEquiv :
    (smoothDiscreteResTopRep U M ⟶ A) ≃+ (M ⟶ coindTopRep R G U A) where
  toFun := smoothDiscreteResCoindToHom R G U M A
  invFun f := ObjectProperty.homMk
    ((TopRep.resFunctor U.subtype).map f.hom ≫ TopRep.ofHom (coindCounit R G U A))
  left_inv f := by
    ext m
    -- Restriction changes only the action, and the counit evaluates at `1`.
    exact (smoothDiscreteResCoindToHom_apply R G U M A f m 1).trans
      (congrArg f.hom.hom (one_smul G m))
  right_inv f := by
    ext m
    apply DiscreteCoind.ext
    intro x
    -- The orbit formula is instantiated explicitly because the dictionary changes instances.
    refine (smoothDiscreteResCoindToHom_apply R G U M A _ m x).trans ?_
    -- Evaluation of equivariance at `1` identifies the reconstructed coinduced function.
    change (show DiscreteCoind G U A.obj.V from f.hom.hom (x • m)) 1 =
      (show DiscreteCoind G U A.obj.V from f.hom.hom m) x
    have h := congrArg (fun a : DiscreteCoind G U A.obj.V ↦ a 1)
      (f.hom.hom.isIntertwining x m)
    -- The coinduced operator is right translation, transported through the dictionary.
    exact h.trans (by
      -- Identify the dictionary's operator with right translation before simplifying `1 * x`.
      change (show DiscreteCoind G U A.obj.V from f.hom.hom m) (1 * x) = _
      rw [one_mul])
  map_add' f g := by
    ext m
    apply DiscreteCoind.ext
    intro x
    -- Reduce the morphism addition wrappers before applying the public orbit formula.
    change (show DiscreteCoind G U A.obj.V from
      (smoothDiscreteResCoindToHom R G U M A (f + g)).hom.hom m) x =
      (show DiscreteCoind G U A.obj.V from
        (smoothDiscreteResCoindToHom R G U M A f).hom.hom m) x +
      (show DiscreteCoind G U A.obj.V from
        (smoothDiscreteResCoindToHom R G U M A g).hom.hom m) x
    simp only [smoothDiscreteResCoindToHom_apply]
    rfl

/-- The forward Frobenius equivalence evaluates on orbit maps. -/
@[simp]
theorem smoothDiscreteResCoindHomEquiv_apply
    (f : smoothDiscreteResTopRep U M ⟶ A) (m : M.obj.V) (g : G) :
    (dsimp% only (show DiscreteCoind G U A.obj.V from
      (smoothDiscreteResCoindHomEquiv R G U M A f).hom.hom m) g) = f.hom.hom (g • m) :=
  smoothDiscreteResCoindToHom_apply R G U M A f m g

/-- The inverse Frobenius equivalence is restriction followed by the evaluation counit. -/
theorem smoothDiscreteResCoindHomEquiv_symm_eq_res_comp_coindCounit
    (f : M ⟶ coindTopRep R G U A) :
    (smoothDiscreteResCoindHomEquiv R G U M A).symm f =
      ObjectProperty.homMk
        ((TopRep.resFunctor U.subtype).map f.hom ≫ TopRep.ofHom (coindCounit R G U A)) := (rfl)

/-- The inverse Frobenius equivalence evaluates the coinduced function at `1`. -/
@[simp]
theorem smoothDiscreteResCoindHomEquiv_symm_apply
    (f : M ⟶ coindTopRep R G U A) (m : M.obj.V) :
    (dsimp% only ((smoothDiscreteResCoindHomEquiv R G U M A).symm f).hom.hom m) =
      (show DiscreteCoind G U A.obj.V from f.hom.hom m) 1 := (rfl)

/-- Locally constant coinduction is right adjoint to restriction on smooth discrete
representations of a compact group. No closedness assumption on `U` is required. -/
noncomputable def smoothDiscreteResCoindAdjunction :
    smoothDiscreteResFunctor.{u, v, max v w} R G U ⊣ coindFunctor R G U :=
  Adjunction.mkOfHomEquiv
    { homEquiv M A := (smoothDiscreteResCoindHomEquiv R G U M A).toEquiv
      homEquiv_naturality_left_symm := by
        intro M' M A f g
        ext m
        rfl
      homEquiv_naturality_right := by
        intro M A A' f g
        ext m
        apply DiscreteCoind.ext
        intro x
        -- Both composites are pointwise coefficient maps of the same orbit function.
        change g.hom.hom (f.hom.hom (x • m)) = g.hom.hom (f.hom.hom (x • m))
        rfl }

/-- The adjunction uses the explicit Frobenius equivalence, after the canonical object
identifications of restriction and coinduction. -/
theorem smoothDiscreteResCoindAdjunction_homEquiv :
    (smoothDiscreteResCoindAdjunction R G U).homEquiv M A =
      (Iso.homCongr (eqToIso (smoothDiscreteResFunctor_obj R G U M)) (Iso.refl A)).trans
        ((smoothDiscreteResCoindHomEquiv R G U M A).toEquiv.trans
          (Iso.homCongr (Iso.refl M) (eqToIso (coindFunctor_obj R G U A).symm))) := by
  rw [smoothDiscreteResCoindAdjunction]
  simp only [Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The unit of continuous Frobenius reciprocity is the orbit-map adjunct of the identity.
The object identifications display its codomain as locally constant coinduction. -/
theorem smoothDiscreteResCoindAdjunction_unit_app :
    (smoothDiscreteResCoindAdjunction R G U).unit.app M ≫
        (coindFunctor R G U).map (eqToHom (smoothDiscreteResFunctor_obj R G U M)) ≫
        eqToHom (coindFunctor_obj R G U (smoothDiscreteResTopRep U M)) =
      smoothDiscreteResCoindToHom R G U M (smoothDiscreteResTopRep U M)
        (𝟙 (smoothDiscreteResTopRep U M)) := by
  ext m
  apply DiscreteCoind.ext
  intro g
  rfl

/-- The counit of continuous Frobenius reciprocity is the existing evaluation transformation. -/
@[simp]
theorem smoothDiscreteResCoindAdjunction_counit :
    (smoothDiscreteResCoindAdjunction R G U).counit = coindCounitNatTrans R G U := by
  ext A m
  rfl

/-- Coinduction on smooth discrete representations is a right adjoint. -/
noncomputable instance coindFunctor_isRightAdjoint :
    (coindFunctor.{u, v, max v w} R G U).IsRightAdjoint :=
  (smoothDiscreteResCoindAdjunction R G U).isRightAdjoint

end Ring

section Linear

variable (R : Type u) [CommRing R] [TopologicalSpace R]
  (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (U : Subgroup G) (M : SmoothDiscreteTopRep.{u, v, max v w} R G)
  (A : SmoothDiscreteTopRep.{u, v, max v w} R U)

/-- Continuous Frobenius reciprocity is linear over a commutative coefficient ring. -/
noncomputable def smoothDiscreteResCoindHomLinearEquiv :
    (smoothDiscreteResTopRep U M ⟶ A) ≃ₗ[R] (M ⟶ coindTopRep R G U A) where
  toAddEquiv := smoothDiscreteResCoindHomEquiv R G U M A
  map_smul' r f := by
    ext m
    apply DiscreteCoind.ext
    intro g
    -- Strip the scalar-action wrappers on morphisms; the orbit formula is pointwise linear.
    change (show DiscreteCoind G U A.obj.V from
      (smoothDiscreteResCoindHomEquiv R G U M A (r • f)).hom.hom m) g =
      r • (show DiscreteCoind G U A.obj.V from
        (smoothDiscreteResCoindHomEquiv R G U M A f).hom.hom m) g
    simp only [smoothDiscreteResCoindHomEquiv_apply]
    rfl

/-- The linear Frobenius equivalence refines the same additive equivalence. -/
@[simp]
theorem smoothDiscreteResCoindHomLinearEquiv_toAddEquiv :
    (smoothDiscreteResCoindHomLinearEquiv R G U M A).toAddEquiv =
      smoothDiscreteResCoindHomEquiv R G U M A := (rfl)

/-- The linear equivalence evaluates on orbit maps. -/
@[simp]
theorem smoothDiscreteResCoindHomLinearEquiv_apply
    (f : smoothDiscreteResTopRep U M ⟶ A) (m : M.obj.V) (g : G) :
    (dsimp% only (show DiscreteCoind G U A.obj.V from
      (smoothDiscreteResCoindHomLinearEquiv R G U M A f).hom.hom m) g) = f.hom.hom (g • m) :=
  smoothDiscreteResCoindHomEquiv_apply R G U M A f m g

/-- The inverse linear equivalence evaluates at `1`. -/
@[simp]
theorem smoothDiscreteResCoindHomLinearEquiv_symm_apply
    (f : M ⟶ coindTopRep R G U A) (m : M.obj.V) :
    (dsimp% only ((smoothDiscreteResCoindHomLinearEquiv R G U M A).symm f).hom.hom m) =
      (show DiscreteCoind G U A.obj.V from f.hom.hom m) 1 :=
  smoothDiscreteResCoindHomEquiv_symm_apply R G U M A f m

end Linear

end TauCeti
