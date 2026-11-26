/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import TauCeti.Algebra.Lie.GeneralLinear.EndLie
public import TauCeti.RepresentationTheory.LieHom

/-!
# Conjugation action of `GL(V)` on `𝔤𝔩(V)`

For a module `V` over a commutative ring `R`, the group `GL(V)` of units of `Module.End R V` acts
on `𝔤𝔩(V) = TauCeti.EndLie R V` by conjugation, `g • X = g X g⁻¹`. This action is by Lie algebra
automorphisms. For a topological module `V`, the group of units of the algebra `V →L[R] V` of
continuous endomorphisms acts through its image in `GL(V)`.

## Main definitions

* `TauCeti.EndLie.conj R V`: the representation of `GL(V)` on `𝔤𝔩(V)` by conjugation.
* `TauCeti.EndLie.ofContinuousLinearMap R V`: a continuous endomorphism of `V` as an element of
  `𝔤𝔩(V)`.

## Main statements

* `TauCeti.EndLie.instIsLieActionConj`: conjugation acts by Lie algebra morphisms.
-/

public section

namespace TauCeti.EndLie

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]

/-- The action of `GL(V)` on `𝔤𝔩(V)` by conjugation, `g • X = g X g⁻¹`. -/
noncomputable def conj : Representation R (Module.End R V)ˣ (EndLie R V) where
  toFun g := LinearMap.mulLeft R ((equiv R V).symm g) ∘ₗ
    LinearMap.mulRight R ((equiv R V).symm ↑g⁻¹)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_assoc]

variable {R V}

/-- Conjugation by `g` sends `X` to `g X g⁻¹`. -/
@[simp]
theorem conj_apply (g : (Module.End R V)ˣ) (X : EndLie R V) :
    conj R V g X = (equiv R V).symm g * X * (equiv R V).symm ↑g⁻¹ := by
  simp only [conj, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mulRight_apply, LinearMap.mulLeft_apply, mul_assoc]

variable (R V)

-- `LinearEquiv.lieConj` and `AlgEquiv.toLieEquiv` use the commutator Lie algebra structure on
-- `Module.End R V`, which Mathlib provides only as a local instance.
attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra in
/-- Conjugation acts on `𝔤𝔩(V)` by Lie algebra endomorphisms: transported along
`TauCeti.EndLie.equiv`, it is Mathlib's conjugation `LinearEquiv.lieConj`. -/
instance instIsLieActionConj : (conj R V).IsLieAction :=
  .of_lieEquiv (fun g ↦ (equiv R V).toLieEquiv.trans
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv R V g).lieConj.trans
        (equiv R V).toLieEquiv.symm)) fun g X ↦ (equiv R V).injective <| by
    ext v
    simp only [LieEquiv.trans_apply, AlgEquiv.toLieEquiv_apply, LinearEquiv.lieConj_apply,
      AlgEquiv.toLieEquiv_symm_apply, AlgEquiv.apply_symm_apply, LinearEquiv.conj_apply_apply,
      LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, conj_apply, map_mul,
      mul_apply_eq_comp]
    -- Mathlib has no lemma for the inverse of `LinearMap.GeneralLinearGroup.generalLinearEquiv R V
    -- g`, which is `g⁻¹` by definition.
    rfl

section Continuous

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul R V]

/-- A continuous endomorphism of `V` as an element of `𝔤𝔩(V)`. -/
noncomputable def ofContinuousLinearMap : (V →L[R] V) →ₐ[R] EndLie R V :=
  (equiv R V).symm.toAlgHom.comp
    { ContinuousLinearMap.toLinearMapRingHom with commutes' := fun _ ↦ rfl }

variable {R V}

/-- A continuous endomorphism, as an element of `𝔤𝔩(V)`, corresponds to its underlying linear
map. -/
@[simp]
theorem ofContinuousLinearMap_apply (A : V →L[R] V) :
    ofContinuousLinearMap R V A = (equiv R V).symm (A : Module.End R V) :=
  (rfl)

end Continuous

end TauCeti.EndLie
