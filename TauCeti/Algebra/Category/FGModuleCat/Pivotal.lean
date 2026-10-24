/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.Algebra.Category.FGModuleCat.Rigid
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Symmetric
public import TauCeti.LinearAlgebra.Trace.Coevaluation

/-!
# The standard spherical structure on finite-dimensional vector spaces

The category `FGModuleCat K` of finite-dimensional vector spaces over a field `K` is symmetric
and rigid, so it carries the canonical spherical structure of a symmetric rigid category, whose
pivotal isomorphisms are the Drinfeld isomorphisms. This file identifies that structure with the
classical one:

* the pivotal isomorphism `V ≅ Vᘁᘁ` is the evaluation map `Module.Dual.eval K V` of a vector space
  into its double dual;
* the categorical trace of an endomorphism `f` is its linear trace `LinearMap.trace K V f`, read as
  the scalar endomorphism of the unit object `K`;
* consequently the quantum dimension of `V` is its dimension `finrank K V`.

## Main results

* `FGModuleCat.drinfeldIso_hom_hom_hom`: the pivotal isomorphism, which is the Drinfeld isomorphism,
  is the double-dual evaluation map;
* `FGModuleCat.trace_eq_smul`: the categorical trace is the linear trace;
* `FGModuleCat.quantumDim_eq_smul`: the quantum dimension is the dimension.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.7
-/

public section

open CategoryTheory MonoidalCategory Module TauCeti

namespace FGModuleCat

universe u

variable {K : Type u} [Field K]

/-- The Drinfeld isomorphism `V ≅ Vᘁᘁ` of a finite-dimensional vector space, which is the
canonical pivotal isomorphism `pivotalIsoApp V` by `TauCeti.pivotalIsoApp_eq_drinfeldIso`, is the
evaluation map of `V` into its double dual. -/
@[simp]
theorem drinfeldIso_hom_hom_hom (V : FGModuleCat.{u} K) :
    (drinfeldIso V).hom.hom.hom = Dual.eval K V := by
  ext x
  refine LinearMap.ext fun (ξ : Dual K V) => ?_
  have h := congrArg (fun g : V ⊗ Vᘁ ⟶ 𝟙_ (FGModuleCat K) => g.hom.hom (x ⊗ₜ ξ))
    (drinfeldIso_hom_comp_evaluation V)
  simp only [hom_hom_comp, LinearMap.comp_apply] at h
  simp only [evaluation_hom_hom, braiding_hom_hom_hom, whiskerRight_hom_hom] at h
  -- Now `h` reads `contractLeft K Vᘁ (rTensor Vᘁ d (x ⊗ₜ ξ)) = contractLeft K V (comm (x ⊗ₜ ξ))`
  -- with `d = (drinfeldIso V).hom.hom.hom`, while the goal `d x ξ = Dual.eval K V x ξ` is
  -- `d x ξ = ξ x` by `Dual.eval_apply`. Evaluating `h` on the pure tensor takes
  -- `LinearMap.rTensor_tmul`, `TensorProduct.comm_tmul` and `contractLeft_apply`. Neither `simp`
  -- nor `rw` can apply these here: `x ⊗ₜ ξ` lives in the carrier of the tensor product in
  -- `FGModuleCat K` rather than in `V ⊗[K] Dual K V`, and the double dual is written `↑Vᘁᘁ` rather
  -- than `Dual K (Dual K V)`. All four lemmas hold by `rfl`, and after them `h` is the goal.
  exact h

/-- The categorical trace of an endomorphism of a finite-dimensional vector space is its linear
trace, acting on the unit object by scalar multiplication. -/
@[simp]
theorem trace_eq_smul {V : FGModuleCat.{u} K} (f : V ⟶ V) :
    trace f = LinearMap.trace K V f.hom.hom • 𝟙 (𝟙_ (FGModuleCat K)) := by
  ext : 2
  simp only [ObjectProperty.tensorUnit_obj, ObjectProperty.smul_hom,
    ObjectProperty.FullSubcategory.id_hom, ModuleCat.hom_smul, ModuleCat.hom_id,
    LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_eq_mul, mul_one]
  rw [trace_eq_braiding, LinearMap.trace_eq_contractLeft_comm_rTensor_coevaluation]
  simp only [hom_hom_comp, LinearMap.comp_apply]
  simp only [coevaluation_hom_hom, braiding_hom_hom_hom, evaluation_hom_hom,
    whiskerRight_hom_hom]
  -- The two sides are now the same linear maps applied to `1`, except that the left writes the
  -- carrier of the dual object `Vᘁ` as `↑Vᘁ` and the right as `Module.Dual K V`. These agree by
  -- definition, since Mathlib's `Vᘁ` is `FGModuleCat.FGModuleCatDual K V`, built on `Dual K V`.
  rfl

/-- The quantum dimension of a finite-dimensional vector space is its dimension, acting on the
unit object by scalar multiplication. -/
@[simp]
theorem quantumDim_eq_smul (V : FGModuleCat.{u} K) :
    quantumDim V = (finrank K V : K) • 𝟙 (𝟙_ (FGModuleCat K)) := by
  rw [← trace_id, trace_eq_smul, hom_hom_id, LinearMap.trace_id]

end FGModuleCat
