/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Inversion
public import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
public import TauCeti.LinearAlgebra.CliffordAlgebra.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.VectorNormalizer.Basic

/-!
# The vector action of the vector normalizer

For a quadratic form `Q` on a module over a commutative ring, in every characteristic, twisted
conjugation `v ↦ α(g) v g⁻¹` by an element `g` of the vector normalizer
`CliffordAlgebra.vectorNormalizer Q` preserves the vectors `ι(M)`. Whenever `ι` is injective,
pulling it back along `ι` gives a linear automorphism of `M`, and these form a group
homomorphism `CliffordAlgebra.vectorNormalizerAction`. The map `ι` is injective for a free module
in every characteristic (`CliffordAlgebra.ι_injective_of_free`) and whenever `2` is invertible
(`CliffordAlgebra.ι_injective`); the action of the Lipschitz group
`CliffordAlgebra.lipschitzVectorAction` and the vector action of the Clifford group
`CliffordAlgebra.cliffordGroupToOrthogonal` are both restrictions of this one.

The Lipschitz group lies in the vector normalizer whenever `Q(m)` is a unit for every invertible
vector `ι(m)` (`CliffordAlgebra.lipschitzGroup_le_vectorNormalizer_of_isUnit`), in particular
whenever `2` is invertible (`CliffordAlgebra.lipschitzGroup_le_vectorNormalizer`).

## Main declarations

* `CliffordAlgebra.vectorNormalizerAction`: the vector action `vectorNormalizer Q →* M ≃ₗ[R] M`.
* `CliffordAlgebra.ι_vectorNormalizerAction_apply`: `ι (ρ(g) v) = α(g) ι(v) g⁻¹`.
* `CliffordAlgebra.vectorNormalizerAction_map_app`: `ρ(g)` preserves `Q` when the scalars embed
  in the Clifford algebra.
* `CliffordAlgebra.lipschitzGroup_le_vectorNormalizer_of_isUnit`,
  `CliffordAlgebra.lipschitzGroup_le_vectorNormalizer`: the Lipschitz group lies in the vector
  normalizer.
-/

public section

namespace CliffordAlgebra

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

/-- Twisted conjugation by an element of the vector normalizer, pulled back along an injective
`ι`. -/
private noncomputable def twistedVectorMap (hι : Function.Injective (ι Q))
    (x : vectorNormalizer Q) : M →ₗ[R] M :=
  LinearMap.codRestrictOfInjective
    ((LinearMap.mulRight R (((x : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) :
      CliffordAlgebra Q)).comp
        ((LinearMap.mulLeft R (involute ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))).comp
          (ι Q)))
    (ι Q) hι ((mem_vectorNormalizer_iff Q x).mp x.property).1

private theorem ι_twistedVectorMap (hι : Function.Injective (ι Q)) (x : vectorNormalizer Q)
    (m : M) :
    ι Q (twistedVectorMap hι x m) =
      involute ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q m *
        (((x : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) :=
  (LinearMap.codRestrictOfInjective_comp_apply _ _ _ _ m).trans <| by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply]

private noncomputable def twistedEndHom (hι : Function.Injective (ι Q)) :
    vectorNormalizer Q →* Module.End R M where
  toFun := twistedVectorMap hι
  map_one' := LinearMap.ext fun m => hι <| by simp [ι_twistedVectorMap]
  map_mul' x y := LinearMap.ext fun m => hι <| by
    rw [mul_apply_eq_comp, ι_twistedVectorMap, ι_twistedVectorMap, ι_twistedVectorMap]
    simp only [Subgroup.coe_mul, Units.val_mul, map_mul, mul_inv_rev, mul_assoc]

/-- **The vector action of the vector normalizer**, whenever `ι` is injective: `ρ(g)` is the
linear automorphism with `ι (ρ(g) v) = α(g) ι(v) g⁻¹`. -/
noncomputable def vectorNormalizerAction (hι : Function.Injective (ι Q)) :
    vectorNormalizer Q →* M ≃ₗ[R] M :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R M).toMonoidHom.comp
    (twistedEndHom hι).toHomUnits

/-- The vector action is twisted conjugation inside the Clifford algebra. -/
@[simp]
theorem ι_vectorNormalizerAction_apply (hι : Function.Injective (ι Q))
    (x : vectorNormalizer Q) (m : M) :
    ι Q (vectorNormalizerAction hι x m) =
      involute ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q m *
        (((x : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  rw [vectorNormalizerAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, MonoidHom.coe_toHomUnits]
  exact ι_twistedVectorMap hι x m

/-- **The vector normalizer acts by isometries**, `Q (ρ(g) v) = Q v`, whenever the scalars embed in
the Clifford algebra: for a free module in every characteristic
(`CliffordAlgebra.algebraMap_injective_of_free`) and whenever `2` is invertible
(`CliffordAlgebra.algebraMap_injective`). -/
theorem vectorNormalizerAction_map_app (hι : Function.Injective (ι Q))
    (hinj : Function.Injective (algebraMap R (CliffordAlgebra Q))) (x : vectorNormalizer Q)
    (m : M) : Q (vectorNormalizerAction hι x m) = Q m :=
  hinj (algebraMap_apply_eq_of_ι_eq_involute_mul_ι_mul_inv (ι_vectorNormalizerAction_apply hι x m))

/-! ### The Lipschitz group -/

variable (Q) in
/-- **The Lipschitz group lies in the vector normalizer** when `Q(m)` is a unit for every
invertible vector `ι(m)`. The twisted conjugation by an invertible vector `ι(a)` is the reflection
`ι(b) ↦ ι(b - Q(a)⁻¹ polar(a, b) a)`, read off from the Clifford relations. -/
theorem lipschitzGroup_le_vectorNormalizer_of_isUnit (hQ : ∀ m, IsUnit (ι Q m) → IsUnit (Q m)) :
    lipschitzGroup Q ≤ vectorNormalizer Q := by
  rw [lipschitzGroup, Subgroup.closure_le]
  rintro x ⟨a, ha⟩
  -- As in Mathlib's `lipschitzGroup.involute_act_ι_mem_range_ι`, with `hQ` in place of
  -- `invertibleOfInvertibleι`.
  let := x.invertible
  let : Invertible (ι Q a) := by rwa [ha]
  let : Invertible (Q a) := (hQ a (by rw [ha]; exact x.isUnit)).invertible
  refine (mem_vectorNormalizer_iff Q x).mpr ⟨fun b => ?_, fun b => ?_⟩
  · simp_rw [← invOf_units x, ← ha, involute_ι, neg_mul, ι_mul_ι_mul_invOf_ι Q a b, ← map_neg,
      LinearMap.mem_range_self]
  · let := invertibleNeg (ι Q a)
    let := Invertible.map involute (ι Q a)
    simp_rw [← invOf_units x, ← ha, map_invOf, involute_ι, invOf_neg, neg_mul,
      invOf_ι_mul_ι_mul_ι, ← map_neg, LinearMap.mem_range_self]

variable (Q) in
/-- **The Lipschitz group lies in the vector normalizer** when `2` is invertible. -/
theorem lipschitzGroup_le_vectorNormalizer [Invertible (2 : R)] :
    lipschitzGroup Q ≤ vectorNormalizer Q :=
  lipschitzGroup_le_vectorNormalizer_of_isUnit Q fun _ => isUnit_of_isUnit_ι Q

end CliffordAlgebra
