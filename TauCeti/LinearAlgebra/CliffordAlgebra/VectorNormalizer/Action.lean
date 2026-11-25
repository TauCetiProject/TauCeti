/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.VectorNormalizer.Basic

/-!
# The vector action of the vector normalizer on a free module

For a quadratic form `Q` on a free module `M` over a commutative ring, in every characteristic,
twisted conjugation `v ↦ α(g) v g⁻¹` by an element `g` of the vector normalizer
`CliffordAlgebra.vectorNormalizer Q` preserves the vectors `ι(M)`. Reading off the vector with the
left inverse `CliffordAlgebra.vectorPart` of `ι` gives a linear automorphism of `M`, and these
form a group homomorphism `CliffordAlgebra.vectorNormalizerAction`.

## Main declarations

* `CliffordAlgebra.vectorNormalizerAction`: the vector action `vectorNormalizer Q →* M ≃ₗ[R] M`.
* `CliffordAlgebra.ι_vectorNormalizerAction_apply`: `ι (ρ(g) v) = α(g) ι(v) g⁻¹`.
* `CliffordAlgebra.vectorNormalizerAction_map_app`: `ρ(g)` preserves `Q`.
-/

public section

namespace CliffordAlgebra

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Free R M] {Q : QuadraticForm R M}

variable (Q) in
/-- Twisted conjugation by a unit, followed by the vector part. -/
private noncomputable def twistedVectorMap (x : (CliffordAlgebra Q)ˣ) : M →ₗ[R] M where
  toFun m := vectorPart Q (involute (x : CliffordAlgebra Q) * ι Q m * ↑x⁻¹)
  map_add' a b := by rw [map_add, mul_add, add_mul, map_add]
  map_smul' r a := by rw [map_smul, mul_smul_comm, smul_mul_assoc, map_smul, RingHom.id_apply]

private theorem twistedVectorMap_apply (x : (CliffordAlgebra Q)ˣ) (m : M) :
    twistedVectorMap Q x m = vectorPart Q (involute (x : CliffordAlgebra Q) * ι Q m * ↑x⁻¹) :=
  rfl

private theorem ι_twistedVectorMap {x : (CliffordAlgebra Q)ˣ} (hx : x ∈ vectorNormalizer Q)
    (m : M) :
    ι Q (twistedVectorMap Q x m) = involute (x : CliffordAlgebra Q) * ι Q m * ↑x⁻¹ := by
  obtain ⟨w, hw⟩ := ((mem_vectorNormalizer_iff Q x).mp hx).1 m
  rw [twistedVectorMap_apply, ← hw, vectorPart_ι]

variable (Q) in
private noncomputable def twistedEndHom : vectorNormalizer Q →* Module.End R M where
  toFun x := twistedVectorMap Q x
  map_one' := LinearMap.ext fun m => ι_injective_of_free Q <| by
    rw [ι_twistedVectorMap (1 : vectorNormalizer Q).property]
    simp
  map_mul' x y := LinearMap.ext fun m => ι_injective_of_free Q <| by
    rw [mul_apply_eq_comp, ι_twistedVectorMap ((x * y).property), ι_twistedVectorMap x.property,
      ι_twistedVectorMap y.property]
    simp only [Subgroup.coe_mul, Units.val_mul, map_mul, mul_inv_rev, mul_assoc]

variable (Q) in
/-- **The vector action of the vector normalizer** on a free module: `ρ(g)` is the linear
automorphism with `ι (ρ(g) v) = α(g) ι(v) g⁻¹`. -/
noncomputable def vectorNormalizerAction : vectorNormalizer Q →* M ≃ₗ[R] M :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R M).toMonoidHom.comp
    (twistedEndHom Q).toHomUnits

/-- The vector action is twisted conjugation inside the Clifford algebra. -/
@[simp]
theorem ι_vectorNormalizerAction_apply (x : vectorNormalizer Q) (m : M) :
    ι Q (vectorNormalizerAction Q x m) =
      involute ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q m *
        (((x : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  rw [vectorNormalizerAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, MonoidHom.coe_toHomUnits]
  exact ι_twistedVectorMap x.property m

/-- **The vector normalizer acts by isometries**: `Q (ρ(g) v) = Q v`. -/
theorem vectorNormalizerAction_map_app (x : vectorNormalizer Q) (m : M) :
    Q (vectorNormalizerAction Q x m) = Q m :=
  algebraMap_injective_of_free Q
    (algebraMap_apply_eq_of_ι_eq_involute_mul_ι_mul_inv (ι_vectorNormalizerAction_apply x m))

end CliffordAlgebra
