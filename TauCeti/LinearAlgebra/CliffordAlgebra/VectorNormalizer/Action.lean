/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.VectorNormalizer.Basic

/-!
# The vector action of the vector normalizer

For a quadratic form `Q` on a module over a commutative ring, in every characteristic, twisted
conjugation `v ↦ α(g) v g⁻¹` by an element `g` of the vector normalizer
`CliffordAlgebra.vectorNormalizer Q` preserves the vectors `ι(M)`. Reading off the vector with a
linear left inverse `p` of `ι` gives a linear automorphism of `M`, and these form a group
homomorphism `CliffordAlgebra.vectorNormalizerAction`. Its values do not depend on `p`
(`CliffordAlgebra.ι_vectorNormalizerAction_apply`). Such a `p` exists for a free module in every
characteristic (`CliffordAlgebra.exists_leftInverse_ι_of_free`) and whenever `2` is invertible
(`CliffordAlgebra.ι_leftInverse`); the action of the Lipschitz group
`CliffordAlgebra.lipschitzVectorAction` and the vector action of the Clifford group
`CliffordAlgebra.gpinToOrthogonal` are both restrictions of this one.

## Main declarations

* `CliffordAlgebra.vectorNormalizerAction`: the vector action `vectorNormalizer Q →* M ≃ₗ[R] M`.
* `CliffordAlgebra.ι_vectorNormalizerAction_apply`: `ι (ρ(g) v) = α(g) ι(v) g⁻¹`.
* `CliffordAlgebra.vectorNormalizerAction_map_app`: `ρ(g)` preserves `Q` when the scalars embed
  in the Clifford algebra.
-/

public section

namespace CliffordAlgebra

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M} {p : CliffordAlgebra Q →ₗ[R] M}

variable (p) in
/-- Twisted conjugation by a unit, followed by a linear map `p` back to the module. -/
private def twistedVectorMap (x : (CliffordAlgebra Q)ˣ) : M →ₗ[R] M where
  toFun m := p (involute (x : CliffordAlgebra Q) * ι Q m * ↑x⁻¹)
  map_add' a b := by rw [map_add, mul_add, add_mul, map_add]
  map_smul' r a := by rw [map_smul, mul_smul_comm, smul_mul_assoc, map_smul, RingHom.id_apply]

private theorem twistedVectorMap_apply (x : (CliffordAlgebra Q)ˣ) (m : M) :
    twistedVectorMap p x m = p (involute (x : CliffordAlgebra Q) * ι Q m * ↑x⁻¹) :=
  rfl

private theorem ι_twistedVectorMap (hp : Function.LeftInverse p (ι Q)) {x : (CliffordAlgebra Q)ˣ}
    (hx : x ∈ vectorNormalizer Q) (m : M) :
    ι Q (twistedVectorMap p x m) = involute (x : CliffordAlgebra Q) * ι Q m * ↑x⁻¹ := by
  obtain ⟨w, hw⟩ := ((mem_vectorNormalizer_iff Q x).mp hx).1 m
  rw [twistedVectorMap_apply, ← hw, hp]

private def twistedEndHom (hp : Function.LeftInverse p (ι Q)) :
    vectorNormalizer Q →* Module.End R M where
  toFun x := twistedVectorMap p x
  map_one' := LinearMap.ext fun m => hp.injective <| by
    rw [ι_twistedVectorMap hp (1 : vectorNormalizer Q).property]
    simp
  map_mul' x y := LinearMap.ext fun m => hp.injective <| by
    rw [mul_apply_eq_comp, ι_twistedVectorMap hp ((x * y).property),
      ι_twistedVectorMap hp x.property, ι_twistedVectorMap hp y.property]
    simp only [Subgroup.coe_mul, Units.val_mul, map_mul, mul_inv_rev, mul_assoc]

/-- **The vector action of the vector normalizer**, read off through a linear left inverse `p` of
`ι`: `ρ(g)` is the linear automorphism with `ι (ρ(g) v) = α(g) ι(v) g⁻¹`, so it does not depend
on `p` (`ι_vectorNormalizerAction_apply`). -/
def vectorNormalizerAction (hp : Function.LeftInverse p (ι Q)) :
    vectorNormalizer Q →* M ≃ₗ[R] M :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R M).toMonoidHom.comp
    (twistedEndHom hp).toHomUnits

/-- The vector action is twisted conjugation inside the Clifford algebra. -/
@[simp]
theorem ι_vectorNormalizerAction_apply (hp : Function.LeftInverse p (ι Q))
    (x : vectorNormalizer Q) (m : M) :
    ι Q (vectorNormalizerAction hp x m) =
      involute ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q m *
        (((x : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  rw [vectorNormalizerAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, MonoidHom.coe_toHomUnits]
  exact ι_twistedVectorMap hp x.property m

/-- **The vector normalizer acts by isometries**, `Q (ρ(g) v) = Q v`, whenever the scalars embed in
the Clifford algebra: for a free module in every characteristic
(`CliffordAlgebra.algebraMap_injective_of_free`) and whenever `2` is invertible
(`CliffordAlgebra.algebraMap_injective`). -/
theorem vectorNormalizerAction_map_app (hp : Function.LeftInverse p (ι Q))
    (hinj : Function.Injective (algebraMap R (CliffordAlgebra Q))) (x : vectorNormalizer Q)
    (m : M) : Q (vectorNormalizerAction hp x m) = Q m :=
  hinj (algebraMap_apply_eq_of_ι_eq_involute_mul_ι_mul_inv (ι_vectorNormalizerAction_apply hp x m))

end CliffordAlgebra
