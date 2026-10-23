/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.ExteriorAlgebra.Power

/-!
# Exterior comodules and restriction of representations

Exterior algebra and exterior power commute with corestriction along a morphism of
commutative bialgebras. For coordinate algebras of affine groups, this says that taking
exterior powers commutes with restricting a representation to a subgroup.

The equalities identify the two comodule structures on the same underlying module.
They allow exterior powers of subgroup representations to be used inside the restriction
of the ambient exterior representation. No flatness or finite-generation assumption is needed.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 4.27 and Lemma 4.28.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

variable {R H K M : Type*} [CommRing R]
  [CommSemiring H] [Bialgebra R H] [CommSemiring K] [Bialgebra R K]
  [AddCommGroup M] [Module R M] [Comodule R H M]

/-- The multiplicative exterior coaction commutes with a bialgebra morphism. -/
theorem exteriorAlgebraCoact_corestrict (f : H →ₐc[R] K) :
    let : Comodule R K M := Corestrict f.toCoalgHom
    exteriorAlgebraCoact R K M =
      (Algebra.TensorProduct.map (AlgHom.id R (ExteriorAlgebra R M)) f.toAlgHom).comp
        (exteriorAlgebraCoact R H M) := by
  let : Comodule R K M := Corestrict f.toCoalgHom
  apply ExteriorAlgebra.hom_ext
  ext m
  simp only [AlgHom.comp_toLinearMap, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, exteriorAlgebraCoact_ι, corestrict_coact_apply,
    ExteriorAlgebra.map_id_rTensor_ι]
  rfl

/-- Restricting the exterior-algebra representation agrees with taking the exterior
algebra of the restricted representation. -/
theorem exteriorAlgebra_corestrict (f : H →ₐc[R] K) :
    let : Comodule R H (ExteriorAlgebra R M) := exteriorAlgebra R H M
    let restricted := Corestrict f.toCoalgHom (M := ExteriorAlgebra R M)
    let : Comodule R K M := Corestrict f.toCoalgHom
    exteriorAlgebra R K M = restricted := by
  let : Comodule R H (ExteriorAlgebra R M) := exteriorAlgebra R H M
  let : Comodule R K M := Corestrict f.toCoalgHom
  apply Comodule.ext
  apply LinearMap.ext
  intro x
  simp only [exteriorAlgebra_coact, corestrict_coact, corestrictCoact_apply,
    exteriorAlgebraCoact_corestrict, AlgHom.comp_toLinearMap, LinearMap.comp_apply,
    Algebra.TensorProduct.toLinearMap_map, TensorProduct.AlgebraTensorModule.map_eq,
    AlgHom.toLinearMap_id]
  rfl

/-- The homogeneous exterior coaction commutes with a bialgebra morphism. -/
theorem exteriorPowerCoact_corestrict (f : H →ₐc[R] K) (n : ℕ) :
    let : Comodule R K M := Corestrict f.toCoalgHom
    exteriorPowerCoact R K M n =
      TensorProduct.map LinearMap.id f.toLinearMap ∘ₗ exteriorPowerCoact R H M n := by
  let : Comodule R K M := Corestrict f.toCoalgHom
  ext x
  apply DirectSum.subtype_rTensor_injective (fun i : ℕ ↦ ⋀[R]^i M) K n
  simp only [LinearMap.comp_apply, subtype_rTensor_exteriorPowerCoact,
    exteriorAlgebraCoact_corestrict, AlgHom.comp_apply]
  rw [← AlgHom.toLinearMap_apply, Algebra.TensorProduct.toLinearMap_map,
    TensorProduct.AlgebraTensorModule.map_eq, AlgHom.toLinearMap_id]
  rw [← subtype_rTensor_exteriorPowerCoact (R := R) (H := H) n x]
  simp only [LinearMap.rTensor_def, TensorProduct.map_map, LinearMap.comp_id,
    LinearMap.id_comp]
  rfl

/-- Restricting an exterior-power representation agrees with taking the exterior
power of the restricted representation, including degree zero. -/
theorem exteriorPower_corestrict (f : H →ₐc[R] K) (n : ℕ) :
    let : Comodule R H (⋀[R]^n M) := exteriorPower R H M n
    let restricted := Corestrict f.toCoalgHom (M := ⋀[R]^n M)
    let : Comodule R K M := Corestrict f.toCoalgHom
    exteriorPower R K M n = restricted := by
  let : Comodule R H (⋀[R]^n M) := exteriorPower R H M n
  let : Comodule R K M := Corestrict f.toCoalgHom
  apply Comodule.ext
  apply LinearMap.ext
  intro x
  simp only [exteriorPower_coact, corestrict_coact, corestrictCoact_apply,
    exteriorPowerCoact_corestrict, LinearMap.comp_apply]

end TauCeti.Comodule
