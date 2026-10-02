/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import TauCeti.Algebra.Coalgebra.Comodule.ExteriorAlgebra.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.OfInjective

/-!
# Exterior powers as comodules

The homogeneous exterior powers of a right comodule over a commutative bialgebra are
comodules in their own right. The grading splits their inclusions into the exterior
algebra, so no flatness assumption on the bialgebra is needed. Mathlib's finite-generation
instance makes these finite comodules whenever the original module is finite.

The inclusion and maps induced by comodule morphisms are equivariant. The wedge formula
for the point action describes this finite representation inside the scalar extension of
the exterior algebra. It is the homogeneous representation used to replace a subspace
stabilizer by the stabilizer of its top exterior line.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 4.27 and Lemma 4.28.

The construction uses Mathlib's `DirectSum.subtype_rTensor_injective` and
`LinearMap.codRestrictOfInjective`, as does the flat-subcomodule construction in
`TauCeti.Algebra.Coalgebra.Subcomodule.Induced`; the exterior grading replaces flatness here.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

variable {R H M N P : Type*} [CommRing R] [CommSemiring H] [Bialgebra R H]
  [AddCommGroup M] [Module R M] [Comodule R H M]
  [AddCommGroup N] [Module R N] [Comodule R H N]
  [AddCommGroup P] [Module R P] [Comodule R H P]

attribute [local instance] exteriorAlgebra

variable (R H M) in
/-- The coaction on the `n`th exterior power, obtained by restricting the multiplicative
coaction on the exterior algebra to its homogeneous degree `n`. -/
noncomputable def exteriorPowerCoact (n : ℕ) :
    (⋀[R]^n M) →ₗ[R] (⋀[R]^n M) ⊗[R] H :=
  LinearMap.codRestrictOfInjective
    ((exteriorAlgebraCoact R H M).toLinearMap ∘ₗ (⋀[R]^n M).subtype)
    ((⋀[R]^n M).subtype.rTensor H)
    (DirectSum.subtype_rTensor_injective (fun i : ℕ ↦ ⋀[R]^i M) H n)
    (fun x ↦ by
      rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Submodule.subtype_apply,
        ← DirectSum.decomposeTensor_apply]
      exact exteriorAlgebraCoact_mem_decomposeTensor x.2)

/-- Including the exterior-power coaction recovers the coaction on the exterior algebra. -/
@[simp]
theorem subtype_rTensor_exteriorPowerCoact (n : ℕ) (x : ⋀[R]^n M) :
    (⋀[R]^n M).subtype.rTensor H (exteriorPowerCoact R H M n x) =
      exteriorAlgebraCoact R H M x := by
  exact LinearMap.codRestrictOfInjective_comp_apply _ _ _ _ x

variable (R H M) in
/-- The `n`th exterior power of a comodule. This is not a global instance: select it
explicitly, as with `Comodule.exteriorAlgebra`. No flatness hypothesis on `H` is needed. -/
@[implicit_reducible]
noncomputable def exteriorPower (n : ℕ) : Comodule R H (⋀[R]^n M) :=
  ofInjective (exteriorPowerCoact R H M n) (⋀[R]^n M).subtype
    Subtype.val_injective
    (DirectSum.subtype_rTensor_injective (fun i : ℕ ↦ ⋀[R]^i M) (H ⊗[R] H) n)
    (by ext x; simp)

attribute [local instance] exteriorPower

/-- The exterior-power comodule has the homogeneous restriction coaction. -/
@[simp]
theorem exteriorPower_coact (n : ℕ) :
    coact (R := R) (C := H) (M := ⋀[R]^n M) = exteriorPowerCoact R H M n := by
  apply ofInjective_coact

namespace Hom

variable (R H M) in
/-- The inclusion of a homogeneous exterior power into the exterior algebra, as a
comodule morphism. -/
noncomputable def exteriorPowerSubtype (n : ℕ) : Hom R H (⋀[R]^n M) (ExteriorAlgebra R M) where
  toLinearMap := (⋀[R]^n M).subtype
  map_coact := by
    ext x
    simp [← LinearMap.rTensor_def]

@[simp]
theorem exteriorPowerSubtype_toLinearMap (n : ℕ) :
    (exteriorPowerSubtype R H M n).toLinearMap = (⋀[R]^n M).subtype :=
  (rfl)

@[simp]
theorem exteriorPowerSubtype_apply (n : ℕ) (x : ⋀[R]^n M) :
    exteriorPowerSubtype R H M n x = (x : ExteriorAlgebra R M) :=
  (rfl)

/-- The map of exterior powers induced by a comodule morphism, with Mathlib's
`exteriorPower.map` as its underlying linear map. -/
noncomputable def exteriorPowerMap (n : ℕ) (f : Hom R H M N) :
    Hom R H (⋀[R]^n M) (⋀[R]^n N) where
  toLinearMap := _root_.exteriorPower.map n f.toLinearMap
  map_coact := by
    ext x
    apply DirectSum.subtype_rTensor_injective (fun i : ℕ ↦ ⋀[R]^i N) H n
    simp only [LinearMap.comp_apply, exteriorPower_coact, LinearMap.rTensor_def,
      TensorProduct.map_map, LinearMap.comp_id,
      _root_.exteriorPower.subtype_comp_map_eq]
    simp only [← LinearMap.rTensor_def, LinearMap.rTensor_comp_apply,
      subtype_rTensor_exteriorPowerCoact, _root_.exteriorPower.coe_map]
    simpa only [exteriorAlgebraMap_toLinearMap, exteriorAlgebra_coact,
      AlgHom.toLinearMap_apply, exteriorAlgebraMap_apply, ← LinearMap.rTensor_def] using
      (Hom.exteriorAlgebraMap f).map_coact_apply x

@[simp]
theorem exteriorPowerMap_toLinearMap (n : ℕ) (f : Hom R H M N) :
    (exteriorPowerMap n f).toLinearMap = _root_.exteriorPower.map n f.toLinearMap :=
  (rfl)

@[simp]
theorem exteriorPowerMap_apply (n : ℕ) (f : Hom R H M N) (x : ⋀[R]^n M) :
    exteriorPowerMap n f x = _root_.exteriorPower.map n f.toLinearMap x :=
  (rfl)

/-- Exterior-power maps preserve identity morphisms. -/
theorem exteriorPowerMap_id (n : ℕ) : exteriorPowerMap n (id R H M) = id R H (⋀[R]^n M) := by
  apply Hom.toLinearMap_injective
  simp

/-- Exterior-power maps preserve composition. -/
@[simp]
theorem exteriorPowerMap_comp (n : ℕ) (g : Hom R H N P) (f : Hom R H M N) :
    exteriorPowerMap n (g.comp f) = (exteriorPowerMap n g).comp (exteriorPowerMap n f) := by
  apply Hom.toLinearMap_injective
  simp

/-- Exterior-power maps commute with their homogeneous inclusions. -/
@[simp]
theorem exteriorPowerSubtype_comp_exteriorPowerMap (n : ℕ) (f : Hom R H M N) :
    (exteriorPowerSubtype R H N n).comp (exteriorPowerMap n f) =
      (exteriorAlgebraMap f).comp (exteriorPowerSubtype R H M n) := by
  apply Hom.toLinearMap_injective
  simpa only [comp_toLinearMap, exteriorPowerSubtype_toLinearMap,
    exteriorPowerMap_toLinearMap, exteriorAlgebraMap_toLinearMap] using
    _root_.exteriorPower.subtype_comp_map_eq f.toLinearMap

end Hom

section Points

variable {A : Type*} [CommSemiring A] [Algebra R A]

/-- In the scalar-extended exterior algebra, a point acts on a pure wedge by acting on
each generator and multiplying. This describes the point action on the finite-degree
comodule, including degree zero and nonreduced value algebras. -/
theorem baseChange_subtype_endOfPoint_ιMulti (n : ℕ) (g : H →ₐ[R] A)
    (a : A) (v : Fin n → M) :
    (⋀[R]^n M).subtype.baseChange A
        (endOfPoint (⋀[R]^n M) g (a ⊗ₜ[R] _root_.exteriorPower.ιMulti R n v)) =
      a • (List.ofFn fun i ↦
        (ExteriorAlgebra.ι R).baseChange A (endOfPoint M g (1 ⊗ₜ[R] v i))).prod := by
  have hsub := LinearMap.congr_fun
    (baseChange_comp_endOfPoint (Hom.exteriorPowerSubtype R H M n) g)
    (a ⊗ₜ[R] _root_.exteriorPower.ιMulti R n v)
  simp only [LinearMap.comp_apply, Hom.exteriorPowerSubtype_toLinearMap,
    LinearMap.baseChange_tmul, Submodule.subtype_apply,
    _root_.exteriorPower.ιMulti_apply_coe] at hsub
  have ht (x : ExteriorAlgebra R M) : a ⊗ₜ[R] x = a • (1 ⊗ₜ[R] x) := by
    simp [TensorProduct.smul_tmul', smul_eq_mul]
  rw [hsub, ← exteriorAlgebraEndOfPoint_apply, ht, map_smul]
  congr 1
  have hι (m : M) :
      exteriorAlgebraEndOfPoint g (1 ⊗ₜ[R] ExteriorAlgebra.ι R m) =
        (ExteriorAlgebra.ι R).baseChange A (endOfPoint M g (1 ⊗ₜ[R] m)) := by
    have h := LinearMap.congr_fun
      (baseChange_comp_endOfPoint (Hom.exteriorAlgebraι R H M) g) (1 ⊗ₜ[R] m)
    simpa only [LinearMap.comp_apply, Hom.exteriorAlgebraι_toLinearMap,
      LinearMap.baseChange_tmul, exteriorAlgebraEndOfPoint_apply] using h.symm
  rw [ExteriorAlgebra.ιMulti_apply]
  -- `includeRight` is the multiplicative map `x ↦ 1 ⊗ x`.
  have hprod := map_list_prod
    ((exteriorAlgebraEndOfPoint (M := M) g).restrictScalars R |>.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := A)))
    (List.ofFn fun i ↦ ExteriorAlgebra.ι R (v i))
  simpa only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.includeRight_apply, List.map_ofFn, Function.comp_def, hι] using hprod

end Points

end TauCeti.Comodule
