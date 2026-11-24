/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.LocalizedModule.BaseChange
public import TauCeti.RingTheory.TensorProduct.IsBaseChange
public import TauCeti.RingTheory.TensorProduct.LiftEquiv
public import Mathlib.RingTheory.TensorProduct.Maps
import TauCeti.Algebra.TensorProduct.BaseChange

/-!
# Algebra equivalences from base-change and localization comparisons

Let `R → S` be a homomorphism of commutative semirings, `A` an `R`-algebra, and `B` an `S`-algebra
over `R` (neither `A` nor `B` need be commutative). For an `R`-algebra map `f : A →ₐ[R] B`, the
induced `S`-algebra map `f.liftEquiv R S A B : S ⊗[R] A →ₐ[S] B` has underlying `S`-linear map
`f.toLinearMap.liftBaseChange S` (`AlgHom.liftEquiv_toLinearMap`). When `f.toLinearMap` satisfies
`IsBaseChange S`, this induced algebra map is bijective and therefore upgrades `IsBaseChange.equiv`
to an `S`-algebra equivalence `IsBaseChange.algEquiv : S ⊗[R] A ≃ₐ[S] B`.

Similarly, when `R'` is a localization of `R` at a submonoid `T` and `f : A →ₐ[R] B` is an
`R`-algebra map, injectivity, surjectivity, and bijectivity of
`Algebra.TensorProduct.map (AlgHom.id S R') f : R' ⊗[R] A →ₐ[S] R' ⊗[R] B` (for any intermediate
commutative semiring `S` between `R` and `R'`) coincide with the corresponding properties of
`LocalizedModule.map T f.toLinearMap`. In particular, bijectivity after localization defines an
`R'`-algebra equivalence `AlgHom.algEquivOfLocalizedBijective`.

## Main declarations

* `IsBaseChange.iff_liftEquiv_bijective`: `IsBaseChange S f.toLinearMap` holds if and only if
  `f.liftEquiv R S A B` is bijective.
* `IsBaseChange.algEquiv`: the `S`-algebra equivalence `S ⊗[R] A ≃ₐ[S] B` induced by an
  `R`-algebra map `f : A →ₐ[R] B` whose underlying linear map satisfies `IsBaseChange S`.
* `AlgHom.injective_tensorProduct_map_id_iff`, `AlgHom.surjective_tensorProduct_map_id_iff`,
  `AlgHom.bijective_tensorProduct_map_id_iff`: for a localization `R'` of `R` at `T` over an
  intermediate semiring `S`, injectivity, surjectivity, and bijectivity of
  `Algebra.TensorProduct.map (AlgHom.id S R') f` coincide with those of
  `LocalizedModule.map T f.toLinearMap`.
* `AlgHom.algEquivOfLocalizedBijective`: the `R'`-algebra equivalence `R' ⊗[R] A ≃ₐ[R'] R' ⊗[R] B`
  induced by an `R`-algebra map whose localization at `T` is bijective.
-/

public section

open Function TensorProduct

section IsBaseChange

variable {R S A B : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]

/-- An `R`-algebra map `f : A →ₐ[R] B` exhibits `B` as the module base change of `A` along
`R → S` if and only if the induced `S`-algebra map `f.liftEquiv R S A B` is bijective. -/
theorem IsBaseChange.iff_liftEquiv_bijective {f : A →ₐ[R] B} :
    IsBaseChange S f.toLinearMap ↔ Bijective (f.liftEquiv R S A B) := by
  rw [← AlgHom.coe_toLinearMap, AlgHom.liftEquiv_toLinearMap]
  exact IsBaseChange.iff_liftBaseChange_bijective

/-- **Base-change equivalence for algebras.** If an `R`-algebra map `f : A →ₐ[R] B` into an
`S`-algebra exhibits `B` as the module base change of `A` along `R → S`, then `s ⊗ a ↦ s • f a`
is an `S`-algebra equivalence `S ⊗[R] A ≃ₐ[S] B`. Neither `A` nor `B` need be commutative. -/
noncomputable def IsBaseChange.algEquiv {f : A →ₐ[R] B} (hf : IsBaseChange S f.toLinearMap) :
    S ⊗[R] A ≃ₐ[S] B :=
  AlgEquiv.ofBijective (f.liftEquiv R S A B) (IsBaseChange.iff_liftEquiv_bijective.mp hf)

@[simp]
theorem IsBaseChange.toAlgHom_algEquiv {f : A →ₐ[R] B} (hf : IsBaseChange S f.toLinearMap) :
    hf.algEquiv.toAlgHom = f.liftEquiv R S A B := by
  ext a
  simp [IsBaseChange.algEquiv]

@[simp]
theorem IsBaseChange.algEquiv_tmul {f : A →ₐ[R] B} (hf : IsBaseChange S f.toLinearMap)
    (s : S) (a : A) :
    hf.algEquiv (s ⊗ₜ[R] a) = s • f a := by
  simp [IsBaseChange.algEquiv]

theorem IsBaseChange.algEquiv_one_tmul {f : A →ₐ[R] B} (hf : IsBaseChange S f.toLinearMap)
    (a : A) :
    hf.algEquiv (1 ⊗ₜ[R] a) = f a := by
  simp

@[simp]
theorem IsBaseChange.algEquiv_symm_apply {f : A →ₐ[R] B} (hf : IsBaseChange S f.toLinearMap)
    (a : A) :
    hf.algEquiv.symm (f a) = 1 ⊗ₜ[R] a := by
  apply hf.algEquiv.injective
  simp

@[simp]
theorem IsBaseChange.toLinearEquiv_algEquiv {f : A →ₐ[R] B} (hf : IsBaseChange S f.toLinearMap) :
    hf.algEquiv.toLinearEquiv = hf.equiv := by
  apply LinearEquiv.toLinearMap_inj.mp
  ext a
  simp [IsBaseChange.equiv_tmul]

theorem IsBaseChange.algEquiv_comp_includeRight {f : A →ₐ[R] B}
    (hf : IsBaseChange S f.toLinearMap) :
    (hf.algEquiv.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight = f := by
  simp

end IsBaseChange

namespace AlgHom

variable {R : Type*} [CommSemiring R] (T : Submonoid R)
  (R' : Type*) [CommSemiring R'] [Algebra R R'] [IsLocalization T R']
  {A B : Type*} [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- Extending an `R`-algebra map `f : A →ₐ[R] B` to a localization `R'` of `R` at `T` is injective
if and only if `LocalizedModule.map T f.toLinearMap` is injective. -/
theorem injective_tensorProduct_map_id_iff {S : Type*} [CommSemiring S] [Algebra R S]
    [Algebra S R'] [IsScalarTower R S R'] (f : A →ₐ[R] B) :
    Injective (Algebra.TensorProduct.map (AlgHom.id S R') f) ↔
      Injective (LocalizedModule.map T f.toLinearMap) := by
  rw [coe_tensorProduct_map_id, IsLocalization.baseChange_injective_iff T R']

/-- Extending an `R`-algebra map `f : A →ₐ[R] B` to a localization `R'` of `R` at `T` is surjective
if and only if `LocalizedModule.map T f.toLinearMap` is surjective. -/
theorem surjective_tensorProduct_map_id_iff {S : Type*} [CommSemiring S] [Algebra R S]
    [Algebra S R'] [IsScalarTower R S R'] (f : A →ₐ[R] B) :
    Surjective (Algebra.TensorProduct.map (AlgHom.id S R') f) ↔
      Surjective (LocalizedModule.map T f.toLinearMap) := by
  rw [coe_tensorProduct_map_id, IsLocalization.baseChange_surjective_iff T R']

/-- Extending an `R`-algebra map `f : A →ₐ[R] B` to a localization `R'` of `R` at `T` is bijective
if and only if `LocalizedModule.map T f.toLinearMap` is bijective. -/
theorem bijective_tensorProduct_map_id_iff {S : Type*} [CommSemiring S] [Algebra R S]
    [Algebra S R'] [IsScalarTower R S R'] (f : A →ₐ[R] B) :
    Bijective (Algebra.TensorProduct.map (AlgHom.id S R') f) ↔
      Bijective (LocalizedModule.map T f.toLinearMap) := by
  rw [coe_tensorProduct_map_id, IsLocalization.baseChange_bijective_iff T R']

/-- If an `R`-algebra map `f : A →ₐ[R] B` becomes bijective after module localization at `T`, then
scalar extension to any localization `R'` of `R` at `T` gives an `R'`-algebra equivalence
`R' ⊗[R] A ≃ₐ[R'] R' ⊗[R] B`. -/
noncomputable def algEquivOfLocalizedBijective (f : A →ₐ[R] B)
    (hf : Bijective (LocalizedModule.map T f.toLinearMap)) :
    R' ⊗[R] A ≃ₐ[R'] R' ⊗[R] B :=
  AlgEquiv.ofBijective (Algebra.TensorProduct.map (AlgHom.id R' R') f)
    ((bijective_tensorProduct_map_id_iff T R' f).mpr hf)

@[simp]
theorem toAlgHom_algEquivOfLocalizedBijective (f : A →ₐ[R] B)
    (hf : Bijective (LocalizedModule.map T f.toLinearMap)) :
    (f.algEquivOfLocalizedBijective T R' hf).toAlgHom =
      Algebra.TensorProduct.map (AlgHom.id R' R') f := by
  ext a
  simp [algEquivOfLocalizedBijective]

@[simp]
theorem algEquivOfLocalizedBijective_tmul (f : A →ₐ[R] B)
    (hf : Bijective (LocalizedModule.map T f.toLinearMap)) (r' : R') (a : A) :
    f.algEquivOfLocalizedBijective T R' hf (r' ⊗ₜ[R] a) = r' ⊗ₜ[R] f a := by
  simp [algEquivOfLocalizedBijective]

@[simp]
theorem algEquivOfLocalizedBijective_symm_tmul (f : A →ₐ[R] B)
    (hf : Bijective (LocalizedModule.map T f.toLinearMap)) (r' : R') (a : A) :
    (f.algEquivOfLocalizedBijective T R' hf).symm (r' ⊗ₜ[R] f a) = r' ⊗ₜ[R] a := by
  apply (f.algEquivOfLocalizedBijective T R' hf).injective
  simp

end AlgHom
