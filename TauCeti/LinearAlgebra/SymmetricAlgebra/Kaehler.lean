/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Derivation.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
public import TauCeti.RingTheory.Kaehler.MapSemilinear
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Kähler differentials of symmetric algebras

For any commutative ring `R` and `R`-module `M`, the module of Kähler differentials of
`SymmetricAlgebra R M` over `R` is canonically isomorphic as a `SymmetricAlgebra R M`-module to
`SymmetricAlgebra R M ⊗[R] M` (`SymmetricAlgebra.kaehlerDifferentialEquiv`): the differential
`d(ι m)` of a generator corresponds to `1 ⊗ₜ m`. No freeness, projectivity, or finiteness assumption
on `M` is required.

Both directions come from the two universal properties:
* the derivation `SymmetricAlgebra.mkDerivation (TensorProduct.mk R _ M 1)` sends `ι m` to
  `1 ⊗ₜ m`, and `Derivation.liftKaehlerDifferential` extends it `SymmetricAlgebra R M`-linearly
  out of `Ω[SymmetricAlgebra R M⁄R]`;
* the `R`-linear map `m ↦ d(ι m)` extends by base change along `R → SymmetricAlgebra R M` to
  `SymmetricAlgebra R M ⊗[R] M →ₗ[SymmetricAlgebra R M] Ω[SymmetricAlgebra R M⁄R]`.

When `M` carries an `R`-basis `b`, base change transports `b` along this equivalence to a basis of
`Ω[SymmetricAlgebra R M⁄R]` consisting of the differentials `d(ι (b i))`
(`Module.Basis.kaehlerDifferentialSymmetricAlgebra`).

## Main definitions and results

* `SymmetricAlgebra.kaehlerDifferentialEquiv`: the `SymmetricAlgebra R M`-linear equivalence
  `Ω[SymmetricAlgebra R M⁄R] ≃ₗ[SymmetricAlgebra R M] SymmetricAlgebra R M ⊗[R] M`.
* `SymmetricAlgebra.kaehlerDifferentialEquiv_D_ι` and
  `SymmetricAlgebra.kaehlerDifferentialEquiv_symm_tmul`: action on differentials of generators and
  on pure tensors.
* `SymmetricAlgebra.kaehlerDifferentialEquiv_mapSemilinear_map`: naturality with respect to
  `SymmetricAlgebra.map` and `KaehlerDifferential.mapSemilinear`.
* `Module.Basis.kaehlerDifferentialSymmetricAlgebra`: the basis of `Ω[SymmetricAlgebra R M⁄R]`
  induced by a basis of `M`.
-/

public section

noncomputable section

open KaehlerDifferential TensorProduct

universe u v w

namespace SymmetricAlgebra

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/-- The Kähler differentials of `SymmetricAlgebra R M` over `R` are canonically isomorphic to the
base change `SymmetricAlgebra R M ⊗[R] M`, identifying `d(ι m)` with `1 ⊗ₜ m`. -/
def kaehlerDifferentialEquiv :
    Ω[SymmetricAlgebra R M⁄R] ≃ₗ[SymmetricAlgebra R M] SymmetricAlgebra R M ⊗[R] M :=
  LinearEquiv.ofLinearMap
    (mkDerivation (TensorProduct.mk R (SymmetricAlgebra R M) M 1)).liftKaehlerDifferential
    (((D R (SymmetricAlgebra R M)).toLinearMap ∘ₗ ι R M).liftBaseChange (SymmetricAlgebra R M))
    (LinearMap.ext fun x ↦ by
      -- Check `toFun ∘ invFun = id` on pure tensors `s ⊗ₜ m`.
      refine TensorProduct.inductionOn x (fun s m ↦ ?_)
        (fun x y hx hy ↦ by rw [map_add, map_add, hx, hy])
      simp [TensorProduct.smul_tmul'])
    (Derivation.liftKaehlerDifferential_unique _ _ <|
      -- Check `invFun ∘ toFun = id` on `Ω` by checking the induced derivations on generators `ι m`.
      derivation_ext fun m ↦ by simp)

/-- Composing `kaehlerDifferentialEquiv` with the universal derivation `D` recovers
`SymmetricAlgebra.mkDerivation (1 ⊗ₜ ·)`. -/
theorem kaehlerDifferentialEquiv_comp_D :
    (kaehlerDifferentialEquiv R M).toLinearMap.compDer (D R (SymmetricAlgebra R M)) =
      mkDerivation (TensorProduct.mk R (SymmetricAlgebra R M) M 1) :=
  Derivation.liftKaehlerDifferential_comp _

variable {R M}

/-- `kaehlerDifferentialEquiv` sends the differential of a canonical generator `ι R M m` to
`1 ⊗ₜ m`. -/
@[simp]
theorem kaehlerDifferentialEquiv_D_ι (m : M) :
    kaehlerDifferentialEquiv R M (D R (SymmetricAlgebra R M) (ι R M m)) =
      1 ⊗ₜ[R] m := by
  simp [kaehlerDifferentialEquiv]

/-- The inverse of `kaehlerDifferentialEquiv` sends `s ⊗ₜ m` to `s • d(ι R M m)`. -/
@[simp]
theorem kaehlerDifferentialEquiv_symm_tmul (s : SymmetricAlgebra R M) (m : M) :
    (kaehlerDifferentialEquiv R M).symm (s ⊗ₜ[R] m) =
      s • D R (SymmetricAlgebra R M) (ι R M m) := by
  simp [kaehlerDifferentialEquiv]

/-- Naturality of `kaehlerDifferentialEquiv` with respect to an `R`-linear map `f : M →ₗ[R] N`:
`KaehlerDifferential.mapSemilinear (SymmetricAlgebra.map R f)` corresponds to
`SymmetricAlgebra.map R f ⊗ f`. -/
@[simp]
theorem kaehlerDifferentialEquiv_mapSemilinear_map {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (ω : Ω[SymmetricAlgebra R M⁄R]) :
    kaehlerDifferentialEquiv R N (mapSemilinear (SymmetricAlgebra.map R f) ω) =
      TensorProduct.AlgebraTensorModule.map (SymmetricAlgebra.map R f).toLinearMap f
        (kaehlerDifferentialEquiv R M ω) := by
  let : Algebra (SymmetricAlgebra R M) (SymmetricAlgebra R N) :=
    (SymmetricAlgebra.map R f).toRingHom.toAlgebra
  have : IsScalarTower R (SymmetricAlgebra R M) (SymmetricAlgebra R N) :=
    .of_algebraMap_eq' (SymmetricAlgebra.map R f).comp_algebraMap.symm
  have hmap : SymmetricAlgebra.map R f =
      IsScalarTower.toAlgHom R (SymmetricAlgebra R M) (SymmetricAlgebra R N) :=
    AlgHom.ext fun _ ↦ rfl
  let lhs : Ω[SymmetricAlgebra R M⁄R] →ₗ[SymmetricAlgebra R M] SymmetricAlgebra R N ⊗[R] N :=
    (kaehlerDifferentialEquiv R N).toLinearMap.restrictScalars (SymmetricAlgebra R M) ∘ₗ
      KaehlerDifferential.map R R (SymmetricAlgebra R M) (SymmetricAlgebra R N)
  let rhs : Ω[SymmetricAlgebra R M⁄R] →ₗ[SymmetricAlgebra R M] SymmetricAlgebra R N ⊗[R] N :=
    TensorProduct.AlgebraTensorModule.map
      (Algebra.linearMap (SymmetricAlgebra R M) (SymmetricAlgebra R N)) f ∘ₗ
      (kaehlerDifferentialEquiv R M).toLinearMap
  have heq : lhs = rhs := Derivation.liftKaehlerDifferential_unique _ _ <|
    derivation_ext fun m ↦ by
      simp [lhs, rhs, RingHom.algebraMap_toAlgebra]
  have hω := congr($heq ω)
  have hrhs (x : SymmetricAlgebra R M ⊗[R] M) :
      TensorProduct.AlgebraTensorModule.map
          (Algebra.linearMap (SymmetricAlgebra R M) (SymmetricAlgebra R N)) f x =
        TensorProduct.AlgebraTensorModule.map (SymmetricAlgebra.map R f).toLinearMap f x :=
    TensorProduct.inductionOn x (fun _ _ ↦ by simp [RingHom.algebraMap_toAlgebra])
      (fun _ _ hx hy ↦ by rw [map_add, map_add, hx, hy])
  dsimp only [lhs, rhs, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe] at hω
  conv_lhs => rw [hmap, mapSemilinear_toAlgHom_apply]
  exact hω.trans (hrhs _)

end SymmetricAlgebra

namespace Module.Basis

/-- An `R`-basis `b` of `M` induces a `SymmetricAlgebra R M`-basis of
`Ω[SymmetricAlgebra R M⁄R]` consisting of the differentials `d(ι R M (b i))`. -/
def kaehlerDifferentialSymmetricAlgebra {R : Type u} {M : Type v} {κ : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (b : Module.Basis κ R M) :
    Module.Basis κ (SymmetricAlgebra R M) Ω[SymmetricAlgebra R M⁄R] :=
  (Algebra.TensorProduct.basis (SymmetricAlgebra R M) b).map
    (SymmetricAlgebra.kaehlerDifferentialEquiv R M).symm

/-- The `i`-th vector of `b.kaehlerDifferentialSymmetricAlgebra` is `d(ι R M (b i))`. -/
@[simp]
theorem kaehlerDifferentialSymmetricAlgebra_apply {R : Type u} {M : Type v} {κ : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] (b : Module.Basis κ R M) (i : κ) :
    b.kaehlerDifferentialSymmetricAlgebra i =
      D R (SymmetricAlgebra R M) (SymmetricAlgebra.ι R M (b i)) := by
  simp [kaehlerDifferentialSymmetricAlgebra]

end Module.Basis
