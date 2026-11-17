/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.Algebra.MonoidAlgebra.PowerSeries

/-!
# Continuity of power-series identifications over finite monoid algebras

For a finite monoid `M` and an `R`-algebra `A`, `MonoidAlgebra.powerSeriesAlgEquiv R A M`
identifies `A⟦X⟧[M]` with `A[M]⟦X⟧`. When `A[M]` carries the `R`-module topology and power-series
rings carry their coefficientwise topology (`PowerSeries.WithPiTopology`), extracting each
`M`-coefficient series through `(powerSeriesAlgEquiv R A M).symm` is continuous, and hence any
lifted algebra homomorphism `A[M]⟦X⟧ →ₐ[R] B` built from a continuous `ε : A⟦X⟧ →ₐ[R] B` and a
commuting monoid homomorphism `η : M →* B` is continuous.

## Main results

* `TauCeti.continuous_coeff_powerSeriesAlgEquiv_symm`: extracting the `m`-coefficient series
  through `(MonoidAlgebra.powerSeriesAlgEquiv R A M).symm` is continuous.
* `TauCeti.continuous_liftNCAlgHom_powerSeriesAlgEquiv_symm`: lifting a continuous
  `ε : A⟦X⟧ →ₐ[R] B` and a commuting `η : M →* B` along `(powerSeriesAlgEquiv R A M).symm` is
  continuous.
-/

public section

open scoped PowerSeries.WithPiTopology

namespace TauCeti

/-- Extracting the `m`-coefficient series through `(MonoidAlgebra.powerSeriesAlgEquiv R A M).symm`
is continuous for the `R`-module topology on `A[M]` and the coefficientwise topology on `A[M]⟦X⟧`
and `A⟦X⟧`. -/
theorem continuous_coeff_powerSeriesAlgEquiv_symm {R A M : Type*} [CommSemiring R]
    [TopologicalSpace R] [Semiring A] [Algebra R A] [TopologicalSpace A] [ContinuousAdd A]
    [ContinuousSMul R A] [Monoid M] [Finite M] [TopologicalSpace (MonoidAlgebra A M)]
    [IsModuleTopology R (MonoidAlgebra A M)] (m : M) :
    Continuous fun ψ : PowerSeries (MonoidAlgebra A M) ↦
      ((MonoidAlgebra.powerSeriesAlgEquiv R A M).symm ψ).coeff m := by
  refine continuous_iff_continuousAt.mpr fun ψ ↦
    (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto A _ _ _).mpr fun n ↦ ?_
  let l : MonoidAlgebra A M →ₗ[R] A :=
    (Finsupp.lapply m).comp (MonoidAlgebra.coeffLinearEquiv R).toLinearMap
  have hl : ∀ a : MonoidAlgebra A M, l a = a.coeff m := fun a ↦ by
    simp only [l, LinearMap.comp_apply, LinearEquiv.coe_coe,
      MonoidAlgebra.coeffLinearEquiv_apply, Finsupp.lapply_apply]
  simpa only [MonoidAlgebra.coeff_coeff_powerSeriesAlgEquiv_symm, ContinuousAt,
    Function.comp_def, hl] using
      ((IsModuleTopology.continuous_of_linearMap l).comp
        (PowerSeries.WithPiTopology.continuous_coeff (MonoidAlgebra A M) n)).continuousAt

/-- For a finite monoid `M` and a continuous `ε : A⟦X⟧ →ₐ[R] B` commuting with `η : M →* B`, the
induced map `A[M]⟦X⟧ →ₐ[R] B` through `(MonoidAlgebra.powerSeriesAlgEquiv R A M).symm` is
continuous. -/
theorem continuous_liftNCAlgHom_powerSeriesAlgEquiv_symm {R A M B : Type*} [CommSemiring R]
    [TopologicalSpace R] [Semiring A] [Algebra R A] [TopologicalSpace A] [ContinuousAdd A]
    [ContinuousSMul R A] [Monoid M] [Finite M] [TopologicalSpace (MonoidAlgebra A M)]
    [IsModuleTopology R (MonoidAlgebra A M)] [Semiring B] [Algebra R B] [TopologicalSpace B]
    [ContinuousAdd B] [ContinuousMul B] {ε : PowerSeries A →ₐ[R] B} (hε : Continuous ε)
    (η : M →* B) (h_comm : ∀ x y, Commute (ε x) (η y)) :
    Continuous ((MonoidAlgebra.liftNCAlgHom ε η h_comm).comp
      (MonoidAlgebra.powerSeriesAlgEquiv R A M).symm.toAlgHom) := by
  have := Fintype.ofFinite M
  exact (continuous_finsetSum (s := Finset.univ)
    (f := fun m ψ ↦ ε (((MonoidAlgebra.powerSeriesAlgEquiv R A M).symm ψ).coeff m) * η m) fun m _ ↦
      (hε.comp (continuous_coeff_powerSeriesAlgEquiv_symm m)).mul continuous_const).congr fun ψ ↦ by
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] using
      (MonoidAlgebra.liftNCAlgHom_powerSeriesAlgEquiv_symm_apply R A M ε η h_comm ψ).symm

end TauCeti
