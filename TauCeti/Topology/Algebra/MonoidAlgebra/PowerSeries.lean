/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.Algebra.MonoidAlgebra.CharGroupRing.Splitting
public import TauCeti.Algebra.MonoidAlgebra.PowerSeries
import TauCeti.Algebra.MonoidAlgebra.Basic
import TauCeti.RingTheory.PowerSeries.PiTopology

/-!
# Continuity and series expansions for power series over finite monoid algebras

For a finite monoid `M` and an `R`-algebra `A`, `MonoidAlgebra.powerSeriesAlgEquiv R A M`
identifies `A⟦X⟧[M]` with `A[M]⟦X⟧`. When `A[M]` carries the `R`-module topology and power-series
rings carry their coefficientwise topology (`PowerSeries.WithPiTopology`), extracting each
`M`-coefficient series through `(powerSeriesAlgEquiv R A M).symm` is continuous, and hence any
lifted algebra homomorphism `A[M]⟦X⟧ →ₐ[R] B` built from a continuous `ε : A⟦X⟧ →ₐ[R] B` and a
commuting monoid homomorphism `η : M →* B` is continuous.

Moreover, if `ε` evaluates power series via convergent sums in `B` against powers of an element `t`
commuting with the image of `η`, then the lifted map through `(powerSeriesAlgEquiv R A M).symm`
evaluates `F ∈ A[M]⟦X⟧` via the convergent series whose `n`-th term applies the coefficientwise lift
to `F.coeff n` multiplied by `t ^ n`.

When `G` is a finite commutative group, `O` is a topological domain with enough roots of unity of
exponent `exp(G)` in which `#G` is a unit, and `O[G]` carries the `O`-module topology, the character
splitting `TauCeti.powerSeriesCharEvalEquiv hG : O[G]⟦X⟧ ≃ₐ[O] ((G →* Oˣ) → O⟦X⟧)` is a
homeomorphism (`TauCeti.continuous_powerSeriesCharEvalEquiv`,
`TauCeti.continuous_powerSeriesCharEvalEquiv_symm`).

## Main results

* `TauCeti.continuous_coeff_powerSeriesAlgEquiv_symm`: extracting the `m`-coefficient series
  through `(MonoidAlgebra.powerSeriesAlgEquiv R A M).symm` is continuous.
* `TauCeti.continuous_liftNCAlgHom_powerSeriesAlgEquiv_symm`: lifting a continuous
  `ε : A⟦X⟧ →ₐ[R] B` and a commuting `η : M →* B` along `(powerSeriesAlgEquiv R A M).symm` is
  continuous.
* `TauCeti.hasSum_liftNC_powerSeriesAlgEquiv_symm`: convergent power-series expansion of
  `MonoidAlgebra.liftNC ε η` along `(MonoidAlgebra.powerSeriesAlgEquiv R A M).symm`.
* `TauCeti.hasSum_liftNCAlgHom_powerSeriesAlgEquiv_symm`: convergent power-series expansion of
  `MonoidAlgebra.liftNCAlgHom ε η h_comm` along `(MonoidAlgebra.powerSeriesAlgEquiv R R M).symm`
  using `MonoidAlgebra.lift R B M η`.
* `TauCeti.continuous_powerSeriesCharEvalEquiv` and
  `TauCeti.continuous_powerSeriesCharEvalEquiv_symm`: `TauCeti.powerSeriesCharEvalEquiv` is a
  homeomorphism for the `O`-module topology on `O[G]` and the coefficientwise topologies on
  `O[G]⟦X⟧` and `(G →* Oˣ) → O⟦X⟧`.
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
  let l : MonoidAlgebra A M →ₗ[R] A :=
    (Finsupp.lapply m).comp (MonoidAlgebra.coeffLinearEquiv R).toLinearMap
  exact (PowerSeries.WithPiTopology.continuous_mk_comp_coeff
    (IsModuleTopology.continuous_of_linearMap l)).congr fun ψ ↦
      PowerSeries.ext fun n ↦ by simp [l]

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
    rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, MonoidAlgebra.coe_liftNCAlgHom,
      MonoidAlgebra.liftNC_eq_sum (ε : PowerSeries A →+ B) η]
    simp only [AlgHom.coe_toAddMonoidHom]

/-- For a finite monoid `M`, if `ε : A⟦X⟧ →+ B` evaluates power series via convergent sums
`∑ n, f (φ.coeff n) * t ^ n` where `t` commutes with every `η m`, then `MonoidAlgebra.liftNC ε η`
composed with `(MonoidAlgebra.powerSeriesAlgEquiv R A M).symm` evaluates `F ∈ A[M]⟦X⟧` via the
convergent series `∑ n, MonoidAlgebra.liftNC f η (F.coeff n) * t ^ n`. -/
theorem hasSum_liftNC_powerSeriesAlgEquiv_symm {R A M B : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [Monoid M] [Finite M] [Semiring B] [TopologicalSpace B]
    [ContinuousAdd B] [ContinuousMul B] {L : SummationFilter ℕ} {ε : PowerSeries A →+ B}
    {f : A →+ B} {t : B}
    (hε : ∀ φ : PowerSeries A, HasSum (fun n : ℕ ↦ f (φ.coeff n) * t ^ n) (ε φ) L)
    (η : M → B) (ht : ∀ m, Commute t (η m)) (F : PowerSeries (MonoidAlgebra A M)) :
    HasSum (fun n : ℕ ↦ MonoidAlgebra.liftNC f η (F.coeff n) * t ^ n)
      (MonoidAlgebra.liftNC ε η ((MonoidAlgebra.powerSeriesAlgEquiv R A M).symm F)) L := by
  classical
  have := Fintype.ofFinite M
  rw [MonoidAlgebra.liftNC_eq_sum]
  refine (hasSum_sum fun m _ ↦
    (hε (((MonoidAlgebra.powerSeriesAlgEquiv R A M).symm F).coeff m)).map
      (AddMonoidHom.mulRight (η m)) (continuous_id.mul continuous_const)).congr_fun fun n ↦ ?_
  rw [MonoidAlgebra.liftNC_eq_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m _ ↦ by
    simp only [Function.comp_apply, AddMonoidHom.coe_mulRight,
      MonoidAlgebra.coeff_coeff_powerSeriesAlgEquiv_symm, mul_assoc, ((ht m).pow_left n).eq]

/-- For a finite monoid `M`, if `ε : R⟦X⟧ →ₐ[R] B` evaluates power series via convergent sums
`∑ n, φ.coeff n • t ^ n` where `t` commutes with `η : M →* B`, then the lifted algebra homomorphism
`R[M]⟦X⟧ →ₐ[R] B` through `(MonoidAlgebra.powerSeriesAlgEquiv R R M).symm` evaluates `F` via the
convergent series `∑ n, MonoidAlgebra.lift R B M η (F.coeff n) * t ^ n`. -/
theorem hasSum_liftNCAlgHom_powerSeriesAlgEquiv_symm {R M B : Type*} [CommSemiring R]
    [Monoid M] [Finite M] [Semiring B] [Algebra R B] [TopologicalSpace B] [ContinuousAdd B]
    [ContinuousMul B] {L : SummationFilter ℕ} {ε : PowerSeries R →ₐ[R] B} {t : B}
    (hε : ∀ φ : PowerSeries R, HasSum (fun n : ℕ ↦ φ.coeff n • t ^ n) (ε φ) L)
    (η : M →* B) (h_comm : ∀ x y, Commute (ε x) (η y)) (ht : ∀ m, Commute t (η m))
    (F : PowerSeries (MonoidAlgebra R M)) :
    HasSum (fun n : ℕ ↦ MonoidAlgebra.lift R B M η (F.coeff n) * t ^ n)
      (MonoidAlgebra.liftNCAlgHom ε η h_comm
        ((MonoidAlgebra.powerSeriesAlgEquiv R R M).symm F)) L := by
  simpa only [MonoidAlgebra.lift_def, MonoidAlgebra.coe_liftNCAlgHom] using
    hasSum_liftNC_powerSeriesAlgEquiv_symm (R := R) (A := R) (ε := (ε : PowerSeries R →+ B))
      (f := (algebraMap R B : R →+ B))
      (fun φ ↦ by simpa only [Algebra.smul_def, AddMonoidHom.coe_ofClass] using hε φ) η ht F

section CharEval

variable {O G : Type*} [CommRing O] [IsDomain O] [TopologicalSpace O] [CommGroup G]
  [Finite G] [HasEnoughRootsOfUnity O (Monoid.exponent G)]
  [TopologicalSpace (MonoidAlgebra O G)] [IsModuleTopology O (MonoidAlgebra O G)]

/-- **Continuity of the character splitting on `O[G]⟦X⟧`.** For the `O`-module topology on `O[G]`
and the coefficientwise topologies on `O[G]⟦X⟧` and `(G →* Oˣ) → O⟦X⟧`, `powerSeriesCharEvalEquiv`
is continuous. -/
theorem continuous_powerSeriesCharEvalEquiv [ContinuousAdd O] [ContinuousSMul O O]
    (hG : IsUnit (Nat.card G : O)) :
    Continuous (powerSeriesCharEvalEquiv hG) :=
  continuous_pi fun ψ ↦
    (PowerSeries.WithPiTopology.continuous_map
      (IsModuleTopology.continuous_of_linearMap ψ.charEval.toLinearMap)).congr fun φ ↦
        (powerSeriesCharEvalEquiv_apply hG φ ψ).symm

/-- **Continuity of the inverse character splitting on `O[G]⟦X⟧`.** For the `O`-module topology
on `O[G]` and the coefficientwise topologies on `(G →* Oˣ) → O⟦X⟧` and `O[G]⟦X⟧`,
`(powerSeriesCharEvalEquiv hG).symm` is continuous. -/
theorem continuous_powerSeriesCharEvalEquiv_symm (hG : IsUnit (Nat.card G : O)) :
    Continuous (powerSeriesCharEvalEquiv hG).symm := by
  classical
  have : ContinuousAdd (MonoidAlgebra O G) := IsModuleTopology.toContinuousAdd O _
  have : ContinuousSMul O (MonoidAlgebra O G) := IsModuleTopology.toContinuousSMul O _
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype (G →* Oˣ) := Fintype.ofFinite _
  refine continuous_iff_continuousAt.mpr fun F ↦
    (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto _ _ _ _).mpr fun n ↦ ?_
  refine ((continuous_finsetSum (s := Finset.univ)
    (f := fun (χ : G →* Oˣ) (H : (G →* Oˣ) → PowerSeries O) ↦
      (H χ).coeff n • charIdempotent χ)
    fun χ _ ↦ ((PowerSeries.WithPiTopology.continuous_coeff O n).comp
      (continuous_apply χ)).smul continuous_const).congr fun H ↦ ?_).continuousAt
  rw [coeff_powerSeriesCharEvalEquiv_symm, charEvalEquiv_symm_apply]

end CharEval

end TauCeti
