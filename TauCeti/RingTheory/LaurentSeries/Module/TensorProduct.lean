/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import TauCeti.RingTheory.HahnSeries.TensorProduct
public import TauCeti.RingTheory.LaurentSeries.Module.Lattice

/-!
# Power-series lattices and finite jets as scalar extensions

For a finite free module `V` over a commutative ring `R`, the comparison
`R⸨X⸩ ⊗[R] V ≃ V⸨X⸩` (`HahnModule.tensorProductEquiv`) identifies module-valued Laurent series
with the scalar extension of `V`. This file shows that it is compatible with the lattices
`U_a(V) = X ^ a V⟦X⟧` of series vanishing below `a`, and with their finite jets:

* `R⟦X⟧ ⊗[R] V ≃ U_a(V)`, `p ⊗ v ↦ p X ^ a v`, as `R⟦X⟧`-modules. For `a = 0` this is the
  restriction of `R⸨X⸩ ⊗[R] V ≃ V⸨X⸩` along `R⟦X⟧ → R⸨X⸩`, so `V⟦X⟧ = R⟦X⟧ ⊗[R] V`.
* `(R⟦X⟧ ⧸ (X ^ n)) ⊗[R] V ≃ U_a(V) / U_(a+n)(V)`, as `R⟦X⟧`-modules: the jets of length `n` of
  module-valued series are the scalar extension of `V` to jets of power series.

Over a field `K` and a finite-dimensional `V`, these are the lattice and finite-jet comparisons
`K⟦t⟧ ⊗[K] V ≃ V⟦t⟧` and `(K⟦t⟧ ⧸ (t ^ n)) ⊗[K] V ≃ U_0(V)/U_n(V)` for `V((t))`.

## Main definitions

* `TauCeti.HahnModule.tensorProductPowerSeriesLatticeEquiv R V a`: the `R⟦X⟧`-linear
  equivalence `R⟦X⟧ ⊗[R] V ≃ U_a(V)`.
* `TauCeti.HahnModule.tensorProductLatticeQuotientEquiv R V a n`: the `R⟦X⟧`-linear
  equivalence `(R⟦X⟧ ⧸ (X ^ n)) ⊗[R] V ≃ U_a(V) / U_(a+n)(V)`.

## Main results

* `TauCeti.HahnModule.coe_tensorProductPowerSeriesLatticeEquiv_tmul`: `p ⊗ v ↦ p X ^ a v`.
* `TauCeti.HahnModule.coe_tensorProductPowerSeriesLatticeEquiv_zero`: for `a = 0`, the
  equivalence is the restriction of `HahnModule.tensorProductToHahnModule`.
* `TauCeti.HahnModule.tensorProductLatticeQuotientEquiv_mk_tmul`: the jet of `p` tensored with
  `v` maps to the jet of `p X ^ a v`.
-/

public section

noncomputable section

open _root_.HahnModule HahnSeries TensorProduct
open scoped LaurentSeries PowerSeries Pointwise

namespace TauCeti.HahnModule

section CommSemiring

variable (R V : Type*) [CommSemiring R] [AddCommMonoid V] [Module R V]

/-- The scalar-extension map `R⟦X⟧ ⊗[R] V → V⸨X⸩`, `p ⊗ v ↦ p v`. -/
private def powerSeriesTensorToHahnModule : R⟦X⟧ ⊗[R] V →ₗ[R⟦X⟧] HahnModule ℤ R V :=
  AlgebraTensorModule.lift
    { toFun := fun p ↦
        { toFun := fun v ↦ p • of R (single 0 v)
          map_add' := fun v w ↦ by rw [single_add, of_add, _root_.smul_add]
          map_smul' := fun r v ↦ by
            have h : of R (single 0 (r • v)) = r • of R (single (0 : ℤ) v) := by
              apply HahnModule.ext
              funext g
              by_cases hg : g = 0 <;> simp [hg]
            rw [RingHom.id_apply, h, smul_comm] }
      map_add' := fun p q ↦ LinearMap.ext fun v ↦ add_smul p q _
      map_smul' := fun p q ↦ LinearMap.ext fun v ↦ mul_smul p q _ }

variable {R V}

private theorem powerSeriesTensorToHahnModule_tmul (p : R⟦X⟧) (v : V) :
    powerSeriesTensorToHahnModule R V (p ⊗ₜ[R] v) = p • of R (single 0 v) :=
  (rfl)

/-- In a basis of `V`, the power-series coordinates of a tensor are the coordinates of the
coefficients of its image. -/
private theorem coeff_equivFinsuppOfBasisRight {ι : Type*} [DecidableEq ι]
    (b : Module.Basis ι R V) (z : R⟦X⟧ ⊗[R] V) (i : ι) (n : ℕ) :
    PowerSeries.coeff n (TensorProduct.equivFinsuppOfBasisRight b z i) =
      b.repr (((of R).symm (powerSeriesTensorToHahnModule R V z)).coeff n) i := by
  induction z using TensorProduct.inductionOn with
  | tmul p v =>
    simp [powerSeriesTensorToHahnModule_tmul, powerSeries_smul, mul_comm]
  | add z w hz hw => simp [hz, hw]

private theorem powerSeriesTensorToHahnModule_injective [Module.Free R V] :
    Function.Injective (powerSeriesTensorToHahnModule R V) := by
  classical
  let b := Module.Free.chooseBasis R V
  intro z w h
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i n
  simp only [coeff_equivFinsuppOfBasisRight, h]

private theorem range_powerSeriesTensorToHahnModule [Module.Free R V] [Module.Finite R V] :
    LinearMap.range (powerSeriesTensorToHahnModule R V) = powerSeriesLattice R V 0 := by
  classical
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul p v =>
      rw [powerSeriesTensorToHahnModule_tmul]
      exact (powerSeriesLattice R V 0).smul_mem p ((mem_powerSeriesLattice R V).2
        ((of_mem_lattice_iff R V).2 (LaurentSeries.single_mem_lattice le_rfl v)))
    | add z w hz hw => simpa using add_mem hz hw
  · intro x hx
    let b := Module.Free.chooseBasis R V
    have hcoord (i : _) : ∃ p : R⟦X⟧, (p : R⸨X⸩) = ((of R).symm x).map (b.coord i) := by
      refine LaurentSeries.mem_lattice_zero_iff.1 (LaurentSeries.mem_lattice_iff.2 fun n hn ↦ ?_)
      simp [(mem_lattice_iff R V).1 ((mem_powerSeriesLattice R V).1 hx) n hn]
    choose p hp using hcoord
    refine ⟨∑ i, p i ⊗ₜ[R] b i, ?_⟩
    simp only [map_sum, powerSeriesTensorToHahnModule_tmul, powerSeries_smul, hp]
    exact sum_map_coord_smul_single b x

variable (R V) in
/-- For a finite free module `V`, the power-series lattice `U_a(V) = X ^ a V⟦X⟧` of `V`-valued
Laurent series vanishing below `a` is the scalar extension `R⟦X⟧ ⊗[R] V`, through
`p ⊗ v ↦ p X ^ a v`. -/
def tensorProductPowerSeriesLatticeEquiv [Module.Free R V] [Module.Finite R V] (a : ℤ) :
    R⟦X⟧ ⊗[R] V ≃ₗ[R⟦X⟧] powerSeriesLattice R V a :=
  (LinearEquiv.ofInjective _ powerSeriesTensorToHahnModule_injective).trans <|
    (LinearEquiv.ofEq _ _ range_powerSeriesTensorToHahnModule).trans <|
      (powerSeriesLatticeShift 0 a).trans (LinearEquiv.ofEq _ _ (by rw [zero_add]))

/-- The lattice comparison sends `p ⊗ v` to `p X ^ a v`. -/
@[simp]
theorem coe_tensorProductPowerSeriesLatticeEquiv_tmul [Module.Free R V] [Module.Finite R V]
    (a : ℤ) (p : R⟦X⟧) (v : V) :
    (tensorProductPowerSeriesLatticeEquiv R V a (p ⊗ₜ[R] v) : HahnModule ℤ R V) =
      p • of R (single a v) := by
  simp only [tensorProductPowerSeriesLatticeEquiv, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, powerSeriesLatticeShift_apply, LinearEquiv.ofInjective_apply,
    powerSeriesTensorToHahnModule_tmul, powerSeries_smul, ← mul_smul]
  rw [mul_comm, mul_smul, single_smul_single_zero, one_smul]

end CommSemiring

section Comparison

variable {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]

-- Match the coefficientwise scalar action used by `HahnModule.tensorProductToHahnModule`.
attribute [local instance 1100] HahnSeries.instAlgebra

/-- At `a = 0` the lattice comparison is the restriction of the scalar-extension comparison
`R⸨X⸩ ⊗[R] V → V⸨X⸩` along `R⟦X⟧ → R⸨X⸩`. -/
theorem coe_tensorProductPowerSeriesLatticeEquiv_zero [Module.Free R V] [Module.Finite R V]
    (z : R⟦X⟧ ⊗[R] V) :
    (tensorProductPowerSeriesLatticeEquiv R V 0 z : HahnModule ℤ R V) =
      _root_.HahnModule.tensorProductToHahnModule ℤ R V
        ((HahnSeries.ofPowerSeriesAlg ℤ R (A := R)).toLinearMap.rTensor V z) := by
  induction z using TensorProduct.inductionOn with
  | tmul p v =>
    -- `ofPowerSeriesAlg` is `ofPowerSeries` bundled as an algebra map.
    have h : HahnSeries.ofPowerSeriesAlg ℤ R (A := R) p = ofPowerSeries ℤ R p := rfl
    simp [powerSeries_smul, h]
  | add z w hz hw => simp [hz, hw]

end Comparison

section CommRing

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]

/-- Inside `U_a(V)`, the multiples of `X ^ n` are the series in `U_(a+n)(V)`. -/
private theorem X_pow_smul_top_eq_comap (a : ℤ) (n : ℕ) :
    (PowerSeries.X ^ n : R⟦X⟧) • (⊤ : Submodule R⟦X⟧ (powerSeriesLattice R V a)) =
      (powerSeriesLattice R V (a + n)).comap (powerSeriesLattice R V a).subtype := by
  ext f
  rw [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨g, -, rfl⟩
    exact (X_pow_smul_mem_powerSeriesLattice_iff a n g.1).2 g.2
  · intro hf
    rw [← X_pow_smul_powerSeriesLattice, Submodule.mem_smul_pointwise_iff_exists] at hf
    obtain ⟨g, hg, hgf⟩ := hf
    exact ⟨⟨g, hg⟩, Submodule.mem_top, Subtype.ext hgf⟩

private theorem map_span_X_pow_smul_top [Module.Free R V] [Module.Finite R V] (a : ℤ) (n : ℕ) :
    (Ideal.span {(PowerSeries.X ^ n : R⟦X⟧)} • (⊤ : Submodule R⟦X⟧ (R⟦X⟧ ⊗[R] V))).map
        (tensorProductPowerSeriesLatticeEquiv R V a :
          R⟦X⟧ ⊗[R] V →ₗ[R⟦X⟧] powerSeriesLattice R V a) =
      (powerSeriesLattice R V (a + n)).comap (powerSeriesLattice R V a).subtype := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.map_pointwise_smul, Submodule.map_top,
    LinearEquiv.range, X_pow_smul_top_eq_comap]

variable [Module.Free R V] [Module.Finite R V]

/-- The jet of the image of a tensor under the lattice comparison. -/
private def tensorProductToLatticeQuotient (a b : ℤ) :
    R⟦X⟧ ⊗[R] V →ₗ[R⟦X⟧] latticeQuotient R V a b where
  toFun z := Submodule.Quotient.mk ⟨tensorProductPowerSeriesLatticeEquiv R V a z,
    (mem_powerSeriesLattice R V).1 (tensorProductPowerSeriesLatticeEquiv R V a z).2⟩
  map_add' z w := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
    exact Subtype.ext (by simp)
  map_smul' p z := by
    rw [RingHom.id_apply, smul_latticeQuotient_mk]
    congr 1
    exact Subtype.ext (by simp)

private theorem tensorProductToLatticeQuotient_surjective (a b : ℤ) :
    Function.Surjective (tensorProductToLatticeQuotient R V a b) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ f =>
    refine ⟨(tensorProductPowerSeriesLatticeEquiv R V a).symm
      ⟨f, (mem_powerSeriesLattice R V).2 f.2⟩, ?_⟩
    simp [tensorProductToLatticeQuotient]

private theorem ker_tensorProductToLatticeQuotient (a : ℤ) (n : ℕ) :
    LinearMap.ker (tensorProductToLatticeQuotient R V a (a + n)) =
      Ideal.span {(PowerSeries.X ^ n : R⟦X⟧)} • ⊤ := by
  ext z
  rw [LinearMap.mem_ker, ← Submodule.comap_map_eq_of_injective
    (tensorProductPowerSeriesLatticeEquiv R V a).injective
    (Ideal.span {(PowerSeries.X ^ n : R⟦X⟧)} • ⊤), map_span_X_pow_smul_top]
  simp [tensorProductToLatticeQuotient, Submodule.Quotient.mk_eq_zero]

/-- For a finite free module `V`, the jets `U_a(V) / U_(a+n)(V)` of length `n` of `V`-valued
Laurent series are the scalar extension `(R⟦X⟧ ⧸ (X ^ n)) ⊗[R] V` of `V` to jets of power series,
through `p ⊗ v ↦ p X ^ a v`. -/
def tensorProductLatticeQuotientEquiv (a : ℤ) (n : ℕ) :
    (R⟦X⟧ ⧸ Ideal.span {(PowerSeries.X ^ n : R⟦X⟧)}) ⊗[R] V ≃ₗ[R⟦X⟧]
      latticeQuotient R V a (a + n) :=
  (AlgebraTensorModule.cancelBaseChange R R⟦X⟧ R⟦X⟧ _ V).symm ≪≫ₗ
    quotTensorEquivQuotSMul (R⟦X⟧ ⊗[R] V) _ ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (ker_tensorProductToLatticeQuotient R V a n).symm ≪≫ₗ
        (tensorProductToLatticeQuotient R V a (a + n)).quotKerEquivOfSurjective
          (tensorProductToLatticeQuotient_surjective R V a (a + n))

/-- The jet comparison sends the jet of `p` tensored with `v` to the jet of `p X ^ a v`. -/
@[simp]
theorem tensorProductLatticeQuotientEquiv_mk_tmul (a : ℤ) (n : ℕ) (p : R⟦X⟧) (v : V) :
    tensorProductLatticeQuotientEquiv R V a n (Ideal.Quotient.mk _ p ⊗ₜ[R] v) =
      Submodule.Quotient.mk ⟨p • of R (single a v), by
        rw [← coe_tensorProductPowerSeriesLatticeEquiv_tmul, ← mem_powerSeriesLattice]
        exact Subtype.prop _⟩ := by
  simp only [tensorProductLatticeQuotientEquiv, LinearEquiv.trans_apply,
    AlgebraTensorModule.cancelBaseChange_symm_tmul, quotTensorEquivQuotSMul_mk_tmul, smul_tmul',
    smul_eq_mul, mul_one, Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  simp [tensorProductToLatticeQuotient]

end CommRing

end TauCeti.HahnModule
