/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
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
  module-valued series are the scalar extension of `V` to jets of power series. This holds for
  every module `V`: the inverse reads off the coefficients at `a, …, a + n - 1`.

Over a field `K` and a finite-dimensional `V`, these are the lattice and finite-jet comparisons
`K⟦t⟧ ⊗[K] V ≃ V⟦t⟧` and `(K⟦t⟧ ⧸ (t ^ n)) ⊗[K] V ≃ U_0(V)/U_n(V)` for `V((t))`.

## Main definitions

* `TauCeti.HahnModule.tensorProductPowerSeriesLatticeEquiv R V a`: the `R⟦X⟧`-linear
  equivalence `R⟦X⟧ ⊗[R] V ≃ U_a(V)`.
* `TauCeti.HahnModule.tensorProductLatticeQuotientEquiv R V a n`: the `R⟦X⟧`-linear
  equivalence `(R⟦X⟧ ⧸ (X ^ n)) ⊗[R] V ≃ U_a(V) / U_(a+n)(V)`, for any module `V`.

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

end CommSemiring

section Lattice

variable {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]

-- Match the coefficientwise scalar action used by `HahnModule.tensorProductToHahnModule`.
attribute [local instance 1100] HahnSeries.instAlgebra

/-- The power-series map is the restriction of `R⸨X⸩ ⊗[R] V → V⸨X⸩` along `R⟦X⟧ → R⸨X⸩`. -/
private theorem powerSeriesTensorToHahnModule_eq (z : R⟦X⟧ ⊗[R] V) :
    powerSeriesTensorToHahnModule R V z =
      _root_.HahnModule.tensorProductToHahnModule ℤ R V
        ((HahnSeries.ofPowerSeriesAlg ℤ R (A := R)).toLinearMap.rTensor V z) := by
  induction z using TensorProduct.inductionOn with
  | tmul p v =>
    -- `ofPowerSeriesAlg` is `ofPowerSeries` bundled as an algebra map.
    have h : HahnSeries.ofPowerSeriesAlg ℤ R (A := R) p = ofPowerSeries ℤ R p := rfl
    simp [powerSeriesTensorToHahnModule_tmul, powerSeries_smul, h]
  | add z w hz hw => simp [hz, hw]

private theorem powerSeriesTensorToHahnModule_injective [Module.Free R V] :
    Function.Injective (powerSeriesTensorToHahnModule R V) := by
  have h := (_root_.HahnModule.tensorProductToHahnModule_injective (Γ := ℤ) (R := R)
    (V := V)).comp (Module.Flat.rTensor_preserves_injective_linearMap
      (HahnSeries.ofPowerSeriesAlg ℤ R (A := R)).toLinearMap ofPowerSeries_injective)
  convert h using 1
  exact funext powerSeriesTensorToHahnModule_eq

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

/-- At `a = 0` the lattice comparison is the restriction of the scalar-extension comparison
`R⸨X⸩ ⊗[R] V → V⸨X⸩` along `R⟦X⟧ → R⸨X⸩`. -/
theorem coe_tensorProductPowerSeriesLatticeEquiv_zero [Module.Free R V] [Module.Finite R V]
    (z : R⟦X⟧ ⊗[R] V) :
    (tensorProductPowerSeriesLatticeEquiv R V 0 z : HahnModule ℤ R V) =
      _root_.HahnModule.tensorProductToHahnModule ℤ R V
        ((HahnSeries.ofPowerSeriesAlg ℤ R (A := R)).toLinearMap.rTensor V z) := by
  rw [← powerSeriesTensorToHahnModule_eq]
  simp only [tensorProductPowerSeriesLatticeEquiv, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, powerSeriesLatticeShift_apply, LinearEquiv.ofInjective_apply,
    single_zero_one, one_smul]

end Lattice

section CommRing

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]

/-- The coefficient of `p X ^ a v` at `a + k` is the `k`-th coefficient of `p` times `v`. -/
private theorem coeff_smul_single (p : R⟦X⟧) (a : ℤ) (v : V) (k : ℕ) :
    ((of R).symm (p • of R (single a v))).coeff (a + k) = PowerSeries.coeff k p • v := by
  rw [powerSeries_smul, ← one_smul R v, ← single_smul_single_zero, smul_smul, one_smul,
    coeff_smul_single_zero, add_comm, coeff_mul_single_add, mul_one, ofPowerSeries_apply_coeff]

/-- Multiplying by `X ^ k` shifts a monomial by `k`. -/
private theorem X_pow_smul_single (k : ℕ) (a : ℤ) (v : V) :
    (PowerSeries.X ^ k : R⟦X⟧) • of R (single a v) = of R (single (a + k) v) := by
  rw [powerSeries_smul, ofPowerSeries_X_pow, ← one_smul R v, ← single_smul_single_zero,
    smul_smul, single_mul_single, one_mul, single_smul_single_zero, add_comm]

/-- The class of `v X ^ a` in the jets `U_a(V) / U_b(V)`. -/
private def singleLatticeQuotient (a b : ℤ) : V →ₗ[R] latticeQuotient R V a b where
  toFun v := Submodule.Quotient.mk ⟨of R (single a v),
    (of_mem_lattice_iff R V).2 (LaurentSeries.single_mem_lattice le_rfl v)⟩
  map_add' v w := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
    exact Subtype.ext (by simp [single_add])
  map_smul' r v := by
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    congr 1
    refine Subtype.ext ?_
    apply HahnModule.ext
    funext g
    by_cases hg : g = a <;> simp [hg]

/-- The jet map `(R⟦X⟧ ⧸ (X ^ n)) ⊗[R] V → U_a(V) / U_(a+n)(V)`, `p ⊗ v ↦ p X ^ a v`. -/
private def tensorProductToLatticeQuotient (a : ℤ) (n : ℕ) :
    (R⟦X⟧ ⧸ Ideal.span {(PowerSeries.X ^ n : R⟦X⟧)}) ⊗[R] V →ₗ[R⟦X⟧]
      latticeQuotient R V a (a + n) :=
  AlgebraTensorModule.lift <| (Ideal.span {(PowerSeries.X ^ n : R⟦X⟧)}).liftQ
    (LinearMap.toSpanSingleton R⟦X⟧ _ (singleLatticeQuotient R V a (a + n))) <| by
      rw [Ideal.span, Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact LinearMap.ext fun v ↦ X_pow_smul_latticeQuotient_eq_zero R V a _ n le_rfl _

private theorem tensorProductToLatticeQuotient_mk_tmul (a : ℤ) (n : ℕ) (p : R⟦X⟧) (v : V) :
    tensorProductToLatticeQuotient R V a n (Ideal.Quotient.mk _ p ⊗ₜ[R] v) =
      Submodule.Quotient.mk ⟨p • of R (single a v), (mem_powerSeriesLattice R V).1
        ((powerSeriesLattice R V a).smul_mem p ((mem_powerSeriesLattice R V).2
          ((of_mem_lattice_iff R V).2 (LaurentSeries.single_mem_lattice le_rfl v))))⟩ := by
  rw [tensorProductToLatticeQuotient, AlgebraTensorModule.lift_tmul]
  exact smul_latticeQuotient_mk R V a (a + n) p _

/-- The coefficients of a jet at `a, …, a + n - 1`, as a tensor of truncated power series. -/
private def latticeQuotientToTensorProduct (a : ℤ) (n : ℕ) :
    latticeQuotient R V a (a + n) →ₗ[R]
      (R⟦X⟧ ⧸ Ideal.span {(PowerSeries.X ^ n : R⟦X⟧)}) ⊗[R] V :=
  ∑ k : Fin n, TensorProduct.mk R _ V (Ideal.Quotient.mk _ (PowerSeries.X ^ (k : ℕ))) ∘ₗ
    LinearMap.proj ⟨a + k, Finset.mem_Ico.2 ⟨by omega, by omega⟩⟩ ∘ₗ
      (latticeQuotientEquiv R V a (a + n)).toLinearMap

private theorem latticeQuotientToTensorProduct_apply (a : ℤ) (n : ℕ)
    (q : latticeQuotient R V a (a + n)) :
    latticeQuotientToTensorProduct R V a n q = ∑ k : Fin n,
      Ideal.Quotient.mk _ (PowerSeries.X ^ (k : ℕ)) ⊗ₜ[R]
        latticeQuotientEquiv R V a (a + n) q ⟨a + k, Finset.mem_Ico.2 ⟨by omega, by omega⟩⟩ := by
  simp [latticeQuotientToTensorProduct]

/-- Modulo `X ^ n`, a power series is the sum of its first `n` monomials. -/
private theorem mk_eq_sum (n : ℕ) (p : R⟦X⟧) :
    Ideal.Quotient.mk (Ideal.span {(PowerSeries.X ^ n : R⟦X⟧)}) p =
      ∑ k : Fin n, PowerSeries.coeff k p • Ideal.Quotient.mk _ (PowerSeries.X ^ (k : ℕ)) := by
  simp only [← Ideal.Quotient.mkₐ_eq_mk R, ← map_smul, ← map_sum]
  simp only [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton,
    PowerSeries.X_pow_dvd_iff]
  intro m hm
  simp [Fin.sum_univ_eq_sum_range (fun k ↦ PowerSeries.coeff k p • (PowerSeries.X ^ k : R⟦X⟧)),
    PowerSeries.coeff_X_pow, hm]

private theorem leftInverse_latticeQuotientToTensorProduct (a : ℤ) (n : ℕ) :
    Function.LeftInverse (latticeQuotientToTensorProduct R V a n)
      (tensorProductToLatticeQuotient R V a n) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => rw [map_add, map_add, hz, hw]
  | tmul x v =>
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [tensorProductToLatticeQuotient_mk_tmul, latticeQuotientToTensorProduct_apply, mk_eq_sum,
      sum_tmul]
    simp [coeff_smul_single, smul_tmul]

private theorem rightInverse_latticeQuotientToTensorProduct (a : ℤ) (n : ℕ) :
    Function.RightInverse (latticeQuotientToTensorProduct R V a n)
      (tensorProductToLatticeQuotient R V a n) := by
  intro q
  let e := latticeQuotientEquiv R V a (a + n)
  let σ : Fin n → Finset.Ico a (a + n) := fun k ↦ ⟨a + k, Finset.mem_Ico.2 ⟨by omega, by omega⟩⟩
  have hσ : Function.Bijective σ := by
    refine ⟨fun k l h ↦ Fin.ext ?_, fun j ↦ ?_⟩
    · have := congrArg Subtype.val h
      simp only [σ] at this
      omega
    · obtain ⟨j, hj⟩ := j
      rw [Finset.mem_Ico] at hj
      exact ⟨⟨(j - a).toNat, by omega⟩, Subtype.ext (by simp only [σ]; omega)⟩
  have hφ (k : Fin n) (v : V) : tensorProductToLatticeQuotient R V a n
      (Ideal.Quotient.mk _ (PowerSeries.X ^ (k : ℕ)) ⊗ₜ[R] v) = e.symm (Pi.single (σ k) v) := by
    rw [tensorProductToLatticeQuotient_mk_tmul, latticeQuotientEquiv_symm_single]
    exact congrArg Submodule.Quotient.mk (Subtype.ext (X_pow_smul_single R V k a v))
  rw [latticeQuotientToTensorProduct_apply, map_sum]
  simp only [hφ, ← map_sum]
  rw [Fintype.sum_bijective σ hσ _ (fun j ↦ Pi.single j (e q j)) (fun _ ↦ rfl),
    Finset.univ_sum_single, LinearEquiv.symm_apply_apply]

/-- The jets `U_a(V) / U_(a+n)(V)` of length `n` of `V`-valued Laurent series are the scalar
extension `(R⟦X⟧ ⧸ (X ^ n)) ⊗[R] V` of `V` to jets of power series, through `p ⊗ v ↦ p X ^ a v`. -/
def tensorProductLatticeQuotientEquiv (a : ℤ) (n : ℕ) :
    (R⟦X⟧ ⧸ Ideal.span {(PowerSeries.X ^ n : R⟦X⟧)}) ⊗[R] V ≃ₗ[R⟦X⟧]
      latticeQuotient R V a (a + n) :=
  .ofBijective (tensorProductToLatticeQuotient R V a n)
    ⟨(leftInverse_latticeQuotientToTensorProduct R V a n).injective,
      (rightInverse_latticeQuotientToTensorProduct R V a n).surjective⟩

/-- The jet comparison sends the jet of `p` tensored with `v` to the jet of `p X ^ a v`. -/
@[simp]
theorem tensorProductLatticeQuotientEquiv_mk_tmul (a : ℤ) (n : ℕ) (p : R⟦X⟧) (v : V) :
    tensorProductLatticeQuotientEquiv R V a n (Ideal.Quotient.mk _ p ⊗ₜ[R] v) =
      Submodule.Quotient.mk ⟨p • of R (single a v), (mem_powerSeriesLattice R V).1
        ((powerSeriesLattice R V a).smul_mem p ((mem_powerSeriesLattice R V).2
          ((of_mem_lattice_iff R V).2 (LaurentSeries.single_mem_lattice le_rfl v))))⟩ :=
  tensorProductToLatticeQuotient_mk_tmul R V a n p v

end CommRing

end TauCeti.HahnModule
