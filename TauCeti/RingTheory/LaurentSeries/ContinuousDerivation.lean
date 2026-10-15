/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.Derivation.Localization
public import TauCeti.RingTheory.HahnSeries.Multiplication
public import TauCeti.RingTheory.LaurentSeries.Derivative

/-!
# Continuous derivations of formal Laurent series

Let `K` be a field and `F = K⸨X⸩`, with the valuation topology, and let `D` be the formal
derivative `TauCeti.laurentSeriesDerivation K`. This file shows that the continuous
`K`-derivations `F → F` are exactly the multiples `a • D` with `a : F`, and that `a = δ X` is
the value of such a derivation `δ` at the parameter `X = single 1 1`.

The algebraic part of the argument holds for every derivation: `δ` agrees with `δ X • D` on the
rational functions `K(X)`, since both are derivations of the fraction field of `K[X]` with the
same value at `X`. Continuity then extends the agreement from `K(X)` to `F`, because `K(X)` is
dense in `F` (`LaurentSeries.coe_range_dense`) and two continuous maps to the Hausdorff space `F`
that agree on a dense subset are equal.

The continuous derivations form an `F`-submodule `TauCeti.continuousDerivations K` of
`Derivation K F F`, which `TauCeti.continuousDerivationsEquiv K` identifies with `F` itself.

## Main results

* `Polynomial.aeval_single_one_eq_algebraMap`: a polynomial evaluated at `X = single 1 1` is its
  image as a Laurent series.
* `Derivation.apply_coe_ratFunc`: on rational functions every `K`-derivation `δ` is `δ X • D`.
* `Derivation.eq_smul_laurentSeriesDerivation`: a continuous derivation `δ` equals `δ X • D`.
* `TauCeti.continuous_smul_laurentSeriesDerivation`: conversely every `a • D` is continuous.
* `Derivation.continuous_iff_exists_eq_smul_laurentSeriesDerivation`: a derivation is continuous
  if and only if it is a multiple of `D`, and `TauCeti.smul_laurentSeriesDerivation_inj`: the
  multiple is unique.
* `TauCeti.continuousDerivations`: the `F`-submodule of continuous derivations, and
  `TauCeti.continuousDerivationsEquiv`: its identification with `F` sending `a` to `a • D`.
-/

public section

open HahnSeries Polynomial RatFunc
open scoped LaurentSeries

/-- A polynomial evaluated at the parameter `X = single 1 1` of `R⸨X⸩` is its image as a Laurent
series. -/
theorem Polynomial.aeval_single_one_eq_algebraMap {R : Type*} [CommSemiring R] (p : R[X]) :
    aeval (single 1 1 : R⸨X⸩) p = algebraMap R[X] R⸨X⸩ p := by
  induction p using Polynomial.induction_on with
  | C a =>
    simp [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, PowerSeries.algebraMap_apply']
  | add p q hp hq => simp [hp, hq]
  | monomial n a h => simp_all [pow_succ, ← mul_assoc]

namespace TauCeti

/-- A multiple of the formal derivative determines the multiplier. -/
@[simp]
theorem smul_laurentSeriesDerivation_inj {R : Type*} [CommRing R] {a b : R⸨X⸩} :
    a • laurentSeriesDerivation R = b • laurentSeriesDerivation R ↔ a = b := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  simpa using congr($h (single 1 1))

variable {K : Type*} [Field K]

/-- Every multiple of the formal derivative is continuous for the valuation topology. -/
theorem continuous_smul_laurentSeriesDerivation (a : K⸨X⸩) :
    Continuous (a • laurentSeriesDerivation K) := by
  refine continuous_const.mul ?_
  -- The body of `laurentSeriesDerivation` is not exposed, so match its coercion explicitly.
  convert LaurentSeries.continuous_derivative (K := K) using 1
  exact funext (laurentSeriesDerivation_apply K)

end TauCeti

variable {K : Type*} [Field K]

namespace Derivation

/-- On rational functions, every `K`-derivation `δ` of `K⸨X⸩` agrees with `δ X • D`, where `D` is
the formal derivative: both are derivations of `K(X)` with the same value at `X`. -/
theorem apply_coe_ratFunc (δ : Derivation K K⸨X⸩ K⸨X⸩) (r : RatFunc K) :
    δ r = δ (single 1 1) * TauCeti.laurentSeriesDerivation K r := by
  set δ' := δ (single 1 1) • TauCeti.laurentSeriesDerivation K
  have hX : δ (single 1 1) = δ' (single 1 1) := by simp [δ']
  have h := IsLocalization.eq_of_leibniz (nonZeroDivisors K[X])
    (δ₁ := fun r : RatFunc K ↦ δ r) (δ₂ := fun r : RatFunc K ↦ δ' r)
    (fun x y ↦ by simp only [map_mul, leibniz, Algebra.smul_def, Algebra.algebraMap_self,
      RingHom.id_apply])
    (fun x y ↦ by simp only [map_mul, leibniz, Algebra.smul_def, Algebra.algebraMap_self,
      RingHom.id_apply])
    fun p ↦ by
      simp only [← IsScalarTower.algebraMap_apply, ← aeval_single_one_eq_algebraMap, map_aeval,
        hX]
  simpa [δ'] using congrFun h r

/-- **Continuous derivations of Laurent series.** A `K`-derivation `δ` of `K⸨X⸩` that is continuous
for the valuation topology is the multiple `δ X • D` of the formal derivative `D`. -/
theorem eq_smul_laurentSeriesDerivation (δ : Derivation K K⸨X⸩ K⸨X⸩) (hδ : Continuous δ) :
    δ = δ (single 1 1) • TauCeti.laurentSeriesDerivation K := by
  refine DFunLike.coe_injective <|
    LaurentSeries.coe_range_dense.equalizer hδ
      (TauCeti.continuous_smul_laurentSeriesDerivation _) ?_
  funext r
  rw [Function.comp_apply, Function.comp_apply, apply_coe_ratFunc, smul_apply, smul_eq_mul]

/-- A `K`-derivation of `K⸨X⸩` is continuous for the valuation topology if and only if it is a
multiple of the formal derivative. -/
theorem continuous_iff_exists_eq_smul_laurentSeriesDerivation {δ : Derivation K K⸨X⸩ K⸨X⸩} :
    Continuous δ ↔ ∃ a : K⸨X⸩, δ = a • TauCeti.laurentSeriesDerivation K := by
  refine ⟨fun hδ ↦ ⟨_, δ.eq_smul_laurentSeriesDerivation hδ⟩, ?_⟩
  rintro ⟨a, rfl⟩
  exact TauCeti.continuous_smul_laurentSeriesDerivation a

end Derivation

namespace TauCeti

variable (K) in
/-- The `K⸨X⸩`-submodule of `K`-derivations of `K⸨X⸩` that are continuous for the valuation
topology. -/
def continuousDerivations : Submodule K⸨X⸩ (Derivation K K⸨X⸩ K⸨X⸩) where
  carrier := {δ | Continuous δ}
  add_mem' hδ hδ' := hδ.add hδ'
  zero_mem' := continuous_zero
  smul_mem' _ _ hδ := continuous_const.mul hδ

@[simp]
theorem mem_continuousDerivations {δ : Derivation K K⸨X⸩ K⸨X⸩} :
    δ ∈ continuousDerivations K ↔ Continuous δ :=
  Iff.rfl

variable (K) in
/-- **The continuous derivations of `K⸨X⸩` form a free module of rank one** with basis the formal
derivative `D`: the equivalence sends `a` to `a • D`, and its inverse evaluates a derivation at the
parameter `X`. -/
noncomputable def continuousDerivationsEquiv : K⸨X⸩ ≃ₗ[K⸨X⸩] continuousDerivations K where
  toFun a := ⟨a • laurentSeriesDerivation K, continuous_smul_laurentSeriesDerivation a⟩
  map_add' a b := Subtype.ext (add_smul a b _)
  map_smul' a b := Subtype.ext (smul_assoc a b _)
  invFun δ := (δ : Derivation K K⸨X⸩ K⸨X⸩) (single 1 1)
  left_inv a := by simp
  right_inv δ := Subtype.ext (δ.1.eq_smul_laurentSeriesDerivation δ.2).symm

@[simp]
theorem coe_continuousDerivationsEquiv_apply (a : K⸨X⸩) :
    (continuousDerivationsEquiv K a : Derivation K K⸨X⸩ K⸨X⸩) = a • laurentSeriesDerivation K :=
  (rfl)

@[simp]
theorem continuousDerivationsEquiv_symm_apply (δ : continuousDerivations K) :
    (continuousDerivationsEquiv K).symm δ = (δ : Derivation K K⸨X⸩ K⸨X⸩) (single 1 1) :=
  (rfl)

end TauCeti
