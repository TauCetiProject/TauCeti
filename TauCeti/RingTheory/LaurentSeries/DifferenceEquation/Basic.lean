/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.HahnSeries.Map
import TauCeti.RingTheory.LaurentSeries.Multiplication
import TauCeti.RingTheory.PowerSeries.Basic

/-!
# Lifting difference equations to Laurent series

Factoring a common power of `X` out of the multipliers reduces a finite sum of coefficient
maps to a power-series equation. Surjectivity of its leading coefficient equation suffices
over any ring.
-/

public section

open scoped PowerSeries LaurentSeries
open Finset Function HahnSeries

namespace TauCeti.LaurentSeries

/-- A finite sum of coefficient maps with Laurent-series multipliers acts surjectively if
the multipliers have a common lower exponent `m` and their coefficients there give a
surjective equation on the coefficient ring. -/
theorem surjective_sum_mul_mapRingHom_of_surjective_coeff {R ι : Type*} [Ring R]
    (s : Finset ι) (a : ι → R⸨X⸩) (τ : ι → R →+* R) (m : ℤ)
    (hm : ∀ i ∈ s, (m : WithTop ℤ) ≤ (a i).orderTop)
    (hlead : Surjective (fun x => ∑ i ∈ s, (a i).coeff m * τ i x)) :
    Surjective (fun x : R⸨X⸩ => ∑ i ∈ s, a i * mapRingHom (τ i) x) := by
  classical
  choose! A hA using fun i (hi : i ∈ s) ↦
    exists_single_mul_of_le_orderTop (hm i hi)
  have hconst (i : ι) (hi : i ∈ s) : PowerSeries.constantCoeff (A i) = (a i).coeff m := by
    simpa [coeff_single_mul, PowerSeries.coeff_coe, PowerSeries.coeff_zero_eq_constantCoeff_apply]
      using congr($(hA i hi).coeff m)
  intro b
  obtain ⟨x, hx⟩ := TauCeti.surjective_sum_mul_map_of_surjective_constantCoeff s A τ
    (by
      convert hlead using 1
      funext y
      exact sum_congr rfl fun i hi ↦ by rw [hconst i hi]) b.powerSeriesPart
  let d := b.order - m
  refine ⟨single d 1 * (x : R⸨X⸩), ?_⟩
  have hshift : (single d 1 : R⸨X⸩) * single m 1 = single b.order 1 := by
    simp [d, single_mul_single]
  calc
    _ = single b.order 1 * (b.powerSeriesPart : R⸨X⸩) := by
      rw [← hx, map_sum, mul_sum]
      refine sum_congr rfl fun i hi ↦ ?_
      simp only [map_mul, mapRingHom_single, map_one]
      rw [mapRingHom_apply, map_ofPowerSeries]
      let y : R⸨X⸩ := PowerSeries.map (τ i) x
      calc
        a i * (single d 1 * y) = single d 1 * (a i * y) := ((a i).commute_single_one d).left_comm y
        _ = single d 1 * (single m 1 * ((A i : R⸨X⸩) * y)) := by rw [← hA i hi, mul_assoc]
        _ = single b.order 1 * ((A i : R⸨X⸩) * y) := by rw [← mul_assoc, hshift]
    _ = b := b.single_order_mul_powerSeriesPart

end TauCeti.LaurentSeries
