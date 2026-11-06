/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.EulerCharacteristic
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere

/-!
# Critical counts of Morse functions on spheres

On the sphere `Sⁿ` the height function has a minimum and a maximum and no other critical point.
Comparing an arbitrary Morse function on `Sⁿ` with it, through the parity of the number of critical
points (`TauCeti.IsMorse.toNat_totalCriticalCount_modEq`), shows that every Morse function on `Sⁿ`
has an even number of critical points
(`TauCeti.IsMorse.even_toNat_totalCriticalCount_sphere`). Its signed count is the Euler
characteristic `1 + (-1)ⁿ` of `Sⁿ`
(`TauCeti.IsMorse.sum_range_neg_one_pow_mul_toNat_criticalCount_sphere`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
-/

public section

open Metric Module Set
open scoped Manifold

universe u

namespace TauCeti

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- **Morse functions on a sphere have an even number of critical points.** -/
theorem IsMorse.even_toNat_totalCriticalCount_sphere {f : sphere (0 : E) 1 → ℝ}
    (hf : IsMorse (𝓡 n) f) : Even (totalCriticalCount (𝓡 n) f).toNat := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ E = n + 1)
  obtain ⟨v⟩ := NormedSpace.sphere_nonempty_rclike ℝ (E := E) zero_le_one
  have h₂ : totalCriticalCount (𝓡 n) (sphereHeight v) = 2 := by
    rw [totalCriticalCount_def, criticalPoints_sphereHeight,
      encard_pair (ne_neg_of_mem_unit_sphere ℝ v)]
  have h := hf.toNat_totalCriticalCount_modEq (isMorse_sphereHeight v)
  rw [h₂] at h
  exact Nat.even_iff.2 h

/-- Every Morse function on the sphere `Sⁿ` has signed count `∑ᵢ₌₀ⁿ (-1)ⁱ cᵢ = 1 + (-1)ⁿ`, the
Euler characteristic of `Sⁿ`. -/
theorem IsMorse.sum_range_neg_one_pow_mul_toNat_criticalCount_sphere
    {f : sphere (0 : E) 1 → ℝ} (hf : IsMorse (𝓡 n) f) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount (𝓡 n) f i).toNat =
      1 + (-1) ^ n := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  rw [hf.sum_range_neg_one_pow_mul_toNat_criticalCount_eq_eulerChar finrank_euclideanSpace_fin.le,
    eulerChar_sphere (Fact.out : finrank ℝ E = n + 1)]

end TauCeti
