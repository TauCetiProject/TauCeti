/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import TauCeti.Geometry.Manifold.Morse.IteratedProd
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# The sum of two height functions on a product of spheres is a Morse function

On the product `Sⁿ × Sᵐ` of two unit spheres, the sum `sphereHeight v ∘ Prod.fst +
sphereHeight w ∘ Prod.snd` of the height functions in the directions of the unit vectors `v` and
`w` is a Morse function. Its critical points are the four pairs of poles `(±v, ±w)`, and its Morse
index at `(x, y)` is the sum of the indices of the two height functions, so the four critical
points have indices `n + m`, `n`, `m` and `0`. For `n = m = 1` this is the standard Morse function
on the two-torus `S¹ × S¹`, with one critical point of index `2`, two of index `1` and one of
index `0`.

More generally, on the product `(Sⁿ)ʳ⁺¹ = IteratedProd (sphere (0 : E) 1) r` of `r + 1` copies of
`Sⁿ`, the iterated sum `iteratedProdSum (sphereHeight v) r` of the height functions has as many
critical points of index `k` as the coefficient of `tᵏ` in `(1 + tⁿ)ʳ⁺¹`.

## Main declarations

* `TauCeti.isMorse_sphereHeight_comp_fst_add_comp_snd`: the sum of two height functions is Morse
  on the product of spheres.
* `TauCeti.mvfderiv_sphereHeight_comp_fst_add_comp_snd_eq_zero_iff`: its critical points are the
  pairs of poles.
* `TauCeti.manifoldMorseIndex_sphereHeight_comp_fst_add_comp_snd`: its Morse index is the sum of
  the indices of the two height functions.
* `TauCeti.criticalCount_sphereHeight_comp_fst_add_comp_snd`: its critical counts, one for each of
  the four pairs of poles.
* `TauCeti.criticalCount_iteratedProdSum_sphereHeight`: the critical counts of the sum of the
  height functions on the power `(Sⁿ)ʳ⁺¹` of `r + 1` spheres are the coefficients of
  `(1 + tⁿ)ʳ⁺¹`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1.
-/

public section

open Metric Module Polynomial
open scoped Manifold

namespace TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] {n m : ℕ}
  [Fact (finrank ℝ E = n + 1)] [Fact (finrank ℝ E' = m + 1)]

/-- **The sum of two height functions is a Morse function on a product of spheres.** -/
theorem isMorse_sphereHeight_comp_fst_add_comp_snd (v : sphere (0 : E) 1)
    (w : sphere (0 : E') 1) :
    IsMorse ((𝓡 n).prod (𝓡 m)) (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) :=
  (isMorse_sphereHeight v).comp_fst_add_comp_snd (isMorse_sphereHeight w)

/-- The critical points of the sum of two height functions on a product of spheres are the four
pairs of poles. -/
@[simp]
theorem mvfderiv_sphereHeight_comp_fst_add_comp_snd_eq_zero_iff (v x : sphere (0 : E) 1)
    (w y : sphere (0 : E') 1) :
    mvfderiv ((𝓡 n).prod (𝓡 m)) (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) (x, y) =
        0 ↔
      (x = v ∨ x = -v) ∧ (y = w ∨ y = -w) := by
  rw [mvfderiv_comp_fst_add_comp_snd_eq_zero_iff
    ((contMDiff_sphereHeight (m := 1) v x).mdifferentiableAt one_ne_zero)
    ((contMDiff_sphereHeight (m := 1) w y).mdifferentiableAt one_ne_zero),
    mvfderiv_sphereHeight_eq_zero_iff, mvfderiv_sphereHeight_eq_zero_iff]

/-- The Morse index of the sum of two height functions on a product of spheres is the sum of the
indices of the two height functions; at the four critical points these are `n + m`, `n`, `m` and
`0`. -/
@[simp]
theorem manifoldMorseIndex_sphereHeight_comp_fst_add_comp_snd (v x : sphere (0 : E) 1)
    (w y : sphere (0 : E') 1) :
    manifoldMorseIndex ((𝓡 n).prod (𝓡 m))
        (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) (x, y) =
      manifoldMorseIndex (𝓡 n) (sphereHeight v) x + manifoldMorseIndex (𝓡 m) (sphereHeight w) y :=
  manifoldMorseIndex_comp_fst_add_comp_snd
    (contMDiff_sphereHeight (m := 2) v x).contDiffAt_comp_extChartAt_symm
    (contMDiff_sphereHeight (m := 2) w y).contDiffAt_comp_extChartAt_symm

/-- **The critical counts of the sum of two height functions on a product of spheres.** Each of the
four pairs of poles, of indices `n + m`, `n`, `m` and `0`, counts once in its index. On the torus
`S¹ × S¹` the critical counts in indices `0`, `1` and `2` are `1`, `2` and `1`. -/
theorem criticalCount_sphereHeight_comp_fst_add_comp_snd (v : sphere (0 : E) 1)
    (w : sphere (0 : E') 1) (j : ℕ) :
    criticalCount ((𝓡 n).prod (𝓡 m)) (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) j =
      (if n + m = j then 1 else 0) + (if n = j then 1 else 0) + (if m = j then 1 else 0) +
        (if 0 = j then 1 else 0) := by
  classical
  have hv := ne_neg_of_mem_unit_sphere ℝ v
  have hw := ne_neg_of_mem_unit_sphere ℝ w
  -- The critical points of index `j` are the pairs of poles whose indices add up to `j`.
  have hset : {z ∈ criticalPoints ((𝓡 n).prod (𝓡 m))
      (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) | manifoldMorseIndex
        ((𝓡 n).prod (𝓡 m)) (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) z = j} =
      ↑(({(v, w), (v, -w), (-v, w), (-v, -w)} : Finset _).filter fun z ↦
        manifoldMorseIndex (𝓡 n) (sphereHeight v) z.1 +
          manifoldMorseIndex (𝓡 m) (sphereHeight w) z.2 = j) := by
    ext ⟨x, y⟩
    simp only [Set.mem_ofPred_eq, mem_criticalPoints,
      mvfderiv_sphereHeight_comp_fst_add_comp_snd_eq_zero_iff,
      manifoldMorseIndex_sphereHeight_comp_fst_add_comp_snd, Finset.coe_filter,
      Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    tauto
  rw [criticalCount_def, hset, Set.encard_coe_eq_coe_finsetCard, Finset.card_filter,
    Finset.sum_insert (by simp [hv, hw]), Finset.sum_insert (by simp [hv]),
    Finset.sum_insert (by simp [hw]), Finset.sum_singleton]
  simp [add_assoc]

/-- **The critical counts of a sum of height functions on a power of a sphere.** The sum of the
height functions on the product `(Sⁿ)ʳ⁺¹` of `r + 1` copies of the sphere `Sⁿ` has as many
critical points of index `k` as the coefficient of `tᵏ` in `(1 + tⁿ)ʳ⁺¹`: a critical point is a
tuple of poles, of index `n` times its number of north poles. -/
theorem criticalCount_iteratedProdSum_sphereHeight (v : sphere (0 : E) 1) (r k : ℕ) :
    criticalCount 𝓘(ℝ, IteratedProdModel (EuclideanSpace ℝ (Fin n)) r)
        (iteratedProdSum (sphereHeight v) r) k =
      (((1 + X ^ n) ^ (r + 1) : ℕ[X]).coeff k : ℕ∞) := by
  -- The critical counts of the height function are the coefficients of `1 + tⁿ`.
  have hcount (j : ℕ) :
      criticalCount (𝓡 n) (sphereHeight v) j = ((1 + X ^ n : ℕ[X]).coeff j : ℕ∞) := by
    rw [criticalCount_sphereHeight, coeff_add, coeff_one, coeff_X_pow]
    split_ifs <;> simp [one_add_one_eq_two]
  induction r generalizing k with
  | zero => rw [criticalCount_iteratedProdSum_zero, hcount, zero_add, pow_one]
  | succ r ih =>
    rw [criticalCount_iteratedProdSum_succ (contMDiff_sphereHeight v), pow_succ, coeff_mul,
      Nat.cast_sum]
    exact Finset.sum_congr rfl fun ij _ ↦ by rw [ih, hcount, Nat.cast_mul]

end TauCeti

end
