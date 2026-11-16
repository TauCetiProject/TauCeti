/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Cohomology.Basic

/-!
# Cohomology maps of divisor inclusions

For divisors `D ≤ E` on a complex curve, the sheaf inclusion `O(D) → O(E)` induces maps
`Hⁿ(O(D)) → Hⁿ(O(E))` on cover-colimit Čech cohomology. These maps are functorial in the
inclusion, and the point-twist cohomology map is the case `E = D + x`.

On a compact Hausdorff complex curve the map on first cohomology is surjective for every
inclusion `D ≤ E`. This follows by adding the points of `E - D` one at a time, since each
point twist is surjective on `H¹` (the point skyscraper has no first Čech cohomology).
Consequently, when `H¹(O(D))` is finite-dimensional, `dim H¹(O(E)) ≤ dim H¹(O(D))`.

## Main definitions and results

* `divisorCechCohomologyMapOfLE`: the map `Hⁿ(O(D)) → Hⁿ(O(E))` induced by `D ≤ E`.
* `divisorCechCohomologyMapOfLE_refl`, `divisorCechCohomologyMapOfLE_comp`: functoriality.
* `pointTwistCohomologyMap_eq_divisorCechCohomologyMapOfLE`: the point twist is a special case.
* `divisorCechCohomologyMapOfLE_one_surjective`: surjectivity on `H¹`.
* `finrank_divisorCechCohomology_one_le_of_le`: `h¹` is antitone in the divisor.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §16 and the proof of Theorem 17.6.
-/

public noncomputable section

open CategoryTheory TopologicalSpace
open TauCeti.Topology TauCeti.AlgebraicGeometry
open scoped Manifold

namespace TauCeti.RiemannSurface

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The map `Hⁿ(O(D)) → Hⁿ(O(E))` on cover-colimit Čech cohomology induced by the divisor
inclusion `O(D) → O(E)` for `D ≤ E`. -/
def divisorCechCohomologyMapOfLE {D E : WeilDivisor X} (h : D ≤ E) (n : ℕ) :
    divisorCechCohomology D n →ₗ[ℂ] divisorCechCohomology E n :=
  ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map (divisorSheafMapOfLE h).hom).hom

/-- The divisor-inclusion cohomology map is the Čech cohomology functor applied to the native
divisor sheaf inclusion. -/
theorem divisorCechCohomologyMapOfLE_def {D E : WeilDivisor X} (h : D ≤ E) (n : ℕ) :
    divisorCechCohomologyMapOfLE h n =
      ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
        (divisorSheafMapOfLE h).hom).hom := (rfl)

/-- The cohomology map of the identity inclusion `D ≤ D` is the identity. -/
@[simp]
theorem divisorCechCohomologyMapOfLE_refl (D : WeilDivisor X) (n : ℕ) :
    divisorCechCohomologyMapOfLE (le_refl D) n = LinearMap.id := by
  rw [divisorCechCohomologyMapOfLE_def, divisorSheafMapOfLE_refl]
  exact congrArg ModuleCat.Hom.hom
    ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map_id _)

/-- The cohomology maps of divisor inclusions compose. -/
@[simp]
theorem divisorCechCohomologyMapOfLE_comp {D E F : WeilDivisor X} (hDE : D ≤ E) (hEF : E ≤ F)
    (n : ℕ) :
    divisorCechCohomologyMapOfLE hEF n ∘ₗ divisorCechCohomologyMapOfLE hDE n =
      divisorCechCohomologyMapOfLE (hDE.trans hEF) n := by
  simp only [divisorCechCohomologyMapOfLE_def, ← divisorSheafMapOfLE_comp hDE hEF]
  exact (congrArg ModuleCat.Hom.hom
    ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map_comp _ _)).symm

/-- Pointwise form of `divisorCechCohomologyMapOfLE_comp`. -/
@[simp]
theorem divisorCechCohomologyMapOfLE_comp_apply {D E F : WeilDivisor X} (hDE : D ≤ E)
    (hEF : E ≤ F) (n : ℕ) (c : divisorCechCohomology D n) :
    divisorCechCohomologyMapOfLE hEF n (divisorCechCohomologyMapOfLE hDE n c) =
      divisorCechCohomologyMapOfLE (hDE.trans hEF) n c := by
  rw [← divisorCechCohomologyMapOfLE_comp hDE hEF n, LinearMap.comp_apply]

/-- The point-twist cohomology map is the cohomology map of the inclusion `D ≤ D + x`. -/
theorem pointTwistCohomologyMap_eq_divisorCechCohomologyMapOfLE (D : WeilDivisor X) (x : X)
    (n : ℕ) :
    pointTwistCohomologyMap D x n =
      divisorCechCohomologyMapOfLE (WeilDivisor.le_add_ofPoint D x) n := by
  rw [pointTwistCohomologyMap_def, divisorCechCohomologyMapOfLE_def]

variable [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X] [T2Space X]

/-- The surjectivity on `H¹` for `D ≤ E`, by induction on the degree of the effective divisor
`E - D`: remove one point of `E - D` at a time, starting from `D`. -/
private theorem divisorCechCohomologyMapOfLE_one_surjective_aux (E : WeilDivisor X) :
    ∀ (k : ℕ) (D : WeilDivisor X) (h : D ≤ E), WeilDivisor.degree (E - D) = k →
      Function.Surjective (divisorCechCohomologyMapOfLE h 1) := by
  intro k
  induction k with
  | zero =>
    intro D h hk
    have hED : E - D = 0 :=
      (WeilDivisor.degree_eq_zero_iff (sub_nonneg.mpr h)).mp (by exact_mod_cast hk)
    obtain rfl : E = D := sub_eq_zero.mp hED
    rw [divisorCechCohomologyMapOfLE_refl]
    exact Function.surjective_id
  | succ k ih =>
    intro D h hk
    have hpos : E - D ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hk
      exact absurd hk (by omega)
    obtain ⟨x, hx⟩ := WeilDivisor.exists_pos_coeff_of_ne_zero (sub_nonneg.mpr h) hpos
    have hD' : D + WeilDivisor.ofPoint x ≤ E := WeilDivisor.add_ofPoint_le_of_coeff_lt h
      (by simpa only [WeilDivisor.coeff_sub, sub_pos] using hx)
    have hk' : WeilDivisor.degree (E - (D + WeilDivisor.ofPoint x)) = k := by
      rw [sub_add_eq_sub_sub, map_sub, WeilDivisor.degree_ofPoint, hk]
      push_cast
      ring
    rw [← divisorCechCohomologyMapOfLE_comp (WeilDivisor.le_add_ofPoint D x) hD',
      LinearMap.coe_comp]
    exact (ih _ hD' hk').comp (by
      rw [← pointTwistCohomologyMap_eq_divisorCechCohomologyMapOfLE]
      exact pointTwistCohomologyMap_one_surjective D x)

/-- On a compact Hausdorff complex curve, the map `H¹(O(D)) → H¹(O(E))` induced by `D ≤ E` is
surjective. Each point twist is surjective on `H¹`, and `O(E)` is reached from `O(D)` by
finitely many point twists. -/
theorem divisorCechCohomologyMapOfLE_one_surjective {D E : WeilDivisor X} (h : D ≤ E) :
    Function.Surjective (divisorCechCohomologyMapOfLE h 1) :=
  divisorCechCohomologyMapOfLE_one_surjective_aux E _ D h
    (Int.toNat_of_nonneg (WeilDivisor.degree_nonneg (sub_nonneg.mpr h))).symm

/-- On a compact Hausdorff complex curve, `h¹(O(E)) ≤ h¹(O(D))` for `D ≤ E` whenever the first
cohomology of `O(D)` is finite-dimensional. -/
theorem finrank_divisorCechCohomology_one_le_of_le {D E : WeilDivisor X} (h : D ≤ E)
    [FiniteDimensional ℂ (divisorCechCohomology D 1)] :
    Module.finrank ℂ (divisorCechCohomology E 1) ≤ Module.finrank ℂ (divisorCechCohomology D 1) :=
  LinearMap.finrank_le_finrank_of_surjective (divisorCechCohomologyMapOfLE_one_surjective h)

end TauCeti.RiemannSurface
