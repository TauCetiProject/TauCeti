/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Finrank
public import TauCeti.Algebra.Homology.EulerCharacteristic.HomologicalComplex
public import TauCeti.Algebra.Homology.ShortComplex.ModuleCat
import TauCeti.Algebra.Homology.ModuleCat.Finrank

/-!
# Euler--Poincaré for chain complexes of modules indexed by `ℕ`

A chain complex `K` indexed by `ℕ`, with differentials `Kₙ₊₁ ⟶ Kₙ`, is the shape of singular and
cellular chains.  Over any ring `R` satisfying the strong rank condition and rank--nullity (for
instance a division ring or a commutative domain), when its terms are finitely generated,
rank--nullity at each degree (`HomologicalComplex.finrank_X_eq`), applied to the boundaries
`Bₙ = im (Kₙ₊₁ ⟶ Kₙ)`, gives

```text
finrank R Kₙ = finrank R Hₙ(K) + finrank R Bₙ + finrank R Bₙ₋₁,
```

(`ChainComplex.finrank_X_zero`, `ChainComplex.finrank_X_succ`, and `ChainComplex.finrank_X` in
every degree at once), and the alternating sum of these identities telescopes: up to degree `n` the
alternating sums of the finranks of the terms and of the homology differ by `(-1)ⁿ finrank R Bₙ`
(`ChainComplex.sum_range_finrank_X_eq_sum_range_finrank_homology_add`).  If the differential
`Kₙ₊₁ ⟶ Kₙ` vanishes, the last boundary term `finrank R Bₙ` vanishes, so the alternating sums of
the finranks of the terms and of the homology agree up to degree `n`
(`ChainComplex.sum_range_finrank_X_eq_sum_range_finrank_homology`).  The terms in degrees above
`n + 1` play no role.

For a complex whose terms are all finitely generated and vanish in all large degrees, combining
`HomologicalComplex.finite_not_isZero_X_of_eventually_isZero` with
`HomologicalComplex.eulerChar_eq_homologyEulerChar` gives the equality of Mathlib's term and
homology Euler characteristics directly over any ring satisfying the strong rank condition and
rank--nullity. The same equality for bounded cochain complexes indexed by `ℤ` with terms in
`FGModuleCat R` is `HomologicalComplex.eulerChar_forgetFG_eq_homologyEulerChar`.

Over any ring, both Euler characteristics of a complex indexed by `ℕ` unfold to the alternating
sums `∑ᶠ i, (-1)ⁱ · finrank` (`ChainComplex.eulerChar_eq_finsum_finrank` and
`ChainComplex.homologyEulerChar_eq_finsum_finrank`).

The telescoping rests on the description of the homology of one short complex `X₁ ⟶ X₂ ⟶ X₃` of
modules as the kernel of the second map modulo the range of the first: over a ring satisfying the
strong rank condition and rank--nullity, when `X₂` is finitely generated, the rank of the homology
plus the rank of `im f` is the rank of `ker g`
(`CategoryTheory.ShortComplex.finrank_homology_add_finrank_range_f`).  The same description shows
that over a noetherian ring the homology is finitely generated when `X₂` is
(`CategoryTheory.ShortComplex.finite_homology`).

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 1.1 and 1.3.
-/

public section

open CategoryTheory Limits Module

universe u v

namespace ChainComplex

section Ring

variable {R : Type u} [Ring R] (K : ChainComplex (ModuleCat.{v} R) ℕ)

/-- For a chain complex indexed by `ℕ`, Mathlib's Euler characteristic of the terms is the
alternating sum `∑ᶠ i, (-1)ⁱ · finrank R (Kᵢ)`. -/
theorem eulerChar_eq_finsum_finrank :
    K.eulerChar = ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank R (K.X i) := by
  simp only [HomologicalComplex.eulerChar, GradedObject.eulerChar,
    ComplexShape.eulerCharSignsDownNat_χ, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]

/-- For a chain complex indexed by `ℕ`, Mathlib's Euler characteristic of the homology is the
alternating sum `∑ᶠ i, (-1)ⁱ · finrank R (Hᵢ(K))`. -/
theorem homologyEulerChar_eq_finsum_finrank :
    K.homologyEulerChar = ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank R (K.homology i) := by
  simp only [HomologicalComplex.homologyEulerChar, GradedObject.eulerChar,
    ComplexShape.eulerCharSignsDownNat_χ, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]

end Ring

variable {R : Type u} [Ring R] [StrongRankCondition R] [HasRankNullity.{v} R]
  (K : ChainComplex (ModuleCat.{v} R) ℕ)

/-- In degree `0`, every element is a cycle, so
`finrank R K₀ = finrank R H₀(K) + finrank R im (K₁ ⟶ K₀)`. -/
theorem finrank_X_zero [Module.Finite R (K.X 0)] :
    finrank R (K.X 0) = finrank R (K.homology 0) + finrank R (LinearMap.range (K.d 1 0).hom) := by
  have h := K.finrank_X_eq 0
  -- `simp` cannot rewrite the submodule inside `finrank`, as the instances depend on it.
  rw [ChainComplex.prev, ChainComplex.next_nat_zero, K.shape 0 0 (by simp), ModuleCat.hom_zero,
    LinearMap.range_zero, finrank_bot] at h
  omega

/-- In degree `n + 1`, rank--nullity gives
`finrank R Kₙ₊₁ = finrank R Hₙ₊₁(K) + finrank R im (Kₙ₊₂ ⟶ Kₙ₊₁) + finrank R im (Kₙ₊₁ ⟶ Kₙ)`. -/
theorem finrank_X_succ (n : ℕ) [Module.Finite R (K.X (n + 1))] :
    finrank R (K.X (n + 1)) = finrank R (K.homology (n + 1)) +
      finrank R (LinearMap.range (K.d (n + 2) (n + 1)).hom) +
        finrank R (LinearMap.range (K.d (n + 1) n).hom) := by
  have h := K.finrank_X_eq (n + 1)
  rwa [ChainComplex.prev, ChainComplex.next_nat_succ] at h

/-- In every degree `n`, rank--nullity gives
`finrank R Kₙ = finrank R Hₙ(K) + finrank R im (Kₙ₊₁ ⟶ Kₙ) + finrank R im (Kₙ ⟶ Kₙ₋₁)`, where in
degree `0` the last differential is `K.d 0 0 = 0`. This is `ChainComplex.finrank_X_zero` and
`ChainComplex.finrank_X_succ` in one formula. -/
theorem finrank_X (n : ℕ) [Module.Finite R (K.X n)] :
    finrank R (K.X n) = finrank R (K.homology n) +
      finrank R (LinearMap.range (K.d (n + 1) n).hom) +
        finrank R (LinearMap.range (K.d n (n - 1)).hom) := by
  cases n with
  | zero =>
    rw [K.finrank_X_zero, Nat.zero_sub, K.shape 0 0 (by simp), ModuleCat.hom_zero,
      LinearMap.range_zero, finrank_bot, add_zero]
  | succ n =>
    rw [Nat.add_sub_cancel]
    exact K.finrank_X_succ n

/-- If the terms of `K` through degree `n` are finitely generated, the alternating sums up to
degree `n` of the finranks of the terms and of the homology of `K` differ by the finrank of the
boundaries `im (Kₙ₊₁ ⟶ Kₙ)` in degree `n`, with sign `(-1)ⁿ`. -/
theorem sum_range_finrank_X_eq_sum_range_finrank_homology_add (n : ℕ)
    (hfinite : ∀ i ≤ n, Module.Finite R (K.X i)) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * finrank R (K.X i) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * finrank R (K.homology i) +
        (-1 : ℤ) ^ n * finrank R (LinearMap.range (K.d (n + 1) n).hom) := by
  induction n with
  | zero =>
    let _ := hfinite 0 le_rfl
    simp [K.finrank_X_zero]
  | succ n ih =>
    let _ := hfinite (n + 1) le_rfl
    rw [Finset.sum_range_succ, ih (fun i hi ↦ hfinite i (hi.trans n.le_succ)),
      Finset.sum_range_succ _ (n + 1), K.finrank_X_succ n]
    push_cast
    ring

/-- **Euler--Poincaré for a chain complex of modules indexed by `ℕ`.**  If the terms of `K`
through degree `n` are finitely generated and the differential `Kₙ₊₁ ⟶ Kₙ` vanishes, then the
alternating sums up to degree `n` of the finranks of the terms and of the homology of `K` agree. -/
theorem sum_range_finrank_X_eq_sum_range_finrank_homology {n : ℕ}
    (hfinite : ∀ i ≤ n, Module.Finite R (K.X i)) (hn : K.d (n + 1) n = 0) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * finrank R (K.X i) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * finrank R (K.homology i) := by
  rw [K.sum_range_finrank_X_eq_sum_range_finrank_homology_add n hfinite, hn, ModuleCat.hom_zero,
    LinearMap.range_zero, finrank_bot]
  simp

end ChainComplex
