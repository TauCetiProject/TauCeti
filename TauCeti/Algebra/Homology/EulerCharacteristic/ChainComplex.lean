/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.EulerCharacteristic
public import TauCeti.Algebra.Category.ModuleCat.Finrank
public import TauCeti.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Euler--Poincaré for chain complexes of vector spaces indexed by `ℕ`

A chain complex `K` indexed by `ℕ`, with differentials `Kₙ₊₁ ⟶ Kₙ`, is the shape of singular and
cellular chains.  When its terms are finite-dimensional vector spaces, rank--nullity for each
differential, applied to the boundaries `Bₙ = im (Kₙ₊₁ ⟶ Kₙ)`, gives

```text
dim Kₙ = dim Hₙ(K) + dim Bₙ + dim Bₙ₋₁,
```

(`ChainComplex.finrank_X_zero`, `ChainComplex.finrank_X_succ`), and the alternating sum of these
identities telescopes: up to degree `n` the alternating sums of the dimensions of the terms and
of the homology differ by `(-1)ⁿ dim Bₙ`
(`ChainComplex.sum_range_finrank_X_eq_sum_range_finrank_homology_add`).  If the differential
`Kₙ₊₁ ⟶ Kₙ` vanishes, the last boundary term `dim Bₙ` vanishes, so the alternating sums of the
dimensions of the terms and of the homology agree up to degree `n`
(`ChainComplex.sum_range_finrank_X_eq_sum_range_finrank_homology`).  The terms in degrees above
`n + 1` play no role.

For a complex of finite-dimensional vector spaces that vanishes in all large degrees this is the
equality of Mathlib's term and homology Euler characteristics
(`ChainComplex.eulerChar_eq_homologyEulerChar`).  Both sides are `finsum`s, and the vanishing
hypothesis is what makes them honest finite sums.  The same equality for bounded cochain
complexes indexed by `ℤ` with terms in `FGModuleCat k` is
`HomologicalComplex.eulerChar_forgetFG_eq_homologyEulerChar`; here the complex stays in
`ModuleCat k` with the homological indexing by `ℕ`, and finite-dimensionality of its terms is a
hypothesis.

The telescoping rests on the description of the homology of one short complex `X₁ ⟶ X₂ ⟶ X₃` of
modules as the kernel of the second map modulo the range of the first: over a division ring its
dimension is `dim ker g - dim im f`
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

variable {k : Type u} [DivisionRing k] (K : ChainComplex (ModuleCat.{v} k) ℕ)

/-- In degree `0`, every element is a cycle, so `dim K₀ = dim H₀(K) + dim im (K₁ ⟶ K₀)`. -/
theorem finrank_X_zero [Module.Finite k (K.X 0)] :
    finrank k (K.X 0) = finrank k (K.homology 0) + finrank k (LinearMap.range (K.d 1 0).hom) := by
  have : Module.Finite k (K.sc' 1 0 0).X₂ := ‹Module.Finite k (K.X 0)›
  -- The maps of `K.sc' i j k` are `K.d i j` and `K.d j k` by construction.
  have h : finrank k (K.sc' 1 0 0).homology + finrank k (LinearMap.range (K.d 1 0).hom) =
      finrank k (LinearMap.ker (K.d 0 0).hom) :=
    (K.sc' 1 0 0).finrank_homology_add_finrank_range_f
  -- `K.homology j` is by definition the homology of `K.sc j`.
  have e : K.homology 0 ≅ (K.sc' 1 0 0).homology :=
    ShortComplex.homologyMapIso (K.isoSc' 1 0 0 (by simp) (by simp))
  rw [K.shape 0 0 (by simp), ModuleCat.hom_zero, LinearMap.ker_zero, finrank_top,
    ← e.toLinearEquiv.finrank_eq] at h
  exact h.symm

/-- In degree `n + 1`, rank--nullity for `Kₙ₊₁ ⟶ Kₙ` gives
`dim Kₙ₊₁ = dim Hₙ₊₁(K) + dim im (Kₙ₊₂ ⟶ Kₙ₊₁) + dim im (Kₙ₊₁ ⟶ Kₙ)`. -/
theorem finrank_X_succ (n : ℕ) [Module.Finite k (K.X (n + 1))] :
    finrank k (K.X (n + 1)) = finrank k (K.homology (n + 1)) +
      finrank k (LinearMap.range (K.d (n + 2) (n + 1)).hom) +
        finrank k (LinearMap.range (K.d (n + 1) n).hom) := by
  have : Module.Finite k (K.sc' (n + 2) (n + 1) n).X₂ := ‹Module.Finite k (K.X (n + 1))›
  -- The maps of `K.sc' i j k` are `K.d i j` and `K.d j k` by construction.
  have h : finrank k (K.sc' (n + 2) (n + 1) n).homology +
      finrank k (LinearMap.range (K.d (n + 2) (n + 1)).hom) =
        finrank k (LinearMap.ker (K.d (n + 1) n).hom) :=
    (K.sc' (n + 2) (n + 1) n).finrank_homology_add_finrank_range_f
  -- `K.homology j` is by definition the homology of `K.sc j`.
  have e : K.homology (n + 1) ≅ (K.sc' (n + 2) (n + 1) n).homology :=
    ShortComplex.homologyMapIso (K.isoSc' (n + 2) (n + 1) n (by simp) (by simp))
  rw [← e.toLinearEquiv.finrank_eq] at h
  rw [← LinearMap.finrank_range_add_finrank_ker (K.d (n + 1) n).hom, ← h]
  ring

/-- If the terms of `K` through degree `n` are finite-dimensional, the alternating sums up to
degree `n` of the dimensions of the terms and of the homology of `K` differ by the dimension of
the boundaries `im (Kₙ₊₁ ⟶ Kₙ)` in degree `n`, with sign `(-1)ⁿ`. -/
theorem sum_range_finrank_X_eq_sum_range_finrank_homology_add (n : ℕ)
    (hfinite : ∀ i ≤ n, Module.Finite k (K.X i)) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * finrank k (K.X i) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * finrank k (K.homology i) +
        (-1 : ℤ) ^ n * finrank k (LinearMap.range (K.d (n + 1) n).hom) := by
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

/-- **Euler--Poincaré for a chain complex of vector spaces indexed by `ℕ`.**  If the terms of
`K` through degree `n` are finite-dimensional and the differential `Kₙ₊₁ ⟶ Kₙ` vanishes, then
the alternating sums up to degree `n` of the dimensions of the terms and of the homology of `K`
agree. -/
theorem sum_range_finrank_X_eq_sum_range_finrank_homology {n : ℕ}
    (hfinite : ∀ i ≤ n, Module.Finite k (K.X i)) (hn : K.d (n + 1) n = 0) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * finrank k (K.X i) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * finrank k (K.homology i) := by
  rw [K.sum_range_finrank_X_eq_sum_range_finrank_homology_add n hfinite, hn, ModuleCat.hom_zero,
    LinearMap.range_zero, finrank_bot]
  simp

/-- **Euler--Poincaré for a bounded chain complex of vector spaces.**  For a chain complex of
finite-dimensional vector spaces indexed by `ℕ` whose terms vanish in all large degrees, Mathlib's
Euler characteristic of the terms equals that of the homology. -/
theorem eulerChar_eq_homologyEulerChar [∀ n, Module.Finite k (K.X n)]
    (hK : ∀ᶠ n in Filter.atTop, IsZero (K.X n)) :
    K.eulerChar = K.homologyEulerChar := by
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 hK
  have hX : ∀ i ∉ Finset.range (n + 1), IsZero (K.X i) := fun i hi ↦
    hn i (by simp at hi; omega)
  rw [HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset K (Finset.range (n + 1))
      ((GradedObject.finrankSupport_subset_iff _ _).2 fun i hi ↦
        ModuleCat.finrank_eq_zero_of_isZero (hX i hi)),
    HomologicalComplex.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset K
      (Finset.range (n + 1))
      ((GradedObject.finrankSupport_subset_iff _ _).2 fun i hi ↦
        ModuleCat.finrank_eq_zero_of_isZero
          (((K.exactAt_iff i).2 (ShortComplex.exact_of_isZero_X₂ _ (hX i hi))).isZero_homology))]
  simpa using K.sum_range_finrank_X_eq_sum_range_finrank_homology
    (fun _ _ ↦ inferInstance) ((hX (n + 1) (by simp)).eq_of_src _ 0)

end ChainComplex
