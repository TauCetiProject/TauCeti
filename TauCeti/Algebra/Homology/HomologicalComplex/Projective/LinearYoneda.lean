/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LinearYoneda

/-!
# Morphisms out of a complex of projectives that is exact in low degrees

Let `K` be a chain complex indexed by `ℕ` in a `k`-linear abelian category, whose terms `Kᵢ` with
`i ≤ n` are projective. If `K` is exact in every degree `i ≤ n`, then the cochain complex
`Hom(K, Y)` of morphisms into any object `Y` is exact in every degree `i ≤ n`
(`ChainComplex.exactAt_linearYonedaObj_of_projective`). Exactness in degree `n` of `Hom(K, Y)` uses
exactness and projectivity of `K` in degrees `≤ n` only, not in degree `n + 1`.

The proof constructs a contracting homotopy in degrees `≤ n` one degree at a time. Exactness in
degree `0` makes `K₁ ⟶ K₀` an epimorphism, and projectivity of `K₀` gives `s₀ : K₀ ⟶ K₁` with
`s₀ ≫ d = 𝟙`. Given `sᵢ : Kᵢ ⟶ Kᵢ₊₁` with `d ≫ sᵢ ≫ d = d`, the map `𝟙 - d ≫ sᵢ` of `Kᵢ₊₁` is a
cycle, so by exactness in degree `i + 1` and projectivity of `Kᵢ₊₁` it lifts to
`sᵢ₊₁ : Kᵢ₊₁ ⟶ Kᵢ₊₂` with `sᵢ₊₁ ≫ d + d ≫ sᵢ = 𝟙`
(`ChainComplex.exists_comp_d_eq_sub_d_comp_of_projective`), which again satisfies `d ≫ sᵢ₊₁ ≫ d = d`
(`ChainComplex.exists_d_comp_comp_d_eq_d_of_projective`). A cocycle `f : Kᵢ₊₁ ⟶ Y`, one with
`d ≫ f = 0`, is then the coboundary `f = d ≫ sᵢ ≫ f`.

Applied to the relative singular chains of a pair that is homologically `n`-connected, this makes
its relative singular cohomology vanish up to degree `n`, with values in any coefficient object.

## Main results

* `ChainComplex.exactAt_linearYonedaObj_of_projective`: `Hom(K, Y)` is exact in degrees `≤ n` when
  `K` has projective terms and is exact in degrees `≤ n`.
* `ChainComplex.exists_comp_d_eq_id_of_projective`,
  `ChainComplex.exists_comp_d_eq_sub_d_comp_of_projective` and
  `ChainComplex.exists_d_comp_comp_d_eq_d_of_projective`: the partial contracting homotopy.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 2.2 (Comparison Theorem 2.2.6, whose
  inductive construction this follows).
-/

public section

open CategoryTheory Limits

namespace ChainComplex

variable {C : Type*} [Category* C] [Abelian C] (k : Type*) [Ring k] [Linear k C]
  (K : ChainComplex C ℕ) (Y : C)

variable {K} in
/-- **The first step of a contraction.** If a chain complex `K` is exact in degree `0` and `K₀` is
projective, then `K₁ ⟶ K₀` has a section `s₀ : K₀ ⟶ K₁`. -/
theorem exists_comp_d_eq_id_of_projective [Projective (K.X 0)] (hK : K.ExactAt 0) :
    ∃ s : K.X 0 ⟶ K.X 1, s ≫ K.d 1 0 = 𝟙 _ := by
  rw [HomologicalComplex.exactAt_iff' K 1 0 0 (by simp) (by simp)] at hK
  refine ⟨hK.liftFromProjective (𝟙 _) ?_, hK.liftFromProjective_comp _ _⟩
  rw [Category.id_comp]
  exact K.shape 0 0 (by simp)

variable {K} in
/-- **The inductive step of a contraction.** If a chain complex `K` is exact in degree `i + 1`,
`Kᵢ₊₁` is projective and `sᵢ : Kᵢ ⟶ Kᵢ₊₁` satisfies `d ≫ sᵢ ≫ d = d`, then there is
`sᵢ₊₁ : Kᵢ₊₁ ⟶ Kᵢ₊₂` with `sᵢ₊₁ ≫ d = 𝟙 - d ≫ sᵢ`. -/
theorem exists_comp_d_eq_sub_d_comp_of_projective {i : ℕ} [Projective (K.X (i + 1))]
    (hK : K.ExactAt (i + 1))
    (s : K.X i ⟶ K.X (i + 1)) (hs : K.d (i + 1) i ≫ s ≫ K.d (i + 1) i = K.d (i + 1) i) :
    ∃ s' : K.X (i + 1) ⟶ K.X (i + 2), s' ≫ K.d (i + 2) (i + 1) = 𝟙 _ - K.d (i + 1) i ≫ s := by
  rw [HomologicalComplex.exactAt_iff' K (i + 2) (i + 1) i (by simp) (by simp)] at hK
  refine ⟨hK.liftFromProjective (𝟙 _ - K.d (i + 1) i ≫ s) ?_, hK.liftFromProjective_comp _ _⟩
  -- `(𝟙 - d ≫ s) ≫ d = d - d ≫ s ≫ d`, which vanishes by `hs`.
  rw [HomologicalComplex.shortComplexFunctor'_obj_g, Preadditive.sub_comp, Category.id_comp,
    Category.assoc, hs, sub_self]

variable {K} in
/-- In a chain complex whose terms in degrees `≤ n` are projective and which is exact in degrees
`≤ n`, every term `Kᵢ` with `i ≤ n` has a map `sᵢ : Kᵢ ⟶ Kᵢ₊₁` with `d ≫ sᵢ ≫ d = d`, where
`d : Kᵢ₊₁ ⟶ Kᵢ`. -/
theorem exists_d_comp_comp_d_eq_d_of_projective {n : ℕ} (hP : ∀ i ≤ n, Projective (K.X i))
    (hK : ∀ i ≤ n, K.ExactAt i) :
    ∀ i ≤ n, ∃ s : K.X i ⟶ K.X (i + 1), K.d (i + 1) i ≫ s ≫ K.d (i + 1) i = K.d (i + 1) i
  | 0, _ => by
    have := hP 0 (Nat.zero_le n)
    obtain ⟨s, hs⟩ := exists_comp_d_eq_id_of_projective (hK 0 (Nat.zero_le n))
    exact ⟨s, by rw [hs, Category.comp_id]⟩
  | i + 1, hi => by
    have := hP (i + 1) hi
    obtain ⟨s, hs⟩ := exists_d_comp_comp_d_eq_d_of_projective hP hK i (by lia)
    obtain ⟨s', hs'⟩ := exists_comp_d_eq_sub_d_comp_of_projective (hK (i + 1) hi) s hs
    refine ⟨s', ?_⟩
    rw [hs', Preadditive.comp_sub, Category.comp_id, K.d_comp_d_assoc, zero_comp, sub_zero]

/-- **Morphisms out of a complex of projectives exact in low degrees.** If a chain complex `K`
indexed by `ℕ` has projective terms and is exact in every degree `≤ n`, then the cochain complex
`Hom(K, Y)` is exact in every degree `≤ n`, for every object `Y`. Only the terms of `K` in degrees
`≤ n` need to be projective. -/
theorem exactAt_linearYonedaObj_of_projective {n : ℕ} (hP : ∀ i ≤ n, Projective (K.X i))
    (hK : ∀ i ≤ n, K.ExactAt i) {i : ℕ} (hi : i ≤ n) : (K.linearYonedaObj k Y).ExactAt i := by
  have := hP 0 (Nat.zero_le n)
  cases i with
  | zero =>
    rw [exactAt_linearYonedaObj_zero_iff]
    intro f hf
    obtain ⟨s, hs⟩ := exists_comp_d_eq_id_of_projective (hK 0 (Nat.zero_le n))
    rw [← Category.id_comp f, ← hs, Category.assoc, hf, comp_zero]
  | succ i =>
    rw [exactAt_linearYonedaObj_succ_iff]
    intro f hf
    have := hP (i + 1) hi
    obtain ⟨s, hs⟩ := exists_d_comp_comp_d_eq_d_of_projective hP hK i (by lia)
    obtain ⟨s', hs'⟩ := exists_comp_d_eq_sub_d_comp_of_projective (hK (i + 1) hi) s hs
    -- `f = (s' ≫ d + d ≫ s) ≫ f = s' ≫ d ≫ f + d ≫ s ≫ f`, and `d ≫ f = 0`.
    refine ⟨s ≫ f, ?_⟩
    calc K.d (i + 1) i ≫ s ≫ f = (s' ≫ K.d (i + 2) (i + 1) + K.d (i + 1) i ≫ s) ≫ f := by
          rw [Preadditive.add_comp, Category.assoc, hf, comp_zero, zero_add, Category.assoc]
      _ = f := by rw [hs', sub_add_cancel, Category.id_comp]

end ChainComplex
