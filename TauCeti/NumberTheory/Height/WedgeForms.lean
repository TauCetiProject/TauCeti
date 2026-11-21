/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.LinearAlgebra.ExteriorPower.LinearForms

import TauCeti.Analysis.ExteriorPower.Plucker
import TauCeti.NumberTheory.Height.LinearForm

/-!
# Local Plücker bounds from nonvanishing wedge forms and projective height

Let `K` be a number field and `l : κ → Dual K (ι → K)` a finite family of linear forms on `ι → K`.
Each `p`-wedge form `TauCeti.wedgeForms l p T` acts on `Set.powersetCard ι p → K` by pairing
against its Plücker coefficient tuple. Whenever `wedgeForms l p T w ≠ 0`, combining the local
Liouville inequality (`NumberField.InfinitePlace.iSup_mul_iSup_pow_mult_le`,
`NumberField.FinitePlace.iSup_mul_iSup_le`) with the minor bound on the `p × p` matrix of form
values bounds the local Plücker sup norm `⨆ s, v (plucker x s)` at a place `v` in terms of the
global projective height `Height.mulHeight (plucker x)` and columnwise bounds `b j` on `l j (x r)`
for `j ∈ T`.

* `NumberField.InfinitePlace.exists_one_le_forall_iSup_plucker_pow_mult_le`: at an infinite place
  `v`, some `A ≥ 1` (uniform across all `p`-subsets `T`, vectors `x`, and bounds `b`) satisfies
  `(⨆ s, v (plucker x s)) ^ v.mult ≤ A * mulHeight (plucker x) * (∏ j ∈ T, b j) ^ v.mult`. Notice
  that `mulHeight (plucker x)` carries exponent `1` rather than `v.mult`.
* `NumberField.FinitePlace.exists_one_le_forall_iSup_plucker_le`: at a finite place `v`, some
  `B ≥ 1` satisfies `⨆ s, v (plucker x s) ≤ B * mulHeight (plucker x) * ∏ j ∈ T, b j`.

Multiplying these estimates over the infinite places and a finite set of finite places yields lower
bounds on the projective height of `plucker x` — and hence on the relative height of the subspace
spanned by `x` — from upper bounds on `l j (x r)`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Lemma 7.5.21.
* J.-H. Evertse and H. P. Schlickewei, *A quantitative version of the absolute Subspace Theorem*,
  J. Reine Angew. Math. **548** (2002), Lemma 12.4.
-/

public section

open Height Module Set Set.powersetCard TauCeti

namespace NumberField

variable {K ι κ : Type*} [Field K] [NumberField K] [LinearOrder ι] [Fintype ι]
  [LinearOrder κ] [Finite κ]

/-- Shared local-Liouville step for `wedgeForms`: given a real-valued absolute value `v`, an
exponent `m`, and the local Liouville inequality at `(v, m)`, some uniform constant `D ≥ 1` bounds
`(⨆ s, v (w s)) ^ m` by `D * mulHeight w * v (wedgeForms l p T w) ^ m` for every `p`-subset `T`
and every `w : powersetCard ι p → K` on which `wedgeForms l p T` does not vanish. -/
private theorem exists_one_le_forall_iSup_pow_le_mul_apply_wedgeForms
    (v : AbsoluteValue K ℝ) (m : ℕ) (p : ℕ)
    (hliouv : ∀ (a w : powersetCard ι p → K), ∑ s, a s * w s ≠ 0 →
      ((⨆ s, v (a s)) * ⨆ s, v (w s)) ^ m ≤
        (Fintype.card (powersetCard ι p) : ℝ) ^ Module.finrank ℚ K *
          (mulHeight a * mulHeight w) * v (∑ s, a s * w s) ^ m)
    (l : κ → Dual K (ι → K)) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (w : powersetCard ι p → K) (T : powersetCard κ p),
      wedgeForms l p T w ≠ 0 →
      (⨆ s, v (w s)) ^ m ≤ D * mulHeight w * v (wedgeForms l p T w) ^ m := by
  let α : powersetCard κ p → powersetCard ι p → K :=
    fun T s ↦ plucker (fun a j ↦ l (ofFinEmbEquiv.symm T a) (Pi.single j 1)) s
  have hα_eq (T : powersetCard κ p) (w : powersetCard ι p → K) :
      wedgeForms l p T w = ∑ s, α T s * w s := by
    simp [α, wedgeForms_apply, wedgeForm_apply]
  let d : powersetCard κ p → ℝ := fun T ↦
    (Fintype.card (powersetCard ι p) : ℝ) ^ Module.finrank ℚ K * mulHeight (α T) /
      (⨆ s, v (α T s)) ^ m
  let D : ℝ := max 1 (⨆ T, d T)
  refine ⟨D, le_max_left _ _, fun w T hne ↦ ?_⟩
  have : Nonempty (powersetCard κ p) := ⟨T⟩
  have hsum : ∑ s, α T s * w s ≠ 0 := hα_eq T w ▸ hne
  obtain ⟨s₀, -, hs₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have : Nonempty (powersetCard ι p) := ⟨s₀⟩
  have hα_pos : 0 < (⨆ s, v (α T s)) ^ m :=
    pow_pos ((v.pos (left_ne_zero_of_mul hs₀)).trans_le (Finite.le_ciSup_of_le s₀ le_rfl)) m
  have hliouv' := hliouv (α T) w hsum
  rw [mul_pow, ← hα_eq T w] at hliouv'
  have hdiv : (⨆ s, v (w s)) ^ m ≤ d T * mulHeight w * v (wedgeForms l p T w) ^ m := by
    dsimp only [d]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀' hα_pos]
    simpa only [mul_assoc] using hliouv'
  exact hdiv.trans <| mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    ((Finite.le_ciSup_of_le T le_rfl).trans (le_max_right _ _)) (mulHeight_pos w).le)
    (pow_nonneg (v.nonneg _) m)

/-- At an infinite place `v`, for any finite family `l : κ → Dual K (ι → K)` of linear forms, some
uniform constant `A ≥ 1` bounds `(⨆ s, v (plucker x s)) ^ v.mult` by
`A * mulHeight (plucker x) * (∏ j ∈ (T : Finset κ), b j) ^ v.mult` whenever `T` is a `p`-subset
whose wedge form `wedgeForms l p T` does not vanish at `plucker x` and `v (l j (x r)) ≤ b j` for
all `r` and `j ∈ T`. -/
theorem InfinitePlace.exists_one_le_forall_iSup_plucker_pow_mult_le (v : InfinitePlace K)
    (l : κ → Dual K (ι → K)) (p : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {x : Fin p → ι → K} (T : powersetCard κ p) {b : κ → ℝ},
      wedgeForms l p T (plucker x) ≠ 0 →
      (∀ r, ∀ j ∈ T, v (l j (x r)) ≤ b j) →
      (⨆ s, v (plucker x s)) ^ v.mult ≤
        A * mulHeight (plucker x) * (∏ j ∈ (T : Finset κ), b j) ^ v.mult := by
  obtain ⟨D, hD1, hD⟩ := exists_one_le_forall_iSup_pow_le_mul_apply_wedgeForms v.val v.mult p
    v.iSup_mul_iSup_pow_mult_le l
  refine ⟨D * (p.factorial : ℝ) ^ v.mult, one_le_mul_of_one_le_of_one_le hD1
    (one_le_pow₀ (by exact_mod_cast Nat.factorial_pos p)), fun {x} T {b} hne hb ↦ ?_⟩
  have hdom : v (wedgeForms l p T (plucker x)) ≤ p.factorial * ∏ j ∈ (T : Finset κ), b j := by
    rw [← plucker_pi_apply]
    exact v.val.plucker_le_factorial_mul_prod _ _ hb
  calc (⨆ s, v (plucker x s)) ^ v.mult
      ≤ D * mulHeight (plucker x) * v (wedgeForms l p T (plucker x)) ^ v.mult := hD _ T hne
    _ ≤ D * mulHeight (plucker x) * (p.factorial * ∏ j ∈ (T : Finset κ), b j) ^ v.mult :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (apply_nonneg _ _) hdom _)
          (mul_nonneg (zero_le_one.trans hD1) (mulHeight_pos _).le)
    _ = D * (p.factorial : ℝ) ^ v.mult * mulHeight (plucker x) *
          (∏ j ∈ (T : Finset κ), b j) ^ v.mult := by
        rw [mul_pow]; ring

/-- At a finite place `v`, for any finite family `l : κ → Dual K (ι → K)` of linear forms, some
uniform constant `B ≥ 1` bounds `⨆ s, v (plucker x s)` by
`B * mulHeight (plucker x) * ∏ j ∈ (T : Finset κ), b j` whenever `T` is a `p`-subset whose wedge
form `wedgeForms l p T` does not vanish at `plucker x` and `v (l j (x r)) ≤ b j` for all `r` and
`j ∈ T`. -/
theorem FinitePlace.exists_one_le_forall_iSup_plucker_le (v : FinitePlace K)
    (l : κ → Dual K (ι → K)) (p : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ {x : Fin p → ι → K} (T : powersetCard κ p) {b : κ → ℝ},
      wedgeForms l p T (plucker x) ≠ 0 →
      (∀ r, ∀ j ∈ T, v (l j (x r)) ≤ b j) →
      ⨆ s, v (plucker x s) ≤
        B * mulHeight (plucker x) * ∏ j ∈ (T : Finset κ), b j := by
  obtain ⟨D, hD1, hD⟩ := exists_one_le_forall_iSup_pow_le_mul_apply_wedgeForms v.val 1 p
    (fun a w h ↦ by rw [pow_one, pow_one]; exact v.iSup_mul_iSup_le a w h) l
  refine ⟨D, hD1, fun {x} T {b} hne hb ↦ ?_⟩
  have hdom : v (wedgeForms l p T (plucker x)) ≤ ∏ j ∈ (T : Finset κ), b j := by
    rw [← plucker_pi_apply]
    exact v.val.plucker_le_prod v.add_le _ _ hb
  have h1 := hD (plucker x) T hne
  rw [pow_one, pow_one] at h1
  exact h1.trans <|
    mul_le_mul_of_nonneg_left hdom (mul_nonneg (zero_le_one.trans hD1) (mulHeight_pos _).le)

end NumberField
