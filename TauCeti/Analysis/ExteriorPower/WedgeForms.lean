/-
Copyright (c) 2026 Ralf Stephan and The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan, The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.BigOperators.Min
public import TauCeti.LinearAlgebra.ExteriorPower.LinearForms
public import TauCeti.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Tactic.SplitIfs

/-!
# Local bounds for wedge forms

Evertse's triangular basis correction gives bounds of the form
`v (l (σ i) (y j)) ≤ C * ν (σ i) * min (μ i) (μ j)` for increasing positive `μ`.
Passing to exterior powers preserves more than the separate row bounds: if the vector subset
meets the first `k` indices, but every form index comes from the last block, each permutation
product gains the factor `μ (k - 1) / μ k`. This is the small factor that produces a large last
minimum in the exterior-power argument for the Subspace Theorem.

`AbsoluteValue.apply_wedgeForms_plucker_le` proves this refined bound, uniformly in the exterior
power: its constant is `N! * max 1 C ^ N`, where `N` is the number of forms. At a
nonarchimedean absolute value, `AbsoluteValue.apply_wedgeForms_plucker_le_prod` passes row bounds
to wedge forms without any factorial loss. Together these are the local estimates needed to
put Plücker vectors into an approximation domain for the wedge forms.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006), §7.5.30,
  inequalities (7.44) and (7.45).
* The refined estimate and its proof follow Ralf Stephan's
  `DiophantineApproximation/WedgeDomain.lean` in `rwst/Subspace-Theorems`, commit
  `09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0), adapted to Tau Ceti's
  `wedgeForms` and `plucker` and generalized from number fields to commutative rings.
-/

public section

open Finset Module Set Set.powersetCard TauCeti

namespace AbsoluteValue

variable {R : Type*} [CommRing R] [Nontrivial R]
  {ι κ : Type*} [Fintype ι] [LinearOrder ι] [LinearOrder κ]

omit [Nontrivial R] [Fintype ι] [LinearOrder ι] in
/-- Evertse's entrywise estimate passes to each permutation product in the wedge determinant,
retaining the gain on the top block and the nonnegativity of the common bound. -/
private theorem prod_apply_le_ite_div_mul_prod [Fintype κ] (v : AbsoluteValue R ℝ)
    (l : κ → Dual R (ι → R)) (σ : Fin (Fintype.card κ) ≃ κ)
    {μ : ℕ → ℝ} (hμm : MonotoneOn μ (Set.Iio (Fintype.card κ)))
    (hμp : ∀ j < Fintype.card κ, 0 < μ j) {ν : κ → ℝ} (hν : ∀ i, 0 ≤ ν i)
    {C : ℝ} (hC : 0 ≤ C) {y : Fin (Fintype.card κ) → ι → R}
    (hy : ∀ i j, v (l (σ i) (y j)) ≤ C * ν (σ i) * min (μ i) (μ j))
    {k p : ℕ} (J : powersetCard (Fin (Fintype.card κ)) p)
    (hJ : ∃ j ∈ J, (j : ℕ) < k) (T : powersetCard κ p) (τ : Equiv.Perm (Fin p)) :
    0 ≤ (∏ t ∈ (T : Finset κ), ν t) *
      ((if ∀ t ∈ (T : Finset κ), k ≤ (σ.symm t : ℕ) then μ (k - 1) / μ k else 1) *
        ∏ t ∈ (T : Finset κ), μ (σ.symm t)) ∧
    ∏ b, v (l (ofFinEmbEquiv.symm T (τ b)) (y (ofFinEmbEquiv.symm J b))) ≤
      C ^ p * ((∏ t ∈ (T : Finset κ), ν t) *
        ((if ∀ t ∈ (T : Finset κ), k ≤ (σ.symm t : ℕ) then μ (k - 1) / μ k else 1) *
          ∏ t ∈ (T : Finset κ), μ (σ.symm t))) := by
  classical
  let eT := ofFinEmbEquiv.symm T
  let eJ := ofFinEmbEquiv.symm J
  have hperm (g : κ → ℝ) : ∏ b, g (eT (τ b)) = ∏ t ∈ (T : Finset κ), g t :=
    (Equiv.prod_comp τ fun a ↦ g (eT a)).trans (prod_comp_ofFinEmbEquiv_symm T g)
  obtain ⟨j₀, hj₀J, hj₀k⟩ := hJ
  obtain ⟨b₀, hb₀⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem J j₀).2 hj₀J
  have hm0 (b) : 0 ≤ min (μ (σ.symm (eT (τ b)))) (μ (eJ b)) :=
    le_min (hμp _ (Fin.is_lt _)).le (hμp _ (Fin.is_lt _)).le
  have hmin : ∏ b, min (μ (σ.symm (eT (τ b)))) (μ (eJ b)) ≤
      (if ∀ t ∈ (T : Finset κ), k ≤ (σ.symm t : ℕ) then μ (k - 1) / μ k else 1) *
        ∏ b, μ (σ.symm (eT (τ b))) := by
    split_ifs with hT
    · exact prod_min_le_div_mul_prod hμm hμp
        (fun _ ↦ Fin.is_lt _) (fun _ ↦ Fin.is_lt _)
        (fun b ↦ hT _ ((mem_range_ofFinEmbEquiv_symm_iff_mem T _).1 ⟨τ b, rfl⟩))
        ⟨b₀, by simpa [eJ, hb₀] using hj₀k⟩
    · rw [one_mul]
      exact prod_le_prod₀ (fun b _ ↦ hm0 b) fun b _ ↦ min_le_left _ _
  have hmin0 : 0 ≤ ∏ b, min (μ (σ.symm (eT (τ b)))) (μ (eJ b)) :=
    prod_nonneg fun b _ ↦ hm0 b
  refine ⟨mul_nonneg (prod_nonneg fun t _ ↦ hν t) ?_, ?_⟩
  · simpa only [hperm (fun t ↦ μ (σ.symm t))] using hmin0.trans hmin
  calc
    _ ≤ ∏ b, C * ν (eT (τ b)) * min (μ (σ.symm (eT (τ b)))) (μ (eJ b)) := by
      refine prod_le_prod₀ (fun _ _ ↦ v.nonneg _) fun b _ ↦ ?_
      simpa only [Equiv.apply_symm_apply] using hy (σ.symm (eT (τ b))) (eJ b)
    _ = C ^ p * (∏ t ∈ (T : Finset κ), ν t) *
        ∏ b, min (μ (σ.symm (eT (τ b)))) (μ (eJ b)) := by
      rw [prod_mul_distrib, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, hperm]
    _ ≤ C ^ p * (∏ t ∈ (T : Finset κ), ν t) *
        ((if ∀ t ∈ (T : Finset κ), k ≤ (σ.symm t : ℕ) then μ (k - 1) / μ k else 1) *
          ∏ b, μ (σ.symm (eT (τ b)))) :=
      mul_le_mul_of_nonneg_left hmin (mul_nonneg (pow_nonneg hC _) (prod_nonneg fun t _ ↦ hν t))
    _ = _ := by rw [hperm (fun t ↦ μ (σ.symm t))]; ring

/-- **The refined local wedge bound** (Bombieri–Gubler (7.44)–(7.45)). Suppose Evertse's bounds
hold with nonnegative row weights `ν` and positive increasing minima `μ`. For a vector subset
`J` meeting the first `k` indices, the wedge bound gains `μ (k - 1) / μ k` whenever all the form
indices, read through `σ`, lie in the top block. The constant is uniform in the exterior degree.
No number-field hypothesis is needed. -/
theorem apply_wedgeForms_plucker_le [Fintype κ] (v : AbsoluteValue R ℝ)
    (l : κ → Dual R (ι → R)) (σ : Fin (Fintype.card κ) ≃ κ) {μ : ℕ → ℝ}
    (hμm : MonotoneOn μ (Set.Iio (Fintype.card κ))) (hμp : ∀ j < Fintype.card κ, 0 < μ j)
    {ν : κ → ℝ} (hν : ∀ i, 0 ≤ ν i) {C : ℝ} (hC : 0 ≤ C)
    {y : Fin (Fintype.card κ) → ι → R}
    (hy : ∀ i j, v (l (σ i) (y j)) ≤ C * ν (σ i) * min (μ i) (μ j))
    {k p : ℕ} (J : powersetCard (Fin (Fintype.card κ)) p)
    (hJ : ∃ j ∈ J, (j : ℕ) < k) (T : powersetCard κ p) :
    v (wedgeForms l p T (plucker (y ∘ ofFinEmbEquiv.symm J))) ≤
      (Fintype.card κ).factorial * max 1 C ^ Fintype.card κ *
        ((∏ t ∈ (T : Finset κ), ν t) *
          ((if ∀ t ∈ (T : Finset κ), k ≤ (σ.symm t : ℕ) then μ (k - 1) / μ k else 1) *
            ∏ t ∈ (T : Finset κ), μ (σ.symm t))) := by
  classical
  rw [wedgeForms_plucker]
  have hterm := prod_apply_le_ite_div_mul_prod v l σ hμm hμp hν hC hy J hJ T
  have hdet := Matrix.abv_det_le_factorial_mul_of_forall_perm
    (Matrix.of fun a b ↦ l (ofFinEmbEquiv.symm T a) ((y ∘ ofFinEmbEquiv.symm J) b)) v
    (fun τ ↦ (hterm τ).2)
  rw [Fintype.card_fin] at hdet
  have hpN : p ≤ Fintype.card κ := by
    simpa using (Finset.card_le_univ (T : Finset κ))
  have hfac : (p.factorial : ℝ) * C ^ p ≤
      (Fintype.card κ).factorial * max 1 C ^ Fintype.card κ := by
    refine mul_le_mul (by exact_mod_cast Nat.factorial_le hpN) ?_ (pow_nonneg hC _) (by positivity)
    exact (pow_le_pow_left₀ hC (le_max_right _ _) p).trans
      (pow_le_pow_right₀ (le_max_left _ _) hpN)
  have hB := (hterm (Equiv.refl _)).1
  exact hdet.trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_right hfac hB)

/-- At a nonarchimedean absolute value, row bounds pass to the wedge forms with no factorial
loss. In particular, wedge-form evaluations are integral at a finite place whenever every
entry `l i (y j)` is integral there. -/
theorem apply_wedgeForms_plucker_le_prod (v : AbsoluteValue R ℝ) (hv : IsNonarchimedean v)
    (l : κ → Dual R (ι → R)) {p : ℕ} (y : Fin p → ι → R) {ν : κ → ℝ}
    (hy : ∀ i j, v (l i (y j)) ≤ ν i) (T : powersetCard κ p) :
    v (wedgeForms l p T (plucker y)) ≤ ∏ t ∈ (T : Finset κ), ν t := by
  rw [wedgeForms_plucker, ← prod_comp_ofFinEmbEquiv_symm T ν]
  exact Matrix.abv_det_le_prod_of_le _ hv fun i j ↦ hy _ _

end AbsoluteValue
