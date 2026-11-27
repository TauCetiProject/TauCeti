/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Polynomial.Basic
public import TauCeti.InformationTheory.Coding.Basic
public import TauCeti.InformationTheory.Coding.MinimumDistance.Basic
import Mathlib.LinearAlgebra.Lagrange

/-!
# Generalized Reed–Solomon codes

For a field `F`, evaluation points `a : ι → F`, multipliers `v : ι → F` and `k : ℕ`, the
generalized Reed–Solomon code `grsCode a v k` is the image of the polynomials of degree less than
`k` under `p ↦ (v i * p(a i))_i`. The Reed–Solomon code is the case `v = 1`.

If the points are distinct and the multipliers nonzero, a nonzero polynomial of degree less than
`k` vanishes at fewer than `k` of the points. So for `k ≤ n` the evaluation is injective on these
polynomials, and every nonzero word of the code has weight at least `n - k + 1`.

## Main results

* `TauCeti.grsCode a v k`: the generalized Reed–Solomon code.
* `TauCeti.finrank_grsCode`: for `k ≤ n` the code has dimension `k`.
* `TauCeti.le_hammingMinDist_grsCode`: for `1 ≤ k ≤ n` the minimum distance is at least
  `n - k + 1`.

## References

* V. Guruswami, A. Rudra and M. Sudan, *Essential Coding Theory*, Definition 5.2.1,
  Theorem 5.2.4 and Exercise 5.10.
-/

public section

open Polynomial

namespace TauCeti

variable {F ι : Type*} [Field F]

/-- The evaluation map `p ↦ (v i * p(a i))_i` of the generalized Reed–Solomon code. -/
noncomputable def grsEval (a v : ι → F) : F[X] →ₗ[F] ι → F :=
  LinearMap.pi fun i ↦ v i • leval (a i)

theorem grsEval_apply (a v : ι → F) (p : F[X]) (i : ι) : grsEval a v p i = v i * p.eval (a i) :=
  (rfl)

/-- The generalized Reed–Solomon code with evaluation points `a`, multipliers `v` and dimension
parameter `k`: the words `(v i * p(a i))_i` for the polynomials `p` of degree less than `k`. -/
noncomputable def grsCode (a v : ι → F) (k : ℕ) : LinearCode F ι :=
  (degreeLT F k).map (grsEval a v)

theorem grsCode_def (a v : ι → F) (k : ℕ) : grsCode a v k = (degreeLT F k).map (grsEval a v) :=
  (rfl)

variable [Fintype ι] {a v : ι → F}

/-- A polynomial of degree less than `k` whose word vanishes at `k` or more coordinates is zero,
when the points are distinct and the multipliers nonzero. -/
theorem eq_zero_of_card_le_filter_grsEval_eq_zero [DecidableEq F] (ha : Function.Injective a)
    (hv : ∀ i, v i ≠ 0) {k : ℕ} {p : F[X]} (hp : p ∈ degreeLT F k)
    (hk : k ≤ Finset.card {i | grsEval a v p i = 0}) : p = 0 := by
  classical
  refine eq_zero_of_degree_lt_of_eval_index_eq_zero {i | grsEval a v p i = 0} ha.injOn
    ((mem_degreeLT.1 hp).trans_le (by exact_mod_cast hk)) fun i hi ↦ ?_
  have := (Finset.mem_filter.1 hi).2
  rw [grsEval_apply] at this
  exact (mul_eq_zero.1 this).resolve_left (hv i)

/-- For `k ≤ n` the generalized Reed–Solomon code has dimension `k`. -/
theorem finrank_grsCode (ha : Function.Injective a) (hv : ∀ i, v i ≠ 0) {k : ℕ}
    (hk : k ≤ Fintype.card ι) : Module.finrank F (grsCode a v k) = k := by
  classical
  rw [grsCode_def, ← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj,
    (degreeLTEquiv F k).finrank_eq, Module.finrank_fin_fun]
  intro p q hpq
  have h0 : grsEval a v ((p : F[X]) - q) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact hpq
  refine Subtype.ext (sub_eq_zero.1 (eq_zero_of_card_le_filter_grsEval_eq_zero ha hv
    (Submodule.sub_mem _ p.property q.property) ?_))
  simpa [h0] using hk

/-- For `1 ≤ k ≤ n` every nonzero word of the generalized Reed–Solomon code has weight at least
`n - k + 1`, so its minimum distance is at least `n - k + 1`. -/
theorem le_hammingMinDist_grsCode [DecidableEq F] (ha : Function.Injective a)
    (hv : ∀ i, v i ≠ 0) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) :
    Fintype.card ι - k + 1 ≤ (grsCode a v k : Set (ι → F)).hammingMinDist := by
  classical
  have hne : (grsCode a v k).toAddSubgroup ≠ ⊥ := by
    intro h
    have h1 : grsEval a v 1 ∈ grsCode a v k :=
      Submodule.mem_map_of_mem (mem_degreeLT.2 (by rw [degree_one]; exact_mod_cast hk))
    have : grsEval a v 1 = 0 := by
      simpa using (AddSubgroup.mem_bot.1 (h ▸ h1 : grsEval a v 1 ∈ (⊥ : AddSubgroup (ι → F))))
    exact one_ne_zero (eq_zero_of_card_le_filter_grsEval_eq_zero ha hv
      (mem_degreeLT.2 (by rw [degree_one]; exact_mod_cast hk)) (by simpa [this] using hkn))
  refine (Set.le_hammingMinDist_iff_hammingNorm hne).2 fun x hx hx0 ↦ ?_
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hx
  -- The word vanishes at fewer than `k` coordinates.
  have hz : Finset.card {i | grsEval a v p i = 0} < k := by
    by_contra h
    exact hx0 (by rw [eq_zero_of_card_le_filter_grsEval_eq_zero ha hv hp (not_lt.1 h), map_zero])
  have hsum : Finset.card {i | grsEval a v p i = 0} + Finset.card {i | grsEval a v p i ≠ 0} =
      Fintype.card ι :=
    Finset.card_filter_add_card_filter_not (s := Finset.univ) _
  rw [hammingNorm]
  omega

end TauCeti
