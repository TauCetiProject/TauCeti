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
* `TauCeti.grsCode_zero`: with parameter `0` the code is zero.
* `TauCeti.finrank_grsCode`: for `k ≤ n` the code has dimension `k`.
* `TauCeti.grsCode_eq_top`: for `n ≤ k` the code is the whole space.
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

@[simp]
theorem grsEval_apply (a v : ι → F) (p : F[X]) (i : ι) : grsEval a v p i = v i * p.eval (a i) :=
  (rfl)

/-- The generalized Reed–Solomon code with evaluation points `a`, multipliers `v` and dimension
parameter `k`: the words `(v i * p(a i))_i` for the polynomials `p` of degree less than `k`. -/
noncomputable def grsCode (a v : ι → F) (k : ℕ) : LinearCode F ι :=
  (degreeLT F k).map (grsEval a v)

theorem grsCode_def (a v : ι → F) (k : ℕ) : grsCode a v k = (degreeLT F k).map (grsEval a v) :=
  (rfl)

variable {a v : ι → F}

@[simp]
theorem mem_grsCode_iff {k : ℕ} {x : ι → F} :
    x ∈ grsCode a v k ↔ ∃ p ∈ degreeLT F k, grsEval a v p = x := by
  rw [grsCode_def, Submodule.mem_map]

theorem grsEval_mem_grsCode {k : ℕ} {p : F[X]} (hp : p ∈ degreeLT F k) :
    grsEval a v p ∈ grsCode a v k :=
  mem_grsCode_iff.2 ⟨p, hp, rfl⟩

/-- With parameter `0` the code is zero: the only polynomial of degree less than `0` is `0`. -/
@[simp]
theorem grsCode_zero (a v : ι → F) : grsCode a v 0 = ⊥ := by
  refine eq_bot_iff.2 fun x hx ↦ ?_
  obtain ⟨p, hp, rfl⟩ := mem_grsCode_iff.1 hx
  rw [mem_degreeLT, Nat.cast_zero, Nat.WithBot.lt_zero_iff, degree_eq_bot] at hp
  rw [hp, map_zero]
  exact zero_mem _

/-- A polynomial of degree less than `k` is zero if its word vanishes on a set `s` of at least `k`
coordinates with distinct points and nonzero multipliers. -/
theorem eq_zero_of_grsEval_eq_zero {s : Finset ι} (ha : Set.InjOn a s) (hv : ∀ i ∈ s, v i ≠ 0)
    {k : ℕ} {p : F[X]} (hp : p ∈ degreeLT F k) (hk : k ≤ s.card)
    (h : ∀ i ∈ s, grsEval a v p i = 0) : p = 0 := by
  classical
  refine eq_zero_of_degree_lt_of_eval_index_eq_zero s ha
    ((mem_degreeLT.1 hp).trans_le (by exact_mod_cast hk)) fun i hi ↦ ?_
  have := h i hi
  rw [grsEval_apply] at this
  exact (mul_eq_zero.1 this).resolve_left (hv i hi)

variable [Fintype ι]

/-- For `k ≤ n` the evaluation map is injective on the polynomials of degree less than `k`, when
the points are distinct and the multipliers nonzero. -/
theorem injOn_grsEval (ha : Function.Injective a) (hv : ∀ i, v i ≠ 0) {k : ℕ}
    (hk : k ≤ Fintype.card ι) : Set.InjOn (grsEval a v) (degreeLT F k) := by
  intro p hp q hq hpq
  refine sub_eq_zero.1 (eq_zero_of_grsEval_eq_zero (s := Finset.univ) ha.injOn (fun i _ ↦ hv i)
    (Submodule.sub_mem _ hp hq) (by simpa using hk) fun _ _ ↦ ?_)
  rw [map_sub, Pi.sub_apply, hpq, sub_self]

/-- The word of a nonzero polynomial of degree less than `k` vanishes at fewer than `k`
coordinates, when the points are distinct and the multipliers nonzero. -/
theorem card_filter_grsEval_eq_zero_lt [DecidableEq F] (ha : Function.Injective a)
    (hv : ∀ i, v i ≠ 0) {k : ℕ} {p : F[X]} (hp : p ∈ degreeLT F k) (hp0 : p ≠ 0) :
    Finset.card {i | grsEval a v p i = 0} < k :=
  not_le.1 fun hk ↦ hp0 (eq_zero_of_grsEval_eq_zero ha.injOn (fun i _ ↦ hv i) hp hk
    fun _ hi ↦ (Finset.mem_filter.1 hi).2)

/-- For `k ≤ n` the generalized Reed–Solomon code has dimension `k`. -/
theorem finrank_grsCode (ha : Function.Injective a) (hv : ∀ i, v i ≠ 0) {k : ℕ}
    (hk : k ≤ Fintype.card ι) : Module.finrank F (grsCode a v k) = k := by
  rw [grsCode_def, ← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj,
    (degreeLTEquiv F k).finrank_eq, Module.finrank_fin_fun]
  exact fun p q hpq ↦ Subtype.ext (injOn_grsEval ha hv hk p.property q.property hpq)

/-- For `n ≤ k` the generalized Reed–Solomon code is the whole space, when the points are distinct
and the multipliers nonzero. -/
theorem grsCode_eq_top (ha : Function.Injective a) (hv : ∀ i, v i ≠ 0) {k : ℕ}
    (hk : Fintype.card ι ≤ k) : grsCode a v k = ⊤ := by
  have hn : grsCode a v (Fintype.card ι) = ⊤ := Submodule.eq_top_of_finrank_eq <| by
    rw [finrank_grsCode ha hv le_rfl, Module.finrank_fintype_fun_eq_card]
  rw [eq_top_iff, ← hn, grsCode_def, grsCode_def]
  exact Submodule.map_mono (degreeLT_mono hk)

/-- For `1 ≤ k ≤ n` every nonzero word of the generalized Reed–Solomon code has weight at least
`n - k + 1`, so its minimum distance is at least `n - k + 1`. -/
theorem le_hammingMinDist_grsCode [DecidableEq F] (ha : Function.Injective a)
    (hv : ∀ i, v i ≠ 0) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) :
    Fintype.card ι - k + 1 ≤ (grsCode a v k : Set (ι → F)).hammingMinDist := by
  -- The word of the constant polynomial `1` is a nonzero word of the code.
  have h1 : (1 : F[X]) ∈ degreeLT F k := mem_degreeLT.2 (by rw [degree_one]; exact_mod_cast hk)
  have hne : (grsCode a v k).toAddSubgroup ≠ ⊥ := fun h ↦ by
    have hmem := (Submodule.mem_toAddSubgroup _).2 (grsEval_mem_grsCode (a := a) (v := v) h1)
    rw [h, AddSubgroup.mem_bot] at hmem
    exact one_ne_zero (injOn_grsEval ha hv hkn h1 (zero_mem _) (hmem.trans (map_zero _).symm))
  refine (Set.le_hammingMinDist_iff_hammingNorm hne).2 fun x hx hx0 ↦ ?_
  obtain ⟨p, hp, rfl⟩ := mem_grsCode_iff.1 hx
  -- The word vanishes at fewer than `k` coordinates.
  have hz := card_filter_grsEval_eq_zero_lt ha hv hp fun h ↦ hx0 (by rw [h, map_zero])
  have hsum : Finset.card {i | grsEval a v p i = 0} + Finset.card {i | grsEval a v p i ≠ 0} =
      Fintype.card ι :=
    Finset.card_filter_add_card_filter_not (s := Finset.univ) _
  rw [hammingNorm]
  omega

end TauCeti
