/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.ApproxProd
public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Volume
public import TauCeti.RingTheory.DedekindDomain.SInteger.Primitive

import TauCeti.NumberTheory.Height.Primitive
import TauCeti.NumberTheory.NumberField.Global.Places.Height
import TauCeti.NumberTheory.NumberField.SUnits.AffineHeight

/-!
# Finitely many classes of approximation domains

Let `K` be a number field, `S₀` a finite set of finite places of `K`, and `L v i` linear forms on
`ι → K` at the infinite places and the places of `S₀`. Schmidt's proof of the Subspace Theorem
sorts the solutions `x` of

`approxProd univ S₀ id L x ≤ mulHeight x ^ (-card ι - ε)`

into finitely many classes, each described by an approximation domain. This file proves that
sorting (`TauCeti.NumberField.exists_finset_forall_exists_smul_mem_approxDomain`): there are
finitely many exponent families `c`, each of weight `approxWeight S₀ c ≤ -ε / 2`, such that every
`S₀`-primitive solution of large height at which no form vanishes has an `S₀`-unit multiple in
`approxDomain S₀ L c (mulHeight x)` for one of them.

The proof normalizes `x` by an `S₀`-unit `u` so that every value `L v i (u • x)` has logarithmic
height at most `log H + C`, where `H = mulHeight x`
(`TauCeti.NumberField.exists_forall_logHeight₁_apply_smul_le`). By Liouville's inequality at a
single place the exponents `log |L v i (u • x)|_v / log H` then lie in `[-2, 2]` once
`log H ≥ C`. Rounding them up to the grid `ℤ / N` gives an exponent family with
`|L v i (u • x)|_v ≤ H ^ c v i`, taken from a finite set. The exact exponents have weight
`log (approxProd … x * H ^ card ι) / log H ≤ -ε`, because the local sup norms of the primitive
point `u • x` multiply to `H`, and rounding raises the weight by at most `ε / 2` once the mesh
`1 / N` is small. The exponents have both signs, so the classes are the cells of side `1 / N` of
the cube `[-2, 2]`, not the cells of the simplex labelled by `TauCeti.cellIndex`, which truncates
negative coordinates to `0`. Their number grows with the number of places.

Solutions at which some form vanishes are excluded: they lie in the kernel of that form.

## Main results

* `TauCeti.NumberField.exists_finset_forall_exists_smul_mem_approxDomain`: the solutions of the
  inequality of the Subspace Theorem fall into finitely many approximation domains of weight at
  most `-ε / 2`, after normalization by an `S₀`-unit.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  7.5.6 and Corollary 7.5.5.
-/

public section

open Finset Height IsDedekindDomain Module Real

namespace TauCeti.NumberField

variable {ι : Type*}

/-! ### Rounding exponents up to a grid -/

/-- The exponent families on the grid `ℤ / N` with entries in `[-2, 2]` on `P` and `0` off `P`,
indexed by the integer numerators. -/
private noncomputable def gridExponent {α : Type*} (P : Set α) (N : ℕ)
    (g : P → ι → Finset.Icc (-(2 * N : ℤ)) (2 * N)) : α → ι → ℝ :=
  open Classical in fun v i ↦ if h : v ∈ P then ((g ⟨v, h⟩ i : ℤ) : ℝ) / N else 0

/-- Rounding up to the grid `ℤ / N`: an exponent family with entries in `[-2, 2]` on `P` lies
below a grid family which exceeds it by at most `1 / N` on `P`. -/
private theorem exists_le_gridExponent {α : Type*} {P : Set α} {N : ℕ} (hN : 0 < N)
    {a : α → ι → ℝ} (ha : ∀ v ∈ P, ∀ i, |a v i| ≤ 2) :
    ∃ g, ∀ v ∈ P, ∀ i, a v i ≤ gridExponent P N g v i ∧
      gridExponent P N g v i ≤ a v i + 1 / N := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNa (v : P) (i : ι) : |(N : ℝ) * a v i| ≤ 2 * N := by
    rw [abs_mul, Nat.abs_cast, mul_comm (2 : ℝ)]
    exact mul_le_mul_of_nonneg_left (ha v v.2 i) hNpos.le
  refine ⟨fun v i ↦ ⟨⌈N * a v i⌉, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩, fun v hv i ↦ ?_⟩
  · have h := (abs_le.mp (hNa v i)).1
    have h' := Int.le_ceil ((N : ℝ) * a v i)
    exact_mod_cast (show ((-(2 * N : ℤ) : ℤ) : ℝ) ≤ ⌈(N : ℝ) * a v i⌉ by push_cast; linarith)
  · exact Int.ceil_le.mpr (by push_cast; linarith [(abs_le.mp (hNa v i)).2])
  · simp only [gridExponent, hv, dite_true]
    rw [le_div_iff₀ hNpos, div_le_iff₀ hNpos, add_mul, one_div_mul_cancel hNpos.ne', mul_comm]
    exact ⟨Int.le_ceil _, (Int.ceil_lt_add_one _).le⟩

/-! ### The classes of solutions -/

variable {K : Type*} [Field K] [NumberField K] [Fintype ι]

open _root_.NumberField

/-- At the absolute value of a place of `K`, the logarithm of an element is at most its
logarithmic height in absolute value. -/
private theorem abs_log_le_logHeight₁_of_mem {v : AbsoluteValue K ℝ}
    (hv : v ∈ Set.range (fun w : InfinitePlace K ↦ w.1) ∪ Set.range fun w : FinitePlace K ↦ w.1)
    (y : K) : |log (v y)| ≤ logHeight₁ y := by
  rcases hv with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · refine le_trans ?_ (InfinitePlace.abs_mult_mul_log_le_logHeight₁ w y)
    rw [abs_mul, InfinitePlace.coe_apply]
    exact le_mul_of_one_le_left (abs_nonneg _) (by simp [w.one_le_mult])
  · exact FinitePlace.abs_log_le_logHeight₁ w y

/-- The values of a family of linear forms at a point whose local sup norms over the infinite
places and `S₀` multiply to `H`: their product, weighted as in `approxProd`, is
`approxProd univ S₀ id L x * H ^ card ι`. -/
private theorem prod_apply_eq_approxProd_mul (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) {x : ι → K} (hx : x ≠ 0) {H : ℝ}
    (hH : H = (∏ v : InfinitePlace K, (⨆ j, v (x j)) ^ v.mult) * ∏ v ∈ S₀, ⨆ j, v (x j)) :
    (∏ v : InfinitePlace K, (∏ i, v.1 (L v.1 i x)) ^ v.mult) * ∏ v ∈ S₀, ∏ i, v.1 (L v.1 i x) =
      approxProd univ S₀ id L x * H ^ Fintype.card ι := by
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hx
  -- at every absolute value, the local factor times the `card ι`-th power of the local sup norm
  -- of the nonzero point `x` is the product of the values of the forms
  have hloc (v : AbsoluteValue K ℝ) (l : ι → Dual K (ι → K)) :
      (∏ i, v (l i x) / ⨆ j, v (x j)) * (⨆ j, v (x j)) ^ Fintype.card ι = ∏ i, v (l i x) := by
    have hpos : 0 < ⨆ j, v (x j) := (v.pos hj₀).trans_le (Finite.le_ciSup (fun j ↦ v (x j)) j₀)
    rw [prod_div_distrib, prod_const, card_univ, div_mul_cancel₀ _ (pow_ne_zero _ hpos.ne')]
  simp only [approxProd_def, id_eq, Algebra.algebraMap_self, RingHom.id_apply,
    InfinitePlace.coe_apply, FinitePlace.coe_apply] at hH ⊢
  rw [hH, mul_pow, ← prod_pow, ← prod_pow, mul_mul_mul_comm, ← prod_mul_distrib,
    ← prod_mul_distrib]
  congr 1
  · refine prod_congr rfl fun v _ ↦ ?_
    rw [pow_right_comm, ← mul_pow]
    exact congrArg (· ^ v.mult) (hloc v.1 (L v.1)).symm
  · exact prod_congr rfl fun v _ ↦ (hloc v.1 (L v.1)).symm

/-- **The exact exponents of a solution.** Let `y` be a point whose local sup norms over the
infinite places and `S₀` multiply to `H > 1`, and at which no form vanishes. The exponents
`logb H |L v i y|_v` have weight at most `-ε` as soon as
`approxProd univ S₀ id L y ≤ H ^ (-card ι - ε)`. -/
private theorem approxWeight_logb_le (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) {y : ι → K} (hy : y ≠ 0) {H ε : ℝ}
    (hH1 : 1 < H)
    (hH : H = (∏ v : InfinitePlace K, (⨆ j, v (y j)) ^ v.mult) * ∏ v ∈ S₀, ⨆ j, v (y j))
    (hLinf : ∀ (v : InfinitePlace K) (i : ι), L v.1 i y ≠ 0) (hLfin : ∀ v ∈ S₀, ∀ i, L v.1 i y ≠ 0)
    (happrox : approxProd univ S₀ id L y ≤ H ^ (-(Fintype.card ι : ℝ) - ε)) :
    approxWeight S₀ (fun v i ↦ logb H (v (L v i y))) ≤ -ε := by
  have hHpos : 0 < H := zero_lt_one.trans hH1
  have hrpow {v : AbsoluteValue K ℝ} {i : ι} (h : L v i y ≠ 0) :
      H ^ logb H (v (L v i y)) = v (L v i y) :=
    rpow_logb hHpos hH1.ne' (v.pos h)
  rw [← rpow_le_rpow_left_iff hH1, rpow_approxWeight S₀ _ hHpos,
    prod_congr rfl fun v _ ↦ congrArg (· ^ v.mult) (prod_congr rfl fun i _ ↦ hrpow (hLinf v i)),
    prod_congr rfl fun v hv ↦ prod_congr rfl fun i _ ↦ hrpow (hLfin v hv i),
    prod_apply_eq_approxProd_mul S₀ L hy hH]
  calc approxProd univ S₀ id L y * H ^ Fintype.card ι
      ≤ H ^ (-(Fintype.card ι : ℝ) - ε) * H ^ (Fintype.card ι : ℝ) := by
        rw [rpow_natCast]
        exact mul_le_mul_of_nonneg_right happrox (by positivity)
    _ = H ^ (-ε) := by rw [← rpow_add hHpos]; ring_nf

/-- **The solutions of the inequality of the Subspace Theorem fall into finitely many
approximation domains** (Bombieri–Gubler 7.5.6). Let `L v i` be linear forms at the infinite
places and the places of `S₀`, and `ε > 0`. There are finitely many exponent families `c`, each of
weight `approxWeight S₀ c ≤ -ε / 2`, and a level `Q₀`, such that every `S₀`-primitive `x` with
`Q₀ ≤ mulHeight x`, at which no form vanishes and with
`approxProd univ S₀ id L x ≤ mulHeight x ^ (-card ι - ε)`, has an `S₀`-unit multiple `u • x` in
`approxDomain S₀ L c (mulHeight x)` for one of these `c`.

The `S₀`-units and `S₀`-primitivity refer to the height one primes `FinitePlace.maximalIdeal v`
of the places `v ∈ S₀`. -/
theorem exists_finset_forall_exists_smul_mem_approxDomain (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (T : Finset (AbsoluteValue K ℝ → ι → ℝ)) (Q₀ : ℝ),
      (∀ c ∈ T, approxWeight S₀ c ≤ -(ε / 2)) ∧
      ∀ x : ι → K, (FinitePlace.maximalIdeal '' (S₀ : Set (FinitePlace K))).IsPrimitive x →
        Q₀ ≤ mulHeight x → (∀ (v : InfinitePlace K) (i : ι), L v.1 i x ≠ 0) →
        (∀ v ∈ S₀, ∀ i, L v.1 i x ≠ 0) →
        approxProd univ S₀ id L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ u : (FinitePlace.maximalIdeal '' (S₀ : Set (FinitePlace K))).unit K, ∃ c ∈ T,
          ((u : Kˣ) : K) • x ∈ approxDomain S₀ L c (mulHeight x) := by
  -- the places of `S₀` as height one primes
  have hS : FinitePlace.maximalIdeal '' (S₀ : Set (FinitePlace K)) =
      ↑(S₀.map FinitePlace.equivHeightOneSpectrum.toEmbedding) := by
    simp
  rw [hS]
  set S := S₀.map FinitePlace.equivHeightOneSpectrum.toEmbedding
  -- the absolute values carrying forms
  set P : Set (AbsoluteValue K ℝ) :=
    Set.range (fun v : InfinitePlace K ↦ v.1) ∪ (fun v : FinitePlace K ↦ v.1) '' S₀
  have : Finite P := ((Set.finite_range _).union (S₀.finite_toSet.image _)).to_subtype
  have hinf (v : InfinitePlace K) : v.1 ∈ P := Or.inl ⟨v, rfl⟩
  have hfin {v : FinitePlace K} (hv : v ∈ S₀) : v.1 ∈ P := Or.inr ⟨v, hv, rfl⟩
  -- the normalizing unit makes every value of a form of logarithmic height `≤ log H + C`
  obtain ⟨C, hC⟩ := exists_forall_logHeight₁_apply_smul_le S (κ := P × ι) fun k ↦ L k.1.1 k.2
  -- the mesh `1 / N` of the grid
  set W := approxWeight S₀ (fun (_ : AbsoluteValue K ℝ) (_ : ι) ↦ (1 : ℝ)) with hW
  have hW0 : 0 ≤ W := approxWeight_nonneg (fun _ _ ↦ zero_le_one) fun _ _ _ ↦ zero_le_one
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * W / ε)
  have hNpos : (0 : ℝ) < N := (div_nonneg (by positivity) hε.le).trans_lt hN
  classical
  refine ⟨(Set.finite_range (gridExponent P N)).toFinset.filter
    fun c ↦ approxWeight S₀ c ≤ -(ε / 2), exp (max C 1), fun c hc ↦ (mem_filter.mp hc).2, ?_⟩
  intro x hx hQ hLinf hLfin happrox
  obtain ⟨u, -, hu⟩ := hC x hx
  set y := ((u : Kˣ) : K) • x with hy
  set H := mulHeight x with hHdef
  have hlogH : max C 1 ≤ log H := by
    rw [← log_exp (max C 1)]
    exact log_le_log (exp_pos _) hQ
  have hlogHpos : 0 < log H := zero_lt_one.trans_le ((le_max_right _ _).trans hlogH)
  have hH1 : 1 < H := (one_lt_exp_iff.mpr hlogHpos).trans_eq (exp_log (mulHeight_pos x))
  have hu0 : ((u : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have hprim : (S : Set (HeightOneSpectrum (𝓞 K))).IsPrimitive y := hx.unit_smul u
  have hLy {v : AbsoluteValue K ℝ} {i : ι} (h : L v i x ≠ 0) : L v i y ≠ 0 := by
    simpa [hy, hu0] using h
  -- the exact exponents `logb H |L v i y|_v` lie in `[-2, 2]` and have weight `≤ -ε`
  set a : AbsoluteValue K ℝ → ι → ℝ := fun v i ↦ logb H (v (L v i y)) with ha_def
  have ha2 : ∀ v ∈ P, ∀ i, |a v i| ≤ 2 := by
    intro v hv i
    have h1 : logHeight₁ (L v i y) ≤ log H + C := hu (⟨v, hv⟩, i)
    have h2 := abs_log_le_logHeight₁_of_mem
      (hv.imp id fun ⟨w, _, hw⟩ ↦ ⟨w, hw⟩) (L v i y)
    simp only [ha_def, ← log_div_log, abs_div, abs_of_pos hlogHpos]
    rw [div_le_iff₀ hlogHpos]
    linarith [le_max_left C 1]
  have hwa : approxWeight S₀ a ≤ -ε := by
    refine approxWeight_logb_le S₀ L hprim.ne_zero hH1 ?_ (fun v i ↦ hLy (hLinf v i))
      (fun v hv i ↦ hLy (hLfin v hv i)) ?_
    · rw [hHdef, ← mulHeight_smul_eq_mulHeight x hu0]
      exact mulHeight_eq_prod_of_isPrimitive_image_maximalIdeal S₀ (by rwa [hS])
    · rwa [approxProd_smul (fun _ _ ↦ ⟨by ext; simp⟩) (fun _ _ ↦ ⟨by ext; simp⟩) hu0 x]
  -- rounding up to the grid raises the weight by at most `ε / 2`
  obtain ⟨g, hg⟩ := exists_le_gridExponent (Nat.cast_pos.mp hNpos) ha2
  have hwc : approxWeight S₀ (gridExponent P N g) ≤ -(ε / 2) := by
    have h := approxWeight_mono (S₀ := S₀) (c₁ := gridExponent P N g)
      (c₂ := a + (1 / (N : ℝ)) • fun _ _ ↦ 1)
      (fun v i ↦ by simpa using (hg v.1 (hinf v) i).2)
      fun v hv i ↦ by simpa using (hg v.1 (hfin hv) i).2
    rw [approxWeight_add, approxWeight_smul, ← hW] at h
    rw [div_lt_iff₀ hε] at hN
    have hWN : 1 / (N : ℝ) * W ≤ ε / 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hNpos]
      linarith
    linarith
  refine ⟨u, gridExponent P N g, by simp [hwc], ?_⟩
  -- membership in the approximation domain: `|L v i y|_v = H ^ a v i ≤ H ^ c v i`
  have hval {v : AbsoluteValue K ℝ} (hv : v ∈ P) {i : ι} (h : L v i x ≠ 0) :
      v (L v i y) ≤ H ^ gridExponent P N g v i := by
    calc v (L v i y) = H ^ a v i := (rpow_logb (zero_lt_one.trans hH1) hH1.ne' (v.pos (hLy h))).symm
      _ ≤ H ^ gridExponent P N g v i := rpow_le_rpow_of_exponent_le hH1.le (hg v hv i).1
  refine mem_approxDomain.mpr ⟨fun v i ↦ hval (hinf v) (hLinf v i),
    fun v hv i ↦ hval (hfin hv) (hLfin v hv i), fun v hv j ↦ ?_⟩
  -- at a finite place outside `S₀` the primitive point `y` has local sup norm `1`
  have hvS : v.maximalIdeal ∉ (S : Set (HeightOneSpectrum (𝓞 K))) := by
    rwa [← hS, FinitePlace.maximalIdeal_injective.mem_set_image]
  have h := (Set.isPrimitive_iff_finitePlace _ hprim.ne_zero).mp hprim _ hvS
  rw [FinitePlace.mk_maximalIdeal] at h
  exact h ▸ Finite.le_ciSup (fun j ↦ v (y j)) j

end TauCeti.NumberField
