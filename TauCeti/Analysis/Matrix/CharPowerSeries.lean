/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Restricted
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import TauCeti.Analysis.Matrix.Ultra
public import TauCeti.LinearAlgebra.Matrix.Minor

/-!
# Principal-minor series of infinite matrices

For a square matrix `A : Matrix ι ι R` over a commutative topological ring, indexed by an
arbitrary (possibly infinite) type `ι`, this file uses the principal minors
`A.principalMinor s = det (A i j)_{i, j ∈ s}` on finite sets `s` of indices
(`Matrix.principalMinor`) to define the coefficients

`A.charCoeff n = (-1) ^ n * ∑' s : {s : Finset ι // s.card = n}, A.principalMinor s`,

and the power series `A.charPowerSeries` with these coefficients. For a finite index type these
are exactly the coefficients of `det (1 - X A)`, Mathlib's `Matrix.charpolyRev`
(`Matrix.charCoeff_eq_coeff_charpolyRev`). For infinite index types the series is the
Fredholm determinant `det (1 - T A)` of Serre's theory of completely continuous endomorphisms
of nonarchimedean Banach spaces, once the defining sums are known to converge.

Over a complete ultrametric normed ring with `‖1‖ = 1`, convergence and growth are governed by
row bounds: if `‖A i j‖ ≤ r i` for all entries, then

* each principal minor is bounded by `∏ i ∈ s, r i` (`Matrix.norm_principalMinor_le`), and
  each coefficient by any common bound of those products (`Matrix.norm_charCoeff_le`);
* if `r` tends to zero along the cofinite filter, the principal minors of each size form a
  summable family (`Matrix.summable_principalMinor`);
* if `ρ * r i ≤ q ≤ 1` off a finite set `T` and `ρ * r i ≤ B` everywhere, with `1 ≤ B`, then
  `‖A.charCoeff n‖ * ρ ^ n ≤ B ^ #T * q ^ (n - #T)` (`Matrix.norm_charCoeff_mul_pow_le`);
* if `r` tends to zero along the cofinite filter, the series is restricted at every radius,
  that is, entire (`Matrix.isRestricted_charPowerSeries`).

The tail estimate depends on `A` only through `r`, so it is uniform over every family of matrices
sharing one row majorant. The coefficients do not depend on an enumeration of the index type
(`Matrix.charCoeff_submatrix_equiv`).

## Main definitions

* `Matrix.charCoeff`: the signed sum of the principal minors of a given size.
* `Matrix.charPowerSeries`: the power series with coefficients `Matrix.charCoeff`.

## Implementation notes

The coefficients are defined by an unconditional `tsum`, which is zero when the family is not
summable. Statements about their values that need convergence carry the corresponding row-decay
hypotheses; the norm bounds hold without them.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§4–5.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A.
-/

public section

open Filter Finset Polynomial Topology

namespace Matrix

variable {ι κ R : Type*} [DecidableEq ι] [DecidableEq κ]

section Defs

variable [CommRing R] [TopologicalSpace R]

/-- The `n`-th coefficient of the principal-minor series `det (1 - T A)`: `(-1) ^ n` times the
sum of the principal minors of size `n`. The sum is an unconditional `tsum`, so it is only
meaningful once the family of minors is summable (`Matrix.summable_principalMinor`). -/
noncomputable def charCoeff (A : Matrix ι ι R) (n : ℕ) : R :=
  (-1) ^ n * ∑' s : {s : Finset ι // s.card = n}, A.principalMinor s

theorem charCoeff_def (A : Matrix ι ι R) (n : ℕ) :
    A.charCoeff n = (-1) ^ n * ∑' s : {s : Finset ι // s.card = n}, A.principalMinor s :=
  (rfl)

@[simp]
theorem charCoeff_zero (A : Matrix ι ι R) : A.charCoeff 0 = 1 := by
  rw [charCoeff_def, tsum_eq_single ⟨∅, card_empty⟩ fun s hs ↦
    (hs (Subtype.ext (card_eq_zero.mp s.2))).elim]
  simp

/-- The coefficients of the principal-minor series do not depend on the enumeration of the
index type. -/
theorem charCoeff_submatrix_equiv (A : Matrix κ κ R) (e : ι ≃ κ) (n : ℕ) :
    (A.submatrix e e).charCoeff n = A.charCoeff n := by
  rw [charCoeff_def, charCoeff_def]
  congr 1
  let E : {s : Finset ι // s.card = n} ≃ {t : Finset κ // t.card = n} :=
    e.finsetCongr.subtypeEquiv fun s ↦ by simp
  rw [← E.tsum_eq]
  exact tsum_congr fun s ↦ by simp [E, principalMinor_submatrix_equiv]

/-- The principal-minor series `det (1 - T A)`, whose coefficients are `Matrix.charCoeff`. -/
noncomputable def charPowerSeries (A : Matrix ι ι R) : PowerSeries R :=
  PowerSeries.mk A.charCoeff

@[simp]
theorem coeff_charPowerSeries (A : Matrix ι ι R) (n : ℕ) :
    PowerSeries.coeff n A.charPowerSeries = A.charCoeff n := by
  rw [charPowerSeries, PowerSeries.coeff_mk]

@[simp]
theorem constantCoeff_charPowerSeries (A : Matrix ι ι R) :
    PowerSeries.constantCoeff A.charPowerSeries = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_charPowerSeries, charCoeff_zero]

/-- The principal-minor series does not depend on the enumeration of the index type. -/
theorem charPowerSeries_submatrix_equiv (A : Matrix κ κ R) (e : ι ≃ κ) :
    (A.submatrix e e).charPowerSeries = A.charPowerSeries := by
  ext n
  simp [charCoeff_submatrix_equiv]

section Fintype

variable [Fintype ι]

/-- For a finite index type, the coefficients of the principal-minor series are those of
`det (1 - X A)`. -/
theorem charCoeff_eq_coeff_charpolyRev (A : Matrix ι ι R) (n : ℕ) :
    A.charCoeff n = A.charpolyRev.coeff n := by
  rw [charCoeff_def, coeff_charpolyRev, tsum_fintype]
  simp only [← principalMinor_def]
  congr 1
  exact (sum_subtype _ (fun s ↦ by simp) fun s ↦ A.principalMinor s).symm

/-- For a finite index type, the principal-minor series is the polynomial `det (1 - X A)`. -/
theorem charPowerSeries_eq_charpolyRev (A : Matrix ι ι R) :
    A.charPowerSeries = (A.charpolyRev : PowerSeries R) := by
  ext n
  rw [coeff_charPowerSeries, charCoeff_eq_coeff_charpolyRev, Polynomial.coeff_coe]

end Fintype

@[simp]
theorem charPowerSeries_of_isEmpty [IsEmpty ι] (A : Matrix ι ι R) : A.charPowerSeries = 1 := by
  let _ : Fintype ι := Fintype.ofIsEmpty
  rw [charPowerSeries_eq_charpolyRev, charpolyRev_isEmpty, Polynomial.coe_one]

end Defs

section Ultra

variable [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]

/-- **Coefficient bound.** If `r` bounds the rows of `A` and `C ≥ 0` bounds `∏ i ∈ s, r i` for
every `n`-element set `s`, then `C` bounds the `n`-th coefficient of the principal-minor
series. No convergence hypothesis is needed. -/
theorem norm_charCoeff_le {A : Matrix ι ι R} {r : ι → ℝ} (hA : ∀ i j, ‖A i j‖ ≤ r i) {n : ℕ}
    {C : ℝ} (hC : 0 ≤ C) (hs : ∀ s : Finset ι, s.card = n → ∏ i ∈ s, r i ≤ C) :
    ‖A.charCoeff n‖ ≤ C := by
  have hsum : ‖∑' s : {s : Finset ι // s.card = n}, A.principalMinor s‖ ≤ C :=
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC fun s ↦
      (norm_principalMinor_le hA s).trans (hs s s.2)
  rw [charCoeff_def]
  rcases neg_one_pow_eq_or R n with hn | hn <;> simpa [hn] using hsum

/-- **Summability of principal minors.** Over a complete ultrametric normed ring with
`‖1‖ = 1`, if the rows of `A` are bounded by a family `r` tending to zero along the cofinite
filter, then the principal minors of each fixed size form a summable family. -/
theorem summable_principalMinor [CompleteSpace R] {A : Matrix ι ι R} {r : ι → ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ r i) (hr : Tendsto r cofinite (𝓝 0)) (n : ℕ) :
    Summable fun s : {s : Finset ι // s.card = n} ↦ A.principalMinor s := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun s ↦ norm_principalMinor_le hA s) ?_
  have hr₀ : ∀ i, 0 ≤ r i := fun i ↦ (norm_nonneg _).trans (hA i i)
  obtain ⟨M, hM⟩ := hr.bddAbove_range_of_cofinite
  set M' := max 1 M
  have hM' : 1 ≤ M' := le_max_left _ _
  have hM'₀ : 0 < M' ^ n := pow_pos (zero_lt_one.trans_le hM') n
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / M' ^ n := div_pos hε hM'₀
  -- The indices with a row bound at least `ε / M' ^ n` form a finite set `F`.
  have hF : {i | ¬r i < ε / M' ^ n}.Finite :=
    eventually_cofinite.mp (hr.eventually (gt_mem_nhds hδ))
  -- A size-`n` product of row bounds that is at least `ε` only involves indices in `F`.
  refine eventually_cofinite.mpr <|
    ((hF.toFinset.powerset.finite_toSet).preimage Subtype.val_injective.injOn).subset ?_
  intro s hs
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, not_lt] at hs
  simp only [Set.mem_preimage, coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset]
  intro i hi
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  intro hri
  have herase : ∏ j ∈ s.1.erase i, r j ≤ M' ^ n := by
    calc ∏ j ∈ s.1.erase i, r j ≤ ∏ _j ∈ s.1.erase i, M' :=
          prod_le_prod₀ (fun j _ ↦ hr₀ j) fun j _ ↦ (hM ⟨j, rfl⟩).trans (le_max_right _ _)
      _ = M' ^ (s.1.erase i).card := prod_const M'
      _ ≤ M' ^ n := pow_le_pow_right₀ hM' (card_erase_le.trans s.2.le)
  have hprod : ∏ j ∈ s.1, r j < ε := by
    calc ∏ j ∈ s.1, r j = r i * ∏ j ∈ s.1.erase i, r j := (mul_prod_erase _ _ hi).symm
      _ ≤ r i * M' ^ n := mul_le_mul_of_nonneg_left herase (hr₀ i)
      _ < ε / M' ^ n * M' ^ n := mul_lt_mul_of_pos_right hri hM'₀
      _ = ε := div_mul_cancel₀ ε hM'₀.ne'
  rw [abs_of_nonneg (prod_nonneg fun j _ ↦ hr₀ j)] at hs
  exact hs.not_gt hprod

/-- **Uniform tail bound.** Suppose `r` bounds the rows of `A`, and let `ρ > 0`, `0 ≤ q ≤ 1`,
`1 ≤ B`, and `T` a finite set of indices with `ρ * r i ≤ q` off `T` and `ρ * r i ≤ B`
everywhere. Then `‖A.charCoeff n‖ * ρ ^ n ≤ B ^ #T * q ^ (n - #T)`, with truncated subtraction
in the exponent. The bound depends on `A` only through `r`. -/
theorem norm_charCoeff_mul_pow_le {A : Matrix ι ι R} {r : ι → ℝ} (hA : ∀ i j, ‖A i j‖ ≤ r i)
    {ρ q B : ℝ} (hρ : 0 < ρ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hB : 1 ≤ B) (T : Finset ι)
    (hT : ∀ i ∉ T, ρ * r i ≤ q) (hrB : ∀ i, ρ * r i ≤ B) (n : ℕ) :
    ‖A.charCoeff n‖ * ρ ^ n ≤ B ^ T.card * q ^ (n - T.card) := by
  have hr₀ : ∀ i, 0 ≤ ρ * r i := fun i ↦ mul_nonneg hρ.le ((norm_nonneg _).trans (hA i i))
  have hρn : 0 < ρ ^ n := pow_pos hρ n
  rw [← le_div_iff₀ hρn]
  refine norm_charCoeff_le hA (div_nonneg (mul_nonneg (pow_nonneg (by linarith) _)
    (pow_nonneg hq₀ _)) hρn.le) fun s hs ↦ ?_
  rw [le_div_iff₀ hρn, ← hs, ← prod_const ρ, ← prod_mul_distrib,
    ← prod_filter_mul_prod_filter_not s (· ∈ T)]
  have hcard := card_filter_add_card_filter_not (s := s) (· ∈ T)
  have hTcard : (s.filter (· ∈ T)).card ≤ T.card :=
    card_le_card fun i hi ↦ (mem_filter.mp hi).2
  refine mul_le_mul ?_ ?_ (prod_nonneg fun i _ ↦ by simpa [mul_comm] using hr₀ i)
    (pow_nonneg (by linarith) _)
  · calc ∏ i ∈ s.filter (· ∈ T), r i * ρ ≤ ∏ _i ∈ s.filter (· ∈ T), B :=
          prod_le_prod₀ (fun i _ ↦ by simpa [mul_comm] using hr₀ i)
            fun i _ ↦ by simpa [mul_comm] using hrB i
      _ = B ^ (s.filter (· ∈ T)).card := prod_const B
      _ ≤ B ^ T.card := pow_le_pow_right₀ hB hTcard
  · calc ∏ i ∈ s.filter (· ∉ T), r i * ρ ≤ ∏ _i ∈ s.filter (· ∉ T), q :=
          prod_le_prod₀ (fun i _ ↦ by simpa [mul_comm] using hr₀ i)
            fun i hi ↦ by simpa [mul_comm] using hT i (mem_filter.mp hi).2
      _ = q ^ (s.filter (· ∉ T)).card := prod_const q
      _ ≤ q ^ (s.card - T.card) := pow_le_pow_of_le_one hq₀ hq₁ (by omega)

/-- **Entirety.** If the rows of `A` are bounded by a family tending to zero along the cofinite
filter, then the principal-minor series is restricted at every radius. -/
theorem isRestricted_charPowerSeries {A : Matrix ι ι R} {r : ι → ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ r i) (hr : Tendsto r cofinite (𝓝 0)) (c : ℝ) :
    A.charPowerSeries.IsRestricted c := by
  rw [← PowerSeries.isRestricted_abs_iff, PowerSeries.isRestricted_iff']
  set ρ := |c| + 1
  have hρ : 0 < ρ := by positivity
  obtain ⟨M, hM⟩ := hr.bddAbove_range_of_cofinite
  -- Off the finite set `T`, the rescaled row bounds are at most `1 / 2`.
  have hT : {i | ¬ρ * r i ≤ 1 / 2}.Finite := by
    refine eventually_cofinite.mp ?_
    have h := (hr.const_mul ρ).eventually (gt_mem_nhds (by norm_num : ρ * 0 < 1 / 2))
    exact h.mono fun _ hi ↦ hi.le
  set T := hT.toFinset
  set B := max 1 (ρ * M)
  have hbound (n : ℕ) : ‖A.charCoeff n‖ * ρ ^ n ≤ B ^ T.card * (1 / 2) ^ (n - T.card) :=
    norm_charCoeff_mul_pow_le hA hρ (by norm_num) (by norm_num) (le_max_left _ _) T
      (fun i hi ↦ by simpa [T] using hi)
      (fun i ↦ (mul_le_mul_of_nonneg_left (hM ⟨i, rfl⟩) hρ.le).trans (le_max_right _ _)) n
  have hlim : Tendsto (fun n : ℕ ↦ B ^ T.card * (1 / 2 : ℝ) ^ (n - T.card)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).comp (tendsto_sub_atTop_nat T.card)).const_mul (B ^ T.card)
  refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) hlim
  rw [coeff_charPowerSeries]
  refine le_trans ?_ (hbound n)
  gcongr
  linarith

end Ultra

end Matrix
