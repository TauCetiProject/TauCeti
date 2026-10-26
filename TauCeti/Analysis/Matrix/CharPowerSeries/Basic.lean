/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Restricted
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import TauCeti.Analysis.Matrix.Ultra
public import TauCeti.Analysis.SpecificLimits.ProductMajorant
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

Over an ultrametric seminormed commutative ring, a product majorant
`‖A.principalMinor s‖ ≤ ∏ i ∈ s, r i` controls convergence and growth:

* any common nonnegative bound on the size-`n` principal minors bounds the coefficient
  (`Matrix.norm_charCoeff_le_of_principalMinor_le`);
* if `r` tends to zero along the cofinite filter and the ring is complete, the principal
  minors of each size form a summable family (`Matrix.summable_principalMinor_of_le_prod`);
* if `ρ * r i ≤ q ≤ 1` off a finite set `T` and `ρ * r i ≤ B` everywhere, with `ρ > 0`,
  `0 ≤ q` and `1 ≤ B`, then `‖A.charCoeff n‖ * ρ ^ n ≤ B ^ #T * q ^ (n - #T)`
  (`Matrix.norm_charCoeff_mul_pow_le_of_le_prod`);
* if `r` tends to zero along the cofinite filter and the ring is normed, the series is
  restricted at every radius, that is, entire (`Matrix.isRestricted_charPowerSeries_of_le_prod`).

The last two estimates depend on the coefficients only through the bound
`‖A.charCoeff n‖ ≤ c` for every nonnegative bound `c` of the `n`-fold products of `r`. They are
instances of the real estimates `TauCeti.mul_pow_le_of_forall_prod_le` and
`TauCeti.tendsto_mul_pow_of_forall_prod_le`, which assume only that bound and so apply equally
to the coefficients of the Fredholm resolvent.

Only summability requires completeness; none of these estimates requires `‖1‖ = 1`.
Over an ultrametric normed commutative ring with `‖1‖ = 1`, row bounds `‖A i j‖ ≤ r i`
supply the product majorant (`Matrix.norm_principalMinor_le`). They give the row-bound
corollaries `Matrix.norm_charCoeff_le`, `Matrix.summable_principalMinor`,
`Matrix.norm_charCoeff_mul_pow_le`, and `Matrix.isRestricted_charPowerSeries`.

The tail estimate depends on `A` only through `r`, so it is uniform over every family of matrices
sharing one product majorant. The coefficients do not depend on an enumeration of the index type
(`Matrix.charCoeff_submatrix_equiv`).

The series is compatible with the operations on matrices that act on each principal minor:

* it is unchanged by transposition (`Matrix.charPowerSeries_transpose`);
* it is unchanged by restriction to the range of an embedding of index types when the rows, or
  the columns, outside that range vanish, that is, under extension by zero
  (`Matrix.charPowerSeries_submatrix_of_row_eq_zero`,
  `Matrix.charPowerSeries_submatrix_of_col_eq_zero`);
* when the principal minors of `A` are summable, a continuous ring morphism `f` carries it to
  the series of `A.map f` (`Matrix.charPowerSeries_map`), and the series of `c • A` is that of
  `A` with the variable scaled by `c`, `det (1 - T (c • A)) = det (1 - (c T) A)`
  (`Matrix.charPowerSeries_smul`).

The product-majorant results `Matrix.summable_principalMinor_of_le_prod` and
`Matrix.isRestricted_charPowerSeries_of_le_prod` only require bounds on principal minors.
They also apply to two-sided entry bounds whose diagonal products tend to zero, even
when the rows themselves do not decay.

The summability hypotheses in `Matrix.charPowerSeries_map` and
`Matrix.charPowerSeries_smul` are needed because the coefficients are unconditional sums: the
image of a non-summable family of minors may be summable with a nonzero
sum. The scaling identities require only continuity of multiplication by each fixed scalar.

## Main definitions

* `Matrix.charCoeff`: the signed sum of the principal minors of a given size.
* `Matrix.charPowerSeries`: the power series with coefficients `Matrix.charCoeff`.

## Implementation notes

The coefficients are defined by an unconditional `tsum`, which is zero when the family is not
summable. Statements about their values that need convergence carry the corresponding row-decay
or product-majorant hypotheses; the norm bounds hold without them.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§4–5.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A.
-/

public section

open Filter Finset Polynomial Topology

namespace TauCeti

private theorem nonneg_of_norm_principalMinor_le_prod {ι R : Type*} [DecidableEq ι]
    [SeminormedCommRing R] {A : Matrix ι ι R} {r : ι → ℝ}
    (hA : ∀ s : Finset ι, ‖A.principalMinor s‖ ≤ ∏ i ∈ s, r i) (i : ι) : 0 ≤ r i := by
  simpa only [prod_singleton] using (norm_nonneg _).trans (hA {i})

end TauCeti

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

/-- **Extension by zero.** If every row of `A` outside the range of an embedding `e` vanishes,
for instance if `A` extends a matrix on `ι` by zero, then restricting `A` along `e` does not
change the coefficients of its principal-minor series. No convergence hypothesis is needed. -/
theorem charCoeff_submatrix_of_row_eq_zero (A : Matrix κ κ R) (e : ι ↪ κ)
    (hA : ∀ i ∉ Set.range e, ∀ j, A i j = 0) (n : ℕ) :
    (A.submatrix e e).charCoeff n = A.charCoeff n := by
  rw [charCoeff_def, charCoeff_def]
  congr 1
  let g : {s : Finset ι // s.card = n} → {t : Finset κ // t.card = n} :=
    fun s ↦ ⟨s.1.map e, by rw [card_map, s.2]⟩
  have hg : Function.Injective g := fun s t h ↦
    Subtype.ext (Finset.map_injective e (congrArg Subtype.val h))
  refine (tsum_congr fun s : {s : Finset ι // s.card = n} ↦
    principalMinor_submatrix A e s.1).trans (hg.tsum_eq (f := fun t ↦ A.principalMinor t.1) ?_)
  intro t ht
  -- A nonzero principal minor only involves indices in the range of `e`.
  have hrange (i : κ) (hi : i ∈ t.1) : i ∈ Set.range e := by_contra fun hi' ↦
    ht (principalMinor_eq_zero_of_row_eq_zero hi fun j _ ↦ hA i hi' j)
  have hmap : (t.1.preimage e e.injective.injOn).map e = t.1 := by
    classical
    rw [map_eq_image, image_preimage, filter_true_of_mem hrange]
  exact ⟨⟨t.1.preimage e e.injective.injOn, by rw [← card_map e, hmap, t.2]⟩, Subtype.ext hmap⟩

/-- The coefficients of the principal-minor series do not depend on the enumeration of the
index type. -/
theorem charCoeff_submatrix_equiv (A : Matrix κ κ R) (e : ι ≃ κ) (n : ℕ) :
    (A.submatrix e e).charCoeff n = A.charCoeff n :=
  charCoeff_submatrix_of_row_eq_zero A e.toEmbedding
    (fun i hi ↦ (hi (e.surjective i)).elim) n

/-- The coefficients of the principal-minor series are unchanged by transposition. -/
@[simp]
theorem charCoeff_transpose (A : Matrix ι ι R) (n : ℕ) : Aᵀ.charCoeff n = A.charCoeff n := by
  simp only [charCoeff_def, principalMinor_transpose]

/-- **Extension by zero, column form.** If every column of `A` outside the range of an embedding
`e` vanishes, then restricting `A` along `e` does not change the coefficients of its
principal-minor series. -/
theorem charCoeff_submatrix_of_col_eq_zero (A : Matrix κ κ R) (e : ι ↪ κ)
    (hA : ∀ j ∉ Set.range e, ∀ i, A i j = 0) (n : ℕ) :
    (A.submatrix e e).charCoeff n = A.charCoeff n := by
  rw [← charCoeff_transpose, transpose_submatrix,
    charCoeff_submatrix_of_row_eq_zero Aᵀ e (fun j hj i ↦ hA j hj i), charCoeff_transpose]

/-- **Base change of coefficients.** A continuous ring morphism `f` carries the `n`-th
coefficient of the principal-minor series of `A` to that of the matrix `A.map f`, provided the
principal minors of `A` of size `n` are summable. -/
theorem charCoeff_map {S : Type*} [CommRing S] [TopologicalSpace S] [T2Space S] (f : R →+* S)
    (hf : Continuous f) {A : Matrix ι ι R} {n : ℕ}
    (hA : Summable fun s : {s : Finset ι // s.card = n} ↦ A.principalMinor s) :
    (A.map f).charCoeff n = f (A.charCoeff n) := by
  rw [charCoeff_def, charCoeff_def, map_mul, map_pow, map_neg, map_one, hA.map_tsum f hf]
  simp only [principalMinor_map]

/-- **Scaling.** Scaling `A` by `c` multiplies the `n`-th coefficient of its principal-minor
series by `c ^ n`, provided the principal minors of `A` of size `n` are summable. -/
theorem charCoeff_smul [ContinuousConstSMul R R] [T2Space R] (c : R) {A : Matrix ι ι R} {n : ℕ}
    (hA : Summable fun s : {s : Finset ι // s.card = n} ↦ A.principalMinor s) :
    (c • A).charCoeff n = c ^ n * A.charCoeff n := by
  have hsum : ∑' s : {s : Finset ι // s.card = n}, (c • A).principalMinor s =
      c ^ n * ∑' s : {s : Finset ι // s.card = n}, A.principalMinor s := by
    rw [← smul_eq_mul, ← hA.tsum_const_smul]
    exact tsum_congr fun s ↦ by rw [principalMinor_smul, s.2, smul_eq_mul]
  rw [charCoeff_def, charCoeff_def, hsum, mul_left_comm]

/-- The principal-minor series `det (1 - T A)`, whose coefficients are `Matrix.charCoeff`. -/
noncomputable def charPowerSeries (A : Matrix ι ι R) : PowerSeries R :=
  PowerSeries.mk A.charCoeff

theorem charPowerSeries_def (A : Matrix ι ι R) : A.charPowerSeries = PowerSeries.mk A.charCoeff :=
  (rfl)

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

/-- **Extension by zero.** If every row of `A` outside the range of an embedding `e` vanishes,
then restricting `A` along `e` does not change its principal-minor series. -/
theorem charPowerSeries_submatrix_of_row_eq_zero (A : Matrix κ κ R) (e : ι ↪ κ)
    (hA : ∀ i ∉ Set.range e, ∀ j, A i j = 0) :
    (A.submatrix e e).charPowerSeries = A.charPowerSeries := by
  ext n
  simp [charCoeff_submatrix_of_row_eq_zero A e hA]

/-- **Extension by zero, column form.** If every column of `A` outside the range of an embedding
`e` vanishes, then restricting `A` along `e` does not change its principal-minor series. -/
theorem charPowerSeries_submatrix_of_col_eq_zero (A : Matrix κ κ R) (e : ι ↪ κ)
    (hA : ∀ j ∉ Set.range e, ∀ i, A i j = 0) :
    (A.submatrix e e).charPowerSeries = A.charPowerSeries := by
  ext n
  simp [charCoeff_submatrix_of_col_eq_zero A e hA]

/-- The principal-minor series is unchanged by transposition. -/
@[simp]
theorem charPowerSeries_transpose (A : Matrix ι ι R) : Aᵀ.charPowerSeries = A.charPowerSeries := by
  ext n
  simp

/-- **Base change.** If the principal minors of `A` of each size are summable, a continuous ring
morphism `f` carries the principal-minor series of `A` to that of the matrix `A.map f`. -/
theorem charPowerSeries_map {S : Type*} [CommRing S] [TopologicalSpace S] [T2Space S]
    (f : R →+* S) (hf : Continuous f) {A : Matrix ι ι R}
    (hA : ∀ n, Summable fun s : {s : Finset ι // s.card = n} ↦ A.principalMinor s) :
    (A.map f).charPowerSeries = PowerSeries.map f A.charPowerSeries := by
  ext n
  rw [PowerSeries.coeff_map, coeff_charPowerSeries, coeff_charPowerSeries,
    charCoeff_map f hf (hA n)]

/-- **Scaling.** If the principal minors of `A` of each size are summable, the principal-minor
series of `c • A` is that of `A` with the variable rescaled by `c`: `H_{c A}(T) = H_A(c T)`. -/
theorem charPowerSeries_smul [ContinuousConstSMul R R] [T2Space R] (c : R) {A : Matrix ι ι R}
    (hA : ∀ n, Summable fun s : {s : Finset ι // s.card = n} ↦ A.principalMinor s) :
    (c • A).charPowerSeries = PowerSeries.rescale c A.charPowerSeries := by
  ext n
  rw [PowerSeries.coeff_rescale, coeff_charPowerSeries, coeff_charPowerSeries,
    charCoeff_smul c (hA n)]

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

/-- The principal-minor series of the zero matrix is `1`: every nonempty principal minor
vanishes. -/
@[simp]
theorem charPowerSeries_zero : (0 : Matrix ι ι R).charPowerSeries = 1 := by
  rw [← charPowerSeries_submatrix_of_row_eq_zero 0 (Function.Embedding.ofIsEmpty (α := PEmpty.{1}))
    fun _ _ _ ↦ rfl, charPowerSeries_of_isEmpty]

end Defs

section ProductMajorants

variable [SeminormedCommRing R] [IsUltrametricDist R]

/-- A common nonnegative bound on the size-`n` principal minors bounds the `n`-th
principal-minor coefficient. No convergence hypothesis is needed. -/
theorem norm_charCoeff_le_of_principalMinor_le {A : Matrix ι ι R} {n : ℕ}
    {C : ℝ} (hC : 0 ≤ C) (hs : ∀ s : Finset ι, s.card = n → ‖A.principalMinor s‖ ≤ C) :
    ‖A.charCoeff n‖ ≤ C := by
  have hsum : ‖∑' s : {s : Finset ι // s.card = n}, A.principalMinor s‖ ≤ C :=
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC fun s ↦
      hs s s.2
  rw [charCoeff_def]
  rcases neg_one_pow_eq_or R n with hn | hn <;> simpa [hn] using hsum

/-- Product majorants tending to zero imply summability of the principal minors of each
fixed size. No bound on individual matrix entries is required. -/
theorem summable_principalMinor_of_le_prod [CompleteSpace R] {A : Matrix ι ι R} {r : ι → ℝ}
    (hA : ∀ s : Finset ι, ‖A.principalMinor s‖ ≤ ∏ i ∈ s, r i)
    (hr : Tendsto r cofinite (𝓝 0)) (n : ℕ) :
    Summable fun s : {s : Finset ι // s.card = n} ↦ A.principalMinor s := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun s ↦ hA s) ?_
  have hr₀ := TauCeti.nonneg_of_norm_principalMinor_le_prod hA
  obtain ⟨M, hM⟩ := hr.bddAbove_range_of_cofinite
  set M' := max 1 M
  have hM' : 1 ≤ M' := le_max_left _ _
  have hM'₀ : 0 < M' ^ n := pow_pos (zero_lt_one.trans_le hM') n
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / M' ^ n := div_pos hε hM'₀
  -- The indices with a majorant at least `ε / M' ^ n` form a finite set `F`.
  have hF : {i | ¬r i < ε / M' ^ n}.Finite :=
    eventually_cofinite.mp (hr.eventually (gt_mem_nhds hδ))
  -- A size-`n` product of majorants that is at least `ε` only involves indices in `F`.
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

/-- **Uniform tail bound from principal minors.** Suppose the principal minors are bounded
by products of nonnegative `r i`, and let `ρ > 0`, `0 ≤ q ≤ 1`,
`1 ≤ B`, and `T` a finite set of indices with `ρ * r i ≤ q` off `T` and `ρ * r i ≤ B`
everywhere. Then `‖A.charCoeff n‖ * ρ ^ n ≤ B ^ #T * q ^ (n - #T)`, with truncated subtraction
in the exponent. The bound depends on `A` only through `r`. -/
theorem norm_charCoeff_mul_pow_le_of_le_prod {A : Matrix ι ι R} {r : ι → ℝ}
    (hA : ∀ s : Finset ι, ‖A.principalMinor s‖ ≤ ∏ i ∈ s, r i)
    {ρ q B : ℝ} (hρ : 0 < ρ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hB : 1 ≤ B) (T : Finset ι)
    (hT : ∀ i ∉ T, ρ * r i ≤ q) (hrB : ∀ i, ρ * r i ≤ B) (n : ℕ) :
    ‖A.charCoeff n‖ * ρ ^ n ≤ B ^ T.card * q ^ (n - T.card) :=
  TauCeti.mul_pow_le_of_forall_prod_le (TauCeti.nonneg_of_norm_principalMinor_le_prod hA)
    (fun _ hc hs ↦ norm_charCoeff_le_of_principalMinor_le hc fun s hs' ↦ (hA s).trans (hs s hs'))
    hρ hq₀ hq₁ hB T hT hrB

end ProductMajorants

section NormedProductMajorants

variable [NormedCommRing R] [IsUltrametricDist R]

/-- A null product majorant for principal minors makes their series restricted at every
radius, even when the matrix has no null row majorant. -/
theorem isRestricted_charPowerSeries_of_le_prod {A : Matrix ι ι R} {r : ι → ℝ}
    (hA : ∀ s : Finset ι, ‖A.principalMinor s‖ ≤ ∏ i ∈ s, r i)
    (hr : Tendsto r cofinite (𝓝 0)) (c : ℝ) :
    A.charPowerSeries.IsRestricted c := by
  rw [← PowerSeries.isRestricted_abs_iff, PowerSeries.isRestricted_iff']
  simpa only [coeff_charPowerSeries] using TauCeti.tendsto_mul_pow_of_forall_prod_le
    (TauCeti.nonneg_of_norm_principalMinor_le_prod hA) hr (fun n ↦ norm_nonneg (A.charCoeff n))
    (fun _ _ hc hs ↦ norm_charCoeff_le_of_principalMinor_le hc fun s hs' ↦
      (hA s).trans (hs s hs')) c

end NormedProductMajorants

section Ultra

variable [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]

/-- **Coefficient bound.** If `r` bounds the rows of `A` and `C ≥ 0` bounds `∏ i ∈ s, r i` for
every `n`-element set `s`, then `C` bounds the `n`-th coefficient of the principal-minor
series. No convergence hypothesis is needed. -/
theorem norm_charCoeff_le {A : Matrix ι ι R} {r : ι → ℝ} (hA : ∀ i j, ‖A i j‖ ≤ r i) {n : ℕ}
    {C : ℝ} (hC : 0 ≤ C) (hs : ∀ s : Finset ι, s.card = n → ∏ i ∈ s, r i ≤ C) :
    ‖A.charCoeff n‖ ≤ C :=
  norm_charCoeff_le_of_principalMinor_le hC fun s hs' ↦
    (norm_principalMinor_le hA s).trans (hs s hs')

/-- **Summability of principal minors.** Over a complete ultrametric normed ring with
`‖1‖ = 1`, if the rows of `A` are bounded by a family `r` tending to zero along the cofinite
filter, then the principal minors of each fixed size form a summable family. -/
theorem summable_principalMinor [CompleteSpace R] {A : Matrix ι ι R} {r : ι → ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ r i) (hr : Tendsto r cofinite (𝓝 0)) (n : ℕ) :
    Summable fun s : {s : Finset ι // s.card = n} ↦ A.principalMinor s :=
  summable_principalMinor_of_le_prod (norm_principalMinor_le hA) hr n

/-- **Uniform tail bound.** Suppose `r` bounds the rows of `A`, and let `ρ > 0`, `0 ≤ q ≤ 1`,
`1 ≤ B`, and `T` a finite set of indices with `ρ * r i ≤ q` off `T` and `ρ * r i ≤ B`
everywhere. Then `‖A.charCoeff n‖ * ρ ^ n ≤ B ^ #T * q ^ (n - #T)`, with truncated subtraction
in the exponent. The bound depends on `A` only through `r`. -/
theorem norm_charCoeff_mul_pow_le {A : Matrix ι ι R} {r : ι → ℝ} (hA : ∀ i j, ‖A i j‖ ≤ r i)
    {ρ q B : ℝ} (hρ : 0 < ρ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hB : 1 ≤ B) (T : Finset ι)
    (hT : ∀ i ∉ T, ρ * r i ≤ q) (hrB : ∀ i, ρ * r i ≤ B) (n : ℕ) :
    ‖A.charCoeff n‖ * ρ ^ n ≤ B ^ T.card * q ^ (n - T.card) :=
  norm_charCoeff_mul_pow_le_of_le_prod (norm_principalMinor_le hA)
    hρ hq₀ hq₁ hB T hT hrB n

/-- **Entirety.** If the rows of `A` are bounded by a family tending to zero along the cofinite
filter, then the principal-minor series is restricted at every radius. -/
theorem isRestricted_charPowerSeries {A : Matrix ι ι R} {r : ι → ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ r i) (hr : Tendsto r cofinite (𝓝 0)) (c : ℝ) :
    A.charPowerSeries.IsRestricted c :=
  isRestricted_charPowerSeries_of_le_prod (norm_principalMinor_le hA) hr c

end Ultra

end Matrix
