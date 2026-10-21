/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Cyclicity
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.RingTheory.PowerSeries.Geometric

/-!
# The Fredholm resolvent of a row-compact operator

Let `R` be a complete ultrametric normed commutative ring with `‖1‖ = 1` and Tate scalars, `I` a
discrete index type, and `u` an endomorphism of the model space `C₀(I, R)` with Fredholm
determinant `H_u(T) = det (1 - T u) = ∑ cₙ Tⁿ`, the principal-minor series
`u.matrixCoeff.charPowerSeries`. The **Fredholm resolvent** of `u` is the power series
`V(T) = ∑ Vₘ Tᵐ` with operator coefficients

`Vₘ = ∑ k ∈ range (m + 1), cₖ • u ^ (m - k)` (`ContinuousLinearMap.resolventCoeff`),

the series `ContinuousLinearMap.resolventSeries`. Formally `V(T) = H_u(T) (1 - T u)⁻¹`: it
satisfies

`(1 - T u) V(T) = V(T) (1 - T u) = H_u(T) • 1`

(`ContinuousLinearMap.one_sub_C_mul_X_mul_resolventSeries`,
`ContinuousLinearMap.resolventSeries_mul_one_sub_C_mul_X`). For a finite matrix `A` it is the
adjugate of `1 - T A` (`Matrix.coeff_adjugate_one_sub_X_smul_apply`). The definition and these
identities are algebraic and hold over any seminormed commutative ring.

The analytic content is that `V` is entire in operator norm when `u` is row compact, even
though the Neumann series `(1 - T u)⁻¹ = ∑ uⁿ Tⁿ` need not converge. If `r i` bounds the `i`-th
row of the matrix of `u`, the coefficients satisfy the same estimate as the determinant:
`‖Vₘ‖ ≤ c` whenever `c ≥ 0` bounds `∏ i ∈ s, r i` for every `m`-element set `s`
(`ContinuousLinearMap.IsRowCompact.ringOpNorm_resolventCoeff_le`). Consequently
`‖Vₘ‖ * ρ ^ m → 0` for every `ρ`, that is, the resolvent is a restricted power series at every
radius (`ContinuousLinearMap.IsRowCompact.isRestricted_resolventSeries`).

The estimate is first proved for the output truncations `π_S ∘ u` to finite sets `S` of
coordinates. The entries of their resolvent coefficients are entries of the coefficients of
`adjugate (1 - T A)` for finite blocks `A`, which are coefficients of determinants of matrices
of linear polynomials (`Matrix.norm_sum_coeff_charpolyRev_smul_pow_apply_le`). It then passes to
`u` because the truncations converge to `u` in operator norm, and each coefficient of the
determinant, hence each `Vₘ`, is continuous in operator norm on row-compact operators.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§4–7.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A.
-/

public section

open Filter Finset Topology ZeroAtInftyContinuousMap
open scoped ZeroAtInfty

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]

namespace ContinuousLinearMap

section Algebraic

variable [SeminormedCommRing R]

/-- The `m`-th coefficient `∑ k ∈ range (m + 1), cₖ • u ^ (m - k)` of the Fredholm resolvent
`det (1 - T u) (1 - T u)⁻¹` of an endomorphism `u` of `C₀(I, R)`, where `cₖ` is the `k`-th
coefficient of the Fredholm determinant `u.matrixCoeff.charPowerSeries`. -/
noncomputable def resolventCoeff (u : C₀(I, R) →L[R] C₀(I, R)) (m : ℕ) :
    C₀(I, R) →L[R] C₀(I, R) :=
  ∑ k ∈ range (m + 1), u.matrixCoeff.charCoeff k • u ^ (m - k)

theorem resolventCoeff_def (u : C₀(I, R) →L[R] C₀(I, R)) (m : ℕ) :
    u.resolventCoeff m = ∑ k ∈ range (m + 1), u.matrixCoeff.charCoeff k • u ^ (m - k) :=
  (rfl)

@[simp]
theorem resolventCoeff_zero (u : C₀(I, R) →L[R] C₀(I, R)) : u.resolventCoeff 0 = 1 := by
  simp [resolventCoeff_def]

/-- The recursion `V_{m+1} = c_{m+1} • 1 + u * V_m` for the coefficients of the Fredholm
resolvent. -/
theorem resolventCoeff_succ (u : C₀(I, R) →L[R] C₀(I, R)) (m : ℕ) :
    u.resolventCoeff (m + 1) = u.matrixCoeff.charCoeff (m + 1) • 1 + u * u.resolventCoeff m := by
  rw [resolventCoeff_def, resolventCoeff_def]
  exact TauCeti.sum_range_succ_smul_pow_sub u.matrixCoeff.charCoeff u m

/-- The recursion `V_{m+1} = c_{m+1} • 1 + V_m * u` for the coefficients of the Fredholm
resolvent. -/
theorem resolventCoeff_succ' (u : C₀(I, R) →L[R] C₀(I, R)) (m : ℕ) :
    u.resolventCoeff (m + 1) = u.matrixCoeff.charCoeff (m + 1) • 1 + u.resolventCoeff m * u := by
  rw [resolventCoeff_def, resolventCoeff_def]
  exact TauCeti.sum_range_succ_smul_pow_sub' u.matrixCoeff.charCoeff u m

/-- Each coefficient of the Fredholm resolvent commutes with the operator. -/
theorem commute_resolventCoeff (u : C₀(I, R) →L[R] C₀(I, R)) (m : ℕ) :
    Commute u (u.resolventCoeff m) := by
  exact (eq_sub_of_add_eq' (u.resolventCoeff_succ m).symm).trans
    (eq_sub_of_add_eq' (u.resolventCoeff_succ' m).symm).symm

/-- The **Fredholm resolvent** `V(T) = det (1 - T u) (1 - T u)⁻¹` of an endomorphism `u` of
`C₀(I, R)`, the power series with coefficients `ContinuousLinearMap.resolventCoeff`. -/
noncomputable def resolventSeries (u : C₀(I, R) →L[R] C₀(I, R)) :
    PowerSeries (C₀(I, R) →L[R] C₀(I, R)) :=
  PowerSeries.mk u.resolventCoeff

theorem resolventSeries_def (u : C₀(I, R) →L[R] C₀(I, R)) :
    u.resolventSeries = PowerSeries.mk u.resolventCoeff :=
  (rfl)

@[simp]
theorem coeff_resolventSeries (u : C₀(I, R) →L[R] C₀(I, R)) (m : ℕ) :
    PowerSeries.coeff m u.resolventSeries = u.resolventCoeff m := by
  rw [resolventSeries_def, PowerSeries.coeff_mk]

/-- **The resolvent identity** `(1 - T u) V(T) = det (1 - T u) • 1`. -/
theorem one_sub_C_mul_X_mul_resolventSeries (u : C₀(I, R) →L[R] C₀(I, R)) :
    (1 - PowerSeries.C u * PowerSeries.X) * u.resolventSeries =
      PowerSeries.map (algebraMap R _) u.matrixCoeff.charPowerSeries := by
  rw [Matrix.charPowerSeries_def, resolventSeries_def]
  exact TauCeti.powerSeries_one_sub_C_mul_X_mul_mk_sum_smul_pow u.matrixCoeff.charCoeff u

/-- **The resolvent identity** `V(T) (1 - T u) = det (1 - T u) • 1`. -/
theorem resolventSeries_mul_one_sub_C_mul_X (u : C₀(I, R) →L[R] C₀(I, R)) :
    u.resolventSeries * (1 - PowerSeries.C u * PowerSeries.X) =
      PowerSeries.map (algebraMap R _) u.matrixCoeff.charPowerSeries := by
  rw [Matrix.charPowerSeries_def, resolventSeries_def]
  exact TauCeti.powerSeries_mk_sum_smul_pow_mul_one_sub_C_mul_X u.matrixCoeff.charCoeff u

end Algebraic

section Analytic

variable [NormedCommRing R]

/-- If the rows of `w` outside a finite set `F` vanish, the block of `w ^ k` on `F` is the
`k`-th power of the block of `w` on `F`. -/
private theorem submatrix_matrixCoeff_pow {w : C₀(I, R) →L[R] C₀(I, R)} {F : Finset I}
    (hw : ∀ i ∉ F, ∀ j, w.matrixCoeff i j = 0) (k : ℕ) :
    (w ^ k).matrixCoeff.submatrix (Subtype.val : F → I) (Subtype.val : F → I) =
      w.matrixCoeff.submatrix (Subtype.val : F → I) (Subtype.val : F → I) ^ k := by
  induction k with
  | zero =>
    ext x y
    simp [Matrix.one_apply]
  | succ k ih =>
    ext x y
    rw [pow_succ, pow_succ, Matrix.submatrix_apply, matrixCoeff_mul, Matrix.mul_apply, ← ih,
      tsum_eq_sum (s := F) fun l hl ↦ by simp [hw l hl], ← Finset.sum_coe_sort F]
    simp

variable [NormOneClass R] [IsUltrametricDist R]

/-- **Resolvent entries of a map with finitely many nonzero rows.** If the rows of `w` outside a
finite set `F` vanish and `r i` bounds the `i`-th row of `w`, then `c ≥ 0` bounds the entries
of `w.resolventCoeff m` in `F × F` whenever it bounds `∏ i ∈ s, r i` for every `m`-element set
`s`. These entries are those of the resolvent of the finite block of `w` on `F`. -/
private theorem norm_matrixCoeff_resolventCoeff_le_of_row_eq_zero
    {w : C₀(I, R) →L[R] C₀(I, R)} {F : Finset I} (hw : ∀ i ∉ F, ∀ j, w.matrixCoeff i j = 0)
    {r : I → ℝ} (hr : ∀ i j, ‖w.matrixCoeff i j‖ ≤ r i) {m : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hs : ∀ s : Finset I, s.card = m → ∏ i ∈ s, r i ≤ c) (x y : F) :
    ‖(w.resolventCoeff m).matrixCoeff x y‖ ≤ c := by
  set B := w.matrixCoeff.submatrix (Subtype.val : F → I) (Subtype.val : F → I)
  -- The determinant coefficients of `w` are those of its block `B`, since the other rows vanish.
  have hcoeff (k : ℕ) : w.matrixCoeff.charCoeff k = B.charpolyRev.coeff k := by
    rw [← Matrix.charCoeff_eq_coeff_charpolyRev,
      ← Matrix.charCoeff_submatrix_of_row_eq_zero w.matrixCoeff (Function.Embedding.subtype _)
        (fun i hi ↦ hw i fun hiF ↦ hi ⟨⟨i, hiF⟩, rfl⟩) k, Function.Embedding.coe_subtype]
  have hentry : (w.resolventCoeff m).matrixCoeff x y =
      (∑ k ∈ range (m + 1), B.charpolyRev.coeff k • B ^ (m - k)) x y := by
    rw [resolventCoeff_def, matrixCoeff_sum, Matrix.sum_apply, Matrix.sum_apply]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [matrixCoeff_smul, Matrix.smul_apply, Matrix.smul_apply, hcoeff,
      ← submatrix_matrixCoeff_pow hw, Matrix.submatrix_apply]
  rw [hentry]
  refine Matrix.norm_sum_coeff_charpolyRev_smul_pow_apply_le (r := fun i : F ↦ r i)
    (fun i j ↦ hr i j) hc (fun s hs' ↦ ?_) x y
  simpa only [prod_map, Function.Embedding.coe_subtype] using
    hs (s.map (Function.Embedding.subtype _)) (by rw [card_map, hs'])

variable [CompleteSpace R] [TauCeti.NormedRing.IsTate R]

open scoped TauCeti.RingOpNorm

/-- **Operator-norm bound for the Fredholm resolvent.** If `u` is row compact, `r i` bounds the
`i`-th row of its matrix, and `c ≥ 0` bounds `∏ i ∈ s, r i` for every `m`-element set `s`, then
`c` bounds the operator norm of the `m`-th coefficient of the Fredholm resolvent of `u`. This is
the bound satisfied by the `m`-th coefficient of the Fredholm determinant
(`Matrix.norm_charCoeff_le`). -/
theorem IsRowCompact.ringOpNorm_resolventCoeff_le {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {r : I → ℝ} (hr : ∀ i j, ‖u.matrixCoeff i j‖ ≤ r i) {m : ℕ} {c : ℝ}
    (hc : 0 ≤ c) (hs : ∀ s : Finset I, s.card = m → ∏ i ∈ s, r i ≤ c) :
    ‖u.resolventCoeff m‖ ≤ c := by
  -- Approximate `u` by its output truncations `π_S ∘ u`, which have finitely many nonzero rows.
  let uS := fun S : Finset I ↦ (indicatorCLM R (S : Set I)).comp u
  have huS : Tendsto (fun S ↦ ‖uS S - u‖) atTop (𝓝 0) :=
    hu.tendsto_ringOpNorm_indicatorCLM_comp_sub
  have huS' : Tendsto uS atTop (𝓝 u) := tendsto_iff_norm_sub_tendsto_zero.2 huS
  have hV : Tendsto (fun S ↦ (uS S).resolventCoeff m) atTop (𝓝 (u.resolventCoeff m)) := by
    simp only [resolventCoeff_def]
    refine tendsto_finsetSum _ fun k _ ↦ Tendsto.smul ?_ (huS'.pow (m - k))
    exact tendsto_charCoeff_matrixCoeff_of_tendsto
      (.of_forall fun S ↦ isRowCompact_indicatorCLM_comp S u) hu huS k
  refine le_of_tendsto' hV.norm fun S ↦
    ringOpNorm_le_of_forall_norm_matrixCoeff_le _ hc fun a b ↦ ?_
  have hrow (i : I) (hi : i ∉ insert a (insert b S)) (j : I) : (uS S).matrixCoeff i j = 0 := by
    simp_all [uS, matrixCoeff_indicatorCLM_comp]
  have hrS (i j : I) : ‖(uS S).matrixCoeff i j‖ ≤ r i := by
    rw [matrixCoeff_indicatorCLM_comp, Set.indicator_apply]
    split_ifs
    · exact hr i j
    · simpa using (norm_nonneg _).trans (hr i j)
  exact norm_matrixCoeff_resolventCoeff_le_of_row_eq_zero hrow hrS hc hs
    ⟨a, mem_insert_self _ _⟩ ⟨b, mem_insert_of_mem (mem_insert_self _ _)⟩

/-- **Uniform tail bound for the Fredholm resolvent.** Suppose `u` is row compact and `r i`
bounds the `i`-th row of its matrix, and let `ρ > 0`, `0 ≤ q ≤ 1`, `1 ≤ B`, and `T` a finite
set of indices with `ρ * r i ≤ q` off `T` and `ρ * r i ≤ B` everywhere. Then
`‖u.resolventCoeff m‖ * ρ ^ m ≤ B ^ #T * q ^ (m - #T)`, with truncated subtraction in the
exponent. The bound depends on `u` only through `r`. -/
theorem IsRowCompact.ringOpNorm_resolventCoeff_mul_pow_le {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {r : I → ℝ} (hr : ∀ i j, ‖u.matrixCoeff i j‖ ≤ r i)
    {ρ q B : ℝ} (hρ : 0 < ρ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hB : 1 ≤ B) (T : Finset I)
    (hT : ∀ i ∉ T, ρ * r i ≤ q) (hrB : ∀ i, ρ * r i ≤ B) (m : ℕ) :
    ‖u.resolventCoeff m‖ * ρ ^ m ≤ B ^ T.card * q ^ (m - T.card) :=
  TauCeti.mul_pow_le_of_forall_prod_le (fun i ↦ (norm_nonneg _).trans (hr i i))
    (fun _ hc hs ↦ hu.ringOpNorm_resolventCoeff_le hr hc hs) hρ hq₀ hq₁ hB T hT hrB

/-- **The Fredholm resolvent is entire.** For a row-compact `u`, the resolvent
`det (1 - T u) (1 - T u)⁻¹` is a restricted power series at every radius in the Banach ring of
operators: `‖u.resolventCoeff m‖ * c ^ m → 0` for every `c`. -/
theorem IsRowCompact.isRestricted_resolventSeries {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) (c : ℝ) : u.resolventSeries.IsRestricted c := by
  rw [← PowerSeries.isRestricted_abs_iff, PowerSeries.isRestricted_iff']
  simpa only [coeff_resolventSeries] using TauCeti.tendsto_mul_pow_of_forall_prod_le
    u.rowNorm_nonneg hu.tendsto_rowNorm (fun m ↦ ringOpNorm_nonneg (u.resolventCoeff m))
    (fun _ _ hc hs ↦ hu.ringOpNorm_resolventCoeff_le hu.norm_matrixCoeff_le_rowNorm hc hs) c

end Analytic

end ContinuousLinearMap
