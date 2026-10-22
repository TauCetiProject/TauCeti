/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Cyclicity
public import TauCeti.RingTheory.PowerSeries.Entire.Eval
import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval
import TauCeti.Topology.Algebra.InfiniteSum.LinearRecurrence
import TauCeti.Algebra.Ring.Commute
import TauCeti.Algebra.Algebra.PowMulRecurrence
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
`‖Vₘ‖ * ρ ^ m → 0` for every `ρ`: the resolvent is a restricted power series at every radius,
that is, entire (`ContinuousLinearMap.IsRowCompact.isEntire_resolventSeries`), as is the
determinant itself (`ContinuousLinearMap.IsRowCompact.isEntire_charPowerSeries`).

Both series can therefore be evaluated at every scalar `a`. The value
`V(a) = ∑ₘ aᵐ • Vₘ` (`ContinuousLinearMap.resolventAt`, the evaluation
`PowerSeries.evalScalar` of `V` at `a`) converges in operator norm
(`ContinuousLinearMap.IsRowCompact.hasSum_resolventAt`), commutes with `u`
(`ContinuousLinearMap.commute_resolventAt`), is bounded by any uniform bound on
`‖a‖ ^ m * ‖Vₘ‖` (`ContinuousLinearMap.ringOpNorm_resolventAt_le`), and satisfies the evaluated
identity

`(1 - a • u) V(a) = V(a) (1 - a • u) = H_u(a) • 1`

(`ContinuousLinearMap.IsRowCompact.one_sub_smul_mul_resolventAt`,
`ContinuousLinearMap.IsRowCompact.resolventAt_mul_one_sub_smul`), where `H_u(a)` is the value
`PowerSeries.evalAt` of the determinant at `a`. Hence `1 - a • u` is invertible whenever `H_u(a)`
is a unit of `R`, with inverse `H_u(a)⁻¹ • V(a)`
(`ContinuousLinearMap.IsRowCompact.isUnit_one_sub_smul`,
`ContinuousLinearMap.IsRowCompact.inverse_one_sub_smul_eq`). This needs no inverse of any
operator in advance: the formal Neumann series `∑ aⁿ uⁿ` need not converge. The value `V(a)` is
an operator-norm limit of polynomials in `u`
(`ContinuousLinearMap.resolventAt_mem_closure_adjoin`).

The same holds for the Hasse derivatives `ΔᵏV` of the resolvent (`PowerSeries.hasseDeriv`, which
divides by no factorials): their values `ΔᵏV(a)` (`ContinuousLinearMap.resolventHasseDerivAt`)
converge in operator norm (`ContinuousLinearMap.IsRowCompact.hasSum_resolventHasseDerivAt`),
commute with `u` and lie in the closure of the polynomials in `u`. Differentiating the resolvent
identity gives

`(1 - a • u) Δᵏ⁺¹V(a) = Δᵏ⁺¹V(a) (1 - a • u) = Δᵏ⁺¹H_u(a) • 1 + u ΔᵏV(a)`

(`ContinuousLinearMap.IsRowCompact.one_sub_smul_mul_resolventHasseDerivAt_succ`,
`ContinuousLinearMap.IsRowCompact.resolventHasseDerivAt_succ_mul_one_sub_smul`). Put
`C = 1 - a • u`. If `ΔʲH_u(a) = 0` for `j < h`, it follows that
`C ^ (h + 1) ΔʰV(a) = ΔʰH_u(a) • C ^ h`
(`ContinuousLinearMap.IsRowCompact.one_sub_smul_pow_succ_mul_resolventHasseDerivAt`). If moreover
`ΔʰH_u(a)` is a unit, so that `a` is a good zero of order `h` of `H_u`, then
`b = ΔʰH_u(a)⁻¹ • ΔʰV(a)` satisfies `C ^ h (C b - 1) = 0`
(`ContinuousLinearMap.IsRowCompact.one_sub_smul_pow_succ_mul_inverse_smul_resolventHasseDerivAt`).
This is the identity behind the Riesz decomposition of `u` at a good zero: `1 - (C b) ^ h` is
the Riesz projector onto the generalized eigenspace `ker C ^ h`, and `(C b) ^ h` is its
complementary projector.

The coefficient estimate `‖Vₘ‖ ≤ c` is first proved for the output truncations `π_S ∘ u` to
finite sets `S` of coordinates. The entries of their resolvent coefficients are entries of the
coefficients of `adjugate (1 - T A)` for finite blocks `A`, which are coefficients of
determinants of matrices of linear polynomials
(`Matrix.norm_sum_coeff_charpolyRev_smul_pow_apply_le`). It then passes to `u` because the
truncations converge to `u` in operator norm, and each coefficient of the determinant, hence
each `Vₘ`, is continuous in operator norm on row-compact operators.

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

/-- The coefficients of the Hasse derivatives of the Fredholm resolvent:
`coeff m (Δᵏ V) = (m + k).choose k • V_{m+k}`. -/
theorem coeff_hasseDeriv_resolventSeries (u : C₀(I, R) →L[R] C₀(I, R)) (k m : ℕ) :
    PowerSeries.coeff m (PowerSeries.hasseDeriv k u.resolventSeries) =
      ((m + k).choose k : R) • u.resolventCoeff (m + k) := by
  ext x
  simp [coeff_resolventSeries]

/-- The constant coefficient of the differentiated resolvent identity
`(1 - T u) Δᵏ⁺¹V(T) = Δᵏ⁺¹H_u(T) • 1 + u Δᵏ V(T)`. -/
private theorem coeff_zero_hasseDeriv_succ_resolventSeries (u : C₀(I, R) →L[R] C₀(I, R))
    (k : ℕ) :
    PowerSeries.coeff 0 (PowerSeries.hasseDeriv (k + 1) u.resolventSeries) =
      PowerSeries.coeff 0 (PowerSeries.hasseDeriv (k + 1) u.matrixCoeff.charPowerSeries) • 1 +
        u * PowerSeries.coeff 0 (PowerSeries.hasseDeriv k u.resolventSeries) := by
  rw [coeff_hasseDeriv_resolventSeries, coeff_hasseDeriv_resolventSeries,
    PowerSeries.coeff_hasseDeriv, Matrix.coeff_charPowerSeries]
  simp only [zero_add, Nat.choose_self, Nat.cast_one, one_smul, one_mul, resolventCoeff_succ]

/-- The coefficient of `T ^ (m + 1)` in the differentiated resolvent identity
`(1 - T u) Δᵏ⁺¹V(T) = Δᵏ⁺¹H_u(T) • 1 + u Δᵏ V(T)`: the recursion `resolventCoeff_succ`
combined with Pascal's rule. -/
private theorem coeff_succ_hasseDeriv_succ_resolventSeries (u : C₀(I, R) →L[R] C₀(I, R))
    (k m : ℕ) :
    PowerSeries.coeff (m + 1) (PowerSeries.hasseDeriv (k + 1) u.resolventSeries) =
      u * PowerSeries.coeff m (PowerSeries.hasseDeriv (k + 1) u.resolventSeries) +
        (PowerSeries.coeff (m + 1)
            (PowerSeries.hasseDeriv (k + 1) u.matrixCoeff.charPowerSeries) • 1 +
          u * PowerSeries.coeff (m + 1) (PowerSeries.hasseDeriv k u.resolventSeries)) := by
  rw [coeff_hasseDeriv_resolventSeries, coeff_hasseDeriv_resolventSeries,
    coeff_hasseDeriv_resolventSeries, PowerSeries.coeff_hasseDeriv, Matrix.coeff_charPowerSeries,
    show m + 1 + (k + 1) = m + k + 1 + 1 by omega, show m + (k + 1) = m + k + 1 by omega,
    show m + 1 + k = m + k + 1 by omega, resolventCoeff_succ, Nat.choose_succ_succ' (m + k + 1)]
  refine ContinuousLinearMap.ext fun x ↦ ?_
  simp only [_root_.smul_apply, _root_.add_apply, mul_apply_eq_comp, map_smul, one_apply_eq_self]
  push_cast
  module

/-- The terms `dₘ = aᵐ • Vₘ` of the value at a scalar `a` of the Fredholm resolvent obey the
first-order recurrence `dₘ₊₁ = (a • u) * dₘ + (cₘ₊₁ aᵐ⁺¹) • 1`. -/
private theorem pow_succ_smul_resolventCoeff_succ (u : C₀(I, R) →L[R] C₀(I, R)) (a : R)
    (m : ℕ) :
    a ^ (m + 1) • u.resolventCoeff (m + 1) =
      (a • u) * (a ^ m • u.resolventCoeff m) +
        (PowerSeries.coeff (m + 1) u.matrixCoeff.charPowerSeries • a ^ (m + 1)) • 1 := by
  refine ContinuousLinearMap.ext fun x ↦ ?_
  simp only [resolventCoeff_succ, _root_.smul_apply, _root_.add_apply, one_apply_eq_self,
    mul_apply_eq_comp, Matrix.coeff_charPowerSeries, smul_eq_mul, map_smul]
  module

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

/-- **The Fredholm determinant is entire.** For a row-compact `u`, the principal-minor series
`det (1 - T u)` is a restricted power series at every radius. -/
theorem IsRowCompact.isEntire_charPowerSeries {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) : u.matrixCoeff.charPowerSeries.IsEntire :=
  PowerSeries.isEntire_iff.2 <|
    Matrix.isRestricted_charPowerSeries hu.norm_matrixCoeff_le_rowNorm hu.tendsto_rowNorm

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
theorem IsRowCompact.isEntire_resolventSeries {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) : u.resolventSeries.IsEntire := PowerSeries.isEntire_iff.2 fun c ↦ by
  rw [← PowerSeries.isRestricted_abs_iff, PowerSeries.isRestricted_iff']
  simpa only [coeff_resolventSeries] using TauCeti.tendsto_mul_pow_of_forall_prod_le
    u.rowNorm_nonneg hu.tendsto_rowNorm (fun m ↦ ringOpNorm_nonneg (u.resolventCoeff m))
    (fun _ _ hc hs ↦ hu.ringOpNorm_resolventCoeff_le hu.norm_matrixCoeff_le_rowNorm hc hs) c

end Analytic

section Evaluation

variable [NormedCommRing R] [TauCeti.NormedRing.IsTate R]

open scoped TauCeti.RingOpNorm

/-- The value `V(a) = ∑ₘ aᵐ • Vₘ` at a scalar `a` of the Fredholm resolvent
`V(T) = det (1 - T u) (1 - T u)⁻¹` of an endomorphism `u` of `C₀(I, R)`, the sum being taken in
the operator norm. It takes the junk value `0` when the sum does not converge; for row-compact
`u` over a complete ring it converges at every `a`
(`ContinuousLinearMap.IsRowCompact.hasSum_resolventAt`).

The coefficients of the resolvent are operators rather than scalars, so this is the evaluation
`PowerSeries.evalScalar` at a scalar rather than `PowerSeries.evalAt`. -/
noncomputable def resolventAt (u : C₀(I, R) →L[R] C₀(I, R)) (a : R) : C₀(I, R) →L[R] C₀(I, R) :=
  u.resolventSeries.evalScalar a

/-- The value of the Fredholm resolvent at `a` is the evaluation of the series
`ContinuousLinearMap.resolventSeries` at `a`. -/
theorem resolventAt_eq_evalScalar (u : C₀(I, R) →L[R] C₀(I, R)) (a : R) :
    u.resolventAt a = u.resolventSeries.evalScalar a :=
  (rfl)

theorem resolventAt_def (u : C₀(I, R) →L[R] C₀(I, R)) (a : R) :
    u.resolventAt a = ∑' m, a ^ m • u.resolventCoeff m := by
  simp only [resolventAt_eq_evalScalar, PowerSeries.evalScalar_def, coeff_resolventSeries]

/-- At the scalar `0` the resolvent is the identity, its constant coefficient. -/
@[simp]
theorem resolventAt_zero (u : C₀(I, R) →L[R] C₀(I, R)) : u.resolventAt 0 = 1 := by
  rw [resolventAt_eq_evalScalar, PowerSeries.evalScalar_at_zero,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_resolventSeries, resolventCoeff_zero]

/-- The value `ΔᵏV(a) = ∑ₘ aᵐ • (m + k).choose k • V_{m+k}` at a scalar `a` of the `k`-th Hasse
derivative of the Fredholm resolvent `V(T)` of an endomorphism `u` of `C₀(I, R)`, the sum being
taken in the operator norm. It takes the junk value `0` when the sum does not converge; for
row-compact `u` over a complete ultrametric ring it converges at every `a`
(`ContinuousLinearMap.IsRowCompact.hasSum_resolventHasseDerivAt`). For `k = 0` it is the value
`ContinuousLinearMap.resolventAt` of the resolvent itself. -/
noncomputable def resolventHasseDerivAt (u : C₀(I, R) →L[R] C₀(I, R)) (k : ℕ) (a : R) :
    C₀(I, R) →L[R] C₀(I, R) :=
  (PowerSeries.hasseDeriv k u.resolventSeries).evalScalar a

/-- The value at `a` of the `k`-th Hasse derivative of the Fredholm resolvent is the evaluation
at `a` of the series `PowerSeries.hasseDeriv k u.resolventSeries`. -/
theorem resolventHasseDerivAt_eq_evalScalar (u : C₀(I, R) →L[R] C₀(I, R)) (k : ℕ) (a : R) :
    u.resolventHasseDerivAt k a = (PowerSeries.hasseDeriv k u.resolventSeries).evalScalar a :=
  (rfl)

theorem resolventHasseDerivAt_def (u : C₀(I, R) →L[R] C₀(I, R)) (k : ℕ) (a : R) :
    u.resolventHasseDerivAt k a =
      ∑' m, a ^ m • ((m + k).choose k : R) • u.resolventCoeff (m + k) := by
  simp only [resolventHasseDerivAt_eq_evalScalar, PowerSeries.evalScalar_def,
    coeff_hasseDeriv_resolventSeries]

/-- The `0`-th Hasse derivative of the resolvent at `a` is the value `V(a)` of the resolvent. -/
@[simp]
theorem resolventHasseDerivAt_zero (u : C₀(I, R) →L[R] C₀(I, R)) (a : R) :
    u.resolventHasseDerivAt 0 a = u.resolventAt a := by
  rw [resolventHasseDerivAt_eq_evalScalar, PowerSeries.hasseDeriv_zero, LinearMap.id_apply,
    resolventAt_eq_evalScalar]

/-- At the scalar `0`, the `k`-th Hasse derivative of the resolvent is its `k`-th coefficient. -/
@[simp]
theorem resolventHasseDerivAt_at_zero (u : C₀(I, R) →L[R] C₀(I, R)) (k : ℕ) :
    u.resolventHasseDerivAt k 0 = u.resolventCoeff k := by
  rw [resolventHasseDerivAt_eq_evalScalar, PowerSeries.evalScalar_at_zero,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_hasseDeriv_resolventSeries, zero_add,
    Nat.choose_self, Nat.cast_one, one_smul]

/-- The Hasse derivatives of the Fredholm resolvent at a scalar commute with the operator. -/
theorem commute_resolventHasseDerivAt (u : C₀(I, R) →L[R] C₀(I, R)) (k : ℕ) (a : R) :
    Commute u (u.resolventHasseDerivAt k a) := by
  -- Synthesized up front: the nested search inside `PowerSeries.commute_evalScalar` does not
  -- find the topological ring structure of the operators.
  have : IsTopologicalSemiring (C₀(I, R) →L[R] C₀(I, R)) := inferInstance
  rw [resolventHasseDerivAt_eq_evalScalar]
  exact PowerSeries.commute_evalScalar (fun m ↦ by
    simpa only [coeff_hasseDeriv_resolventSeries] using
      (u.commute_resolventCoeff (m + k)).smul_right _) a

/-- The normalised Hasse derivative `b = c⁻¹ • ΔʰV(a)` of the resolvent commutes with
`1 - a • u`. -/
theorem commute_one_sub_smul_inverse_smul_resolventHasseDerivAt
    (u : C₀(I, R) →L[R] C₀(I, R)) (a c : R) (h : ℕ) :
    Commute (1 - a • u) (Ring.inverse c • u.resolventHasseDerivAt h a) :=
  ((u.commute_resolventHasseDerivAt h a).one_sub_smul_left (A := C₀(I, R) →L[R] C₀(I, R))
    a).smul_right _

/-- The Hasse derivatives of the Fredholm resolvent at a scalar lie in the operator-norm closure
of the polynomials in `u`. -/
theorem resolventHasseDerivAt_mem_closure_adjoin (u : C₀(I, R) →L[R] C₀(I, R)) (k : ℕ) (a : R) :
    u.resolventHasseDerivAt k a ∈
      closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) := by
  have hV (m : ℕ) : a ^ m • ((m + k).choose k : R) • u.resolventCoeff (m + k) ∈
      Algebra.adjoin R {u} := by
    rw [resolventCoeff_def]
    exact Subalgebra.smul_mem _ (Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun j _ ↦
      Subalgebra.smul_mem _ (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton R u) _) _)
        _) _
  rw [resolventHasseDerivAt_def]
  exact tsum_mem (Algebra.adjoin R {u}).toAddSubmonoid.isClosed_topologicalClosure
    fun m ↦ subset_closure (hV m)

/-- The value of the Fredholm resolvent at a scalar commutes with the operator. -/
theorem commute_resolventAt (u : C₀(I, R) →L[R] C₀(I, R)) (a : R) :
    Commute u (u.resolventAt a) := by
  simpa using u.commute_resolventHasseDerivAt 0 a

/-- The value of the Fredholm resolvent at a scalar lies in the operator-norm closure of the
polynomials in `u`. -/
theorem resolventAt_mem_closure_adjoin (u : C₀(I, R) →L[R] C₀(I, R)) (a : R) :
    u.resolventAt a ∈ closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) := by
  simpa using u.resolventHasseDerivAt_mem_closure_adjoin 0 a

variable [IsUltrametricDist R]

/-- **Operator-norm bound for the value of the Fredholm resolvent.** If `c ≥ 0` bounds
`‖a‖ ^ m * ‖Vₘ‖` for every `m`, then it bounds the operator norm of `V(a)`. -/
theorem ringOpNorm_resolventAt_le (u : C₀(I, R) →L[R] C₀(I, R)) (a : R) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ m, ‖a‖ ^ m * ‖u.resolventCoeff m‖ ≤ c) : ‖u.resolventAt a‖ ≤ c := by
  rw [resolventAt_eq_evalScalar]
  exact PowerSeries.norm_evalScalar_le (F := u.resolventSeries) hc fun m ↦ by
    simpa only [coeff_resolventSeries] using h m

variable [CompleteSpace R]

/-- **Hasse derivatives of the Fredholm resolvent at a scalar.** For a row-compact `u` and every
scalar `a`, the series `∑ₘ aᵐ • (m + k).choose k • V_{m+k}` converges in operator norm to
`ΔᵏV(a)`. -/
theorem IsRowCompact.hasSum_resolventHasseDerivAt {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) (k : ℕ) (a : R) :
    HasSum (fun m ↦ a ^ m • ((m + k).choose k : R) • u.resolventCoeff (m + k))
      (u.resolventHasseDerivAt k a) := by
  rw [resolventHasseDerivAt_eq_evalScalar]
  simpa only [coeff_hasseDeriv_resolventSeries] using
    (hu.isEntire_resolventSeries.hasseDeriv k).hasSum_evalScalar a

/-- **Evaluation of the Fredholm resolvent.** For a row-compact `u` and every scalar `a`, the
series `∑ₘ aᵐ • Vₘ` converges in operator norm to `V(a)`. -/
theorem IsRowCompact.hasSum_resolventAt {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact)
    (a : R) : HasSum (fun m ↦ a ^ m • u.resolventCoeff m) (u.resolventAt a) := by
  simpa using hu.hasSum_resolventHasseDerivAt 0 a

/-- **The evaluated resolvent identity** `(1 - a • u) V(a) = H_u(a) • 1`, where
`H_u(a) = det (1 - a u)` is the value at `a` of the entire Fredholm determinant of the
row-compact operator `u`. -/
theorem IsRowCompact.one_sub_smul_mul_resolventAt {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) (a : R) :
    (1 - a • u) * u.resolventAt a = u.matrixCoeff.charPowerSeries.evalAt a • 1 := by
  -- The sum `∑ₘ aᵐ • Vₘ x` satisfies a first-order recurrence in `C₀(I, R)`, with `a • u` acting
  -- by evaluation and inhomogeneous terms `(cₘ aᵐ) • x` summing to `H_u(a) • x`.
  refine ContinuousLinearMap.ext fun x ↦ ?_
  have h := (hasSum_apply (hu.hasSum_resolventAt a) x).sub_smul_eq_of_linearRec₁ (D := a • u)
    ((hu.isEntire_charPowerSeries.hasSum_evalAt a).smul_const x)
    (by simp)
    fun m ↦ by simpa using congr($(pow_succ_smul_resolventCoeff_succ u a m) x)
  simpa using h

/-- **The evaluated resolvent identity** `V(a) (1 - a • u) = H_u(a) • 1` for a row-compact `u`. -/
theorem IsRowCompact.resolventAt_mul_one_sub_smul {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) (a : R) :
    u.resolventAt a * (1 - a • u) = u.matrixCoeff.charPowerSeries.evalAt a • 1 := by
  have h' := Commute.sub_left (R := C₀(I, R) →L[R] C₀(I, R)) (Commute.one_left _)
    ((u.commute_resolventAt a).smul_left a)
  exact h'.eq.symm.trans (hu.one_sub_smul_mul_resolventAt a)

/-- If `H_u(a)` is a unit, `H_u(a)⁻¹ • V(a)` is a two-sided inverse of `1 - a • u`. -/
private theorem IsRowCompact.mul_inverse_smul_resolventAt {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {a : R} (ha : IsUnit (u.matrixCoeff.charPowerSeries.evalAt a)) :
    (1 - a • u) * (Ring.inverse (u.matrixCoeff.charPowerSeries.evalAt a) • u.resolventAt a) = 1 ∧
      (Ring.inverse (u.matrixCoeff.charPowerSeries.evalAt a) • u.resolventAt a) * (1 - a • u) =
        1 := by
  constructor
  · rw [mul_def, comp_smul, ← mul_def, hu.one_sub_smul_mul_resolventAt, smul_smul,
      Ring.inverse_mul_cancel _ ha, one_smul]
  · rw [mul_def, smul_comp, ← mul_def, hu.resolventAt_mul_one_sub_smul, smul_smul,
      Ring.inverse_mul_cancel _ ha, one_smul]

/-- **Invertibility from the Fredholm determinant.** If `u` is row compact and `H_u(a)`, the
value at `a` of its Fredholm determinant, is a unit of `R`, then `1 - a • u` is invertible. -/
theorem IsRowCompact.isUnit_one_sub_smul {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact)
    {a : R} (ha : IsUnit (u.matrixCoeff.charPowerSeries.evalAt a)) : IsUnit (1 - a • u) :=
  ⟨⟨_, _, (hu.mul_inverse_smul_resolventAt ha).1, (hu.mul_inverse_smul_resolventAt ha).2⟩, rfl⟩

/-- **The inverse of `1 - a • u`.** If `u` is row compact and `H_u(a)`, the value at `a` of its
Fredholm determinant, is a unit of `R`, then the inverse of `1 - a • u` is `H_u(a)⁻¹ • V(a)`. -/
theorem IsRowCompact.inverse_one_sub_smul_eq {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {a : R} (ha : IsUnit (u.matrixCoeff.charPowerSeries.evalAt a)) :
    Ring.inverse (1 - a • u) =
      Ring.inverse (u.matrixCoeff.charPowerSeries.evalAt a) • u.resolventAt a :=
  Ring.inverse_unit ⟨_, _, (hu.mul_inverse_smul_resolventAt ha).1,
    (hu.mul_inverse_smul_resolventAt ha).2⟩

end Evaluation

section HasseDerivatives

variable [NormedCommRing R] [TauCeti.NormedRing.IsTate R] [IsUltrametricDist R] [CompleteSpace R]

open scoped TauCeti.RingOpNorm

/-- **The differentiated resolvent identity** `(1 - a • u) Δᵏ⁺¹V(a) = Δᵏ⁺¹H_u(a) • 1 + u ΔᵏV(a)`
for a row-compact `u`, where `Δᵏ⁺¹H_u(a)` is the value at `a` of the `(k + 1)`-th Hasse
derivative of the Fredholm determinant. It is the value at `a` of the Hasse derivative of
`(1 - T u) V(T) = H_u(T) • 1`. -/
theorem IsRowCompact.one_sub_smul_mul_resolventHasseDerivAt_succ
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) (k : ℕ) (a : R) :
    (1 - a • u) * u.resolventHasseDerivAt (k + 1) a =
      (PowerSeries.hasseDeriv (k + 1) u.matrixCoeff.charPowerSeries).evalAt a • 1 +
        u * u.resolventHasseDerivAt k a := by
  -- As for `ContinuousLinearMap.IsRowCompact.one_sub_smul_mul_resolventAt`: the terms
  -- `aᵐ • (coeff m Δᵏ⁺¹V) x` obey a first-order recurrence in `C₀(I, R)`, now with the
  -- inhomogeneous terms of `Δᵏ⁺¹H_u(a) • x + u (ΔᵏV(a) x)`.
  refine ContinuousLinearMap.ext fun x ↦ ?_
  have hW (j : ℕ) := (hu.isEntire_resolventSeries.hasseDeriv j).hasSum_evalScalar a
  have hb := ((hu.isEntire_charPowerSeries.hasseDeriv (k + 1)).hasSum_evalAt a).smul_const x
    |>.add ((hasSum_apply (hW k) x).mapL u)
  have h := (hasSum_apply (hW (k + 1)) x).sub_smul_eq_of_linearRec₁ (D := a • u) hb
    (by simpa using congr($(u.coeff_zero_hasseDeriv_succ_resolventSeries k) x))
    fun m ↦ by
      have hm := congr(a ^ (m + 1) • $(u.coeff_succ_hasseDeriv_succ_resolventSeries k m) x)
      simp only [_root_.add_apply, mul_apply_eq_comp] at hm
      rw [_root_.smul_apply, hm]
      simp only [_root_.smul_apply, one_apply_eq_self, map_smul, PowerSeries.coeff_hasseDeriv,
        coeff_resolventSeries, mul_apply_eq_comp, natCast_apply_eq_smul, map_smul_of_tower,
        Matrix.coeff_charPowerSeries, ContinuousLinearMap.smul_def, smul_eq_mul]
      module
  simpa [resolventHasseDerivAt_eq_evalScalar] using h

/-- **The differentiated resolvent identity** `Δᵏ⁺¹V(a) (1 - a • u) = Δᵏ⁺¹H_u(a) • 1 + u ΔᵏV(a)`
for a row-compact `u`. -/
theorem IsRowCompact.resolventHasseDerivAt_succ_mul_one_sub_smul
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) (k : ℕ) (a : R) :
    u.resolventHasseDerivAt (k + 1) a * (1 - a • u) =
      (PowerSeries.hasseDeriv (k + 1) u.matrixCoeff.charPowerSeries).evalAt a • 1 +
        u * u.resolventHasseDerivAt k a := by
  have h' := Commute.sub_left (R := C₀(I, R) →L[R] C₀(I, R)) (Commute.one_left _)
    ((u.commute_resolventHasseDerivAt (k + 1) a).smul_left a)
  exact h'.eq.symm.trans (hu.one_sub_smul_mul_resolventHasseDerivAt_succ k a)

/-- **The resolvent at a zero of the Fredholm determinant.** Let `u` be row compact, put
`C = 1 - a • u`, and suppose the Hasse derivatives `ΔʲH_u(a)` vanish for `j < h`. Then
`C ^ (h + 1) ΔʰV(a) = ΔʰH_u(a) • C ^ h`. For `h = 0` this is the evaluated resolvent identity.
In particular `C ^ (j + 1) ΔʲV(a) = 0` for `j < h`. -/
theorem IsRowCompact.one_sub_smul_pow_succ_mul_resolventHasseDerivAt
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {a : R} {h : ℕ}
    (hH : ∀ j < h, (PowerSeries.hasseDeriv j u.matrixCoeff.charPowerSeries).evalAt a = 0) :
    (1 - a • u) ^ (h + 1) * u.resolventHasseDerivAt h a =
      (PowerSeries.hasseDeriv h u.matrixCoeff.charPowerSeries).evalAt a • (1 - a • u) ^ h :=
  Commute.pow_succ_mul_eq_smul_pow_of_mul_eq (A := C₀(I, R) →L[R] C₀(I, R))
    (W := fun j ↦ u.resolventHasseDerivAt j a)
    (c := fun j ↦ (PowerSeries.hasseDeriv j u.matrixCoeff.charPowerSeries).evalAt a)
    (Commute.sub_right (R := C₀(I, R) →L[R] C₀(I, R)) (Commute.one_right u)
      ((Commute.refl u).smul_right a))
    (by simpa [PowerSeries.hasseDeriv_zero] using hu.one_sub_smul_mul_resolventAt a)
    (hu.one_sub_smul_mul_resolventHasseDerivAt_succ · a) hH

/-- **The Riesz identity at a good zero.** Let `u` be row compact, put `C = 1 - a • u`, and
suppose `ΔʲH_u(a) = 0` for `j < h` while `c = ΔʰH_u(a)` is a unit, so that `a` is a good zero
of order `h` of the Fredholm determinant. Then `b = c⁻¹ • ΔʰV(a)` satisfies
`C ^ (h + 1) b = C ^ h`, that is, `C ^ h (C b - 1) = 0`. This is the identity from which the
Riesz projector `1 - (C b) ^ h` at `a` and its complementary projector `(C b) ^ h` are built. -/
theorem IsRowCompact.one_sub_smul_pow_succ_mul_inverse_smul_resolventHasseDerivAt
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {a : R} {h : ℕ}
    (hH : ∀ j < h, (PowerSeries.hasseDeriv j u.matrixCoeff.charPowerSeries).evalAt a = 0)
    (hc : IsUnit ((PowerSeries.hasseDeriv h u.matrixCoeff.charPowerSeries).evalAt a)) :
    (1 - a • u) ^ (h + 1) *
        (Ring.inverse ((PowerSeries.hasseDeriv h u.matrixCoeff.charPowerSeries).evalAt a) •
          u.resolventHasseDerivAt h a) = (1 - a • u) ^ h := by
  rw [mul_def, comp_smul, ← mul_def, hu.one_sub_smul_pow_succ_mul_resolventHasseDerivAt hH,
    smul_smul, Ring.inverse_mul_cancel _ hc, one_smul]

/-- The normalised Hasse derivative of the resolvent inverts `1 - a • u` up to a multiple of `u`:
`(1 - a • u) (c⁻¹ • Δᵏ⁺¹V(a)) = 1 + c⁻¹ • u ΔᵏV(a)` when `c = Δᵏ⁺¹H_u(a)` is a unit. -/
theorem IsRowCompact.one_sub_smul_mul_inverse_smul_resolventHasseDerivAt_succ
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact)
    {a : R} {k : ℕ}
    (hc : IsUnit ((PowerSeries.hasseDeriv (k + 1) u.matrixCoeff.charPowerSeries).evalAt a)) :
    (1 - a • u) * (Ring.inverse
        ((PowerSeries.hasseDeriv (k + 1) u.matrixCoeff.charPowerSeries).evalAt a) •
          u.resolventHasseDerivAt (k + 1) a) =
      1 + Ring.inverse ((PowerSeries.hasseDeriv (k + 1) u.matrixCoeff.charPowerSeries).evalAt a) •
        (u * u.resolventHasseDerivAt k a) := by
  rw [mul_def, comp_smul, ← mul_def, hu.one_sub_smul_mul_resolventHasseDerivAt_succ,
    smul_add (A := C₀(I, R) →L[R] C₀(I, R)),
    smul_smul, Ring.inverse_mul_cancel _ hc, one_smul]

end HasseDerivatives

end ContinuousLinearMap
