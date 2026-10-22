/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.Primitive.Basic
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic

import TauCeti.Analysis.Normed.Field.NatCast
import TauCeti.Data.Finsupp.Interval

/-!
# Termwise primitives of restricted power series

Over a normed field `K` of characteristic zero, the termwise primitive `∫ · dXᵢ` divides the
coefficient `aᵥ` by `νᵢ + 1` and multiplies the weight by the radius `cᵢ`. Since `‖(νᵢ + 1)⁻¹‖`
grows at most polynomially in `νᵢ` (`NormedField.exists_norm_inv_natCast_le_rpow`), the primitive
loses an arbitrarily small amount of the radius in the variable `Xᵢ`: for polyradii `c' ≤ c` with
`c'ᵢ < cᵢ`, it maps series restricted at `c` to series restricted at `c'`, with a Gauss norm bound

```text
‖∫ f dXᵢ‖_{c'} ≤ C ‖f‖_c.
```

The radius cannot be kept: over `ℚ_p` the series `∑ₘ p^m X^(p^m - 1)` is restricted at radius `1`,
but its primitive `∑ₘ X^(p^m)` is not. In particular, over an ultrametric field of characteristic
zero, termwise primitives preserve the overconvergent series, those restricted at some radius
greater than `1`.

## Main results

* `MvPowerSeries.exists_norm_coeff_primitive_mul_prod_le`: the weighted coefficient norms of
  `∫ f dXᵢ` at `c'` are bounded by `C` times those of `f` at `c`.
* `MvPowerSeries.exists_gaussNorm_primitive_le`: the Gauss norm bound.
* `MvPowerSeries.IsRestricted.primitive`: the primitive of a series restricted at `c` is
  restricted at `c'`.
* `MvPowerSeries.restrictedPrimitive`: over an ultrametric field, the primitive as a `K`-linear map
  from series restricted at `c` to series restricted at `c'`, bounded for the Gauss norms
  (`MvPowerSeries.exists_norm_restrictedPrimitive_le`) and hence continuous.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.2.
-/

public section

namespace MvPowerSeries

open Filter Finsupp
open scoped Topology

section NormedField

variable {σ K : Type*} [NormedField K] [CharZero K] {c c' : σ → ℝ} {i : σ}

/-- The coefficient of the termwise primitive at `ν + eᵢ` has norm `‖(νᵢ + 1)⁻¹‖ ‖aᵥ‖`. -/
theorem norm_coeff_add_single_primitive (f : MvPowerSeries σ K) (n : σ →₀ ℕ) :
    ‖coeff (n + single i 1) (primitive i f)‖ = ‖((n i : K) + 1)⁻¹‖ * ‖coeff n f‖ := by
  simp [Rat.smul_def]

/-- The weighted coefficient norms of the termwise primitive at `c'` are bounded by those of `f`
at `c`, times a factor depending on the `i`-th exponent. -/
private theorem norm_coeff_add_single_primitive_mul_prod_le (hc' : ∀ j, 0 ≤ c' j)
    (hle : ∀ j, c' j ≤ c j) (hi : 0 < c i) (f : MvPowerSeries σ K) (n : σ →₀ ℕ) :
    ‖coeff (n + single i 1) (primitive i f)‖ * (n + single i 1).prod (c' · ^ ·) ≤
      c i * (‖((n i + 1 : ℕ) : K)⁻¹‖ * (c' i / c i) ^ (n i + 1)) *
        (‖coeff n f‖ * n.prod (c · ^ ·)) := by
  have hsingle : (single i 1 : σ →₀ ℕ).prod (c' · ^ ·) = c' i := by simp
  rw [norm_coeff_add_single_primitive, prod_pow_add, hsingle]
  calc ‖((n i : K) + 1)⁻¹‖ * ‖coeff n f‖ * (n.prod (c' · ^ ·) * c' i)
      ≤ ‖((n i : K) + 1)⁻¹‖ * ‖coeff n f‖ * (n.prod (c · ^ ·) * (c' i / c i) ^ n i * c' i) := by
        gcongr
        · exact hc' i
        · exact prod_pow_le_prod_pow_mul hc' hle hi n
    _ = c i * (‖((n i + 1 : ℕ) : K)⁻¹‖ * (c' i / c i) ^ (n i + 1)) *
          (‖coeff n f‖ * n.prod (c · ^ ·)) := by
        rw [Nat.cast_succ, pow_succ]
        field_simp

variable (c c' i) in
/-- **Primitives lose an arbitrarily small amount of radius.** Over a normed field of
characteristic zero, for polyradii `0 ≤ c' ≤ c` with `c'ᵢ < cᵢ`, there is `C ≥ 0` such that the
weighted coefficient norms of `∫ f dXᵢ` at `c'` are bounded by `C` times the weighted coefficient
norms of `f` at `c`, shifted down by `eᵢ`. -/
theorem exists_norm_coeff_primitive_mul_prod_le (hc' : ∀ j, 0 ≤ c' j) (hle : ∀ j, c' j ≤ c j)
    (hlt : c' i < c i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : MvPowerSeries σ K) (n : σ →₀ ℕ),
      ‖coeff n (primitive i f)‖ * n.prod (c' · ^ ·) ≤
        C * (‖coeff (n - single i 1) f‖ * (n - single i 1).prod (c · ^ ·)) := by
  have hi : 0 < c i := (hc' i).trans_lt hlt
  have hq₀ : 0 ≤ c' i / c i := div_nonneg (hc' i) hi.le
  have hq₁ : c' i / c i < 1 := (div_lt_one hi).2 hlt
  obtain ⟨B, hB⟩ :=
    ((NormedField.tendsto_norm_inv_natCast_mul_pow K hq₀ hq₁).mono_left
      Nat.cofinite_eq_atTop.le).bddAbove_range_of_cofinite
  have hB₀ : 0 ≤ B := (by positivity : 0 ≤ ‖((0 : ℕ) : K)⁻¹‖ * (c' i / c i) ^ 0).trans (hB ⟨0, rfl⟩)
  have hc : ∀ j, 0 ≤ c j := fun j ↦ (hc' j).trans (hle j)
  refine ⟨c i * B, by positivity, fun f n ↦ ?_⟩
  have hw : 0 ≤ ‖coeff (n - single i 1) f‖ * (n - single i 1).prod (c · ^ ·) :=
    mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun j _ ↦ pow_nonneg (hc j) _)
  by_cases hn : n i = 0
  · rw [coeff_primitive_of_eq_zero i f hn, norm_zero, zero_mul]
    exact mul_nonneg (by positivity) hw
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + single i 1 := ⟨_, (sub_add_single_one_cancel hn).symm⟩
    rw [add_tsub_cancel_right] at hw ⊢
    exact (norm_coeff_add_single_primitive_mul_prod_le hc' hle hi f m).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hB ⟨m i + 1, rfl⟩) hi.le) hw)

variable (c c' i) in
/-- **The Gauss norm bound for primitives.** Over a normed field of characteristic zero, for
polyradii `0 ≤ c' ≤ c` with `c'ᵢ < cᵢ`, there is `C ≥ 0` such that for every `f` with a Gauss norm
at `c`, `∫ f dXᵢ` has a Gauss norm at `c'` and `gaussNorm c' (∫ f dXᵢ) ≤ C * gaussNorm c f`. -/
theorem exists_gaussNorm_primitive_le (hc' : ∀ j, 0 ≤ c' j) (hle : ∀ j, c' j ≤ c j)
    (hlt : c' i < c i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : MvPowerSeries σ K, HasGaussNorm norm c f →
      HasGaussNorm norm c' (primitive i f) ∧
        gaussNorm norm c' (primitive i f) ≤ C * gaussNorm norm c f := by
  obtain ⟨C, hC₀, hC⟩ := exists_norm_coeff_primitive_mul_prod_le (K := K) c c' i hc' hle hlt
  refine ⟨C, hC₀, fun f hf ↦ ?_⟩
  have hbound (n : σ →₀ ℕ) :
      ‖coeff n (primitive i f)‖ * n.prod (c' · ^ ·) ≤ C * gaussNorm norm c f :=
    (hC f n).trans (mul_le_mul_of_nonneg_left (le_gaussNorm _ _ _ hf _) hC₀)
  exact ⟨⟨_, Set.forall_mem_range.2 hbound⟩, ciSup_le hbound⟩

/-- **Primitives of restricted series.** Over a normed field of characteristic zero, for polyradii
`0 ≤ c' ≤ c` with `c'ᵢ < cᵢ`, the termwise primitive of a series restricted at `c` is restricted
at `c'`. -/
theorem IsRestricted.primitive (hc' : ∀ j, 0 ≤ c' j) (hle : ∀ j, c' j ≤ c j) (hlt : c' i < c i)
    {f : MvPowerSeries σ K} (hf : IsRestricted c f) : IsRestricted c' (primitive i f) := by
  obtain ⟨C, -, hC⟩ := exists_norm_coeff_primitive_mul_prod_le (K := K) c c' i hc' hle hlt
  refine squeeze_zero (fun n ↦ mul_nonneg (norm_nonneg _)
    (Finset.prod_nonneg fun j _ ↦ pow_nonneg (hc' j) _)) (hC f) ?_
  simpa using (hf.comp (tendsto_sub_cofinite (single i 1))).const_mul C

end NormedField

section Restricted

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K] {c c' : σ → ℝ}
  [∀ j, Fact (0 < c j)] [∀ j, Fact (0 < c' j)]

/-- The termwise primitive with respect to `Xᵢ`, as a `K`-linear map from series restricted at
positive polyradii `c` to series restricted at positive polyradii `c' ≤ c` with `c'ᵢ < cᵢ`. The
field `K` is ultrametric, as needed for the restricted series to form a ring. -/
noncomputable def restrictedPrimitive (i : σ) (hle : ∀ j, c' j ≤ c j) (hlt : c' i < c i) :
    IsRestricted.subring (R := K) c →ₗ[K] IsRestricted.subring (R := K) c' where
  toFun f := ⟨primitive i (f : MvPowerSeries σ K),
    f.2.primitive (fun j ↦ (Fact.out : 0 < c' j).le) hle hlt⟩
  map_add' f g := Subtype.ext (map_add (primitive i) (f : MvPowerSeries σ K) g)
  map_smul' a f := by
    apply Subtype.ext
    -- The scalar action on restricted series is multiplication by the constant series `C a`.
    simp only [Algebra.smul_def, Subring.coe_mul, coe_algebraMap_isRestrictedSubring,
      RingHom.id_apply]
    simp only [← smul_eq_C_mul, map_smul]

/-- The primitive of a restricted series is its termwise primitive as a formal series. -/
@[simp]
theorem coe_restrictedPrimitive (i : σ) (hle : ∀ j, c' j ≤ c j) (hlt : c' i < c i)
    (f : IsRestricted.subring (R := K) c) :
    (restrictedPrimitive i hle hlt f : MvPowerSeries σ K) = primitive i f :=
  (rfl)

/-- **The operator bound for primitives.** The termwise primitive from series restricted at `c`
to series restricted at `c'` is bounded for the Gauss norms. -/
theorem exists_norm_restrictedPrimitive_le (i : σ) (hle : ∀ j, c' j ≤ c j) (hlt : c' i < c i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : IsRestricted.subring (R := K) c,
      ‖restrictedPrimitive i hle hlt f‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC₀, hC⟩ :=
    exists_gaussNorm_primitive_le (K := K) c c' i (fun j ↦ (Fact.out : 0 < c' j).le) hle hlt
  refine ⟨C, hC₀, fun f ↦ ?_⟩
  rw [norm_eq_gaussNorm, norm_eq_gaussNorm, coe_restrictedPrimitive]
  exact (hC f f.2.hasGaussNorm).2

/-- The termwise primitive from series restricted at `c` to series restricted at `c'` is
continuous for the Gauss norms. -/
theorem continuous_restrictedPrimitive (i : σ) (hle : ∀ j, c' j ≤ c j) (hlt : c' i < c i) :
    Continuous (restrictedPrimitive (K := K) i hle hlt) := by
  obtain ⟨C, -, hC⟩ := exists_norm_restrictedPrimitive_le (K := K) i hle hlt
  exact AddMonoidHomClass.continuous_of_bound _ C hC

end Restricted

end MvPowerSeries
