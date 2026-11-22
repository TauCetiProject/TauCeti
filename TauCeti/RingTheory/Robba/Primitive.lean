/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.Robba.Basic

import TauCeti.Analysis.Normed.Field.NatCast

/-!
# Termwise derivatives and primitives of Laurent series on annuli

A two-sided coefficient family `a : ℤ → V` stands for the Laurent series `f = ∑_{n ∈ ℤ} aₙ tⁿ`, and
it defines a function on the open annulus `{r < |t| < s}` when it converges
(`TauCeti.LaurentConvergesAt`) at every radius `r < ρ < s`. This file differentiates and integrates
such series term by term, and proves that a differential `f dt` on an open annulus over a field of
characteristic zero has a primitive on the same annulus exactly when its residue, the coefficient
`a₋₁` of `t⁻¹`, vanishes. The primitive is then unique up to an additive constant.

The derivative `∑ aₙ tⁿ ↦ ∑ n aₙ tⁿ⁻¹` never has a `t⁻¹` term, so the residue is an obstruction.
Conversely, for `a₋₁ = 0` the termwise primitive `∑_{n ≠ -1} aₙ tⁿ⁺¹ / (n + 1)` converges on the
whole open annulus: the inverses `‖(n + 1)⁻¹‖` grow at most polynomially in `n`
(`NormedField.exists_norm_inv_natCast_le_rpow`), and convergence at radii slightly larger and
slightly smaller than `ρ` absorbs this growth at the two tails. Convergence at the single radius
`ρ` is not enough: over `ℚ_p` the family with `a_{p^k - 1} = p ^ k` converges on `|t| = 1`, but
its primitive `∑ t^(p^k)` does not. This is why annuli are open sets of radii here. Over an
ultrametric field the derivative needs no such room: it preserves convergence at every radius and
satisfies `|f'|_ρ ≤ ρ⁻¹ |f|_ρ`.

The obstruction is the reason the logarithm enters `p`-adic integration: on an annulus `dt / t`
has no analytic primitive.

## Main definitions

* `TauCeti.laurentDerivative`: the termwise derivative of a coefficient family.
* `TauCeti.laurentPrimitive`: the termwise primitive with zero constant coefficient.

## Main results

* `TauCeti.laurentDerivative_apply_neg_one`: a derivative has zero residue.
* `TauCeti.laurentDerivative_eq_zero_iff_eq_single`: without additive torsion, the families with
  zero derivative are the constants.
* `TauCeti.laurentDerivative_laurentPrimitive`, `TauCeti.laurentPrimitive_laurentDerivative`:
  differentiation and integration are inverse up to the residue and the constant term.
* `TauCeti.LaurentConvergesAt.laurentDerivative`, `TauCeti.laurentGaussNorm_laurentDerivative_le`:
  over an ultrametric group the derivative converges wherever the series does, with
  `|f'|_ρ ≤ ρ⁻¹ |f|_ρ`.
* `TauCeti.LaurentConvergesAt.laurentPrimitive`: the primitive converges at `ρ` when the series
  converges at radii on both sides of `ρ`.
* `TauCeti.exists_laurentDerivative_eq_iff`: on an open set of positive radii, a convergent
  Laurent series has a convergent primitive if and only if its residue vanishes.
* `TauCeti.eq_laurentPrimitive_add_single_iff`, `TauCeti.existsUnique_laurentDerivative_eq`: the
  primitives of a residue-free series differ by constants, and a convergent primitive is unique
  once its constant coefficient is fixed.

## References

* J. S. Balakrishnan, R. W. Bradshaw, K. S. Kedlaya, *Explicit Coleman integration for
  hyperelliptic curves*, ANTS IX, LNCS 6197 (2010), §2, Definition 1 and Remark 2.
* A. Besser, *Coleman integration using the Tannakian formalism*, Math. Ann. 322 (2002), §5.
* K. S. Kedlaya, *Local monodromy of p-adic differential equations: an overview*, Int. J. Number
  Theory 1 (2005), Example 4.1.11 and Definition 5.1.1.
-/

public section

open Filter Topology

namespace TauCeti

/-! ### The termwise derivative -/

section Derivative

variable (S : Type*) {V : Type*} [Semiring S] [AddCommGroup V] [Module S V]

/-- The termwise derivative `∑ aₙ tⁿ ↦ ∑ n aₙ tⁿ⁻¹` of a two-sided Laurent coefficient family.
Its coefficient at `n` is `(n + 1) • aₙ₊₁`. -/
def laurentDerivative : (ℤ → V) →ₗ[S] ℤ → V where
  toFun a n := (n + 1) • a (n + 1)
  map_add' a b := funext fun n ↦ smul_add _ (a (n + 1)) (b (n + 1))
  map_smul' c a := funext fun n ↦ smul_comm _ c (a (n + 1))

variable {S}

@[simp]
theorem laurentDerivative_apply (a : ℤ → V) (n : ℤ) :
    laurentDerivative S a n = (n + 1) • a (n + 1) :=
  (rfl)

/-- The coefficient of `tⁿ⁻¹` in the derivative is `n aₙ`. -/
theorem laurentDerivative_apply_sub_one (a : ℤ → V) (n : ℤ) :
    laurentDerivative S a (n - 1) = n • a n := by
  simp

/-- The residue of a derivative, its coefficient of `t⁻¹`, vanishes. -/
theorem laurentDerivative_apply_neg_one (a : ℤ → V) : laurentDerivative S a (-1) = 0 := by
  simp

/-- The derivative of the monomial `c tⁿ` is `n c tⁿ⁻¹`. -/
@[simp]
theorem laurentDerivative_single (n : ℤ) (c : V) :
    laurentDerivative S (Pi.single n c) = Pi.single (n - 1) (n • c) := by
  ext m
  by_cases h : m = n - 1
  · subst m
    simp
  · have h' : m + 1 ≠ n := by omega
    simp [h, h']

/-- A family has zero derivative exactly when `n • aₙ = 0` for every `n`. -/
theorem laurentDerivative_eq_zero_iff {a : ℤ → V} :
    laurentDerivative S a = 0 ↔ ∀ n : ℤ, n • a n = 0 := by
  refine ⟨fun h n ↦ ?_, fun h ↦ funext fun n ↦ by simp [h (n + 1)]⟩
  rw [← laurentDerivative_apply_sub_one (S := S), h, Pi.zero_apply]

/-- Without additive torsion, the families with zero derivative are the constants. -/
theorem laurentDerivative_eq_zero_iff_eq_single [IsAddTorsionFree V] {a : ℤ → V} :
    laurentDerivative S a = 0 ↔ a = Pi.single 0 (a 0) := by
  rw [laurentDerivative_eq_zero_iff]
  refine ⟨fun h ↦ funext fun n ↦ ?_, fun h n ↦ ?_⟩
  · by_cases hn : n = 0
    · subst n
      simp
    · simpa [Pi.single_apply, hn] using h n
  · rw [h]
    by_cases hn : n = 0 <;> simp [hn]

/-- The termwise derivative of the coefficients of a formal Laurent series is the coefficient
family of its derivative. -/
theorem laurentDerivative_coeff (f : LaurentSeries V) :
    laurentDerivative S f.coeff = (LaurentSeries.derivative S f).coeff := by
  ext n
  simp [LaurentSeries.hasseDeriv_coeff]

end Derivative

/-! ### Convergence of the derivative over an ultrametric group -/

section Ultrametric

variable {S V : Type*} [Semiring S] [SeminormedAddCommGroup V] [IsUltrametricDist V]
  [Module S V] {ρ : ℝ} {a : ℤ → V}

/-- In an ultrametric group the weighted coefficient norms of the derivative are bounded by `ρ⁻¹`
times the shifted weighted coefficient norms of the series. -/
theorem norm_laurentDerivative_apply_mul_zpow_le (hρ : 0 < ρ) (n : ℤ) :
    ‖laurentDerivative S a n‖ * ρ ^ n ≤ ρ⁻¹ * (‖a (n + 1)‖ * ρ ^ (n + 1)) :=
  calc ‖laurentDerivative S a n‖ * ρ ^ n ≤ ‖a (n + 1)‖ * ρ ^ n :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_zsmul_le _ _) (by positivity)
    _ = ρ⁻¹ * (‖a (n + 1)‖ * ρ ^ (n + 1)) := by
        rw [zpow_add_one₀ hρ.ne']
        field_simp

/-- Over an ultrametric group the derivative of a series converging on the circle `|t| = ρ`
converges there too. -/
theorem LaurentConvergesAt.laurentDerivative (hρ : 0 < ρ) (ha : LaurentConvergesAt ρ a) :
    LaurentConvergesAt ρ (laurentDerivative S a) := by
  have h : Tendsto (fun n : ℤ ↦ ρ⁻¹ * (‖a (n + 1)‖ * ρ ^ (n + 1))) cofinite (𝓝 0) := by
    simpa using ((laurentConvergesAt_iff.1 ha).comp
      (add_left_injective 1).tendsto_cofinite).const_mul ρ⁻¹
  exact laurentConvergesAt_iff.2 <|
    squeeze_zero (fun n ↦ by positivity) (norm_laurentDerivative_apply_mul_zpow_le hρ) h

/-- Over an ultrametric group, `|f'|_ρ ≤ ρ⁻¹ |f|_ρ` for a family whose weighted norms are bounded
at `ρ`. -/
theorem laurentGaussNorm_laurentDerivative_le (hρ : 0 < ρ)
    (ha : BddAbove (Set.range fun n ↦ ‖a n‖ * ρ ^ n)) :
    laurentGaussNorm ρ (laurentDerivative S a) ≤ ρ⁻¹ * laurentGaussNorm ρ a :=
  laurentGaussNorm_le fun n ↦ (norm_laurentDerivative_apply_mul_zpow_le hρ n).trans <|
    mul_le_mul_of_nonneg_left (le_laurentGaussNorm ha (n + 1)) (by positivity)

end Ultrametric

/-! ### The termwise primitive -/

section Primitive

variable (K : Type*) {V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The termwise primitive `∑ aₙ tⁿ ↦ ∑_{n ≠ -1} aₙ tⁿ⁺¹ / (n + 1)` of a two-sided Laurent
coefficient family, with zero constant coefficient. Its coefficient at `n` is `n⁻¹ • aₙ₋₁`; since
`(0 : K)⁻¹ = 0`, the residue term `a₋₁ t⁻¹` is discarded. -/
noncomputable def laurentPrimitive : (ℤ → V) →ₗ[K] ℤ → V where
  toFun a n := (n : K)⁻¹ • a (n - 1)
  map_add' a b := by
    ext n
    simp [smul_add]
  map_smul' c a := by
    ext n
    simp [smul_smul, mul_comm]

variable {K}

@[simp]
theorem laurentPrimitive_apply (a : ℤ → V) (n : ℤ) :
    laurentPrimitive K a n = (n : K)⁻¹ • a (n - 1) :=
  (rfl)

/-- The primitive has zero constant coefficient. -/
theorem laurentPrimitive_apply_zero (a : ℤ → V) : laurentPrimitive K a 0 = 0 := by
  simp

/-- The primitive of the monomial `c tⁿ` is `(n + 1)⁻¹ c tⁿ⁺¹`; for `n = -1` it is zero. -/
@[simp]
theorem laurentPrimitive_single (n : ℤ) (c : V) :
    laurentPrimitive K (Pi.single n c) = Pi.single (n + 1) (((n : K) + 1)⁻¹ • c) := by
  ext m
  by_cases h : m = n + 1
  · subst m
    simp
  · have h' : m - 1 ≠ n := by omega
    simp [h, h']

variable [CharZero K]

/-- Differentiating the primitive removes exactly the residue term. -/
theorem laurentDerivative_laurentPrimitive (a : ℤ → V) :
    laurentDerivative K (laurentPrimitive K a) = a - Pi.single (-1) (a (-1)) := by
  ext n
  by_cases hn : n = -1
  · subst n
    simp
  · have hcast : (n : K) + 1 ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
    simp [hn, ← Int.cast_smul_eq_zsmul K, smul_smul, hcast]

/-- A family with zero residue is the derivative of its primitive. -/
theorem laurentDerivative_laurentPrimitive_of_apply_neg_one_eq_zero {a : ℤ → V}
    (ha : a (-1) = 0) : laurentDerivative K (laurentPrimitive K a) = a := by
  simp [laurentDerivative_laurentPrimitive, ha]

/-- Integrating a derivative removes exactly the constant term. -/
theorem laurentPrimitive_laurentDerivative (a : ℤ → V) :
    laurentPrimitive K (laurentDerivative K a) = a - Pi.single 0 (a 0) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · have hcast : (n : K) ≠ 0 := Int.cast_ne_zero.mpr hn
    simp [hn, ← Int.cast_smul_eq_zsmul K, smul_smul, hcast]

/-- The families with derivative `a` and constant coefficient `c` are exactly the family
`laurentPrimitive K a + Pi.single 0 c`, provided the residue of `a` vanishes. -/
theorem eq_laurentPrimitive_add_single_iff {a g : ℤ → V} (ha : a (-1) = 0) (c : V) :
    g = laurentPrimitive K a + Pi.single 0 c ↔ laurentDerivative K g = a ∧ g 0 = c := by
  constructor
  · rintro rfl
    simp [laurentDerivative_laurentPrimitive_of_apply_neg_one_eq_zero ha]
  · rintro ⟨rfl, rfl⟩
    rw [laurentPrimitive_laurentDerivative, sub_add_cancel]

end Primitive

/-! ### Convergence of the primitive -/

section Convergence

variable {K V : Type*} [NormedField K] [SeminormedAddCommGroup V] [NormedSpace K V]
  {a : ℤ → V}

/-- Weighted coefficient norm of the primitive at `ρ`, rewritten with a comparison radius `σ`:
the factor `‖n⁻¹‖ (ρ / σ)ⁿ` carries the denominators, and the shifted weighted norm of the series
at `σ` carries the decay. -/
private theorem norm_laurentPrimitive_apply_mul_zpow_eq {ρ σ : ℝ} (hσ : σ ≠ 0) (n : ℤ) :
    ‖laurentPrimitive K a n‖ * ρ ^ n =
      ‖(n : K)⁻¹‖ * (ρ / σ) ^ n * (‖a (n - 1)‖ * σ ^ (n - 1)) * σ := by
  rw [laurentPrimitive_apply, norm_smul, div_zpow, zpow_sub_one₀ hσ]
  field_simp

/-- **Convergence of the termwise primitive.** If a Laurent series converges on two circles
`|t| = ρ₁` and `|t| = ρ₂` with `0 < ρ₁ < ρ < ρ₂`, its termwise primitive converges on `|t| = ρ`.
The two auxiliary radii absorb the polynomial growth of `‖n⁻¹‖` at the two tails. -/
theorem LaurentConvergesAt.laurentPrimitive {ρ₁ ρ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (h₁ : ρ₁ < ρ)
    (h₂ : ρ < ρ₂) (ha₁ : LaurentConvergesAt ρ₁ a) (ha₂ : LaurentConvergesAt ρ₂ a) :
    LaurentConvergesAt ρ (laurentPrimitive K a) := by
  have hρ₂ : 0 < ρ₂ := hρ₁.trans (h₁.trans h₂)
  -- The shifted weighted norms `‖aₙ₋₁‖ σⁿ⁻¹` still tend to zero.
  have hshift {σ : ℝ} (hσ : LaurentConvergesAt σ a) :
      Tendsto (fun n : ℤ ↦ ‖a (n - 1)‖ * σ ^ (n - 1)) cofinite (𝓝 0) :=
    (laurentConvergesAt_iff.1 hσ).comp (sub_left_injective (b := (1 : ℤ))).tendsto_cofinite
  rw [laurentConvergesAt_iff, Int.cofinite_eq]
  refine Tendsto.sup ?_ ?_
  · -- At `-∞`, compare with the inner radius `ρ₁`, where `ρ / ρ₁ > 1`.
    have h := ((NormedField.tendsto_norm_inv_intCast_mul_zpow_atBot K
      ((one_lt_div hρ₁).2 h₁)).mul ((hshift ha₁).mono_left atBot_le_cofinite)).mul_const ρ₁
    simpa only [← norm_laurentPrimitive_apply_mul_zpow_eq hρ₁.ne', zero_mul] using h
  · -- At `+∞`, compare with the outer radius `ρ₂`, where `0 ≤ ρ / ρ₂ < 1`.
    have h := ((NormedField.tendsto_norm_inv_intCast_mul_zpow_atTop K
      (div_nonneg (hρ₁.trans h₁).le hρ₂.le) ((div_lt_one hρ₂).2 h₂)).mul
        ((hshift ha₂).mono_left atTop_le_cofinite)).mul_const ρ₂
    simpa only [← norm_laurentPrimitive_apply_mul_zpow_eq hρ₂.ne', zero_mul] using h

/-- The termwise primitive converges on the circle `|t| = ρ`, `ρ > 0`, when the series converges
on every circle of radius close to `ρ`. -/
theorem laurentConvergesAt_laurentPrimitive_of_eventually {ρ : ℝ} (hρ : 0 < ρ)
    (ha : ∀ᶠ σ in 𝓝 ρ, LaurentConvergesAt σ a) :
    LaurentConvergesAt ρ (laurentPrimitive K a) := by
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff.1 (ha.and (lt_mem_nhds hρ))
  have h₁ := @hP (ρ - ε / 2) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  have h₂ := @hP (ρ + ε / 2) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  exact h₁.1.laurentPrimitive h₁.2 (by linarith) (by linarith) h₂.1

variable [CharZero K]

/-- **Exactness of differentials on an annulus.** Let `I` be an open set of positive radii, such
as the radii `r < ρ < s` of an open annulus, and let `a` converge on every circle `|t| = ρ` with
`ρ ∈ I`. Then the differential `(∑ aₙ tⁿ) dt` has a primitive converging on the same circles if
and only if its residue `a₋₁` vanishes. -/
theorem exists_laurentDerivative_eq_iff {I : Set ℝ} (hI : IsOpen I) (hpos : I ⊆ Set.Ioi 0)
    (ha : ∀ ρ ∈ I, LaurentConvergesAt ρ a) :
    (∃ g : ℤ → V, (∀ ρ ∈ I, LaurentConvergesAt ρ g) ∧ laurentDerivative K g = a) ↔
      a (-1) = 0 := by
  refine ⟨fun ⟨g, _, hg⟩ ↦ hg ▸ laurentDerivative_apply_neg_one g, fun h ↦ ?_⟩
  refine ⟨laurentPrimitive K a, fun ρ hρ ↦ ?_,
    laurentDerivative_laurentPrimitive_of_apply_neg_one_eq_zero h⟩
  exact laurentConvergesAt_laurentPrimitive_of_eventually (hpos hρ)
    (eventually_of_mem (hI.mem_nhds hρ) ha)

/-- **Uniqueness of primitives on an annulus.** On an open set `I` of positive radii, a convergent
Laurent series with zero residue has exactly one primitive converging on the circles of radius in
`I` with a prescribed constant coefficient `c`: two primitives differ by a constant. -/
theorem existsUnique_laurentDerivative_eq {I : Set ℝ} (hI : IsOpen I) (hpos : I ⊆ Set.Ioi 0)
    (ha : ∀ ρ ∈ I, LaurentConvergesAt ρ a) (h : a (-1) = 0) (c : V) :
    ∃! g : ℤ → V, (∀ ρ ∈ I, LaurentConvergesAt ρ g) ∧ laurentDerivative K g = a ∧ g 0 = c := by
  refine ⟨laurentPrimitive K a + Pi.single 0 c, ⟨fun ρ hρ ↦ ?_,
    (eq_laurentPrimitive_add_single_iff h c).1 rfl⟩, fun g hg ↦
      (eq_laurentPrimitive_add_single_iff h c).2 hg.2⟩
  exact (laurentConvergesAt_laurentPrimitive_of_eventually (hpos hρ)
    (eventually_of_mem (hI.mem_nhds hρ) ha)).add (laurentConvergesAt_single ρ 0 c)

end Convergence

end TauCeti
