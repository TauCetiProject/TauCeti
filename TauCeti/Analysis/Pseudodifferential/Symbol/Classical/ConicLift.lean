/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.ConicLift

/-!
# Lifting a classical symbol to a product, cut off near an axis

Let `P : ℝᴺ → ℝⁿ` be linear, for instance the projection of a product `ℝᴺ = ℝⁿ × ℝⁿ'` onto a
factor. A symbol `p(x, ξ)` of order `m` on `ℝⁿ` lifts to the symbol

`c(ξ) p(P x, P ξ)`,  `c(ξ) = 1 - φ(ξ / R) (1 - χ(‖P ξ‖² / (ε² ‖ξ‖²)))`

of order `m` on `ℝᴺ` (`TauCeti.Symbol.conicLift`), for a conic cutoff `χ`
(`TauCeti.ConicCutoff`), a frequency cutoff `φ`, `ε ≠ 0` and `R ≥ 1`. The cutoff `c` removes a
small cone around the axis `P ξ = 0`, where `p(P x, P ξ)` is not a symbol on the product, and
keeps `p` at bounded frequencies. This file shows that **the lift of a classical symbol is
classical** (`TauCeti.ClassicalSymbol.conicLift`).

At frequencies `‖ξ‖ ≥ 2 R` the cutoff `c` is the angular factor `χ(‖P ξ‖² / (ε² ‖ξ‖²))`
(`TauCeti.conicLiftCutoff_eq_of_two_mul_le_norm`), which is homogeneous of degree `0`. So the
homogeneous terms of the lift are the cut-off terms

`χ(‖P ξ‖² / (ε² ‖ξ‖²)) a_{m-j}(P x, P ξ)`

of the homogeneous terms `a_{m-j}` of `p` (`TauCeti.HomogeneousSymbol.conicLift`). Each of them is
smooth away from `ξ = 0` although `a_{m-j}(P x, P ξ)` is singular along the whole axis
`P ξ = 0`, since the angular factor vanishes on the cone `‖P ξ‖² ≤ ε² ‖ξ‖² / 4` around it
(`TauCeti.HomogeneousSymbol.coefficient_conicLift_of_le_div_four`). On the remaining cone
`‖P ξ‖² ≥ ε² ‖ξ‖² / 2` every term is the corresponding term of `p` read through `P`
(`TauCeti.HomogeneousSymbol.coefficient_conicLift_of_le`); in particular the principal symbol of
the lift is the lift of the principal symbol (`TauCeti.ClassicalSymbol.principal_conicLift`).

## The remainders

Write `p = ∑_{j<K} ψ(ξ) a_{m-j} + r` on `ℝⁿ`, with a frequency cutoff `ψ` and a remainder `r` of
order `m - K`. Lifting is linear in `p`, so the lift of `p` is the lift of `r`, a symbol of order
`m - K` on `ℝᴺ`, plus the lifts of the cut-off terms `ψ(ξ) a_{m-j}`. At frequencies `ξ` that are
large compared with `R` and `ε⁻¹`, the lift of `ψ(ξ) a_{m-j}` agrees with the cut-off term
`φ(ξ) χ(‖P ξ‖² / (ε² ‖ξ‖²)) a_{m-j}(P x, P ξ)` on `ℝᴺ`: where the angular factor does not vanish,
`‖P ξ‖ ≥ |ε| ‖ξ‖ / 2` is large, so that `ψ(P ξ) = 1`. Hence the two differ by a smoothing
symbol, and the remainder of the lift after `K` terms has order `m - K`.

## Main declarations

* `TauCeti.HomogeneousSymbol.conicLift`: the lifted homogeneous symbol
  `χ(‖P ξ‖² / (ε² ‖ξ‖²)) a(P x, P ξ)` on `ℝᴺ`, of the same degree.
* `TauCeti.HomogeneousSymbol.coefficient_conicLift_of_le`,
  `TauCeti.HomogeneousSymbol.coefficient_conicLift_of_le_div_four`: it is `a(P x, P ξ)` on the cone
  `‖P ξ‖² ≥ ε² ‖ξ‖² / 2`, and vanishes on the cone `‖P ξ‖² ≤ ε² ‖ξ‖² / 4` around the axis.
* `TauCeti.HomogeneousSymbol.exists_norm_coefficient_conicLift_sub_le`: for degree `m ≥ 0` it is
  within `C ε ^ m ‖ξ‖ ^ m` of `a(P x, P ξ)` over a compact set of positions, uniformly in the
  cutoff and in `ε`.
* `TauCeti.HomogeneousSymbol.adjoint_conicLift`: lifting commutes with pointwise adjoints, so a
  symbol and its adjoint are cut off by the same angular factor.
* `TauCeti.ClassicalSymbol.conicLift`: the lift of a classical symbol of order `m` on `ℝⁿ`, a
  classical symbol of order `m` on `ℝᴺ` with full symbol `TauCeti.Symbol.conicLift`
  (`TauCeti.ClassicalSymbol.toSymbol_conicLift`) and homogeneous terms the lifted terms
  (`TauCeti.ClassicalSymbol.term_conicLift`).
* `TauCeti.ClassicalSymbol.principal_conicLift`: its principal symbol is the lifted principal
  symbol.
* `TauCeti.ClassicalSymbol.conicLift_zero`, `TauCeti.ClassicalSymbol.conicLift_add`,
  `TauCeti.ClassicalSymbol.conicLift_smul`: the lift is linear.

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968), §9,
  pp. 526–530 (the external product of elliptic operators on a product).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1 (classical
  symbols and their asymptotic expansions).
-/

public section

noncomputable section

open Filter Topology
open scoped ContDiff

namespace TauCeti

variable {N n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ} (P : CoordinateSpace N →L[ℝ] CoordinateSpace n) (χ : ConicCutoff)

/-! ### Lifting a homogeneous symbol -/

namespace HomogeneousSymbol

/-- **The lift of a homogeneous symbol to a product, cut off near an axis.** For a linear map
`P : ℝᴺ → ℝⁿ` and a homogeneous symbol `a` of degree `m` on `ℝⁿ`, the homogeneous symbol
`χ(‖P ξ‖² / (ε² ‖ξ‖²)) a(P x, P ξ)` of degree `m` on `ℝᴺ`. The angular factor vanishes on the cone
`‖P ξ‖² ≤ ε² ‖ξ‖² / 4` around the axis `P ξ = 0`, where `a(P x, P ξ)` need not be smooth, and
equals `1` on the cone `‖P ξ‖² ≥ ε² ‖ξ‖² / 2`. These are the homogeneous terms of the lift of a
classical symbol (`TauCeti.ClassicalSymbol.conicLift`). -/
def conicLift (ε : ℝ) (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    HomogeneousSymbol (CoordinateSpace N) (CoordinateSpace N) V W m where
  coefficient q := χ (‖P q.2‖ ^ 2 / (ε ^ 2 * ‖q.2‖ ^ 2)) • a.coefficient (P q.1, P q.2)
  zero_covector _ := by simp
  contDiffOn_coefficient := by
    rcases eq_or_ne ε 0 with rfl | hε
    · -- For `ε = 0` the ratio is `x / 0 = 0`, and the coefficient vanishes identically.
      exact (contDiffOn_const (c := (0 : V →L[ℂ] W))).congr fun q _ ↦ by simp
    · exact (χ.contDiffOn_smul (P.contDiff.comp contDiff_fst) (P.contDiff.comp contDiff_snd)
        (contDiff_const.mul ((contDiff_norm_sq ℝ).comp contDiff_snd))
        a.contDiffOn_coefficient).mono fun q (hq : q.2 ≠ 0) ↦
          (by positivity : ε ^ 2 * ‖q.2‖ ^ 2 ≠ 0)
  homogeneous x ξ t ht := by
    rw [map_smul, a.homogeneous _ _ t ht, norm_smul, norm_smul, Real.norm_of_nonneg ht.le,
      mul_pow, mul_pow, mul_left_comm, mul_div_mul_left _ _ (pow_ne_zero 2 ht.ne')]
    exact smul_comm _ _ _

variable {ε : ℝ}

@[simp]
theorem coefficient_conicLift
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    (q : CoordinateSpace N × CoordinateSpace N) :
    (a.conicLift P χ ε).coefficient q =
      χ (‖P q.2‖ ^ 2 / (ε ^ 2 * ‖q.2‖ ^ 2)) • a.coefficient (P q.1, P q.2) :=
  (rfl)

@[simp]
theorem conicLift_zero :
    (0 : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m).conicLift P χ ε = 0 :=
  HomogeneousSymbol.ext (funext fun q ↦ by simp)

@[simp]
theorem conicLift_add (a b : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    (a + b).conicLift P χ ε = a.conicLift P χ ε + b.conicLift P χ ε :=
  HomogeneousSymbol.ext (funext fun q ↦ by simp [smul_add])

@[simp]
theorem conicLift_smul (c : ℂ)
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    (c • a).conicLift P χ ε = c • a.conicLift P χ ε :=
  HomogeneousSymbol.ext (funext fun q ↦ by simp [smul_comm _ c])

/-- Lifting commutes with taking pointwise adjoints, since the angular factor is real. -/
@[simp]
theorem adjoint_conicLift {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    (a.conicLift P χ ε).adjoint = a.adjoint.conicLift P χ ε :=
  HomogeneousSymbol.ext (funext fun q ↦ by
    simp only [coefficient_adjoint, coefficient_conicLift, ← Complex.coe_smul,
      ContinuousLinearMap.adjoint.map_smulₛₗ, Complex.conj_ofReal])

variable {P χ}

/-- On the cone `‖P ξ‖² ≥ ε² ‖ξ‖² / 2` the lifted homogeneous symbol is `a(P x, P ξ)`. -/
theorem coefficient_conicLift_of_le (hε : ε ≠ 0)
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) (x : CoordinateSpace N)
    {ξ : CoordinateSpace N} (hξ : ε ^ 2 * ‖ξ‖ ^ 2 / 2 ≤ ‖P ξ‖ ^ 2) :
    (a.conicLift P χ ε).coefficient (x, ξ) = a.coefficient (P x, P ξ) := by
  rcases eq_or_ne ξ 0 with rfl | hξ0
  · simp
  have hpos : 0 < ε ^ 2 * ‖ξ‖ ^ 2 := by positivity
  rw [coefficient_conicLift,
    χ.apply_eq_one_of_one_div_two_le (by rw [le_div_iff₀ hpos]; linarith), one_smul]

/-- On the cone `‖P ξ‖² ≤ ε² ‖ξ‖² / 4` around the axis `P ξ = 0` the lifted homogeneous symbol
vanishes. -/
theorem coefficient_conicLift_of_le_div_four
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) (x : CoordinateSpace N)
    {ξ : CoordinateSpace N} (hξ : ‖P ξ‖ ^ 2 ≤ ε ^ 2 * ‖ξ‖ ^ 2 / 4) :
    (a.conicLift P χ ε).coefficient (x, ξ) = 0 := by
  rw [coefficient_conicLift, χ.apply_eq_zero_of_le_one_div_four, zero_smul]
  rcases (show 0 ≤ ε ^ 2 * ‖ξ‖ ^ 2 by positivity).eq_or_lt with h | h
  · rw [← h, div_zero]
    norm_num
  · rw [div_le_iff₀ h]
    linarith

/-- **The lifted homogeneous symbol is close to `a(P x, P ξ)`.** For `m ≥ 0` and a compact set `K`
of positions there is a constant `C` such that

`‖χ(‖P ξ‖² / (ε² ‖ξ‖²)) a(P x, P ξ) - a(P x, P ξ)‖ ≤ C ε ^ m ‖ξ‖ ^ m`

for every conic cutoff `χ`, every `ε > 0`, every `x ∈ K` and every `ξ`. The two differ only where
`‖P ξ‖² < ε² ‖ξ‖² / 2`, where `‖a(P x, P ξ)‖ ≤ C ‖P ξ‖ ^ m ≤ C ε ^ m ‖ξ‖ ^ m`. On the unit sphere
this is a bound `C ε ^ m` uniform in the cutoff. -/
theorem exists_norm_coefficient_conicLift_sub_le (hm : 0 ≤ m)
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    {K : Set (CoordinateSpace N)} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ (χ : ConicCutoff) {ε : ℝ}, 0 < ε → ∀ x ∈ K, ∀ ξ,
      ‖(a.conicLift P χ ε).coefficient (x, ξ) - a.coefficient (P x, P ξ)‖ ≤
        C * ε ^ m * ‖ξ‖ ^ m := by
  obtain ⟨C, hC0, hC⟩ := a.exists_norm_coefficient_le (hK.image P.continuous)
  refine ⟨C, hC0, fun χ ε hε x hx ξ ↦ ?_⟩
  rcases le_or_gt (ε ^ 2 * ‖ξ‖ ^ 2 / 2) (‖P ξ‖ ^ 2) with hcone | hcone
  · rw [coefficient_conicLift_of_le hε.ne' a x hcone, sub_self, norm_zero]
    positivity
  -- Off the cone, `‖P ξ‖ ≤ ε ‖ξ‖`, and the difference is `(χ(…) - 1) a(P x, P ξ)`.
  have hPξ : ‖P ξ‖ ≤ ε * ‖ξ‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1
      (by rw [mul_pow]; nlinarith [sq_nonneg (ε * ‖ξ‖)])
  set t := χ (‖P ξ‖ ^ 2 / (ε ^ 2 * ‖ξ‖ ^ 2))
  have ht : ‖t - 1‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [χ.nonneg (‖P ξ‖ ^ 2 / (ε ^ 2 * ‖ξ‖ ^ 2)),
      χ.le_one (‖P ξ‖ ^ 2 / (ε ^ 2 * ‖ξ‖ ^ 2))]
  calc ‖(a.conicLift P χ ε).coefficient (x, ξ) - a.coefficient (P x, P ξ)‖
      = ‖t - 1‖ * ‖a.coefficient (P x, P ξ)‖ := by
        rw [coefficient_conicLift, ← norm_smul, sub_smul, one_smul]
    _ ≤ 1 * (C * ‖P ξ‖ ^ m) :=
        mul_le_mul ht (hC _ ⟨x, hx, rfl⟩ _) (norm_nonneg _) zero_le_one
    _ ≤ C * ε ^ m * ‖ξ‖ ^ m := by
        rw [one_mul, mul_assoc, ← Real.mul_rpow hε.le (norm_nonneg _)]
        gcongr

end HomogeneousSymbol

/-! ### Lifting a classical symbol -/

namespace ClassicalSymbol

variable (φ : FrequencyCutoff (CoordinateSpace N)) {ε R : ℝ}

/-- At frequencies that are large compared with `R` and `ε⁻¹`, the lift of a cut-off term
`ψ(ξ) a(x, ξ)` on `ℝⁿ` is the cut-off term `φ(ξ) χ(‖P ξ‖² / (ε² ‖ξ‖²)) a(P x, P ξ)` of the lifted
homogeneous symbol on `ℝᴺ`. Where the angular factor does not vanish, `‖P ξ‖ ≥ 2`, so that
`ψ(P ξ) = 1`. -/
private theorem coefficient_conicLift_cutoffSymbol (hε : ε ≠ 0) (hR : 1 ≤ R)
    (ψ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    (x ξ : CoordinateSpace N) (hξ : max (2 * R) (max 2 (4 / |ε|)) ≤ ‖ξ‖) :
    ((HomogeneousSymbol.cutoffSymbol ψ a).conicLift P χ φ hε hR).coefficient (x, ξ) =
      (HomogeneousSymbol.cutoffSymbol φ (a.conicLift P χ ε)).coefficient (x, ξ) := by
  have h2R : 2 * R ≤ ‖ξ‖ := (le_max_left _ _).trans hξ
  have h2 : 2 ≤ ‖ξ‖ := ((le_max_left _ _).trans (le_max_right _ _)).trans hξ
  have h4 : 4 / |ε| ≤ ‖ξ‖ := ((le_max_right _ _).trans (le_max_right _ _)).trans hξ
  rw [Symbol.coefficient_conicLift, conicLiftCutoff_eq_of_two_mul_le_norm (one_pos.trans_le hR) h2R,
    HomogeneousSymbol.coefficient_cutoffSymbol, HomogeneousSymbol.coefficient_cutoffSymbol,
    φ.apply_eq_one_of_two_le_norm h2, one_smul, HomogeneousSymbol.coefficient_conicLift,
    Complex.coe_smul]
  rcases eq_or_ne (χ (‖P ξ‖ ^ 2 / (ε ^ 2 * ‖ξ‖ ^ 2))) 0 with h0 | h0
  · rw [h0, zero_smul, zero_smul]
  -- The angular factor does not vanish, so `‖P ξ‖² > ε² ‖ξ‖² / 4 ≥ 4`.
  have hlt : 1 / 4 < ‖P ξ‖ ^ 2 / (ε ^ 2 * ‖ξ‖ ^ 2) :=
    lt_of_not_ge fun h ↦ h0 (χ.apply_eq_zero_of_le_one_div_four h)
  have hεξ : 4 ≤ |ε| * ‖ξ‖ := by
    rwa [div_le_iff₀ (abs_pos.2 hε), mul_comm] at h4
  have hpos : 0 < ε ^ 2 * ‖ξ‖ ^ 2 := by
    have : ξ ≠ 0 := norm_pos_iff.1 (by linarith)
    positivity
  rw [lt_div_iff₀ hpos] at hlt
  have hsq : 16 ≤ ε ^ 2 * ‖ξ‖ ^ 2 := by
    have h := mul_self_le_mul_self (by norm_num) hεξ
    rw [← sq_abs ε]
    nlinarith
  have hP : 2 ≤ ‖P ξ‖ := by
    nlinarith [norm_nonneg (P ξ)]
  rw [ψ.apply_eq_one_of_two_le_norm hP, one_smul]

/-- The lift of a cut-off term and the cut-off lifted term differ by a smoothing symbol. -/
private theorem isSmoothing_conicLift_cutoffSymbol_sub (hε : ε ≠ 0) (hR : 1 ≤ R)
    (ψ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    ((HomogeneousSymbol.cutoffSymbol ψ a).conicLift P χ φ hε hR -
      HomogeneousSymbol.cutoffSymbol φ (a.conicLift P χ ε)).IsSmoothing :=
  Symbol.isSmoothing_of_coefficient_eq_zero _ fun x ξ hξ ↦ by
    rw [Symbol.coefficient_sub, Pi.sub_apply,
      coefficient_conicLift_cutoffSymbol P χ φ hε hR ψ a x ξ hξ, sub_self]

/-- **The lift of a classical symbol to a product, cut off near an axis, is classical.** For a
linear map `P : ℝᴺ → ℝⁿ`, for instance the projection of a product onto a factor, and a classical
symbol `a` of order `m` on `ℝⁿ`, the classical symbol of order `m` on `ℝᴺ` whose full symbol is the
lift `c(ξ) a(P x, P ξ)` (`TauCeti.Symbol.conicLift`) and whose homogeneous terms are the lifted
terms `χ(‖P ξ‖² / (ε² ‖ξ‖²)) a_{m-j}(P x, P ξ)` (`TauCeti.HomogeneousSymbol.conicLift`), for
`ε ≠ 0` and `R ≥ 1`. -/
def conicLift (hε : ε ≠ 0) (hR : 1 ≤ R) (a : ClassicalSymbol n V W m) :
    ClassicalSymbol N V W m where
  toSymbol := a.toSymbol.conicLift P χ φ hε hR
  term j := (a.term j).conicLift P χ ε
  exists_remainder' := by
    obtain ⟨ψ, h⟩ := a.exists_remainder'
    refine ⟨φ, fun K ↦ ?_⟩
    -- The lift of the remainder of `a`, plus the smoothing differences between the lifts of the
    -- cut-off terms of `a` and the cut-off lifted terms.
    obtain ⟨r, hr⟩ := h K
    choose s hs using fun j : ℕ ↦ Symbol.isSmoothing_iff.1
      (isSmoothing_conicLift_cutoffSymbol_sub P χ φ hε hR ψ (a.term j)) (m - K)
    refine ⟨r.conicLift P χ φ hε hR + ∑ j ∈ Finset.range K, s j, fun q ↦ ?_⟩
    simp only [Symbol.coefficient_add, Pi.add_apply, Symbol.coefficient_sum, Finset.sum_apply, hs,
      Symbol.coefficient_sub, Pi.sub_apply, Symbol.coefficient_conicLift, hr,
      HomogeneousSymbol.coefficient_cutoffSymbol, smul_sub, Finset.smul_sum,
      Finset.sum_sub_distrib]
    abel

@[simp]
theorem toSymbol_conicLift (hε : ε ≠ 0) (hR : 1 ≤ R) (a : ClassicalSymbol n V W m) :
    (a.conicLift P χ φ hε hR).toSymbol = a.toSymbol.conicLift P χ φ hε hR :=
  (rfl)

@[simp]
theorem term_conicLift (hε : ε ≠ 0) (hR : 1 ≤ R) (a : ClassicalSymbol n V W m) (j : ℕ) :
    (a.conicLift P χ φ hε hR).term j = (a.term j).conicLift P χ ε :=
  (rfl)

@[simp]
theorem conicLift_zero (hε : ε ≠ 0) (hR : 1 ≤ R) :
    (0 : ClassicalSymbol n V W m).conicLift P χ φ hε hR = 0 :=
  ClassicalSymbol.ext (Symbol.ext (funext fun q ↦ by simp))

@[simp]
theorem conicLift_add (hε : ε ≠ 0) (hR : 1 ≤ R) (a b : ClassicalSymbol n V W m) :
    (a + b).conicLift P χ φ hε hR = a.conicLift P χ φ hε hR + b.conicLift P χ φ hε hR :=
  ClassicalSymbol.ext (Symbol.ext (funext fun q ↦ by simp [smul_add]))

@[simp]
theorem conicLift_smul (hε : ε ≠ 0) (hR : 1 ≤ R) (c : ℂ) (a : ClassicalSymbol n V W m) :
    (c • a).conicLift P χ φ hε hR = c • a.conicLift P χ φ hε hR :=
  ClassicalSymbol.ext (Symbol.ext (funext fun q ↦ by simp [smul_comm _ c]))

/-- **The principal symbol of the lift is the lifted principal symbol**
`χ(‖P ξ‖² / (ε² ‖ξ‖²)) σ(a)(P x, P ξ)`. -/
@[simp]
theorem principal_conicLift (hε : ε ≠ 0) (hR : 1 ≤ R) (a : ClassicalSymbol n V W m) :
    (a.conicLift P χ φ hε hR).principal = a.principal.conicLift P χ ε :=
  HomogeneousSymbol.ext (funext fun q ↦ by simp [coefficient_principal])

end ClassicalSymbol

end TauCeti
