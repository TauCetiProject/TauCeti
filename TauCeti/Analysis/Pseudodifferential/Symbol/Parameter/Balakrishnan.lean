/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.StrictPositivity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical.HomogeneousAbove
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.AsymptoticSum
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Contour
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Homogeneous
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.TruncatedParametrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

/-!
# Balakrishnan integrals of parameter-dependent symbols

For a strictly positive operator `A` and `0 < σ < 1`, Balakrishnan's formula writes the negative
power `A^{-σ}` as an integral of the resolvent along the negative real axis,

`A^{-σ} = (sin (π σ) / π) ∫₀^∞ t ^ (-σ) (A + t)⁻¹ dt`

(`CFC.rpow_neg_eq_integral_ringInverse_add` for bounded `A`,
`LinearPMap.negPow_eq_integral_resolvent` for operators with compact resolvent). It is Seeley's
contour integral `(i / 2π) ∫_Γ λ ^ (-σ) (A - λ)⁻¹ dλ` around the spectrum, collapsed onto the cut.
Replacing the resolvent by a strongly parameter-dependent symbol `b((x, ξ), λ)`
(`TauCeti.ParameterSymbol`) of order `m`, for instance a parametrix of `A - λ` (of order `-2` for
an operator `A` of order `2`), gives the symbol

`(x, ξ) ↦ (sin (π σ) / π) ∫₀^∞ t ^ (-σ) b((x, ξ), -t) dt`

(`TauCeti.ParameterSymbol.balakrishnanIntegral`). It is a symbol of order `m - 2 σ + 2`, the
spectral parameter counting as two frequency orders, as soon as `σ < 1`, `m - 2 σ + 2 < 0` and the
closed negative real axis lies in the set `Λ` of spectral parameters. This is the contour integral
`TauCeti.ParameterSymbol.contourIntegral` along the path `t ↦ -|t|` with the weight `t ^ (-σ)` on
`t > 0`, which has an integrable singularity at `t = 0`.

At a point `(x, ξ)` where the symbol is the inverse of `A + t` along the axis, `A` a strictly
positive operator on a complex Hilbert space `V`, the integral is the power `A ^ (-σ)` of the
continuous functional calculus (`TauCeti.ParameterSymbol.coefficient_balakrishnanIntegral_eq_rpow`).
So for a symbol `a` elliptic with parameter whose values along the axis are
`a((x, ξ), -t) = A + t` with `A` strictly positive, the integral of the inverse symbol `a⁻¹` is the
pointwise power `A ^ (-σ)` (`TauCeti.ParameterSymbol.coefficient_balakrishnanIntegral_inverse`),
and the integral of a truncated right parametrix `Bₙ` of `a` with at least one term
(`TauCeti.ParameterSymbol.rightParametrix`) is `A ^ (-σ)` up to a symbol of order
`-m - 2 σ + 1`, one order lower
(`TauCeti.ParameterSymbol.exists_coefficient_balakrishnanIntegral_rightParametrix_eq_rpow_add`).
For `m = 2` this identifies the leading term of Seeley's symbol of the power `A^{-σ}`, of order
`-2 σ`, with the pointwise power of the full symbol wherever the latter is strictly positive. The
comparison of the quantization of this symbol with the spectral power of an operator is not made
here.
For the shifted Laplacian `s - Δ`, `s > 0`, the integral of its resolvent symbol is the Fourier
multiplier `(s + ‖ξ‖²) ^ (-σ)`
(`TauCeti.ParameterSymbol.coefficient_balakrishnanIntegral_inverse_shiftedLaplacian`); the
symbol of `s - Δ - z` is elliptic with parameter near the closed negative real axis
(`TauCeti.ParameterSymbol.isElliptic_shiftedLaplacian_of_re_le`).

**Classical expansions.** Since the spectral parameter counts as two frequency orders, the
substitution `t ↦ s² t` turns quasi-homogeneity of `b` under `(ξ, λ) ↦ (s ξ, s² λ)` into
homogeneity of its integral in `ξ`: if `b` is quasi-homogeneous of degree `μ` at frequencies of norm
at least `R` (`TauCeti.ParameterSymbol.IsQuasiHomogeneousAbove`), its integral is homogeneous of
degree `μ - 2 σ + 2` there
(`TauCeti.ParameterSymbol.IsQuasiHomogeneousAbove.isHomogeneousAbove_balakrishnanIntegral`).
Hence if `b ∼ ∑ⱼ bⱼ` is an asymptotic expansion into terms `bⱼ` of orders `m - j`, each
quasi-homogeneous of degree `m - j` at large frequencies, as are the terms of Seeley's resolvent
parametrix, the integral of `b` is a classical symbol of order `m - 2 σ + 2`, whose homogeneous
terms are the integrals of the `bⱼ` at large frequencies
(`TauCeti.ParameterSymbol.classicalBalakrishnanIntegral`). Where `b₀` inverts `A + t` along the
axis, its principal symbol is `A ^ (-σ)`
(`TauCeti.ParameterSymbol.coefficient_principal_classicalBalakrishnanIntegral_eq_rpow`).

## Main declarations

* `TauCeti.ParameterSymbol.balakrishnanIntegral`: the symbol
  `(x, ξ) ↦ (sin (π σ) / π) ∫₀^∞ t ^ (-σ) b((x, ξ), -t) dt` of order `m - 2 σ + 2`, with
  `TauCeti.ParameterSymbol.coefficient_balakrishnanIntegral` for its coefficient. It is linear in
  the parameter-dependent symbol (`TauCeti.ParameterSymbol.balakrishnanIntegralₗ`) and commutes
  with the order inclusions.
* `TauCeti.ParameterSymbol.coefficient_balakrishnanIntegral_eq_rpow`: the integral of a left
  inverse of `A + t` along the axis is `A ^ (-σ)`.
* `TauCeti.ParameterSymbol.coefficient_balakrishnanIntegral_inverse`: the integral of the inverse
  of a symbol `a` elliptic with parameter, equal to `A + t` along the axis, is `A ^ (-σ)`.
* `TauCeti.ParameterSymbol.exists_coefficient_balakrishnanIntegral_rightParametrix_eq_rpow_add`:
  the integral of a truncated right parametrix is `A ^ (-σ)` up to one fixed symbol of lower
  order.
* `TauCeti.ParameterSymbol.coefficient_balakrishnanIntegral_inverse_shiftedLaplacian`: the
  integral of the resolvent symbol of `s - Δ` is `(s + ‖ξ‖²) ^ (-σ)`.
* `TauCeti.ParameterSymbol.IsQuasiHomogeneousAbove.isHomogeneousAbove_balakrishnanIntegral`: the
  integral of a symbol quasi-homogeneous at large frequencies is homogeneous there.
* `TauCeti.ParameterSymbol.classicalBalakrishnanIntegral`: the integral of a quasi-homogeneous
  expansion as a classical symbol, with its homogeneous terms
  (`TauCeti.ParameterSymbol.coefficient_term_classicalBalakrishnanIntegral`) and principal symbol
  (`TauCeti.ParameterSymbol.coefficient_principal_classicalBalakrishnanIntegral`,
  `TauCeti.ParameterSymbol.coefficient_principal_classicalBalakrishnanIntegral_eq_rpow`).

## References

* A. V. Balakrishnan, *Fractional powers of closed operators and the semigroups generated by
  them*, Pacific J. Math. 10 (1960), 419–437.
* R. T. Seeley, *Complex powers of an elliptic operator*, Proc. Sympos. Pure Math. 10 (1967),
  288–307.
* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, Chapter II, §§10–11.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace ParameterSymbol

/-! ### The integral along the negative real axis -/

section Integral

variable {n : ℕ} {Λ : TopologicalSpace.Opens ℂ} {V W : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m σ : ℝ}

/-- The path `t ↦ -|t|` runs through the closed negative real axis. -/
private theorem continuous_neg_abs : Continuous fun t : ℝ ↦ -((|t| : ℝ) : ℂ) := by
  fun_prop

private theorem neg_abs_mem (hΛ : ∀ t : ℝ, t ≤ 0 → (t : ℂ) ∈ Λ) (t : ℝ) :
    -((|t| : ℝ) : ℂ) ∈ Λ := by
  simpa using hΛ (-|t|) (neg_nonpos.2 (abs_nonneg t))

private theorem exists_one_add_abs_le_neg_abs :
    ∃ c, ∀ t : ℝ, 1 + |t| ≤ c * (1 + ‖-((|t| : ℝ) : ℂ)‖) :=
  ⟨1, fun t ↦ by simp⟩

/-- The weight `t ^ (-σ)` on `t > 0`, extended by `0`. -/
private theorem aestronglyMeasurable_indicator_rpow (σ : ℝ) :
    AEStronglyMeasurable (Set.indicator (Ioi 0) fun t : ℝ ↦ ((t ^ (-σ) : ℝ) : ℂ)) :=
  ((by fun_prop : Measurable fun t : ℝ ↦ ((t ^ (-σ) : ℝ) : ℂ)).indicator
    measurableSet_Ioi).aestronglyMeasurable

private theorem exists_norm_indicator_rpow_le (σ : ℝ) :
    ∃ C, ∀ t : ℝ, ‖Set.indicator (Ioi 0) (fun t : ℝ ↦ ((t ^ (-σ) : ℝ) : ℂ)) t‖ ≤
      C * (|t| ^ (-σ) + (1 + |t|) ^ (-σ)) := by
  refine ⟨1, fun t ↦ ?_⟩
  rcases lt_or_ge 0 t with ht | ht
  · rw [indicator_of_mem (mem_Ioi.2 ht), Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), abs_of_pos ht, one_mul]
    exact le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)
  · rw [indicator_of_notMem (notMem_Ioi.2 ht), norm_zero, one_mul]
    positivity

variable (hΛ : ∀ t : ℝ, t ≤ 0 → (t : ℂ) ∈ Λ) (hσ : σ < 1)

section

variable (hm : m - 2 * σ + 2 < 0)

/-- **The Balakrishnan integral of a parameter-dependent symbol.** For a parameter-dependent
symbol `b` of order `m` whose set of spectral parameters contains the closed negative real axis,
and `σ < 1` with `m - 2 σ + 2 < 0`, the symbol

`(x, ξ) ↦ (sin (π σ) / π) ∫₀^∞ t ^ (-σ) b((x, ξ), -t) dt`

of order `m - 2 σ + 2` (`TauCeti.ParameterSymbol.coefficient_balakrishnanIntegral`). For a
resolvent parametrix `b` of an operator `A` of order `2` (so `m = -2`) and `0 < σ < 1`, it is the
symbol-level analogue of Balakrishnan's resolvent integral for the negative power `A ^ (-σ)`, of
order `-2 σ`. Pointwise, where `b` inverts `A + t` along the axis, it is the power `A ^ (-σ)`
(`TauCeti.ParameterSymbol.coefficient_balakrishnanIntegral_eq_rpow`,
`TauCeti.ParameterSymbol.coefficient_balakrishnanIntegral_inverse`). -/
def balakrishnanIntegral (b : ParameterSymbol n Λ V W m) : Symbol n V W (m - 2 * σ + 2) :=
  Symbol.inclusion (le_of_eq (by ring)) (((Real.sin (Real.pi * σ) / Real.pi : ℝ) : ℂ) •
    b.contourIntegral continuous_neg_abs (neg_abs_mem hΛ) (aestronglyMeasurable_indicator_rpow σ)
      exists_one_add_abs_le_neg_abs (exists_norm_indicator_rpow_le σ) (by linarith)
      (by linarith))

/-- The coefficient of the Balakrishnan integral:
`(sin (π σ) / π) ∫₀^∞ t ^ (-σ) b((x, ξ), -t) dt`. -/
@[simp]
theorem coefficient_balakrishnanIntegral (b : ParameterSymbol n Λ V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (b.balakrishnanIntegral hΛ hσ hm).coefficient p = (Real.sin (Real.pi * σ) / Real.pi) •
      ∫ t in Ioi (0 : ℝ), t ^ (-σ) • b.coefficient (p, -(t : ℂ)) := by
  simp only [balakrishnanIntegral, Symbol.coefficient_inclusion, Symbol.coefficient_smul,
    Pi.smul_apply, coefficient_contourIntegral]
  rw [← integral_indicator measurableSet_Ioi, Complex.coe_smul]
  congr 1
  refine integral_congr_ae (.of_forall fun t ↦ ?_)
  dsimp only
  rcases lt_or_ge 0 t with ht | ht
  · rw [indicator_of_mem (mem_Ioi.2 ht), indicator_of_mem (mem_Ioi.2 ht),
      abs_of_pos ht, Complex.coe_smul]
  · rw [indicator_of_notMem (notMem_Ioi.2 ht),
      indicator_of_notMem (notMem_Ioi.2 ht), zero_smul]

@[simp]
theorem balakrishnanIntegral_zero :
    (0 : ParameterSymbol n Λ V W m).balakrishnanIntegral hΛ hσ hm = 0 := by
  simp [balakrishnanIntegral]

@[simp]
theorem balakrishnanIntegral_add (b c : ParameterSymbol n Λ V W m) :
    (b + c).balakrishnanIntegral hΛ hσ hm =
      b.balakrishnanIntegral hΛ hσ hm + c.balakrishnanIntegral hΛ hσ hm := by
  simp [balakrishnanIntegral]

@[simp]
theorem balakrishnanIntegral_smul (c : ℂ) (b : ParameterSymbol n Λ V W m) :
    (c • b).balakrishnanIntegral hΛ hσ hm = c • b.balakrishnanIntegral hΛ hσ hm := by
  simp [balakrishnanIntegral, smul_comm c]

@[simp]
theorem balakrishnanIntegral_neg (b : ParameterSymbol n Λ V W m) :
    (-b).balakrishnanIntegral hΛ hσ hm = -b.balakrishnanIntegral hΛ hσ hm := by
  simp [balakrishnanIntegral]

@[simp]
theorem balakrishnanIntegral_sub (b c : ParameterSymbol n Λ V W m) :
    (b - c).balakrishnanIntegral hΛ hσ hm =
      b.balakrishnanIntegral hΛ hσ hm - c.balakrishnanIntegral hΛ hσ hm := by
  simp [balakrishnanIntegral, smul_sub]

/-- The Balakrishnan integral as a `ℂ`-linear map from parameter-dependent symbols of order `m`
to symbols of order `m - 2 σ + 2`. -/
def balakrishnanIntegralₗ : ParameterSymbol n Λ V W m →ₗ[ℂ] Symbol n V W (m - 2 * σ + 2) where
  toFun b := b.balakrishnanIntegral hΛ hσ hm
  map_add' := balakrishnanIntegral_add hΛ hσ hm
  map_smul' := balakrishnanIntegral_smul hΛ hσ hm

@[simp]
theorem balakrishnanIntegralₗ_apply (b : ParameterSymbol n Λ V W m) :
    balakrishnanIntegralₗ hΛ hσ hm b = b.balakrishnanIntegral hΛ hσ hm :=
  (rfl)

/-- The Balakrishnan integral of a finite sum is the sum of the Balakrishnan integrals, so a
finite parametrix expansion may be integrated term by term. -/
@[simp]
theorem balakrishnanIntegral_sum {ι : Type*} (s : Finset ι) (b : ι → ParameterSymbol n Λ V W m) :
    (∑ i ∈ s, b i).balakrishnanIntegral hΛ hσ hm = ∑ i ∈ s, (b i).balakrishnanIntegral hΛ hσ hm :=
  map_sum (balakrishnanIntegralₗ hΛ hσ hm) b s

end

/-- The Balakrishnan integral commutes with the order inclusions. -/
@[simp]
theorem balakrishnanIntegral_inclusion {m' : ℝ} (h : m ≤ m') (hm' : m' - 2 * σ + 2 < 0)
    (b : ParameterSymbol n Λ V W m) :
    (inclusion h b).balakrishnanIntegral hΛ hσ hm' =
      Symbol.inclusion (by linarith) (b.balakrishnanIntegral hΛ hσ (by linarith)) :=
  Symbol.ext <| funext fun p ↦ by
    simp only [coefficient_balakrishnanIntegral, coefficient_inclusion,
      Symbol.coefficient_inclusion]

end Integral

/-! ### Homogeneous expansions -/

section Classical

variable {n : ℕ} {Λ : TopologicalSpace.Opens ℂ} {V W : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m σ μ R : ℝ}
  (hΛ : ∀ t : ℝ, t ≤ 0 → (t : ℂ) ∈ Λ) (hσ : σ < 1)

/-- **Quasi-homogeneity becomes homogeneity.** If `b` is quasi-homogeneous of degree `μ` above the
radius `R` under `(ξ, z) ↦ (t ξ, t² z)`, its Balakrishnan integral is homogeneous of degree
`μ - 2 σ + 2` in the frequency above `R`. -/
theorem IsQuasiHomogeneousAbove.isHomogeneousAbove_balakrishnanIntegral
    (hm : m - 2 * σ + 2 < 0) {b : ParameterSymbol n Λ V W m}
    (hb : b.IsQuasiHomogeneousAbove μ R) :
    (b.balakrishnanIntegral hΛ hσ hm).IsHomogeneousAbove (μ - 2 * σ + 2) R := by
  refine Symbol.isHomogeneousAbove_iff.2 fun x ξ hξ t ht ↦ ?_
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have ht2 : 0 < t ^ 2 := by positivity
  rw [coefficient_balakrishnanIntegral, coefficient_balakrishnanIntegral,
    smul_comm (t ^ (μ - 2 * σ + 2))]
  congr 1
  -- Substitute `s = t² u` in `∫₀^∞ s ^ (-σ) b((x, t ξ), -s) ds`, then use
  -- `b((x, t ξ), -t² u) = t ^ μ b((x, ξ), -u)`.
  have hsub := integral_comp_mul_left_Ioi'
    (fun s : ℝ ↦ s ^ (-σ) • b.coefficient ((x, t • ξ), -(s : ℂ))) 0 ht2
  rw [mul_zero] at hsub
  rw [← hsub, setIntegral_congr_fun measurableSet_Ioi (g := fun u : ℝ ↦
      (t ^ ((2 : ℕ) * -σ) * t ^ μ) • u ^ (-σ) • b.coefficient ((x, ξ), -(u : ℂ)))
      fun u (hu : 0 < u) ↦ ?_, integral_smul, smul_smul]
  · congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_add ht0, ← Real.rpow_add ht0]
    congr 1
    push_cast
    ring
  -- The dilated spectral parameter `-t² u` stays on the negative real axis.
  have hz : -(((t ^ 2 * u : ℝ)) : ℂ) = (t ^ 2 : ℝ) • -(u : ℂ) := by
    rw [Complex.real_smul]
    push_cast
    ring
  have hu' : -(u : ℂ) ∈ Λ := by simpa using hΛ (-u) (by linarith)
  have htu : (t ^ 2 : ℝ) • -(u : ℂ) ∈ Λ := by
    rw [← hz, ← Complex.ofReal_neg]
    exact hΛ _ (by nlinarith)
  dsimp only
  rw [hz, isQuasiHomogeneousAbove_iff.1 hb x ξ hξ _ hu' t ht htu,
    Real.mul_rpow ht2.le hu.le, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le, smul_smul,
    smul_smul]
  congr 1
  ring

variable (hm : m - 2 * σ + 2 < 0)

include hm in
/-- The orders `m - j` of the terms of an expansion stay in the range of the Balakrishnan
integral. -/
private theorem sub_natCast_sub_two_mul_add_two_neg (j : ℕ) : m - j - 2 * σ + 2 < 0 := by
  have := Nat.cast_nonneg (α := ℝ) j
  linarith

/-- The Balakrishnan integral of a term of a quasi-homogeneous expansion, as a classical symbol
with a single homogeneous term. -/
private def termClassical {j : ℕ} (b : ParameterSymbol n Λ V W (m - j))
    (hb : ∃ R, b.IsQuasiHomogeneousAbove (m - j) R) :
    ClassicalSymbol n V W (m - j - 2 * σ + 2) :=
  ClassicalSymbol.ofIsHomogeneousAbove
    (b.balakrishnanIntegral hΛ hσ (sub_natCast_sub_two_mul_add_two_neg hm j))
    (hb.imp fun _ hR ↦ hR.isHomogeneousAbove_balakrishnanIntegral hΛ hσ _)

/-- The remainders of the expansion of the Balakrishnan integral of `b ∼ ∑ⱼ bⱼ` into the cut-off
integrals of the `bⱼ` at large frequencies. -/
private theorem exists_remainder_balakrishnanIntegral (b : ParameterSymbol n Λ V W m)
    (bs : ∀ j : ℕ, ParameterSymbol n Λ V W (m - j))
    (hbs : ∀ j, ∃ R, (bs j).IsQuasiHomogeneousAbove (m - j) R)
    (hb : IsAsymptoticSum (m := fun j : ℕ ↦ m - j) (inclusion (by simp) b) bs) :
    ∃ χ : FrequencyCutoff (CoordinateSpace n), ∀ N : ℕ,
      ∃ r : Symbol n V W (m - 2 * σ + 2 - N), ∀ p, r.coefficient p =
        (b.balakrishnanIntegral hΛ hσ hm).coefficient p - ∑ j ∈ Finset.range N, χ p.2 •
          ((termClassical hΛ hσ hm (bs j) (hbs j)).principal.castDegree
            (by ring : m - j - 2 * σ + 2 = m - 2 * σ + 2 - j)).coefficient p := by
  refine ⟨default, fun N ↦ ?_⟩
  have hm' := sub_natCast_sub_two_mul_add_two_neg hm (σ := σ)
  obtain ⟨r, hr⟩ := isAsymptoticSum_iff.1 hb N
  -- Integrate the decomposition `b = r + ∑_{j < N} bⱼ` term by term.
  have hdecomp : b = inclusion (by simp) r +
      ∑ j ∈ Finset.range N, inclusion (by simp) (bs j) :=
    coefficient_injective (by
      simp only [coefficient_add, coefficient_sum, coefficient_inclusion, ← hr]
      abel)
  have hB : ∀ p, (b.balakrishnanIntegral hΛ hσ hm).coefficient p =
      (r.balakrishnanIntegral hΛ hσ (hm' N)).coefficient p +
        ∑ j ∈ Finset.range N, ((bs j).balakrishnanIntegral hΛ hσ (hm' j)).coefficient p := by
    intro p
    rw [hdecomp]
    simp only [balakrishnanIntegral_add, balakrishnanIntegral_sum, Symbol.coefficient_add,
      Symbol.coefficient_sum, Pi.add_apply, Finset.sum_apply, coefficient_balakrishnanIntegral,
      coefficient_inclusion]
  -- Each integral `∫ bⱼ` differs from its cut-off homogeneous term by a smoothing symbol.
  have hS : ∀ j, (Symbol.inclusion (le_of_eq (by ring))
      ((bs j).balakrishnanIntegral hΛ hσ (hm' j)) - HomogeneousSymbol.cutoffSymbol default
        ((termClassical hΛ hσ hm (bs j) (hbs j)).principal.castDegree
          (by ring : m - j - 2 * σ + 2 = m - 2 * σ + 2 - j))).IsSmoothing := by
    intro j
    obtain ⟨R, hR⟩ := hbs j
    refine Symbol.isSmoothing_of_coefficient_eq_zero (max R 2) fun x ξ hξ ↦ ?_
    have hξ2 : 2 ≤ ‖ξ‖ := le_of_max_le_right hξ
    rw [Symbol.coefficient_sub, Pi.sub_apply, Symbol.coefficient_inclusion,
      HomogeneousSymbol.coefficient_cutoffSymbol_of_two_le_norm _ _ hξ2,
      HomogeneousSymbol.coefficient_castDegree, termClassical,
      ClassicalSymbol.coefficient_principal_of_isHomogeneousAbove _
        (by simpa using hR.isHomogeneousAbove_balakrishnanIntegral hΛ hσ _)
        (le_of_max_le_left hξ) (norm_pos_iff.1 (by linarith)),
      ClassicalSymbol.toSymbol_ofIsHomogeneousAbove, sub_self]
  choose s hs using fun j ↦ Symbol.isSmoothing_iff.1 (hS j) (m - 2 * σ + 2 - N)
  refine ⟨Symbol.inclusion (le_of_eq (by ring)) (r.balakrishnanIntegral hΛ hσ (hm' N)) +
    ∑ j ∈ Finset.range N, s j, fun p ↦ ?_⟩
  simp only [Symbol.coefficient_add, Symbol.coefficient_sum, Pi.add_apply, Finset.sum_apply, hs,
    Symbol.coefficient_sub, Pi.sub_apply, Symbol.coefficient_inclusion,
    HomogeneousSymbol.coefficient_cutoffSymbol, hB, Finset.sum_sub_distrib]
  abel

/-- **The Balakrishnan integral of a quasi-homogeneous expansion is classical.** Let `b` be a
parameter-dependent symbol of order `m` with an asymptotic expansion `b ∼ ∑ⱼ bⱼ`
(`TauCeti.ParameterSymbol.IsAsymptoticSum`) into symbols `bⱼ` of orders `m - j`, each
quasi-homogeneous of degree `m - j` above some radius, as are the terms of Seeley's resolvent
parametrix once they are cut off near `(ξ, z) = (0, 0)`. Then the Balakrishnan integral of `b`, of
order `m - 2 σ + 2`, is a classical symbol. Its homogeneous term of degree `m - 2 σ + 2 - j` is the
Balakrishnan integral of `bⱼ` at large frequencies
(`TauCeti.ParameterSymbol.coefficient_term_classicalBalakrishnanIntegral`); in particular its
principal symbol is the Balakrishnan integral of `b₀` there
(`TauCeti.ParameterSymbol.coefficient_principal_classicalBalakrishnanIntegral`). -/
def classicalBalakrishnanIntegral (b : ParameterSymbol n Λ V W m)
    (bs : ∀ j : ℕ, ParameterSymbol n Λ V W (m - j))
    (hbs : ∀ j, ∃ R, (bs j).IsQuasiHomogeneousAbove (m - j) R)
    (hb : IsAsymptoticSum (m := fun j : ℕ ↦ m - j) (inclusion (by simp) b) bs) :
    ClassicalSymbol n V W (m - 2 * σ + 2) where
  toSymbol := b.balakrishnanIntegral hΛ hσ hm
  term j := (termClassical hΛ hσ hm (bs j) (hbs j)).principal.castDegree (by ring)
  exists_remainder' := exists_remainder_balakrishnanIntegral hΛ hσ hm b bs hbs hb

variable (b : ParameterSymbol n Λ V W m) (bs : ∀ j : ℕ, ParameterSymbol n Λ V W (m - j))
  (hbs : ∀ j, ∃ R, (bs j).IsQuasiHomogeneousAbove (m - j) R)
  (hb : IsAsymptoticSum (m := fun j : ℕ ↦ m - j) (inclusion (by simp) b) bs)

@[simp]
theorem toSymbol_classicalBalakrishnanIntegral :
    (classicalBalakrishnanIntegral hΛ hσ hm b bs hbs hb).toSymbol =
      b.balakrishnanIntegral hΛ hσ hm :=
  (rfl)

private theorem term_classicalBalakrishnanIntegral (j : ℕ) :
    (classicalBalakrishnanIntegral hΛ hσ hm b bs hbs hb).term j =
      (termClassical hΛ hσ hm (bs j) (hbs j)).principal.castDegree (by ring) :=
  (rfl)

/-- The homogeneous term of degree `m - 2 σ + 2 - j` of the Balakrishnan integral of an expansion
`b ∼ ∑ⱼ bⱼ` is the Balakrishnan integral of `bⱼ` at every nonzero frequency of norm at least a
radius above which `bⱼ` is quasi-homogeneous. -/
theorem coefficient_term_classicalBalakrishnanIntegral (j : ℕ)
    (hR : (bs j).IsQuasiHomogeneousAbove (m - j) R) {x ξ : CoordinateSpace n} (hξ : R ≤ ‖ξ‖)
    (hξ0 : ξ ≠ 0) :
    ((classicalBalakrishnanIntegral hΛ hσ hm b bs hbs hb).term j).coefficient (x, ξ) =
      ((bs j).balakrishnanIntegral hΛ hσ
        (by linarith [Nat.cast_nonneg (α := ℝ) j])).coefficient (x, ξ) := by
  rw [term_classicalBalakrishnanIntegral, HomogeneousSymbol.coefficient_castDegree, termClassical,
    ClassicalSymbol.coefficient_principal_of_isHomogeneousAbove _
      (by simpa using hR.isHomogeneousAbove_balakrishnanIntegral hΛ hσ _) hξ hξ0,
    ClassicalSymbol.toSymbol_ofIsHomogeneousAbove]

/-- The principal symbol of the Balakrishnan integral of an expansion `b ∼ ∑ⱼ bⱼ` is the
Balakrishnan integral of the leading term `b₀` at every nonzero frequency of norm at least a radius
above which `b₀` is quasi-homogeneous. -/
theorem coefficient_principal_classicalBalakrishnanIntegral
    (hR : (bs 0).IsQuasiHomogeneousAbove (m - (0 : ℕ)) R) {x ξ : CoordinateSpace n}
    (hξ : R ≤ ‖ξ‖) (hξ0 : ξ ≠ 0) :
    (classicalBalakrishnanIntegral hΛ hσ hm b bs hbs hb).principal.coefficient (x, ξ) =
      ((bs 0).balakrishnanIntegral hΛ hσ (by simpa using hm)).coefficient (x, ξ) := by
  rw [ClassicalSymbol.coefficient_principal]
  exact coefficient_term_classicalBalakrishnanIntegral hΛ hσ hm b bs hbs hb 0 hR hξ hξ0

end Classical

/-! ### Negative powers -/

section Power

variable {n : ℕ} {Λ : TopologicalSpace.Opens ℂ} {V : Type*} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V] {m σ : ℝ}
  (hΛ : ∀ t : ℝ, t ≤ 0 → (t : ℂ) ∈ Λ) (hσ : σ < 1)

/-- **The Balakrishnan integral of a resolvent is a negative power.** Let `A` be a strictly
positive operator on a complex Hilbert space `V`, and let `r` be a parameter-dependent symbol whose
value at `(x, ξ)` is, at each point `-t`, `t > 0`, of the negative real axis, a left inverse of
`A + t`. Then for `0 < σ < 1` the Balakrishnan integral of `r` at `(x, ξ)` is the power
`A ^ (-σ)` of the continuous functional calculus:

`(sin (π σ) / π) ∫₀^∞ t ^ (-σ) (A + t)⁻¹ dt = A ^ (-σ)`. -/
theorem coefficient_balakrishnanIntegral_eq_rpow (hσ0 : 0 < σ) (hm : m - 2 * σ + 2 < 0)
    (r : ParameterSymbol n Λ V V m) {p : CoordinateSpace n × CoordinateSpace n}
    {A : V →L[ℂ] V} (hA : IsStrictlyPositive A)
    (hr : ∀ t : ℝ, 0 < t → r.coefficient (p, -(t : ℂ)) * (A + t • 1) = 1) :
    (r.balakrishnanIntegral hΛ hσ hm).coefficient p = A ^ (-σ) := by
  rw [coefficient_balakrishnanIntegral, CFC.rpow_neg_eq_integral_ringInverse_add hA hσ0 hσ]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
  -- Along the axis, `r` is a left inverse of the unit `A + t`, so it is `(A + t)⁻¹`.
  have hunit : IsUnit (A + t • (1 : V →L[ℂ] V)) :=
    (hA.add_nonneg (smul_nonneg ht.le zero_le_one)).isUnit
  rw [hunit.mul_left_inj.1 ((hr t ht).trans (Ring.inverse_mul_cancel _ hunit).symm)]

/-- **The principal symbol of a negative power.** Let `b ∼ ∑ⱼ bⱼ` be an expansion into symbols
quasi-homogeneous above some radius, as in
`TauCeti.ParameterSymbol.classicalBalakrishnanIntegral`, with `b₀` quasi-homogeneous above the
radius `R`, and let `0 < σ < 1`. At a nonzero frequency `ξ` with `‖ξ‖ ≥ R` where the leading term
`b₀` is, along the negative real axis, a left inverse of `A + t` for a strictly positive operator
`A`, the principal symbol of the Balakrishnan integral of `b` is `A ^ (-σ)`. For the resolvent
parametrix of an elliptic operator of order `2` with principal symbol `A` at `(x, ξ)`, this is the
principal symbol `σ(A) ^ (-σ)` of the power. -/
theorem coefficient_principal_classicalBalakrishnanIntegral_eq_rpow (hσ0 : 0 < σ)
    (hm : m - 2 * σ + 2 < 0) (b : ParameterSymbol n Λ V V m)
    (bs : ∀ j : ℕ, ParameterSymbol n Λ V V (m - j))
    (hbs : ∀ j, ∃ R, (bs j).IsQuasiHomogeneousAbove (m - j) R)
    (hb : IsAsymptoticSum (m := fun j : ℕ ↦ m - j) (inclusion (by simp) b) bs) {R : ℝ}
    (hR : (bs 0).IsQuasiHomogeneousAbove (m - (0 : ℕ)) R) {x ξ : CoordinateSpace n}
    (hξ : R ≤ ‖ξ‖) (hξ0 : ξ ≠ 0) {A : V →L[ℂ] V} (hA : IsStrictlyPositive A)
    (hr : ∀ t : ℝ, 0 < t → (bs 0).coefficient ((x, ξ), -(t : ℂ)) * (A + t • 1) = 1) :
    (classicalBalakrishnanIntegral hΛ hσ hm b bs hbs hb).principal.coefficient (x, ξ) =
      A ^ (-σ) := by
  rw [coefficient_principal_classicalBalakrishnanIntegral hΛ hσ hm b bs hbs hb hR hξ hξ0]
  exact coefficient_balakrishnanIntegral_eq_rpow hΛ hσ hσ0 _ (bs 0) hA hr

/-- **The Balakrishnan integral of the inverse of a parameter-elliptic symbol.** Let `a` be a
symbol of order `m` elliptic with parameter whose value at `(x, ξ)` along the negative real axis is
`a((x, ξ), -t) = A + t`, `t > 0`, for a strictly positive operator `A`, as for the symbol of
`P - λ` with `P` an elliptic operator whose full symbol at `(x, ξ)` is `A`. Then for `0 < σ < 1`
the Balakrishnan integral of the inverse symbol `a⁻¹` at `(x, ξ)` is `A ^ (-σ)`. -/
theorem coefficient_balakrishnanIntegral_inverse (hσ0 : 0 < σ) (hm : -m - 2 * σ + 2 < 0)
    {a : ParameterSymbol n Λ V V m} (ha : a.IsElliptic)
    {p : CoordinateSpace n × CoordinateSpace n} {A : V →L[ℂ] V} (hA : IsStrictlyPositive A)
    (hpA : ∀ t : ℝ, 0 < t → a.coefficient (p, -(t : ℂ)) = A + t • 1) :
    ((a.inverse ha).balakrishnanIntegral hΛ hσ hm).coefficient p = A ^ (-σ) := by
  refine coefficient_balakrishnanIntegral_eq_rpow hΛ hσ hσ0 hm _ hA fun t ht ↦ ?_
  have hmem : -(t : ℂ) ∈ Λ := by simpa using hΛ (-t) (by linarith)
  rw [← hpA t ht]
  exact coefficient_inverse_comp_coefficient ha p.1 p.2 hmem

/-- **The principal part of Seeley's symbol of a negative power.** Let `a` be a symbol of order
`m` elliptic with parameter, and `N : ℕ`. The Balakrishnan integral of its truncated right
parametrix `Bₙ₊₁` (`TauCeti.ParameterSymbol.rightParametrix`) satisfies: there is one symbol `d`
of order `-m - 2 σ + 1` such that at every `(x, ξ)` where `a((x, ξ), -t) = A + t` along the
negative real axis, for a strictly positive operator `A`, the integral of `Bₙ₊₁` at `(x, ξ)` is
`A ^ (-σ) + d(x, ξ)`. For `m = 2` it is pointwise the power `A ^ (-σ)`, of order `-2 σ`, up to
the value of a symbol of order `-2 σ - 1`. -/
theorem exists_coefficient_balakrishnanIntegral_rightParametrix_eq_rpow_add (hσ0 : 0 < σ)
    (hm : -m - 2 * σ + 2 < 0) {a : ParameterSymbol n Λ V V m} (ha : a.IsElliptic) (N : ℕ) :
    ∃ d : Symbol n V V (-m - 1 - 2 * σ + 2), ∀ (p : CoordinateSpace n × CoordinateSpace n)
      (A : V →L[ℂ] V), IsStrictlyPositive A →
        (∀ t : ℝ, 0 < t → a.coefficient (p, -(t : ℂ)) = A + t • 1) →
        ((a.rightParametrix ha (N + 1)).balakrishnanIntegral hΛ hσ hm).coefficient p =
          A ^ (-σ) + d.coefficient p := by
  obtain ⟨d, hd⟩ := exists_coefficient_rightParametrix_eq_inverse_add ha N
  have hm' : -m - 1 - 2 * σ + 2 < 0 := by linarith
  have hsum : a.rightParametrix ha (N + 1) =
      a.inverse ha + inclusion (by linarith : -m - 1 ≤ -m) d :=
    coefficient_injective (by rw [hd, coefficient_add, coefficient_inclusion])
  refine ⟨d.balakrishnanIntegral hΛ hσ hm', fun p A hA hpA ↦ ?_⟩
  rw [hsum, balakrishnanIntegral_add, balakrishnanIntegral_inclusion, Symbol.coefficient_add,
    Pi.add_apply, coefficient_balakrishnanIntegral_inverse hΛ hσ hσ0 hm ha hA hpA,
    Symbol.coefficient_inclusion]

end Power

/-! ### The shifted Laplacian -/

section ShiftedLaplacian

variable {n : ℕ} {Λ : TopologicalSpace.Opens ℂ} {σ : ℝ}

/-- **The Balakrishnan integral of the resolvent of the shifted Laplacian.** For `s > 0` and
`0 < σ < 1` (the hypothesis `-2 - 2 σ + 2 < 0` is `0 < σ`), the Balakrishnan integral of the
resolvent symbol `((s + ‖ξ‖²) - z)⁻¹` of `s - Δ` is the Fourier multiplier `(s + ‖ξ‖²) ^ (-σ)`, the
symbol of `(s - Δ) ^ (-σ)`. -/
theorem coefficient_balakrishnanIntegral_inverse_shiftedLaplacian {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] {s : ℝ} (hs : 0 < s)
    (h : (shiftedLaplacian V s : ParameterSymbol n Λ V V 2).IsElliptic)
    (hΛ : ∀ t : ℝ, t ≤ 0 → (t : ℂ) ∈ Λ) (hσ : σ < 1) (hm : -2 - 2 * σ + 2 < 0)
    (x ξ : CoordinateSpace n) :
    (((shiftedLaplacian V s).inverse h).balakrishnanIntegral hΛ hσ hm).coefficient (x, ξ) =
      ((s + ‖ξ‖ ^ 2) ^ (-σ) : ℝ) • (1 : V →L[ℂ] V) := by
  have hq : 0 < s + ‖ξ‖ ^ 2 := by positivity
  obtain ⟨q, hq_def⟩ : ∃ q : NNReal, (q : ℝ) = s + ‖ξ‖ ^ 2 := ⟨⟨_, hq.le⟩, rfl⟩
  have hq0 : 0 < q := by rwa [← NNReal.coe_pos, hq_def]
  have hmap (r : NNReal) : algebraMap NNReal (V →L[ℂ] V) r = (r : ℝ) • (1 : V →L[ℂ] V) := by
    rw [Algebra.algebraMap_eq_smul_one, NNReal.smul_def]
  rw [coefficient_balakrishnanIntegral_inverse hΛ hσ (by linarith) hm h (A := algebraMap NNReal _ q)
    (isStrictlyPositive_algebraMap hq0) fun t ht ↦ ?_, CFC.rpow_algebraMap, hmap, NNReal.coe_rpow,
    hq_def]
  have hmem : -(t : ℂ) ∈ Λ := by simpa using hΛ (-t) (by linarith)
  rw [coefficient_shiftedLaplacian s x ξ hmem, hmap, hq_def, ← add_smul, ← Complex.coe_smul]
  congr 1
  push_cast
  ring

end ShiftedLaplacian

end ParameterSymbol

end TauCeti
