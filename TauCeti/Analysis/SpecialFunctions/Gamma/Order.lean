/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
public import Mathlib.Analysis.Meromorphic.Complex
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean

/-!
# Exact orders of Gamma and the archimedean factors

The entire reciprocal of `Complex.Gamma` has a simple zero at each nonpositive integer,
with derivative `(-1)^n n!` at `-n`. Hence Gamma has a simple pole at each such point, with
leading Laurent coefficient `(-1)^n / n!` (`Complex.tendsto_add_natCast_mul_Gamma`,
`Complex.meromorphicTrailingCoeffAt_Gamma_neg_nat`,
`Complex.meromorphicTrailingCoeffAt_Gamma_zero`), and has order zero everywhere else. In particular,
`Complex.Gamma` and the shifted Gamma–power kernel `s ↦ Γ(s - β) * x ^ (β - s)` are analytic
wherever the Gamma argument avoids the nonpositive integers (`Complex.analyticAt_Gamma`,
`Complex.analyticAt_Gamma_sub_mul_cpow`). Deligne's
factors inherit exactly the pole lattices `-2n` and `-n`. Their meromorphic orders are
nonpositive: none has a zero as a meromorphic germ. Their leading Laurent coefficients are
`2 (-1)^n π^n / n!` at `-2n` and `2 (-1)^n (2π)^n / n!` at `-n`
(`Complex.meromorphicTrailingCoeffAt_Gammaℝ_neg_two_mul_nat`,
`Complex.meromorphicTrailingCoeffAt_Gammaℂ_neg_nat`), in particular `2` at `0`
(`Complex.meromorphicTrailingCoeffAt_Gammaℝ_zero`,
`Complex.meromorphicTrailingCoeffAt_Gammaℂ_zero`).

For `n ≥ 1`, the product `Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂` has a pole of order `d = r₂` at `1 - n` when
`n` is even and `d = r₁ + r₂` when `n` is odd
(`TauCeti.meromorphicOrderAt_Gammaℝ_pow_mul_Gammaℂ_pow_one_sub_nat`), and its value at `n` is a
nonzero rational multiple of `π ^ (d - (r₁ + 2 r₂) n)` times its leading coefficient at `1 - n`
(`TauCeti.exists_rat_Gammaℝ_pow_mul_Gammaℂ_pow_eq_mul_meromorphicTrailingCoeffAt`). For the
signature `(r₁, r₂)` of a number field `F`, this product is the archimedean factor of the
completed Dedekind zeta function. For `n ≥ 2`, where the completed zeta function is regular and
nonzero at `n`, the functional equation turns these two statements into the order `d` of the zero
of `ζ_F` at `1 - n` and the power of `π` in its leading coefficient there (Borel). At `n = 1` the
pole of the completed zeta function at `0` lowers the order of `ζ_F` at `0` to `r₁ + r₂ - 1`.

The total values at poles are zero by Mathlib's convention. The zero-order characterizations
therefore use nonzero total values, while the negative-order characterizations identify the
pole lattices. These formulas supply the local orders from which shifted products and
archimedean divisors of L-function records are assembled.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory* (2004), §5.1.
* A. Borel, *Cohomologie de SL_n et valeurs de fonctions zêta aux points entiers*,
  Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) 4 (1977), §1.4 and §6.4.
-/

public section

open Complex Filter Topology

namespace Complex

/-- The reciprocal Gamma derivative at a nonpositive integer is `(-1)^n n!`. -/
theorem hasDerivAt_inv_Gamma_neg_nat (n : ℕ) :
    HasDerivAt (fun s : ℂ ↦ (Gamma s)⁻¹) ((-1 : ℂ) ^ n * n.factorial) (-(n : ℂ)) := by
  let q : ℂ → ℂ := fun s ↦ (Gamma s)⁻¹
  have hq : Differentiable ℂ q := differentiable_one_div_Gamma
  have he : q = fun s ↦ s * q (s + 1) := funext one_div_Gamma_eq_self_mul_one_div_Gamma_add_one
  -- Express the target using the named reciprocal before differentiating its recurrence.
  change HasDerivAt q ((-1 : ℂ) ^ n * n.factorial) (-(n : ℂ))
  induction n with
  | zero =>
    have hd := (hasDerivAt_id (0 : ℂ)).mul
      ((hq ((0 : ℂ) + 1)).hasDerivAt.comp (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).add_const 1))
    rw [he]
    simpa [q, Function.comp_def, Pi.mul_def] using hd
  | succ n ih =>
    have hp : -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) := by push_cast; ring
    have hi : HasDerivAt q ((-1 : ℂ) ^ n * n.factorial) (-((n + 1 : ℕ) : ℂ) + 1) := by
      rw [hp]
      exact ih
    have hd := (hasDerivAt_id (-((n + 1 : ℕ) : ℂ))).mul
      (hi.comp (-((n + 1 : ℕ) : ℂ)) ((hasDerivAt_id _).add_const 1))
    have hqn : q (-(n : ℂ)) = 0 := by simp [q, Gamma_eq_zero_iff]
    simp only [Function.comp_def, Pi.mul_def, id_eq, hp, hqn, one_mul, mul_one, zero_add] at hd
    rw [he]
    convert hd using 1
    simp only [Nat.factorial_succ, pow_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

/-- **The residue of `Γ` at `−n`**: `(a + n) Γ(a) → (−1)ⁿ/n!` as `a → −n`. -/
theorem tendsto_add_natCast_mul_Gamma (n : ℕ) :
    Tendsto (fun a : ℂ ↦ (a + n) * Gamma a) (𝓝[≠] (-(n : ℂ)))
      (𝓝 ((-1) ^ n / (n.factorial : ℂ))) := by
  have hd : (-1 : ℂ) ^ n * n.factorial ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  have hlim : ((-1 : ℂ) ^ n * n.factorial)⁻¹ = (-1) ^ n / (n.factorial : ℂ) := by
    rw [mul_inv, ← inv_pow, inv_neg, inv_one, div_eq_mul_inv]
  rw [← hlim]
  refine ((hasDerivAt_inv_Gamma_neg_nat n).tendsto_slope.inv₀ hd).congr fun a ↦ ?_
  simp [slope_def_field, Gamma_neg_nat_eq_zero]

/-- The entire reciprocal Gamma function has a simple zero at each nonpositive integer. -/
@[simp]
theorem analyticOrderAt_inv_Gamma_neg_nat (n : ℕ) :
    analyticOrderAt (fun s : ℂ ↦ (Gamma s)⁻¹) (-(n : ℂ)) = 1 := by
  apply (differentiable_one_div_Gamma.analyticAt _).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · simp [Gamma_neg_nat_eq_zero]
  · rw [(hasDerivAt_inv_Gamma_neg_nat n).deriv]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

/-- Gamma has a simple pole at each nonpositive integer. -/
@[simp]
theorem meromorphicOrderAt_Gamma_neg_nat (n : ℕ) :
    meromorphicOrderAt Gamma (-(n : ℂ)) = -1 := by
  have hq : meromorphicOrderAt (fun s : ℂ ↦ (Gamma s)⁻¹) (-(n : ℂ)) = 1 := by
    rw [(differentiable_one_div_Gamma.analyticAt _).meromorphicOrderAt_eq,
      analyticOrderAt_inv_Gamma_neg_nat]
    simp
  rw [← Pi.inv_def, meromorphicOrderAt_inv] at hq
  have h := congrArg Neg.neg hq
  simpa only [neg_neg] using h

/-- The leading Laurent coefficient of `Complex.Gamma` at `-n` is `(-1)^n / n!`. -/
@[simp]
theorem meromorphicTrailingCoeffAt_Gamma_neg_nat (n : ℕ) :
    meromorphicTrailingCoeffAt Gamma (-(n : ℂ)) = (-1) ^ n / (n.factorial : ℂ) := by
  refine tendsto_nhds_unique
    ((Meromorphic.Gamma (-(n : ℂ))).tendsto_nhds_meromorphicTrailingCoeffAt.congr fun a ↦ ?_)
    (tendsto_add_natCast_mul_Gamma n)
  simp [meromorphicOrderAt_Gamma_neg_nat, Pi.smul_apply', sub_neg_eq_add, smul_eq_mul]

/-- The leading Laurent coefficient of `Complex.Gamma` at `0` is `1`. -/
@[simp]
theorem meromorphicTrailingCoeffAt_Gamma_zero : meromorphicTrailingCoeffAt Gamma 0 = 1 := by
  simpa using meromorphicTrailingCoeffAt_Gamma_neg_nat 0

/-- Gamma is analytic away from the nonpositive integers. -/
@[fun_prop]
theorem analyticAt_Gamma {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(n : ℂ)) : AnalyticAt ℂ Gamma s := by
  have h := (differentiable_one_div_Gamma.analyticAt s).inv (inv_ne_zero (Gamma_ne_zero hs))
  simpa only [Pi.inv_def, inv_inv] using h

/-- For any complex base `x` and shift `β`, the shifted Gamma–power kernel
`s ↦ Γ(s - β) * x ^ (β - s)` is analytic at every `s₀` where `s₀ - β` is not a nonpositive
integer (including `x = 0`, where `β - s₀ ≠ 0` forces `0 ^ (β - s) = 0` near `s₀`). -/
theorem analyticAt_Gamma_sub_mul_cpow {s₀ β : ℂ} (x : ℂ) (hs : ∀ n : ℕ, s₀ - β ≠ -(n : ℂ)) :
    AnalyticAt ℂ (fun s ↦ Gamma (s - β) * x ^ (β - s)) s₀ := by
  have hne : β - s₀ ≠ 0 := fun h ↦ hs 0 (by simpa [sub_eq_zero] using (sub_eq_zero.mp h).symm)
  rcases eq_or_ne x 0 with rfl | hx
  · refine (analyticAt_const (v := (0 : ℂ))).congr ?_
    filter_upwards [(continuous_const.sub continuous_id).continuousAt.eventually_ne hne]
      with s (hs' : β - s ≠ 0)
    simp [zero_cpow hs']
  · have hcpow : AnalyticAt ℂ (fun s : ℂ ↦ x ^ (β - s)) s₀ :=
      (((differentiable_const β).sub differentiable_id).const_cpow (.inl hx)).analyticAt s₀
    exact (AnalyticAt.comp (g := Gamma) (f := fun s : ℂ ↦ s - β) (analyticAt_Gamma hs)
      (by fun_prop)).mul hcpow

/-- Gamma has order zero at every regular point. -/
theorem meromorphicOrderAt_Gamma_of_ne_neg_nat {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ -(n : ℂ)) : meromorphicOrderAt Gamma s = 0 := by
  have ha := analyticAt_Gamma hs
  rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr (Gamma_ne_zero hs)]
  simp

/-- The simple poles of Gamma are exactly the nonpositive integers. -/
theorem meromorphicOrderAt_Gamma_eq_neg_one_iff (s : ℂ) :
    meromorphicOrderAt Gamma s = -1 ↔ ∃ n : ℕ, s = -(n : ℂ) := by
  classical
  by_cases hs : ∃ n : ℕ, s = -(n : ℂ)
  · obtain ⟨n, rfl⟩ := hs
    simp [meromorphicOrderAt_Gamma_neg_nat]
  · rw [meromorphicOrderAt_Gamma_of_ne_neg_nat (not_exists.mp hs)]
    simp [hs]

/-- The exponential prefactor `z ↦ π ^ (-z / 2)` of `Gammaℝ` is analytic everywhere. -/
private theorem analyticAt_pi_cpow_neg_div_two (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-z / 2)) s := by
  fun_prop (disch := exact Or.inl (by simpa using Real.pi_pos))

/-- The exponential prefactor `z ↦ 2 (2π) ^ (-z)` of `Gammaℂ` is analytic everywhere. -/
private theorem analyticAt_two_mul_two_pi_cpow_neg (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ ↦ 2 * (2 * Real.pi : ℂ) ^ (-z)) s := by
  have hp : (2 * Real.pi : ℂ) ∈ slitPlane :=
    Or.inl (by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)
  exact analyticAt_const.mul (analyticAt_const.cpow (by fun_prop) hp)

/-- The meromorphic order of `Gammaℝ` at `s` equals that of `Gamma` at `s / 2`. -/
@[simp]
theorem meromorphicOrderAt_Gammaℝ (s : ℂ) :
    meromorphicOrderAt Gammaℝ s = meromorphicOrderAt Gamma (s / 2) := by
  have he : Gammaℝ = (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-z / 2)) *
      (Gamma ∘ fun z : ℂ ↦ z / 2) := funext Gammaℝ_def
  have ha := analyticAt_pi_cpow_neg_div_two s
  have hn : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [he, meromorphicOrderAt_mul_of_ne_zero ha hn]
  apply meromorphicOrderAt_comp_of_deriv_ne_zero (by fun_prop)
  simp

/-- The complex archimedean factor has the same meromorphic orders as Gamma. -/
@[simp]
theorem meromorphicOrderAt_Gammaℂ (s : ℂ) :
    meromorphicOrderAt Gammaℂ s = meromorphicOrderAt Gamma s := by
  have he : Gammaℂ = (fun z : ℂ ↦ 2 * (2 * Real.pi : ℂ) ^ (-z)) * Gamma :=
    funext Gammaℂ_def
  have ha := analyticAt_two_mul_two_pi_cpow_neg s
  have hn : 2 * (2 * Real.pi : ℂ) ^ (-s) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [he, meromorphicOrderAt_mul_of_ne_zero ha hn]

/-- The leading Laurent coefficient of `Gammaℂ` at `-n` is `2 (-1)^n (2π)^n / n!`. -/
@[simp]
theorem meromorphicTrailingCoeffAt_Gammaℂ_neg_nat (n : ℕ) :
    meromorphicTrailingCoeffAt Gammaℂ (-(n : ℂ)) =
      2 * (-1) ^ n * (2 * Real.pi) ^ n / (n.factorial : ℂ) := by
  have he : Gammaℂ = (fun z : ℂ ↦ 2 * (2 * Real.pi : ℂ) ^ (-z)) * Gamma :=
    funext Gammaℂ_def
  have ha := analyticAt_two_mul_two_pi_cpow_neg (-(n : ℂ))
  rw [he, ha.meromorphicAt.meromorphicTrailingCoeffAt_mul (Meromorphic.Gamma _),
    ha.meromorphicTrailingCoeffAt_of_ne_zero (by simp [Real.pi_ne_zero]),
    meromorphicTrailingCoeffAt_Gamma_neg_nat, neg_neg, cpow_natCast]
  ring

/-- The leading Laurent coefficient of `Gammaℝ` at `-2n` is `2 (-1)^n π^n / n!`. -/
@[simp]
theorem meromorphicTrailingCoeffAt_Gammaℝ_neg_two_mul_nat (n : ℕ) :
    meromorphicTrailingCoeffAt Gammaℝ (-(2 * n : ℂ)) =
      2 * (-1) ^ n * Real.pi ^ n / (n.factorial : ℂ) := by
  have he : Gammaℝ = (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-z / 2)) * (Gamma ∘ fun z : ℂ ↦ z / 2) :=
    funext Gammaℝ_def
  have ha := analyticAt_pi_cpow_neg_div_two (-(2 * n : ℂ))
  have hg : AnalyticAt ℂ (fun z : ℂ ↦ z / 2) (-(2 * n : ℂ)) := by fun_prop
  have hgx : -(2 * n : ℂ) / 2 = -(n : ℂ) := by ring
  -- `z ↦ z / 2` has a simple zero after recentring, with leading coefficient `1 / 2`
  have hsub : meromorphicTrailingCoeffAt (fun z : ℂ ↦ z / 2 - -(2 * n : ℂ) / 2)
      (-(2 * n : ℂ)) = 1 / 2 :=
    analyticAt_const.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := 1) (by norm_num)
      (Eventually.of_forall fun z ↦ by simp only [zpow_one, smul_eq_mul]; ring)
  have hnc : ¬EventuallyConst (fun z : ℂ ↦ z / 2) (𝓝 (-(2 * n : ℂ))) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top,
      hg.analyticOrderAt_sub_eq_one_of_deriv_ne_zero (by simp)]
    simp
  have hcomp : meromorphicTrailingCoeffAt (Gamma ∘ fun z : ℂ ↦ z / 2) (-(2 * n : ℂ)) =
      2 * ((-1) ^ n / (n.factorial : ℂ)) := by
    rw [MeromorphicAt.meromorphicTrailingCoeffAt_comp (Meromorphic.Gamma _) hg hnc, hsub, hgx,
      meromorphicOrderAt_Gamma_neg_nat, meromorphicTrailingCoeffAt_Gamma_neg_nat]
    simp
  rw [he, ha.meromorphicAt.meromorphicTrailingCoeffAt_mul
      ((Meromorphic.Gamma _).comp_analyticAt hg),
    ha.meromorphicTrailingCoeffAt_of_ne_zero (by simp [Real.pi_ne_zero]), hcomp,
    show -(-(2 * n : ℂ)) / 2 = (n : ℂ) by ring, cpow_natCast]
  ring

/-- The leading Laurent coefficient of `Gammaℂ` at `0` is `2`. -/
@[simp]
theorem meromorphicTrailingCoeffAt_Gammaℂ_zero : meromorphicTrailingCoeffAt Gammaℂ 0 = 2 := by
  simpa using meromorphicTrailingCoeffAt_Gammaℂ_neg_nat 0

/-- The leading Laurent coefficient of `Gammaℝ` at `0` is `2`. -/
@[simp]
theorem meromorphicTrailingCoeffAt_Gammaℝ_zero : meromorphicTrailingCoeffAt Gammaℝ 0 = 2 := by
  simpa using meromorphicTrailingCoeffAt_Gammaℝ_neg_two_mul_nat 0

/-- Gamma has no zeros as a meromorphic germ. -/
theorem meromorphicOrderAt_Gamma_nonpos (s : ℂ) : meromorphicOrderAt Gamma s ≤ 0 := by
  by_cases hs : ∃ n : ℕ, s = -(n : ℂ)
  · obtain ⟨n, rfl⟩ := hs
    rw [meromorphicOrderAt_Gamma_neg_nat]
    exact WithTop.coe_le_coe.mpr (by norm_num : (-1 : ℤ) ≤ 0)
  · rw [meromorphicOrderAt_Gamma_of_ne_neg_nat (not_exists.mp hs)]

/-- The real archimedean factor has simple poles exactly at the nonpositive even integers. -/
theorem meromorphicOrderAt_Gammaℝ_eq_neg_one_iff (s : ℂ) :
    meromorphicOrderAt Gammaℝ s = -1 ↔ ∃ n : ℕ, s = -(2 * (n : ℂ)) := by
  rw [meromorphicOrderAt_Gammaℝ, meromorphicOrderAt_Gamma_eq_neg_one_iff]
  simp only [div_eq_iff (two_ne_zero : (2 : ℂ) ≠ 0), neg_mul, mul_comm]

/-- The complex archimedean factor has simple poles exactly at the nonpositive integers. -/
theorem meromorphicOrderAt_Gammaℂ_eq_neg_one_iff (s : ℂ) :
    meromorphicOrderAt Gammaℂ s = -1 ↔ ∃ n : ℕ, s = -(n : ℂ) := by
  rw [meromorphicOrderAt_Gammaℂ, meromorphicOrderAt_Gamma_eq_neg_one_iff]

/-- The real archimedean factor has no zeros as a meromorphic germ. -/
theorem meromorphicOrderAt_Gammaℝ_nonpos (s : ℂ) : meromorphicOrderAt Gammaℝ s ≤ 0 := by
  rw [meromorphicOrderAt_Gammaℝ]
  exact meromorphicOrderAt_Gamma_nonpos _

/-- The complex archimedean factor has no zeros as a meromorphic germ. -/
theorem meromorphicOrderAt_Gammaℂ_nonpos (s : ℂ) : meromorphicOrderAt Gammaℂ s ≤ 0 := by
  rw [meromorphicOrderAt_Gammaℂ]
  exact meromorphicOrderAt_Gamma_nonpos _

end Complex

namespace TauCeti

/-- The real archimedean gamma factor is in meromorphic normal form on the whole plane. -/
theorem meromorphicNFOn_Gammaℝ : MeromorphicNFOn Gammaℝ Set.univ :=
  meromorphicNFOn_inv.mp <| AnalyticOnNhd.meromorphicNFOn <|
    analyticOnNhd_univ_iff_differentiable.mpr differentiable_Gammaℝ_inv

/-- The complex archimedean gamma factor is in meromorphic normal form on the whole plane. -/
theorem meromorphicNFOn_Gammaℂ : MeromorphicNFOn Gammaℂ Set.univ :=
  meromorphicNFOn_inv.mp <| AnalyticOnNhd.meromorphicNFOn <|
    analyticOnNhd_univ_iff_differentiable.mpr differentiable_Gammaℂ_inv

/-- The real archimedean gamma factor is meromorphic on the whole plane. -/
@[fun_prop]
theorem meromorphic_Gammaℝ : Meromorphic Gammaℝ :=
  meromorphicOn_univ.mp meromorphicNFOn_Gammaℝ.meromorphicOn

/-- The complex archimedean gamma factor is meromorphic on the whole plane. -/
@[fun_prop]
theorem meromorphic_Gammaℂ : Meromorphic Gammaℂ :=
  meromorphicOn_univ.mp meromorphicNFOn_Gammaℂ.meromorphicOn

/-- The real archimedean gamma factor is meromorphic on any subset of the plane. -/
@[fun_prop]
theorem meromorphicOn_Gammaℝ {U : Set ℂ} : MeromorphicOn Gammaℝ U :=
  meromorphic_Gammaℝ.meromorphicOn

/-- The complex archimedean gamma factor is meromorphic on any subset of the plane. -/
@[fun_prop]
theorem meromorphicOn_Gammaℂ {U : Set ℂ} : MeromorphicOn Gammaℂ U :=
  meromorphic_Gammaℂ.meromorphicOn

end TauCeti

namespace Complex

/-- Gamma has order zero exactly where its total value is nonzero. -/
theorem meromorphicOrderAt_Gamma_eq_zero_iff (s : ℂ) :
    meromorphicOrderAt Gamma s = 0 ↔ Gamma s ≠ 0 :=
  (MeromorphicNFOn.Gamma (Set.mem_univ s)).meromorphicOrderAt_eq_zero_iff

/-- The real archimedean factor has order zero exactly where its total value is nonzero. -/
theorem meromorphicOrderAt_Gammaℝ_eq_zero_iff (s : ℂ) :
    meromorphicOrderAt Gammaℝ s = 0 ↔ Gammaℝ s ≠ 0 :=
  (TauCeti.meromorphicNFOn_Gammaℝ (Set.mem_univ s)).meromorphicOrderAt_eq_zero_iff

/-- The complex archimedean factor has order zero exactly where its total value is nonzero. -/
theorem meromorphicOrderAt_Gammaℂ_eq_zero_iff (s : ℂ) :
    meromorphicOrderAt Gammaℂ s = 0 ↔ Gammaℂ s ≠ 0 :=
  (TauCeti.meromorphicNFOn_Gammaℂ (Set.mem_univ s)).meromorphicOrderAt_eq_zero_iff

end Complex

namespace TauCeti

open scoped Nat

/-- At `1 - n` for `n ≥ 1`, `Γ_ℝ(n)` is a nonzero rational multiple of `π ^ (-n)` (even `n`) or
`π ^ (1 - n)` (odd `n`) times the leading coefficient of `Γ_ℝ`. -/
private theorem exists_rat_Gammaℝ_eq_mul_meromorphicTrailingCoeffAt {n : ℕ} (hn : 1 ≤ n) :
    ∃ q : ℚ, q ≠ 0 ∧ Gammaℝ n = q * (Real.pi : ℂ) ^ ((if Even n then 0 else 1 : ℤ) - n) *
      meromorphicTrailingCoeffAt Gammaℝ (1 - n) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · -- `n = 2j + 2`: `Γ_ℝ` is regular and nonzero at `1 - n = -2j - 1`
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hx : 1 - ((2 * (j + 1) : ℕ) : ℂ) = -(2 * j) - 1 := by push_cast; ring
    have hv := Gammaℝ_neg_two_mul_nat_sub_one j
    have hne : Gammaℝ (-(2 * j) - 1) ≠ 0 := by
      rw [hv]; simp [hπ, Nat.factorial_ne_zero]
    have hj : ((j + 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (j + 1).factorial_ne_zero
    have hj' : ((2 * j + 2)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (2 * j + 2).factorial_ne_zero
    have hif : (if Even (2 * (j + 1)) then 0 else 1 : ℤ) = 0 := by simp
    refine ⟨j ! * (2 * j + 2)! / ((-1) ^ (j + 1) * 4 ^ (j + 1) * (j + 1)!),
      by simp [Nat.factorial_ne_zero], ?_⟩
    rw [hx, (analyticAt_Gammaℝ_of_ne_zero hne).meromorphicTrailingCoeffAt_of_ne_zero hne, hv, hif,
      show ((0 : ℤ) - ((2 * (j + 1) : ℕ) : ℤ)) = -((2 * j + 2 : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast,
      show ((2 * (j + 1) : ℕ) : ℂ) = 2 * j + 2 by push_cast; ring, Gammaℝ_two_mul_nat_add_two]
    push_cast
    field_simp
    ring
  · -- `n = 2k + 1`: `Γ_ℝ` has a simple pole at `1 - n = -2k`
    have hx : 1 - ((2 * k + 1 : ℕ) : ℂ) = -(2 * k : ℂ) := by push_cast; ring
    have hif : (if Even (2 * k + 1) then 0 else 1 : ℤ) = 1 := by simp [parity_simps]
    refine ⟨(2 * k)! / (2 * (-1) ^ k * 4 ^ k), by simp [Nat.factorial_ne_zero], ?_⟩
    rw [hx, meromorphicTrailingCoeffAt_Gammaℝ_neg_two_mul_nat, hif,
      show ((1 : ℤ) - ((2 * k + 1 : ℕ) : ℤ)) = -((2 * k : ℕ) : ℤ) by push_cast; ring, zpow_neg,
      zpow_natCast, show ((2 * k + 1 : ℕ) : ℂ) = 2 * k + 1 by push_cast; ring,
      Gammaℝ_two_mul_nat_add_one]
    push_cast
    field_simp
    ring

/-- At `1 - n` for `n ≥ 1`, `Γ_ℂ(n)` is a nonzero rational multiple of `π ^ (1 - 2n)` times the
leading coefficient of `Γ_ℂ`. -/
private theorem exists_rat_Gammaℂ_eq_mul_meromorphicTrailingCoeffAt {n : ℕ} (hn : 1 ≤ n) :
    ∃ q : ℚ, q ≠ 0 ∧ Gammaℂ n = q * (Real.pi : ℂ) ^ (1 - 2 * n : ℤ) *
      meromorphicTrailingCoeffAt Gammaℂ (1 - n) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨m ! ^ 2 / ((-1) ^ m * 2 ^ (2 * m + 1)), by simp [Nat.factorial_ne_zero], ?_⟩
  rw [show 1 - ((m + 1 : ℕ) : ℂ) = -(m : ℂ) by push_cast; ring,
    meromorphicTrailingCoeffAt_Gammaℂ_neg_nat,
    show (1 - 2 * ((m + 1 : ℕ) : ℤ)) = -((2 * m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
    zpow_natCast, Nat.cast_succ, Gammaℂ_nat_add_one]
  push_cast
  field_simp
  ring

/-- The product `Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂` of archimedean factors has a pole of order `r₂` at
`1 - n` for even `n ≥ 1` and of order `r₁ + r₂` for odd `n`: the factor `Γ_ℂ` has a pole at every
nonpositive integer, while `Γ_ℝ` has one only at the nonpositive even integers. -/
theorem meromorphicOrderAt_Gammaℝ_pow_mul_Gammaℂ_pow_one_sub_nat (r₁ r₂ : ℕ) {n : ℕ}
    (hn : 1 ≤ n) :
    meromorphicOrderAt (fun s ↦ Gammaℝ s ^ r₁ * Gammaℂ s ^ r₂) (1 - n) =
      -((if Even n then r₂ else r₁ + r₂ : ℕ) : ℤ) := by
  have hR := meromorphic_Gammaℝ (1 - n)
  have hC := meromorphic_Gammaℂ (1 - n)
  have hCord : meromorphicOrderAt Gammaℂ (1 - n) = -1 :=
    (meromorphicOrderAt_Gammaℂ_eq_neg_one_iff _).mpr ⟨n - 1, by push_cast [hn]; ring⟩
  have he : (fun s ↦ Gammaℝ s ^ r₁ * Gammaℂ s ^ r₂) = Gammaℝ ^ r₁ * Gammaℂ ^ r₂ := by
    ext; simp
  rw [he, meromorphicOrderAt_mul (hR.pow r₁) (hC.pow r₂), meromorphicOrderAt_pow hR,
    meromorphicOrderAt_pow hC, hCord]
  have hRord : meromorphicOrderAt Gammaℝ (1 - n) = if Even n then 0 else -1 := by
    split_ifs with he
    · rw [meromorphicOrderAt_Gammaℝ_eq_zero_iff, Ne, Gammaℝ_eq_zero_iff]
      rintro ⟨m, hm⟩
      have h : ((1 - n : ℤ) : ℂ) = ((-(2 * m) : ℤ) : ℂ) := by push_cast at hm ⊢; exact hm
      have := Int.cast_injective h
      obtain ⟨k, rfl⟩ := he
      omega
    · obtain ⟨k, rfl⟩ := Nat.not_even_iff_odd.mp he
      exact (meromorphicOrderAt_Gammaℝ_eq_neg_one_iff _).mpr ⟨k, by push_cast; ring⟩
  rw [hRord]
  -- the identity is one of integers, cast into `WithTop ℤ`
  split_ifs <;>
  · simp only [← WithTop.coe_natCast, ← WithTop.coe_one, ← WithTop.coe_zero,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_mul, ← WithTop.coe_add,
      WithTop.coe_inj]
    push_cast
    ring

/-- **The leading coefficient of the archimedean factors at `1 - n`.** For `n ≥ 1`, the value at
`n` of `Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂` is a nonzero rational multiple of `π ^ (d - (r₁ + 2 r₂) n)` times
its leading Laurent coefficient at `1 - n`, where `d` is the pole order there: `r₂` for even `n`
and `r₁ + r₂` for odd `n` (`meromorphicOrderAt_Gammaℝ_pow_mul_Gammaℂ_pow_one_sub_nat`). For the
signature `(r₁, r₂)` of a number field of degree `r₁ + 2 r₂` and `n ≥ 2`, this is the
archimedean part of the leading term of its Dedekind zeta function at `1 - n` (Borel 1977, §1.4);
at `n = 1` the pole of the completed zeta function at `0` also contributes. -/
theorem exists_rat_Gammaℝ_pow_mul_Gammaℂ_pow_eq_mul_meromorphicTrailingCoeffAt
    (r₁ r₂ : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ q : ℚ, q ≠ 0 ∧ Gammaℝ n ^ r₁ * Gammaℂ n ^ r₂ =
      q * (Real.pi : ℂ) ^ (((if Even n then r₂ else r₁ + r₂ : ℕ) : ℤ) - (r₁ + 2 * r₂ : ℕ) * n) *
        meromorphicTrailingCoeffAt (fun s ↦ Gammaℝ s ^ r₁ * Gammaℂ s ^ r₂) (1 - n) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  obtain ⟨a, ha, hR⟩ := exists_rat_Gammaℝ_eq_mul_meromorphicTrailingCoeffAt hn
  obtain ⟨b, hb, hC⟩ := exists_rat_Gammaℂ_eq_mul_meromorphicTrailingCoeffAt hn
  have hexp : ((if Even n then r₂ else r₁ + r₂ : ℕ) : ℤ) - (r₁ + 2 * r₂ : ℕ) * n =
      ((if Even n then 0 else 1 : ℤ) - n) * r₁ + (1 - 2 * n) * r₂ := by
    split_ifs <;> push_cast <;> ring
  refine ⟨a ^ r₁ * b ^ r₂, by simp [ha, hb], ?_⟩
  rw [MeromorphicAt.meromorphicTrailingCoeffAt_fun_mul ((meromorphic_Gammaℝ _).fun_pow r₁)
      ((meromorphic_Gammaℂ _).fun_pow r₂),
    (meromorphic_Gammaℝ _).meromorphicTrailingCoeffAt_fun_pow,
    (meromorphic_Gammaℂ _).meromorphicTrailingCoeffAt_fun_pow, hR, hC, hexp,
    zpow_add₀ hπ, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  push_cast
  ring

end TauCeti
