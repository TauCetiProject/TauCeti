/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
public import Mathlib.Analysis.Meromorphic.Complex
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Exact orders of Gamma and the archimedean factors

The entire reciprocal of `Complex.Gamma` has a simple zero at each nonpositive integer,
with derivative `(-1)^n n!` at `-n`. Hence Gamma has a simple pole at each such point, with
leading Laurent coefficient `(-1)^n / n!` (`Complex.tendsto_add_natCast_mul_Gamma`,
`Complex.meromorphicTrailingCoeffAt_Gamma_neg_nat`,
`Complex.meromorphicTrailingCoeffAt_Gamma_zero`), and has order zero everywhere else. In particular,
`Complex.Gamma`, `Complex.digamma`, `b ↦ Γ(2b) / Γ(b)²`, and the shifted Gamma–power kernel
`s ↦ Γ(s - β) * x ^ (β - s)` are analytic wherever the Gamma argument avoids the nonpositive
integers (`Complex.analyticAt_Gamma`, `Complex.analyticAt_digamma`,
`Complex.analyticAt_Gamma_two_mul_div_Gamma_sq`, `Complex.analyticOnNhd_Gamma_two_mul_div_Gamma_sq`,
`Complex.analyticAt_Gamma_sub_mul_cpow`). Deligne's
factors inherit exactly the pole lattices `-2n` and `-n`. Their meromorphic orders are
nonpositive: none has a zero as a meromorphic germ.

The total values at poles are zero by Mathlib's convention. The zero-order characterizations
therefore use nonzero total values, while the negative-order characterizations identify the
pole lattices. These formulas supply the local orders from which shifted products and
archimedean divisors of L-function records are assembled.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory* (2004), §5.1.
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

/-- Complex digamma is analytic away from the nonpositive integers. -/
@[fun_prop]
theorem analyticAt_digamma {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(n : ℂ)) : AnalyticAt ℂ digamma s := by
  have hΓ := analyticAt_Gamma hs
  simpa only [digamma_def, logDeriv, Pi.div_def] using hΓ.deriv.div hΓ (Gamma_ne_zero hs)

/-- `b ↦ Γ(2b) / Γ(b)²` is analytic wherever `2b` is not a nonpositive integer. -/
theorem analyticAt_Gamma_two_mul_div_Gamma_sq {b : ℂ} (hb : ∀ n : ℕ, 2 * b ≠ -(n : ℂ)) :
    AnalyticAt ℂ (fun z : ℂ ↦ Gamma (2 * z) / Gamma z ^ 2) b := by
  have hb' : ∀ m : ℕ, b ≠ -(m : ℂ) := fun m hm ↦
    hb (2 * m) (by push_cast; linear_combination 2 * hm)
  exact ((analyticAt_Gamma hb).comp (analyticAt_const.mul analyticAt_id)).div
    ((analyticAt_Gamma hb').pow 2) (pow_ne_zero 2 (Gamma_ne_zero hb'))

/-- `b ↦ Γ(2b) / Γ(b)²` is analytic on `{b : ℂ | ∀ n : ℕ, 2 * b ≠ -(n : ℂ)}`. -/
theorem analyticOnNhd_Gamma_two_mul_div_Gamma_sq :
    AnalyticOnNhd ℂ (fun b : ℂ ↦ Gamma (2 * b) / Gamma b ^ 2)
      {b : ℂ | ∀ n : ℕ, 2 * b ≠ -(n : ℂ)} :=
  fun _ hb ↦ analyticAt_Gamma_two_mul_div_Gamma_sq hb

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

/-- The meromorphic order of `Gammaℝ` at `s` equals that of `Gamma` at `s / 2`. -/
@[simp]
theorem meromorphicOrderAt_Gammaℝ (s : ℂ) :
    meromorphicOrderAt Gammaℝ s = meromorphicOrderAt Gamma (s / 2) := by
  have he : Gammaℝ = (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-z / 2)) *
      (Gamma ∘ fun z : ℂ ↦ z / 2) := funext Gammaℝ_def
  have ha : AnalyticAt ℂ (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-z / 2)) s := by
    fun_prop (disch := exact Or.inl (by simpa using Real.pi_pos))
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
  have ha : AnalyticAt ℂ (fun z : ℂ ↦ 2 * (2 * Real.pi : ℂ) ^ (-z)) s := by
    have hp : (2 * Real.pi : ℂ) ∈ slitPlane :=
      Or.inl (by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)
    exact analyticAt_const.mul (analyticAt_const.cpow (by fun_prop) hp)
  have hn : 2 * (2 * Real.pi : ℂ) ^ (-s) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [he, meromorphicOrderAt_mul_of_ne_zero ha hn]

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
