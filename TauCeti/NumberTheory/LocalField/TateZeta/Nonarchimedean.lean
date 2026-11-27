/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuasiCharacter
public import TauCeti.NumberTheory.LocalField.TateZeta.Basic
public import TauCeti.NumberTheory.LocalField.Units.Haar
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.LocallyConstant.Algebra
import TauCeti.NumberTheory.LocalField.HaarCharacter
import TauCeti.NumberTheory.LocalField.NormedField
import TauCeti.NumberTheory.LocalField.Units.Decomposition

/-!
# The local Tate zeta integral over a nonarchimedean local field

Let `K` be a nonarchimedean local field with residue field of cardinality `q`, normalized
valuation `v_K` and normalized absolute value `|x| = q ^ (-v_K(x))`, and let `ν` be a Haar measure
on `Kˣ`. For a quasi-character `ω : Kˣ → ℂˣ` of exponent `r` (so `‖ω(x)‖ = |x| ^ r`) and a
continuous compactly supported test function `f : K → ℂ`, this file studies Tate's local zeta
integral

`z(s, ω; f) = ∫_{Kˣ} f(x) ω(x) |x| ^ s dν(x)`

(`TauCeti.TateZeta.localZetaIntegral` with `a = |·|`).

The proofs cut `Kˣ` into the compact shells `{x | v_K(x) = n}`, `n ∈ ℤ`. Each shell is a
translate `ϖ ^ n 𝒪[K]ˣ` of the units of the ring of integers, so it has the `ν`-mass of `𝒪[K]ˣ`;
on it `|x| ^ s = (q ^ (-s)) ^ n`; and a compactly supported `f` vanishes on the shells with
`n < -N` for some `N`. Hence the integral is the Laurent series
`z(s, ω; f) = ∑ₙ dₙ (q ^ (-s)) ^ n` with `dₙ = ∫_{v_K(x) = n} f ω dν`, `‖dₙ‖ ≤ C q ^ (-n r)`
and `dₙ = 0` for `n < -N`, which converges absolutely for `re s + r > 0`.

## Main results

* `TauCeti.TateZeta.integrable_mul_of_characterExponent_pos`: `x ↦ f(x) c(x)` is integrable on
  `Kˣ` for every quasi-character `c` of positive exponent.
* `TauCeti.TateZeta.integrable_localZetaIntegral`: the integrand of `z(s, ω; f)` is integrable
  for `re s + r > 0`; for unitary `ω` this is the half-plane `re s > 0`.
* `TauCeti.TateZeta.differentiableOn_localZetaIntegral`: `s ↦ z(s, ω; f)` is holomorphic on
  `re s + r > 0`.
* `TauCeti.TateZeta.localZetaIntegral_indicator_integer_of_unramified`: for `ω` unramified,
  `z(s, ω; 1_𝒪) = ν(𝒪[K]ˣ) (1 - ω(ϖ) q ^ (-s))⁻¹` on `re s + r > 0`, where `ϖ` is a uniformizer;
  with the normalized measure `TauCeti.unitsHaar K` (`ν(𝒪[K]ˣ) = 1`) this is the local
  `L`-factor `(1 - ω(ϖ) q ^ (-s))⁻¹`
  (`localZetaIntegral_unitsHaar_indicator_integer_of_unramified`), and for `ω = 1` it is
  `(1 - q ^ (-s))⁻¹` on `re s > 0` (`localZetaIntegral_unitsHaar_indicator_integer_one`).
* `TauCeti.TateZeta.localZetaIntegral_eq_zero_of_ramified`: for `ω` ramified, that is
  nontrivial on `𝒪[K]ˣ`, `z(s, ω; f) = 0` for every `f` invariant under `𝒪[K]ˣ`, in particular
  for `f = 1_𝒪` (`localZetaIntegral_indicator_integer_of_ramified`).

## Implementation notes

The measure is any Haar measure on `Kˣ`, so the statements hold for Kudla's normalization
`TauCeti.unitsHaar K` (`𝒪[K]ˣ` of mass one) and for Tate's (`𝒪[K]ˣ` of mass `N𝔡^(-1/2)` at a
completion of a number field) alike; the unramified value records the mass of `𝒪[K]ˣ`. The
characteristic of `K` is arbitrary.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels
  and A. Fröhlich, eds., *Algebraic Number Theory*, §2.4.
* S. S. Kudla, *Tate's thesis*, in J. Bernstein and S. Gelbart, eds., *An Introduction to the
  Langlands Program*, §3, (3.4)–(3.6).
* At the completions of a number field, absolute convergence and the unramified Euler factor
  are `finiteLocalIdelicZetaIntegral_integrable` and `finiteLocalEulerFactor_norm` in
  `RiemannMasullo/Ch03_IdelicZeta/Sec3b.lean` of the Riemann–Masullo formalization
  (https://github.com/mccorvie/riemann-masullo); this file proves them for every
  nonarchimedean local field and every Haar measure, by the shell decomposition above.
-/

public section
noncomputable section

open MeasureTheory Complex ValuativeRel
open scoped NNReal

namespace TauCeti.TateZeta

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### Valuation shells -/

variable (K) in
/-- The shell `{x ∈ Kˣ | v_K(x) = n}` of the units of valuation `n`. -/
private def shell (n : ℤ) : Set Kˣ := normalizedValuation K ⁻¹' {Multiplicative.ofAdd n}

private theorem mem_shell {n : ℤ} {x : Kˣ} :
    x ∈ shell K n ↔ (normalizedValuation K x).toAdd = n := by
  simp only [shell, Set.mem_preimage, Set.mem_singleton_iff]
  exact ⟨fun h ↦ by rw [h, toAdd_ofAdd], fun h ↦ by rw [← h, ofAdd_toAdd]⟩

private theorem isOpen_shell (n : ℤ) : IsOpen (shell K n) :=
  (isOpen_discrete _).preimage (continuous_normalizedValuation K)

private theorem pairwise_disjoint_shell : Pairwise (Function.onFun Disjoint (shell K)) :=
  fun _ _ h ↦ Set.disjoint_left.2 fun _ hm hn ↦ h ((mem_shell.1 hm).symm.trans (mem_shell.1 hn))

private theorem iUnion_shell : ⋃ n, shell K n = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ Set.mem_iUnion.2 ⟨_, mem_shell.2 rfl⟩

/-- The shell of valuation `n` is the translate `ϖ ^ n 𝒪[K]ˣ` of the units of `𝒪[K]`. -/
private theorem shell_eq_preimage {ϖ : Kˣ} (hϖ : IsUniformizer K ϖ) (n : ℤ) :
    shell K n = (fun x ↦ ϖ ^ (-n) * x) ⁻¹' (unitFiltration K 0 : Set Kˣ) := by
  ext x
  rw [Set.mem_preimage, SetLike.mem_coe, ← ker_normalizedValuation, MonoidHom.mem_ker, map_mul,
    normalizedValuation_zpow_of_eq_ofAdd_one ((isUniformizer_def ϖ).1 hϖ), mem_shell]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← ofAdd_toAdd (normalizedValuation K x), h, ← ofAdd_add, neg_add_cancel, ofAdd_zero]
  · have h' := congrArg Multiplicative.toAdd h
    rw [toAdd_mul, toAdd_ofAdd, toAdd_one] at h'
    omega

private theorem isCompact_shell (n : ℤ) : IsCompact (shell K n) := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUniformizer K
  rw [shell_eq_preimage hϖ]
  exact (Homeomorph.mulLeft (ϖ ^ (-n))).isCompact_preimage.2 (isCompact_unitFiltration 0)

/-- `|x| = q ^ (-n)` on the shell of valuation `n`. -/
private theorem normalizedAbsoluteValue_of_mem_shell {n : ℤ} {x : Kˣ} (hx : x ∈ shell K n) :
    (normalizedAbsoluteValue K (x : K) : ℝ) = (Nat.card 𝓀[K] : ℝ) ^ (-n) := by
  rw [coe_normalizedAbsoluteValue_eq_zpow, mem_shell.1 hx]

/-- `ω_s(x) = (q ^ (-s)) ^ n` on the shell of valuation `n`. -/
private theorem normalizedAbsCpowCharacter_of_mem_shell (s : ℂ) {n : ℤ} {x : Kˣ}
    (hx : x ∈ shell K n) :
    (normalizedAbsCpowCharacter K s x : ℂ) = ((Nat.card 𝓀[K] : ℂ) ^ (-s)) ^ n := by
  rw [coe_normalizedAbsCpowCharacter_apply_eq_zpow, mem_shell.1 hx]

/-- `‖c(x)‖ = (q ^ (-r)) ^ n` on the shell of valuation `n`, for `c` of exponent `r`. -/
private theorem norm_apply_of_mem_shell (c : Kˣ →ₜ* ℂˣ) {n : ℤ} {x : Kˣ}
    (hx : x ∈ shell K n) :
    ‖(c x : ℂ)‖ = ((Nat.card 𝓀[K] : ℝ) ^ (-characterExponent K c)) ^ n := by
  have hq := natCard_residueField_pos (K := K) (R := ℝ)
  rw [norm_coe_apply_eq_rpow_characterExponent, normalizedAbsoluteValue_of_mem_shell hx,
    ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le]
  congr 1
  push_cast
  ring

/-- A compactly supported function on `K` vanishes on the shells of valuation `n < -N`, for some
`N`. -/
private theorem exists_eq_zero_of_lt_shell {f : K → ℂ} (hf : HasCompactSupport f) :
    ∃ N : ℤ, ∀ n < -N, ∀ x ∈ shell K n, f x = 0 := by
  obtain ⟨M, hM⟩ := hf.isCompact.bddAbove_image continuous_normalizedAbsoluteValue.continuousOn
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt M (one_lt_natCard_residueField (K := K) (R := ℝ))
  refine ⟨N, fun n hn x hx ↦ by_contra fun h ↦ ?_⟩
  have hle : (normalizedAbsoluteValue K (x : K) : ℝ) ≤ M := hM ⟨x, subset_tsupport _ h, rfl⟩
  rw [normalizedAbsoluteValue_of_mem_shell hx] at hle
  have hlt : (Nat.card 𝓀[K] : ℝ) ^ ((N : ℤ)) < (Nat.card 𝓀[K] : ℝ) ^ (-n) :=
    zpow_lt_zpow_right₀ (one_lt_natCard_residueField (K := K)) (by omega)
  rw [zpow_natCast] at hlt
  linarith

/-- The indicator `1_𝒪` of the ring of integers is continuous: `𝒪[K]` is clopen. -/
private theorem continuous_indicator_integer :
    Continuous ((𝒪[K] : Set K).indicator (1 : K → ℂ)) := by
  rw [← LocallyConstant.coe_charFn ℂ (Valuation.isClopen_integer (v := valuation K))]
  exact LocallyConstant.continuous _

/-- The indicator `1_𝒪` of the ring of integers has compact support. -/
private theorem hasCompactSupport_indicator_integer :
    HasCompactSupport ((𝒪[K] : Set K).indicator (1 : K → ℂ)) :=
  HasCompactSupport.intro (by simpa using (integerPositiveCompacts K).isCompact)
    fun _ hx ↦ Set.indicator_of_notMem hx _

/-- A unit of valuation `n` lies in `𝒪[K]` exactly when `n ≥ 0`. -/
private theorem mem_integer_iff_of_mem_shell {n : ℤ} {x : Kˣ} (hx : x ∈ shell K n) :
    (x : K) ∈ 𝒪[K] ↔ 0 ≤ n := by
  rw [mem_integer_iff_normalizedAbsoluteValue_le_one, ← NNRat.cast_le (K := ℝ),
    NNRat.cast_one, normalizedAbsoluteValue_of_mem_shell hx,
    zpow_le_one_iff_right₀ (one_lt_natCard_residueField (K := K)), neg_nonpos]

/-- An unramified quasi-character takes the value `ω(ϖ) ^ n` on the shell of valuation `n`. -/
private theorem apply_of_mem_shell_of_unramified {ω : Kˣ →ₜ* ℂˣ}
    (hω : ∀ u ∈ unitFiltration K 0, ω u = 1) {ϖ : Kˣ} (hϖ : IsUniformizer K ϖ) {n : ℤ}
    {x : Kˣ} (hx : x ∈ shell K n) : (ω x : ℂ) = (ω ϖ : ℂ) ^ n := by
  have hu : ϖ ^ (-n) * x ∈ unitFiltration K 0 := by
    have := hx
    rwa [shell_eq_preimage hϖ] at this
  have hx' : x = ϖ ^ n * (ϖ ^ (-n) * x) := by group
  rw [hx', map_mul, hω _ hu, mul_one, map_zpow, Units.val_zpow_eq_zpow_val]

variable [MeasurableSpace K] [BorelSpace K]

private theorem measurableSet_shell (n : ℤ) : MeasurableSet (shell K n) :=
  (isOpen_shell n).measurableSet

/-- Every shell has the mass of `𝒪[K]ˣ` for a left-invariant measure. -/
private theorem measure_shell (ν : Measure Kˣ) [ν.IsMulLeftInvariant] (n : ℤ) :
    ν (shell K n) = ν (unitFiltration K 0) := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUniformizer K
  rw [shell_eq_preimage hϖ, measure_preimage_mul]

/-- The geometric bound `n ↦ ρ ^ n` cut off below `-N` is summable over `ℤ`, for `0 < ρ < 1`. -/
private theorem summable_ite_zpow (N : ℤ) {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ : ρ < 1) :
    Summable fun n : ℤ ↦ if -N ≤ n then ρ ^ n else 0 := by
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine (summable_geometric_of_lt_one hρ₀.le hρ).of_nonneg_of_le
      (fun k ↦ by split_ifs <;> positivity) fun k ↦ ?_
    split_ifs
    · rw [zpow_natCast]
    · positivity
  · refine summable_of_ne_finset_zero (s := Finset.range N.toNat) fun k hk ↦ ?_
    rw [Finset.mem_range, not_lt] at hk
    exact ite_eq_right_iff.2 fun h ↦ absurd h (by omega)

/-- For `1 ≤ q` and `a ≤ t ≤ b`, `(q ^ (-t)) ^ n ≤ (q ^ (-a)) ^ n + (q ^ (-b)) ^ n` for every
integer `n`: the first term dominates for `n ≥ 0` and the second for `n < 0`. -/
private theorem zpow_rpow_neg_le_add {q a b t : ℝ} (hq : 1 ≤ q) (ha : a ≤ t) (hb : t ≤ b)
    (n : ℤ) : (q ^ (-t)) ^ n ≤ (q ^ (-a)) ^ n + (q ^ (-b)) ^ n := by
  have hq₀ : 0 ≤ q := zero_le_one.trans hq
  simp only [← Real.rpow_intCast, ← Real.rpow_mul hq₀]
  rcases le_or_gt 0 n with hn | hn
  · have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
    exact le_add_of_le_of_nonneg (Real.rpow_le_rpow_of_exponent_le hq (by nlinarith))
      (by positivity)
  · have hn' : (n : ℝ) < 0 := by exact_mod_cast hn
    exact le_add_of_nonneg_of_le (by positivity)
      (Real.rpow_le_rpow_of_exponent_le hq (by nlinarith))

/-! ### Absolute convergence -/

/-- **Absolute convergence on shells.** For a Haar measure `ν` on `Kˣ`, a continuous compactly
supported `f : K → ℂ` and a quasi-character `c` of positive exponent, `x ↦ f(x) c(x)` is
integrable on `Kˣ`. -/
theorem integrable_mul_of_characterExponent_pos (ν : Measure Kˣ) [ν.IsHaarMeasure] {f : K → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) {c : Kˣ →ₜ* ℂˣ}
    (hc : 0 < characterExponent K c) :
    Integrable (fun x : Kˣ ↦ f x * (c x : ℂ)) ν := by
  obtain ⟨B, hB⟩ := hf.bounded_above_of_compact_support hfc
  obtain ⟨N, hN⟩ := exists_eq_zero_of_lt_shell hfc
  have hq := one_lt_natCard_residueField (K := K) (R := ℝ)
  set ρ := (Nat.card 𝓀[K] : ℝ) ^ (-characterExponent K c)
  have hρ₀ : 0 < ρ := Real.rpow_pos_of_pos (zero_lt_one.trans hq) _
  have hρ : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  let g : C(Kˣ, ℂ) := ⟨fun x ↦ f x * (c x : ℂ),
    (hf.comp Units.continuous_val).mul (Units.continuous_val.comp c.continuous)⟩
  let s (n : ℤ) : TopologicalSpace.Compacts Kˣ := ⟨shell K n, isCompact_shell n⟩
  have hite (n : ℤ) : 0 ≤ (if -N ≤ n then ρ ^ n else 0) := by split_ifs <;> positivity
  have hbound (n : ℤ) :
      ‖g.restrict (s n)‖ ≤ max B 0 * (if -N ≤ n then ρ ^ n else 0) := by
    refine (ContinuousMap.norm_le _ (by have := hite n; positivity)).2 fun ⟨x, hx⟩ ↦ ?_
    change ‖f x * (c x : ℂ)‖ ≤ _
    split_ifs with hn
    · rw [norm_mul, norm_apply_of_mem_shell c hx]
      exact mul_le_mul_of_nonneg_right ((hB x).trans (le_max_left _ _)) (by positivity)
    · rw [hN n (by omega) x hx, zero_mul, norm_zero, mul_zero]
  refine integrable_of_summable_norm_restrict (f := g) (s := s) ?_ iUnion_shell
  refine ((summable_ite_zpow N hρ₀ hρ).mul_left (max B 0 * ν.real (shell K 0))).of_nonneg_of_le
    (fun n ↦ by positivity) fun n ↦ ?_
  have hsn : ν.real (s n) = ν.real (shell K 0) := by
    change ν.real (shell K n) = _
    rw [measureReal_def, measureReal_def, measure_shell, measure_shell]
  rw [hsn]
  calc ‖g.restrict (s n)‖ * ν.real (shell K 0)
      ≤ (max B 0 * if -N ≤ n then ρ ^ n else 0) * ν.real (shell K 0) :=
        mul_le_mul_of_nonneg_right (hbound n) measureReal_nonneg
    _ = _ := by ring

/-- **Convergence of the local zeta integral.** For a Haar measure `ν` on `Kˣ`, a continuous
compactly supported `f : K → ℂ` and a quasi-character `ω` of exponent `r`, the integrand
`f(x) ω(x) |x| ^ s` of `z(s, ω; f)` is integrable on `Kˣ` for `re s + r > 0`. For unitary `ω` this
is the half-plane `re s > 0`. -/
theorem integrable_localZetaIntegral (ν : Measure Kˣ) [ν.IsHaarMeasure] (ω : Kˣ →ₜ* ℂˣ)
    {f : K → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) {s : ℂ}
    (hs : 0 < s.re + characterExponent K ω) :
    Integrable (fun x : Kˣ ↦
      f x * (ω x : ℂ) * ((normalizedAbsoluteValue K (x : K) : ℝ) : ℂ) ^ s) ν := by
  refine (integrable_mul_of_characterExponent_pos ν hf hfc
    (c := ω * normalizedAbsCpowCharacter K s) (by simpa [add_comm] using hs)).congr
    (Filter.Eventually.of_forall fun x ↦ ?_)
  simp [mul_assoc]

/-- The local zeta integral as the sum over the shells `v_K(x) = n` of
`(∫_{v_K(x) = n} f ω dν) (q ^ (-s)) ^ n`, in the half-plane of absolute convergence. -/
private theorem localZetaIntegral_eq_tsum (ν : Measure Kˣ) [ν.IsHaarMeasure] (ω : Kˣ →ₜ* ℂˣ)
    {f : K → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) {s : ℂ}
    (hs : 0 < s.re + characterExponent K ω) :
    localZetaIntegral ν (fun x ↦ (normalizedAbsoluteValue K x : ℝ)) ω f s =
      ∑' n : ℤ, (∫ x in shell K n, f x * (ω x : ℂ) ∂ν) * ((Nat.card 𝓀[K] : ℂ) ^ (-s)) ^ n := by
  rw [localZetaIntegral, ← setIntegral_univ, ← iUnion_shell,
    integral_iUnion measurableSet_shell pairwise_disjoint_shell
      (integrable_localZetaIntegral ν ω hf hfc hs).integrableOn]
  refine tsum_congr fun n ↦ ?_
  rw [← integral_mul_const]
  refine setIntegral_congr_fun (measurableSet_shell n) fun x hx ↦ ?_
  rw [← normalizedAbsCpowCharacter_of_mem_shell s hx, coe_normalizedAbsCpowCharacter_apply]

/-- The shell coefficient `∫_{v_K(x) = n} f ω dν` has norm at most `B (q ^ (-r)) ^ n ν(𝒪[K]ˣ)`,
and vanishes below the support of `f`. -/
private theorem norm_setIntegral_shell_le (ν : Measure Kˣ) [ν.IsHaarMeasure] (ω : Kˣ →ₜ* ℂˣ)
    {f : K → ℂ} {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) {N : ℤ}
    (hN : ∀ n < -N, ∀ x ∈ shell K n, f x = 0) (n : ℤ) :
    ‖∫ x in shell K n, f x * (ω x : ℂ) ∂ν‖ ≤
      max B 0 * ν.real (shell K 0) *
        (if -N ≤ n then ((Nat.card 𝓀[K] : ℝ) ^ (-characterExponent K ω)) ^ n else 0) := by
  have hfin : ν (shell K n) < ⊤ := (isCompact_shell n).measure_lt_top
  have hsn : ν.real (shell K n) = ν.real (shell K 0) := by
    rw [measureReal_def, measureReal_def, measure_shell, measure_shell]
  split_ifs with hn
  · refine (norm_setIntegral_le_of_norm_le_const (C := max B 0 *
      ((Nat.card 𝓀[K] : ℝ) ^ (-characterExponent K ω)) ^ n) hfin fun x hx ↦ ?_).trans_eq
      (by rw [hsn]; ring)
    rw [norm_mul, norm_apply_of_mem_shell ω hx]
    exact mul_le_mul_of_nonneg_right ((hB x).trans (le_max_left _ _)) (by positivity)
  · rw [mul_zero, norm_le_zero_iff]
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ ?_
    rw [hN n (by omega) x hx, zero_mul]

/-- On a vertical strip `a < re s < b` with `a + r > 0`, the shell series of `z(s, ω; f)` is
dominated termwise by a summable sequence, so `s ↦ z(s, ω; f)` is holomorphic there. -/
private theorem differentiableOn_localZetaIntegral_strip (ν : Measure Kˣ) [ν.IsHaarMeasure]
    (ω : Kˣ →ₜ* ℂˣ) {f : K → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) {a b : ℝ}
    (ha : 0 < a + characterExponent K ω) (hab : a < b) :
    DifferentiableOn ℂ (localZetaIntegral ν (fun x ↦ (normalizedAbsoluteValue K x : ℝ)) ω f)
      {s | a < s.re ∧ s.re < b} := by
  set r := characterExponent K ω
  obtain ⟨B, hB⟩ := hf.bounded_above_of_compact_support hfc
  obtain ⟨N, hN⟩ := exists_eq_zero_of_lt_shell hfc
  have hq := one_lt_natCard_residueField (K := K) (R := ℝ)
  have hq₀ : (0 : ℝ) < Nat.card 𝓀[K] := zero_lt_one.trans hq
  have hU : IsOpen {s : ℂ | a < s.re ∧ s.re < b} :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  set ρa := (Nat.card 𝓀[K] : ℝ) ^ (-(r + a))
  set ρb := (Nat.card 𝓀[K] : ℝ) ^ (-(r + b))
  set C := max B 0 * ν.real (shell K 0)
  have hterm (n : ℤ) (s : ℂ) (hs : a < s.re ∧ s.re < b) :
      ‖(∫ x in shell K n, f x * (ω x : ℂ) ∂ν) * ((Nat.card 𝓀[K] : ℂ) ^ (-s)) ^ n‖ ≤
        C * ((if -N ≤ n then ρa ^ n else 0) + (if -N ≤ n then ρb ^ n else 0)) := by
    have hw : ‖((Nat.card 𝓀[K] : ℂ) ^ (-s)) ^ n‖ = ((Nat.card 𝓀[K] : ℝ) ^ (-s.re)) ^ n := by
      rw [norm_zpow, ← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos hq₀, neg_re]
    rw [norm_mul, hw]
    refine (mul_le_mul_of_nonneg_right (norm_setIntegral_shell_le ν ω hB hN n)
      (by positivity)).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    split_ifs
    · rw [← mul_zpow, ← Real.rpow_add hq₀, ← neg_add]
      exact zpow_rpow_neg_le_add hq.le (by linarith [hs.1]) (by linarith [hs.2]) n
    · simp
  have hsum : Summable fun n : ℤ ↦
      C * ((if -N ≤ n then ρa ^ n else 0) + (if -N ≤ n then ρb ^ n else 0)) :=
    ((summable_ite_zpow N (Real.rpow_pos_of_pos hq₀ _)
      (Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith))).add
      (summable_ite_zpow N (Real.rpow_pos_of_pos hq₀ _)
        (Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)))).mul_left C
  have hd : DifferentiableOn ℂ (fun s : ℂ ↦ ∑' n : ℤ,
      (∫ x in shell K n, f x * (ω x : ℂ) ∂ν) * ((Nat.card 𝓀[K] : ℂ) ^ (-s)) ^ n)
      {s | a < s.re ∧ s.re < b} := by
    refine differentiableOn_tsum_of_summable_norm hsum (fun n ↦ ?_) hU hterm
    refine (DifferentiableOn.zpow ?_ (Or.inl fun s _ ↦ ?_)).const_mul _
    · exact (differentiable_neg.const_cpow (Or.inl (by exact_mod_cast hq₀.ne'))).differentiableOn
    · exact cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast hq₀.ne'))
  exact hd.congr fun s hs ↦ localZetaIntegral_eq_tsum ν ω hf hfc (by linarith [hs.1])

/-- **Holomorphy of the local zeta integral.** For a Haar measure `ν` on `Kˣ`, a continuous
compactly supported `f : K → ℂ` and a quasi-character `ω` of exponent `r`, the function
`s ↦ z(s, ω; f)` is holomorphic on the half-plane `re s + r > 0`. -/
theorem differentiableOn_localZetaIntegral (ν : Measure Kˣ) [ν.IsHaarMeasure] (ω : Kˣ →ₜ* ℂˣ)
    {f : K → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    DifferentiableOn ℂ (localZetaIntegral ν (fun x ↦ (normalizedAbsoluteValue K x : ℝ)) ω f)
      {s | 0 < s.re + characterExponent K ω} := by
  intro s₀ (hs₀ : 0 < s₀.re + characterExponent K ω)
  -- Use the strip `(re s₀ - r) / 2 < re s < re s₀ + 1` around `s₀`.
  have hU : IsOpen {s : ℂ | (s₀.re - characterExponent K ω) / 2 < s.re ∧ s.re < s₀.re + 1} :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  refine ((differentiableOn_localZetaIntegral_strip ν ω hf hfc (by linarith)
    (by linarith)).differentiableAt
    (hU.mem_nhds ⟨by linarith, by linarith⟩)).differentiableWithinAt

/-! ### Explicit values -/

/-- **The unramified local factor.** For an unramified quasi-character `ω` of exponent `r`, a
uniformizer `ϖ` and `re s + r > 0`,
`z(s, ω; 1_𝒪) = ν(𝒪[K]ˣ) (1 - ω(ϖ) q ^ (-s))⁻¹`. -/
theorem localZetaIntegral_indicator_integer_of_unramified (ν : Measure Kˣ) [ν.IsHaarMeasure]
    {ω : Kˣ →ₜ* ℂˣ} (hω : ∀ u ∈ unitFiltration K 0, ω u = 1) {ϖ : Kˣ}
    (hϖ : IsUniformizer K ϖ) {s : ℂ} (hs : 0 < s.re + characterExponent K ω) :
    localZetaIntegral ν (fun x ↦ (normalizedAbsoluteValue K x : ℝ)) ω
        ((𝒪[K] : Set K).indicator 1) s =
      ν.real (unitFiltration K 0 : Set Kˣ) * (1 - ω ϖ * (Nat.card 𝓀[K] : ℂ) ^ (-s))⁻¹ := by
  have hq := one_lt_natCard_residueField (K := K) (R := ℝ)
  have hq₀ : (0 : ℝ) < Nat.card 𝓀[K] := zero_lt_one.trans hq
  have hϖ1 : ϖ ∈ shell K 1 := mem_shell.2 (by rw [(isUniformizer_def ϖ).1 hϖ, toAdd_ofAdd])
  set c : ℂ := (ν.real (unitFiltration K 0 : Set Kˣ) : ℂ)
  set w := (ω ϖ : ℂ) * (Nat.card 𝓀[K] : ℂ) ^ (-s)
  have hw : ‖w‖ < 1 := by
    rw [norm_mul, norm_apply_of_mem_shell ω hϖ1, zpow_one, ← ofReal_natCast,
      norm_cpow_eq_rpow_re_of_pos hq₀, neg_re, ← Real.rpow_add hq₀]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  have hd (n : ℤ) : (∫ x in shell K n, (𝒪[K] : Set K).indicator 1 (x : K) * (ω x : ℂ) ∂ν) *
      ((Nat.card 𝓀[K] : ℂ) ^ (-s)) ^ n = if 0 ≤ n then c * w ^ n else 0 := by
    have hconst : ∀ x ∈ shell K n, (𝒪[K] : Set K).indicator 1 (x : K) * (ω x : ℂ) =
        if 0 ≤ n then (ω ϖ : ℂ) ^ n else 0 := fun x hx ↦ by
      by_cases hn : 0 ≤ n
      · simp only [hn, ↓reduceIte]
        rw [Set.indicator_of_mem ((mem_integer_iff_of_mem_shell hx).2 hn),
          Pi.one_apply, one_mul, apply_of_mem_shell_of_unramified hω hϖ hx]
      · simp only [hn, ↓reduceIte]
        rw [Set.indicator_of_notMem (mt (mem_integer_iff_of_mem_shell hx).1 hn),
          zero_mul]
    have hsn : ν.real (shell K n) = ν.real (unitFiltration K 0 : Set Kˣ) := by
      rw [measureReal_def, measureReal_def, measure_shell]
    rw [setIntegral_congr_fun (measurableSet_shell n) hconst, setIntegral_const, hsn,
      Complex.real_smul]
    split_ifs
    · rw [mul_zpow]
      ring
    · rw [mul_zero, zero_mul]
  rw [localZetaIntegral_eq_tsum ν ω continuous_indicator_integer
    hasCompactSupport_indicator_integer hs]
  simp_rw [hd]
  refine HasSum.tsum_eq ?_
  set g : ℤ → ℂ := fun n ↦ if 0 ≤ n then c * w ^ n else 0
  have h₁ : HasSum (fun n : ℕ ↦ g n) (c * (1 - w)⁻¹) := by
    simpa [g] using (hasSum_geometric_of_norm_lt_one hw).mul_left c
  have h₂ : HasSum (fun n : ℕ ↦ g (-(n + 1))) 0 := by
    convert hasSum_zero with n
    exact ite_eq_right_iff.2 fun h ↦ absurd h (by omega)
  simpa using h₁.of_nat_of_neg_add_one h₂

/-- **The unramified local factor in Kudla's normalization.** With the Haar measure
`TauCeti.unitsHaar K` giving `𝒪[K]ˣ` mass one, an unramified quasi-character `ω` of exponent `r`
and `re s + r > 0`, `z(s, ω; 1_𝒪) = (1 - ω(ϖ) q ^ (-s))⁻¹`. For `ω = 1` this is
`(1 - q ^ (-s))⁻¹` on `re s > 0`. -/
theorem localZetaIntegral_unitsHaar_indicator_integer_of_unramified {ω : Kˣ →ₜ* ℂˣ}
    (hω : ∀ u ∈ unitFiltration K 0, ω u = 1) {ϖ : Kˣ} (hϖ : IsUniformizer K ϖ) {s : ℂ}
    (hs : 0 < s.re + characterExponent K ω) :
    localZetaIntegral (unitsHaar K) (fun x ↦ (normalizedAbsoluteValue K x : ℝ)) ω
        ((𝒪[K] : Set K).indicator 1) s =
      (1 - ω ϖ * (Nat.card 𝓀[K] : ℂ) ^ (-s))⁻¹ := by
  rw [localZetaIntegral_indicator_integer_of_unramified _ hω hϖ hs, measureReal_def,
    unitsHaar_unitFiltration_zero, ENNReal.toReal_one, ofReal_one, one_mul]

/-- `z(s, 1; 1_𝒪) = (1 - q ^ (-s))⁻¹` on `re s > 0`, for the Haar measure giving `𝒪[K]ˣ`
mass one. At `s = 0` the integrand is not integrable, since its shell integrals are all `1`. -/
theorem localZetaIntegral_unitsHaar_indicator_integer_one {s : ℂ} (hs : 0 < s.re) :
    localZetaIntegral (unitsHaar K) (fun x ↦ (normalizedAbsoluteValue K x : ℝ)) 1
        ((𝒪[K] : Set K).indicator 1) s =
      (1 - (Nat.card 𝓀[K] : ℂ) ^ (-s))⁻¹ := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUniformizer K
  simpa using localZetaIntegral_unitsHaar_indicator_integer_of_unramified
    (ω := 1) (fun _ _ ↦ rfl) hϖ (s := s) (by simpa using hs)

/-- **Ramified characters annihilate `𝒪[K]ˣ`-invariant test functions.** If `ω` is nontrivial
on `𝒪[K]ˣ`, then `z(s, ω; f) = 0` for every `s` and every `f` invariant under multiplication by
`𝒪[K]ˣ`: the substitution `x ↦ u x` multiplies the integral by `ω(u)⁻¹ ≠ 1`. -/
theorem localZetaIntegral_eq_zero_of_ramified (ν : Measure Kˣ) [ν.IsHaarMeasure]
    {ω : Kˣ →ₜ* ℂˣ} {u : Kˣ} (hu : u ∈ unitFiltration K 0) (hωu : ω u ≠ 1) {f : K → ℂ}
    (hf : ∀ v ∈ unitFiltration K 0, ∀ x, f (v * x) = f x) (s : ℂ) :
    localZetaIntegral ν (fun x ↦ (normalizedAbsoluteValue K x : ℝ)) ω f s = 0 := by
  have h := localZetaIntegral_comp_mul_left ν (fun x ↦ (normalizedAbsoluteValue K x : ℝ)) ω
    (fun x ↦ coe_normalizedAbsoluteValue_pos x) (fun x y ↦ by simp) f u s
  have hu1 : (normalizedAbsoluteValue K (u : K) : ℝ) = 1 := by
    rw [coe_normalizedAbsoluteValue_eq_zpow,
      (normalizedValuation_eq_one_iff u).2 ((mem_unitFiltration_zero u).1 hu), toAdd_one,
      neg_zero, zpow_zero]
  simp only [hf u hu, hu1, ofReal_one, one_cpow, mul_one] at h
  have hne : (ω u : ℂ)⁻¹ ≠ 1 := fun h' ↦ hωu (Units.ext (by simpa using h'))
  have h0 : (1 - (ω u : ℂ)⁻¹) *
      localZetaIntegral ν (fun x ↦ (normalizedAbsoluteValue K x : ℝ)) ω f s = 0 := by
    linear_combination h
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hne.symm)

/-- For `ω` nontrivial on `𝒪[K]ˣ`, `z(s, ω; 1_𝒪) = 0` for every `s`. -/
theorem localZetaIntegral_indicator_integer_of_ramified (ν : Measure Kˣ) [ν.IsHaarMeasure]
    {ω : Kˣ →ₜ* ℂˣ} {u : Kˣ} (hu : u ∈ unitFiltration K 0) (hωu : ω u ≠ 1) (s : ℂ) :
    localZetaIntegral ν (fun x ↦ (normalizedAbsoluteValue K x : ℝ)) ω
      ((𝒪[K] : Set K).indicator 1) s = 0 := by
  refine localZetaIntegral_eq_zero_of_ramified ν hu hωu (fun v hv x ↦ ?_) s
  have hv1 : normalizedAbsoluteValue K (v : K) = 1 := by
    rw [normalizedAbsoluteValue_coe,
      (normalizedValuation_eq_one_iff v).2 ((mem_unitFiltration_zero v).1 hv), toAdd_one,
      neg_zero, zpow_zero]
  simp only [Set.indicator, SetLike.mem_coe, mem_integer_iff_normalizedAbsoluteValue_le_one,
    map_mul, hv1, one_mul, Pi.one_apply]

end TauCeti.TateZeta
