/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.TateZeta.FunctionalEquation
public import TauCeti.NumberTheory.LocalField.Units.Shell
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.NumberTheory.LocalField.HaarCharacter
import TauCeti.NumberTheory.LocalField.Uniformizer
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Continuation of the local zeta integral over a nonarchimedean local field

Let `K` be a nonarchimedean local field with residue field of cardinality `q`, `ν` a Haar measure
on `Kˣ` and `ω` a quasi-character of exponent `r`. For a locally constant compactly supported
`f : K → ℂ`, the function `g = f - f(0) 1_𝒪` vanishes near `0` and far out, hence on all but
finitely many valuation shells `{v_K(x) = n}`, so its zeta integral is the Laurent polynomial

`z(s, ω; g) = ∑_{a ≤ n < b} (∫_{v_K(x) = n} g ω dν) (q ^ (-s)) ^ n`,

an entire function of `s`. Hence `z(s, ω; f) = P(s) + f(0) z(s, ω; 1_𝒪)` with `P` entire, and
the explicit values of `z(s, ω; 1_𝒪)` (`TauCeti.NumberTheory.LocalField.TateZeta.Nonarchimedean`)
give the meromorphic continuation of `z(s, ω; f)`:

* for `ω` ramified, `z(s, ω; 1_𝒪) = 0`, so `z(s, ω; f)` is entire (`L(s, ω) = 1`);
* for `ω` unramified, `(1 - ω(ϖ) q ^ (-s)) z(s, ω; f) = L(s, ω)⁻¹ z(s, ω; f)` is entire.

Applied to the gamma factor `γ(s, ω, ψ) = z(1 - s, ω⁻¹; 𝓕f₀) / ν(U(K, c(ω)))` of
`TauCeti.NumberTheory.LocalField.TateZeta.FunctionalEquation`, this shows that `γ` is entire for
ramified `ω`, and that `L(1 - s, ω⁻¹)⁻¹ γ(s, ω, ψ)` is entire for unramified `ω`. These entire
functions are the input for continuing both sides of the local functional equation
`z(1 - s, ω⁻¹; 𝓕f) = γ(s, ω, ψ) z(s, ω; f)` meromorphically; that packaged meromorphic statement
is not formalized here.

## Main results

* `TauCeti.TateZeta.localZetaIntegral_eq_sum_of_forall_valuationShell`: the finite shell
  expansion.
* `TauCeti.TateZeta.exists_differentiable_localZetaIntegral_eq_add`:
  `z(s, ω; f) = P(s) + f(0) z(s, ω; 1_𝒪)` on `re s + r > 0` with `P` entire.
* `TauCeti.TateZeta.exists_differentiable_eqOn_localZetaIntegral_of_ramified`,
  `TauCeti.TateZeta.exists_differentiable_eqOn_mul_localZetaIntegral_of_unramified`: the
  ramified and unramified continuations.
* `TauCeti.TateZeta.exists_differentiable_eqOn_gammaFactor_of_ramified`,
  `TauCeti.TateZeta.exists_differentiable_eqOn_mul_gammaFactor_of_unramified`: the continuation
  of the gamma factor.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels and
  A. Fröhlich, eds., *Algebraic Number Theory*, §2.5.
* S. S. Kudla, *Tate's thesis*, in J. Bernstein and S. Gelbart, eds., *An Introduction to the
  Langlands Program*, §3, (3.11)–(3.17).
-/

public section
noncomputable section

open MeasureTheory Complex ValuativeRel Set Filter Topology

namespace TauCeti.TateZeta

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]

/-- The local zeta integral `z(s, ω; f)` for `ν` and the normalized absolute value. -/
local notation "𝔷[" ν "]" => localZetaIntegral ν (fun x ↦ (normalizedAbsoluteValue _ x : ℝ))

/-- The Fourier transform `f ↦ ∫ ψ(x y) f(x) dμ(x)` with Tate's kernel. -/
local notation "𝓕[" ψ ", " μ "]" => VectorFourier.fourierIntegral ψ μ (-LinearMap.mul _ _)

/-- **Finite shell expansion.** If a continuous `g` vanishes on the valuation shells `v_K(x) = n`
for `n < a` and for `n ≥ b`, then for every `s`,
`z(s, ω; g) = ∑_{a ≤ n < b} (∫_{v_K(x) = n} g ω dν) (q ^ (-s)) ^ n`. -/
theorem localZetaIntegral_eq_sum_of_forall_valuationShell (ν : Measure Kˣ) [ν.IsHaarMeasure]
    (ω : Kˣ →ₜ* ℂˣ) {g : K → ℂ} (hg : Continuous g) {a b : ℤ}
    (hgab : ∀ n, n < a ∨ b ≤ n → ∀ x ∈ valuationShell K n, g x = 0) (s : ℂ) :
    𝔷[ν] ω g s = ∑ n ∈ Finset.Ico a b,
      (∫ x in valuationShell K n, g x * (ω x : ℂ) ∂ν) * ((Nat.card 𝓀[K] : ℂ) ^ (-s)) ^ n := by
  set F : Kˣ → ℂ := fun x ↦ g x * (ω x : ℂ) * ((normalizedAbsoluteValue K (x : K) : ℝ) : ℂ) ^ s
  have hF : Continuous F := by
    have h : F = fun x : Kˣ ↦ g x * (ω x : ℂ) * (normalizedAbsCpowCharacter K s x : ℂ) := by
      ext x
      rw [coe_normalizedAbsCpowCharacter_apply]
    rw [h]
    exact ((hg.comp Units.continuous_val).mul (Units.continuous_val.comp ω.continuous)).mul
      (Units.continuous_val.comp (normalizedAbsCpowCharacter K s).continuous)
  set S := ⋃ n ∈ Finset.Ico a b, valuationShell K n
  have hS : ∀ x ∉ S, F x = 0 := fun x hx ↦ by
    have hn : (normalizedValuation K x).toAdd < a ∨ b ≤ (normalizedValuation K x).toAdd := by
      by_contra! h
      exact hx (mem_biUnion (Finset.mem_Ico.2 h) (mem_valuationShell.2 rfl))
    simp only [F]
    rw [hgab _ hn x (mem_valuationShell.2 rfl), zero_mul, zero_mul]
  rw [localZetaIntegral_def, ← setIntegral_eq_integral_of_forall_compl_eq_zero hS,
    integral_biUnion_finset _ (fun n _ ↦ measurableSet_valuationShell n)
      (fun m _ n _ hmn ↦ pairwise_disjoint_valuationShell hmn)
      (fun n _ ↦ hF.continuousOn.integrableOn_compact (isCompact_valuationShell n))]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [← integral_mul_const]
  refine setIntegral_congr_fun (measurableSet_valuationShell n) fun x hx ↦ ?_
  simp only [F]
  rw [← coe_normalizedAbsCpowCharacter_apply, coe_normalizedAbsCpowCharacter_apply_eq_zpow,
    mem_valuationShell.1 hx]

/-- A function vanishing on the valuation shells outside `[a, b)` has an entire local zeta
integral. -/
theorem differentiable_localZetaIntegral_of_forall_valuationShell (ν : Measure Kˣ)
    [ν.IsHaarMeasure] (ω : Kˣ →ₜ* ℂˣ) {g : K → ℂ} (hg : Continuous g) {a b : ℤ}
    (hgab : ∀ n, n < a ∨ b ≤ n → ∀ x ∈ valuationShell K n, g x = 0) :
    Differentiable ℂ (𝔷[ν] ω g) := by
  have hq : (Nat.card 𝓀[K] : ℂ) ≠ 0 := natCard_residueField_ne_zero
  rw [show 𝔷[ν] ω g = fun s ↦ _ from funext
    (localZetaIntegral_eq_sum_of_forall_valuationShell ν ω hg hgab)]
  refine Differentiable.fun_sum fun n _ ↦ (Differentiable.zpow ?_ (Or.inl fun s ↦ ?_)).const_mul _
  · exact differentiable_neg.const_cpow (Or.inl hq)
  · exact cpow_ne_zero_iff.2 (Or.inl hq)

omit [MeasurableSpace K] [BorelSpace K] in
/-- `f - f(0) 1_𝒪` vanishes on the valuation shells outside a finite interval, for a locally
constant compactly supported `f`. -/
theorem exists_forall_valuationShell_sub_indicator_eq_zero {f : K → ℂ}
    (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    ∃ a b : ℤ, ∀ n, n < a ∨ b ≤ n → ∀ x ∈ valuationShell K n,
      f x - f 0 * (𝒪[K] : Set K).indicator 1 x = 0 := by
  have hgc : HasCompactSupport fun x ↦ f x - f 0 * (𝒪[K] : Set K).indicator 1 x :=
    hfc.sub ((hasCompactSupport_indicator_integer K).mul_left)
  obtain ⟨N, hN⟩ := exists_forall_valuationShell_eq_zero_of_hasCompactSupport hgc
  -- `f = f(0)` and `1_𝒪 = 1` on a neighbourhood `{v_K(x) ≥ m}` of `0`.
  have hV : {x | f x = f 0} ∩ (𝒪[K] : Set K) ∈ 𝓝 (0 : K) :=
    inter_mem ((hf.isOpen_fiber _).mem_nhds rfl)
      ((Valuation.isClopen_integer (v := valuation K)).isOpen.mem_nhds (zero_mem _))
  obtain ⟨m, -, hm⟩ := (hasBasis_nhds_zero_valuation_le_uniformizer_zpow K).mem_iff.1 hV
  refine ⟨-N, m, fun n hn x hx ↦ ?_⟩
  rcases hn with hn | hn
  · exact hN n hn x hx
  · have hxm : (x : K) ∈ {x | f x = f 0} ∩ (𝒪[K] : Set K) :=
      hm ((valuation_le_uniformizer_zpow_iff x m).2 (by rw [mem_valuationShell.1 hx]; exact hn))
    rw [hxm.1, indicator_of_mem hxm.2, Pi.one_apply, mul_one, sub_self]

/-- **Continuation of the local zeta integral.** For a locally constant compactly supported `f`
there is an entire `P` with `z(s, ω; f) = P(s) + f(0) z(s, ω; 1_𝒪)` on the half-plane of
convergence `re s + r > 0`: `P` is the zeta integral of `f - f(0) 1_𝒪`, which vanishes near `0`,
so that it is a Laurent polynomial in `q ^ (-s)`. -/
theorem exists_differentiable_localZetaIntegral_eq_add (ν : Measure Kˣ) [ν.IsHaarMeasure]
    (ω : Kˣ →ₜ* ℂˣ) {f : K → ℂ} (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    ∃ P : ℂ → ℂ, Differentiable ℂ P ∧ ∀ s : ℂ, 0 < s.re + characterExponent K ω →
      𝔷[ν] ω f s = P s + f 0 * 𝔷[ν] ω ((𝒪[K] : Set K).indicator 1) s := by
  set g := fun x ↦ f x - f 0 * (𝒪[K] : Set K).indicator 1 x
  have hg : Continuous g :=
    hf.continuous.sub (continuous_const.mul (continuous_indicator_integer K))
  obtain ⟨a, b, hab⟩ := exists_forall_valuationShell_sub_indicator_eq_zero hf hfc
  refine ⟨𝔷[ν] ω g, differentiable_localZetaIntegral_of_forall_valuationShell ν ω hg hab,
    fun s hs ↦ ?_⟩
  have hgc : HasCompactSupport g := hfc.sub ((hasCompactSupport_indicator_integer K).mul_left)
  have h1c : HasCompactSupport fun x ↦ f 0 * (𝒪[K] : Set K).indicator (1 : K → ℂ) x :=
    (hasCompactSupport_indicator_integer K).mul_left
  have hfg : f = g + fun x ↦ f 0 * (𝒪[K] : Set K).indicator 1 x := by
    ext x
    simp [g]
  conv_lhs => rw [hfg]
  rw [localZetaIntegral_add _ _ _ (localZetaIntegral_convergent ν ω hg hgc hs)
    (localZetaIntegral_convergent ν ω
      (continuous_const.mul (continuous_indicator_integer K)) h1c hs),
    localZetaIntegral_const_mul]

/-- **Ramified local theory: the zeta integral is entire.** For `ω` nontrivial on `𝒪[K]ˣ` and a
locally constant compactly supported `f`, `s ↦ z(s, ω; f)` agrees on its half-plane of
convergence with an entire function: the local `L`-factor is `1`. -/
theorem exists_differentiable_eqOn_localZetaIntegral_of_ramified (ν : Measure Kˣ)
    [ν.IsHaarMeasure] {ω : Kˣ →ₜ* ℂˣ} (hω : ¬ unitFiltration K 0 ≤ ω.ker) {f : K → ℂ}
    (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
      EqOn (𝔷[ν] ω f) P {s | 0 < s.re + characterExponent K ω} := by
  obtain ⟨P, hP, hfP⟩ := exists_differentiable_localZetaIntegral_eq_add ν ω hf hfc
  refine ⟨P, hP, fun s hs ↦ ?_⟩
  rw [hfP s hs, localZetaIntegral_indicator_integer_of_ramified ν hω, mul_zero, add_zero]

/-- **Unramified local theory: `z = L z₀` with `z₀` entire.** For `ω` trivial on `𝒪[K]ˣ`, a
uniformizer `ϖ` and a locally constant compactly supported `f`, the product
`(1 - ω(ϖ) q ^ (-s)) z(s, ω; f) = L(s, ω)⁻¹ z(s, ω; f)` agrees on the half-plane of convergence
with an entire function. -/
theorem exists_differentiable_eqOn_mul_localZetaIntegral_of_unramified (ν : Measure Kˣ)
    [ν.IsHaarMeasure] {ω : Kˣ →ₜ* ℂˣ} (hω : unitFiltration K 0 ≤ ω.ker) {ϖ : Kˣ}
    (hϖ : IsUniformizer K ϖ) {f : K → ℂ} (hf : IsLocallyConstant f)
    (hfc : HasCompactSupport f) :
    ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
      EqOn (fun s ↦ (1 - ω ϖ * (Nat.card 𝓀[K] : ℂ) ^ (-s)) * 𝔷[ν] ω f s) P
        {s | 0 < s.re + characterExponent K ω} := by
  obtain ⟨P, hP, hfP⟩ := exists_differentiable_localZetaIntegral_eq_add ν ω hf hfc
  have hq : (Nat.card 𝓀[K] : ℂ) ≠ 0 := natCard_residueField_ne_zero
  refine ⟨fun s ↦ (1 - ω ϖ * (Nat.card 𝓀[K] : ℂ) ^ (-s)) * P s +
      f 0 * ν.real (unitFiltration K 0 : Set Kˣ), ?_, fun s hs ↦ ?_⟩
  · exact ((differentiable_const _).sub ((differentiable_neg.const_cpow (Or.inl hq)).const_mul
      _)).mul hP |>.add_const _
  · simp only
    rw [hfP s hs, localZetaIntegral_indicator_integer_of_unramified ν hω hϖ hs]
    have hX := one_sub_apply_mul_natCard_cpow_ne_zero hϖ hs
    field_simp

/-! ### Continuation of the gamma factor -/

variable (μ : Measure K) [μ.IsAddHaarMeasure] {ψ : AddChar K Circle}

/-- **The gamma factor of a ramified character is entire.** For `ω` nontrivial on `𝒪[K]ˣ`,
`s ↦ γ(s, ω, ψ)` agrees on the half-plane `re s + r < 1` with an entire function. -/
theorem exists_differentiable_eqOn_gammaFactor_of_ramified (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    {ω : Kˣ →ₜ* ℂˣ} (hω : ¬ unitFiltration K 0 ≤ ω.ker) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      EqOn (gammaFactor ω μ ψ) G {s | s.re + characterExponent K ω < 1} := by
  have hω' : ¬ unitFiltration K 0 ≤ (ω⁻¹).ker := by rwa [ContinuousMonoidHom.ker_inv]
  obtain ⟨hl, hc⟩ := isLocallyConstant_hasCompactSupport_fourierIntegral μ hψ h1
    (isLocallyConstant_gammaTestFunction ω) (hasCompactSupport_gammaTestFunction ω)
  obtain ⟨P, hP, hzP⟩ := exists_differentiable_eqOn_localZetaIntegral_of_ramified (unitsHaar K)
    hω' hl hc
  refine ⟨fun s ↦ P (1 - s) / (unitsHaar K).real
    (unitFiltration K (ClassFieldTheory.characterConductorExp K ω)),
    ((hP.comp ((differentiable_const 1).sub differentiable_id)).div_const _), fun s hs ↦ ?_⟩
  dsimp only
  rw [gammaFactor_eq ω μ ψ (unitsHaar K), hzP (one_sub_re_add_characterExponent_inv_pos hs)]

/-- **The gamma factor of an unramified character is meromorphic.** For `ω` trivial on
`𝒪[K]ˣ` and a uniformizer `ϖ`, `s ↦ (1 - ω(ϖ)⁻¹ q ^ (-(1 - s))) γ(s, ω, ψ)` agrees on the
half-plane `re s + r < 1` with an entire function: `γ(s, ω, ψ) L(1 - s, ω⁻¹)⁻¹` is entire. -/
theorem exists_differentiable_eqOn_mul_gammaFactor_of_unramified (hψ : Continuous ψ)
    (h1 : ψ ≠ 1) {ω : Kˣ →ₜ* ℂˣ} (hω : unitFiltration K 0 ≤ ω.ker) {ϖ : Kˣ}
    (hϖ : IsUniformizer K ϖ) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      EqOn (fun s ↦ (1 - (ω ϖ : ℂ)⁻¹ * (Nat.card 𝓀[K] : ℂ) ^ (-(1 - s))) * gammaFactor ω μ ψ s) G
        {s | s.re + characterExponent K ω < 1} := by
  have hω' : unitFiltration K 0 ≤ (ω⁻¹).ker := by rwa [ContinuousMonoidHom.ker_inv]
  obtain ⟨hl, hc⟩ := isLocallyConstant_hasCompactSupport_fourierIntegral μ hψ h1
    (isLocallyConstant_gammaTestFunction ω) (hasCompactSupport_gammaTestFunction ω)
  obtain ⟨P, hP, hzP⟩ := exists_differentiable_eqOn_mul_localZetaIntegral_of_unramified
    (unitsHaar K) hω' hϖ hl hc
  refine ⟨fun s ↦ P (1 - s) / (unitsHaar K).real
    (unitFiltration K (ClassFieldTheory.characterConductorExp K ω)),
    ((hP.comp ((differentiable_const 1).sub differentiable_id)).div_const _), fun s hs ↦ ?_⟩
  have h := hzP (one_sub_re_add_characterExponent_inv_pos hs)
  simp only [ContinuousMonoidHom.inv_apply, Units.val_inv_eq_inv_val] at h
  dsimp only
  rw [gammaFactor_eq ω μ ψ (unitsHaar K), mul_div_assoc', h]

end TauCeti.TateZeta
