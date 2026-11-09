/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Compactness
public import TauCeti.Analysis.Distribution.Mass.FormCurrent
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity

/-!
# Mass bounds for the curvature current at large parameter

In Taubes's passage from Seiberg–Witten solutions on a symplectic four-manifold to
pseudoholomorphic curves, a solution at parameter `r` has normalized spinor `χ = α u₀ + β` and an
`E`-connection `a = i b`, whose curvature is `i F_a = -db`. Its **curvature current** is

`T_r(ζ) = (2π)⁻¹ ∫ i F_a ∧ ζ`

(`Orientation.curvatureCurrent`). This file shows that the coarse large-parameter
estimates bound the mass of `T_r` independently of `r`, and hence that the curvature currents have
closed weak limits as `r → ∞`.

The scaled `L²` bound `r⁻¹ ‖F_a‖₂² ≤ C` alone only gives `‖F_a‖₂ = O(√r)`. The mass bound instead
combines three inputs, each of which Taubes proves for actual solutions:

* the `L¹` bound `r ∫ |1 - |α|² - |β|²| ≤ L` on the spinor defect;
* the bound `|β|² ≤ (C / r) w₊ + C / r²` on the off-diagonal component, where
  `w₊ = max (1 - |α|²) 0` is the vacuum defect;
* the curvature bounds `|F_a⁺| ≤ (r / (4√2)) w₊ + C` and
  `|F_a⁻| ≤ (r / (4√2)) (1 + C r^(-1/2)) w₊ + C`.

Since `1 - |α|² = (1 - |α|² - |β|²) + |β|²`, the first two give, once `r ≥ 2C`, the pointwise bound
`w₊ ≤ 2 |1 - |α|² - |β|²| + 2C / r²` (`TauCeti.SeibergWitten.max_one_sub_le_two_mul_abs_sub_add`)
and so the `L¹` bound `r ∫ w₊ ≤ 2L + 2C vol / r` on the vacuum defect
(`TauCeti.SeibergWitten.mul_setIntegral_max_one_sub_le`). Integrating the curvature bound
`|F_a| ≤ A r w₊ + B` then bounds `∫ |F_a|` independently of `r`
(`TauCeti.SeibergWitten.setLIntegral_enorm_le_of_norm_le`), and with it the mass of `T_r`
(`Orientation.exists_mass_curvatureCurrent_le`). Because `F_a` is exact, `T_r` has zero
boundary (`Orientation.curvatureCurrent_comp_extDerivCLM`). The weak compactness of
mass-bounded currents then provides, for any family of solutions with `r ≥ r₀`, a weak cluster
point which is a closed current of bounded mass
(`Orientation.exists_mapClusterPt_curvatureCurrent`).

The setting is a coordinate chart: an oriented finite-dimensional real vector space with an open
set `Ω` of finite Haar measure, on which the fields and estimates are given. The pointwise norms
are operator norms of alternating maps, as in `Distribution.mass`; on an inner product space they
differ from the Euclidean norms of forms by dimensional constants only. The estimates themselves,
and the splitting of `i F_a` into its self-dual and anti-self-dual parts, are inputs here.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* C. H. Taubes, *Seiberg–Witten invariants and pseudo-holomorphic subvarieties for self-dual,
  harmonic 2-forms*, Geom. Topol. 3 (1999), 167–210.
-/

public section

open MeasureTheory TopologicalSpace TestFunction Distribution Filter Set Real
open scoped Distributions ENNReal NNReal

namespace TauCeti.SeibergWitten

/-- **The vacuum defect is controlled by the spinor defect.** Let `s = |α|²` and `t = |β|²`, and
suppose `t ≤ (C / r) w₊ + C / r²` for the vacuum defect `w₊ = max (1 - s) 0`. If `0 ≤ C` and
`2 C ≤ r`, then `w₊ ≤ 2 |1 - s - t| + 2 C / r²`. -/
theorem max_one_sub_le_two_mul_abs_sub_add {s t C r : ℝ} (hC : 0 ≤ C) (hr : 2 * C ≤ r)
    (ht : t ≤ C / r * max (1 - s) 0 + C / r ^ 2) :
    max (1 - s) 0 ≤ 2 * |1 - s - t| + 2 * (C / r ^ 2) := by
  have hCr : C / r ≤ 1 / 2 := by
    rcases (show (0 : ℝ) ≤ r by linarith).eq_or_lt with h | h
    · simp [← h]
    · rw [div_le_iff₀ h]
      linarith
  have h₂ : 0 ≤ C / r ^ 2 := div_nonneg hC (sq_nonneg r)
  rcases le_total (1 - s) 0 with h | h
  · rw [max_eq_right h]
    positivity
  · rw [max_eq_left h] at ht ⊢
    have : C / r * (1 - s) ≤ (1 - s) / 2 := by nlinarith
    have := le_abs_self (1 - s - t)
    linarith

section Integral

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {S : Set X} {s t : X → ℝ}
  {C r L : ℝ}

/-- **`L¹` bound on the vacuum defect.** Let `s = |α|²` and `t = |β|²` on a measurable set `S` of
finite measure, with `t ≤ (C / r) w₊ + C / r²` on `S` for `w₊ = max (1 - s) 0`, `0 ≤ C` and
`2 C ≤ r`. If the spinor defect `1 - s - t` is integrable on `S` with
`r ∫_S |1 - s - t| ≤ L`, then `r ∫_S w₊ ≤ 2 L + 2 (C / r) μ(S)`. -/
theorem mul_setIntegral_max_one_sub_le (hS : MeasurableSet S) (hμS : μ S ≠ ∞) (hC : 0 ≤ C)
    (hr : 2 * C ≤ r) (hd : IntegrableOn (fun x ↦ 1 - s x - t x) S μ)
    (ht : ∀ x ∈ S, t x ≤ C / r * max (1 - s x) 0 + C / r ^ 2)
    (hL : r * ∫ x in S, |1 - s x - t x| ∂μ ≤ L) :
    r * ∫ x in S, max (1 - s x) 0 ∂μ ≤ 2 * L + 2 * (C / r) * μ.real S := by
  have hr₀ : 0 ≤ r := by linarith
  have hd' : IntegrableOn (fun x ↦ 2 * |1 - s x - t x|) S μ := hd.abs.const_mul 2
  have hc : IntegrableOn (fun _ ↦ 2 * (C / r ^ 2)) S μ := integrableOn_const hμS
  have hle : ∫ x in S, max (1 - s x) 0 ∂μ ≤
      ∫ x in S, (2 * |1 - s x - t x| + 2 * (C / r ^ 2)) ∂μ :=
    integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ le_max_right _ _) (hd'.add hc)
      ((ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx ↦
        max_one_sub_le_two_mul_abs_sub_add hC hr (ht x hx)))
  rw [integral_add hd' hc, integral_const_mul, setIntegral_const, smul_eq_mul] at hle
  have hrC : r * (C / r ^ 2) = C / r := by
    rcases eq_or_ne r 0 with h | h
    · simp [h]
    · field_simp
  calc r * ∫ x in S, max (1 - s x) 0 ∂μ
      ≤ r * (2 * ∫ x in S, |1 - s x - t x| ∂μ + μ.real S * (2 * (C / r ^ 2))) :=
        mul_le_mul_of_nonneg_left hle hr₀
    _ = 2 * (r * ∫ x in S, |1 - s x - t x| ∂μ) + 2 * (r * (C / r ^ 2)) * μ.real S := by ring
    _ ≤ 2 * L + 2 * (C / r) * μ.real S := by
        rw [hrC]
        linarith

/-- **`L¹` bound on the curvature.** Under the hypotheses of
`TauCeti.SeibergWitten.mul_setIntegral_max_one_sub_le`, a field `F` with the pointwise bound
`‖F‖ ≤ A r w₊ + B` on `S`, `0 ≤ A`, satisfies
`∫_S ‖F‖ ≤ 2 A L + (2 A (C / r) + B) μ(S)`. No measurability of `F` is needed: the bound is on the
lower Lebesgue integral of `‖F‖`. -/
theorem setLIntegral_enorm_le_of_norm_le {V : Type*} [NormedAddCommGroup V] {F : X → V}
    {A B : ℝ} (hS : MeasurableSet S) (hμS : μ S ≠ ∞) (hC : 0 ≤ C) (hr : 2 * C ≤ r)
    (hd : IntegrableOn (fun x ↦ 1 - s x - t x) S μ)
    (ht : ∀ x ∈ S, t x ≤ C / r * max (1 - s x) 0 + C / r ^ 2)
    (hL : r * ∫ x in S, |1 - s x - t x| ∂μ ≤ L) (hA : 0 ≤ A)
    (hF : ∀ x ∈ S, ‖F x‖ ≤ A * r * max (1 - s x) 0 + B) :
    ∫⁻ x in S, ‖F x‖ₑ ∂μ ≤ ENNReal.ofReal (2 * A * L + (2 * A * (C / r) + B) * μ.real S) := by
  have hr₀ : 0 ≤ r := by linarith
  have hrC : r * (C / r ^ 2) = C / r := by
    rcases eq_or_ne r 0 with h | h
    · simp [h]
    · field_simp
  -- The pointwise majorant `g = 2 A r |1 - s - t| + (2 A (C / r) + B)` of `‖F‖` on `S`.
  set g : X → ℝ := fun x ↦ 2 * A * r * |1 - s x - t x| + (2 * A * (C / r) + B)
  have hg : IntegrableOn g S μ :=
    (hd.abs.const_mul (2 * A * r)).add (integrableOn_const hμS)
  have hFg (x : X) (hx : x ∈ S) : ‖F x‖ ≤ g x := by
    have hw := max_one_sub_le_two_mul_abs_sub_add hC hr (ht x hx)
    calc ‖F x‖ ≤ A * r * max (1 - s x) 0 + B := hF x hx
      _ ≤ A * r * (2 * |1 - s x - t x| + 2 * (C / r ^ 2)) + B := by gcongr
      _ = g x := by
          simp only [g]
          rw [← hrC]
          ring
  have hg₀ : 0 ≤ᵐ[μ.restrict S] g :=
    (ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx ↦ (norm_nonneg _).trans (hFg x hx))
  calc ∫⁻ x in S, ‖F x‖ₑ ∂μ ≤ ∫⁻ x in S, ENNReal.ofReal (g x) ∂μ :=
        setLIntegral_mono_ae' hS (Eventually.of_forall fun x hx ↦ by
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hFg x hx))
    _ = ENNReal.ofReal (∫ x in S, g x ∂μ) := (ofReal_integral_eq_lintegral_ofReal hg hg₀).symm
    _ ≤ ENNReal.ofReal (2 * A * L + (2 * A * (C / r) + B) * μ.real S) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_add (hd.abs.const_mul (2 * A * r)) (integrableOn_const hμS),
          integral_const_mul, setIntegral_const, smul_eq_mul]
        have h2A : 0 ≤ 2 * A := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hL h2A]

end Integral

end TauCeti.SeibergWitten

namespace Orientation

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {l : ℕ} {n : ℕ∞}

/-- The **curvature current** `T(ζ) = (2π)⁻¹ ∫ i F_a ∧ ζ` of the connection `a = i b` on the
trivial line over `Ω`, whose curvature is `i F_a = -db`. It is `-(2π)⁻¹` times the current of the
form `db` (`Orientation.formCurrent`). -/
noncomputable def curvatureCurrent (o : Orientation ℝ E (Fin (1 + 1 + l))) (Ω : Opens E)
    (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) : 𝓓^{n}(Ω, E [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  -(2 * π)⁻¹ • o.formCurrent Ω (extDeriv b)

/-- The curvature current is `-(2π)⁻¹` times the current of `db`. -/
theorem curvatureCurrent_def (o : Orientation ℝ E (Fin (1 + 1 + l))) (Ω : Opens E)
    (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) :
    (curvatureCurrent o Ω b : 𝓓^{n}(Ω, E [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] ℝ) =
      -(2 * π)⁻¹ • o.formCurrent Ω (extDeriv b) :=
  (rfl)

/-- For a form `b` that is `C¹` on `Ω`, the curvature current is `ζ ↦ (2π)⁻¹ ∫ (-db) ∧ ζ`,
computed in any basis `e` of the given orientation with its Haar measure. -/
theorem curvatureCurrent_apply (o : Orientation ℝ E (Fin (1 + 1 + l))) (Ω : Opens E)
    (e : Module.Basis (Fin (1 + 1 + l)) ℝ E) (he : e.orientation = o)
    {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} (hb : ContDiffOn ℝ 1 b Ω) (ζ : 𝓓^{n}(Ω, E [⋀^Fin l]→L[ℝ] ℝ)) :
    curvatureCurrent o Ω b ζ =
      (2 * π)⁻¹ * ∫ x, ContinuousAlternatingMap.wedge (-extDeriv b x) (ζ x) e ∂e.addHaar := by
  have hloc : LocallyIntegrableOn (extDeriv b) Ω e.addHaar :=
    ContinuousOn.locallyIntegrableOn (fun x hx ↦ (TauCeti.contDiffAt_extDeriv (r := 0)
      (hb.contDiffAt (Ω.isOpen.mem_nhds hx)) (by simp)).continuousAt.continuousWithinAt)
      Ω.isOpen.measurableSet
  rw [curvatureCurrent_def, smul_apply, o.formCurrent_apply Ω e he hloc, smul_eq_mul,
    ← integral_const_mul, ← integral_const_mul]
  congr 1 with x
  rw [← neg_one_smul ℝ (extDeriv b x), ContinuousAlternatingMap.wedge_smul_left,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  ring

/-- **The curvature current has zero boundary**: for a form `b` that is `C²` on `Ω`, `T (dη) = 0`
for every test form `η`, because `i F_a = -db` is closed on `Ω`. -/
theorem curvatureCurrent_comp_extDerivCLM {k : ℕ} (o : Orientation ℝ E (Fin (1 + 1 + (k + 1))))
    (Ω : Opens E) {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} (hb : ContDiffOn ℝ 2 b Ω) :
    curvatureCurrent o Ω b ∘L (extDerivCLM : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] _) = 0 := by
  have hb' (x : E) (hx : x ∈ Ω) : ContDiffAt ℝ 2 b x := hb.contDiffAt (Ω.isOpen.mem_nhds hx)
  rw [curvatureCurrent_def, ContinuousLinearMap.smul_comp,
    o.formCurrent_comp_extDerivCLM_of_extDeriv_eq_zero Ω
      (fun x hx ↦ (TauCeti.contDiffAt_extDeriv (hb' x hx) (by norm_num)).contDiffWithinAt)
      (fun x hx ↦ extDeriv_extDeriv_apply (hb' x hx) (by simp)), smul_zero]

variable {H G : Type*} [NormedAddCommGroup H] [NormedAddCommGroup G]

/-- **The mass of the curvature current is bounded independently of `r`.** Fix an open set `Ω` of
finite Haar measure and constants `C, A ≥ 0`, `L` and `B`. There is `M` such that the following
holds for every `r ≥ max 1 (2 C)` and all fields: a connection `a = i b`, a section `α` and a
component `β`, such that on `Ω`, with the vacuum defect
`w₊ = max (1 - |α|²) 0`,

* `|β|² ≤ (C / r) w₊ + C / r²`,
* the spinor defect `1 - |α|² - |β|²` is integrable with `r ∫_Ω |1 - |α|² - |β|²| ≤ L`,
* `|db| ≤ A r w₊ + B`.

Then the curvature current `T = (2π)⁻¹ ∫ i F_a ∧ ·` of `a` has mass at most `M`. -/
theorem exists_mass_curvatureCurrent_le (o : Orientation ℝ E (Fin (1 + 1 + l))) (Ω : Opens E)
    (μ : Measure E) [μ.IsAddHaarMeasure] (hΩ : μ Ω ≠ ∞) {C L A B : ℝ} (hC : 0 ≤ C)
    (hA : 0 ≤ A) :
    ∃ M : ℝ≥0, ∀ ⦃r : ℝ⦄ ⦃b : E → E [⋀^Fin 1]→L[ℝ] ℝ⦄ ⦃α : E → H⦄ ⦃β : E → G⦄,
      max 1 (2 * C) ≤ r →
      (∀ x ∈ Ω, ‖β x‖ ^ 2 ≤ C / r * max (1 - ‖α x‖ ^ 2) 0 + C / r ^ 2) →
      IntegrableOn (fun x ↦ 1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2) Ω μ →
      r * ∫ x in Ω, |1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2| ∂μ ≤ L →
      (∀ x ∈ Ω, ‖extDeriv b x‖ ≤ A * r * max (1 - ‖α x‖ ^ 2) 0 + B) →
      mass (curvatureCurrent o Ω b : 𝓓^{n}(Ω, E [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] ℝ) ≤ M := by
  obtain ⟨K, hK⟩ := o.exists_mass_formCurrent_le (n := n) Ω μ
  set N : ℝ := 2 * A * L + (2 * A * C + max B 0) * μ.real Ω
  refine ⟨‖(2 * π)⁻¹‖₊ * K * N.toNNReal, fun r b α β hr hβ hd hL hF ↦ ?_⟩
  have hr₁ : 1 ≤ r := le_of_max_le_left hr
  have hrC : 2 * C ≤ r := le_of_max_le_right hr
  have hint := TauCeti.SeibergWitten.setLIntegral_enorm_le_of_norm_le Ω.isOpen.measurableSet hΩ
    hC hrC hd hβ hL hA hF
  -- `C / r ≤ C` and `B ≤ max B 0` remove the dependence on `r`.
  have hN : 2 * A * L + (2 * A * (C / r) + B) * μ.real Ω ≤ N := by
    have : C / r ≤ C := div_le_self hC hr₁
    have : 0 ≤ μ.real Ω := measureReal_nonneg
    simp only [N]
    gcongr
    exact le_max_left B 0
  rw [curvatureCurrent_def, FunLike.coe_smul, mass_smul, enorm_neg]
  calc ‖(2 * π)⁻¹‖ₑ * mass (o.formCurrent Ω (extDeriv b) : 𝓓^{n}(Ω, _) →L[ℝ] ℝ)
      ≤ ‖(2 * π)⁻¹‖ₑ * (K * ∫⁻ x in Ω, ‖extDeriv b x‖ₑ ∂μ) := by gcongr; exact hK _
    _ ≤ ‖(2 * π)⁻¹‖ₑ * (K * ENNReal.ofReal N) := by
        gcongr
        exact hint.trans (ENNReal.ofReal_le_ofReal hN)
    _ = ((‖(2 * π)⁻¹‖₊ * K * N.toNNReal : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.ofReal, enorm_eq_nnnorm]
        push_cast
        ring

/-- **Closed weak limits of the curvature currents.** Fix an open set `Ω` of finite Haar measure,
a constant `C ≥ 0` and a constant `L`. There is `M`, depending only on these data and the
orientation, with the following property. Consider a family, indexed by `i` along a nontrivial
filter, of parameters `rᵢ ≥ max 1 (2 C)` and fields `(bᵢ, αᵢ, βᵢ)` with `bᵢ` of class `C²` on
`Ω` satisfying Taubes's coarse estimates there: with `w₊ = max (1 - |αᵢ|²) 0`,

* `|βᵢ|² ≤ (C / rᵢ) w₊ + C / rᵢ²`,
* `rᵢ ∫_Ω |1 - |αᵢ|² - |βᵢ|²| ≤ L`, the spinor defect being integrable,
* `i F_{aᵢ} = -dbᵢ = F⁺ + F⁻` with `|F⁺| ≤ (rᵢ / (4√2)) w₊ + C` and
  `|F⁻| ≤ (rᵢ / (4√2)) (1 + C rᵢ^(-1/2)) w₊ + C`.

Then the curvature currents `Tᵢ = (2π)⁻¹ ∫ i F_{aᵢ} ∧ ·` have a cluster point `T`, for convergence
on each test form, which is a closed current of mass at most `M`. The forms `F⁺` and `F⁻` may be
any splitting of `i F_{aᵢ}`; in Taubes's estimates they are its self-dual and anti-self-dual
parts. -/
theorem exists_mapClusterPt_curvatureCurrent {k : ℕ}
    (o : Orientation ℝ E (Fin (1 + 1 + (k + 1)))) (Ω : Opens E) (μ : Measure E)
    [μ.IsAddHaarMeasure] (hΩ : μ Ω ≠ ∞) {C : ℝ} (L : ℝ) (hC : 0 ≤ C) :
    ∃ M : ℝ≥0, ∀ {ι : Type u} (f : Filter ι) [f.NeBot] {r : ι → ℝ}
      {b : ι → E → E [⋀^Fin 1]→L[ℝ] ℝ} {α : ι → E → H} {β : ι → E → G}
      {Fp Fm : ι → E → E [⋀^Fin (1 + 1)]→L[ℝ] ℝ}, (∀ i, max 1 (2 * C) ≤ r i) →
      (∀ i, ContDiffOn ℝ 2 (b i) Ω) →
      (∀ i, ∀ x ∈ Ω, ‖β i x‖ ^ 2 ≤ C / r i * max (1 - ‖α i x‖ ^ 2) 0 + C / r i ^ 2) →
      (∀ i, IntegrableOn (fun x ↦ 1 - ‖α i x‖ ^ 2 - ‖β i x‖ ^ 2) Ω μ) →
      (∀ i, r i * ∫ x in Ω, |1 - ‖α i x‖ ^ 2 - ‖β i x‖ ^ 2| ∂μ ≤ L) →
      (∀ i, ∀ x ∈ Ω, -extDeriv (b i) x = Fp i x + Fm i x) →
      (∀ i, ∀ x ∈ Ω, ‖Fp i x‖ ≤ r i / (4 * √2) * max (1 - ‖α i x‖ ^ 2) 0 + C) →
      (∀ i, ∀ x ∈ Ω,
        ‖Fm i x‖ ≤ r i / (4 * √2) * (1 + C / √(r i)) * max (1 - ‖α i x‖ ^ 2) 0 + C) →
      ∃ T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ,
        mass T ≤ M ∧ T ∘L extDerivCLM = 0 ∧
          MapClusterPt (⇑T) f fun i ↦ ⇑(curvatureCurrent o Ω (b i)) := by
  set A : ℝ := (2 + C) / (4 * √2)
  have hA : 0 ≤ A := by positivity
  obtain ⟨M, hM⟩ := exists_mass_curvatureCurrent_le (H := H) (G := G) (n := ⊤) (l := k + 1) o Ω
    μ hΩ (L := L) (B := 2 * C) hC hA
  refine ⟨M, fun f _ r b α β Fp Fm hr hb hβ hd hL hsplit hFp hFm ↦ ?_⟩
  -- The two curvature bounds give `|db| ≤ A r w₊ + 2 C`, using `C / √r ≤ C` for `r ≥ 1`.
  have hF (i) (x : E) (hx : x ∈ Ω) :
      ‖extDeriv (b i) x‖ ≤ A * r i * max (1 - ‖α i x‖ ^ 2) 0 + 2 * C := by
    have hr₁ : 1 ≤ r i := le_of_max_le_left (hr i)
    have hsq : C / √(r i) ≤ C := div_le_self hC (by simpa using Real.sqrt_le_sqrt hr₁)
    have hw : 0 ≤ max (1 - ‖α i x‖ ^ 2) 0 := le_max_right _ _
    have hq : 0 ≤ r i / (4 * √2) := by positivity
    calc ‖extDeriv (b i) x‖ = ‖Fp i x + Fm i x‖ := by rw [← hsplit i x hx, norm_neg]
      _ ≤ ‖Fp i x‖ + ‖Fm i x‖ := norm_add_le _ _
      _ ≤ r i / (4 * √2) * max (1 - ‖α i x‖ ^ 2) 0 + C +
          (r i / (4 * √2) * (1 + C / √(r i)) * max (1 - ‖α i x‖ ^ 2) 0 + C) :=
          add_le_add (hFp i x hx) (hFm i x hx)
      _ ≤ r i / (4 * √2) * max (1 - ‖α i x‖ ^ 2) 0 + C +
          (r i / (4 * √2) * (1 + C) * max (1 - ‖α i x‖ ^ 2) 0 + C) := by gcongr
      _ = A * r i * max (1 - ‖α i x‖ ^ 2) 0 + 2 * C := by
          simp only [A]
          ring
  -- The curvature currents lie in the weakly compact set of closed currents of mass `≤ M`.
  have hcpt := isCompact_image_coe_mass_le_comp_extDerivCLM_le_dsupport_subset (Ω := Ω)
    (F := ℝ) k M 0 isClosed_univ
  have hmem (i) : ⇑(curvatureCurrent o Ω (b i) : 𝓓(Ω, _) →L[ℝ] ℝ) ∈
      (fun T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ ↦ (T : _ → ℝ)) ''
        {T | mass T ≤ M ∧ mass (T ∘L extDerivCLM) ≤ (0 : ℝ≥0) ∧ dsupport T ⊆ univ} := by
    refine ⟨_, ⟨hM (hr i) (hβ i) (hd i) (hL i) (hF i), ?_, subset_univ _⟩, rfl⟩
    rw [curvatureCurrent_comp_extDerivCLM o Ω (hb i)]
    simp [mass_zero]
  obtain ⟨_, ⟨T, ⟨hTM, hTd, -⟩, rfl⟩, hT⟩ :=
    hcpt.exists_mapClusterPt (f := f) (u := fun i ↦ ⇑(curvatureCurrent o Ω (b i)))
      (tendsto_principal.2 (Eventually.of_forall hmem))
  refine ⟨T, hTM, ?_, hT⟩
  have h0 : mass (T ∘L extDerivCLM : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) = 0 :=
    le_antisymm (by simpa using hTd) zero_le
  exact DFunLike.coe_injective ((mass_eq_zero_iff _).1 h0)

end Orientation
