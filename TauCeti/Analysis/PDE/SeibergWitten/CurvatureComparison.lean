/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Integral
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Calculus.DifferentialForm.Wedge
import TauCeti.Analysis.PDE.SeibergWitten.CoarseBounds
import TauCeti.LinearAlgebra.Basis.Fin

/-!
# The cutoff current and the curvature current against test forms

Let `(a, α)` be an abelian Higgs pair with `a = i b`, on a finite-dimensional real normed space
`E` of dimension `2 + n` carrying an almost complex structure `J`. Its cutoff current
`Θ = i F_a + d(χ(|α|²) τ)` (`TauCeti.SeibergWitten.cutoffCurrent`) differs from the curvature
current `i F_a = -db` by the exact form `d(χ(|α|²) τ)`. In Taubes's passage from Seiberg–Witten
solutions to pseudoholomorphic curves, `Θ / 2π` is the current that converges to the limiting
curve, and this file shows that `Θ` and `i F_a` have the same pairings with test forms up to an
error controlled by two integrals: that of `|1 - |α|²|` and that of `|∂bar_a α|`.

For a compactly supported test form `ζ` of degree `n`, integration by parts gives

`∫ (Θ - i F_a) ∧ ζ = ∫ χ(|α|²) τ ∧ dζ`

(`TauCeti.SeibergWitten.integral_cutoffCurrent_add_extDeriv_wedge_eq`). By the
modulus-potential decomposition `χ(|α|²) τ = d^c_J H(|α|²) + E`
(`TauCeti.SeibergWitten.cutoffPhaseForm_eq_twistedDifferential_add`), a second integration by
parts moves the derivative in `d^c_J H(|α|²)` onto `dζ`
(`TauCeti.AlmostComplexStructure.integral_twistedDifferential_wedge_eq`). The pointwise bounds
`|H(s)| ≤ |s - 1| / c` and `|E| ≤ (2 / √c) |∂bar_a α|`, for a cutoff `χ` vanishing below `c`,
then give

`|∫ (Θ - i F_a) ∧ ζ| ≤ C (A₂ / c ∫_K |1 - |α|²| + A₁ / √c ∫_K |∂bar_a α|)`

(`TauCeti.SeibergWitten.exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le`). Here `K` is a
compact set containing the support of `ζ`, `A₁` bounds `|dζ|` and `A₂` bounds the derivative of
`dζ`, so `A₁` and `A₂` are controlled by the `C²` norm of `ζ`. The constant `C` depends only on
`J` and on the basis used to integrate top-degree forms.

For large-parameter Seiberg–Witten solutions, with `h = (2r)^(-1/2)`, Taubes's coarse estimates
give `∫_K |1 - |α|²| = O(h²)` (`TauCeti.SeibergWitten.mul_setIntegral_abs_one_sub_le`) and,
through the `L²` bound on `∂bar_a α` and Cauchy–Schwarz on `K`, `∫_K |∂bar_a α| = O(h)`
(`TauCeti.SeibergWitten.setIntegral_norm_le_div_sqrt`). So the right side is `O(h)`, uniformly
over all fields satisfying the coarse bounds with a fixed constant
(`TauCeti.SeibergWitten.exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le_div_add_div_sqrt`).
Along a sequence of such fields with `r → ∞`, the pairings of `Θ` and of `i F_a` with each fixed
`C²` test form therefore differ by a sequence tending to zero
(`TauCeti.SeibergWitten.tendsto_integral_cutoffCurrent_add_extDeriv_wedge_nhds_zero`), and one
converges exactly when the other does, to the same limit
(`TauCeti.SeibergWitten.tendsto_integral_cutoffCurrent_wedge_iff`): `Θ / 2π` and `i F_a / 2π`
have the same weak limits. The coarse estimates themselves are hypotheses here.

## Main results

* `TauCeti.SeibergWitten.exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le`: the comparison
  for a single field, in terms of `∫_K |1 - |α|²|` and `∫_K |∂bar_a α|`.
* `TauCeti.SeibergWitten.exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le_div_add_div_sqrt`:
  the comparison is `O(r^(-1/2))` under the coarse bounds.
* `TauCeti.SeibergWitten.tendsto_integral_cutoffCurrent_wedge_iff`: the cutoff currents and the
  curvature currents have the same limits against each fixed test form as `r → ∞`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* C. H. Taubes, *Seiberg–Witten invariants and pseudo-holomorphic subvarieties for self-dual,
  harmonic 2-forms*, Geom. Topol. 3 (1999), 167–210.
-/

public section

noncomputable section

open ContinuousAlternatingMap Complex Filter MeasureTheory Set
open scoped Topology

namespace TauCeti.SeibergWitten

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {χ : ℝ → ℝ} {ζ : E → E [⋀^Fin n]→L[ℝ] ℝ}

omit [FiniteDimensional ℝ E] in
/-- **The cutoff current against a test form.** For a compactly supported C1 test form `ζ` of
degree `n` on a space of dimension `2 + n`, the pairing of `Θ - i F_a = Θ + db` with `ζ` is the
pairing of the cutoff phase form `χ(|α|²) τ` with `dζ`. Top-degree coefficients are taken on a
basis `e` and integrated against its Haar measure. -/
theorem integral_cutoffCurrent_add_extDeriv_wedge_eq (e : Module.Basis (Fin (2 + n)) ℝ E)
    (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b) (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0)
    (hζ : ContDiff ℝ 1 ζ) (hc : HasCompactSupport ζ) :
    ∫ x, wedge (cutoffCurrent χ b α x + extDeriv b x) (ζ x) e ∂e.addHaar =
      ∫ x, wedge (cutoffPhaseForm χ b α x) (extDeriv ζ x) (e ∘ Fin.cast (by omega)) ∂e.addHaar := by
  have h := e.integral_extDeriv_wedge_eq_integral_wedge_extDeriv (by omega)
    (contDiff_cutoffPhaseForm hα hb hχ hχ₀) hζ hc
  -- The index cast `1 + 1 + n = 2 + n` is the identity.
  have e₁ : ⇑e ∘ Fin.cast (show 1 + 1 + n = 2 + n by omega) = ⇑e := rfl
  rw [e₁, pow_one, neg_neg, one_mul] at h
  simpa only [cutoffCurrent_apply, sub_add_cancel] using h

variable (J : AlmostComplexStructure E)

/-- **Comparison of the cutoff current with the curvature current.** There is a constant `C`,
depending only on `J` and the basis `e`, with the following property. Let `χ` vanish below
`c > 0` with `|χ| ≤ 1`, and let `ζ` be a `C²` test form of degree `n` supported in a compact set
`K`, with `|dζ| ≤ A₁` and `|D(dζ)| ≤ A₂`. Then

`|∫ (Θ - i F_a) ∧ ζ| ≤ C (A₂ / c ∫_K |1 - |α|²| + A₁ / √c ∫_K |∂bar_a α|)`,

where `Θ - i F_a = Θ + db`. Top-degree coefficients are taken on `e` and integrated against its
Haar measure. -/
theorem exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le
    (e : Module.Basis (Fin (2 + n)) ℝ E) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃χ : ℝ → ℝ⦄ ⦃b : E → E [⋀^Fin 1]→L[ℝ] ℝ⦄ ⦃α : E → ℂ⦄
      ⦃ζ : E → E [⋀^Fin n]→L[ℝ] ℝ⦄ ⦃K : Set E⦄ ⦃c A₁ A₂ : ℝ⦄, 0 < c →
      (∀ t < c, χ t = 0) → (∀ t, |χ t| ≤ 1) → ContDiff ℝ 1 χ → ContDiff ℝ 2 α →
      ContDiff ℝ 1 b → ContDiff ℝ 2 ζ → IsCompact K → tsupport ζ ⊆ K →
      (∀ x, ‖extDeriv ζ x‖ ≤ A₁) → (∀ x, ‖fderiv ℝ (extDeriv ζ) x‖ ≤ A₂) →
      |∫ x, wedge (cutoffCurrent χ b α x + extDeriv b x) (ζ x) e ∂e.addHaar| ≤
        C * (A₂ / c * ∫ x in K, |normSq (α x) - 1| ∂e.addHaar +
          A₁ / √c * ∫ x in K, ‖covariantDBar J b α x‖ ∂e.addHaar) := by
  let e₁ := e.reindex (finCongr (by omega : 2 + n = 1 + (n + 1)))
  obtain ⟨C₁, hC₁, hIA⟩ := J.exists_abs_integral_twistedDifferential_wedge_le e₁
  obtain ⟨C₂, _, hIB⟩ := e₁.exists_abs_integral_wedge_le
  refine ⟨max C₁ (2 * C₂), by positivity, ?_⟩
  intro χ b α ζ K c A₁ A₂ hc hχc hχ₁ hχ hα hb hζ hK hζK hA₁ hA₂
  have hχ₀ : χ =ᶠ[𝓝 0] 0 := (eventually_lt_nhds hc).mono hχc
  have hcζ : HasCompactSupport ζ := hK.of_isClosed_subset (isClosed_tsupport ζ) hζK
  set η := extDeriv ζ
  have hη : ContDiff ℝ 1 η := contDiff_extDeriv hζ (by norm_num)
  have hcη : HasCompactSupport η := hcζ.extDeriv
  -- Outside `K` the form `dζ` vanishes.
  have hηK : tsupport η ⊆ K := tsupport_extDeriv_subset.trans hζK
  have hη0 (x) (hx : x ∉ K) : η x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (hηK h)
  have hA₁0 : 0 ≤ A₁ := (norm_nonneg _).trans (hA₁ 0)
  have hA₂0 : 0 ≤ A₂ := (ContinuousLinearMap.opNorm_nonneg _).trans (hA₂ 0)
  -- The modulus potential `H(|α|²)` and the decomposition `χ(|α|²) τ = d^c_J H(|α|²) + E`.
  set H := modulusPotential χ
  have hH (t : ℝ) : HasDerivAt H (χ t / t) t := hasDerivAt_modulusPotential hχ.continuous hχ₀ t
  have hs : ContDiff ℝ 1 fun y ↦ normSq (α y) := by
    simp_rw [normSq_eq_norm_sq]
    exact (contDiff_norm_sq ℝ).comp (hα.of_le one_le_two)
  have hg : ContDiff ℝ 1 fun y ↦ H (normSq (α y)) :=
    (contDiff_modulusPotential hχ.continuous hχ₀).comp hs
  have hdec (x : E) : cutoffPhaseForm χ b α x =
      J.twistedDifferential (fun y ↦ H (normSq (α y))) x + cutoffDBarForm J χ b α x :=
    cutoffPhaseForm_eq_twistedDifferential_add J (hH _) (hχc 0 hc)
      (hα.differentiable two_ne_zero x)
  -- Reduce to the pairing of the cutoff phase form with `dζ`, evaluated on `e₁`.
  have he₁ : ⇑e ∘ Fin.cast (show 1 + (n + 1) = 2 + n by omega) = ⇑e₁ :=
    (e.reindex_finCongr_comp_cast _ rfl).symm
  have hμ : e₁.addHaar = e.addHaar := Module.Basis.addHaar_reindex _ _
  rw [integral_cutoffCurrent_add_extDeriv_wedge_eq e hα hb hχ hχ₀ (hζ.of_le one_le_two) hcζ, he₁,
    ← hμ]
  set g := fun y ↦ H (normSq (α y))
  set A := fun x ↦ wedge (J.twistedDifferential g x) (η x) e₁
  set B := fun x ↦ wedge (cutoffDBarForm J χ b α x) (η x) e₁
  have hcw (φ : E → E [⋀^Fin 1]→L[ℝ] ℝ) : HasCompactSupport fun x ↦ wedge (φ x) (η x) e₁ :=
    hcη.wedge_left.comp_left (g := fun ω : E [⋀^Fin (1 + (n + 1))]→L[ℝ] ℝ ↦ ω e₁) rfl
  have hA : Integrable A e₁.addHaar :=
    (((J.contDiff_twistedDifferential (n := 0) hg (by simp)).wedge
      (hη.of_le zero_le_one)).continuous.eval_const _).integrable_of_hasCompactSupport
      (hcw _)
  have hT : Integrable (fun x ↦ wedge (cutoffPhaseForm χ b α x) (η x) e₁) e₁.addHaar :=
    (((contDiff_cutoffPhaseForm (n := 0) (by simpa using hα.of_le one_le_two)
      (hb.of_le zero_le_one) (hχ.of_le zero_le_one) hχ₀).wedge
      (hη.of_le zero_le_one)).continuous.eval_const _).integrable_of_hasCompactSupport
      (hcw _)
  have hsplit (x : E) : wedge (cutoffPhaseForm χ b α x) (η x) e₁ = A x + B x := by
    simp only [A, B, hdec, wedge_add_left, ContinuousAlternatingMap.add_apply]
  have hB : Integrable B e₁.addHaar :=
    (hT.sub hA).congr (Eventually.of_forall fun x ↦ by
      rw [Pi.sub_apply, hsplit, add_sub_cancel_left])
  rw [integral_congr_ae (Eventually.of_forall hsplit), integral_add hA hB]
  -- The `d^c_J H(|α|²)` term, by `|H(s)| ≤ |s - 1| / c`.
  have hA' : |∫ x, A x ∂e₁.addHaar| ≤
      C₁ * (A₂ / c * ∫ x in K, |normSq (α x) - 1| ∂e₁.addHaar) :=
    calc |∫ x, A x ∂e₁.addHaar|
        ≤ C₁ * (A₂ * ∫ x in K, |normSq (α x) - 1| / c ∂e₁.addHaar) :=
          hIA hg hη hK hηK
            (((hs.continuous.sub continuous_const).abs.div_const c).continuousOn
              |>.integrableOn_compact hK)
            (fun x _ ↦ abs_modulusPotential_le hc (fun t _ ht ↦ hχc t ht) hχ₁ (normSq_nonneg _))
            hA₂
      _ = _ := by
          rw [integral_div]
          ring
  -- The correction term `E = 2 χ(|α|²) Re (α⁻¹ ∂bar_a α) ∘ J`, by `|E| ≤ (2 / √c) |∂bar_a α|`.
  have hB' : |∫ x, B x ∂e₁.addHaar| ≤
      2 * C₂ * (A₁ / √c * ∫ x in K, ‖covariantDBar J b α x‖ ∂e₁.addHaar) :=
    calc |∫ x, B x ∂e₁.addHaar|
        ≤ C₂ * (A₁ * ∫ x in K, 2 / √c * ‖covariantDBar J b α x‖ ∂e₁.addHaar) :=
          hIB hK.measurableSet hη0
            ((continuous_const.mul (continuous_covariantDBar J (hα.of_le one_le_two)
              hb.continuous).norm).continuousOn.integrableOn_compact hK)
            (fun x _ ↦ norm_cutoffDBarForm_le J hc (fun t _ ht ↦ hχc t ht) hχ₁ b α x) hA₁
      _ = _ := by
          rw [integral_const_mul]
          ring
  calc |∫ x, A x ∂e₁.addHaar + ∫ x, B x ∂e₁.addHaar|
      ≤ |∫ x, A x ∂e₁.addHaar| + |∫ x, B x ∂e₁.addHaar| := abs_add_le _ _
    _ ≤ C₁ * (A₂ / c * ∫ x in K, |normSq (α x) - 1| ∂e₁.addHaar) +
        2 * C₂ * (A₁ / √c * ∫ x in K, ‖covariantDBar J b α x‖ ∂e₁.addHaar) := add_le_add hA' hB'
    _ ≤ _ := by
        rw [mul_add]
        gcongr
        exacts [le_max_left _ _, le_max_right _ _]

/-! ### The comparison at large parameter -/

variable {B : Type*} [NormedAddCommGroup B]

/-- **The cutoff current and the curvature current at large parameter.** There is a constant
`C₀`, depending only on `J` and the basis `e`, with the following property. Let `χ`, `ζ`, `K`,
`c`, `A₁` and `A₂` be as in
`TauCeti.SeibergWitten.exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le`, and let
`(a, α, β)`, `a = i b`, satisfy on `K` the coarse bounds of a large-parameter solution at
parameter `r > 0` with constant `C`, `2 C ≤ r`, where `w₊ = max (1 - |α|²) 0`:

* the spinor defect `1 - |α|² - |β|²` is integrable on `K` with `r ∫_K |1 - |α|² - |β|²| ≤ C`;
* `|β|² ≤ (C / r) w₊ + C / r²` and `|∇_a α|² ≤ C r w₊ + C` on `K`;
* `‖∂bar_a α‖₂ ≤ C r^(-1/2) (‖∇_a α‖₂ + 1)`, with `L²` norms over `K`.

Then, with `V` the measure of `K`,

`|∫ (Θ - i F_a) ∧ ζ| ≤ C₀ (A₂ / c (2 C + V) / r + A₁ / √c √V C (√(2 C (C + V)) + 1) / √r)`.

With `h = (2 r)^(-1/2)` this is `O(h)`, uniformly over all fields satisfying the bounds. Taubes's
estimate is stated with `‖∂_a α‖₂` in place of `‖∇_a α‖₂`; it implies the one used here when `J`
preserves the norm, by `TauCeti.SeibergWitten.norm_covariantDeriv_sub_covariantDBar_le`. -/
theorem exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le_div_add_div_sqrt
    (e : Module.Basis (Fin (2 + n)) ℝ E) :
    ∃ C₀, 0 ≤ C₀ ∧ ∀ ⦃χ : ℝ → ℝ⦄ ⦃b : E → E [⋀^Fin 1]→L[ℝ] ℝ⦄ ⦃α : E → ℂ⦄ ⦃β : E → B⦄
      ⦃ζ : E → E [⋀^Fin n]→L[ℝ] ℝ⦄ ⦃K : Set E⦄ ⦃c A₁ A₂ C r : ℝ⦄, 0 < c →
      (∀ t < c, χ t = 0) → (∀ t, |χ t| ≤ 1) → ContDiff ℝ 1 χ → ContDiff ℝ 2 α →
      ContDiff ℝ 1 b → ContDiff ℝ 2 ζ → IsCompact K → tsupport ζ ⊆ K →
      (∀ x, ‖extDeriv ζ x‖ ≤ A₁) → (∀ x, ‖fderiv ℝ (extDeriv ζ) x‖ ≤ A₂) → 0 < r →
      2 * C ≤ r → IntegrableOn (fun x ↦ 1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2) K e.addHaar →
      r * ∫ x in K, |1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2| ∂e.addHaar ≤ C →
      (∀ x ∈ K, ‖β x‖ ^ 2 ≤ C / r * max (1 - ‖α x‖ ^ 2) 0 + C / r ^ 2) →
      (∀ x ∈ K, ‖covariantDeriv b α x‖ ^ 2 ≤ C * r * max (1 - ‖α x‖ ^ 2) 0 + C) →
      √(∫ x in K, ‖covariantDBar J b α x‖ ^ 2 ∂e.addHaar) ≤
        C / √r * (√(∫ x in K, ‖covariantDeriv b α x‖ ^ 2 ∂e.addHaar) + 1) →
      |∫ x, wedge (cutoffCurrent χ b α x + extDeriv b x) (ζ x) e ∂e.addHaar| ≤
        C₀ * (A₂ / c * (2 * C + e.addHaar.real K) / r + A₁ / √c * √(e.addHaar.real K) *
          (C * (√(2 * C * (C + e.addHaar.real K)) + 1)) / √r) := by
  obtain ⟨C₀, hC₀, hcmp⟩ := exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le J e
  refine ⟨C₀, hC₀, ?_⟩
  intro χ b α β ζ K c A₁ A₂ C r hc hχc hχ₁ hχ hα hb hζ hK hζK hA₁ hA₂ hr hCr hδ hL1 hβ hgrad
    hDbar
  set V := e.addHaar.real K
  have hC : 0 ≤ C := (mul_nonneg hr.le (integral_nonneg fun _ ↦ abs_nonneg _)).trans hL1
  have hμK : e.addHaar K ≠ ⊤ := hK.measure_lt_top.ne
  have hV : 0 ≤ V := measureReal_nonneg
  have hA₁0 : 0 ≤ A₁ := (norm_nonneg _).trans (hA₁ 0)
  have hA₂0 : 0 ≤ A₂ := (ContinuousLinearMap.opNorm_nonneg _).trans (hA₂ 0)
  -- The modulus defect: `∫_K |1 - |α|²| ≤ (2 C + V) / r`.
  have h₁ : ∫ x in K, |normSq (α x) - 1| ∂e.addHaar ≤ (2 * C + V) / r := by
    have h := mul_setIntegral_abs_one_sub_le (s := fun x ↦ ‖α x‖ ^ 2)
      (t := fun x ↦ ‖β x‖ ^ 2) hK.measurableSet hμK hC hCr hδ (fun _ _ ↦ by positivity) hβ hL1
    have hCr' : 2 * (C / r) * V ≤ V := by
      refine mul_le_of_le_one_left hV ?_
      rw [mul_div_assoc', div_le_one hr]
      exact hCr
    simp_rw [normSq_eq_norm_sq, abs_sub_comm _ (1 : ℝ)]
    rw [le_div_iff₀ hr, mul_comm]
    linarith
  -- The `∂bar_a α` term, by the `L²` bound and Cauchy–Schwarz on `K`.
  have hcont : Continuous fun x ↦ ‖covariantDBar J b α x‖ :=
    (continuous_covariantDBar J (hα.of_le one_le_two) hb.continuous).norm
  have h₂ := setIntegral_norm_le_div_sqrt hK.measurableSet hμK hCr hδ hL1 hβ hgrad
    ((hcont.pow 2).continuousOn.integrableOn_compact hK) hDbar
  calc |∫ x, wedge (cutoffCurrent χ b α x + extDeriv b x) (ζ x) e ∂e.addHaar|
      ≤ C₀ * (A₂ / c * ∫ x in K, |normSq (α x) - 1| ∂e.addHaar +
          A₁ / √c * ∫ x in K, ‖covariantDBar J b α x‖ ∂e.addHaar) :=
        hcmp hc hχc hχ₁ hχ hα hb hζ hK hζK hA₁ hA₂
    _ ≤ C₀ * (A₂ / c * ((2 * C + V) / r) +
          A₁ / √c * (√V * (C * (√(2 * C * (C + V)) + 1)) / √r)) := by gcongr
    _ = _ := by ring

/-- **The cutoff current and the curvature current have the same limits: the difference.** Let
`(a_i, α_i, β_i)`, `a_i = i b_i`, be fields indexed along a filter `l` which eventually satisfy on
the compact set `K` the coarse bounds of
`TauCeti.SeibergWitten.exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le_div_add_div_sqrt`
at parameters `r_i → ∞`, with a fixed constant `C`. Then for every fixed `C²` test form `ζ`
supported in `K`, `∫ (Θ_i - i F_(a_i)) ∧ ζ → 0`. -/
theorem tendsto_integral_cutoffCurrent_add_extDeriv_wedge_nhds_zero
    (e : Module.Basis (Fin (2 + n)) ℝ E) {ι : Type*} {l : Filter ι}
    {b : ι → E → E [⋀^Fin 1]→L[ℝ] ℝ} {α : ι → E → ℂ} {β : ι → E → B} {r : ι → ℝ} {K : Set E}
    {c C : ℝ} (hc : 0 < c) (hχc : ∀ t < c, χ t = 0) (hχ₁ : ∀ t, |χ t| ≤ 1)
    (hχ : ContDiff ℝ 1 χ) (hα : ∀ᶠ i in l, ContDiff ℝ 2 (α i))
    (hb : ∀ᶠ i in l, ContDiff ℝ 1 (b i)) (hζ : ContDiff ℝ 2 ζ) (hK : IsCompact K)
    (hζK : tsupport ζ ⊆ K) (hr : Tendsto r l atTop)
    (hδ : ∀ᶠ i in l, IntegrableOn (fun x ↦ 1 - ‖α i x‖ ^ 2 - ‖β i x‖ ^ 2) K e.addHaar)
    (hL1 : ∀ᶠ i in l, r i * ∫ x in K, |1 - ‖α i x‖ ^ 2 - ‖β i x‖ ^ 2| ∂e.addHaar ≤ C)
    (hβ : ∀ᶠ i in l, ∀ x ∈ K,
      ‖β i x‖ ^ 2 ≤ C / r i * max (1 - ‖α i x‖ ^ 2) 0 + C / r i ^ 2)
    (hgrad : ∀ᶠ i in l, ∀ x ∈ K,
      ‖covariantDeriv (b i) (α i) x‖ ^ 2 ≤ C * r i * max (1 - ‖α i x‖ ^ 2) 0 + C)
    (hDbar : ∀ᶠ i in l, √(∫ x in K, ‖covariantDBar J (b i) (α i) x‖ ^ 2 ∂e.addHaar) ≤
      C / √(r i) * (√(∫ x in K, ‖covariantDeriv (b i) (α i) x‖ ^ 2 ∂e.addHaar) + 1)) :
    Tendsto (fun i ↦ ∫ x, wedge (cutoffCurrent χ (b i) (α i) x + extDeriv (b i) x) (ζ x) e
      ∂e.addHaar) l (𝓝 0) := by
  obtain ⟨C₀, -, hbd⟩ :=
    exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le_div_add_div_sqrt (B := B) J e
  -- Uniform bounds on `dζ` and its derivative.
  have hcζ : HasCompactSupport ζ := hK.of_isClosed_subset (isClosed_tsupport ζ) hζK
  have hη : ContDiff ℝ 1 (extDeriv ζ) := contDiff_extDeriv hζ (by norm_num)
  obtain ⟨A₁, hA₁⟩ := hη.continuous.bounded_above_of_compact_support hcζ.extDeriv
  obtain ⟨A₂, hA₂⟩ := (hη.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hcζ.extDeriv.fderiv (𝕜 := ℝ))
  set V := e.addHaar.real K
  -- The bound of the previous theorem tends to zero as `r → ∞`.
  have hg : Tendsto (fun i ↦ C₀ * (A₂ / c * (2 * C + V) / r i + A₁ / √c * √V *
      (C * (√(2 * C * (C + V)) + 1)) / √(r i))) l (𝓝 0) := by
    simpa using ((tendsto_const_nhds.div_atTop hr).add
      (tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hr))).const_mul C₀
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [hα, hb, hδ, hL1, hβ, hgrad, hDbar, hr.eventually_gt_atTop 0,
    hr.eventually_ge_atTop (2 * C)] with i hαi hbi hδi hL1i hβi hgradi hDbari hri hCri
  rw [Real.norm_eq_abs]
  exact hbd hc hχc hχ₁ hχ hαi hbi hζ hK hζK hA₁ hA₂ hri hCri hδi hL1i hβi hgradi hDbari

/-- **The cutoff currents and the curvature currents have the same limits.** Under the
hypotheses of `TauCeti.SeibergWitten.tendsto_integral_cutoffCurrent_add_extDeriv_wedge_nhds_zero`,
for every fixed `C²` test form `ζ` supported in `K`, the pairings `∫ Θ_i ∧ ζ` of the cutoff
currents converge to `T` exactly when the pairings `∫ i F_(a_i) ∧ ζ = ∫ (-d b_i) ∧ ζ` of the
curvature currents do. -/
theorem tendsto_integral_cutoffCurrent_wedge_iff (e : Module.Basis (Fin (2 + n)) ℝ E)
    {ι : Type*} {l : Filter ι} {b : ι → E → E [⋀^Fin 1]→L[ℝ] ℝ} {α : ι → E → ℂ}
    {β : ι → E → B} {r : ι → ℝ} {K : Set E} {c C T : ℝ} (hc : 0 < c)
    (hχc : ∀ t < c, χ t = 0) (hχ₁ : ∀ t, |χ t| ≤ 1) (hχ : ContDiff ℝ 1 χ)
    (hα : ∀ᶠ i in l, ContDiff ℝ 2 (α i)) (hb : ∀ᶠ i in l, ContDiff ℝ 1 (b i))
    (hζ : ContDiff ℝ 2 ζ) (hK : IsCompact K) (hζK : tsupport ζ ⊆ K) (hr : Tendsto r l atTop)
    (hδ : ∀ᶠ i in l, IntegrableOn (fun x ↦ 1 - ‖α i x‖ ^ 2 - ‖β i x‖ ^ 2) K e.addHaar)
    (hL1 : ∀ᶠ i in l, r i * ∫ x in K, |1 - ‖α i x‖ ^ 2 - ‖β i x‖ ^ 2| ∂e.addHaar ≤ C)
    (hβ : ∀ᶠ i in l, ∀ x ∈ K,
      ‖β i x‖ ^ 2 ≤ C / r i * max (1 - ‖α i x‖ ^ 2) 0 + C / r i ^ 2)
    (hgrad : ∀ᶠ i in l, ∀ x ∈ K,
      ‖covariantDeriv (b i) (α i) x‖ ^ 2 ≤ C * r i * max (1 - ‖α i x‖ ^ 2) 0 + C)
    (hDbar : ∀ᶠ i in l, √(∫ x in K, ‖covariantDBar J (b i) (α i) x‖ ^ 2 ∂e.addHaar) ≤
      C / √(r i) * (√(∫ x in K, ‖covariantDeriv (b i) (α i) x‖ ^ 2 ∂e.addHaar) + 1)) :
    Tendsto (fun i ↦ ∫ x, wedge (cutoffCurrent χ (b i) (α i) x) (ζ x) e ∂e.addHaar) l (𝓝 T) ↔
      Tendsto (fun i ↦ ∫ x, wedge (-extDeriv (b i) x) (ζ x) e ∂e.addHaar) l (𝓝 T) := by
  have h₀ := tendsto_integral_cutoffCurrent_add_extDeriv_wedge_nhds_zero J e hc hχc hχ₁ hχ hα hb
    hζ hK hζK hr hδ hL1 hβ hgrad hDbar
  have hχ₀ : χ =ᶠ[𝓝 0] 0 := (eventually_lt_nhds hc).mono hχc
  have hcζ : HasCompactSupport ζ := hK.of_isClosed_subset (isClosed_tsupport ζ) hζK
  -- A continuous two-form pairs integrably with `ζ`.
  have hint {φ : E → E [⋀^Fin 2]→L[ℝ] ℝ} (hφ : ContDiff ℝ 0 φ) :
      Integrable (fun x ↦ wedge (φ x) (ζ x) e) e.addHaar :=
    ((hφ.wedge (hζ.of_le (by norm_num))).continuous.eval_const _).integrable_of_hasCompactSupport
      (hcζ.wedge_left.comp_left (g := fun ω : E [⋀^Fin (2 + n)]→L[ℝ] ℝ ↦ ω e) rfl)
  -- Split `∫ Θ_i ∧ ζ = ∫ (Θ_i - i F_(a_i)) ∧ ζ + ∫ i F_(a_i) ∧ ζ`.
  have hsplit : ∀ᶠ i in l,
      ∫ x, wedge (cutoffCurrent χ (b i) (α i) x + extDeriv (b i) x) (ζ x) e ∂e.addHaar +
        ∫ x, wedge (-extDeriv (b i) x) (ζ x) e ∂e.addHaar =
      ∫ x, wedge (cutoffCurrent χ (b i) (α i) x) (ζ x) e ∂e.addHaar := by
    filter_upwards [hα, hb] with i hαi hbi
    have hdb : ContDiff ℝ 0 (extDeriv (b i)) := contDiff_extDeriv hbi (by norm_num)
    have hΘ : ContDiff ℝ 0 (cutoffCurrent χ (b i) (α i)) :=
      contDiff_cutoffCurrent (n := 1) hαi hbi hχ hχ₀ (by norm_num)
    rw [← integral_add (hint (hΘ.add hdb)) (hint hdb.neg)]
    congr 1 with x
    rw [← ContinuousAlternatingMap.add_apply, ← wedge_add_left, add_neg_cancel_right]
  constructor
  · intro h
    simpa using (h.congr' (hsplit.mono fun _ h ↦ h.symm)).sub h₀
  · intro h
    simpa using (h₀.add h).congr' hsplit

end TauCeti.SeibergWitten
