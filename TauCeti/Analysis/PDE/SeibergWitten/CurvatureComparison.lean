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
`J` and on the basis used to integrate top-degree forms. For a family of fields with
`∫_K |1 - |α|²| = O(h²)` and `∫_K |∂bar_a α| = O(h)`, the right side is `O(h)` for each fixed
test form, so `Θ / 2π` and `i F_a / 2π` have the same weak limits as `h → 0`. For
large-parameter Seiberg–Witten solutions, with `h = (2r)^(-1/2)`, these are the scales of the
coarse estimates on `1 - |α|²` and `∂bar_a α`.

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

omit [FiniteDimensional ℝ E] in
/-- The integral of the wedge of a form `ω` with a form `η` vanishing outside a set `K` is at
most a constant depending only on the basis `e` times `A ∫_K G`, when `‖ω‖ ≤ G` on `K` and
`‖η‖ ≤ A`. -/
private theorem exists_abs_integral_wedge_le {k l : ℕ} (e : Module.Basis (Fin (k + l)) ℝ E) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃ω : E → E [⋀^Fin k]→L[ℝ] ℝ⦄ ⦃η : E → E [⋀^Fin l]→L[ℝ] ℝ⦄ ⦃K : Set E⦄
      ⦃G : E → ℝ⦄ ⦃A : ℝ⦄, MeasurableSet K → (∀ x ∉ K, η x = 0) →
      IntegrableOn G K e.addHaar → (∀ x ∈ K, ‖ω x‖ ≤ G x) → (∀ x, ‖η x‖ ≤ A) →
      |∫ x, wedge (ω x) (η x) e ∂e.addHaar| ≤ C * (A * ∫ x in K, G x ∂e.addHaar) := by
  refine ⟨(k + l).choose k * ∏ i, ‖e i‖, by positivity, ?_⟩
  intro ω η K G A hK hη0 hG hωG hηA
  have hvan (x : E) (hx : x ∉ K) : wedge (ω x) (η x) e = 0 := by
    simp [hη0 x hx, wedge_def]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan, ← integral_const_mul,
    ← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ((hG.const_mul _).const_mul _)
    (ae_restrict_of_forall_mem hK fun x hx ↦ ?_)
  have hG0 : 0 ≤ G x := (norm_nonneg _).trans (hωG x hx)
  calc ‖wedge (ω x) (η x) e‖ ≤ ‖wedge (ω x) (η x)‖ * ∏ i, ‖e i‖ :=
        (wedge (ω x) (η x)).le_opNorm _
    _ ≤ (k + l).choose k * ‖ω x‖ * ‖η x‖ * ∏ i, ‖e i‖ := by
        gcongr
        exact norm_wedge_le _ _
    _ ≤ (k + l).choose k * G x * A * ∏ i, ‖e i‖ := by
        gcongr
        exacts [hωG x hx, hηA x]
    _ = _ := by ring

variable (J : AlmostComplexStructure E)

/-- The integral of `d^c_J g ∧ η`, for a C1 function `g` with `|g| ≤ G` on a compact set `K` and
a C1 form `η` supported in `K` with `‖Dη‖ ≤ A`, is at most a constant depending only on `J` and
the basis `e` times `A ∫_K G`. Integration by parts moves the derivative from `g` onto `η`. -/
private theorem exists_abs_integral_twistedDifferential_wedge_le {m : ℕ}
    (e : Module.Basis (Fin (1 + m)) ℝ E) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃g : E → ℝ⦄ ⦃η : E → E [⋀^Fin m]→L[ℝ] ℝ⦄ ⦃K : Set E⦄ ⦃G : E → ℝ⦄
      ⦃A : ℝ⦄, ContDiff ℝ 1 g → ContDiff ℝ 1 η → IsCompact K → tsupport η ⊆ K →
      IntegrableOn G K e.addHaar → (∀ x ∈ K, |g x| ≤ G x) → (∀ x, ‖fderiv ℝ η x‖ ≤ A) →
      |∫ x, wedge (J.twistedDifferential g x) (η x) e ∂e.addHaar| ≤
        C * (A * ∫ x in K, G x ∂e.addHaar) := by
  let J' := LinearMap.toContinuousLinearMap J.toLinearMap
  let L := compContinuousLinearMapCLM (F := ℝ) (ι := Fin m) (-J')
  let e' := ⇑e ∘ Fin.cast (show m + 1 = 1 + m by omega)
  refine ⟨|LinearMap.det J.toLinearMap| / 2 * ((m + 1) * ‖L‖ * ∏ i, ‖e' i‖), by positivity, ?_⟩
  intro g η K G A hg hη hK hηK hG hgG hηA
  have hDη0 (x) (hx : x ∉ K) : fderiv ℝ η x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hηK (tsupport_fderiv_subset ℝ h))
  rw [J.integral_twistedDifferential_wedge_eq e hg hη
    (hK.of_isClosed_subset (isClosed_tsupport η) hηK)]
  set η' := fun y ↦ (η y).compContinuousLinearMap (-J')
  have hDη' (x : E) : fderiv ℝ η' x = L.comp (fderiv ℝ η x) :=
    (L.hasFDerivAt.comp x (hη.differentiable one_ne_zero x).hasFDerivAt).fderiv
  have hnorm (x : E) : ‖extDeriv η' x‖ ≤ (m + 1) * ‖L‖ * A :=
    calc ‖extDeriv η' x‖ ≤ (m + 1) * ‖fderiv ℝ η' x‖ := norm_alternatizeUncurryFin_le _
      _ ≤ (m + 1) * (‖L‖ * A) := by
          rw [hDη']
          gcongr
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr; exact hηA x)
      _ = _ := by ring
  have hvan (x : E) (hx : x ∉ K) : g x * extDeriv η' x e' = 0 := by
    simp [extDeriv, hDη', hDη0 x hx, ← alternatizeUncurryFinCLM_apply]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan, abs_mul, abs_div, abs_two]
  calc |LinearMap.det J.toLinearMap| / 2 * |∫ x in K, g x * extDeriv η' x e' ∂e.addHaar|
      ≤ |LinearMap.det J.toLinearMap| / 2 *
          ∫ x in K, (m + 1) * ‖L‖ * A * (∏ i, ‖e' i‖) * G x ∂e.addHaar := by
        gcongr
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le (hG.const_mul _)
          (ae_restrict_of_forall_mem hK.measurableSet fun x hx ↦ ?_)
        have hD : |extDeriv η' x e'| ≤ (m + 1) * ‖L‖ * A * ∏ i, ‖e' i‖ := by
          rw [← Real.norm_eq_abs]
          exact ((extDeriv η' x).le_opNorm e').trans (by gcongr; exact hnorm x)
        rw [Real.norm_eq_abs, abs_mul, mul_comm _ (G x)]
        exact mul_le_mul (hgG x hx) hD (abs_nonneg _) ((abs_nonneg _).trans (hgG x hx))
    _ = _ := by
        rw [integral_const_mul]
        ring

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
  obtain ⟨C₁, hC₁, hIA⟩ := exists_abs_integral_twistedDifferential_wedge_le J e₁
  obtain ⟨C₂, hC₂, hIB⟩ := exists_abs_integral_wedge_le e₁
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
    (((J.contDiff_twistedDifferential (n := 0) (by simpa using hg)).wedge
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
  have hX : 0 ≤ A₂ / c * ∫ x in K, |normSq (α x) - 1| ∂e₁.addHaar :=
    mul_nonneg (div_nonneg hA₂0 hc.le) (setIntegral_nonneg hK.measurableSet fun _ _ ↦ abs_nonneg _)
  have hY : 0 ≤ A₁ / √c * ∫ x in K, ‖covariantDBar J b α x‖ ∂e₁.addHaar :=
    mul_nonneg (div_nonneg hA₁0 (Real.sqrt_nonneg _))
      (setIntegral_nonneg hK.measurableSet fun _ _ ↦ norm_nonneg _)
  calc |∫ x, A x ∂e₁.addHaar + ∫ x, B x ∂e₁.addHaar|
      ≤ |∫ x, A x ∂e₁.addHaar| + |∫ x, B x ∂e₁.addHaar| := abs_add_le _ _
    _ ≤ C₁ * (A₂ / c * ∫ x in K, |normSq (α x) - 1| ∂e₁.addHaar) +
        2 * C₂ * (A₁ / √c * ∫ x in K, ‖covariantDBar J b α x‖ ∂e₁.addHaar) := add_le_add hA' hB'
    _ ≤ _ := by
        rw [mul_add]
        gcongr
        exacts [le_max_left _ _, le_max_right _ _]

end TauCeti.SeibergWitten
