/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Topology.Algebra.GroupWithZero.DivId
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Integral
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Calculus.DifferentialForm.Wedge

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
  {α : E → ℂ} {a : E → E [⋀^Fin 1]→L[ℝ] ℝ} {χ : ℝ → ℝ} {ζ : E → E [⋀^Fin n]→L[ℝ] ℝ}

/-- **The cutoff current against a test form.** For a compactly supported C1 test form `ζ` of
degree `n` on a space of dimension `2 + n`, the pairing of `Θ - i F_a = Θ + da` with `ζ` is the
pairing of the cutoff phase form `χ(|α|²) τ` with `dζ`. Top-degree coefficients are taken on a
basis `e` and integrated against its Haar measure. -/
theorem integral_cutoffCurrent_add_extDeriv_wedge_eq (e : Module.Basis (Fin (2 + n)) ℝ E)
    (hα : ContDiff ℝ 2 α) (ha : ContDiff ℝ 1 a) (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0)
    (hζ : ContDiff ℝ 1 ζ) (hc : HasCompactSupport ζ) :
    ∫ x, wedge (cutoffCurrent χ a α x + extDeriv a x) (ζ x) e ∂e.addHaar =
      ∫ x, wedge (cutoffPhaseForm χ a α x) (extDeriv ζ x) (e ∘ Fin.cast (by omega)) ∂e.addHaar := by
  let b := e.reindex (finCongr (by omega : 2 + n = 1 + n + 1))
  have hb : b.addHaar = e.addHaar := Module.Basis.addHaar_reindex _ _
  have h := b.integral_extDeriv_wedge_eq_integral_wedge_extDeriv
    (contDiff_cutoffPhaseForm hα ha hχ hχ₀) hζ hc
  have e₁ : ⇑b ∘ Fin.cast (show 1 + 1 + n = 1 + n + 1 by omega) = ⇑e := by
    funext i
    simp [b]
  have e₂ : ⇑b ∘ Fin.cast (show 1 + (n + 1) = 1 + n + 1 by omega) =
      ⇑e ∘ Fin.cast (show 1 + (n + 1) = 2 + n by omega) := by
    funext i
    simp [b]
  rw [e₁, e₂, hb, pow_one, neg_neg, one_mul] at h
  simpa only [cutoffCurrent_apply, sub_add_cancel] using h

variable (J : AlmostComplexStructure E)

/-- **Comparison of the cutoff current with the curvature current.** There is a constant `C`,
depending only on `J` and the basis `e`, with the following property. Let `χ` vanish below
`c > 0` with `|χ| ≤ 1`, and let `ζ` be a `C²` test form of degree `n` supported in a compact set
`K`, with `|dζ| ≤ A₁` and `|D(dζ)| ≤ A₂`. Then

`|∫ (Θ - i F_a) ∧ ζ| ≤ C (A₂ / c ∫_K |1 - |α|²| + A₁ / √c ∫_K |∂bar_a α|)`,

where `Θ - i F_a = Θ + da`. Top-degree coefficients are taken on `e` and integrated against its
Haar measure. -/
theorem exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le
    (e : Module.Basis (Fin (2 + n)) ℝ E) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃χ : ℝ → ℝ⦄ ⦃a : E → E [⋀^Fin 1]→L[ℝ] ℝ⦄ ⦃α : E → ℂ⦄
      ⦃ζ : E → E [⋀^Fin n]→L[ℝ] ℝ⦄ ⦃K : Set E⦄ ⦃c A₁ A₂ : ℝ⦄, 0 < c →
      (∀ t < c, χ t = 0) → (∀ t, |χ t| ≤ 1) → ContDiff ℝ 1 χ → ContDiff ℝ 2 α →
      ContDiff ℝ 1 a → ContDiff ℝ 2 ζ → IsCompact K → tsupport ζ ⊆ K →
      (∀ x, ‖extDeriv ζ x‖ ≤ A₁) → (∀ x, ‖fderiv ℝ (extDeriv ζ) x‖ ≤ A₂) →
      |∫ x, wedge (cutoffCurrent χ a α x + extDeriv a x) (ζ x) e ∂e.addHaar| ≤
        C * (A₂ / c * ∫ x in K, |normSq (α x) - 1| ∂e.addHaar +
          A₁ / √c * ∫ x in K, ‖covariantDBar J a α x‖ ∂e.addHaar) := by
  let e₁ := e.reindex (finCongr (by omega : 2 + n = 1 + (n + 1)))
  let J' := LinearMap.toContinuousLinearMap J.toLinearMap
  let L := compContinuousLinearMapCLM (F := ℝ) (ι := Fin (n + 1)) (-J')
  let e₂ := ⇑e₁ ∘ Fin.cast (show n + 1 + 1 = 1 + (n + 1) by omega)
  let K₁ := |LinearMap.det J.toLinearMap| / 2 * ((n + 2) * ‖L‖ * ∏ i, ‖e₂ i‖)
  let K₂ := (n + 2) * (∏ i, ‖e₁ i‖) * 2
  refine ⟨max K₁ K₂, by positivity, ?_⟩
  intro χ a α ζ K c A₁ A₂ hc hχc hχ₁ hχ hα ha hζ hK hζK hA₁ hA₂
  have hχ₀ : χ =ᶠ[𝓝 0] 0 := (eventually_lt_nhds hc).mono hχc
  have hcζ : HasCompactSupport ζ := hK.of_isClosed_subset (isClosed_tsupport ζ) hζK
  set η := extDeriv ζ
  have hη : ContDiff ℝ 1 η := contDiff_extDeriv hζ (by norm_num)
  have hcη : HasCompactSupport η := hcζ.extDeriv
  -- Outside `K` the form `dζ` and its derivative vanish.
  have hηK : tsupport η ⊆ K := tsupport_extDeriv_subset.trans hζK
  have hη0 (x) (hx : x ∉ K) : η x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (hηK h)
  have hDη0 (x) (hx : x ∉ K) : fderiv ℝ η x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hηK (tsupport_fderiv_subset ℝ h))
  have hA₁0 : 0 ≤ A₁ := (norm_nonneg _).trans (hA₁ 0)
  have hA₂0 : 0 ≤ A₂ := (ContinuousLinearMap.opNorm_nonneg _).trans (hA₂ 0)
  -- The modulus potential `H(|α|²)` and the decomposition `χ(|α|²) τ = d^c_J H(|α|²) + E`.
  set H := modulusPotential χ
  have hH (t : ℝ) : HasDerivAt H (χ t / t) t := hasDerivAt_modulusPotential hχ.continuous hχ₀ t
  have hs : ContDiff ℝ 1 fun y ↦ normSq (α y) := by
    simp_rw [normSq_eq_norm_sq]
    exact (contDiff_norm_sq ℝ).comp (hα.of_le one_le_two)
  have hg : ContDiff ℝ 1 fun y ↦ H (normSq (α y)) := by
    refine (contDiff_one_iff_deriv.2 ⟨fun t ↦ (hH t).differentiableAt, ?_⟩).comp hs
    rw [show deriv H = fun t ↦ χ t / t from funext fun t ↦ (hH t).deriv]
    exact hχ.continuous.div_id_of_eventuallyEq_zero hχ₀
  have hdec (x : E) : cutoffPhaseForm χ a α x =
      J.twistedDifferential (fun y ↦ H (normSq (α y))) x + cutoffDBarForm J χ a α x :=
    cutoffPhaseForm_eq_twistedDifferential_add J (hH _) (hχc 0 hc)
      (hα.differentiable two_ne_zero x)
  -- Reduce to the pairing of the cutoff phase form with `dζ`, evaluated on `e₁`.
  have he₁ : ⇑e ∘ Fin.cast (show 1 + (n + 1) = 2 + n by omega) = ⇑e₁ := by
    funext i
    simp [e₁]
  have hμ : e₁.addHaar = e.addHaar := Module.Basis.addHaar_reindex _ _
  rw [integral_cutoffCurrent_add_extDeriv_wedge_eq e hα ha hχ hχ₀ (hζ.of_le one_le_two) hcζ, he₁,
    ← hμ]
  set g := fun y ↦ H (normSq (α y))
  set A := fun x ↦ wedge (J.twistedDifferential g x) (η x) e₁ with hA_def
  set B := fun x ↦ wedge (cutoffDBarForm J χ a α x) (η x) e₁
  have hA : Integrable A e₁.addHaar :=
    (((J.contDiff_twistedDifferential (n := 0) (by simpa using hg)).wedge
      (hη.of_le zero_le_one)).continuous.eval_const _).integrable_of_hasCompactSupport
      (hcη.mono fun x hx h ↦ hx (by simp [h, wedge_def, pairedWedge_zero_right]))
  have hT : Integrable (fun x ↦ wedge (cutoffPhaseForm χ a α x) (η x) e₁) e₁.addHaar :=
    (((contDiff_cutoffPhaseForm (n := 0) (by simpa using hα.of_le one_le_two)
      (ha.of_le zero_le_one) (hχ.of_le zero_le_one) hχ₀).wedge
      (hη.of_le zero_le_one)).continuous.eval_const _).integrable_of_hasCompactSupport
      (hcη.mono fun x hx h ↦ hx (by simp [h, wedge_def, pairedWedge_zero_right]))
  have hsplit (x : E) : wedge (cutoffPhaseForm χ a α x) (η x) e₁ = A x + B x := by
    simp only [A, B, hdec, wedge_add_left, ContinuousAlternatingMap.add_apply]
  have hB : Integrable B e₁.addHaar :=
    (hT.sub hA).congr (Eventually.of_forall fun x ↦ by
      rw [Pi.sub_apply, hsplit, add_sub_cancel_left])
  rw [integral_congr_ae (Eventually.of_forall hsplit), integral_add hA hB]
  -- The `d^c_J H(|α|²)` term: integrate by parts onto the derivative of `dζ`.
  have hIA : |∫ x, A x ∂e₁.addHaar| ≤
      K₁ * (A₂ / c * ∫ x in K, |normSq (α x) - 1| ∂e₁.addHaar) := by
    rw [hA_def, J.integral_twistedDifferential_wedge_eq e₁ hg hη hcη]
    set η' := fun y ↦ (η y).compContinuousLinearMap (-J')
    have hDη' (x : E) : fderiv ℝ η' x = L.comp (fderiv ℝ η x) :=
      (L.hasFDerivAt.comp x (hη.differentiable one_ne_zero x).hasFDerivAt).fderiv
    have hnorm (x : E) : ‖extDeriv η' x‖ ≤ (n + 2) * ‖L‖ * A₂ := by
      have h₁ : ‖extDeriv η' x‖ ≤ ((n + 1 : ℕ) + 1 : ℝ) * ‖fderiv ℝ η' x‖ := by
        rw [extDeriv]
        exact norm_alternatizeUncurryFin_le _
      have h₂ : ‖fderiv ℝ η' x‖ ≤ ‖L‖ * A₂ := by
        rw [hDη']
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr; exact hA₂ x)
      calc ‖extDeriv η' x‖ ≤ (n + 2) * (‖L‖ * A₂) := by
            refine h₁.trans ?_
            push_cast
            rw [show (n : ℝ) + 1 + 1 = n + 2 by ring]
            gcongr
        _ = _ := by ring
    have hvan (x : E) (hx : x ∉ K) : g x * extDeriv η' x e₂ = 0 := by
      simp [extDeriv, hDη', hDη0 x hx, ← alternatizeUncurryFinCLM_apply]
    have hint : IntegrableOn (fun x ↦ (n + 2) * ‖L‖ * A₂ * (∏ i, ‖e₂ i‖) / c *
        |normSq (α x) - 1|) K e₁.addHaar :=
      (continuous_const.mul ((hs.continuous.sub continuous_const).abs)).continuousOn
        |>.integrableOn_compact hK
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan, abs_mul, abs_div, abs_two]
    calc |LinearMap.det J.toLinearMap| / 2 * |∫ x in K, g x * extDeriv η' x e₂ ∂e₁.addHaar|
        ≤ |LinearMap.det J.toLinearMap| / 2 * ∫ x in K, (n + 2) * ‖L‖ * A₂ * (∏ i, ‖e₂ i‖) / c *
            |normSq (α x) - 1| ∂e₁.addHaar := by
          gcongr
          rw [← Real.norm_eq_abs]
          refine norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem hK.measurableSet ?_)
          intro x _
          rw [Real.norm_eq_abs, abs_mul]
          have hH' : |g x| ≤ |normSq (α x) - 1| / c :=
            abs_modulusPotential_le hc (fun t _ ht ↦ hχc t ht) hχ₁ (normSq_nonneg _)
          have hD : |extDeriv η' x e₂| ≤ (n + 2) * ‖L‖ * A₂ * ∏ i, ‖e₂ i‖ := by
            rw [← Real.norm_eq_abs]
            exact ((extDeriv η' x).le_opNorm e₂).trans (by gcongr; exact hnorm x)
          calc |g x| * |extDeriv η' x e₂|
              ≤ |normSq (α x) - 1| / c * ((n + 2) * ‖L‖ * A₂ * ∏ i, ‖e₂ i‖) := by
                gcongr
            _ = _ := by ring
      _ = K₁ * (A₂ / c * ∫ x in K, |normSq (α x) - 1| ∂e₁.addHaar) := by
          rw [integral_const_mul]
          ring
  -- The correction term `E = 2 χ(|α|²) Re (α⁻¹ ∂bar_a α) ∘ J`, bounded pointwise.
  have hIB : |∫ x, B x ∂e₁.addHaar| ≤
      K₂ * (A₁ / √c * ∫ x in K, ‖covariantDBar J a α x‖ ∂e₁.addHaar) := by
    have hvan (x : E) (hx : x ∉ K) : B x = 0 := by
      simp [B, hη0 x hx, wedge_def, pairedWedge_zero_right]
    have hint : IntegrableOn (fun x ↦ K₂ * (A₁ / √c) * ‖covariantDBar J a α x‖) K e₁.addHaar :=
      (continuous_const.mul (continuous_covariantDBar J (hα.of_le one_le_two)
        ha.continuous).norm).continuousOn.integrableOn_compact hK
    have hrhs : K₂ * (A₁ / √c * ∫ x in K, ‖covariantDBar J a α x‖ ∂e₁.addHaar) =
        ∫ x in K, K₂ * (A₁ / √c) * ‖covariantDBar J a α x‖ ∂e₁.addHaar := by
      rw [integral_const_mul]
      ring
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan, hrhs, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem hK.measurableSet ?_)
    intro x _
    have hE := norm_cutoffDBarForm_le J hc (fun t _ ht ↦ hχc t ht) hχ₁ a α x
    calc ‖B x‖ ≤ ‖wedge (cutoffDBarForm J χ a α x) (η x)‖ * ∏ i, ‖e₁ i‖ :=
          (wedge (cutoffDBarForm J χ a α x) (η x)).le_opNorm _
      _ ≤ ((1 + (n + 1)).choose 1 * ‖cutoffDBarForm J χ a α x‖ * ‖η x‖) * ∏ i, ‖e₁ i‖ := by
          gcongr
          exact norm_wedge_le _ _
      _ ≤ ((n + 2) * (2 / √c * ‖covariantDBar J a α x‖) * A₁) * ∏ i, ‖e₁ i‖ := by
          rw [Nat.choose_one_right]
          push_cast
          rw [show (1 : ℝ) + (n + 1) = n + 2 by ring]
          gcongr
          exact hA₁ x
      _ = K₂ * (A₁ / √c) * ‖covariantDBar J a α x‖ := by
          simp only [K₂]
          ring
  have hX : 0 ≤ A₂ / c * ∫ x in K, |normSq (α x) - 1| ∂e₁.addHaar :=
    mul_nonneg (div_nonneg hA₂0 hc.le) (setIntegral_nonneg hK.measurableSet fun _ _ ↦ abs_nonneg _)
  have hY : 0 ≤ A₁ / √c * ∫ x in K, ‖covariantDBar J a α x‖ ∂e₁.addHaar :=
    mul_nonneg (div_nonneg hA₁0 (Real.sqrt_nonneg _))
      (setIntegral_nonneg hK.measurableSet fun _ _ ↦ norm_nonneg _)
  calc |∫ x, A x ∂e₁.addHaar + ∫ x, B x ∂e₁.addHaar|
      ≤ |∫ x, A x ∂e₁.addHaar| + |∫ x, B x ∂e₁.addHaar| := abs_add_le _ _
    _ ≤ K₁ * (A₂ / c * ∫ x in K, |normSq (α x) - 1| ∂e₁.addHaar) +
        K₂ * (A₁ / √c * ∫ x in K, ‖covariantDBar J a α x‖ ∂e₁.addHaar) := add_le_add hIA hIB
    _ ≤ _ := by
        rw [mul_add]
        gcongr
        exacts [le_max_left _ _, le_max_right _ _]

end TauCeti.SeibergWitten
