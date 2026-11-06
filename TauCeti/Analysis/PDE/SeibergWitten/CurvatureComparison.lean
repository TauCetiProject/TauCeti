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
import TauCeti.LinearAlgebra.Basis.Basic

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
  let e' := e.reindex (finCongr (by omega : 2 + n = 1 + n + 1))
  have h := e'.integral_extDeriv_wedge_eq_integral_wedge_extDeriv
    (contDiff_cutoffPhaseForm hα hb hχ hχ₀) hζ hc
  have h₁ : ⇑e' ∘ Fin.cast (show 1 + 1 + n = 1 + n + 1 by omega) = ⇑e :=
    e.reindex_finCongr_comp_cast _ _
  rw [h₁, e.reindex_finCongr_comp_cast, Module.Basis.addHaar_reindex, pow_one, neg_neg,
    one_mul] at h
  simpa only [cutoffCurrent_apply, sub_add_cancel] using h

variable (J : AlmostComplexStructure E)

/-- The pairing of a twisted differential `d^c_J g` with a compactly supported C1 form `η` of
complementary degree is bounded by `C A ∫_K |g|`, where `K` is a compact set containing the
support of `η` and `A` bounds the derivative of `η`. The constant `C` depends only on `J` and the
basis `e`. -/
private theorem exists_abs_integral_twistedDifferential_wedge_le {m : ℕ}
    (e : Module.Basis (Fin (1 + m)) ℝ E) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃g : E → ℝ⦄ ⦃η : E → E [⋀^Fin m]→L[ℝ] ℝ⦄ ⦃K : Set E⦄ ⦃A : ℝ⦄,
      ContDiff ℝ 1 g → ContDiff ℝ 1 η → IsCompact K → tsupport η ⊆ K →
      (∀ x, ‖fderiv ℝ η x‖ ≤ A) →
      |∫ x, wedge (J.twistedDifferential g x) (η x) e ∂e.addHaar| ≤
        C * (A * ∫ x in K, |g x| ∂e.addHaar) := by
  let J' := LinearMap.toContinuousLinearMap J.toLinearMap
  let L := compContinuousLinearMapCLM (F := ℝ) (ι := Fin m) (-J')
  let e' := ⇑e ∘ Fin.cast (show m + 1 = 1 + m by omega)
  refine ⟨|LinearMap.det J.toLinearMap| / 2 * ((m + 1) * ‖L‖ * ∏ i, ‖e' i‖), by positivity, ?_⟩
  intro g η K A hg hη hK hηK hA
  have hcη : HasCompactSupport η := hK.of_isClosed_subset (isClosed_tsupport η) hηK
  -- Integrate by parts onto the derivative of `η`, which vanishes outside `K`.
  rw [J.integral_twistedDifferential_wedge_eq e hg hη hcη]
  set η' := fun y ↦ (η y).compContinuousLinearMap (-J')
  have hDη' (x : E) : fderiv ℝ η' x = L.comp (fderiv ℝ η x) :=
    (L.hasFDerivAt.comp x (hη.differentiable one_ne_zero x).hasFDerivAt).fderiv
  have hnorm (x : E) : ‖extDeriv η' x‖ ≤ (m + 1) * ‖L‖ * A := by
    calc ‖extDeriv η' x‖ ≤ (m + 1) * ‖fderiv ℝ η' x‖ := norm_alternatizeUncurryFin_le _
      _ ≤ (m + 1) * (‖L‖ * A) := by
          rw [hDη']
          gcongr
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr; exact hA x)
      _ = _ := by ring
  have hvan (x : E) (hx : x ∉ K) : g x * extDeriv η' x e' = 0 := by
    have hDη0 : fderiv ℝ η x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (hηK (tsupport_fderiv_subset ℝ h))
    simp [extDeriv, hDη', hDη0, ← alternatizeUncurryFinCLM_apply]
  have hint : IntegrableOn (fun x ↦ (m + 1) * ‖L‖ * A * (∏ i, ‖e' i‖) * |g x|) K e.addHaar :=
    (continuous_const.mul hg.continuous.abs).continuousOn.integrableOn_compact hK
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan, abs_mul, abs_div, abs_two]
  calc |LinearMap.det J.toLinearMap| / 2 * |∫ x in K, g x * extDeriv η' x e' ∂e.addHaar|
      ≤ |LinearMap.det J.toLinearMap| / 2 *
          ∫ x in K, (m + 1) * ‖L‖ * A * (∏ i, ‖e' i‖) * |g x| ∂e.addHaar := by
        gcongr
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem hK.measurableSet ?_)
        intro x _
        rw [Real.norm_eq_abs, abs_mul, mul_comm]
        gcongr
        rw [← Real.norm_eq_abs]
        exact ((extDeriv η' x).le_opNorm e').trans (by gcongr; exact hnorm x)
    _ = _ := by
        rw [integral_const_mul]
        ring

/-- The pairing of the correction one-form `E = 2 χ(|α|²) Re (α⁻¹ ∂bar_a α) ∘ J` with a form `η`
of complementary degree is bounded by `2 (1 + m) A / √c ∫_K |∂bar_a α|` times the product of the
norms of the basis vectors, where `η` vanishes outside `K`, `|η| ≤ A`, and the cutoff `χ` vanishes
below `c` with `|χ| ≤ 1`. -/
private theorem abs_integral_cutoffDBarForm_wedge_le {m : ℕ} (e : Module.Basis (Fin (1 + m)) ℝ E)
    {η : E → E [⋀^Fin m]→L[ℝ] ℝ} {K : Set E} {c A : ℝ} (hc : 0 < c) (hχc : ∀ t < c, χ t = 0)
    (hχ₁ : ∀ t, |χ t| ≤ 1) (hα : ContDiff ℝ 1 α) (hb : Continuous b) (hK : IsCompact K)
    (hηK : ∀ x ∉ K, η x = 0) (hA : ∀ x, ‖η x‖ ≤ A) :
    |∫ x, wedge (cutoffDBarForm J χ b α x) (η x) e ∂e.addHaar| ≤
      2 * (1 + m) * (∏ i, ‖e i‖) * (A / √c * ∫ x in K, ‖covariantDBar J b α x‖ ∂e.addHaar) := by
  have hvan (x : E) (hx : x ∉ K) : wedge (cutoffDBarForm J χ b α x) (η x) e = 0 := by
    simp [hηK x hx, wedge_def, pairedWedge_zero_right]
  have hint : IntegrableOn
      (fun x ↦ 2 * (1 + m) * (∏ i, ‖e i‖) * (A / √c * ‖covariantDBar J b α x‖)) K e.addHaar :=
    (continuous_const.mul (continuous_const.mul (continuous_covariantDBar J hα hb).norm))
      |>.continuousOn.integrableOn_compact hK
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan, ← integral_const_mul,
    ← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem hK.measurableSet fun x _ ↦ ?_)
  have hE := norm_cutoffDBarForm_le J hc (fun t _ ht ↦ hχc t ht) hχ₁ b α x
  calc ‖wedge (cutoffDBarForm J χ b α x) (η x) e‖
      ≤ ‖wedge (cutoffDBarForm J χ b α x) (η x)‖ * ∏ i, ‖e i‖ :=
        (wedge (cutoffDBarForm J χ b α x) (η x)).le_opNorm _
    _ ≤ ((1 + m).choose 1 * ‖cutoffDBarForm J χ b α x‖ * ‖η x‖) * ∏ i, ‖e i‖ := by
        gcongr
        exact norm_wedge_le _ _
    _ ≤ ((1 + m) * (2 / √c * ‖covariantDBar J b α x‖) * A) * ∏ i, ‖e i‖ := by
        rw [Nat.choose_one_right]
        push_cast
        gcongr
        exact hA x
    _ = 2 * (1 + m) * (∏ i, ‖e i‖) * (A / √c * ‖covariantDBar J b α x‖) := by ring

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
  obtain ⟨C₁, hC₁, hTw⟩ := exists_abs_integral_twistedDifferential_wedge_le J e₁
  let C₂ : ℝ := 2 * (1 + (n + 1 : ℕ)) * ∏ i, ‖e₁ i‖
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, ?_⟩
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
  have hg : ContDiff ℝ 1 fun y ↦ H (normSq (α y)) := by
    refine (contDiff_one_iff_deriv.2 ⟨fun t ↦ (hH t).differentiableAt, ?_⟩).comp hs
    rw [show deriv H = fun t ↦ χ t / t from funext fun t ↦ (hH t).deriv]
    exact hχ.continuous.div_id_of_eventuallyEq_zero hχ₀
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
  set P := fun x ↦ wedge (J.twistedDifferential g x) (η x) e₁
  set Q := fun x ↦ wedge (cutoffDBarForm J χ b α x) (η x) e₁
  have hcw (φ : E → E [⋀^Fin 1]→L[ℝ] ℝ) : HasCompactSupport fun x ↦ wedge (φ x) (η x) e₁ :=
    hcη.wedge_left.comp_left (g := fun ω : E [⋀^Fin (1 + (n + 1))]→L[ℝ] ℝ ↦ ω e₁) rfl
  have hP : Integrable P e₁.addHaar :=
    (((J.contDiff_twistedDifferential (n := 0) (by simpa using hg)).wedge
      (hη.of_le zero_le_one)).continuous.eval_const _).integrable_of_hasCompactSupport
      (hcw _)
  have hT : Integrable (fun x ↦ wedge (cutoffPhaseForm χ b α x) (η x) e₁) e₁.addHaar :=
    (((contDiff_cutoffPhaseForm (n := 0) (by simpa using hα.of_le one_le_two)
      (hb.of_le zero_le_one) (hχ.of_le zero_le_one) hχ₀).wedge
      (hη.of_le zero_le_one)).continuous.eval_const _).integrable_of_hasCompactSupport
      (hcw _)
  have hsplit (x : E) : wedge (cutoffPhaseForm χ b α x) (η x) e₁ = P x + Q x := by
    simp only [P, Q, hdec, wedge_add_left, ContinuousAlternatingMap.add_apply]
  have hQ : Integrable Q e₁.addHaar :=
    (hT.sub hP).congr (Eventually.of_forall fun x ↦ by
      rw [Pi.sub_apply, hsplit, add_sub_cancel_left])
  rw [integral_congr_ae (Eventually.of_forall hsplit), integral_add hP hQ]
  -- The `d^c_J H(|α|²)` term, using `|H(s)| ≤ |s - 1| / c`.
  have hgK : ∫ x in K, |g x| ∂e₁.addHaar ≤ (∫ x in K, |normSq (α x) - 1| ∂e₁.addHaar) / c := by
    rw [← integral_div]
    refine setIntegral_mono_on (hg.continuous.abs.continuousOn.integrableOn_compact hK)
      (((hs.continuous.sub continuous_const).abs.div_const c).continuousOn.integrableOn_compact
        hK) hK.measurableSet fun x _ ↦ ?_
    exact abs_modulusPotential_le hc (fun t _ ht ↦ hχc t ht) hχ₁ (normSq_nonneg _)
  have hIP : |∫ x, P x ∂e₁.addHaar| ≤
      C₁ * (A₂ / c * ∫ x in K, |normSq (α x) - 1| ∂e₁.addHaar) :=
    calc |∫ x, P x ∂e₁.addHaar| ≤ C₁ * (A₂ * ∫ x in K, |g x| ∂e₁.addHaar) :=
          hTw hg hη hK hηK hA₂
      _ ≤ C₁ * (A₂ * ((∫ x in K, |normSq (α x) - 1| ∂e₁.addHaar) / c)) := by gcongr
      _ = _ := by ring
  -- The correction term `E = 2 χ(|α|²) Re (α⁻¹ ∂bar_a α) ∘ J`.
  have hIQ : |∫ x, Q x ∂e₁.addHaar| ≤
      C₂ * (A₁ / √c * ∫ x in K, ‖covariantDBar J b α x‖ ∂e₁.addHaar) := by
    simpa only [C₂, Nat.cast_add, Nat.cast_one] using
      abs_integral_cutoffDBarForm_wedge_le J e₁ hc hχc hχ₁ (hα.of_le one_le_two) hb.continuous hK
        hη0 hA₁
  have hX : 0 ≤ A₂ / c * ∫ x in K, |normSq (α x) - 1| ∂e₁.addHaar :=
    mul_nonneg (div_nonneg hA₂0 hc.le) (setIntegral_nonneg hK.measurableSet fun _ _ ↦ abs_nonneg _)
  have hY : 0 ≤ A₁ / √c * ∫ x in K, ‖covariantDBar J b α x‖ ∂e₁.addHaar :=
    mul_nonneg (div_nonneg hA₁0 (Real.sqrt_nonneg _))
      (setIntegral_nonneg hK.measurableSet fun _ _ ↦ norm_nonneg _)
  calc |∫ x, P x ∂e₁.addHaar + ∫ x, Q x ∂e₁.addHaar|
      ≤ |∫ x, P x ∂e₁.addHaar| + |∫ x, Q x ∂e₁.addHaar| := abs_add_le _ _
    _ ≤ C₁ * (A₂ / c * ∫ x in K, |normSq (α x) - 1| ∂e₁.addHaar) +
        C₂ * (A₁ / √c * ∫ x in K, ‖covariantDBar J b α x‖ ∂e₁.addHaar) := add_le_add hIP hIQ
    _ ≤ _ := by
        rw [mul_add]
        gcongr
        exacts [le_max_left _ _, le_max_right _ _]

end TauCeti.SeibergWitten
