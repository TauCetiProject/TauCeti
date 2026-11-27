/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.DiscCharge.Basic
public import TauCeti.MeasureTheory.Measure.NewtonMoments
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.MeasureTheory.Integral.Bochner.WithDensity
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# The slice measures of the cutoff current on a disc

Let `Θ = i F_a + d(χ(|α|²) τ)` be the cutoff current of an abelian Higgs pair `(a, α)`
(`TauCeti.SeibergWitten.cutoffCurrent`) and let `σ : ℂ → E` be a `C²` disc. The pullback `σ^* Θ`
is the two-form `f(w) dx ∧ dy` on the plane with *slice density*

`f(w) = (σ^* Θ)_w(1, i)`

(`TauCeti.SeibergWitten.sliceDensity`). In Taubes's analysis of Seiberg–Witten solutions near a
pseudoholomorphic curve `C`, `σ` runs over the dilated normal discs of `C`, and the normalized
slice `f dλ / 2π` on the closed disc of radius `R` is the signed measure `μ_z` whose moments
locate the local branches of the limiting curve.

For any density `f : ℂ → ℝ` this file splits the normalized slice into its positive and negative
parts,

`μ⁺ = (f⁺ / 2π) λ|_{B_R}`,  `μ⁻ = (f⁻ / 2π) λ|_{B_R}`

(`TauCeti.SeibergWitten.posSliceMeasure`, `TauCeti.SeibergWitten.negSliceMeasure`), two measures
carried by the closed disc `B_R = closedBall 0 R`, finite when `f` is integrable on it. Each
integrates a weight `g` to `(2π)⁻¹ ∫_{B_R} f^± g` (`TauCeti.SeibergWitten.integral_posSliceMeasure`,
`TauCeti.SeibergWitten.integral_negSliceMeasure`), so their difference integrates every weight `g`
continuous on the disc to `(2π)⁻¹ ∫_{B_R} f g`
(`TauCeti.SeibergWitten.integral_posSliceMeasure_sub_integral_negSliceMeasure`). They are the two
measures in Mathlib's decomposition of the signed measure `(f / 2π) λ|_{B_R}`
(`MeasureTheory.withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part`), kept as a pair
of finite measures because the compact moment lemma takes them in that form: given `m`, `R` and an
accuracy `ε > 0`, there is `δ > 0` such that for every density integrable on `B_R` whose slice has
mass `m`, with negative mass and Newton variance at most `δ`, the slice is within `ε` in the
bounded-Lipschitz distance of the counting measure of the roots of the Newton polynomial of its
moments (`TauCeti.SeibergWitten.exists_forall_abs_setIntegral_mul_sub_sum_roots_le`).

For the slice density of the cutoff current the file proves the two facts that make the slice an
input of that lemma:

* **Mass.** If the boundary circle of the disc lies in the vacuum region `χ(|α|²) = 1`, the
  total mass `μ⁺(ℂ) - μ⁻(ℂ)` is the winding number `n ∈ ℤ` of `α ∘ σ` around that circle
  (`TauCeti.SeibergWitten.exists_int_measureReal_posSliceMeasure_sub`). This is the integrality of
  the disc charge, `TauCeti.SeibergWitten.exists_int_integral_cutoffCurrent_comp_closedBall`.
* **Negative mass.** If `σ` is `J`-holomorphic, the Hermitian part of the curvature is bounded
  below, `i F_a(v, J v) ≥ -K |v|²`, and `|∂bar_a α| ≤ D`, then
  `μ⁻(ℂ) ≤ (K + 2 M D²) / 2π · ∫_{B_R} |dσ(1)|²`, where `M` bounds `χ'`
  (`TauCeti.SeibergWitten.measureReal_negSliceMeasure_le`). If moreover `|dσ(1)| ≤ L` on the disc,
  the energy is at most `π R² L²`, so `μ⁻(ℂ) ≤ (K + 2 M D²) L² R² / 2`
  (`TauCeti.SeibergWitten.measureReal_negSliceMeasure_le_of_norm_le`). For a dilated normal
  disc `w ↦ F(a • w)` the chain rule gives `dσ_w(1) = a dF_{a w}(1)`, so `|dF(1)| ≤ K'` allows
  `L = |a| K'`, and the negative mass is `O(a²)`.

The Newton-variance bound, which in Taubes's argument comes from the coupled Seiberg–Witten
equations, is not proved here.

## Main definitions

* `TauCeti.SeibergWitten.sliceDensity χ b α σ`: the density `(σ^* Θ)(1, i)` of the pullback of
  the cutoff current by a disc.
* `TauCeti.SeibergWitten.posSliceMeasure f R`, `TauCeti.SeibergWitten.negSliceMeasure f R`: the
  positive and negative parts of the normalized slice `f dλ / 2π` on the closed disc of radius
  `R`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open ContinuousAlternatingMap Complex Filter Metric MeasureTheory Set
open scoped Topology Real ENNReal

namespace TauCeti.SeibergWitten

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {χ : ℝ → ℝ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {α : E → ℂ} {σ : ℂ → E} {f : ℂ → ℝ} {R : ℝ}

/-! ### The slice density -/

/-- The **slice density** of the cutoff current on a disc `σ : ℂ → E`: the coefficient
`(σ^* Θ)_w(1, i)` of the pullback of the cutoff current `Θ` by `σ`, so that
`σ^* Θ = sliceDensity χ b α σ w dx ∧ dy`. -/
def sliceDensity (χ : ℝ → ℝ) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → ℂ) (σ : ℂ → E) (w : ℂ) :
    ℝ :=
  (cutoffCurrent χ b α (σ w)).compContinuousLinearMap (fderiv ℝ σ w) ![1, I]

theorem sliceDensity_def (χ : ℝ → ℝ) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → ℂ) (σ : ℂ → E)
    (w : ℂ) :
    sliceDensity χ b α σ w =
      (cutoffCurrent χ b α (σ w)).compContinuousLinearMap (fderiv ℝ σ w) ![1, I] := (rfl)

/-- The slice density vanishes wherever the disc meets a zero of the cutoff current: it is
supported in the preimage of the support of `Θ`. -/
theorem support_sliceDensity_subset (χ : ℝ → ℝ) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → ℂ)
    (σ : ℂ → E) :
    Function.support (sliceDensity χ b α σ) ⊆ σ ⁻¹' Function.support (cutoffCurrent χ b α) := by
  intro w hw hΘ
  simp [Function.mem_support, sliceDensity_def, hΘ] at hw

/-- The slice density of a `C²` pair on a `C²` disc is continuous, for a `C¹` cutoff vanishing
near `0`. -/
theorem continuous_sliceDensity (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b)
    (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (hσ : ContDiff ℝ 2 σ) :
    Continuous (sliceDensity χ b α σ) := by
  have hpull : ContDiff ℝ 1 fun z ↦ (b (σ z)).compContinuousLinearMap (fderiv ℝ σ z) :=
    contDiff_iff_contDiffAt.2 fun z ↦ hσ.contDiffAt.differentialForm_pullback hb.contDiffAt
  have hΘ := (contDiff_cutoffCurrent (m := 0) (n := 1) (hα.comp hσ) hpull hχ hχ₀
    le_rfl).continuous
  have heq : sliceDensity χ b α σ = fun w ↦
      cutoffCurrent χ (fun z ↦ (b (σ z)).compContinuousLinearMap (fderiv ℝ σ z)) (α ∘ σ) w
        ![1, I] := by
    funext w
    rw [sliceDensity_def, cutoffCurrent_comp hα.contDiffAt hb.contDiffAt hχ hχ₀ hσ.contDiffAt]
  rw [heq]
  exact continuous_eval_const _ |>.comp hΘ

/-! ### The positive and negative slice measures of a density -/

/-- The **positive slice measure** of a density `f` on the plane: the positive part `(f⁺ / 2π) λ`
of the normalized slice `f dλ / 2π` on the closed disc of radius `R`. -/
def posSliceMeasure (f : ℂ → ℝ) (R : ℝ) : Measure ℂ :=
  (volume.restrict (closedBall 0 R)).withDensity fun w ↦ ENNReal.ofReal ((f w)⁺ / (2 * π))

/-- The **negative slice measure** of a density `f` on the plane: the negative part `(f⁻ / 2π) λ`
of the normalized slice `f dλ / 2π` on the closed disc of radius `R`. -/
def negSliceMeasure (f : ℂ → ℝ) (R : ℝ) : Measure ℂ :=
  (volume.restrict (closedBall 0 R)).withDensity fun w ↦ ENNReal.ofReal ((f w)⁻ / (2 * π))

theorem posSliceMeasure_def (f : ℂ → ℝ) (R : ℝ) :
    posSliceMeasure f R = (volume.restrict (closedBall 0 R)).withDensity fun w ↦
      ENNReal.ofReal ((f w)⁺ / (2 * π)) := (rfl)

theorem negSliceMeasure_def (f : ℂ → ℝ) (R : ℝ) :
    negSliceMeasure f R = (volume.restrict (closedBall 0 R)).withDensity fun w ↦
      ENNReal.ofReal ((f w)⁻ / (2 * π)) := (rfl)

/-- The negative slice measure of `f` is the positive slice measure of `-f`. -/
theorem negSliceMeasure_eq_posSliceMeasure_neg (f : ℂ → ℝ) (R : ℝ) :
    negSliceMeasure f R = posSliceMeasure (-f) R := by
  simp only [negSliceMeasure_def, posSliceMeasure_def, Pi.neg_apply, posPart_neg]

/-- The positive slice measure is carried by the closed disc of radius `R`. -/
@[simp]
theorem posSliceMeasure_compl_closedBall : posSliceMeasure f R (closedBall 0 R)ᶜ = 0 :=
  withDensity_restrict_apply_compl measurableSet_closedBall _

/-- The negative slice measure is carried by the closed disc of radius `R`. -/
@[simp]
theorem negSliceMeasure_compl_closedBall : negSliceMeasure f R (closedBall 0 R)ᶜ = 0 := by
  rw [negSliceMeasure_eq_posSliceMeasure_neg]
  exact posSliceMeasure_compl_closedBall

/-- The positive slice measure of a density integrable on the closed disc of radius `R` is
finite. -/
theorem isFiniteMeasure_posSliceMeasure (hf : IntegrableOn f (closedBall 0 R)) :
    IsFiniteMeasure (posSliceMeasure f R) :=
  isFiniteMeasure_withDensity_ofReal (hf.pos_part.div_const _).2

/-- The negative slice measure of a density integrable on the closed disc of radius `R` is
finite. -/
theorem isFiniteMeasure_negSliceMeasure (hf : IntegrableOn f (closedBall 0 R)) :
    IsFiniteMeasure (negSliceMeasure f R) := by
  rw [negSliceMeasure_eq_posSliceMeasure_neg]
  exact isFiniteMeasure_posSliceMeasure hf.neg

/-- **Integrals against the positive slice measure.** Integrating `h` against `μ⁺` is integrating
`(f⁺ / 2π) h` over the closed disc of radius `R`. -/
theorem integral_posSliceMeasure {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hf : AEMeasurable f (volume.restrict (closedBall 0 R))) (h : ℂ → F) :
    ∫ w, h w ∂posSliceMeasure f R = ∫ w in closedBall 0 R, ((f w)⁺ / (2 * π)) • h w :=
  TauCeti.MeasureTheory.integral_withDensity_ofReal
    ((continuous_posPart.measurable.comp_aemeasurable hf).div_const _)
    (ae_of_all _ fun _ ↦ div_nonneg (posPart_nonneg _) (by positivity)) h

/-- **Integrals against the negative slice measure.** Integrating `h` against `μ⁻` is integrating
`(f⁻ / 2π) h` over the closed disc of radius `R`. -/
theorem integral_negSliceMeasure {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hf : AEMeasurable f (volume.restrict (closedBall 0 R))) (h : ℂ → F) :
    ∫ w, h w ∂negSliceMeasure f R = ∫ w in closedBall 0 R, ((f w)⁻ / (2 * π)) • h w := by
  simpa only [negSliceMeasure_eq_posSliceMeasure_neg, Pi.neg_apply, posPart_neg] using
    integral_posSliceMeasure hf.neg h

/-- The mass of the positive slice measure is `(2π)⁻¹ ∫_{B_R} f⁺`. -/
theorem measureReal_posSliceMeasure (hf : AEMeasurable f (volume.restrict (closedBall 0 R))) :
    (posSliceMeasure f R).real univ = (2 * π)⁻¹ * ∫ w in closedBall 0 R, (f w)⁺ := by
  have h := integral_posSliceMeasure hf fun _ ↦ (1 : ℝ)
  rw [integral_const, smul_eq_mul, mul_one] at h
  rw [h, ← integral_const_mul]
  congr 1 with w
  rw [smul_eq_mul, mul_one, div_eq_inv_mul]

/-- The mass of the negative slice measure is `(2π)⁻¹ ∫_{B_R} f⁻`. -/
theorem measureReal_negSliceMeasure (hf : AEMeasurable f (volume.restrict (closedBall 0 R))) :
    (negSliceMeasure f R).real univ = (2 * π)⁻¹ * ∫ w in closedBall 0 R, (f w)⁻ := by
  simpa only [negSliceMeasure_eq_posSliceMeasure_neg, Pi.neg_apply, posPart_neg] using
    measureReal_posSliceMeasure hf.neg

/-- **The integral against the normalized slice.** For a density `f` integrable on the closed disc
of radius `R` and a weight `h` continuous on it, the difference of the integrals of `h` against
the positive and negative slice measures is the integral of `h` against the normalized slice
`f dλ / 2π` on the disc. -/
theorem integral_posSliceMeasure_sub_integral_negSliceMeasure {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hf : IntegrableOn f (closedBall 0 R)) {h : ℂ → F}
    (hh : ContinuousOn h (closedBall 0 R)) :
    ∫ w, h w ∂posSliceMeasure f R - ∫ w, h w ∂negSliceMeasure f R =
      (2 * π)⁻¹ • ∫ w in closedBall 0 R, f w • h w := by
  have hint {g : ℂ → ℝ} (hg : IntegrableOn g (closedBall 0 R)) :
      IntegrableOn (fun w ↦ (g w / (2 * π)) • h w) (closedBall 0 R) :=
    IntegrableOn.smul_continuousOn (hg.div_const _) hh (isCompact_closedBall 0 R)
  have hpos : IntegrableOn (fun w ↦ (f w)⁺) (closedBall 0 R) := hf.pos_part
  have hneg : IntegrableOn (fun w ↦ (f w)⁻) (closedBall 0 R) := hf.neg_part
  rw [integral_posSliceMeasure hf.aemeasurable, integral_negSliceMeasure hf.aemeasurable,
    ← integral_sub (hint hpos) (hint hneg), ← integral_smul]
  congr 1 with w
  rw [← sub_smul, ← sub_div, posPart_sub_negPart, smul_smul, div_eq_inv_mul]

/-- The total mass of the normalized slice: the difference of the masses of the positive and
negative slice measures is `(2π)⁻¹ ∫_{B_R} f`. -/
theorem measureReal_posSliceMeasure_sub_measureReal_negSliceMeasure
    (hf : IntegrableOn f (closedBall 0 R)) :
    (posSliceMeasure f R).real univ - (negSliceMeasure f R).real univ =
      (2 * π)⁻¹ * ∫ w in closedBall 0 R, f w := by
  have h := integral_posSliceMeasure_sub_integral_negSliceMeasure hf
    (h := fun _ ↦ (1 : ℝ)) continuousOn_const
  simpa using h

/-! ### The compact moment lemma for slices -/

/-- **The compact moment lemma for slices.** For every accuracy `ε > 0` there is a tolerance
`δ > 0`, depending only on `m`, `R` and `ε`, with the following property. Let `f` be a density
integrable on the closed disc of radius `R`, and suppose that the normalized slice `f dλ / 2π` on
that disc has total mass `m`, negative mass at most `δ`, and Newton variance `∫ |P(w)|² dμ⁺(w)` at
most `δ`, where `P` is the Newton polynomial of degree `m` of its moments. Then for every
`1`-Lipschitz `g : ℂ → ℝ` bounded by `1`, the integral of `g` against the normalized slice is
within `ε` of the sum of `g` over the roots of `P`. -/
theorem exists_forall_abs_setIntegral_mul_sub_sum_roots_le (m : ℕ) (R : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ f : ℂ → ℝ, IntegrableOn f (closedBall 0 R) →
      (posSliceMeasure f R).real univ - (negSliceMeasure f R).real univ = m →
      (negSliceMeasure f R).real univ ≤ δ →
      ∫ w, ‖(newtonPolynomial (fun k ↦ ∫ w, w ^ k ∂posSliceMeasure f R -
        ∫ w, w ^ k ∂negSliceMeasure f R) m).eval w‖ ^ 2 ∂posSliceMeasure f R ≤ δ →
      ∀ g : ℂ → ℝ, LipschitzWith 1 g → (∀ w, |g w| ≤ 1) →
        |(2 * π)⁻¹ * (∫ w in closedBall 0 R, f w * g w) -
          ((newtonPolynomial (fun k ↦ ∫ w, w ^ k ∂posSliceMeasure f R -
            ∫ w, w ^ k ∂negSliceMeasure f R) m).roots.map g).sum| ≤ ε := by
  obtain ⟨δ, hδ, h⟩ := exists_forall_abs_integral_sub_sum_roots_le m R hε
  refine ⟨δ, hδ, fun f hf hmass hneg hvar g hg hg₁ ↦ ?_⟩
  have := isFiniteMeasure_posSliceMeasure hf
  have := isFiniteMeasure_negSliceMeasure hf
  have hint := integral_posSliceMeasure_sub_integral_negSliceMeasure hf hg.continuous.continuousOn
  simp only [smul_eq_mul] at hint
  rw [← hint]
  exact h _ _ posSliceMeasure_compl_closedBall negSliceMeasure_compl_closedBall hmass hneg hvar
    g hg hg₁

/-! ### Mass and negative mass of the slices of the cutoff current -/

/-- **The slice has integer mass.** If the cutoff is `1` along `σ` of the boundary circle of the
closed disc of radius `R`, the total mass `μ⁺(ℂ) - μ⁻(ℂ)` of the normalized slice of the cutoff
current is the winding number of `α ∘ σ` around that circle, an integer. -/
theorem exists_int_measureReal_posSliceMeasure_sub (hR : 0 ≤ R) (hα : ContDiff ℝ 2 α)
    (hb : ContDiff ℝ 1 b) (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (hσ : ContDiff ℝ 2 σ)
    (hbd : ∀ θ, χ (normSq (α (σ (circleMap 0 R θ)))) = 1) :
    ∃ n : ℤ, Contour.windingNumber (α ∘ σ ∘ circleMap 0 R) (-π) π 0 = n ∧
      (posSliceMeasure (sliceDensity χ b α σ) R).real univ -
        (negSliceMeasure (sliceDensity χ b α σ) R).real univ = n := by
  obtain ⟨n, hn, hint⟩ :=
    exists_int_integral_cutoffCurrent_comp_closedBall (b := b) hR hα hb hχ hχ₀ hσ hbd
  refine ⟨n, hn, ?_⟩
  rw [measureReal_posSliceMeasure_sub_measureReal_negSliceMeasure
    ((continuous_sliceDensity hα hb hχ hχ₀ hσ).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 R))]
  simp only [sliceDensity_def, hint]
  field_simp

section AlmostComplex

variable [FiniteDimensional ℝ E] (J : AlmostComplexStructure E)

/-- **Negative mass of the slice.** Let `σ` be a `C²` disc, `J`-holomorphic on the closed disc of
radius `R`, `dσ(i) = J dσ(1)`, and suppose that along it the cutoff satisfies `0 ≤ χ ≤ 1` and
`0 ≤ χ' ≤ M`, the curvature `i F_a = -db` satisfies `i F_a(v, J v) ≥ -K |v|²` for `v = dσ(1)`,
with `K ≥ 0`, and `|∂bar_a α| ≤ D`. Then the negative slice measure has mass at most
`(K + 2 M D²) / 2π` times the directional energy `∫_{B_R} |dσ(1)|²`. -/
theorem measureReal_negSliceMeasure_le (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b)
    (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (hσ : ContDiff ℝ 2 σ) {K M D : ℝ}
    (hχ₁ : ∀ w ∈ closedBall (0 : ℂ) R, χ (normSq (α (σ w))) ∈ Icc 0 1)
    (hχ' : ∀ w ∈ closedBall (0 : ℂ) R, deriv χ (normSq (α (σ w))) ∈ Icc 0 M) (hK : 0 ≤ K)
    (hJ : ∀ w ∈ closedBall (0 : ℂ) R, fderiv ℝ σ w I = J (fderiv ℝ σ w 1))
    (hF : ∀ w ∈ closedBall (0 : ℂ) R, -K * ‖fderiv ℝ σ w 1‖ ^ 2 ≤
      -extDeriv b (σ w) ![fderiv ℝ σ w 1, J (fderiv ℝ σ w 1)])
    (hD : ∀ w ∈ closedBall (0 : ℂ) R, ‖covariantDBar J b α (σ w)‖ ≤ D) :
    (negSliceMeasure (sliceDensity χ b α σ) R).real univ ≤
      (K + 2 * M * D ^ 2) / (2 * π) * ∫ w in closedBall 0 R, ‖fderiv ℝ σ w 1‖ ^ 2 := by
  have hσ' : Continuous fun w ↦ ‖fderiv ℝ σ w 1‖ ^ 2 :=
    ((hσ.continuous_fderiv two_ne_zero).clm_apply continuous_const).norm.pow 2
  have hneg := integral_negPart_cutoffCurrent_compContinuousLinearMap_le J
    (s := closedBall 0 R) measurableSet_closedBall (fun _ _ ↦ hα.contDiffAt)
    (fun _ _ ↦ hb.differentiable one_ne_zero _)
    (fun _ _ ↦ hχ.differentiable one_ne_zero _) hχ₀ hχ₁ hχ' hK hJ hF hD
    (hσ'.continuousOn.integrableOn_compact (isCompact_closedBall 0 R))
  rw [measureReal_negSliceMeasure (continuous_sliceDensity hα hb hχ hχ₀ hσ).aemeasurable,
    div_eq_inv_mul, mul_assoc]
  simp only [sliceDensity_def]
  exact mul_le_mul_of_nonneg_left hneg (by positivity)

/-- **The negative mass of a slice of bounded derivative.** Under the hypotheses of
`TauCeti.SeibergWitten.measureReal_negSliceMeasure_le`, if moreover `|dσ(1)| ≤ L` on the closed
disc of radius `R ≥ 0`, the negative slice measure has mass at most `(K + 2 M D²) L² R² / 2`. For
a dilated disc `w ↦ F(a • w)` with `|dF(1)| ≤ K'` on the disc of radius `|a| R` one may take
`L = |a| K'`, so the negative mass is `O(a²)`. -/
theorem measureReal_negSliceMeasure_le_of_norm_le (hR : 0 ≤ R) (hα : ContDiff ℝ 2 α)
    (hb : ContDiff ℝ 1 b) (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (hσ : ContDiff ℝ 2 σ)
    {K M D L : ℝ}
    (hχ₁ : ∀ w ∈ closedBall (0 : ℂ) R, χ (normSq (α (σ w))) ∈ Icc 0 1)
    (hχ' : ∀ w ∈ closedBall (0 : ℂ) R, deriv χ (normSq (α (σ w))) ∈ Icc 0 M) (hK : 0 ≤ K)
    (hJ : ∀ w ∈ closedBall (0 : ℂ) R, fderiv ℝ σ w I = J (fderiv ℝ σ w 1))
    (hF : ∀ w ∈ closedBall (0 : ℂ) R, -K * ‖fderiv ℝ σ w 1‖ ^ 2 ≤
      -extDeriv b (σ w) ![fderiv ℝ σ w 1, J (fderiv ℝ σ w 1)])
    (hD : ∀ w ∈ closedBall (0 : ℂ) R, ‖covariantDBar J b α (σ w)‖ ≤ D)
    (hL : ∀ w ∈ closedBall (0 : ℂ) R, ‖fderiv ℝ σ w 1‖ ≤ L) :
    (negSliceMeasure (sliceDensity χ b α σ) R).real univ ≤
      (K + 2 * M * D ^ 2) * L ^ 2 * R ^ 2 / 2 := by
  have hM : 0 ≤ M := (hχ' 0 (mem_closedBall_self hR)).1.trans (hχ' 0 (mem_closedBall_self hR)).2
  have hvol : volume.real (closedBall (0 : ℂ) R) = π * R ^ 2 := by
    simp [measureReal_def, ENNReal.toReal_ofReal hR, mul_comm]
  calc (negSliceMeasure (sliceDensity χ b α σ) R).real univ
      ≤ (K + 2 * M * D ^ 2) / (2 * π) * ∫ w in closedBall 0 R, ‖fderiv ℝ σ w 1‖ ^ 2 :=
        measureReal_negSliceMeasure_le J hα hb hχ hχ₀ hσ hχ₁ hχ' hK hJ hF hD
    _ ≤ (K + 2 * M * D ^ 2) / (2 * π) * (L ^ 2 * volume.real (closedBall (0 : ℂ) R)) := by
        gcongr
        refine (Real.le_norm_self _).trans <|
          norm_setIntegral_le_of_norm_le_const measure_closedBall_lt_top fun w hw ↦ ?_
        rw [norm_pow, norm_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) (hL w hw) 2
    _ = (K + 2 * M * D ^ 2) * L ^ 2 * R ^ 2 / 2 := by
        rw [hvol]
        field_simp

end AlmostComplex

end TauCeti.SeibergWitten
