/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.SchwarzRearrangement.CriticalValues
public import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Continuous
import TauCeti.Analysis.BoundedVariation.LevelSurface
import TauCeti.Analysis.BoundedVariation.SchwarzRearrangement
import TauCeti.Analysis.Calculus.FDeriv.Norm
import TauCeti.Analysis.Calculus.FDeriv.Measurable
import TauCeti.Analysis.Convex.Deriv
import TauCeti.MeasureTheory.Function.Coarea.Critical

/-!
# The Pólya–Szegő inequality for Lipschitz functions

Let `h` be a real Lipschitz function on a finite-dimensional real inner product space whose
superlevel sets `{h > t}` have finite volume for `t > 0`, for instance a nonnegative integrable
Lipschitz function, and let `h*` be the real Schwarz rearrangement of its positive part. For every
convex `Φ` on `[0, ∞)` with `Φ 0 ≤ 0`,

`∫ Φ(‖∇h*‖) ≤ ∫ Φ(‖∇h‖)`

(`LipschitzWith.lintegral_ofReal_comp_norm_fderiv_toReal_schwarzRearrangement_le`), as extended
nonnegative integrals of the positive part of `Φ`, so that both sides may be infinite. Gradients
are the totalized Fréchet derivatives, which agree almost everywhere with the Rademacher gradients
of these Lipschitz functions. The case `Φ(s) = s` is the `L¹` comparison of gradients
(`LipschitzWith.lintegral_enorm_fderiv_toReal_schwarzRearrangement_le`). Usually `Φ` is also
nondecreasing with `Φ 0 = 0`; then the positive part of `Φ` is `Φ` itself on `[0, ∞)`.

## Strategy

By the coarea formula, `∫ Φ(‖∇g‖)` is the integral over the levels `t` of the level contributions
`F_g(t) = ∫_{{g = t} ∩ {∇g ≠ 0}} Φ(‖∇g‖) ‖∇g‖⁻¹ dHⁿ⁻¹`
(`MeasureTheory.lintegral_comp_norm_fderiv_eq_lintegral_setLIntegral`). We compare `F_{h*}(t)`
with `F_h(t)` at almost every level `t > 0`, using the following inputs.

* **Volume.** The level integrals `m_g(t) = ∫_{{g = t} ∩ {∇g ≠ 0}} ‖∇g‖⁻¹ dHⁿ⁻¹` satisfy
  `m_h(t) ≤ -μ'(t) = m_{h*}(t)`, where `μ(t) = |{h > t}|` is the common distribution function.
* **Area.** The regular part of the level surface of `h*` has at most the area of that of `h`:
  the level surfaces carry the perimeters of the superlevel sets, the rearranged superlevel set is
  the ball of the same volume, and the critical part of almost every level surface of `h` is
  Hausdorff-null. The sharp isoperimetric inequality then compares the two perimeters.
* **Radial structure.** The gradient norm of the radially nonincreasing function `h*` is constant
  on the regular part of each level set (`TauCeti.norm_fderiv_eq_of_antitone_norm`).

Write `P_g(t)` for the area of the regular part of the level surface of `g`. A tangent line to
the positive part of `Φ` at the constant gradient norm `c` of `h*` on its level `t` has slope
`k ≥ 0` and intercept `-d ≤ 0`. It lies below that positive part, so
`F_h(t) + d m_h(t) ≥ k P_h(t)`, with equality `F_{h*}(t) + d m_{h*}(t) = k P_{h*}(t)` for `h*`.
This is Jensen's inequality for the probability measure proportional to `‖∇h‖⁻¹ dHⁿ⁻¹` on the
level surface, and the volume and area comparisons then give `F_{h*}(t) ≤ F_h(t)`.

## References

* G. Bianchi, R. J. Gardner, P. Gronchi, M. Kiderlen, *The Pólya–Szegő inequality for smoothing
  rearrangements*, arXiv:2206.09833, Theorem 5.8.
* J. E. Brothers, W. P. Ziemer, *Minimal rearrangements of Sobolev functions*, J. Reine Angew.
  Math. **384** (1988), 153–179.
-/

public section

open MeasureTheory Set Filter Module
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A tangent line to the positive part of a convex function `Φ` on `[0, ∞)` with `Φ 0 ≤ 0`, at a
point `c > 0`, written in `ℝ≥0∞`: it has a slope `k` and a finite intercept `-d`, lies below
`Φ` on `[0, ∞)` and touches it at `c`. -/
private theorem exists_tangent {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦ0 : Φ 0 ≤ 0)
    {c : ℝ} (hc : 0 < c) :
    ∃ k d : ℝ≥0∞, d ≠ ∞ ∧
      (∀ s, 0 ≤ s → k * ENNReal.ofReal s ≤ ENNReal.ofReal (Φ s) + d) ∧
      ENNReal.ofReal (Φ c) + d = k * ENNReal.ofReal c := by
  set Ψ : ℝ → ℝ := fun s ↦ max (Φ s) 0
  have hΨ : ConvexOn ℝ (Ici 0) Ψ := hΦ.sup (convexOn_const 0 (convex_Ici 0))
  have hΨ0 : Ψ 0 = 0 := max_eq_right hΦ0
  have hc' : c ∈ interior (Ici (0 : ℝ)) := by rwa [interior_Ici]
  set k := derivWithin Ψ (Ioi c) c
  have htan (s : ℝ) (hs : 0 ≤ s) : Ψ c + k * (s - c) ≤ Ψ s := hΨ.add_rightDeriv_mul_sub_le hc' hs
  -- The tangent line passes below the origin, so its slope is nonnegative.
  have hd : 0 ≤ k * c - Ψ c := by linarith [htan 0 le_rfl]
  have hk : 0 ≤ k := nonneg_of_mul_nonneg_left (by linarith [le_max_right (Φ c) 0]) hc
  have hofReal (s : ℝ) : ENNReal.ofReal (Φ s) = ENNReal.ofReal (Ψ s) := by
    simp [Ψ, ENNReal.ofReal_max]
  refine ⟨ENNReal.ofReal k, ENNReal.ofReal (k * c - Ψ c), ENNReal.ofReal_ne_top,
    fun s hs ↦ ?_, ?_⟩
  · rw [hofReal, ← ENNReal.ofReal_mul hk, ← ENNReal.ofReal_add (le_max_right _ _) hd]
    exact ENNReal.ofReal_le_ofReal (by linarith [htan s hs])
  · rw [hofReal, ← ENNReal.ofReal_mul hk, ← ENNReal.ofReal_add (le_max_right _ _) hd]
    congr 1
    ring

/-- The levelwise comparison behind the Pólya–Szegő inequality, in the form of Jensen's inequality
for a tangent line. Let `u` and `v` be nonvanishing on measurable sets `A` and `B`, with `‖v‖`
constant on `B`. If `B` has at most the measure of `A`, and the integral of `‖v‖⁻¹` over `B` is
finite and at least that of `‖u‖⁻¹` over `A`, then the integral of `Φ(‖v‖) ‖v‖⁻¹` over `B` is at
most that of `Φ(‖u‖) ‖u‖⁻¹` over `A`. -/
private theorem setLIntegral_ofReal_mul_inv_le {X F G : Type*} [MeasurableSpace X]
    {ν : Measure X} [NormedAddCommGroup F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [NormedAddCommGroup G] {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦ0 : Φ 0 ≤ 0)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) {u : X → F} {v : X → G}
    (hu : Measurable u) (huA : ∀ x ∈ A, u x ≠ 0) (hvB : ∀ x ∈ B, v x ≠ 0)
    (hvc : ∀ x ∈ B, ∀ y ∈ B, ‖v x‖ = ‖v y‖) (hP : ν B ≤ ν A)
    (hm : ∫⁻ x in A, ‖u x‖ₑ⁻¹ ∂ν ≤ ∫⁻ x in B, ‖v x‖ₑ⁻¹ ∂ν)
    (hm' : ∫⁻ x in B, ‖v x‖ₑ⁻¹ ∂ν ≠ ∞) :
    ∫⁻ x in B, ENNReal.ofReal (Φ ‖v x‖) * ‖v x‖ₑ⁻¹ ∂ν ≤
      ∫⁻ x in A, ENNReal.ofReal (Φ ‖u x‖) * ‖u x‖ₑ⁻¹ ∂ν := by
  rcases B.eq_empty_or_nonempty with rfl | ⟨b, hb⟩
  · simp
  obtain ⟨k, d, hd, hle, heq⟩ := exists_tangent hΦ hΦ0 (norm_pos_iff.2 (hvB b hb))
  -- On `B` the tangent line touches: the weight `(Φ(‖v‖) + d) ‖v‖⁻¹` is the slope `k`.
  have hBk : ∫⁻ x in B, ENNReal.ofReal (Φ ‖v x‖) * ‖v x‖ₑ⁻¹ ∂ν +
      d * ∫⁻ x in B, ‖v x‖ₑ⁻¹ ∂ν ≤ k * ν B := by
    rw [← lintegral_const_mul' d _ hd, ← setLIntegral_const]
    refine (le_lintegral_add _ _).trans (setLIntegral_mono' hB fun x hx ↦ ?_)
    rw [← add_mul, ← ofReal_norm, hvc x hx b hb, heq, mul_assoc,
      ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 (norm_pos_iff.2 (hvB b hb))).ne'
        ENNReal.ofReal_ne_top, mul_one]
  -- On `A` the tangent line lies below: the weight `(Φ(‖u‖) + d) ‖u‖⁻¹` is at least `k`.
  have hAk : k * ν A ≤ ∫⁻ x in A, ENNReal.ofReal (Φ ‖u x‖) * ‖u x‖ₑ⁻¹ ∂ν +
      d * ∫⁻ x in A, ‖u x‖ₑ⁻¹ ∂ν := by
    have hmeas : Measurable fun x ↦ d * ‖u x‖ₑ⁻¹ := hu.eNorm.inv.const_mul d
    rw [← lintegral_const_mul' d _ hd, ← setLIntegral_const, ← lintegral_add_right _ hmeas]
    refine setLIntegral_mono' hA fun x hx ↦ ?_
    have hx0 : ‖u x‖ₑ ≠ 0 := ENNReal.coe_ne_zero.2 (nnNorm_ne_zero_iff.2 (huA x hx))
    calc k = k * ‖u x‖ₑ * ‖u x‖ₑ⁻¹ := by
          rw [mul_assoc, ENNReal.mul_inv_cancel hx0 eNorm_ne_top, mul_one]
      _ ≤ (ENNReal.ofReal (Φ ‖u x‖) + d) * ‖u x‖ₑ⁻¹ := by
          rw [← ofReal_norm]
          gcongr
          exact hle _ (norm_nonneg _)
      _ = _ := by rw [add_mul, mul_comm d]
  refine ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top hd hm') ?_
  calc _ ≤ k * ν B := hBk
    _ ≤ k * ν A := by gcongr
    _ ≤ _ := hAk
    _ ≤ _ := by gcongr

/-- The coarea formula for the gradient integral `∫ Φ(‖∇g‖)`, as an integral over levels. -/
private theorem lintegral_ofReal_comp_norm_fderiv_eq [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦ0 : Φ 0 ≤ 0) (g : E → ℝ) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ g x‖) =
      ∫⁻ t, ∫⁻ x in {x | fderiv ℝ g x ≠ 0} ∩ g ⁻¹' {t},
        ENNReal.ofReal (Φ ‖fderiv ℝ g x‖) * ‖fderiv ℝ g x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1] := by
  classical
  -- A measurable function agreeing with `ENNReal.ofReal ∘ Φ` on `[0, ∞)`.
  set G : ℝ → ℝ≥0∞ := (Ioi 0).piecewise (fun s ↦ ENNReal.ofReal (Φ s)) 0
  have hG (s : ℝ) (hs : 0 ≤ s) : G s = ENNReal.ofReal (Φ s) := by
    rcases hs.eq_or_lt with rfl | hs
    · simp [G, ENNReal.ofReal_eq_zero.2 hΦ0]
    · exact piecewise_eq_of_mem _ _ _ hs
  have hGm : Measurable G := by
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const measurableSet_Ioi
    have hcont := hΦ.continuousOn_interior
    rw [interior_Ici] at hcont
    exact ENNReal.continuous_ofReal.comp_continuousOn hcont
  have h := lintegral_comp_norm_fderiv_eq_lintegral_setLIntegral (h := g) hGm
    ((hG 0 le_rfl).trans (ENNReal.ofReal_eq_zero.2 hΦ0))
  simp_rw [hG _ (norm_nonneg _)] at h
  exact h

/-- **The area comparison.** For a Lipschitz `h` whose positive superlevel sets have finite volume
and its real Schwarz rearrangement `h*`, at almost every level `t > 0` the regular part
`{h* = t} ∩ {∇h* ≠ 0}` of the level surface of `h*` has at most the area `Hⁿ⁻¹` of the regular part
of the level surface of `h`. -/
private theorem ae_euclideanHausdorffMeasure_regularLevel_le [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E] {K : ℝ≥0} {h : E → ℝ}
    (hh : LipschitzWith K h) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞) :
    ∀ᵐ t, 0 < t →
      μHE[finrank ℝ E - 1] ({x | fderiv ℝ (fun z ↦ (schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x ≠ 0} ∩
          (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) ⁻¹' {t})
        ≤ μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}) := by
  set f : E → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (h y)
  set w : E → ℝ := fun z ↦ (schwarzRearrangement volume f z).toReal
  have hfS := hh.schwarzRearrangement_ofReal_ne_top volume (hfin 1 one_pos)
  have hcrit := hh.ae_euclideanHausdorffMeasure_setOf_fderiv_eq_zero_inter_preimage_eq_zero
    volume (by simpa using Nat.one_le_iff_ne_zero.2 (finrank_pos (R := ℝ) (M := E)).ne')
  -- Almost every level surface carries the perimeter of its superlevel set.
  filter_upwards [(lipschitzWith_toReal_schwarzRearrangement volume
      hh).locallyLipschitz.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure ⊤,
    hh.locallyLipschitz.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure ⊤, hcrit]
    with t hPw hPh hcrit ht
  rw [finrank_self] at hcrit
  simp only [TopologicalSpace.Opens.coe_top, univ_inter] at hPw hPh
  -- The superlevel sets of `w` are the rearranged superlevel sets of `h`.
  have hset : {x | t < w x} = {x | ENNReal.ofReal t < schwarzRearrangement volume f x} := by
    ext x
    exact (ENNReal.ofReal_lt_iff_lt_toReal ht.le (hfS x)).symm
  have hsource : {x | ENNReal.ofReal t < f x} = {x | t < h x} := by
    ext x
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le
  have hper : perimeter volume ⊤ {x | t < w x} ≤ perimeter volume ⊤ {x | t < h x} := by
    have hs : NullMeasurableSet {x | ENNReal.ofReal t < f x} := nullMeasurableSet_lt
      aemeasurable_const hh.continuous.measurable.ennreal_ofReal.aemeasurable
    rw [hset, ← hsource]
    exact hs.perimeter_setOf_lt_schwarzRearrangement_le
  -- The critical part of the level surface of `h` is null.
  calc _ ≤ μHE[finrank ℝ E - 1] (w ⁻¹' {t}) := measure_mono inter_subset_right
    _ ≤ μHE[finrank ℝ E - 1] (h ⁻¹' {t}) := by rw [← hPw, ← hPh]; exact hper
    _ ≤ μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}) +
        μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x = 0} ∩ h ⁻¹' {t}) := by
      refine (measure_mono fun x hx ↦ ?_).trans (measure_union_le _ _)
      by_cases hx0 : fderiv ℝ h x = 0
      · exact Or.inr ⟨hx0, hx⟩
      · exact Or.inl ⟨hx0, hx⟩
    _ = _ := by rw [hcrit, add_zero]

/-- **The level comparison.** For a Lipschitz `h` whose positive superlevel sets have finite volume
and its real Schwarz rearrangement `h*`, at almost every level `t > 0` the contribution
`∫_{{h* = t} ∩ {∇h* ≠ 0}} Φ(‖∇h*‖) ‖∇h*‖⁻¹ dHⁿ⁻¹` of that level to `∫ Φ(‖∇h*‖)` is at most the
corresponding contribution for `h`. -/
private theorem ae_setLIntegral_ofReal_comp_norm_fderiv_toReal_schwarzRearrangement_le
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] {K : ℝ≥0}
    {h : E → ℝ} (hh : LipschitzWith K h) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦ0 : Φ 0 ≤ 0) :
    ∀ᵐ t, 0 < t →
      ∫⁻ x in {x | fderiv ℝ (fun z ↦ (schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x ≠ 0} ∩
          (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) ⁻¹' {t},
        ENNReal.ofReal (Φ ‖fderiv ℝ (fun z ↦ (schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) *
        ‖fderiv ℝ (fun z ↦ (schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1] ≤
      ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t},
        ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) * ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1] := by
  have hfS := hh.schwarzRearrangement_ofReal_ne_top volume (hfin 1 one_pos)
  -- The rearrangement is radially nonincreasing, so its gradient norm is constant on each level.
  have hanti (x y : E) (hxy : ‖x‖ ≤ ‖y‖) :
      (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) y).toReal ≤
        (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) x).toReal :=
    ENNReal.toReal_mono (hfS x) (schwarzRearrangement_le_of_norm_le volume _ hxy)
  -- The level integrals of `‖∇h‖⁻¹` compare through the distribution function.
  filter_upwards [MeasureTheory.ae_setLIntegral_inv_enorm_fderiv_le_ofReal_neg_deriv hfin,
    hh.ae_setLIntegral_inv_enorm_fderiv_toReal_schwarzRearrangement_eq_ofReal_neg_deriv hfin,
    ae_euclideanHausdorffMeasure_regularLevel_le hh hfin] with t hm hm' hP ht
  have hmeas {g : E → ℝ} : MeasurableSet ({x | fderiv ℝ g x ≠ 0} ∩ g ⁻¹' {t}) := by
    rw [inter_comm]
    exact measurableSet_preimage_inter_setOf_fderiv_ne_zero (measurableSet_singleton t)
  refine setLIntegral_ofReal_mul_inv_le hΦ hΦ0 hmeas hmeas (measurable_fderiv ℝ h)
    (fun x hx ↦ hx.1) (fun x hx ↦ hx.1) (fun x hx y hy ↦ ?_) (hP ht)
    ((hm ht).trans (hm' ht).ge) ((hm' ht).trans_ne ENNReal.ofReal_ne_top)
  exact norm_fderiv_eq_of_antitone_norm hanti hx.1 hy.1 (hx.2.trans hy.2.symm)

end TauCeti

namespace LipschitzWith

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {K : ℝ≥0} {h : E → ℝ}

/-- **The Pólya–Szegő inequality for Lipschitz functions.** Let `h` be Lipschitz with superlevel
sets `{h > t}` of finite volume for `t > 0`, and let `h*` be the real Schwarz rearrangement of its
positive part. For every convex `Φ` on `[0, ∞)` with `Φ 0 ≤ 0`,

`∫ Φ(‖∇h*‖) ≤ ∫ Φ(‖∇h‖)`,

where both sides are extended integrals of the positive part of `Φ`, finite or infinite. The
gradients are the totalized Fréchet derivatives. -/
theorem lintegral_ofReal_comp_norm_fderiv_toReal_schwarzRearrangement_le (hh : LipschitzWith K h)
    (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞) {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ)
    (hΦ0 : Φ 0 ≤ 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ (fun z ↦ (schwarzRearrangement volume
        (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In the zero space every derivative vanishes, and `Φ 0 ≤ 0`.
    have hzero (g : E → ℝ) (x : E) : fderiv ℝ g x = 0 :=
      ContinuousLinearMap.ext fun v ↦ by rw [Subsingleton.elim v 0, map_zero, map_zero]
    simp [hzero, ENNReal.ofReal_eq_zero.2 hΦ0]
  rw [lintegral_ofReal_comp_norm_fderiv_eq hΦ hΦ0, lintegral_ofReal_comp_norm_fderiv_eq hΦ hΦ0]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_setLIntegral_ofReal_comp_norm_fderiv_toReal_schwarzRearrangement_le hh hfin
    hΦ hΦ0, volume.ae_ne (0 : ℝ)] with t ht ht0
  rcases lt_or_gt_of_ne ht0 with htneg | htpos
  · -- The rearrangement is nonnegative, so its negative levels are empty.
    have hempty : (fun z ↦ (schwarzRearrangement volume
        (fun y ↦ ENNReal.ofReal (h y)) z).toReal) ⁻¹' {t} = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ (htneg.trans_le ENNReal.toReal_nonneg).ne' hx
    simp [hempty]
  · exact ht htpos

/-- **`L¹` comparison of gradients under rearrangement.** Let `h` be Lipschitz with superlevel
sets `{h > t}` of finite volume for `t > 0`, and let `h*` be the real Schwarz rearrangement of its
positive part. Then `∫ ‖∇h*‖ ≤ ∫ ‖∇h‖`, as extended integrals. -/
theorem lintegral_enorm_fderiv_toReal_schwarzRearrangement_le (hh : LipschitzWith K h)
    (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞) :
    ∫⁻ x, ‖fderiv ℝ (fun z ↦ (schwarzRearrangement volume
        (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖ₑ ≤ ∫⁻ x, ‖fderiv ℝ h x‖ₑ := by
  simpa only [id, ofReal_norm] using
    hh.lintegral_ofReal_comp_norm_fderiv_toReal_schwarzRearrangement_le hfin
      (convexOn_id (convex_Ici 0)) le_rfl

end LipschitzWith
