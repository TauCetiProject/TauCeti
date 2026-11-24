/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann
public import TauCeti.Analysis.Complex.Wirtinger.InteriorEstimate
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Density
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

/-!
# The elliptic estimate for smooth real Cauchy–Riemann operators on closed surfaces

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre, smooth as a real vector bundle, with a finite bundle atlas `A` (so
`M` is compact). Let `D` be a smooth real Cauchy–Riemann operator on `V` and `1 < p < ∞`. This
file proves the elliptic estimate

`‖ξ‖_{W^{1,p}} ≤ C (‖D ξ‖_{Lᵖ} + ‖ξ‖_{Lᵖ})`

for every `ξ ∈ W^{1,p}(Σ, V)`, where `D ξ` is the bounded realization
`TauCeti.IsRealCauchyRiemannOperator.sobolevL : W^{1,p}(Σ, V) → L^p(Σ, Λ^{0,1} ⊗ V)` and
`‖ξ‖_{Lᵖ}` is the norm of `ξ` in `W^{0,p}(Σ, V)`
(`TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_sobolevL_add_norm`). The `Lᵖ` term
cannot be dropped: a nonzero element of the kernel of `D`, such as a constant function for `∂bar`
on the trivial line bundle, has `D ξ = 0`.

## The argument

Choose a smooth partition of unity `χᵢ` subordinate to the chart domains of `A`, and smooth
cutoffs `ψᵢ` equal to one on the support of `χᵢ` with support inside the domain of chart `i`.
Then `ξ = ∑ᵢ χᵢ ξ`, and `χᵢ ξ = ψᵢ (χᵢ ξ)` is controlled in `W^{1,p}(Σ, V)` by its chart-`i`
components (`TauCeti.SobolevSection.exists_norm_contMDiffSMulL_le`). Each chart-`i` component is
controlled by the `Lᵖ` norms of the chart data and of their weak derivative
(`TauCeti.SectionChartData.norm_le_mul_norm_chartValueL_add_norm_chartDerivL`).

For a smooth section `s`, the reading of `χᵢ s` in chart `i` is `χ' u`, where `u` is the reading
of `s` and `χ'` that of `χᵢ`. The set `K` of points of the chart image where `χ'` can be nonzero
is compact, and the product rule bounds the derivative of `χ' u` by that of `u` on `K` and by
`u` itself. In the chart, `D s` reads as `\bar∂u + Zᵢ u` for a zeroth-order term `Zᵢ` bounded on
the chart image, so the interior estimate for `\bar∂`
(`TauCeti.exists_eLpNorm_fderiv_le_of_norm_sub_complexAntilinearPartL_le`, from
`TauCeti.exists_eLpNorm_fderiv_le_of_norm_sub_conjWirtingerDeriv_le`) bounds the derivative of `u`
on `K` by the readings of `D s` and `s` on the chart image
(`TauCeti.IsRealCauchyRiemannOperator.exists_eLpNorm_coord_smul_add_eLpNorm_fderiv_le`).

Both sides of the estimate are continuous on `W^{1,p}(Σ, V)`, and smooth sections are dense there
for finite `p` (`TauCeti.SobolevSection.dense_ofContMDiffSection_contMDiff`), so the estimate
extends from smooth sections to all of `W^{1,p}(Σ, V)`.

## Main results

* `TauCeti.exists_eLpNorm_fderiv_le_of_norm_sub_complexAntilinearPartL_le`: the interior `Lᵖ`
  estimate for `\bar∂` plus a bounded zeroth-order term, for maps into a finite-dimensional complex
  normed space.
* `TauCeti.SectionChartData.norm_le_mul_norm_chartValueL_add_norm_chartDerivL`: the `W^{1,p}` norm
  of a chart component of an order-one tuple is controlled by the chart data and their weak
  derivative.
* `TauCeti.IsRealCauchyRiemannOperator.exists_eLpNorm_coord_smul_add_eLpNorm_fderiv_le`: the
  estimate in one chart, for smooth sections cut off inside the chart domain.
* `TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_sobolevL_add_norm`: the elliptic
  estimate on `W^{1,p}(Σ, V)`.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open ContinuousLinearMap (complexAntilinearPartL complexAntilinearPartL_apply_apply)
open scoped Manifold ENNReal NNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

section Local

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The derivative of `e ∘ u` for a complex-linear isomorphism `e`. -/
private theorem fderiv_comp_continuousLinearEquiv (e : F ≃L[ℂ] G) (u : ℂ → F) (z : ℂ) :
    fderiv ℝ (fun y ↦ e (u y)) z =
      ((e : F →L[ℂ] G).restrictScalars ℝ).comp (fderiv ℝ u z) :=
  (ContinuousLinearEquiv.ofContinuousLinearMap ((e : F →L[ℂ] G).restrictScalars ℝ)
    ((e.symm : G →L[ℂ] F).restrictScalars ℝ) (by ext; simp) (by ext; simp)).comp_fderiv

/-- The conjugate Wirtinger derivative of `e ∘ u` is `e` applied to `\bar∂u` at `1`. -/
private theorem conjWirtingerDeriv_comp_continuousLinearEquiv_one (e : F ≃L[ℂ] G) (u : ℂ → F)
    (z : ℂ) : conjWirtingerDeriv (fun y ↦ e (u y)) z 1 =
      e (complexAntilinearPartL (fderiv ℝ u z) 1) := by
  rw [conjWirtingerDeriv_apply, fderiv_comp_continuousLinearEquiv,
    complexAntilinearPartL_apply_apply]
  simp only [ContinuousLinearMap.comp_apply, smul_eq_mul, mul_one]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, map_add, map_smul]
  push_cast
  rfl

/-- The derivative of `u` is bounded by `‖e⁻¹‖` times that of `e ∘ u`. -/
private theorem norm_fderiv_le_of_continuousLinearEquiv (e : F ≃L[ℂ] G) (u : ℂ → F) (z : ℂ) :
    ‖fderiv ℝ u z‖ ≤ ‖(e.symm : G →L[ℂ] F)‖ * ‖fderiv ℝ (fun y ↦ e (u y)) z‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  calc ‖fderiv ℝ u z v‖ = ‖e.symm (fderiv ℝ (fun y ↦ e (u y)) z v)‖ := by
        simp [fderiv_comp_continuousLinearEquiv]
    _ ≤ ‖(e.symm : G →L[ℂ] F)‖ * ‖fderiv ℝ (fun y ↦ e (u y)) z v‖ :=
        (e.symm : G →L[ℂ] F).le_opNorm _
    _ ≤ ‖(e.symm : G →L[ℂ] F)‖ * (‖fderiv ℝ (fun y ↦ e (u y)) z‖ * ‖v‖) := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖(e.symm : G →L[ℂ] F)‖ * ‖fderiv ℝ (fun y ↦ e (u y)) z‖ * ‖v‖ := by ring

/-- A pointwise bound `‖g - \bar∂u‖ ≤ M ‖u‖` transported along a complex-linear isomorphism `e`,
with `\bar∂(e ∘ u)` written as a conjugate Wirtinger derivative. -/
private theorem norm_sub_conjWirtingerDeriv_comp_le (e : F ≃L[ℂ] G) {u : ℂ → F}
    {g : ℂ →L[ℝ] F} {M : ℝ≥0} {z : ℂ}
    (hg : ‖g - complexAntilinearPartL (fderiv ℝ u z)‖ ≤ M * ‖u z‖) :
    ‖e (g 1) - conjWirtingerDeriv (fun y ↦ e (u y)) z 1‖ ≤
      ‖(e : F →L[ℂ] G)‖ * M * ‖(e.symm : G →L[ℂ] F)‖ * ‖e (u z)‖ := by
  rw [conjWirtingerDeriv_comp_continuousLinearEquiv_one, ← map_sub]
  calc ‖e (g 1 - complexAntilinearPartL (fderiv ℝ u z) 1)‖
      ≤ ‖(e : F →L[ℂ] G)‖ * ‖(g - complexAntilinearPartL (fderiv ℝ u z)) 1‖ :=
        (e : F →L[ℂ] G).le_opNorm _
    _ ≤ ‖(e : F →L[ℂ] G)‖ * (M * ‖e.symm (e (u z))‖) := by
        gcongr
        simpa using ((g - complexAntilinearPartL (fderiv ℝ u z)).le_opNorm 1).trans
          (by simpa using hg)
    _ ≤ ‖(e : F →L[ℂ] G)‖ * (M * (‖(e.symm : G →L[ℂ] F)‖ * ‖e (u z)‖)) := by
        gcongr
        exact (e.symm : G →L[ℂ] F).le_opNorm _
    _ = ‖(e : F →L[ℂ] G)‖ * M * ‖(e.symm : G →L[ℂ] F)‖ * ‖e (u z)‖ := by ring

variable [FiniteDimensional ℝ F]

/-- **The interior `Lᵖ` estimate for `\bar∂` plus a zeroth-order term, with finite-dimensional
values.** For `1 < p < ∞`, `U ⊆ ℂ` open, `K ⊆ U` compact and `M ≥ 0` there is a constant `C` such
that every map `u` smooth on `U`, with values in a finite-dimensional complex normed space, and
every field `g` of real-linear maps with `‖g - \bar∂u‖ ≤ M ‖u‖` on `U` satisfy
`‖Du‖_{Lᵖ(K)} ≤ C (‖g‖_{Lᵖ(U)} + ‖u‖_{Lᵖ(U)})`. Here `\bar∂u` is the complex-antilinear part
`complexAntilinearPartL (fderiv ℝ u z)` of the derivative, a `(0,1)`-form, and the real structure of
the values is any one compatible with the complex structure. This is
`TauCeti.exists_eLpNorm_fderiv_le_of_norm_sub_conjWirtingerDeriv_le`, transported along a complex
linear isomorphism with a Euclidean space. -/
theorem exists_eLpNorm_fderiv_le_of_norm_sub_complexAntilinearPartL_le {p : ℝ≥0∞} (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (M : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (u : ℂ → F) (g : ℂ → ℂ →L[ℝ] F), ContDiffOn ℝ ∞ u U →
      (∀ z ∈ U, ‖g z - complexAntilinearPartL (fderiv ℝ u z)‖ ≤ M * ‖u z‖) →
      eLpNorm (fderiv ℝ u) p (volume.restrict K) ≤
        C * (eLpNorm g p (volume.restrict U) + eLpNorm u p (volume.restrict U)) := by
  have : FiniteDimensional ℂ F := Module.Finite.of_restrictScalars_finite ℝ ℂ F
  let Eu := EuclideanSpace ℂ (Fin (finrank ℂ F))
  let e : F ≃L[ℂ] Eu := .ofFinrankEq (by simp [Eu])
  set a : ℝ≥0 := ‖(e : F →L[ℂ] Eu)‖₊ + 1
  set b : ℝ≥0 := ‖(e.symm : Eu →L[ℂ] F)‖₊ + 1
  have ha (x : F) : ‖e x‖₊ ≤ a * ‖x‖₊ :=
    ((e : F →L[ℂ] Eu).le_opNNNorm x).trans (by gcongr; simp [a])
  obtain ⟨δ, -, hδ⟩ := exists_eLpNorm_fderiv_le_of_norm_sub_conjWirtingerDeriv_le (F := Eu) hp
    hp_top
  obtain ⟨C, hC⟩ := hδ hU hK hKU (a * M * b)
  refine ⟨b * (C + 1) * a, fun u g hu hg ↦ ?_⟩
  -- A nonmeasurable `g` has infinite `Lᵖ` norm, and there is nothing to prove.
  by_cases hgm : AEStronglyMeasurable g (volume.restrict U)
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hgm, top_add, ENNReal.mul_top (by positivity)]
    exact le_top
  have hCe := hC (fun y ↦ e (u y)) (fun z ↦ e (g z 1))
    (((e : F →L[ℂ] Eu).restrictScalars ℝ).contDiff.comp_contDiffOn hu) fun z hz ↦
      (norm_sub_conjWirtingerDeriv_comp_le e (hg z hz)).trans
        (le_add_of_nonneg_of_le (by positivity) (by push_cast; gcongr <;> simp [a, b]))
  have h₁ : eLpNorm (fderiv ℝ u) p (volume.restrict K) ≤
      b * eLpNorm (fderiv ℝ fun y ↦ e (u y)) p (volume.restrict K) :=
    (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (c := b)
      (g := fderiv ℝ fun y ↦ e (u y)) (measurable_fderiv ℝ u).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z ↦ by
        rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnNorm, coe_nnNorm]
        exact (norm_fderiv_le_of_continuousLinearEquiv e u z).trans (by gcongr; simp [b])) p
      ).trans_eq (by rw [ENNReal.smul_def, smul_eq_mul])
  have h₂ : eLpNorm (fun z ↦ e (g z 1)) p (volume.restrict U) ≤
      a * eLpNorm g p (volume.restrict U) :=
    (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (f := fun z ↦ e (g z 1)) (g := g) (c := a)
      ((e.continuous.comp (ContinuousLinearMap.apply ℝ F (1 : ℂ)).continuous
        ).comp_aestronglyMeasurable hgm) (Filter.Eventually.of_forall fun z ↦
          (ha _).trans (by gcongr; simpa using (g z).le_opNNNorm 1)) p).trans_eq
      (by rw [ENNReal.smul_def, smul_eq_mul])
  have h₃ : eLpNorm (fun z ↦ e (u z)) p (volume.restrict U) ≤
      a * eLpNorm u p (volume.restrict U) :=
    (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (f := fun z ↦ e (u z)) (g := u) (c := a)
      (e.continuous.comp_aestronglyMeasurable
      (hu.continuousOn.aestronglyMeasurable hU.measurableSet))
      (Filter.Eventually.of_forall fun z ↦ ha _) p).trans_eq
      (by rw [ENNReal.smul_def, smul_eq_mul])
  calc eLpNorm (fderiv ℝ u) p (volume.restrict K)
      ≤ b * (C * (a * eLpNorm g p (volume.restrict U) + a * eLpNorm u p (volume.restrict U))) :=
        h₁.trans (by gcongr; exact hCe.trans (by gcongr))
    _ ≤ b * ((C + 1) * (a * eLpNorm g p (volume.restrict U) +
          a * eLpNorm u p (volume.restrict U))) := by gcongr; exact_mod_cast le_self_add
    _ = ((b * (C + 1) * a : ℝ≥0) : ℝ≥0∞) *
          (eLpNorm g p (volume.restrict U) + eLpNorm u p (volume.restrict U)) := by
        push_cast
        ring

end Local

section ChartDeriv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {S : Type*} [AddCommGroup S] [Module ℝ S] (C : SectionChartData E F S)
  (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)]

namespace SectionChartData

/-- **The components are controlled by the chart data and their derivative.** The `W^{1,p}` norm of
the `j`-th chart-`i` component of an order-one tuple is at most the norm of the `j`-th coordinate
functional of `Module.finBasis ℝ F` times the sum of the `Lᵖ` norms of the chart data and of their
weak derivative. -/
theorem norm_le_mul_norm_chartValueL_add_norm_chartDerivL (i : Fin C.n)
    (w : C.SobolevData μ p 1) (j : Fin (finrank ℝ F)) :
    ‖w i j‖ ≤ ‖LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord j)‖ *
      (‖C.chartValueL μ p 1 i w‖ + ‖C.chartDerivL μ p i w‖) := by
  set c := LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord j)
  have hv : ‖W1p.value (w i j)‖ ≤ ‖c‖ * ‖C.chartValueL μ p 1 i w‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [C.chartValueL_apply_ae μ p 1 i w] with y hy
    have : c (C.chartValueL μ p 1 i w y) = W1p.value (w i j) y := by
      rw [hy]
      simp [c, Finsupp.single_apply]
    rw [← this]
    exact c.le_opNorm _
  have hg : ‖W1p.gradient (w i j)‖ ≤ ‖c‖ * ‖C.chartDerivL μ p i w‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [C.chartDerivL_apply_ae μ p i w] with y hy
    have : c.comp (C.chartDerivL μ p i w y) = innerSL ℝ (W1p.gradient (w i j) y) := by
      rw [hy]
      ext v
      simp [c, Finsupp.single_apply]
    rw [← innerSL_apply_norm ℝ, ← this]
    exact c.opNorm_comp_le _
  calc ‖w i j‖ ≤ ‖W1p.value (w i j)‖ + ‖W1p.gradient (w i j)‖ :=
        W1p.norm_le_norm_value_add_norm_gradient _
    _ ≤ ‖c‖ * (‖C.chartValueL μ p 1 i w‖ + ‖C.chartDerivL μ p i w‖) := by
        rw [mul_add]
        exact add_le_add hv hg

end SectionChartData

end ChartDeriv

section Cutoff

/-! ### Products with a cutoff on an open subset of the plane -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If `v = χ u` on an open set `U ⊆ ℂ` with `|χ| ≤ B` on `U`, then
`‖v‖_{Lᵖ(U)} ≤ B ‖u‖_{Lᵖ(U)}`. -/
private theorem eLpNorm_le_of_eqOn_smul {p : ℝ≥0∞} {U : Set ℂ} (hU : IsOpen U) {u v : ℂ → F}
    {χ : ℂ → ℝ} (hu : ContDiffOn ℝ 1 u U) (hχ : ContDiffOn ℝ 1 χ U)
    (hv : EqOn v (fun y ↦ χ y • u y) U) {B : ℝ≥0} (hB : ∀ z ∈ U, |χ z| ≤ B) :
    eLpNorm v p (volume.restrict U) ≤ B * eLpNorm u p (volume.restrict U) := by
  have hUm := hU.measurableSet
  refine (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (((hχ.continuousOn.aestronglyMeasurable hUm).smul
      (hu.continuousOn.aestronglyMeasurable hUm)).congr
        ((ae_restrict_mem hUm).mono fun y hy ↦ (hv hy).symm)) ?_ p).trans_eq
    (by rw [ENNReal.smul_def, smul_eq_mul])
  filter_upwards [ae_restrict_mem hUm] with z hz
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnNorm, coe_nnNorm, hv hz, norm_smul,
    Real.norm_eq_abs]
  gcongr
  exact hB z hz

variable [FiniteDimensional ℝ F]

/-- **The product rule estimate for a cutoff.** Let `v = χ u` on an open set `U ⊆ ℂ`, with `u` and
`χ` of class `C¹` on `U`, `|χ| ≤ B` and `‖Dχ‖ ≤ L` on `U`, and `χ = 0` on `U` off a measurable
subset `K ⊆ U`. Then `‖Dv‖_{Lᵖ(U)} ≤ B ‖Du‖_{Lᵖ(K)} + L ‖u‖_{Lᵖ(U)}`. -/
private theorem eLpNorm_fderiv_le_of_eqOn_smul {p : ℝ≥0∞} (hp : 1 ≤ p) {U K : Set ℂ}
    (hU : IsOpen U) (hK : MeasurableSet K) (hKU : K ⊆ U) {u v : ℂ → F} {χ : ℂ → ℝ}
    (hu : ContDiffOn ℝ 1 u U) (hχ : ContDiffOn ℝ 1 χ U) (hv : EqOn v (fun y ↦ χ y • u y) U)
    {B L : ℝ≥0} (hB : ∀ z ∈ U, |χ z| ≤ B) (hL : ∀ z ∈ U, ‖fderiv ℝ χ z‖ ≤ L)
    (hχK : ∀ z ∈ U, z ∉ K → χ z = 0) :
    eLpNorm (fderiv ℝ v) p (volume.restrict U) ≤
      B * eLpNorm (fderiv ℝ u) p (volume.restrict K) + L * eLpNorm u p (volume.restrict U) := by
  have hUm := hU.measurableSet
  have hχm : AEStronglyMeasurable χ (volume.restrict U) :=
    hχ.continuousOn.aestronglyMeasurable hUm
  have hum : AEStronglyMeasurable u (volume.restrict U) :=
    hu.continuousOn.aestronglyMeasurable hUm
  have h₁ : eLpNorm (fun z ↦ χ z • fderiv ℝ u z) p (volume.restrict U) ≤
      B * eLpNorm (fderiv ℝ u) p (volume.restrict K) := by
    rw [← Measure.restrict_restrict_of_subset hKU,
      ← eLpNorm_indicator_eq_eLpNorm_restrict hK.nullMeasurableSet]
    refine (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      (hχm.smul (measurable_fderiv ℝ u).aestronglyMeasurable) ?_ p).trans_eq
      (by rw [ENNReal.smul_def, smul_eq_mul])
    filter_upwards [ae_restrict_mem hUm] with z hz
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnNorm, coe_nnNorm]
    by_cases hzK : z ∈ K
    · rw [indicator_of_mem hzK, Pi.smul_apply', norm_smul, Real.norm_eq_abs]
      gcongr
      exact hB z hz
    · rw [Pi.smul_apply', hχK z hz hzK, zero_smul, norm_zero]
      positivity
  have h₂ : eLpNorm (fun z ↦ (fderiv ℝ χ z).smulRight (u z)) p (volume.restrict U) ≤
      L * eLpNorm u p (volume.restrict U) := by
    refine (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul ?_ ?_ p).trans_eq
      (by rw [ENNReal.smul_def, smul_eq_mul])
    · simpa using (StrongDual.smulRightL ℝ ℂ F).aestronglyMeasurable_comp₂
        (measurable_fderiv ℝ χ).aestronglyMeasurable hum
    filter_upwards [ae_restrict_mem hUm] with z hz
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnNorm, coe_nnNorm,
      ContinuousLinearMap.norm_smulRight_apply]
    gcongr
    exact hL z hz
  -- On `U`, the derivative of `v` is `χ Du + Dχ ⊗ u`.
  have hdv : fderiv ℝ v =ᵐ[volume.restrict U]
      (fun z ↦ χ z • fderiv ℝ u z) + fun z ↦ (fderiv ℝ χ z).smulRight (u z) := by
    filter_upwards [ae_restrict_mem hUm] with z hz
    rw [Filter.EventuallyEq.fderiv_eq (hv.eventuallyEq_of_mem (hU.mem_nhds hz))]
    exact fderiv_smul ((hχ.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hz))
      ((hu.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hz))
  exact (eLpNorm_congr_ae hdv).trans_le ((eLpNorm_add_le hp).trans (add_le_add h₁ h₂))

end Cutoff

section ChartBound

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  {F : Type*} [TopologicalSpace F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] (A : FiniteBundleAtlas ℂ M F V)

/-- A smooth function on `M`, read in chart `i`, is bounded and has bounded derivative on the
image of the chart. -/
private theorem FiniteBundleAtlas.exists_bound_comp_chart_symm {χ : M → ℝ}
    (hχ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ χ) (i : Fin A.n) :
    ∃ B L : ℝ≥0, ∀ z ∈ (A.image i : Set ℂ), |χ ((A.chart i).symm z)| ≤ B ∧
      ‖fderiv ℝ (fun y ↦ χ ((A.chart i).symm y)) z‖ ≤ L := by
  have hχ' := A.contDiffOn_comp_chart_symm hχ i
  have hcl := A.closure_image_subset_target i
  obtain ⟨B, hB⟩ :=
    (A.isCompact_closure_image i).exists_bound_of_continuousOn (hχ'.continuousOn.mono hcl)
  obtain ⟨L, hL⟩ := (A.isCompact_closure_image i).exists_bound_of_continuousOn
    ((hχ'.continuousOn_fderiv_of_isOpen (A.chart i).open_target (by simp)).mono hcl)
  refine ⟨B.toNNReal, L.toNNReal, fun z hz ↦
    ⟨?_, (hL z (subset_closure hz)).trans (Real.le_coe_toNNReal _)⟩⟩
  have h := hB z (subset_closure hz)
  rw [Real.norm_eq_abs] at h
  exact h.trans (Real.le_coe_toNNReal _)

end ChartBound

section Global

open SmoothAlmostComplexStructure FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealCauchyRiemannEstimate : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace IsRealCauchyRiemannOperator

include hD hDs in
/-- The zeroth-order term of a smooth real Cauchy–Riemann operator in chart `i` is bounded on the
image of the chart. -/
private theorem exists_bound_chartZeroOrder (i : Fin A.n) :
    ∃ Z : ℝ≥0, ∀ z ∈ (A.image i : Set ℂ), ‖A.chartZeroOrder D i z‖ ≤ Z := by
  have hZc : ContinuousOn (A.chartZeroOrder D i) (closure (A.image i : Set ℂ)) := by
    refine (A.contDiffOn_chartZeroOrder hD hDs isOpen_univ i).continuousOn.mono ?_
    simpa only [inter_univ] using (A.closure_image_subset_chart_image_closure_dom i).trans
      (A.chart_image_closure_dom_subset i)
  obtain ⟨Z, hZ⟩ :=
    (A.isCompact_closure_image i).exists_bound_of_continuousOn (f := A.chartZeroOrder D i) hZc
  exact ⟨Z.toNNReal, fun z hz ↦ (hZ z (subset_closure hz)).trans (Real.le_coe_toNNReal _)⟩

include hD hDs in
/-- **The elliptic estimate in a chart.** Let `χ` be a smooth function whose support has closure
in the domain of chart `i`. For `1 < p < ∞` there is a constant `C` such that the reading `v` of
`χ s` in chart `i`, for every smooth section `s`, satisfies
`‖v‖_{Lᵖ} + ‖Dv‖_{Lᵖ} ≤ C (‖(D s)ᵢ‖_{Lᵖ} + ‖sᵢ‖_{Lᵖ})` on the image of the chart, where `sᵢ` and
`(D s)ᵢ` are the readings of `s` and `D s`. In chart `i`, `D s` is `\bar∂ sᵢ + Zᵢ sᵢ` for a
zeroth-order term `Zᵢ` bounded on the chart image, and the support of `χ` read in the chart is a
compact subset of the chart image, so this is the interior estimate
`TauCeti.exists_eLpNorm_fderiv_le_of_norm_sub_complexAntilinearPartL_le` together with the product
rule for `χ s`. -/
theorem exists_eLpNorm_coord_smul_add_eLpNorm_fderiv_le (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) {i : Fin A.n} {χ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ χ)
    (hχi : tsupport χ ⊆ A.dom i) :
    ∃ C : ℝ≥0, ∀ s : Π x, V x,
      ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (fun x ↦ TotalSpace.mk' F x (s x)) →
      eLpNorm (A.coord i fun x ↦ χ x • s x) p (volume.restrict (A.image i)) +
          eLpNorm (fderiv ℝ (A.coord i fun x ↦ χ x • s x)) p (volume.restrict (A.image i)) ≤
        C * (eLpNorm (A.tangentHom.coord i (D s)) p (volume.restrict (A.image i)) +
          eLpNorm (A.coord i s) p (volume.restrict (A.image i))) := by
  have := A.compactSpace
  have : ∀ x, ContinuousSMul ℂ (V x) := VectorBundle.continuousSMul ℂ F V
  set U : Set ℂ := (A.image i : Set ℂ)
  have hU : IsOpen U := (A.image i).isOpen
  have hcl : closure U ⊆ (A.chart i).target := A.closure_image_subset_target i
  set K : Set ℂ := A.chart i '' tsupport χ
  have hK : IsCompact K := (isClosed_tsupport χ).isCompact.image_of_continuousOn
    ((A.chart i).continuousOn.mono (hχi.trans (A.dom_subset_chart_source i)))
  have hKU : K ⊆ U := fun y hy ↦ A.mem_image.2 (image_mono hχi hy)
  set χ' : ℂ → ℝ := fun y ↦ χ ((A.chart i).symm y)
  obtain ⟨B, L, hBL⟩ := A.exists_bound_comp_chart_symm hχ i
  obtain ⟨Z, hZ⟩ := exists_bound_chartZeroOrder A hD hDs i
  obtain ⟨C₀, hC₀⟩ := exists_eLpNorm_fderiv_le_of_norm_sub_complexAntilinearPartL_le (F := F) hp
    hp_top hU hK hKU Z
  refine ⟨B * C₀ + L + B, fun s hs ↦ ?_⟩
  set u := A.coord i s
  have hu : ContDiffOn ℝ ∞ u U :=
    ((contDiffOn_trivialization_comp_chart_symm_of_contMDiff hs
      (IsManifold.chart_mem_maximalAtlas _) (A.triv i)).congr fun y _ ↦ A.coord_def i s y).mono
        ((A.image_subset_chart_image_closure_dom i).trans (A.chart_image_closure_dom_subset i))
  -- In chart `i`, `D s` is `\bar∂ u + Zᵢ u`.
  have hDs' := hC₀ u (A.tangentHom.coord i (D s)) hu fun z hz ↦ by
    rw [A.coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder hD hz
      ((hs _).mdifferentiableAt (by simp)), add_sub_cancel_left]
    exact ((A.chartZeroOrder D i z).le_opNorm _).trans (by gcongr; exact hZ z hz)
  -- The reading of `χ s` is `χ' u` on the chart image, and `χ'` vanishes off `K`.
  have hχK : ∀ z ∈ U, z ∉ K → χ' z = 0 := fun z hz hzK ↦ by
    by_contra h
    exact hzK ⟨_, subset_tsupport _ h, (A.chart i).right_inv (hcl (subset_closure hz))⟩
  have hvU : EqOn (A.coord i fun x ↦ χ x • s x) (fun y ↦ χ' y • u y) U :=
    fun y hy ↦ A.coord_fun_smul i χ s hy
  have hχ'U : ContDiffOn ℝ 1 χ' U :=
    ((A.contDiffOn_comp_chart_symm hχ i).mono (subset_closure.trans hcl)).of_le (by simp)
  have h₁ := eLpNorm_le_of_eqOn_smul (p := p) hU (hu.of_le (by simp)) hχ'U hvU
    fun z hz ↦ (hBL z hz).1
  have h₂ := eLpNorm_fderiv_le_of_eqOn_smul (Fact.out : 1 ≤ p) hU hK.measurableSet hKU
    (hu.of_le (by simp)) hχ'U hvU (fun z hz ↦ (hBL z hz).1) (fun z hz ↦ (hBL z hz).2) hχK
  set G := eLpNorm (A.tangentHom.coord i (D s)) p (volume.restrict U)
  set Y := eLpNorm u p (volume.restrict U)
  calc eLpNorm (A.coord i fun x ↦ χ x • s x) p (volume.restrict U) +
        eLpNorm (fderiv ℝ (A.coord i fun x ↦ χ x • s x)) p (volume.restrict U)
      ≤ B * Y + (B * (C₀ * (G + Y)) + L * Y) := add_le_add h₁ (h₂.trans (by gcongr))
    _ ≤ B * (G + Y) + (B * (C₀ * (G + Y)) + L * (G + Y)) := by gcongr <;> exact le_add_self
    _ = ((B * C₀ + L + B : ℝ≥0) : ℝ≥0∞) * (G + Y) := by
        push_cast
        ring

include hD hDs in
/-- The chart estimate
`TauCeti.IsRealCauchyRiemannOperator.exists_eLpNorm_coord_smul_add_eLpNorm_fderiv_le` in terms of
the chart data of the Sobolev sections of a `C¹` section `s` and of `χ s`. -/
private theorem norm_chartValueL_add_norm_chartDerivL_le (s : Cₛ^1⟮𝓘(ℝ, ℂ); F, V⟯) {i : Fin A.n}
    {χ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ χ) {c : ℝ≥0}
    (h : eLpNorm (A.coord i fun x ↦ χ x • s x) p (volume.restrict (A.image i)) +
        eLpNorm (fderiv ℝ (A.coord i fun x ↦ χ x • s x)) p (volume.restrict (A.image i)) ≤
      c * (eLpNorm (A.tangentHom.coord i (D s)) p (volume.restrict (A.image i)) +
        eLpNorm (A.coord i s) p (volume.restrict (A.image i)))) :
    ‖A.sectionChartData.chartValueL volume p 1 i (SobolevSection.contMDiffSMulL A volume p 1 hχ
        (SobolevSection.ofContMDiffSection A volume p 1 s))‖ +
      ‖A.sectionChartData.chartDerivL volume p i (SobolevSection.contMDiffSMulL A volume p 1 hχ
        (SobolevSection.ofContMDiffSection A volume p 1 s))‖ ≤
      c * (‖A.tangentHom.sectionChartData.chartValueL volume p 0 i
          (hD.sobolevL A hDs volume p (SobolevSection.ofContMDiffSection A volume p 1 s) :
            SobolevSection A.tangentHom volume p 0)‖ +
        ‖A.sectionChartData.chartValueL volume p 0 i (A.sectionChartData.lowerOrderL volume p 0
          (SobolevSection.ofContMDiffSection A volume p 1 s))‖) := by
  set w := SobolevSection.ofContMDiffSection A volume p 1 s
  set v := SobolevSection.contMDiffSMulL A volume p 1 hχ w
  have hv := SobolevSection.chartValueL_contMDiffSMulL_ae_coord hχ
    (SobolevSection.chartValueL_ofContMDiffSection_ae A volume p 1 s) i
  have hc : ContDiffOn ℝ 1 (A.coord i fun x ↦ χ x • s x) (A.image i) :=
    (A.contDiffOn_coord ((hχ.of_le (by exact_mod_cast le_top)).smul_section s.contMDiff) i).mono
      ((A.image_subset_chart_image_closure_dom i).trans (A.chart_image_closure_dom_subset i))
  have hd := (A.sectionChartData.hasWeakFDerivOn_chartValueL volume p i v).ae_eq
    ((hc.hasWeakFDerivOn_fderiv (μ := volume) (Ω := A.image i)).congr_ae hv.symm)
  have hu := SobolevSection.chartValueL_ofContMDiffSection_ae A volume p 1 s i
  rw [← A.sectionChartData.chartValueL_coe_lowerOrderL volume p 0 w i] at hu
  have e₁ : eLpNorm (A.sectionChartData.chartValueL volume p 1 i v) p
      (volume.restrict (A.image i)) =
        eLpNorm (A.coord i fun x ↦ χ x • s x) p (volume.restrict (A.image i)) :=
    eLpNorm_congr_ae hv
  have e₂ : eLpNorm (A.sectionChartData.chartDerivL volume p i v) p
      (volume.restrict (A.image i)) =
        eLpNorm (fderiv ℝ (A.coord i fun x ↦ χ x • s x)) p (volume.restrict (A.image i)) :=
    eLpNorm_congr_ae hd
  have e₃ : eLpNorm (A.tangentHom.sectionChartData.chartValueL volume p 0 i
      (hD.sobolevL A hDs volume p w : SobolevSection A.tangentHom volume p 0)) p
      (volume.restrict (A.tangentHom.sectionChartData.image i : Set ℂ)) =
        eLpNorm (A.tangentHom.coord i (D s)) p (volume.restrict (A.image i)) := by
    rw [eLpNorm_congr_ae ((ae_image_tangentHom_iff A volume i).2
      (hD.chartValueL_sobolevL_ofContMDiffSection_ae A hDs volume p s i)),
      sectionChartData_image_tangentHom]
  have hCs := (congrArg₂ (· + ·) e₁ e₂).trans_le (h.trans_eq
    (congrArg₂ (fun a b ↦ (c : ℝ≥0∞) * (a + b)) e₃ (eLpNorm_congr_ae hu)).symm)
  simp only [Lp.norm_def]
  rw [← ENNReal.toReal_add (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _),
    ← ENNReal.toReal_add (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _), ← ENNReal.coe_toReal,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.add_ne_top.2 ⟨Lp.eLpNorm_ne_top _, Lp.eLpNorm_ne_top _⟩)) hCs

include hD hDs in
/-- **The chart estimate in Sobolev norms, for smooth sections.** For a smooth `χ` whose support
has closure in the domain of chart `i`, the chart-`i` components of `χ w`, for the Sobolev section
`w` of a smooth section, are bounded in `W^{1,p}` by a multiple of
`‖D w‖_{Lᵖ} + ‖w‖_{Lᵖ}`. -/
private theorem exists_norm_contMDiffSMulL_component_le (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {i : Fin A.n} {χ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ χ) (hχi : tsupport χ ⊆ A.dom i) :
    ∃ C : ℝ, ∀ s : Cₛ^1⟮𝓘(ℝ, ℂ); F, V⟯,
      ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (fun x ↦ TotalSpace.mk' F x (s x)) →
      ‖(SobolevSection.contMDiffSMulL A volume p 1 hχ
          (SobolevSection.ofContMDiffSection A volume p 1 s) :
            A.sectionChartData.SobolevData volume p 1) i‖ ≤
        C * (‖hD.sobolevL A hDs volume p (SobolevSection.ofContMDiffSection A volume p 1 s)‖ +
          ‖A.sectionChartData.lowerOrderL volume p 0
            (SobolevSection.ofContMDiffSection A volume p 1 s)‖) := by
  obtain ⟨Cc, hCc⟩ := hD.exists_eLpNorm_coord_smul_add_eLpNorm_fderiv_le A hDs hp hp_top hχ hχi
  set cB : ℝ := ∑ j, ‖LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord j)‖
  set T := A.tangentHom.sectionChartData.chartValueL volume p 0 i
  set S := A.sectionChartData.chartValueL volume p 0 i
  refine ⟨cB * (Cc * (‖T‖ + ‖S‖)), fun s hs ↦ ?_⟩
  set w := SobolevSection.ofContMDiffSection A volume p 1 s
  set v := SobolevSection.contMDiffSMulL A volume p 1 hχ w
  have hchart := norm_chartValueL_add_norm_chartDerivL_le A hD hDs s hχ (hCc s hs)
  set X := ‖hD.sobolevL A hDs volume p w‖
  set Y := ‖A.sectionChartData.lowerOrderL volume p 0 w‖
  have hT : ‖T (hD.sobolevL A hDs volume p w : SobolevSection A.tangentHom volume p 0)‖ ≤
      ‖T‖ * X := T.le_opNorm _
  have hS : ‖S (A.sectionChartData.lowerOrderL volume p 0 w)‖ ≤ ‖S‖ * Y := S.le_opNorm _
  have hX : 0 ≤ X := by positivity
  have hY : 0 ≤ Y := by positivity
  calc ‖(v : A.sectionChartData.SobolevData volume p 1) i‖
      ≤ cB * (‖A.sectionChartData.chartValueL volume p 1 i v‖ +
          ‖A.sectionChartData.chartDerivL volume p i v‖) := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j ↦
          (A.sectionChartData.norm_le_mul_norm_chartValueL_add_norm_chartDerivL volume p i v
            j).trans ?_
        gcongr
        exact Finset.single_le_sum (f := fun j ↦
          ‖LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord j)‖)
          (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ j)
    _ ≤ cB * (Cc * ((‖T‖ + ‖S‖) * (X + Y))) := by
        gcongr
        refine hchart.trans ?_
        gcongr
        nlinarith [norm_nonneg T, norm_nonneg S]
    _ = cB * (Cc * (‖T‖ + ‖S‖)) * (X + Y) := by ring

include hD hDs in
/-- **The elliptic estimate for a smooth real Cauchy–Riemann operator on a closed surface.** Let
`D` be a smooth real Cauchy–Riemann operator on a complex vector bundle `V` over a compact
boundaryless complex curve, with a finite bundle atlas `A`, and let `1 < p < ∞`. There is a
constant `C` such that every `ξ ∈ W^{1,p}(Σ, V)` satisfies
`‖ξ‖_{W^{1,p}} ≤ C (‖D ξ‖_{Lᵖ} + ‖ξ‖_{Lᵖ})`, where `D ξ` is the realization
`TauCeti.IsRealCauchyRiemannOperator.sobolevL` and `‖ξ‖_{Lᵖ}` is the norm of `ξ` in
`W^{0,p}(Σ, V)`. -/
theorem exists_norm_le_norm_sobolevL_add_norm (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ, ∀ w : SobolevSection A volume p 1,
      ‖w‖ ≤ C * (‖hD.sobolevL A hDs volume p w‖ +
        ‖A.sectionChartData.lowerOrderL volume p 0 w‖) := by
  have := A.compactSpace
  -- A partition of unity subordinate to the chart domains, and cutoffs equal to one on its
  -- supports.
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ) isClosed_univ A.dom
    A.isOpen_dom (by rw [A.iUnion_dom])
  have hχ1 (x : M) : ∑ i, χ i x = 1 := by
    simpa [finsum_eq_sum_of_fintype] using χ.sum_eq_one (mem_univ x)
  choose ψ hψ _ hψi hψ1 using fun i ↦
    (isClosed_tsupport (χ i)).exists_contMDiff_tsupport_subset_eq_one_iff (I := 𝓘(ℝ, ℂ))
      (A.isOpen_dom i) (hχ i)
  choose Cψ hCψ using fun i ↦
    SobolevSection.exists_norm_contMDiffSMulL_le (μ := volume) (p := p) (k := 1) (hψ i) (hψi i)
  choose Cc hCc using fun i ↦
    exists_norm_contMDiffSMulL_component_le A hD hDs hp hp_top (χ i).contMDiff (hχ i)
  set C := ∑ i, max (Cψ i) 0 * max (Cc i) 0
  refine ⟨C, fun w ↦ ?_⟩
  -- The estimate is a closed condition, so it suffices to prove it on the dense set of smooth
  -- sections.
  have hc₁ : Continuous fun w : SobolevSection A volume p 1 ↦ ‖hD.sobolevL A hDs volume p w‖ :=
    (continuous_norm (E := zeroOneSobolevSections A volume p 0)).comp
      (hD.sobolevL A hDs volume p).continuous
  have hc₂ : Continuous fun w : SobolevSection A volume p 1 ↦
      ‖A.sectionChartData.lowerOrderL volume p 0 w‖ :=
    continuous_norm.comp (A.sectionChartData.lowerOrderL volume p 0).continuous
  have hP : IsClosed {w : SobolevSection A volume p 1 | ‖w‖ ≤ C *
      (‖hD.sobolevL A hDs volume p w‖ + ‖A.sectionChartData.lowerOrderL volume p 0 w‖)} :=
    isClosed_le continuous_norm (continuous_const.mul (hc₁.add hc₂))
  have hdense := SobolevSection.dense_ofContMDiffSection_contMDiff (A := A) (μ := volume)
    (p := p) (k := 1) hp_top
  refine hP.closure_subset_iff.2 ?_ (hdense.closure_eq ▸ mem_univ w)
  rintro _ ⟨s, hs, rfl⟩
  set w := SobolevSection.ofContMDiffSection A volume p 1 s
  set X := ‖hD.sobolevL A hDs volume p w‖ + ‖A.sectionChartData.lowerOrderL volume p 0 w‖
  change ‖w‖ ≤ C * X
  calc ‖w‖ = ‖∑ i, SobolevSection.contMDiffSMulL A volume p 1 (χ i).contMDiff w‖ := by
        rw [SobolevSection.sum_contMDiffSMulL_eq_self_of_sum_eq_one _ hχ1]
    _ ≤ ∑ i, ‖SobolevSection.contMDiffSMulL A volume p 1 (χ i).contMDiff w‖ := norm_sum_le _ _
    _ ≤ ∑ i, max (Cψ i) 0 * max (Cc i) 0 * X := Finset.sum_le_sum fun i _ ↦ ?_
    _ = C * X := by rw [Finset.sum_mul]
  set v := SobolevSection.contMDiffSMulL A volume p 1 (χ i).contMDiff w
  have hvi := hCc i s hs
  calc ‖v‖ = ‖SobolevSection.contMDiffSMulL A volume p 1 (hψ i) v‖ := by
        rw [SobolevSection.contMDiffSMulL_contMDiffSMulL_of_eqOn _ (hψ i) fun _ h ↦ (hψ1 i _).1 h]
    _ ≤ Cψ i * ‖(v : A.sectionChartData.SobolevData volume p 1) i‖ := hCψ i v
    _ ≤ max (Cψ i) 0 * ‖(v : A.sectionChartData.SobolevData volume p 1) i‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max (Cψ i) 0 * (max (Cc i) 0 * X) := by
        gcongr
        exact hvi.trans (by gcongr; exact le_max_left _ _)
    _ = max (Cψ i) 0 * max (Cc i) 0 * X := by ring

end IsRealCauchyRiemannOperator

end Global

end TauCeti
