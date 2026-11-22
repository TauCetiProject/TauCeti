/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Beltrami.Chart
public import TauCeti.Analysis.Holder.Rescaling
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Complex.Conformal.Moebius
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy
import TauCeti.Topology.MetricSpace.Holder

/-!
# Isothermal charts for a Hölder almost complex structure on the plane

Let `J` be a field of almost complex structures on the plane, tame near a point `c`, whose scalar
Beltrami coefficient `μ` is `α`-Hölder near `c` for some `0 < α < 1`. This file proves that `c`
has an *isothermal chart*: a `C¹` open partial homeomorphism `e` of `ℂ`, defined near `c`, with
`α`-Hölder and invertible derivative, in which `J` becomes multiplication by `i`:
`de_z (J z v) = i · de_z v` (`TauCeti.Beltrami.exists_isothermal_chart`). If the field `J`
itself is `C¹` at `c`, the same conclusion holds for every `0 < α < 1`, with no orientation
condition (`TauCeti.Beltrami.exists_isothermal_chart_of_contDiffAt`): if `J` is tame at `c`, its
coefficient is Lipschitz, hence Hölder, near `c`; otherwise the field conjugated by `z ↦ conj z`
is tame at `conj c`. The transition maps between two such charts are holomorphic
(`TauCeti.Beltrami.differentiableOn_symm_trans_of_fderiv_comp`).

No orientation need be assumed either for a field `J` of real-linear endomorphisms of the plane
which is `C¹` near `c` and squares to `-1` there: it has an isothermal chart at `c` which is `C¹`
with `C¹` inverse
(`TauCeti.Beltrami.exists_isothermal_chart_of_contDiffAt_of_sq_eq_neg_one`). Read through the
charts of a surface, these planar charts give the isothermal charts of `TauCeti.IsIsothermalChart`.

The proof is the direct Beltrami argument, assembling three steps proved before.

* **Normalization.** The real-linear map `L = (z ↦ z + a conj z)` with `a = μ(c)` changes the
  coefficient to `ν = (μ - a) / (1 - conj a μ)`
  (`TauCeti.Beltrami.isComplexLinear_comp_linearMap_iff`), which vanishes at `c`. Since `μ`
  stays in a disc of radius less than one near `c`, the Möbius map `t ↦ (t - a) / (1 - conj a t)`
  is Lipschitz there, so `ν` is still `α`-Hölder.
* **Rescaling.** Cut off and rescaled, `w ↦ χ(w) ν(c + L⁻¹(ε w))` has arbitrarily small Hölder
  norm as `ε → 0` (`TauCeti.eventually_exists_holderSpace_cutoff_rescale`), while it agrees with
  the rescaled coefficient on the unit disc, where `χ = 1`.
* **Solution.** For a small coefficient, the Beltrami equation has a solution `ψ` that is
  `C¹`-close to the identity, and its normalization is a chart in which the rescaled structure is
  standard (`TauCeti.Beltrami.exists_isComplexLinear_chart`).

The isothermal chart is the normalized solution composed with `z ↦ ε⁻¹ L(z - c)`.

For a field of either orientation, the normalization is instead a real-linear automorphism `B`
carrying multiplication by `i` to `J c`
(`ContinuousLinearMap.exists_continuousLinearEquiv_comp_eq_comp_I_smul`), followed by the affine
Beltrami normalizer of the coefficient `ν = (i - K 1) / (conj (K 1) - i)` of the conjugated field
`K`, which intertwines `K` with `i` whatever its orientation
(`TauCeti.Beltrami.linearMap_apply_eq_I_mul`).

## Main results

* `TauCeti.Beltrami.exists_isothermal_chart`: a tame field of structures with `α`-Hölder
  Beltrami coefficient near `c` has a `C^{1,α}` isothermal chart at `c`.
* `TauCeti.Beltrami.exists_isothermal_chart_of_contDiffAt`: the same for a field of structures
  that is `C¹` at `c`, of either orientation, for every `0 < α < 1`.
* `TauCeti.Beltrami.exists_isothermal_chart_of_contDiffAt_of_sq_eq_neg_one`: a `C¹` field of
  complex structures of either orientation has a `C¹` isothermal chart, with `C¹` inverse, at
  every point.

## References

* L. V. Ahlfors, *Lectures on Quasiconformal Mappings*, 2nd ed., AMS University Lecture Series
  **38**, 2006, Chapter V.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Appendix E.
-/

public section

open Complex Metric Set Filter
open scoped ComplexConjugate NNReal Topology

namespace TauCeti.Beltrami

/-- **The normalized coefficient is Hölder.** If `μ` is `α`-Hölder on `ball c ρ` and bounded
there by `R < 1`, and `x ↦ c + L x` maps `ball 0 ρ'` into `ball c ρ`, then for `‖a‖ ≤ 1` the
coefficient `x ↦ (μ(c + L x) - a) / (1 - conj a μ(c + L x))` is `α`-Hölder on `ball 0 ρ'`. -/
private theorem exists_holderOnWith_moebius_comp {μ : ℂ → ℂ} {C α : ℝ≥0} {c a : ℂ}
    {L : ℂ →L[ℝ] ℂ} {ρ ρ' R : ℝ} (hμ : HolderOnWith C α μ (ball c ρ)) (hR : R < 1)
    (ha : ‖a‖ ≤ 1) (hμR : ∀ z ∈ ball c ρ, ‖μ z‖ ≤ R)
    (hmaps : MapsTo (fun x ↦ c + L x) (ball (0 : ℂ) ρ') (ball c ρ)) :
    ∃ K : ℝ≥0, HolderOnWith K α
      (fun x ↦ (μ (c + L x) - a) / (1 - conj a * μ (c + L x))) (ball 0 ρ') := by
  -- Compose `μ` with the affine map and the Möbius map, Lipschitz on `closedBall 0 R`.
  have hpre : HolderOnWith ‖L‖₊ 1 (fun x ↦ c + L x) (ball (0 : ℂ) ρ') :=
    holderOnWith_one.mpr (LipschitzOnWith.of_dist_le_mul fun x _ y _ ↦ by
      rw [dist_add_left, dist_eq_norm, dist_eq_norm, ← map_sub]
      exact L.le_opNorm _)
  have h := (holderOnWith_one.mpr (lipschitzOnWith_unitDiscMoebiusFormula_of_norm_le_one ha
    hR)).comp (hμ.comp hpre hmaps) fun x hx ↦ mem_closedBall_zero_iff.mpr (hμR _ (hmaps hx))
  rw [mul_one, one_mul] at h
  exact ⟨_, h⟩

/-- **Normalized and rescaled coefficient.** Let `μ` be `α`-Hölder on `ball c ρ` with
`‖μ c‖ < 1`, write `a = μ c`, and let `M` be a real-linear map. For every `δ > 0` there are
`ε > 0` and an `α`-Hölder function `f` vanishing off `closedBall 0 2`, of norm less than `δ`, that
on the unit disc is the coefficient `(μ - a) / (1 - conj a μ)` read at `z = c + M (ε w)`, with
`z ∈ ball c ρ`. -/
private theorem exists_rescaled_coefficient {α C : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    {μ : ℂ → ℂ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hμ : HolderOnWith C α μ (ball c ρ))
    (hμc : ‖μ c‖ < 1) (M : ℂ →L[ℝ] ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > (0 : ℝ), ∃ f ∈ supportedHolderSubmodule (Y := ℂ) α (closedBall (0 : ℂ) 2), ‖f‖ < δ ∧
      ∀ w ∈ ball (0 : ℂ) 1, c + M (ε • w) ∈ ball c ρ ∧
        f w * (1 - conj (μ c) * μ (c + M (ε • w))) = μ (c + M (ε • w)) - μ c := by
  set a := μ c
  set R := (1 + ‖a‖) / 2
  have hR : R < 1 := by simp only [R]; linarith
  -- Near `c` the coefficient stays in the closed disc of radius `R < 1`.
  obtain ⟨ρ₁, hρ₁, hρ₁μ⟩ := Metric.continuousAt_iff.mp
    ((hμ.continuousOn hα0).continuousAt (isOpen_ball.mem_nhds (mem_ball_self hρ)))
    ((1 - ‖a‖) / 2) (by linarith)
  set ρ₂ := min ρ₁ ρ
  have hρ₂ : 0 < ρ₂ := lt_min hρ₁ hρ
  have hμR : ∀ z ∈ ball c ρ₂, ‖μ z‖ ≤ R := by
    intro z hz
    have := hρ₁μ (lt_of_lt_of_le hz (min_le_left _ _))
    rw [dist_eq_norm] at this
    have := norm_le_norm_add_norm_sub' (μ z) a
    simp only [R]
    linarith
  set ρ₃ := ρ₂ / (‖M‖ + 1)
  have hρ₃ : 0 < ρ₃ := div_pos hρ₂ (by positivity)
  have hM : ‖M‖ * ρ₃ < ρ₂ := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg M]
  have hmaps : MapsTo (fun x ↦ c + M x) (ball (0 : ℂ) ρ₃) (ball c ρ₂) := by
    intro x hx
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact (M.le_opNorm x).trans_lt
      ((mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hx).le (norm_nonneg M)).trans_lt hM)
  obtain ⟨K, hK⟩ := exists_holderOnWith_moebius_comp
    (hμ.mono (ball_subset_ball (min_le_right _ _))) hR hμc.le hμR hmaps
  -- Rescale with a bump equal to `1` on the unit disc and supported in the disc of radius `2`.
  let χ : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hsmall := eventually_exists_holderSpace_cutoff_rescale hα0 hα1.le hρ₃ hK (by simp [a])
    (χ.contDiff (n := 1)) χ.hasCompactSupport hδ
  obtain ⟨ε, ⟨hεf, hε⟩⟩ :=
    ((hsmall.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT hρ₃)).exists
  obtain ⟨f, hf, hfχ, hfδ⟩ := hεf
  refine ⟨ε, hε.1, f, by rwa [χ.tsupport_eq] at hf, hfδ, fun w hw ↦ ?_⟩
  have hεw : ε • w ∈ ball (0 : ℂ) ρ₃ := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hε.1.le]
    calc ε * ‖w‖ ≤ ε * 1 := by gcongr; exacts [hε.1.le, (mem_ball_zero_iff.mp hw).le]
      _ < ρ₃ := by rw [mul_one]; exact hε.2
  have hz := hmaps hεw
  refine ⟨ball_subset_ball (min_le_right _ _) hz, ?_⟩
  have hden : 1 - conj a * μ (c + M (ε • w)) ≠ 0 :=
    one_sub_conj_mul_ne_zero_of_norm_le_one_of_norm_lt_one ((hμR _ hz).trans hR.le) hμc
  rw [hfχ, χ.one_of_mem_closedBall (ball_subset_closedBall hw), one_smul,
    div_mul_cancel₀ _ hden]

/-- **The Beltrami chart for a small coefficient.** There is `δ > 0` such that every
`α`-Hölder function `f` vanishing off `closedBall 0 2` with `‖f‖ < δ` is the Beltrami coefficient
of a chart at `0`: a `C¹` map `φ` near the disc, an open partial homeomorphism at `0`, whose
derivative is `α`-Hölder and injective on the disc and intertwines with `i` every tame structure
of coefficient `f w` at `w`. -/
private theorem exists_chart_of_norm_lt {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ δ > (0 : ℝ), ∀ f ∈ supportedHolderSubmodule (Y := ℂ) α (closedBall (0 : ℂ) 2), ‖f‖ < δ →
      ∃ (φ : ℂ → ℂ) (e : OpenPartialHomeomorph ℂ ℂ), ⇑e = φ ∧ (0 : ℂ) ∈ e.source ∧
        ContDiffOn ℝ 1 φ (ball 0 3) ∧
        (∃ K : ℝ≥0, HolderOnWith K α (fderiv ℝ φ) (closedBall 0 2)) ∧
        (∀ w ∈ closedBall (0 : ℂ) 2, Function.Injective (fderiv ℝ φ w)) ∧
        ∀ w ∈ closedBall (0 : ℂ) 2, ∀ (J : AlmostComplexStructure ℂ)
          (hJ : stdComplexSymplecticForm.Tames J), (coefficientEquiv ⟨J, hJ⟩).val = f w →
          IsComplexLinear J.toLinearMap (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
            (fderiv ℝ φ w).toLinearMap := by
  obtain ⟨δ, hδ, C₁, hchart⟩ := exists_isComplexLinear_chart hα0 hα1 (0 : ℂ) two_pos
  refine ⟨min δ 1, lt_min hδ one_pos, fun f hf hfδ ↦ ?_⟩
  have hf1 (w : ℂ) : ‖f w‖ < 1 :=
    (f.norm_apply_le w).trans_lt (hfδ.trans_le (min_le_right _ _))
  -- The structure with coefficient `f`, standard in the chart of the Beltrami solution.
  set Jf : ℂ → AlmostComplexStructure ℂ := fun w ↦ (coefficientEquiv.symm ⟨f w, hf1 w⟩).val
  have hJf (w : ℂ) : stdComplexSymplecticForm.Tames (Jf w) := (coefficientEquiv.symm _).property
  obtain ⟨h, -, -, -, -, -, hhol, hinv, -, hψ0, hφC1, -, -, hlin, e, he, he0, -⟩ :=
    hchart Jf (fun w _ ↦ hJf w) f hf (fun w _ ↦ by simp [Jf]) (hfδ.trans_le (min_le_left _ _))
  have hφ (w : ℂ) := fderiv_normalizedChart (ψ := cauchySolution h) (c := 0) (z := w)
  refine ⟨_, e, he, he0, by convert hφC1 using 2; norm_num,
    ⟨‖(wirtingerDeriv (cauchySolution h) 0 1)⁻¹‖₊ * (C₁ * ‖f‖₊), HolderOnWith.of_dist_le ?_⟩,
    fun w hw ↦ ?_, fun w hw J hJ hJw ↦ ?_⟩
  · intro w hw w' hw'
    rw [hφ, hφ, dist_eq_norm, ← smul_sub, norm_smul, ← dist_eq_norm, NNReal.coe_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hhol.dist_le hw hw') (norm_nonneg _)
  · obtain ⟨L, hL⟩ := hinv w hw
    rw [hφ, hL.hasFDerivAt.fderiv]
    exact (smul_right_injective ℂ (inv_ne_zero hψ0)).comp L.injective
  · obtain rfl : J = Jf w := congrArg Subtype.val (coefficientEquiv.injective
      (Subtype.ext (hJw.trans (by simp [Jf]))) : (⟨J, hJ⟩ : {J // _}) = ⟨Jf w, hJf w⟩)
    exact hlin w hw

/-- **Reading a chart through an affine map.** Let `φ` be `C¹` on `ball 0 2` with `α`-Hölder and
injective derivative on `ball 0 1`, and `e` an open partial homeomorphism with `⇑e = φ`. For a
real-linear isomorphism `L`, `ε ≠ 0` and `c`, the map `z ↦ φ (ε⁻¹ L (z - c))`, defined where
`ε⁻¹ L (z - c)` lies in `e.source ∩ ball 0 1`, is an open partial homeomorphism that is `C¹` on
its source with `α`-Hölder and invertible derivative. -/
private theorem exists_chart_comp_affine {α K : ℝ≥0} {φ : ℂ → ℂ} {e : OpenPartialHomeomorph ℂ ℂ}
    (he : ⇑e = φ) (hφ : ContDiffOn ℝ 1 φ (ball 0 2))
    (hK : HolderOnWith K α (fderiv ℝ φ) (ball 0 1))
    (hinj : ∀ w ∈ ball (0 : ℂ) 1, Function.Injective (fderiv ℝ φ w)) (L : ℂ ≃L[ℝ] ℂ) {ε : ℝ}
    (hε : ε ≠ 0) (c : ℂ) :
    ∃ E : OpenPartialHomeomorph ℂ ℂ,
      (∀ z, z ∈ E.source ↔ ε⁻¹ • L (z - c) ∈ e.source ∧ ε⁻¹ • L (z - c) ∈ ball (0 : ℂ) 1) ∧
      ContDiffOn ℝ 1 E E.source ∧ (∃ K' : ℝ≥0, HolderOnWith K' α (fderiv ℝ E) E.source) ∧
      (∀ z ∈ E.source, (fderiv ℝ E z).IsInvertible) ∧
      ∀ z ∈ E.source, fderiv ℝ E z =
        (fderiv ℝ φ (ε⁻¹ • L (z - c))).comp (ε⁻¹ • (L : ℂ →L[ℝ] ℂ)) := by
  set T : ℂ →L[ℝ] ℂ := ε⁻¹ • (L : ℂ →L[ℝ] ℂ)
  have hT (z : ℂ) : T z = ε⁻¹ • L z := by simp [T]
  let R : ℂ ≃ₜ ℂ := (Homeomorph.subRight c).trans
    (L.toHomeomorph.trans (Homeomorph.smulOfNeZero ε⁻¹ (inv_ne_zero hε)))
  set E := R.toOpenPartialHomeomorph.trans (e.restrOpen (ball 0 1) isOpen_ball)
  have hE : ⇑E = fun z ↦ φ (T (z - c)) := by
    ext z
    simp [E, R, he, hT]
  have hEs (z : ℂ) : z ∈ E.source ↔ T (z - c) ∈ e.source ∧ T (z - c) ∈ ball (0 : ℂ) 1 := by
    simp [E, R, hT]
  have hball (z : ℂ) (hz : z ∈ E.source) : T (z - c) ∈ ball (0 : ℂ) 2 :=
    ball_subset_ball one_le_two ((hEs z).mp hz).2
  have hdE (z : ℂ) (hz : z ∈ E.source) : fderiv ℝ E z = (fderiv ℝ φ (T (z - c))).comp T := by
    have hφd : DifferentiableAt ℝ φ (T (z - c)) :=
      (hφ.differentiableOn one_ne_zero _ (hball z hz)).differentiableAt
        (isOpen_ball.mem_nhds (hball z hz))
    rw [hE]
    exact (hφd.hasFDerivAt.comp z (T.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const c))).fderiv
  refine ⟨E, hEs, ?_, ?_, fun z hz ↦ ?_, hdE⟩
  · rw [hE]
    exact hφ.comp (T.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn hball
  · -- Precompose `fderiv ℝ φ` with the affine map and postcompose with `D ↦ D ∘ T`.
    have hpre : HolderOnWith ‖T‖₊ 1 (fun z ↦ T (z - c)) E.source :=
      holderOnWith_one.mpr (LipschitzOnWith.of_dist_le_mul fun z _ z' _ ↦ by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub, sub_sub_sub_cancel_right]
        exact T.le_opNorm _)
    have h := (holderWith_one.mpr ((ContinuousLinearMap.compL ℝ ℂ ℂ ℂ).flip T).lipschitzWith
      ).comp_holderOnWith (hK.comp hpre fun z hz ↦ ((hEs z).mp hz).2)
    rw [mul_one, one_mul] at h
    exact ⟨_, fun z hz z' hz' ↦ by rw [hdE z hz, hdE z' hz']; exact h z hz z' hz'⟩
  · rw [hdE z hz]
    refine (ContinuousLinearMap.isInvertible_iff_injective_of_finrank_eq rfl).2 ?_
    exact (hinj _ ((hEs z).mp hz).2).comp
      ((smul_right_injective ℂ (inv_ne_zero hε)).comp L.injective)

/-- **Isothermal coordinates for a Hölder structure.** Let `0 < α < 1` and let `J` be a field of
almost complex structures on the plane, tame on `ball c ρ`, whose scalar Beltrami coefficient `μ`
is `α`-Hölder there. Then `c` has an isothermal chart: an open partial homeomorphism `e` whose
source contains `c` and lies in `ball c ρ`, which is `C¹` on its source with `α`-Hölder and
invertible derivative, and in which `J` is multiplication by `i`: `de_z (J z v) = i · de_z v`. -/
theorem exists_isothermal_chart {α C : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    {J : ℂ → AlmostComplexStructure ℂ} {μ : ℂ → ℂ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hJ : ∀ z ∈ ball c ρ, stdComplexSymplecticForm.Tames (J z))
    (hμJ : ∀ z (hz : z ∈ ball c ρ), μ z = (coefficientEquiv ⟨J z, hJ z hz⟩).val)
    (hμ : HolderOnWith C α μ (ball c ρ)) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, c ∈ e.source ∧ e.source ⊆ ball c ρ ∧
      ContDiffOn ℝ 1 e e.source ∧ (∃ K : ℝ≥0, HolderOnWith K α (fderiv ℝ e) e.source) ∧
      (∀ z ∈ e.source, (fderiv ℝ e z).IsInvertible) ∧
      ∀ z ∈ e.source, ∀ v, fderiv ℝ e z (J z v) = I * fderiv ℝ e z v := by
  have hc : c ∈ ball c ρ := mem_ball_self hρ
  set a := μ c
  have ha : ‖a‖ < 1 := by
    have := (coefficientEquiv ⟨J c, hJ c hc⟩).property
    rwa [← hμJ c hc] at this
  have ha' : Complex.normSq a ≠ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  set L := linearEquiv a ha'
  -- Normalize by `L`, rescale, and solve the Beltrami equation for the rescaled coefficient.
  obtain ⟨δ, hδ, hchart⟩ := exists_chart_of_norm_lt hα0 hα1
  obtain ⟨ε, hε, f, hf, hfδ, hfw⟩ := exists_rescaled_coefficient hα0 hα1 hρ hμ ha
    (L.symm : ℂ →L[ℝ] ℂ) (lt_min hδ one_pos)
  obtain ⟨φ, e, he, he0, hφC1, ⟨K, hK⟩, hinj, hlin⟩ := hchart f hf (hfδ.trans_le (min_le_left _ _))
  have h1 : ball (0 : ℂ) 1 ⊆ closedBall 0 2 :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall one_le_two)
  obtain ⟨E, hEs, hEC1, hEK, hEinv, hdE⟩ := exists_chart_comp_affine he
    (hφC1.mono (ball_subset_ball (by norm_num))) (hK.mono h1) (fun w hw ↦ hinj w (h1 hw)) L
    hε.ne' c
  -- The point of the source read at `w = ε⁻¹ L (z - c)` is `z` again.
  have hz (z : ℂ) : c + (L.symm : ℂ →L[ℝ] ℂ) (ε • ε⁻¹ • L (z - c)) = z := by
    simp [hε.ne']
  have hsrc : E.source ⊆ ball c ρ := fun z hzE ↦ by
    have := (hfw _ ((hEs z).mp hzE).2).1
    rwa [hz] at this
  refine ⟨E, (hEs c).mpr (by simpa using he0), hsrc, hEC1, hEK, hEinv, fun z hzE v ↦ ?_⟩
  rw [hdE z hzE]
  set w := ε⁻¹ • L (z - c)
  have hw := ((hEs z).mp hzE).2
  have hzρ := hsrc hzE
  -- At `w`, the chart intertwines with `i` the structure `J'` of coefficient `f w`, which is the
  -- normalized coefficient of `J z`.
  set J' := coefficientEquiv.symm ⟨f w, (f.norm_apply_le w).trans_lt
    (hfδ.trans_le (min_le_right _ _))⟩
  have hJ' : (coefficientEquiv ⟨J'.val, J'.property⟩).val = f w := by simp [J']
  have hcoef : (coefficientEquiv ⟨J'.val, J'.property⟩).val *
      (1 - conj a * (coefficientEquiv ⟨J z, hJ z hzρ⟩).val) =
        (coefficientEquiv ⟨J z, hJ z hzρ⟩).val - a := by
    rw [hJ', ← hμJ z hzρ]
    have := (hfw w hw).2
    rwa [show c + (L.symm : ℂ →L[ℝ] ℂ) (ε • w) = z from hz z] at this
  have hkey := ((isComplexLinear_comp_linearMap_iff (J z) J'.val (hJ z hzρ) J'.property hcoef
    (fderiv ℝ φ w)).mpr (hlin w (h1 hw) J'.val J'.property hJ')).apply v
  have hkey' : fderiv ℝ φ w (linearMap a (J z v)) = I * fderiv ℝ φ w (linearMap a v) := by
    simpa only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_comp, AlmostComplexStructure.ofComplexModule_apply, smul_eq_mul] using hkey
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.map_smul_of_tower, L, linearEquiv_toContinuousLinearMap]
  rw [hkey', Complex.real_smul, Complex.real_smul]
  ring

/-- **Isothermal coordinates for a `C¹` structure, tame case.** The conclusion of
`exists_isothermal_chart_of_contDiffAt` for a field of structures that is tame at `c`. -/
private theorem exists_isothermal_chart_of_contDiffAt_of_tames {α : ℝ≥0} (hα0 : 0 < α)
    (hα1 : α < 1)
    {J : ℂ → AlmostComplexStructure ℂ} {c : ℂ}
    (hJ : ContDiffAt ℝ 1 (fun z ↦ LinearMap.toContinuousLinearMap (J z).toLinearMap) c)
    (hJc : stdComplexSymplecticForm.Tames (J c)) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, c ∈ e.source ∧
      ContDiffOn ℝ 1 e e.source ∧ (∃ K : ℝ≥0, HolderOnWith K α (fderiv ℝ e) e.source) ∧
      (∀ z ∈ e.source, (fderiv ℝ e z).IsInvertible) ∧
      ∀ z ∈ e.source, ∀ v, fderiv ℝ e z (J z v) = I * fderiv ℝ e z v := by
  set μ : ℂ → ℂ := fun z ↦ (AlmostComplexStructure.ofComplexModule ℂ).cayley (J z) 1
  -- The coefficient is `C¹` at `c`, hence Lipschitz near `c`.
  have hμ : ContDiffAt ℝ 1 μ c := contMDiffAt_iff_contDiffAt.mp
    ((stdComplexSymplecticForm_tames.contMDiffAt_cayley hJc hJ.contMDiffAt).clm_apply
      (contMDiffAt_const (c := (1 : ℂ))))
  obtain ⟨K, t, ht, hK⟩ := hμ.exists_lipschitzOnWith
  obtain ⟨ρ, hρ, hρt⟩ := Metric.mem_nhds_iff.mp
    (inter_mem ht (SymplecticForm.Tames.eventually_of_continuousAt hJ.continuousAt hJc))
  have hJρ (z : ℂ) (hz : z ∈ ball c ρ) : stdComplexSymplecticForm.Tames (J z) := (hρt hz).2
  have hμJ (z : ℂ) (hz : z ∈ ball c ρ) : μ z = (coefficientEquiv ⟨J z, hJρ z hz⟩).val :=
    (coefficientEquiv_apply (J z) (hJρ z hz)).symm
  -- A bounded Lipschitz function is `α`-Hölder.
  have hHolder := (hK.mono fun z hz ↦ (hρt hz).1).holderOnWith_of_norm_le (M := 1)
    (fun z hz ↦ by rw [hμJ z hz]; exact (coefficientEquiv _).property.le) hα1.le
  obtain ⟨e, hce, -, he⟩ := exists_isothermal_chart hα0 hα1 hρ hJρ hμJ hHolder
  exact ⟨e, hce, he⟩

/-! ### Fields of complex structures of either orientation -/

/-- An isothermal chart `e` for a field `K` on the plane, composed with a real-affine change of
coordinates `z ↦ A (z - c)` that carries a field `J` to `K`, is an isothermal chart for `J`. -/
private theorem exists_isothermal_chart_comp_affine {J K : ℂ → ℂ →L[ℝ] ℂ}
    {e : OpenPartialHomeomorph ℂ ℂ} (he : ∀ w ∈ e.source, ContDiffAt ℝ 1 e w)
    (hes : ∀ w ∈ e.target, ContDiffAt ℝ 1 e.symm w)
    (hK : ∀ w ∈ e.source, ∀ v, fderiv ℝ e w (K w v) = I * fderiv ℝ e w v) (A : ℂ ≃L[ℝ] ℂ)
    (c : ℂ) (hJ : ∀ z, A (z - c) ∈ e.source → ∀ v, A (J z v) = K (A (z - c)) (A v)) :
    ∃ F : OpenPartialHomeomorph ℂ ℂ, (∀ z, z ∈ F.source ↔ A (z - c) ∈ e.source) ∧
      (∀ z ∈ F.source, ContDiffAt ℝ 1 F z) ∧ (∀ z ∈ F.target, ContDiffAt ℝ 1 F.symm z) ∧
      ∀ z ∈ F.source, ∀ v, fderiv ℝ F z (J z v) = I * fderiv ℝ F z v := by
  let T : ℂ ≃ₜ ℂ := (Homeomorph.subRight c).trans A.toHomeomorph
  have hT : ∀ z, HasFDerivAt (fun z ↦ A (z - c)) (A : ℂ →L[ℝ] ℂ) z := fun z ↦
    (A : ℂ →L[ℝ] ℂ).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const c)
  have hTc : ContDiff ℝ 1 fun z ↦ A (z - c) := A.contDiff.comp (contDiff_id.sub contDiff_const)
  have hTsc : ContDiff ℝ 1 fun w ↦ A.symm w + c := A.symm.contDiff.add contDiff_const
  let F := T.toOpenPartialHomeomorph.trans e
  have hFcoe : ⇑F = e ∘ fun z ↦ A (z - c) := by
    ext z
    simp [F, T]
  have hFsrc : ∀ z, z ∈ F.source ↔ A (z - c) ∈ e.source := fun z ↦ by simp [F, T]
  refine ⟨F, hFsrc, fun z hz ↦ ?_, fun a ha ↦ ?_, fun z hz v ↦ ?_⟩
  · rw [hFcoe]
    exact (he _ ((hFsrc z).1 hz)).comp z hTc.contDiffAt
  · rw [OpenPartialHomeomorph.trans_target] at ha
    rw [OpenPartialHomeomorph.coe_trans_symm]
    exact hTsc.contDiffAt.comp a (hes a ha.1)
  · have hw := (hFsrc z).1 hz
    have hFd : fderiv ℝ F z = (fderiv ℝ e (A (z - c))).comp (A : ℂ →L[ℝ] ℂ) := by
      rw [hFcoe]
      exact ((((he _ hw).differentiableAt one_ne_zero).hasFDerivAt).comp z (hT z)).fderiv
    rw [hFd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, hJ z hw, hK _ hw]

/-! ### Fields equal to `i` at the origin -/

/-- The Beltrami coefficient `ν u = (i - K u 1) / (conj (K u 1) - i)` of a `C¹` field `K` of
complex structures with `K 0 = i` is `1/2`-Hölder near `0`, and conjugates `K u` to `i` there. -/
private theorem exists_holderOnWith_coefficient {K : ℂ → ℂ →L[ℝ] ℂ} (hK : ContDiffAt ℝ 1 K 0)
    (hsq : ∀ᶠ u in 𝓝 0, ∀ v, K u (K u v) = -v) (hK0 : K 0 1 = I) :
    ∃ ρ > 0, ∃ C : ℝ≥0,
      HolderOnWith C (1 / 2) (fun u ↦ (I - K u 1) / (conj (K u 1) - I)) (ball 0 ρ) ∧
      ∀ u ∈ ball (0 : ℂ) ρ, ∀ v, linearMap ((I - K u 1) / (conj (K u 1) - I)) (K u v) =
        I * linearMap ((I - K u 1) / (conj (K u 1) - I)) v := by
  set b : ℂ → ℂ := fun u ↦ K u 1
  set ν : ℂ → ℂ := fun u ↦ (I - b u) / (conj (b u) - I)
  have hbc : ContDiffAt ℝ 1 b 0 := hK.clm_apply contDiffAt_const
  have hν0 : ν 0 = 0 := by simp [ν, b, hK0]
  -- `ν` is `C¹` near `0`, hence Lipschitz there.
  have hνc : ContDiffAt ℝ 1 ν 0 := by
    have hden : ContDiffAt ℝ 1 (fun u ↦ conj (b u) - I) 0 :=
      (Complex.conjCLE.contDiff.contDiffAt.comp 0 hbc).sub contDiffAt_const
    have hden0 : conj (b 0) - I ≠ 0 := by
      rw [show b 0 = I from hK0, conj_I]
      norm_num [Complex.ext_iff]
    convert (contDiffAt_const (c := I)).sub hbc |>.mul (hden.inv hden0) using 1
    ext u
    simp [ν, div_eq_mul_inv]
  obtain ⟨L, t, ht, hL⟩ := hνc.exists_lipschitzOnWith
  have hgood : ∀ᶠ u in 𝓝 (0 : ℂ), u ∈ t ∧ (∀ v, K u (K u v) = -v) ∧ b u ≠ -I :=
    (show ∀ᶠ u in 𝓝 (0 : ℂ), u ∈ t from ht).and (hsq.and (hbc.continuousAt.eventually_ne
      (by rw [show b 0 = I from hK0]; norm_num [Complex.ext_iff])))
  obtain ⟨ρ, hρ, hρgood⟩ := Metric.eventually_nhds_iff_ball.1 hgood
  -- A Lipschitz function vanishing at `0` is bounded on a ball, hence Hölder there.
  have hνL : LipschitzOnWith L ν (ball 0 ρ) := hL.mono fun u hu ↦ (hρgood u hu).1
  have hνb : ∀ u ∈ ball (0 : ℂ) ρ, ‖ν u‖ ≤ ((L * ρ.toNNReal : ℝ≥0) : ℝ) := by
    intro u hu
    have h := hνL.dist_le_mul u hu 0 (mem_ball_self hρ)
    rw [hν0, dist_zero_right, dist_zero_right] at h
    refine h.trans ?_
    push_cast
    rw [Real.coe_toNNReal _ hρ.le]
    exact mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hu).le L.coe_nonneg
  refine ⟨ρ, hρ, _, hνL.holderOnWith_of_norm_le hνb (by norm_num), fun u hu v ↦ ?_⟩
  obtain ⟨-, hKsq, hbne⟩ := hρgood u hu
  exact linearMap_apply_eq_I_mul hKsq hbne v

/-- **Isothermal charts at a point where the field is `i`, after rescaling.** If `K` is a `C¹`
field of complex structures near `0` with `K 0 = i`, then for some `ε > 0` the rescaled field
`w ↦ K (ε w)` has a `C¹` isothermal chart at `0`, with `C¹` inverse. -/
private theorem exists_isothermal_chart_rescale {K : ℂ → ℂ →L[ℝ] ℂ} (hK : ContDiffAt ℝ 1 K 0)
    (hsq : ∀ᶠ u in 𝓝 0, ∀ v, K u (K u v) = -v) (hK0 : K 0 1 = I) :
    ∃ ε > (0 : ℝ), ∃ e : OpenPartialHomeomorph ℂ ℂ, 0 ∈ e.source ∧
      (∀ w ∈ e.source, ContDiffAt ℝ 1 e w) ∧ (∀ w ∈ e.target, ContDiffAt ℝ 1 e.symm w) ∧
      ∀ w ∈ e.source, ∀ v, fderiv ℝ e w (K (ε • w) v) = I * fderiv ℝ e w v := by
  obtain ⟨ρ, hρ, C', hνH, hνK⟩ := exists_holderOnWith_coefficient hK hsq hK0
  set ν : ℂ → ℂ := fun u ↦ (I - K u 1) / (conj (K u 1) - I)
  have hν0 : ν 0 = 0 := by simp [ν, hK0]
  have hα0 : (0 : ℝ≥0) < 1 / 2 := by norm_num
  have hα1 : (1 / 2 : ℝ≥0) < 1 := by
    rw [← NNReal.coe_lt_coe]
    norm_num
  -- The planar Beltrami chart on the disc of radius `2`, for the coefficient `χ w ν (ε w)`.
  obtain ⟨δ, hδ, C, hchart⟩ := exists_isComplexLinear_chart hα0 hα1 (0 : ℂ) (r := 2) two_pos
  let χ : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨ε, ⟨⟨f, hf, hfχ, hfδ⟩, hερ⟩, hε⟩ :=
    ((((eventually_exists_holderSpace_cutoff_rescale hα0 hα1.le hρ hνH hν0 χ.contDiff
      χ.hasCompactSupport (lt_min hδ one_pos)).and (ball_mem_nhds (0 : ℝ) hρ)).filter_mono
        nhdsWithin_le_nhds).and self_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), _).exists
  rw [χ.tsupport_eq] at hf
  have hf1 : ∀ w, ‖f w‖ < 1 := fun w ↦
    (HolderSpace.norm_apply_le f w).trans_lt (hfδ.trans_le (min_le_right _ _))
  set Jf : ℂ → AlmostComplexStructure ℂ := fun w ↦ (coefficientEquiv.symm ⟨f w, hf1 w⟩).val
  obtain ⟨h, -, -, -, -, -, -, -, -, -, hφC1, -, -, hφlin, e, he, he0, hesrc, hes⟩ :=
    hchart Jf (fun w _ ↦ (coefficientEquiv.symm ⟨f w, hf1 w⟩).property) f hf
      (fun w _ ↦ by simp [Jf]) (hfδ.trans_le (min_le_left _ _))
  rw [← he] at hφC1 hφlin
  -- On the unit disc, the structure with coefficient `f w = ν (ε w)` is `K (ε w)`.
  have hJfK : ∀ w ∈ ball (0 : ℂ) 1, ∀ v, (Jf w).toLinearMap v = K (ε • w) v := by
    intro w hw v
    have hu : ε • w ∈ ball (0 : ℂ) ρ := by
      rw [mem_ball_zero_iff, norm_smul]
      calc ‖ε‖ * ‖w‖ ≤ ‖ε‖ * 1 := mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hw).le
            (norm_nonneg _)
        _ < ρ := by simpa using hερ
    have hfw : (f w : ℂ) = ν (ε • w) := by
      rw [hfχ, χ.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp hw).le),
        one_smul]
    simp only [Jf, coefficientEquiv_symm_apply]
    rw [ContinuousLinearEquiv.symm_apply_eq, linearEquiv_apply, linearEquiv_apply]
    have hlin := hνK _ hu v
    simp only [linearMap_apply] at hlin
    simp only [hfw, ν]
    rw [hlin]
  -- Restrict the chart to the unit disc.
  refine ⟨ε, hε, e.restrOpen (ball 0 1) isOpen_ball, ⟨he0, mem_ball_self one_pos⟩,
    fun w hw ↦ ?_, fun w hw ↦ ?_, fun w hw v ↦ ?_⟩
  · exact hφC1.contDiffAt (isOpen_ball.mem_nhds (ball_subset_ball (by norm_num) (hesrc hw.1)))
  · exact hes w (by simpa using hw : w ∈ e.target ∧ _).1
  · have h := (hφlin w (ball_subset_closedBall (hesrc hw.1))).apply v
    rw [OpenPartialHomeomorph.coe_restrOpen, ← hJfK w hw.2 v]
    simpa [AlmostComplexStructure.ofComplexModule_apply] using h

/-- **Isothermal coordinates for a field of either orientation.** Let `J` be a field of
real-linear endomorphisms of the plane which is `C¹` at `z₀` and squares to `-1` near `z₀`, of
either orientation. Then there is an open partial homeomorphism `e` of the plane, with `z₀` in its
source, which is `C¹` on its source with `C¹` inverse on its target and whose derivative carries
`J` to multiplication by `i` at every point of its source: `J = i` in the chart `e`. -/
theorem exists_isothermal_chart_of_contDiffAt_of_sq_eq_neg_one {J : ℂ → ℂ →L[ℝ] ℂ} {z₀ : ℂ}
    (hJ : ContDiffAt ℝ 1 J z₀)
    (hsq : ∀ᶠ z in 𝓝 z₀, ∀ v, J z (J z v) = -v) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, z₀ ∈ e.source ∧ (∀ z ∈ e.source, ContDiffAt ℝ 1 e z) ∧
      (∀ z ∈ e.target, ContDiffAt ℝ 1 e.symm z) ∧
      ∀ z ∈ e.source, ∀ v, fderiv ℝ e z (J z v) = I * fderiv ℝ e z v := by
  /- In the coordinates `u = B⁻¹ (z - z₀)`, where `B` carries `i` to `J z₀`, the field becomes
  `K u = B⁻¹ ∘ J (z₀ + B u) ∘ B`, with `K 0 = i`. -/
  obtain ⟨B, hB⟩ := (J z₀).exists_continuousLinearEquiv_comp_eq_comp_I_smul
    (ContinuousLinearMap.ext hsq.self_of_nhds)
  set K : ℂ → ℂ →L[ℝ] ℂ :=
    fun u ↦ (B.symm : ℂ →L[ℝ] ℂ).comp ((J (z₀ + B u)).comp (B : ℂ →L[ℝ] ℂ))
  have hKc : ContDiffAt ℝ 1 K 0 := by
    have hJ₀ : ContDiffAt ℝ 1 J (z₀ + B 0) := by simpa using hJ
    exact contDiffAt_const.clm_comp
      ((hJ₀.comp 0 (contDiffAt_const.add B.contDiff.contDiffAt)).clm_comp contDiffAt_const)
  have hKsq : ∀ᶠ u in 𝓝 (0 : ℂ), ∀ v, K u (K u v) = -v := by
    have hT : Tendsto (fun u : ℂ ↦ z₀ + B u) (𝓝 0) (𝓝 z₀) :=
      (show Continuous (fun u : ℂ ↦ z₀ + B u) by fun_prop).tendsto' 0 z₀ (by simp)
    filter_upwards [hT.eventually hsq] with u hu v
    simp [K, hu]
  /- After rescaling by `ε`, `K` has an isothermal chart `e` at `0`; composing it with
  `z ↦ ε⁻¹ B⁻¹ (z - z₀)` gives the chart of `J`. -/
  obtain ⟨ε, hε, e, he0, he, hes, heK⟩ := exists_isothermal_chart_rescale hKc hKsq
    (by simpa [K] using congr(B.symm ($hB 1)))
  obtain ⟨F, hFsrc, hF, hFs, hFJ⟩ := exists_isothermal_chart_comp_affine (J := J)
    (K := fun w ↦ K (ε • w)) he hes heK
    (B.symm.trans (ContinuousLinearEquiv.smulLeft (Units.mk0 (ε⁻¹ : ℝ) (inv_ne_zero hε.ne'))))
    z₀ fun z _ v ↦ by
      simp [K, Units.smul_def, smul_smul, mul_inv_cancel₀ hε.ne', -Complex.real_smul]
  exact ⟨F, (hFsrc z₀).2 (by simpa using he0), hF, hFs, hFJ⟩

/-! ### Untamed fields of almost complex structures -/

/-- **Isothermal charts after conjugation.** If `e'` is an isothermal chart at `conj c` for the
conjugated field `z ↦ conj ∘ J (conj z) ∘ conj`, then `e' ∘ conj` is an isothermal chart at `c`
for `J`, with derivative `de'_(conj z) ∘ conj`, again `α`-Hölder and invertible. -/
private theorem exists_isothermal_chart_of_transport_conj {α K : ℝ≥0}
    {J : ℂ → AlmostComplexStructure ℂ} {c : ℂ} (e' : OpenPartialHomeomorph ℂ ℂ)
    (hce' : conj c ∈ e'.source) (he'C : ContDiffOn ℝ 1 e' e'.source)
    (hK : HolderOnWith K α (fderiv ℝ e') e'.source)
    (he'inv : ∀ z ∈ e'.source, (fderiv ℝ e' z).IsInvertible)
    (he'J : ∀ z ∈ e'.source, ∀ v, fderiv ℝ e' z ((J (conj z)).transport conjCLE.toLinearEquiv v) =
      I * fderiv ℝ e' z v) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, c ∈ e.source ∧
      ContDiffOn ℝ 1 e e.source ∧ (∃ K : ℝ≥0, HolderOnWith K α (fderiv ℝ e) e.source) ∧
      (∀ z ∈ e.source, (fderiv ℝ e z).IsInvertible) ∧
      ∀ z ∈ e.source, ∀ v, fderiv ℝ e z (J z v) = I * fderiv ℝ e z v := by
  set σ : ℂ ≃L[ℝ] ℂ := conjCLE with hσdef
  have hσ (z : ℂ) : σ z = conj z := conjCLE_apply z
  set e := σ.toHomeomorph.toOpenPartialHomeomorph.trans e'
  have hes (z : ℂ) : z ∈ e.source ↔ σ z ∈ e'.source := by simp [e]
  have hecoe : (e : ℂ → ℂ) = e' ∘ σ := by
    simp [e, OpenPartialHomeomorph.coe_trans]
  have hde (z : ℂ) : fderiv ℝ e z = (fderiv ℝ e' (σ z)).comp (σ : ℂ →L[ℝ] ℂ) := by
    rw [hecoe]
    exact σ.comp_right_fderiv
  refine ⟨e, (hes c).2 hce', ?_, ⟨K, fun z hz w hw ↦ ?_⟩, fun z hz ↦ ?_, fun z hz v ↦ ?_⟩
  · rw [hecoe]
    exact he'C.comp σ.contDiff.contDiffOn fun z hz ↦ (hes z).1 hz
  · -- Precomposition with the linear isometry `σ = conjLIE` preserves distances of operators.
    rw [hde, hde]
    calc edist ((fderiv ℝ e' (σ z)).comp (σ : ℂ →L[ℝ] ℂ))
          ((fderiv ℝ e' (σ w)).comp (σ : ℂ →L[ℝ] ℂ))
        = edist (fderiv ℝ e' (σ z)) (fderiv ℝ e' (σ w)) := by
          rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.sub_comp,
            hσdef, ← conjLIE_toCLE]
          exact congrArg ENNReal.ofReal
            (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ conjLIE)
      _ ≤ K * edist (σ z) (σ w) ^ (α : ℝ) := hK.edist_le ((hes z).1 hz) ((hes w).1 hw)
      _ = K * edist z w ^ (α : ℝ) := by rw [hσ, hσ, isometry_conj.edist_eq]
  · rw [hde]
    exact (he'inv _ ((hes z).1 hz)).comp ContinuousLinearMap.isInvertible_equiv
  · -- `σ (J z v)` is the conjugated structure at `σ z` applied to `σ v`.
    have hJ'z : σ (J z v) = (J (conj (σ z))).transport σ.toLinearEquiv (σ v) := by
      simp only [σ, AlmostComplexStructure.transport_conjCLE_apply, conjCLE_apply, conj_conj]
    rw [hde, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, hJ'z, he'J _ ((hes z).1 hz)]

/-- **Isothermal coordinates for a `C¹` structure.** Let `J` be a field of almost complex
structures on the plane that is `C¹` at `c` in the operator norm. Then for every `0 < α < 1`, `c`
has an isothermal chart: an open partial homeomorphism `e` whose source contains `c`, which is `C¹`
on its source with `α`-Hölder and invertible derivative, and in which `J` is multiplication by `i`.

No orientation condition is needed: if `J c` is not tamed by the standard area form, then its
conjugate by complex conjugation is (`stdComplexSymplecticForm_tames_or_tames_transport_conj`). -/
theorem exists_isothermal_chart_of_contDiffAt {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    {J : ℂ → AlmostComplexStructure ℂ} {c : ℂ}
    (hJ : ContDiffAt ℝ 1 (fun z ↦ LinearMap.toContinuousLinearMap (J z).toLinearMap) c) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, c ∈ e.source ∧
      ContDiffOn ℝ 1 e e.source ∧ (∃ K : ℝ≥0, HolderOnWith K α (fderiv ℝ e) e.source) ∧
      (∀ z ∈ e.source, (fderiv ℝ e z).IsInvertible) ∧
      ∀ z ∈ e.source, ∀ v, fderiv ℝ e z (J z v) = I * fderiv ℝ e z v := by
  rcases stdComplexSymplecticForm_tames_or_tames_transport_conj (J c) with hJc | hJc
  · exact exists_isothermal_chart_of_contDiffAt_of_tames hα0 hα1 hJ hJc
  -- Otherwise the conjugated field `J'` is `C¹` and tame at `conj c`.
  set σ : ℂ ≃L[ℝ] ℂ := conjCLE
  have hσc : σ (σ c) = c := by simp only [σ, conjCLE_apply, conj_conj]
  set J' : ℂ → AlmostComplexStructure ℂ := fun z ↦ (J (conj z)).transport σ.toLinearEquiv
  have hJ'eq : (fun z ↦ LinearMap.toContinuousLinearMap (J' z).toLinearMap) = fun z ↦
      (σ : ℂ →L[ℝ] ℂ) ∘L LinearMap.toContinuousLinearMap (J (σ z)).toLinearMap ∘L
        (σ : ℂ →L[ℝ] ℂ) := by
    funext z
    ext1 v
    simp only [J', σ, AlmostComplexStructure.transport_conjCLE_apply,
      LinearMap.coe_toContinuousLinearMap', ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, conjCLE_apply]
  have hJ' : ContDiffAt ℝ 1 (fun z ↦ LinearMap.toContinuousLinearMap (J' z).toLinearMap)
      (σ c) := by
    rw [hJ'eq]
    exact contDiffAt_const.clm_comp
      (((hσc ▸ hJ).comp (σ c) σ.contDiff.contDiffAt).clm_comp contDiffAt_const)
  have hJ'c : stdComplexSymplecticForm.Tames (J' (σ c)) := by
    simpa [J', σ] using hJc
  obtain ⟨e', hce', he'C, ⟨K, hK⟩, he'inv, he'J⟩ :=
    exists_isothermal_chart_of_contDiffAt_of_tames hα0 hα1 hJ' hJ'c
  exact exists_isothermal_chart_of_transport_conj e' hce' he'C hK he'inv he'J

end TauCeti.Beltrami
