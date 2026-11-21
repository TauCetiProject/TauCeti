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
import TauCeti.Analysis.Normed.Operator.FiniteDimensional
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Analysis.Complex.Beltrami.HigherHolder
import TauCeti.Analysis.Complex.Beltrami.Transition
import TauCeti.Analysis.Complex.Conformal.Moebius
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy
import TauCeti.Topology.MetricSpace.Holder

/-!
# Isothermal charts for planar almost complex structures

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

For a smooth field, finite-order Beltrami solutions give isothermal charts of every finite order,
with a local scale depending on the order. Holomorphic transition maps then show that the original
`C¹` chart is smooth on its source; its inverse is smooth as well. Smooth coordinates may be
centred at any prescribed point.

## Main results

* `TauCeti.Beltrami.exists_isothermal_chart`: a tame field of structures with `α`-Hölder
  Beltrami coefficient near `c` has a `C^{1,α}` isothermal chart at `c`.
* `TauCeti.Beltrami.exists_isothermal_chart_of_contDiffAt`: the same for a field of structures
  that is `C¹` at `c`, of either orientation, for every `0 < α < 1`.
* `TauCeti.Beltrami.exists_isothermal_chart_of_contDiffAt_of_sq_eq_neg_one`: a `C¹` field of
  complex structures of either orientation has a `C¹` isothermal chart, with `C¹` inverse, at
  every point.
* `TauCeti.Beltrami.exists_isothermal_chart_finite_order`: a `C^(k+1)` field of either orientation
  has a centred local isothermal chart of the same order.
* `TauCeti.Beltrami.contDiffOn_infty_and_symm_of_contDiffOn_field`: a `C¹` isothermal chart for a
  smooth field, and its inverse, are smooth on their original domains.
* `TauCeti.Beltrami.exists_centered_smooth_isothermal_chart`: centred smooth coordinates for a
  smooth field of either orientation.

## References

* L. V. Ahlfors, *Lectures on Quasiconformal Mappings*, 2nd ed., AMS University Lecture Series
  **38**, 2006, Chapter V.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Appendix E.
-/

public section

open Complex Metric Set Filter
open scoped ComplexConjugate NNReal Topology ContDiff

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
    {e : OpenPartialHomeomorph ℂ ℂ} {n : ℕ∞ω} (hn : 1 ≤ n)
    (he : ∀ w ∈ e.source, ContDiffAt ℝ n e w)
    (hes : ∀ w ∈ e.target, ContDiffAt ℝ n e.symm w)
    (hK : ∀ w ∈ e.source, ∀ v, fderiv ℝ e w (K w v) = I * fderiv ℝ e w v) (A : ℂ ≃L[ℝ] ℂ)
    (c : ℂ) (hJ : ∀ z, A (z - c) ∈ e.source → ∀ v, A (J z v) = K (A (z - c)) (A v)) :
    ∃ F : OpenPartialHomeomorph ℂ ℂ, (∀ z, z ∈ F.source ↔ A (z - c) ∈ e.source) ∧
      (∀ z, F z = e (A (z - c))) ∧ (∀ z ∈ F.source, ContDiffAt ℝ n F z) ∧
      (∀ z ∈ F.target, ContDiffAt ℝ n F.symm z) ∧
      ∀ z ∈ F.source, ∀ v, fderiv ℝ F z (J z v) = I * fderiv ℝ F z v := by
  let T : ℂ ≃ₜ ℂ := (Homeomorph.subRight c).trans A.toHomeomorph
  have hT : ∀ z, HasFDerivAt (fun z ↦ A (z - c)) (A : ℂ →L[ℝ] ℂ) z := fun z ↦
    (A : ℂ →L[ℝ] ℂ).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const c)
  have hTc : ContDiff ℝ n fun z ↦ A (z - c) := A.contDiff.comp (contDiff_id.sub contDiff_const)
  have hTsc : ContDiff ℝ n fun w ↦ A.symm w + c := A.symm.contDiff.add contDiff_const
  let F := T.toOpenPartialHomeomorph.trans e
  have hFcoe : ⇑F = e ∘ fun z ↦ A (z - c) := by
    ext z
    simp [F, T]
  have hFsrc : ∀ z, z ∈ F.source ↔ A (z - c) ∈ e.source := fun z ↦ by simp [F, T]
  refine ⟨F, hFsrc, fun z ↦ congrFun hFcoe z, fun z hz ↦ ?_,
    fun a ha ↦ ?_, fun z hz v ↦ ?_⟩
  · rw [hFcoe]
    exact (he _ ((hFsrc z).1 hz)).comp z hTc.contDiffAt
  · rw [OpenPartialHomeomorph.trans_target] at ha
    rw [OpenPartialHomeomorph.coe_trans_symm]
    exact hTsc.contDiffAt.comp a (hes a ha.1)
  · have hw := (hFsrc z).1 hz
    have hFd : fderiv ℝ F z = (fderiv ℝ e (A (z - c))).comp (A : ℂ →L[ℝ] ℂ) := by
      rw [hFcoe]
      exact (((he _ hw).differentiableAt
        (ne_of_gt (lt_of_lt_of_le zero_lt_one hn))).hasFDerivAt.comp z (hT z)).fderiv
    rw [hFd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, hJ z hw, hK _ hw]

/-! ### Fields equal to `i` at the origin -/

/-- The scalar normalizer is smooth wherever its denominator is nonzero. -/
private theorem contDiffAt_normalizer {K : ℂ → ℂ →L[ℝ] ℂ} {n : ℕ∞ω}
    (hK : ContDiffAt ℝ n K 0) (hden : conj (K 0 1) - I ≠ 0) :
    ContDiffAt ℝ n (fun u ↦ (I - K u 1) / (conj (K u 1) - I)) 0 := by
  have hb := hK.clm_apply (contDiffAt_const (c := (1 : ℂ)))
  have hd : ContDiffAt ℝ n (fun u ↦ conj (K u 1) - I) 0 :=
    (Complex.conjCLE.contDiff.contDiffAt.comp 0 hb).sub contDiffAt_const
  convert (contDiffAt_const (c := I)).sub hb |>.mul (hd.inv hden) using 1
  ext u
  simp [div_eq_mul_inv]

/-- Coordinates in which the field at the chosen point is multiplication by `i`. -/
private theorem exists_standardizing_equiv {J : ℂ → ℂ →L[ℝ] ℂ} {c : ℂ} {n : ℕ∞ω}
    (hJ : ContDiffAt ℝ n J c) (hsq : ∀ᶠ z in 𝓝 c, ∀ v, J z (J z v) = -v) :
    ∃ B : ℂ ≃L[ℝ] ℂ,
      let K : ℂ → ℂ →L[ℝ] ℂ := fun u ↦ (B.symm.arrowCongr B.symm) (J (c + B u))
      ContDiffAt ℝ n K 0 ∧ (∀ᶠ u in 𝓝 0, ∀ v, K u (K u v) = -v) ∧ K 0 1 = I ∧
      ∀ (ε : ℝ) (hε : ε ≠ 0),
        let A := B.symm.trans
          (ContinuousLinearEquiv.smulLeft (Units.mk0 (ε⁻¹ : ℝ) (inv_ne_zero hε)))
        ∀ z v, A (J z v) = K (ε • A (z - c)) (A v) := by
  obtain ⟨B, hB⟩ := (J c).exists_continuousLinearEquiv_comp_eq_comp_I_smul
    (ContinuousLinearMap.ext hsq.self_of_nhds)
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · have hJc : ContDiffAt ℝ n J (c + B 0) := by simpa using hJ
    exact (B.symm.arrowCongr B.symm).contDiff.contDiffAt.comp 0
      (hJc.comp 0 (contDiffAt_const.add B.contDiff.contDiffAt))
  · have hcont : Continuous (fun u : ℂ ↦ c + B u) := by fun_prop
    have hT : Tendsto (fun u : ℂ ↦ c + B u) (𝓝 0) (𝓝 c) :=
      hcont.tendsto' 0 c (by simp)
    filter_upwards [hT.eventually hsq] with u hu v
    simp [ContinuousLinearEquiv.arrowCongr_apply, hu]
  · simpa [ContinuousLinearEquiv.arrowCongr_apply] using congr(B.symm ($hB 1))
  · intro ε hε
    dsimp only
    intro z v
    simp [ContinuousLinearEquiv.arrowCongr_apply, Units.smul_def, smul_smul,
      mul_inv_cancel₀ hε, -Complex.real_smul]

/-! ### Smooth fields -/

/-- Near a standard value, the scalar normalizer preserves the given finite order. -/
private theorem exists_contDiffOn_normalizer_ball (k : ℕ) {K : ℂ → ℂ →L[ℝ] ℂ}
    (hK : ContDiffAt ℝ (k + 1 : ℕ) K 0) (hsq : ∀ᶠ u in 𝓝 0, ∀ v, K u (K u v) = -v)
    (hK0 : K 0 1 = I) :
    ∃ ρ > 0,
      ContDiffOn ℝ (k + 1 : ℕ) (fun u ↦ (I - K u 1) / (conj (K u 1) - I)) (ball 0 ρ) ∧
      ∀ u ∈ ball (0 : ℂ) ρ, ∀ v,
        linearMap ((I - K u 1) / (conj (K u 1) - I)) (K u v) =
          I * linearMap ((I - K u 1) / (conj (K u 1) - I)) v := by
  have hb : ContDiffAt ℝ (k + 1 : ℕ) (fun u ↦ K u 1) 0 := hK.clm_apply contDiffAt_const
  have hden : conj (K 0 1) - I ≠ 0 := by rw [hK0, conj_I]; norm_num [Complex.ext_iff]
  have hν := contDiffAt_normalizer hK hden
  obtain ⟨t, ht, hνt⟩ := hν.contDiffOn (m := (k + 1 : ℕ)) (by simp) (by simp)
  have hne : ∀ᶠ u in 𝓝 (0 : ℂ), K u 1 ≠ -I :=
    hb.continuousAt.eventually_ne (by rw [hK0]; norm_num [Complex.ext_iff])
  obtain ⟨ρ, hρ, hρt⟩ := Metric.mem_nhds_iff.mp (inter_mem ht (hsq.and hne))
  exact ⟨ρ, hρ, hνt.mono fun u hu ↦ (hρt hu).1, fun u hu v ↦
    linearMap_apply_eq_I_mul (hρt hu).2.1 (hρt hu).2.2 v⟩

/-- A `C^(k+1)` normalizer admits arbitrarily small supported `C^(k, 1/2)` rescalings. -/
private theorem exists_small_ckHolder_normalizer (k : ℕ) {K : ℂ → ℂ →L[ℝ] ℂ}
    (hK : ContDiffAt ℝ (k + 1 : ℕ) K 0) (hsq : ∀ᶠ u in 𝓝 0, ∀ v, K u (K u v) = -v)
    (hK0 : K 0 1 = I) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > (0 : ℝ), ∃ f ∈ supportedCkHolderSubmodule (E := ℂ) (F := ℂ)
      k (1 / 2) (closedBall (0 : ℂ) 2), ‖f‖ < δ ∧
      ∀ w ∈ ball (0 : ℂ) 1,
        f w = (I - K (ε • w) 1) / (conj (K (ε • w) 1) - I) ∧
        ∀ v, linearMap (f w) (K (ε • w) v) = I * linearMap (f w) v := by
  obtain ⟨ρ, hρ, hν, hlin⟩ := exists_contDiffOn_normalizer_ball k hK hsq hK0
  let ν : ℂ → ℂ := fun u ↦ (I - K u 1) / (conj (K u 1) - I)
  have hsub : closedBall (0 : ℂ) (ρ / 2) ⊆ ball 0 ρ :=
    closedBall_subset_ball (by linarith)
  obtain ⟨H, hH⟩ := hν.exists_holderOnWith_iteratedFDeriv (α := 1 / 2) isOpen_ball
    (by norm_num) (isCompact_closedBall 0 (ρ / 2)) hsub
  let χ : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hsmall := eventually_exists_ckHolderSpace_cutoff_rescale (ℓ := k)
    (by norm_num : (0 : ℝ≥0) < 1 / 2) (by norm_num) (by linarith : 0 < ρ / 2)
    ((hν.of_le (by norm_cast; omega)).mono
      (ball_subset_ball (by linarith : ρ / 2 ≤ ρ)))
    (hH.mono ball_subset_closedBall) (by simp [hK0]) χ.contDiff χ.hasCompactSupport hδ
  obtain ⟨ε, ⟨⟨f, hf, hfχ, hfδ⟩, hερ⟩, hε⟩ :=
    (((hsmall.and (ball_mem_nhds (0 : ℝ) hρ)).filter_mono nhdsWithin_le_nhds).and
      self_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), _).exists
  rw [χ.tsupport_eq] at hf
  refine ⟨ε, hε, f, hf, hfδ, fun w hw ↦ ?_⟩
  have hu : ε • w ∈ ball (0 : ℂ) ρ := by
    rw [mem_ball_zero_iff, norm_smul]
    exact (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hw).le (norm_nonneg ε)).trans_lt
      (by simpa using hερ)
  have hfw : f w = ν (ε • w) := by
    rw [hfχ, χ.one_of_mem_closedBall (ball_subset_closedBall hw), one_smul]
  exact ⟨hfw, fun v ↦ by rw [hfw]; exact hlin _ hu v⟩

/-- Small supported coefficients produce centred finite-order local diffeomorphisms. -/
private theorem exists_ckHolder_isothermal_chart (k : ℕ) :
    ∃ δ > (0 : ℝ), ∀ f ∈ supportedCkHolderSubmodule (E := ℂ) (F := ℂ)
      k (1 / 2) (closedBall (0 : ℂ) 2), ‖f‖ < δ →
      ∃ e : OpenPartialHomeomorph ℂ ℂ, (0 : ℂ) ∈ e.source ∧ e 0 = 0 ∧
        ContDiffOn ℝ (k + 1 : ℕ) e e.source ∧
        ContDiffOn ℝ (k + 1 : ℕ) e.symm e.target ∧
        e.source ⊆ ball 0 1 ∧
        ∀ z, ∀ (J : AlmostComplexStructure ℂ)
          (hJ : stdComplexSymplecticForm.Tames J), (coefficientEquiv ⟨J, hJ⟩).val = f z →
          ∀ v, fderiv ℝ e z (J v) = I * fderiv ℝ e z v := by
  obtain ⟨δ, hδ, C, hsolve⟩ :=
    exists_ckHolder_conjWirtingerDeriv_eq_mul_wirtingerDeriv k
      (by norm_num : (0 : ℝ≥0) < 1 / 2) (by norm_num) (0 : ℂ) 2
  refine ⟨δ, hδ, fun f hf hfδ ↦ ?_⟩
  obtain ⟨h, -, -, hψ, -, hpde, -, -, -, hinv⟩ := hsolve f hf hfδ
  let ψ : ℂ → ℂ := fun w ↦ w + cauchyTransform h w
  obtain ⟨L, hL⟩ := hinv 0 (mem_closedBall_self (by norm_num))
  have hshift : ContDiff ℝ (k + 1 : ℕ) (fun w ↦ ψ w - ψ 0) := hψ.sub contDiff_const
  obtain ⟨e, he, he0, hes, hec⟩ := TauCeti.ContDiffOn.exists_openPartialHomeomorph
    (s := ball (0 : ℂ) 1) hshift.contDiffOn isOpen_ball (mem_ball_self one_pos)
    (by exact_mod_cast Nat.le_add_left 1 k) (hL.sub_const (ψ 0)).hasFDerivAt.fderiv.symm
  have hd (z : ℂ) : fderiv ℝ e z = fderiv ℝ ψ z := by
    rw [he, fderiv_sub_const]
  refine ⟨e, he0, by rw [he]; exact sub_self _, by rw [he]; exact hshift.contDiffOn,
    hec, hes, fun z J hJ hJf v ↦ ?_⟩
  have hlin := (isComplexLinear_iff_conjWirtingerDeriv_eq J hJ ψ z).mpr
    (by rw [hJf]; exact hpde z)
  rw [hd]
  simpa only [ContinuousLinearMap.coe_coe, AlmostComplexStructure.ofComplexModule_apply,
    smul_eq_mul] using hlin.apply v

/-- A `C^(k+1)` field equal to `i` at zero admits rescaled isothermal charts of that order. -/
private theorem exists_finite_order_isothermal_chart_rescale (k : ℕ) {K : ℂ → ℂ →L[ℝ] ℂ}
    (hK : ContDiffAt ℝ (k + 1 : ℕ) K 0) (hsq : ∀ᶠ u in 𝓝 0, ∀ v, K u (K u v) = -v)
    (hK0 : K 0 1 = I) :
    ∃ ε > (0 : ℝ), ∃ e : OpenPartialHomeomorph ℂ ℂ, (0 : ℂ) ∈ e.source ∧ e 0 = 0 ∧
      ContDiffOn ℝ (k + 1 : ℕ) e e.source ∧
      ContDiffOn ℝ (k + 1 : ℕ) e.symm e.target ∧
      ∀ w ∈ e.source, ∀ v, fderiv ℝ e w (K (ε • w) v) = I * fderiv ℝ e w v := by
  obtain ⟨δ, hδ, hchart⟩ := exists_ckHolder_isothermal_chart k
  obtain ⟨ε, hε, f, hf, hfδ, hfK⟩ :=
    exists_small_ckHolder_normalizer k hK hsq hK0 (lt_min hδ one_pos)
  have hf1 (w : ℂ) : ‖f w‖ < 1 :=
    (f.norm_apply_le w).trans_lt (hfδ.trans_le (min_le_right _ _))
  obtain ⟨e, he0, heval, he, heSym, hes, hlin⟩ :=
    hchart f hf (hfδ.trans_le (min_le_left _ _))
  let Jf (w : ℂ) : AlmostComplexStructure ℂ := (coefficientEquiv.symm ⟨f w, hf1 w⟩).val
  have hJfK (w : ℂ) (hw : w ∈ e.source) (v : ℂ) : Jf w v = K (ε • w) v := by
    simp only [Jf, coefficientEquiv_symm_apply]
    rw [ContinuousLinearEquiv.symm_apply_eq, linearEquiv_apply, linearEquiv_apply]
    simpa only [linearMap_apply] using ((hfK w (hes hw)).2 v).symm
  refine ⟨ε, hε, e, he0, heval, he, heSym, fun w hw v ↦ ?_⟩
  rw [← hJfK w hw v]
  exact hlin w (Jf w) (coefficientEquiv.symm _).property (by simp [Jf]) v

/-- A planar field of either orientation which is `C^(k+1)` at a point has a centred
local isothermal chart of the same order. -/
theorem exists_isothermal_chart_finite_order (k : ℕ) {J : ℂ → ℂ →L[ℝ] ℂ} {c : ℂ}
    (hJ : ContDiffAt ℝ (k + 1 : ℕ) J c) (hsq : ∀ᶠ z in 𝓝 c, ∀ v, J z (J z v) = -v) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, c ∈ e.source ∧ e c = 0 ∧
      ContDiffOn ℝ (k + 1 : ℕ) e e.source ∧
      (∀ z ∈ e.source, (fderiv ℝ e z).IsInvertible) ∧
      ∀ z ∈ e.source, ∀ v, fderiv ℝ e z (J z v) = I * fderiv ℝ e z v := by
  obtain ⟨B, hK, hKsq, hK0, hconj⟩ := exists_standardizing_equiv hJ hsq
  let K : ℂ → ℂ →L[ℝ] ℂ := fun u ↦ (B.symm.arrowCongr B.symm) (J (c + B u))
  obtain ⟨ε, hε, e, he0, heval, he, heSym, heK⟩ :=
    exists_finite_order_isothermal_chart_rescale k hK hKsq hK0
  obtain ⟨F, hFs, hFval, hFc, hFsc, hFJ⟩ := exists_isothermal_chart_comp_affine
    (J := J) (K := fun w ↦ K (ε • w)) (by exact_mod_cast Nat.le_add_left 1 k)
    (fun w hw ↦ he.contDiffAt (e.open_source.mem_nhds hw))
    (fun w hw ↦ heSym.contDiffAt (e.open_target.mem_nhds hw)) heK
    (B.symm.trans (ContinuousLinearEquiv.smulLeft (Units.mk0 (ε⁻¹ : ℝ) (inv_ne_zero hε.ne')))) c
    (fun z _ v ↦ hconj ε hε.ne' z v)
  refine ⟨F, (hFs c).mpr (by simpa using he0), by simpa [hFval] using heval,
    fun z hz ↦ (hFc z hz).contDiffWithinAt, fun z hz ↦ ?_, hFJ⟩
  exact F.isInvertible_fderiv hz ((hFc z hz).differentiableAt (by simp))
    ((hFsc _ (F.map_source hz)).differentiableAt (by simp))

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
  obtain ⟨e, hc, -, he, hinv, hlin⟩ := exists_isothermal_chart_finite_order 0 hJ hsq
  have hes := e.contDiffOn_symm_of_isInvertible_fderiv he hinv
  exact ⟨e, hc, fun z hz ↦ he.contDiffAt (e.open_source.mem_nhds hz),
    fun z hz ↦ hes.contDiffAt (e.open_target.mem_nhds hz), hlin⟩

/-- A `C¹` isothermal chart and its inverse are smooth for a smooth field. -/
theorem contDiffOn_infty_and_symm_of_contDiffOn_field {J : ℂ → ℂ →L[ℝ] ℂ}
    {e : OpenPartialHomeomorph ℂ ℂ} (hJ : ContDiffOn ℝ ∞ J e.source)
    (hsq : ∀ z ∈ e.source, ∀ v, J z (J z v) = -v)
    (he : ContDiffOn ℝ 1 e e.source) (hes : ContDiffOn ℝ 1 e.symm e.target)
    (hlin : ∀ z ∈ e.source, ∀ v, fderiv ℝ e z (J z v) = I * fderiv ℝ e z v) :
    ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have h : ContDiffOn ℝ ∞ e e.source := by
    refine contDiffOn_infty_of_fderiv_comp (he.differentiableOn one_ne_zero) hlin fun z hz m ↦ ?_
    obtain ⟨e', hz', -, hc', hi', hJ'⟩ := exists_isothermal_chart_finite_order m
      ((hJ.contDiffAt (e.open_source.mem_nhds hz)).of_le (by simp))
      (eventually_of_mem (e.open_source.mem_nhds hz) fun y hy ↦ hsq y hy)
    exact ⟨e', hz', hc'.of_le (by exact_mod_cast Nat.le_succ m), hi', hJ'⟩
  refine ⟨h, e.contDiffOn_symm_of_isInvertible_fderiv h fun z hz ↦ ?_⟩
  exact e.isInvertible_fderiv hz
    ((he.contDiffAt (e.open_source.mem_nhds hz)).differentiableAt one_ne_zero)
    ((hes.contDiffAt (e.open_target.mem_nhds (e.map_source hz))).differentiableAt one_ne_zero)

/-- A smooth field of complex structures of either orientation has smooth local coordinates. -/
private theorem exists_smooth_isothermal_chart {J : ℂ → ℂ →L[ℝ] ℂ} {U : Set ℂ} {c : ℂ}
    (hJ : ContDiffOn ℝ ∞ J U) (hU : IsOpen U) (hc : c ∈ U)
    (hsq : ∀ z ∈ U, ∀ v, J z (J z v) = -v) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, c ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ z ∈ e.source, ∀ v, fderiv ℝ e z (J z v) = I * fderiv ℝ e z v := by
  obtain ⟨e, hce, he, hes, hlin⟩ := exists_isothermal_chart_of_contDiffAt_of_sq_eq_neg_one
    ((hJ.contDiffAt (hU.mem_nhds hc)).of_le (by simp))
    (eventually_of_mem (hU.mem_nhds hc) fun z hz ↦ hsq z hz)
  let E := e.restrOpen U hU
  have hEs : E.source ⊆ U := fun z hz ↦ hz.2
  have hEc : ContDiffOn ℝ 1 E E.source := fun z hz ↦ (he z hz.1).contDiffWithinAt
  have hEsc : ContDiffOn ℝ 1 E.symm E.target := fun w hw ↦
    (hes w hw.1).contDiffWithinAt
  have hElin : ∀ z ∈ E.source, ∀ v,
      fderiv ℝ E z (J z v) = I * fderiv ℝ E z v := fun z hz v ↦ hlin z hz.1 v
  obtain ⟨hE, hEsym⟩ := contDiffOn_infty_and_symm_of_contDiffOn_field (hJ.mono hEs)
    (fun z hz ↦ hsq z (hEs hz)) hEc hEsc hElin
  exact ⟨E, ⟨hce, hc⟩, hEs, hE, hEsym, hElin⟩

/-- Smooth isothermal coordinates can be centred at the prescribed point. -/
theorem exists_centered_smooth_isothermal_chart {J : ℂ → ℂ →L[ℝ] ℂ} {U : Set ℂ} {c : ℂ}
    (hJ : ContDiffOn ℝ ∞ J U) (hU : IsOpen U) (hc : c ∈ U)
    (hsq : ∀ z ∈ U, ∀ v, J z (J z v) = -v) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, c ∈ e.source ∧ e c = 0 ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ z ∈ e.source, ∀ v, fderiv ℝ e z (J z v) = I * fderiv ℝ e z v := by
  obtain ⟨e, hce, hesub, he, hes, hlin⟩ := exists_smooth_isothermal_chart hJ hU hc hsq
  let E := e.trans (Homeomorph.subRight (e c)).toOpenPartialHomeomorph
  have hE : ⇑E = fun z ↦ e z - e c := by ext z; simp [E]
  have hEs : E.source = e.source := by simp [E]
  have hEc : ContDiffOn ℝ ∞ E E.source := by rw [hE, hEs]; exact he.sub contDiffOn_const
  have hEd (z : ℂ) : fderiv ℝ E z = fderiv ℝ e z := by rw [hE, fderiv_sub_const]
  have hEsym : ContDiffOn ℝ ∞ E.symm E.target := by
    intro w hw
    dsimp only [E] at hw ⊢
    rw [OpenPartialHomeomorph.trans_target] at hw
    rw [OpenPartialHomeomorph.coe_trans_symm]
    exact ((hes.contDiffAt (e.open_target.mem_nhds hw.2)).comp w
      (contDiffAt_id.add contDiffAt_const)).contDiffWithinAt
  refine ⟨E, hEs.symm ▸ hce, by rw [hE]; exact sub_self _, hEs.symm ▸ hesub,
    hEc, hEsym, fun z hz v ↦ ?_⟩
  rw [hEd]
  exact hlin z (hEs ▸ hz) v

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
