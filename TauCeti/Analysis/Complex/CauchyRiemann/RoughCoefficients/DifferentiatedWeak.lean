/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Differentiated
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.Local.Multiplication.Higher
import TauCeti.Analysis.Sobolev.Mollification.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Function.Lp.Holder

/-!
# The differentiated Cauchy–Riemann system as a weak equation

Write `z = s + i t` and consider `D ξ = ∂_s ξ + J ∂_t ξ + S ξ` with Sobolev coefficients
`J, S ∈ W^{1,p}_loc(Ω; V →L[ℝ] V)` on an open `Ω ⊆ ℂ`, where `V` is a finite-dimensional real inner
product space, `p > 2` and `1/p + 1/q ≤ 1`. Interior regularity for `D` is proved by induction on
the order (McDuff–Salamon, Proposition B.4.9, Steps 2 and 3): if `D ξ = η`, then
`Ξ = (∂_s ξ, ∂_t ξ)` solves

`∂_s Ξ + J₂ ∂_t Ξ + S₂ Ξ = (∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)`,

with `J₂ = diag(J, J)` and `S₂ = [[S, ∂_s J], [0, S + ∂_t J]]`
(`TauCeti.differentiatedCRCoefficient`). `TauCeti.ae_differentiated_cauchyRiemann` proves this
almost everywhere for `ξ ∈ W^{2,q}_loc`. The induction step starts one order lower, from
`ξ ∈ W^{1,q}_loc`, and applies the order-zero regularity to `(J₂, S₂)`; for that it needs `Ξ` as a
*weak* solution in the sense of `TauCeti.IsWeakCRSolution`, which this file proves.

`IsWeakCRSolution` needs an inner product on the target, and `V × V` carries the sup norm, so the
system lives on the Euclidean product `WithLp 2 (V × V)`: operators on `V × V` are transported by
`TauCeti.euclideanProdArrowCongr`, and `J₂` is `TauCeti.differentiatedCRStructureL J`.

The proof tests `D ξ = η` against `∂_v φ` for a test function `φ` and moves the derivative across
`ξ`. The one step that is not algebra is the symmetry of mixed partials of `ξ ∈ W^{1,q}_loc`
against a compactly supported `ψ ∈ W^{1,p}`, applied to `ψ = φ` and to `ψ = Jᵀ φ`:
`∫ ⟪∂_v ψ, ∂_w ξ⟫ = ∫ ⟪∂_w ψ, ∂_v ξ⟫`. For test functions both sides are `-∫ ⟪∂_v ∂_w ψ, ξ⟫`; in
general `ψ` is mollified and the limit is taken by Hölder's inequality.

## Main results

* `TauCeti.IsSobolevCRCoefficients.differentiated`: `(J₂, diag(DJ, DJ), S₂)` are Sobolev
  Cauchy–Riemann coefficients whenever `(J, DJ, S)` are.
* `TauCeti.isWeakCRSolution_differentiated`: `Ξ` is a weak solution of the differentiated system.
* `TauCeti.memWkpLoc_differentiatedCR_rightSide`: the right side is in `W^{k,q}_loc` when
  `S ∈ W^{k+1,p}_loc` and `ξ, η ∈ W^{k+1,q}_loc`.
* `TauCeti.differentiatedCRStructureL_mul_self`: `J₂² = -1` whenever `J² = -1`.
* `TauCeti.isWeakCRSolution_differentiated_const`: for constant `J = A` and `S = 0` the system is
  the original operator on each component.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Proposition B.4.9.
-/

public noncomputable section

open Complex MeasureTheory TopologicalSpace Filter Metric Set
open LineDeriv
open scoped ENNReal NNReal InnerProductSpace Distributions Convolution Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ}

/-! ### The coefficients on the Euclidean product -/

section Transport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Operators on `E × E` act on the Euclidean product `WithLp 2 (E × E)`, which carries the same
vector space structure and, for an inner product space `E`, the product inner product. -/
@[expose] def euclideanProdArrowCongr :
    (E × E →L[ℝ] E × E) ≃L[ℝ] (WithLp 2 (E × E) →L[ℝ] WithLp 2 (E × E)) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.arrowCongr
    (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm

@[simp]
theorem euclideanProdArrowCongr_apply (A : E × E →L[ℝ] E × E) (x : WithLp 2 (E × E)) :
    euclideanProdArrowCongr A x = WithLp.toLp 2 (A (WithLp.ofLp x)) :=
  rfl

/-- The coefficient `J₂ = diag(J, J)` of the differentiated Cauchy–Riemann system, as a
continuous linear function of `J`, acting on the Euclidean product `WithLp 2 (E × E)`. -/
@[expose] def differentiatedCRStructureL :
    (E →L[ℝ] E) →L[ℝ] (WithLp 2 (E × E) →L[ℝ] WithLp 2 (E × E)) :=
  (euclideanProdArrowCongr (E := E)).toContinuousLinearMap.comp
    ((ContinuousLinearMap.prodMapL ℝ E E E E).comp
      ((ContinuousLinearMap.id ℝ (E →L[ℝ] E)).prod (ContinuousLinearMap.id ℝ (E →L[ℝ] E))))

@[simp]
theorem differentiatedCRStructureL_apply (A : E →L[ℝ] E) (x : WithLp 2 (E × E)) :
    differentiatedCRStructureL A x =
      WithLp.toLp 2 (A (WithLp.ofLp x).1, A (WithLp.ofLp x).2) := by
  simp [differentiatedCRStructureL]
  rfl

/-- `J₂ = diag(J, J)` is a complex structure whenever `J` is. -/
theorem differentiatedCRStructureL_mul_self {A : E →L[ℝ] E} (hA : A * A = -1) :
    differentiatedCRStructureL A * differentiatedCRStructureL A = -1 := by
  have h (v : E) : A (A v) = -v := by simpa using congr($hA v)
  refine ContinuousLinearMap.ext fun x => WithLp.ofLp_injective 2 (Prod.ext ?_ ?_) <;> simp [h]

end Transport

/-! ### Mixed partial derivatives against a compactly supported Sobolev field -/

/-- For a test function `χ` and a weakly differentiable `ξ`, the pairings `⟪∂_v χ, ∂_w ξ⟫` and
`⟪∂_w χ, ∂_v ξ⟫` have the same integral: both are `-∫ ⟪∂_v ∂_w χ, ξ⟫`. -/
private theorem integral_inner_fderiv_comm_testFunction {ξ : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V}
    (hξ : HasWeakFDerivOn volume Ω ξ Dξ) (χ : 𝓓(Ω, V)) (v w : ℂ) :
    ∫ z, ⟪fderiv ℝ (χ : ℂ → V) z v, Dξ z w⟫_ℝ = ∫ z, ⟪fderiv ℝ (χ : ℂ → V) z w, Dξ z v⟫_ℝ := by
  have h₁ := (hξ.hasWeakLineDerivOn w).integral_inner_lineDeriv_eq_neg (∂_{v} χ)
  have h₂ := (hξ.hasWeakLineDerivOn v).integral_inner_lineDeriv_eq_neg (∂_{w} χ)
  simp only [TestFunction.lineDeriv_lineDerivOp_comm χ v w,
    TestFunction.lineDerivOp_apply_eq_fderiv] at h₁ h₂
  linarith

/-- Mollifying a field vanishing off `K` by a bump of outer radius `r` gives a field supported in
the closed `r`-thickening of `K`. -/
private theorem tsupport_convolution_subset_cthickening {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {K : Set ℂ} (φ : ContDiffBump (0 : ℂ)) {f : ℂ → F}
    (hf : ∀ z ∉ K, f z = 0) :
    tsupport (f ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] φ.normed volume) ⊆
      cthickening φ.rOut K := by
  refine closure_minimal ((support_convolution_subset _).trans ?_) isClosed_cthickening
  rw [φ.support_normed_eq]
  rintro _ ⟨a, ha, b, hb, rfl⟩
  refine mem_cthickening_of_dist_le _ a _ K (by_contra fun h => ha (hf a h)) ?_
  simpa [dist_eq_norm] using (mem_ball_zero_iff.1 hb).le

omit [FiniteDimensional ℝ V] in
/-- The derivative of the mollification of a compactly supported weakly differentiable field
`ψ` vanishing off `K ⊆ Ω` is the mollification of its weak derivative, everywhere, once the
radius is at most half of a `δ` with `cthickening δ K ⊆ Ω`. -/
private theorem fderiv_convolution_eq_of_compact {ψ : ℂ → V} {Dψ : ℂ → ℂ →L[ℝ] V} {K : Set ℂ}
    (hψK : ∀ z ∉ K, ψ z = 0) (hDψK : ∀ z ∉ K, Dψ z = 0)
    (hψ : HasWeakFDerivOn volume Ω ψ Dψ) (hψi : LocallyIntegrable ψ volume)
    (hDψi : LocallyIntegrable Dψ volume) {δ : ℝ} (hδ : 0 < δ) (hδΩ : cthickening δ K ⊆ Ω)
    (φ : ContDiffBump (0 : ℂ)) (hφ : φ.rOut ≤ δ / 2) (x : ℂ) :
    fderiv ℝ (ψ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] φ.normed volume) x =
      (Dψ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] φ.normed volume) x := by
  by_cases hx : x ∈ cthickening (δ / 2) K
  · refine hψ.fderiv_convolution_right hψi hDψi _ φ.contDiff_normed φ.hasCompactSupport_normed x
      fun y hy => hδΩ ?_
    rw [φ.tsupport_normed_eq] at hy
    have h := cthickening_cthickening_subset φ.rOut_pos.le (half_pos hδ).le K
      (mem_cthickening_of_dist_le (x - y) x _ _ hx (by simpa [dist_eq_norm] using hy))
    exact cthickening_mono (by linarith) K h
  · have hx' : x ∉ cthickening φ.rOut K := fun h => hx (cthickening_mono hφ K h)
    rw [fderiv_of_notMem_tsupport ℝ fun h => hx' (tsupport_convolution_subset_cthickening φ hψK h),
      image_eq_zero_of_notMem_tsupport fun h =>
        hx' (tsupport_convolution_subset_cthickening φ hDψK h)]

/-- **Mixed partial derivatives against a compactly supported Sobolev field.** Let `ψ` vanish off
a compact `K ⊆ Ω` together with its weak derivative `Dψ ∈ Lᵖ_loc`, and let `ξ` have weak
derivative `Dξ ∈ L^q_loc` on `Ω`, with `1/p + 1/q ≤ 1` and `p < ∞`. Then
`∫ ⟪∂_v ψ, ∂_w ξ⟫ = ∫ ⟪∂_w ψ, ∂_v ξ⟫`. The proof mollifies `ψ` into test functions, for which this
is `TauCeti.integral_inner_fderiv_comm_testFunction`, and passes to the limit by Hölder's
inequality on a compact neighbourhood of `K`. -/
private theorem integral_inner_comm_of_compact {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (hp : p ≠ ⊤) {ψ ξ : ℂ → V} {Dψ Dξ : ℂ → ℂ →L[ℝ] V} {K : Set ℂ}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hψK : ∀ z ∉ K, ψ z = 0) (hDψK : ∀ z ∉ K, Dψ z = 0)
    (hψ : HasWeakFDerivOn volume Ω ψ Dψ) (hDψp : MemLpLoc p Ω Dψ)
    (hξ : HasWeakFDerivOn volume Ω ξ Dξ) (hDξq : MemLpLoc q Ω Dξ) (v w : ℂ) :
    ∫ z, ⟪Dψ z v, Dξ z w⟫_ℝ = ∫ z, ⟪Dψ z w, Dξ z v⟫_ℝ := by
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open Ω.isOpen hKΩ
  have : Fact (1 ≤ (p⁻¹ + q⁻¹)⁻¹) := ⟨ENNReal.one_le_inv.2 hpq⟩
  have : ENNReal.HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ := ⟨(inv_inv _).symm⟩
  have hψi : Integrable ψ :=
    (hψ.locallyIntegrableOn.integrableOn_compact_subset hKΩ hK).integrable_of_forall_notMem_eq_zero
      hψK
  have hDψ : MemLp Dψ p volume := by
    have h := (memLp_indicator_iff_restrict hK.measurableSet.nullMeasurableSet).2
      (memLpLoc_iff.1 hDψp K hKΩ hK)
    rwa [indicator_eq_self.2 fun z hz => by_contra fun h => hz (hDψK z h)] at h
  have hDψi : LocallyIntegrable Dψ volume := hDψ.locallyIntegrable Fact.out
  -- The compact neighbourhood `W` of `K` on which the limit is taken.
  set W := cthickening (δ / 2) K
  have hWc : IsCompact W := hK.cthickening
  have hWΩ : W ⊆ Ω := (cthickening_mono (by linarith) K).trans hδΩ
  have : IsFiniteMeasure (volume.restrict W) := isFiniteMeasure_restrict.2 hWc.measure_lt_top.ne
  have hKW : K ⊆ W := self_subset_cthickening K
  have hDξW : MemLp (W.indicator Dξ) q volume :=
    (memLp_indicator_iff_restrict hWc.measurableSet.nullMeasurableSet).2
      (memLpLoc_iff.1 hDξq W hWΩ hWc)
  -- Normalized bumps with outer radii `δ / 2 / (n + 1)`.
  let φ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨δ / 2 * (1 / ((n : ℝ) + 1)) / 2, δ / 2 * (1 / ((n : ℝ) + 1)), by positivity,
      half_lt_self (by positivity)⟩
  have hφ (n : ℕ) : (φ n).rOut ≤ δ / 2 :=
    mul_le_of_le_one_right (by positivity) (div_le_one_of_le₀ (by simp) (by positivity))
  have hφ0 : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (δ / 2)
    rw [mul_zero] at h
    exact h
  -- The mollified fields are test functions whose derivatives mollify `Dψ`.
  let a (n : ℕ) := (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Dψ
  have hfd (n : ℕ) : fderiv ℝ (ψ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume]
      (φ n).normed volume) = a n := by
    funext x
    rw [fderiv_convolution_eq_of_compact hψK hDψK hψ hψi.locallyIntegrable hDψi hδ hδΩ (φ n)
      (hφ n) x, convolution_flip]
  have hsuppW (n : ℕ) :
      tsupport (ψ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] (φ n).normed volume) ⊆ W :=
    (tsupport_convolution_subset_cthickening (φ n) hψK).trans (cthickening_mono (hφ n) K)
  have hsuppW' (n : ℕ) :
      tsupport (Dψ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] (φ n).normed volume) ⊆ W :=
    (tsupport_convolution_subset_cthickening (φ n) hDψK).trans (cthickening_mono (hφ n) K)
  let χ (n : ℕ) : 𝓓(Ω, V) :=
    ⟨ψ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] (φ n).normed volume,
      (φ n).hasCompactSupport_normed.contDiff_convolution_right _ hψi.locallyIntegrable
        (φ n).contDiff_normed,
      hWc.of_isClosed_subset (isClosed_tsupport _) (hsuppW n), (hsuppW n).trans hWΩ⟩
  have ha0 (n : ℕ) (z : ℂ) (hz : z ∉ W) : a n z = 0 := by
    simp only [a]
    rw [← convolution_flip]
    exact image_eq_zero_of_notMem_tsupport fun h => hz (hsuppW' n h)
  -- Each mollification satisfies the identity.
  have hn (n : ℕ) : ∫ z, ⟪a n z v, Dξ z w⟫_ℝ = ∫ z, ⟪a n z w, Dξ z v⟫_ℝ := by
    have h := integral_inner_fderiv_comm_testFunction hξ (χ n) v w
    have hχ : (χ n : ℂ → V) =
        ψ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] (φ n).normed volume := rfl
    rwa [hχ, hfd] at h
  -- Passing to the limit on `W`.
  have hlim (v w : ℂ) : Tendsto (fun n => ∫ z, ⟪a n z v, Dξ z w⟫_ℝ) atTop
      (𝓝 (∫ z, ⟪Dψ z v, Dξ z w⟫_ℝ)) := by
    let B : (ℂ →L[ℝ] V) →L[ℝ] (ℂ →L[ℝ] V) →L[ℝ] ℝ :=
      (innerSL ℝ).bilinearComp (ContinuousLinearMap.apply ℝ V v)
        (ContinuousLinearMap.apply ℝ V w)
    have hB (x y : ℂ →L[ℝ] V) : B x y = ⟪x v, y w⟫_ℝ := rfl
    have hW (f : ℂ → ℂ →L[ℝ] V) (hf : ∀ z ∉ W, f z = 0) :
        ∫ z, ⟪f z v, Dξ z w⟫_ℝ = ∫ z in W, B (f z) (W.indicator Dξ z) := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by simp [hf z hz]]
      exact setIntegral_congr_fun hWc.measurableSet fun z hz => by
        simp [hB, indicator_of_mem hz]
    simp only [hW _ (ha0 _), hW Dψ fun z hz => hDψK z fun h => hz (hKW h)]
    refine tendsto_integral_of_L1 _
      ((B.memLp_of_bilin (p⁻¹ + q⁻¹)⁻¹ hDψ hDξW).restrict W).aestronglyMeasurable
      (.of_forall fun n => ?_) ?_
    · have hA := Lp.memLp (normedBumpLp hp (φ n) volume (hDψ.toLp Dψ))
      have hA' : MemLp (a n) p volume := hA.ae_eq (normedBumpLp_ae_eq_convolution hp (φ n) hDψ)
      exact ((B.memLp_of_bilin (p⁻¹ + q⁻¹)⁻¹ hA' hDξW).restrict W).integrable Fact.out
    · exact tendsto_setLIntegral_enorm_bilin_sub (r := (p⁻¹ + q⁻¹)⁻¹) B hWc.measure_lt_top
        (tendsto_normedBumpLp hp hφ0 (hDψ.toLp Dψ)) tendsto_const_nhds
        (fun n => normedBumpLp_ae_eq_convolution hp (φ n) hDψ)
        (ae_restrict_of_ae hDψ.coeFn_toLp) (fun _ => hDξW.coeFn_toLp)
        (ae_restrict_of_ae hDξW.coeFn_toLp)
  exact tendsto_nhds_unique (hlim v w) ((hlim w v).congr fun n => (hn n).symm)

/-! ### One component of the differentiated system -/

/-- The adjoint, as a continuous linear map on the real operators of `V`. -/
private def adjointL : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap
    { toFun := ContinuousLinearMap.adjoint
      map_add' := map_add _
      map_smul' := fun c A => by simp }

private theorem adjointL_apply (A : V →L[ℝ] V) : adjointL A = ContinuousLinearMap.adjoint A :=
  rfl

/-- `1/p + 1/q ≤ 1` with `p` finite forces `1 < q`. -/
private theorem one_lt_of_inv_add_inv_le_one {p q : ℝ≥0}
    (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ ≤ 1) : 1 < q := by
  by_contra! h
  have h1 : (1 : ℝ≥0∞) ≤ (q : ℝ≥0∞)⁻¹ := ENNReal.one_le_inv.2 (by exact_mod_cast h)
  have h2 : (0 : ℝ≥0∞) < (p : ℝ≥0∞)⁻¹ := ENNReal.inv_pos.2 ENNReal.coe_ne_top
  have hq : (q : ℝ≥0∞)⁻¹ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans hpq)
  have h3 : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ ≤ 0 + (q : ℝ≥0∞)⁻¹ := by
    rw [zero_add]
    exact hpq.trans h1
  exact h2.ne' (le_antisymm ((ENNReal.add_le_add_iff_right hq).1 h3) zero_le)

/-- **One component of the differentiated system, weakly.** Under the hypotheses of
`TauCeti.isWeakCRSolution_differentiated`, for a test function `φ` and a direction `v`, the
pairing of `φ` with the `v`-component of the differentiated system integrates to
`∫ ⟪φ, ∂_v η - (∂_v S) ξ⟫`. Writing `ξ_v = ∂_v ξ`, the integrand is
`-⟪∂_s φ, ξ_v⟫ - ⟪∂_t φ, J ξ_v⟫ - ⟪φ, (∂_t J) ξ_v⟫ + ⟪φ, S ξ_v⟫ + ⟪φ, (∂_v J) ξ_t⟫`. The proof tests
the equation against `∂_v φ` and moves the derivative across `ξ` with the commutation of mixed
partials (`TauCeti.integral_inner_comm_of_compact`), applied to `φ` and to `Jᵀ φ`. -/
private theorem integral_differentiated_component {p q : ℝ≥0} (hp : 2 < p)
    (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ ≤ 1) (hqp : q ≤ p)
    {J S : ℂ → V →L[ℝ] V} {DJ DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    {Dξ Dη : ℂ → ℂ →L[ℝ] V}
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hη : MemWkpLoc q Ω 1 η) (hDη : HasWeakFDerivOn volume Ω η Dη)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z)
    (φ : 𝓓(Ω, V)) (v : ℂ) :
    Integrable (fun z => -⟪fderiv ℝ (φ : ℂ → V) z 1, Dξ z v⟫_ℝ -
        ⟪fderiv ℝ (φ : ℂ → V) z I, J z (Dξ z v)⟫_ℝ - ⟪(φ : ℂ → V) z, DJ z I (Dξ z v)⟫_ℝ +
        ⟪(φ : ℂ → V) z, S z (Dξ z v)⟫_ℝ + ⟪(φ : ℂ → V) z, DJ z v (Dξ z I)⟫_ℝ) ∧
    ∫ z, (-⟪fderiv ℝ (φ : ℂ → V) z 1, Dξ z v⟫_ℝ -
        ⟪fderiv ℝ (φ : ℂ → V) z I, J z (Dξ z v)⟫_ℝ - ⟪(φ : ℂ → V) z, DJ z I (Dξ z v)⟫_ℝ +
        ⟪(φ : ℂ → V) z, S z (Dξ z v)⟫_ℝ + ⟪(φ : ℂ → V) z, DJ z v (Dξ z I)⟫_ℝ) =
      ∫ z, ⟪(φ : ℂ → V) z, Dη z v - DS z v (ξ z)⟫_ℝ := by
  have hq := one_lt_of_inv_add_inv_le_one hpq
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq.le⟩
  have : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hq.le.trans hqp⟩
  have hloc := Ω.isOpen.isLocallyClosed
  have hφc : ContinuousOn (φ : ℂ → V) Ω := φ.continuous.continuousOn
  have hφ' : Continuous (fderiv ℝ (φ : ℂ → V)) := φ.contDiff.continuous_fderiv (by simp)
  have hφw : HasWeakFDerivOn volume Ω (φ : ℂ → V) (fderiv ℝ (φ : ℂ → V)) :=
    hasWeakFDerivOn_of_differentiableOn (hφ'.continuousOn.locallyIntegrableOn
      Ω.isOpen.measurableSet) fun z _ => φ.contDiff.differentiable (by simp) z
  have hfK (z : ℂ) (hz : z ∉ tsupport (φ : ℂ → V)) : (φ : ℂ → V) z = 0 :=
    image_eq_zero_of_notMem_tsupport hz
  have hfK' (z : ℂ) (hz : z ∉ tsupport (φ : ℂ → V)) : fderiv ℝ (φ : ℂ → V) z = 0 :=
    fderiv_of_notMem_tsupport ℝ hz
  have hDξq := hξ.memLpLoc_of_hasWeakFDerivOn hDξ
  have hDηq := hη.memLpLoc_of_hasWeakFDerivOn hDη
  have hpart (u : ℂ) : MemLpLoc q Ω (fun z => Dξ z u) :=
    hDξq.clm_comp (ContinuousLinearMap.apply ℝ V u)
  have hJp : MemLpLoc p Ω J := hJ.memLpLoc
  have hSp : MemLpLoc p Ω S := hS.memLpLoc
  have hDJp := hJ.memLpLoc_of_hasWeakFDerivOn hDJ
  have hDSp := hS.memLpLoc_of_hasWeakFDerivOn hDS
  have hDJu (u : ℂ) : MemLpLoc p Ω (fun z => DJ z u) :=
    hDJp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) u)
  have hDSu (u : ℂ) : MemLpLoc p Ω (fun z => DS z u) :=
    hDSp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) u)
  have li : ∀ {A : ℂ → V →L[ℝ] V} {g : ℂ → V}, MemLpLoc p Ω A → MemLpLoc q Ω g →
      LocallyIntegrableOn (fun z => A z (g z)) Ω := fun hA hg =>
    hA.locallyIntegrableOn_clm_apply hg hpq hloc
  have lq : ∀ {g : ℂ → V}, MemLpLoc q Ω g → LocallyIntegrableOn g Ω := fun hg =>
    hg.locallyIntegrableOn Fact.out hloc
  have i1 := φ.integrable_inner_fderiv (lq (hpart v)) 1
  have i2 := φ.integrable_inner_fderiv (li hJp (hpart v)) I
  have i3 := φ.integrable_inner (li (hDJu I) (hpart v))
  have i4 := φ.integrable_inner (li hSp (hpart v))
  have i5 := φ.integrable_inner (li (hDJu v) (hpart I))
  have i6 := φ.integrable_inner (lq (hDηq.clm_comp (ContinuousLinearMap.apply ℝ V v)))
  have i7 := φ.integrable_inner (li (hDSu v) hξ.memLpLoc)
  have u1 := φ.integrable_inner_fderiv (lq (hpart 1)) v
  have u2 := φ.integrable_inner_fderiv (li hJp (hpart I)) v
  have u3 := φ.integrable_inner_fderiv (li hSp hξ.memLpLoc) v
  -- Testing the derivative of `η` against `φ`.
  have hA : ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z v, η z⟫_ℝ = -∫ z, ⟪(φ : ℂ → V) z, Dη z v⟫_ℝ := by
    have h := (hDη.hasWeakLineDerivOn v).integral_inner_lineDeriv_eq_neg φ
    simpa only [TestFunction.lineDeriv_eq_fderiv] using h
  -- The equation, tested against `∂_v φ`.
  have hA' : ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z v, η z⟫_ℝ = (∫ z, ⟪fderiv ℝ (φ : ℂ → V) z v, Dξ z 1⟫_ℝ) +
      (∫ z, ⟪fderiv ℝ (φ : ℂ → V) z v, J z (Dξ z I)⟫_ℝ) +
        ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z v, S z (ξ z)⟫_ℝ := by
    have h := integral_add (u1.add u2) u3
    simp only [Pi.add_apply] at h
    rw [integral_add u1 u2] at h
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [ae_imp_of_ae_restrict heq] with z hz
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · simp only [← hz hzΩ, inner_add_right]
    · simp [hfK' z fun h' => hzΩ (φ.tsupport_subset h')]
  -- The weak Leibniz rule for `S ξ`.
  have hSξ := hDS.bilin_of_memLpLoc (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hq hqp
    ((hS.memLpLoc_of_holderTriple hp le_rfl).mono_exponent le_top) hDSp hDξ hξ.memLpLoc hDξq
  have hB : ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z v, S z (ξ z)⟫_ℝ =
      -((∫ z, ⟪(φ : ℂ → V) z, DS z v (ξ z)⟫_ℝ) + ∫ z, ⟪(φ : ℂ → V) z, S z (Dξ z v)⟫_ℝ) := by
    have h := (hSξ.hasWeakLineDerivOn v).integral_inner_lineDeriv_eq_neg φ
    simp only [TestFunction.lineDeriv_eq_fderiv] at h
    refine h.trans ?_
    rw [← integral_add i7 i4]
    congr 1
    refine integral_congr_ae (.of_forall fun z => ?_)
    simp [inner_add_right]
  -- Mixed partials of `ξ` against `φ`.
  have hC : ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z v, Dξ z 1⟫_ℝ = ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1, Dξ z v⟫_ℝ :=
    integral_inner_comm_of_compact (p := p) (q := q) hpq ENNReal.coe_ne_top φ.hasCompactSupport
      φ.tsupport_subset hfK hfK' hφw hφ'.continuousOn.memLpLoc hDξ hDξq v 1
  -- Mixed partials of `ξ` against `Jᵀ φ`.
  let Dψ : ℂ → ℂ →L[ℝ] V := fun z =>
    adjointL.flip ((φ : ℂ → V) z) ∘L DJ z + adjointL (J z) ∘L fderiv ℝ (φ : ℂ → V) z
  have hDψ (z u : ℂ) (y : V) :
      ⟪Dψ z u, y⟫_ℝ = ⟪(φ : ℂ → V) z, DJ z u y⟫_ℝ + ⟪fderiv ℝ (φ : ℂ → V) z u, J z y⟫_ℝ := by
    simp [Dψ, adjointL_apply, inner_add_left, ContinuousLinearMap.adjoint_inner_left]
  have hψw : HasWeakFDerivOn volume Ω (fun z => adjointL (J z) ((φ : ℂ → V) z)) Dψ := by
    have h := hDJ.bilin_of_memLpLoc adjointL hp hq hqp
      ((hJ.memLpLoc_of_holderTriple hp le_rfl).mono_exponent le_top) hDJp hφw hφc.memLpLoc
      hφ'.continuousOn.memLpLoc
    convert h using 2 with z
    ext u
    simp [Dψ]
  have hDψ₁ : MemLpLoc p Ω (fun z => adjointL.flip ((φ : ℂ → V) z) ∘L DJ z) :=
    hDJp.continuousOn_clm_comp ((adjointL (V := V)).flip.continuous.comp_continuousOn hφc)
  have hDψ₂ : MemLpLoc p Ω (fun z => adjointL (J z) ∘L fderiv ℝ (φ : ℂ → V) z) :=
    (hJp.clm_comp adjointL).clm_comp_continuousOn hφ'.continuousOn
  have hDψp : MemLpLoc p Ω Dψ := hDψ₁.add hDψ₂
  have hD := integral_inner_comm_of_compact (p := p) (q := q) hpq ENNReal.coe_ne_top
    φ.hasCompactSupport φ.tsupport_subset (ψ := fun z => adjointL (J z) ((φ : ℂ → V) z)) (Dψ := Dψ)
    (fun z hz => by simp [hfK z hz]) (fun z hz => by simp [Dψ, hfK z hz, hfK' z hz]) hψw hDψp
    hDξ hDξq v I
  simp only [hDψ] at hD
  rw [integral_add i5 u2, integral_add i3 i2] at hD
  refine ⟨(((i1.neg.sub i2).sub i3).add i4).add i5, ?_⟩
  rw [integral_add ?_ i5, integral_add ?_ i4, integral_sub ?_ i3, integral_sub ?_ i2, integral_neg]
  · simp only [inner_sub_right]
    rw [integral_sub ?_ i7]
    · linarith
    exact i6
  exacts [i1.neg, i1.neg.sub i2, (i1.neg.sub i2).sub i3, ((i1.neg.sub i2).sub i3).add i4]

/-! ### The differentiated system as a weak equation -/

/-- **The coefficients of the differentiated system.** If `J`, with weak derivative `DJ`, and `S`
are Sobolev coefficients of class `W^{1,p}` and `Lᵖ` on `Ω`, then so are, on the Euclidean product
`WithLp 2 (V × V)`, `J₂ = diag(J, J)` with weak derivative `diag(DJ, DJ)` and the transport of
`S₂ = [[S, ∂_s J], [0, S + ∂_t J]]` (`TauCeti.differentiatedCRCoefficient`). The zeroth-order
coefficient `S₂` contains `DJ`, so it is only locally `Lᵖ`, which is all the structure asks. -/
theorem IsSobolevCRCoefficients.differentiated {p : ℝ≥0∞} {J S : ℂ → V →L[ℝ] V}
    {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} (hc : IsSobolevCRCoefficients p Ω J DJ S) :
    IsSobolevCRCoefficients p Ω (fun z => differentiatedCRStructureL (J z))
      (fun z => differentiatedCRStructureL ∘L DJ z)
      (fun z => euclideanProdArrowCongr (differentiatedCRCoefficient (S z) (DJ z))) where
  hasWeakFDerivOn :=
    hc.hasWeakFDerivOn.clm_comp (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V))
      differentiatedCRStructureL
  memLpLoc_coeff :=
    hc.memLpLoc_coeff.clm_comp (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V))
      differentiatedCRStructureL
  memLpLoc_deriv := hc.memLpLoc_deriv.continuousOn_clm_comp continuousOn_const
  memLpLoc_zeroth := by
    have h : MemLpLoc p Ω (fun z => (S z, DJ z)) := memWkpLoc_zero_iff.1
      ((memWkpLoc_zero_iff.2 hc.memLpLoc_zeroth).prodMk (memWkpLoc_zero_iff.2 hc.memLpLoc_deriv))
    simpa using h.clm_comp (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V))
      ((euclideanProdArrowCongr (E := V)).toContinuousLinearMap.comp
      differentiatedCRCoefficientL)

/-- **The differentiated system holds weakly.** Let `p > 2` and `1/p + 1/q ≤ 1` with `q ≤ p`. Let
`J, S ∈ W^{1,p}_loc(Ω)` have weak derivatives `DJ`, `DS`, and let `ξ, η ∈ W^{1,q}_loc(Ω)` have weak
derivatives `Dξ`, `Dη`. If `∂_s ξ + J ∂_t ξ + S ξ = η` almost everywhere on `Ω`, then
`Ξ = (∂_s ξ, ∂_t ξ)` is a weak solution, on the Euclidean product `WithLp 2 (V × V)`, of
`∂_s Ξ + J₂ ∂_t Ξ + S₂ Ξ = (∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)`, with the coefficients of
`TauCeti.IsSobolevCRCoefficients.differentiated`.

Unlike `TauCeti.ae_differentiated_cauchyRiemann`, `ξ` is only assumed to be in `W^{1,q}_loc`: this
is the form in which the induction of McDuff–Salamon, Proposition B.4.9, applies the order-zero
regularity to `(J₂, S₂)`. -/
theorem isWeakCRSolution_differentiated {p q : ℝ≥0} (hp : 2 < p)
    (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ ≤ 1) (hqp : q ≤ p)
    {J S : ℂ → V →L[ℝ] V} {DJ DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    {Dξ Dη : ℂ → ℂ →L[ℝ] V}
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hη : MemWkpLoc q Ω 1 η) (hDη : HasWeakFDerivOn volume Ω η Dη)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z) :
    IsWeakCRSolution q Ω (fun z => differentiatedCRStructureL (J z))
      (fun z => differentiatedCRStructureL ∘L DJ z)
      (fun z => euclideanProdArrowCongr (differentiatedCRCoefficient (S z) (DJ z)))
      (fun z => WithLp.toLp 2 (Dξ z 1, Dξ z I))
      (fun z => WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) := by
  have hq := one_lt_of_inv_add_inv_le_one hpq
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq.le⟩
  have hloc := Ω.isOpen.isLocallyClosed
  have hc₂ : IsSobolevCRCoefficients (p : ℝ≥0∞) Ω J DJ S :=
    { hasWeakFDerivOn := hDJ
      memLpLoc_coeff := hJ.memLpLoc
      memLpLoc_deriv := hJ.memLpLoc_of_hasWeakFDerivOn hDJ
      memLpLoc_zeroth := hS.memLpLoc }
  replace hc₂ := hc₂.differentiated
  let e : V × V →L[ℝ] WithLp 2 (V × V) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm.toContinuousLinearMap
  have hΞ : MemLpLoc q Ω (fun z => WithLp.toLp 2 (Dξ z 1, Dξ z I)) := by
    simpa [e] using (hξ.memLpLoc_of_hasWeakFDerivOn hDξ).clm_comp (G := WithLp 2 (V × V))
      (e ∘L (ContinuousLinearMap.apply ℝ V 1).prod (ContinuousLinearMap.apply ℝ V I))
  have hR := memLpLoc_differentiatedCR_rightSide hp hq.le hqp hS hDS hξ hη hDη
  have hR₁ := ((hR.clm_comp (ContinuousLinearMap.fst ℝ V V)).locallyIntegrableOn Fact.out hloc)
  have hR₂ := ((hR.clm_comp (ContinuousLinearMap.snd ℝ V V)).locallyIntegrableOn Fact.out hloc)
  refine isWeakCRSolution_iff.2 ⟨hΞ,
    (hR.clm_comp (G := WithLp 2 (V × V)) e).locallyIntegrableOn Fact.out hloc, fun Φ =>
    ⟨hc₂.integrable_inner_crFormalAdjoint (by exact_mod_cast hpq) hΞ Φ, ?_⟩⟩
  -- The two components of the test function.
  let φ₁ : 𝓓(Ω, V) := TestFunction.postcompCLM (WithLp.fstL 2 ℝ V V) Φ
  let φ₂ : 𝓓(Ω, V) := TestFunction.postcompCLM (WithLp.sndL 2 ℝ V V) Φ
  have hΦd : ∀ z, HasFDerivAt (Φ : ℂ → WithLp 2 (V × V)) (fderiv ℝ Φ z) z := fun z =>
    (Φ.contDiff.differentiable (by simp) z).hasFDerivAt
  have hd₁ (z u : ℂ) :
      fderiv ℝ (φ₁ : ℂ → V) z u = (WithLp.ofLp (fderiv ℝ (Φ : ℂ → WithLp 2 (V × V)) z u)).1 := by
    rw [show (φ₁ : ℂ → V) = WithLp.fstL 2 ℝ V V ∘ Φ from rfl,
      ((WithLp.fstL 2 ℝ V V).hasFDerivAt.comp z (hΦd z)).fderiv]
    rfl
  have hd₂ (z u : ℂ) :
      fderiv ℝ (φ₂ : ℂ → V) z u = (WithLp.ofLp (fderiv ℝ (Φ : ℂ → WithLp 2 (V × V)) z u)).2 := by
    rw [show (φ₂ : ℂ → V) = WithLp.sndL 2 ℝ V V ∘ Φ from rfl,
      ((WithLp.sndL 2 ℝ V V).hasFDerivAt.comp z (hΦd z)).fderiv]
    rfl
  have hv₁ (z : ℂ) : (φ₁ : ℂ → V) z = (WithLp.ofLp ((Φ : ℂ → WithLp 2 (V × V)) z)).1 := rfl
  have hv₂ (z : ℂ) : (φ₂ : ℂ → V) z = (WithLp.ofLp ((Φ : ℂ → WithLp 2 (V × V)) z)).2 := rfl
  obtain ⟨i₁, e₁⟩ :=
    integral_differentiated_component hp hpq hqp hJ hDJ hS hDS hξ hDξ hη hDη heq φ₁ 1
  obtain ⟨i₂, e₂⟩ :=
    integral_differentiated_component hp hpq hqp hJ hDJ hS hDS hξ hDξ hη hDη heq φ₂ I
  have j₁ := φ₁.integrable_inner hR₁
  have j₂ := φ₂.integrable_inner hR₂
  have hL : ∫ z, ⟪crFormalAdjoint (fun z => differentiatedCRStructureL (J z))
      (fun z => differentiatedCRStructureL ∘L DJ z)
      (fun z => euclideanProdArrowCongr (differentiatedCRCoefficient (S z) (DJ z))) Φ z,
        WithLp.toLp 2 (Dξ z 1, Dξ z I)⟫_ℝ = ∫ z, ((-⟪fderiv ℝ (φ₁ : ℂ → V) z 1, Dξ z 1⟫_ℝ -
        ⟪fderiv ℝ (φ₁ : ℂ → V) z I, J z (Dξ z 1)⟫_ℝ - ⟪(φ₁ : ℂ → V) z, DJ z I (Dξ z 1)⟫_ℝ +
        ⟪(φ₁ : ℂ → V) z, S z (Dξ z 1)⟫_ℝ + ⟪(φ₁ : ℂ → V) z, DJ z 1 (Dξ z I)⟫_ℝ) +
        (-⟪fderiv ℝ (φ₂ : ℂ → V) z 1, Dξ z I⟫_ℝ -
        ⟪fderiv ℝ (φ₂ : ℂ → V) z I, J z (Dξ z I)⟫_ℝ - ⟪(φ₂ : ℂ → V) z, DJ z I (Dξ z I)⟫_ℝ +
        ⟪(φ₂ : ℂ → V) z, S z (Dξ z I)⟫_ℝ + ⟪(φ₂ : ℂ → V) z, DJ z I (Dξ z I)⟫_ℝ)) := by
    refine integral_congr_ae (.of_forall fun z => ?_)
    dsimp only
    rw [inner_crFormalAdjoint]
    simp only [WithLp.prod_inner_apply, differentiatedCRStructureL_apply,
      euclideanProdArrowCongr_apply, ContinuousLinearMap.comp_apply,
      differentiatedCRCoefficient_apply, inner_add_right, hd₁, hd₂, hv₁, hv₂]
    ring
  have hRhs : ∫ z, ⟪(Φ : ℂ → WithLp 2 (V × V)) z,
      WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))⟫_ℝ =
      ∫ z, (⟪(φ₁ : ℂ → V) z, Dη z 1 - DS z 1 (ξ z)⟫_ℝ +
        ⟪(φ₂ : ℂ → V) z, Dη z I - DS z I (ξ z)⟫_ℝ) :=
    integral_congr_ae (.of_forall fun z => by simp [hv₁, hv₂])
  rw [hL, hRhs]
  exact (integral_add i₁ i₂).trans ((congrArg₂ (· + ·) e₁ e₂).trans (integral_add j₁ j₂).symm)

/-- **The right side of the differentiated system at higher order.** For `p > 2`, `1 < q ≤ p` and
`k ≥ 0`, if `S ∈ W^{k+1,p}_loc(Ω)` and `ξ, η ∈ W^{k+1,q}_loc(Ω)`, with weak derivatives `DS` and
`Dη`, then `(∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)` is in `W^{k,q}_loc(Ω)`. The case `k = 0` is
`TauCeti.memLpLoc_differentiatedCR_rightSide`. -/
theorem memWkpLoc_differentiatedCR_rightSide {p q : ℝ≥0} (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    {k : ℕ} {S : ℂ → V →L[ℝ] V} {DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    {Dη : ℂ → ℂ →L[ℝ] V} (hS : MemWkpLoc p Ω (k + 1) S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω (k + 1) ξ) (hη : MemWkpLoc q Ω (k + 1) η)
    (hDη : HasWeakFDerivOn volume Ω η Dη) :
    MemWkpLoc q Ω k (fun z => (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) := by
  cases k with
  | zero =>
    exact memWkpLoc_zero_iff.2 (memLpLoc_differentiatedCR_rightSide hp hq.le hqp
      hS hDS hξ hη hDη)
  | succ k =>
    have hDS' := hS.memWkpLoc_of_hasWeakFDerivOn hDS
    have hDη' := hη.memWkpLoc_of_hasWeakFDerivOn hDη
    have hcomp (v : ℂ) : MemWkpLoc q Ω (k + 1) (fun z => Dη z v - DS z v (ξ z)) :=
      (hDη'.clm_comp (ContinuousLinearMap.apply ℝ V v)).sub
        ((hDS'.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) v)).clm_apply_succ hp hq hqp
          hξ.of_succ)
    exact (hcomp 1).prodMk (hcomp I)

/-- **Check: the constant case.** For a constant structure `J = A` and `S = 0`, the weak form of
the differentiated system is the original operator `∂_s + A ∂_t` applied weakly to each component
of `Ξ = (∂_s ξ, ∂_t ξ)`, with right side `(∂_s η, ∂_t η)`. -/
theorem isWeakCRSolution_differentiated_const {p q : ℝ≥0} (hp : 2 < p)
    (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ ≤ 1) (hqp : q ≤ p) (A : V →L[ℝ] V)
    {ξ η : ℂ → V} {Dξ Dη : ℂ → ℂ →L[ℝ] V}
    (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hη : MemWkpLoc q Ω 1 η) (hDη : HasWeakFDerivOn volume Ω η Dη)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + A (Dξ z I) = η z) :
    IsWeakCRSolution q Ω (fun _ => differentiatedCRStructureL A) 0 0
      (fun z => WithLp.toLp 2 (Dξ z 1, Dξ z I)) (fun z => WithLp.toLp 2 (Dη z 1, Dη z I)) := by
  have hA : HasWeakFDerivOn volume Ω (fun _ => A) 0 := hasWeakFDerivOn_iff.2 fun v => by
    simpa using hasWeakLineDerivOn_const (μ := volume) (Ω := Ω) (v := v) A
  have h0 : HasWeakFDerivOn volume Ω (0 : ℂ → V →L[ℝ] V) 0 := hasWeakFDerivOn_zero
  have h := isWeakCRSolution_differentiated hp hpq hqp (memWkpLoc_const A) hA memWkpLoc_zero_fun
    h0 hξ hDξ hη hDη (heq.mono fun z hz => by simpa using hz)
  convert h using 1 <;> ext <;> simp

end TauCeti
