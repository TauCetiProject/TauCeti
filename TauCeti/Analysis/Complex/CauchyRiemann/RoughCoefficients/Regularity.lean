/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Differentiated
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.OrderZero
public import TauCeti.Analysis.Normed.Lp.ProdLp
public import TauCeti.Analysis.Sobolev.Local.Morrey.Higher
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.Sobolev.Local.Coordinates
import TauCeti.Analysis.Sobolev.Mollification.Interior
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry
import TauCeti.Data.ENNReal.Holder
import TauCeti.Data.ENNReal.Inv

/-!
# Higher-order interior regularity for Cauchy–Riemann operators with Sobolev coefficients

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a finite-dimensional real inner product
space. Consider the real linear Cauchy–Riemann operator

`D ξ = ∂_s ξ + J ∂_t ξ + S ξ`

with Sobolev coefficients `J ∈ W^{max 1 k, p}_loc(Ω; V →L[ℝ] V)` satisfying `J² = -1` almost
everywhere on `Ω` and `S ∈ W^{k,p}_loc(Ω; V →L[ℝ] V)` for `2 < p ≤ ∞`.

Building on the order-zero regularity theorem `TauCeti.IsWeakCRSolution.memWkpLoc_one_of_memLpLoc`
of `TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.OrderZero`, this file proves
higher-order interior regularity (McDuff–Salamon, Proposition B.4.9):

1. **The weak differentiated system** (`TauCeti.isWeakCRSolution_differentiated`). For finite
   exponents `p, q` with `p⁻¹ + q⁻¹ ≤ 1`, when `J, S ∈ W^{1,p}_loc(Ω)`, `ξ ∈ W^{1,q}_loc(Ω)`, and
   `η` has weak derivative `Dη` on `Ω` with `∂_s ξ + J ∂_t ξ + S ξ = η` almost everywhere on `Ω`,
   the pair `Ξ = (∂_s ξ, ∂_t ξ)` valued in `WithLp 2 (V × V)` is a *weak* solution
   (`TauCeti.IsWeakCRSolution`) of
   `∂_s Ξ + diag(J, J) ∂_t Ξ + S₂ Ξ = (∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)` with
   `S₂ = TauCeti.differentiatedCRCoefficient S DJ`. Neither second weak derivatives of `ξ` nor
   second weak derivatives of `J` are assumed: the `∂_s` row uses a distributional commutator
   identity established by interior mollification of `ξ`.
2. **Higher-order interior regularity** (`TauCeti.IsWeakCRSolution.memWkpLoc_succ_of_memWkpLoc`
   and `TauCeti.IsWeakCRSolution.memWkpLoc_succ`). By induction on `k`, if `2 < p ≤ ∞`,
   `1 < r < ∞`, `r ≤ p`, `p⁻¹ + q⁻¹ < 1`, `J ∈ W^{max 1 k, p}_loc(Ω)` with `J² = -1` almost
   everywhere, `S ∈ W^{k,p}_loc(Ω)`, and `η ∈ W^{k,r}_loc(Ω)`, then every weak solution
   `ξ ∈ L^q_loc(Ω)` belongs to `W^{k+1,r}_loc(Ω)`.
3. **Regularity on general finite-dimensional normed spaces**
   (`TauCeti.HasWeakFDerivOn.memWkpLoc_succ_of_ae_cauchyRiemann`,
   `TauCeti.IsWeakLinearCauchyRiemannOn.memWkpLoc_succ`,
   `TauCeti.IsWeakLinearCauchyRiemannOn.contDiffOn`, and
   `TauCeti.IsWeakLinearCauchyRiemannOn.contDiffOn_infty`). Transporting along a continuous linear
   equivalence to Euclidean space yields inhomogeneous `W^{k+1,r}_loc` regularity for `W^{1,q}_loc`
   solutions (`1 < q ≤ ∞`, `1 < r < ∞`, `r ≤ p`) and `W^{k+1,p}_loc`, `C^k`, and `C^∞` regularity
   for `TauCeti.IsWeakLinearCauchyRiemannOn`.

## Main declarations

* `TauCeti.isWeakCRSolution_differentiated`: `Ξ = (∂_s ξ, ∂_t ξ)` weakly solves the differentiated
  Cauchy–Riemann system when `ξ ∈ W^{1,q}_loc(Ω)` and `p⁻¹ + q⁻¹ ≤ 1`.
* `TauCeti.IsWeakCRSolution.memWkpLoc_succ_of_memWkpLoc`,
  `TauCeti.IsWeakCRSolution.memWkpLoc_succ`, and `TauCeti.IsWeakCRSolution.memWkpLoc_succ_self`:
  McDuff–Salamon Proposition B.4.9 (`ξ ∈ W^{k+1,r}_loc`, `W^{k+1,q}_loc`, and `W^{k+1,p}_loc`).
* `TauCeti.IsWeakCRSolution.exists_contDiffOn_ae_eq`: `C^k` representative almost everywhere on `Ω`
  when `2 < r ≤ p` and `η ∈ W^{k,r}_loc(Ω)`.
* `TauCeti.HasWeakFDerivOn.memWkpLoc_succ_of_ae_cauchyRiemann`: inhomogeneous `W^{k+1,r}_loc`
  regularity of `W^{1,q}_loc` solutions valued in any finite-dimensional real normed space.
* `TauCeti.IsWeakLinearCauchyRiemannOn.memWkpLoc_succ`,
  `TauCeti.IsWeakLinearCauchyRiemannOn.contDiffOn`, and
  `TauCeti.IsWeakLinearCauchyRiemannOn.contDiffOn_infty`: `W^{k+1,p}_loc`, `C^k`, and `C^∞`
  regularity of continuous weak linear Cauchy–Riemann solutions valued in any finite-dimensional
  real normed space.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Proposition B.4.9).
-/

public noncomputable section

open Complex Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal InnerProductSpace LineDeriv NNReal Topology

namespace TauCeti

/-! ### Weak differentiated system -/

section WeakDifferentiated

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Opens ℂ}

private local instance : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup (ℂ →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ (ℂ →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup (V × V →L[ℝ] V × V) := inferInstance
private local instance : NormedSpace ℝ (V × V →L[ℝ] V × V) := inferInstance
private local instance :
    NormedAddCommGroup (WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) := inferInstance
private local instance :
    NormedSpace ℝ (WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) := inferInstance

/-- Commutator identity for a smooth field `ψ` and a `W^{1,p}_loc` coefficient `J`: symmetry of the
second Fréchet derivative of `ψ` cancels the second-derivative terms in the weak Leibniz rules for
`∂_t(J ∂_s ψ)` and `∂_s(J ∂_t ψ)`. -/
private theorem integral_commutator_of_contDiff [FiniteDimensional ℝ V] {p q : ℝ≥0∞}
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (φ : 𝓓(Ω, V)) {ψ : ℂ → V}
    (hψ : ContDiff ℝ ∞ ψ) :
    -(∫ z, ⟪fderiv ℝ (φ : ℂ → V) z I, J z (fderiv ℝ ψ z 1)⟫_ℝ) -
        (∫ z, ⟪(φ : ℂ → V) z, DJ z I (fderiv ℝ ψ z 1)⟫_ℝ) +
        ∫ z, ⟪(φ : ℂ → V) z, DJ z 1 (fderiv ℝ ψ z I)⟫_ℝ =
      -(∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1, J z (fderiv ℝ ψ z I)⟫_ℝ) := by
  have : Fact (1 ≤ p) := ⟨ENNReal.inv_le_one.1 (le_self_add.trans hpq)⟩
  have : Fact (1 ≤ q) := ⟨ENNReal.inv_le_one.1 (le_add_self.trans hpq)⟩
  let u : ℂ → ℂ → V := fun v z => fderiv ℝ ψ z v
  have hu_smooth (v : ℂ) : ContDiff ℝ ∞ (u v) :=
    (hψ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hu_weak (v : ℂ) : HasWeakFDerivOn volume Ω (u v) (fderiv ℝ (u v)) :=
    ((hu_smooth v).contDiffOn.of_le (by simp)).hasWeakFDerivOn_fderiv
  have hu_q (v : ℂ) : MemLpLoc q Ω (u v) := (hu_smooth v).continuous.continuousOn.memLpLoc
  have hdu_q (v w : ℂ) : MemLpLoc q Ω (fun z => fderiv ℝ (u v) z w) :=
    (((hu_smooth v).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply
      contDiff_const).continuous.continuousOn.memLpLoc
  have hDJw (w : ℂ) : MemLpLoc p Ω (fun z => DJ z w) :=
    hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) w)
  have hJu (v w : ℂ) : HasWeakLineDerivOn volume Ω (fun z => J z (u v z))
      (fun z => DJ z w (u v z) + J z (fderiv ℝ (u v) z w)) w := by
    simpa using (hc.hasWeakFDerivOn.hasWeakLineDerivOn w).bilin_of_memLp
      (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hp hq hq hpq hpq hpq
      ((hu_weak v).hasWeakLineDerivOn w)
      (fun K hK hKΩ => memLpLoc_iff.1 hc.memLpLoc_coeff K hKΩ hK)
      (fun K hK hKΩ => memLpLoc_iff.1 (hDJw w) K hKΩ hK)
      (fun K hK hKΩ => memLpLoc_iff.1 (hu_q v) K hKΩ hK)
      (fun K hK hKΩ => memLpLoc_iff.1 (hdu_q v w) K hKΩ hK)
  have hloc := Ω.isOpen.isLocallyClosed
  have hibp (v w : ℂ) : ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z w, J z (u v z)⟫_ℝ =
      -((∫ z, ⟪(φ : ℂ → V) z, DJ z w (u v z)⟫_ℝ) +
        ∫ z, ⟪(φ : ℂ → V) z, J z (fderiv ℝ (u v) z w)⟫_ℝ) := by
    have h := (hJu v w).integral_inner_lineDeriv_eq_neg φ
    simp only [TestFunction.lineDeriv_eq_fderiv, inner_add_right] at h
    exact h.trans (congrArg Neg.neg (integral_add
      (φ.integrable_inner ((hDJw w).locallyIntegrableOn_clm_apply (hu_q v) hpq hloc))
      (φ.integrable_inner (hc.memLpLoc_coeff.locallyIntegrableOn_clm_apply (hdu_q v w) hpq hloc))))
  have hsymm (z : ℂ) : fderiv ℝ (u 1) z I = fderiv ℝ (u I) z 1 := by
    have hd : DifferentiableAt ℝ (fderiv ℝ ψ) z :=
      (hψ.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero z
    simpa [u, fderiv_clm_apply hd (differentiableAt_const _)] using
      ((hψ.contDiffAt (x := z)).isSymmSndFDerivAt (by simp)).eq I 1
  have h1 := hibp 1 I
  have h2 := hibp I 1
  simp_rw [hsymm] at h1
  linarith

omit [CompleteSpace V] in
/-- On the support of `Θ`, if every `ρ.rOut`-ball around `tsupport Θ` lies in `W ⊆ Ω`, the Fréchet
derivative of `ρ.normed ⋆ 1_W ξ` agrees with `ρ.normed ⋆ 1_W Dξ`, so their inner-product pairings
against `z ↦ A z (· v)` are equal. -/
private theorem integral_inner_clm_mollified_fderiv_eq {q : ℝ≥0∞} (hq1 : 1 ≤ q)
    {W : Opens ℂ} (hWΩ : closure (W : Set ℂ) ⊆ Ω) {ξ : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V}
    (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hξW : MemLp ξ q (volume.restrict W)) (hDξW : MemLp Dξ q (volume.restrict W))
    (ρ : ContDiffBump (0 : ℂ)) (Θ : 𝓓(Ω, V))
    (hball : ∀ z ∈ tsupport (Θ : ℂ → V), closedBall z ρ.rOut ⊆ W)
    (A : ℂ → V →L[ℝ] V) (v : ℂ) :
    (∫ z, ⟪(Θ : ℂ → V) z, A z (fderiv ℝ
        (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator ξ)
        z v)⟫_ℝ) =
      ∫ z, ⟪(Θ : ℂ → V) z, A z
        ((ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator Dξ)
          z v)⟫_ℝ := by
  refine integral_congr_ae (.of_forall fun z => ?_)
  dsimp only
  by_cases hz : z ∈ tsupport (Θ : ℂ → V)
  · have hd := (hDξ.mono (subset_closure.trans hWΩ)).fderiv_indicator_convolution_normed
      hξW hDξW hq1 hq1 ρ z (hball z hz)
    have hd' : fderiv ℝ (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (W : Set ℂ).indicator ξ) z =
      (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator Dξ) z := by
      simpa only [convolution_flip] using hd
    rw [hd']
  · simp [image_eq_zero_of_notMem_tsupport hz]

/-- Distributional commutator identity for `J ∈ W^{1,p}_loc(Ω)` and `ξ ∈ W^{1,q}_loc(Ω)` when
`p⁻¹ + q⁻¹ ≤ 1`, proved by interior mollification of `ξ` on a precompact open neighbourhood of
`tsupport φ`. -/
private theorem integral_commutator_of_hasWeakFDerivOn [FiniteDimensional ℝ V] {p q : ℝ≥0∞}
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V}
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hξq : MemLpLoc q Ω ξ) (hDξq : MemLpLoc q Ω Dξ) (φ : 𝓓(Ω, V)) :
    -(∫ z, ⟪fderiv ℝ (φ : ℂ → V) z I, J z (Dξ z 1)⟫_ℝ) -
        (∫ z, ⟪(φ : ℂ → V) z, DJ z I (Dξ z 1)⟫_ℝ) +
        ∫ z, ⟪(φ : ℂ → V) z, DJ z 1 (Dξ z I)⟫_ℝ =
      -(∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1, J z (Dξ z I)⟫_ℝ) := by
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  obtain ⟨W, hφW, hWΩ, hWc⟩ :=
    Opens.exists_between_and_isCompact_closure φ.hasCompactSupport φ.tsupport_subset
  obtain ⟨ρ, hρ0, hball⟩ :=
    exists_contDiffBump_tendsto_rOut_closedBall_subset W.isOpen φ.hasCompactSupport hφW
  have hξW : MemLp ξ q (volume.restrict W) := hξq.memLp_of_closure_subset hWc hWΩ
  have hDξW : MemLp Dξ q (volume.restrict W) := hDξq.memLp_of_closure_subset hWc hWΩ
  have hJW : MemLp J p (volume.restrict W) := hc.memLpLoc_coeff.memLp_of_closure_subset hWc hWΩ
  have hDJW (w : ℂ) : MemLp (fun z => DJ z w) p (volume.restrict W) :=
    (hc.memLpLoc_deriv.memLp_of_closure_subset hWc hWΩ).continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) w)
  have hξext : MemLp ((W : Set ℂ).indicator ξ) q volume :=
    (memLp_indicator_iff_restrict W.isOpen.measurableSet.nullMeasurableSet).2 hξW
  let Dψ (n : ℕ) : ℂ → ℂ →L[ℝ] V :=
    (ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator Dξ
  have hid (n : ℕ) : -(∫ z, ⟪(∂_{I} φ : 𝓓(Ω, V)) z, J z (Dψ n z 1)⟫_ℝ) -
      (∫ z, ⟪(φ : ℂ → V) z, DJ z I (Dψ n z 1)⟫_ℝ) +
      (∫ z, ⟪(φ : ℂ → V) z, DJ z 1 (Dψ n z I)⟫_ℝ) =
      -(∫ z, ⟪(∂_{(1 : ℂ)} φ : 𝓓(Ω, V)) z, J z (Dψ n z I)⟫_ℝ) := by
    have hψ_smooth : ContDiff ℝ ∞
        ((ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator ξ) :=
      ((ρ n).hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ) ((ρ n).contDiff_normed (μ := volume))
        (hξext.locallyIntegrable hq1)
    have hc_n := integral_commutator_of_contDiff hp hq hpq hc φ hψ_smooth
    simp_rw [← TestFunction.lineDerivOp_apply_eq_fderiv] at hc_n
    rwa [integral_inner_clm_mollified_fderiv_eq hq1 hWΩ hDξ hξW hDξW (ρ n) (∂_{I} φ)
        (fun z hz => hball n z (φ.tsupport_lineDerivOp_subset I hz)) J 1,
      integral_inner_clm_mollified_fderiv_eq hq1 hWΩ hDξ hξW hDξW (ρ n) φ (hball n)
        (fun z => DJ z I) 1,
      integral_inner_clm_mollified_fderiv_eq hq1 hWΩ hDξ hξW hDξW (ρ n) φ (hball n)
        (fun z => DJ z 1) I,
      integral_inner_clm_mollified_fderiv_eq hq1 hWΩ hDξ hξW hDξW (ρ n) (∂_{(1 : ℂ)} φ)
        (fun z hz => hball n z (φ.tsupport_lineDerivOp_subset 1 hz)) J I] at hc_n
  let B (v : ℂ) : (ℂ →L[ℝ] V) →L[ℝ] (V →L[ℝ] V) →L[ℝ] V :=
    (ContinuousLinearMap.id ℝ (V →L[ℝ] V)).flip.comp (ContinuousLinearMap.apply ℝ V v)
  have hconv (Θ : 𝓓(Ω, V)) (hΘW : tsupport (Θ : ℂ → V) ⊆ W) {A : ℂ → V →L[ℝ] V}
      (hAW : MemLp A p (volume.restrict W)) (v : ℂ) :
      Tendsto (fun n => ∫ z, ⟪(Θ : ℂ → V) z, A z (Dψ n z v)⟫_ℝ)
        atTop (𝓝 (∫ z, ⟪(Θ : ℂ → V) z, A z (Dξ z v)⟫_ℝ)) := by
    simpa [B, Dψ] using Θ.tendsto_integral_inner_bilin_normed_convolution (B v) hq
      (add_comm p⁻¹ q⁻¹ ▸ hpq) hWc hΘW hDξW hAW hρ0
  have ht1 := hconv (∂_{I} φ) ((φ.tsupport_lineDerivOp_subset I).trans hφW) hJW 1
  have ht4 := hconv (∂_{(1 : ℂ)} φ) ((φ.tsupport_lineDerivOp_subset 1).trans hφW) hJW I
  simpa only [TestFunction.lineDerivOp_apply_eq_fderiv] using tendsto_nhds_unique
    ((ht1.neg.sub (hconv φ hφW (hDJW I) 1)).add (hconv φ hφW (hDJW 1) I))
    (ht4.neg.congr fun n => (hid n).symm)

omit [CompleteSpace V] in
/-- Local integrability of each coordinate `Dη · v - DS · v (ξ ·)` of the differentiated right-hand
side without assuming `L^q_loc` integrability on `Dη`. -/
private theorem locallyIntegrableOn_differentiatedCR_coord {p q : ℝ≥0∞} (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {S : ℂ → V →L[ℝ] V} {DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V} {Dη : ℂ → ℂ →L[ℝ] V}
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemLpLoc q Ω ξ) (hDη : HasWeakFDerivOn volume Ω η Dη) (v : ℂ) :
    LocallyIntegrableOn (fun z => Dη z v - DS z v (ξ z)) Ω volume := by
  have hDSp : MemLpLoc p Ω DS := memWkpLoc_zero_iff.1 (hS.memWkpLoc_of_hasWeakFDerivOn hDS)
  exact (hDη.hasWeakLineDerivOn v).locallyIntegrableOn_deriv.sub
    ((hDSp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) v)).locallyIntegrableOn_clm_apply
      hξ hpq Ω.isOpen.isLocallyClosed)

/-- Common weak directional differentiation of `∂_s ξ + J ∂_t ξ + S ξ = η` along `v ∈ ℂ` against a
test function `θ ∈ 𝓓(Ω, V)`. -/
private theorem integral_lineDeriv_crEquation [FiniteDimensional ℝ V] {p q : ℝ≥0∞}
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {J S : ℂ → V →L[ℝ] V} {DJ DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    {Dξ Dη : ℂ → ℂ →L[ℝ] V} (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hDη : HasWeakFDerivOn volume Ω η Dη)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z)
    (v : ℂ) (θ : 𝓓(Ω, V)) :
    -(∫ z, ⟪fderiv ℝ (θ : ℂ → V) z v, Dξ z 1⟫_ℝ) -
        (∫ z, ⟪fderiv ℝ (θ : ℂ → V) z v, J z (Dξ z I)⟫_ℝ) +
        ∫ z, ⟪(θ : ℂ → V) z, S z (Dξ z v)⟫_ℝ =
      ∫ z, ⟪(θ : ℂ → V) z, Dη z v - DS z v (ξ z)⟫_ℝ := by
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have : Fact (1 ≤ p) := ⟨ENNReal.inv_le_one.1 (le_self_add.trans hpq)⟩
  have : Fact (1 ≤ q) := ⟨hq1⟩
  have hloc := Ω.isOpen.isLocallyClosed
  have hDξq : MemLpLoc q Ω Dξ := memWkpLoc_zero_iff.1 (hξ.memWkpLoc_of_hasWeakFDerivOn hDξ)
  have hDSp : MemLpLoc p Ω DS := memWkpLoc_zero_iff.1 (hS.memWkpLoc_of_hasWeakFDerivOn hDS)
  have hDSv : MemLpLoc p Ω (fun z => DS z v) :=
    hDSp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) v)
  have hDξv : MemLpLoc q Ω (fun z => Dξ z v) :=
    hDξq.clm_comp (ContinuousLinearMap.apply ℝ V v)
  have hSξ : HasWeakLineDerivOn volume Ω (fun z => S z (ξ z))
      (fun z => DS z v (ξ z) + S z (Dξ z v)) v := by
    simpa using (hDS.hasWeakLineDerivOn v).bilin_of_memLp
      (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hp hq hq hpq hpq hpq
      (hDξ.hasWeakLineDerivOn v)
      (fun K hK hKΩ => memLpLoc_iff.1 hS.memLpLoc K hKΩ hK)
      (fun K hK hKΩ => memLpLoc_iff.1 hDSv K hKΩ hK)
      (fun K hK hKΩ => memLpLoc_iff.1 hξ.memLpLoc K hKΩ hK)
      (fun K hK hKΩ => memLpLoc_iff.1 hDξv K hKΩ hK)
  have iD1 : Integrable (fun z => ⟪fderiv ℝ (θ : ℂ → V) z v, Dξ z 1⟫_ℝ) :=
    θ.integrable_inner_fderiv
      ((hDξq.clm_comp (ContinuousLinearMap.apply ℝ V 1)).locallyIntegrableOn hq1 hloc) v
  have iJD : Integrable (fun z => ⟪fderiv ℝ (θ : ℂ → V) z v, J z (Dξ z I)⟫_ℝ) :=
    θ.integrable_inner_fderiv (hc.memLpLoc_coeff.locallyIntegrableOn_clm_apply
      (hDξq.clm_comp (ContinuousLinearMap.apply ℝ V I)) hpq hloc) v
  have iSξ := θ.integrable_inner_fderiv
    (hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hξ.memLpLoc hpq hloc) v
  have iDSξ : Integrable (fun z => ⟪(θ : ℂ → V) z, DS z v (ξ z)⟫_ℝ) :=
    θ.integrable_inner (hDSv.locallyIntegrableOn_clm_apply hξ.memLpLoc hpq hloc)
  have iSD : Integrable (fun z => ⟪(θ : ℂ → V) z, S z (Dξ z v)⟫_ℝ) :=
    θ.integrable_inner (hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hDξv hpq hloc)
  have iDη : Integrable (fun z => ⟪(θ : ℂ → V) z, Dη z v⟫_ℝ) :=
    θ.integrable_inner (hDη.hasWeakLineDerivOn v).locallyIntegrableOn_deriv
  have hpde : (∫ z, ⟪fderiv ℝ (θ : ℂ → V) z v, Dξ z 1⟫_ℝ) +
      (∫ z, ⟪fderiv ℝ (θ : ℂ → V) z v, J z (Dξ z I)⟫_ℝ) +
      (∫ z, ⟪fderiv ℝ (θ : ℂ → V) z v, S z (ξ z)⟫_ℝ) =
      ∫ z, ⟪fderiv ℝ (θ : ℂ → V) z v, η z⟫_ℝ := by
    rw [← integral_add iD1 iJD]
    refine (integral_add (iD1.add iJD) iSξ).symm.trans
      (integral_congr_ae ((ae_imp_of_ae_restrict heq).mono fun z hz => ?_))
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · simp only [Pi.add_apply, ← inner_add_right, hz hzΩ]
    · simp [fderiv_of_notMem_tsupport ℝ fun h => hzΩ (θ.tsupport_subset h)]
  have hS_ibp := hSξ.integral_inner_lineDeriv_eq_neg θ
  have hη_ibp := (hDη.hasWeakLineDerivOn v).integral_inner_lineDeriv_eq_neg θ
  simp only [TestFunction.lineDeriv_eq_fderiv, inner_add_right, integral_add iDSξ iSD]
    at hS_ibp hη_ibp
  simp_rw [inner_sub_right, integral_sub iDη iDSξ]
  linarith

/-- Pointwise decomposition of the formal adjoint pairing on `WithLp 2 (V × V)` into the two
coordinate test functions `φ₁ = fst ∘ Φ` and `φ₂ = snd ∘ Φ`. -/
private theorem inner_crFormalAdjoint_withLp_eq
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (Φ : 𝓓(Ω, WithLp 2 (V × V))) (z : ℂ) (u₁ u₂ : V) :
    let e := (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm
    let φ₁ : 𝓓(Ω, V) := TestFunction.postcompCLM (WithLp.fstL 2 ℝ V V) Φ
    let φ₂ : 𝓓(Ω, V) := TestFunction.postcompCLM (WithLp.sndL 2 ℝ V V) Φ
    ⟪crFormalAdjoint (fun w => (J w).withLpProdMap 2 (J w))
        (fun w => (ContinuousLinearMap.withLpDiagL 2 ℝ V V).comp (DJ w))
        (fun w => e.arrowCongr e (differentiatedCRCoefficient (S w) (DJ w))) Φ z,
        WithLp.toLp 2 (u₁, u₂)⟫_ℝ =
      (⟪crFormalAdjoint J DJ S φ₁ z, u₁⟫_ℝ + ⟪(φ₁ : ℂ → V) z, DJ z 1 u₂⟫_ℝ) +
        (⟪crFormalAdjoint J DJ S φ₂ z, u₂⟫_ℝ + ⟪(φ₂ : ℂ → V) z, DJ z I u₂⟫_ℝ) := by
  intro e φ₁ φ₂
  have hf1 (v : ℂ) : (fderiv ℝ (Φ : ℂ → WithLp 2 (V × V)) z v).fst =
      fderiv ℝ (φ₁ : ℂ → V) z v := by
    rw [← TestFunction.lineDerivOp_apply_eq_fderiv, ← TestFunction.lineDerivOp_apply_eq_fderiv]
    simp [φ₁]
  have hf2 (v : ℂ) : (fderiv ℝ (Φ : ℂ → WithLp 2 (V × V)) z v).snd =
      fderiv ℝ (φ₂ : ℂ → V) z v := by
    rw [← TestFunction.lineDerivOp_apply_eq_fderiv, ← TestFunction.lineDerivOp_apply_eq_fderiv]
    simp [φ₂]
  have hφ1 : ((Φ : ℂ → WithLp 2 (V × V)) z).fst = (φ₁ : ℂ → V) z := by simp [φ₁]
  have hφ2 : ((Φ : ℂ → WithLp 2 (V × V)) z).snd = (φ₂ : ℂ → V) z := by simp [φ₂]
  rw [inner_crFormalAdjoint, inner_crFormalAdjoint, inner_crFormalAdjoint]
  simp [e, hf1 1, hf1 I, hf2 1, hf2 I, hφ1, hφ2, inner_add_right]
  ring

/-- Evaluates `∫ ⟪crFormalAdjoint J₂ DJ₂ S₂ Φ, Ξ⟫` on `WithLp 2 (V × V)` by splitting into the
two coordinate rows and combining `integral_commutator_of_hasWeakFDerivOn` (row 1) and
`HasWeakFDerivOn.integral_inner_fderiv_comm` (row 2) with `integral_lineDeriv_crEquation`. -/
private theorem integral_inner_crFormalAdjoint_differentiated_aux [FiniteDimensional ℝ V]
    {p q : ℝ≥0∞} (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {J S : ℂ → V →L[ℝ] V} {DJ DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    {Dξ Dη : ℂ → ℂ →L[ℝ] V} (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hDη : HasWeakFDerivOn volume Ω η Dη)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z)
    (Φ : 𝓓(Ω, WithLp 2 (V × V))) :
    let e := (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm
    ∫ z, ⟪crFormalAdjoint (fun w => (J w).withLpProdMap 2 (J w))
        (fun w => (ContinuousLinearMap.withLpDiagL 2 ℝ V V).comp (DJ w))
        (fun w => e.arrowCongr e (differentiatedCRCoefficient (S w) (DJ w))) Φ z,
        WithLp.toLp 2 (Dξ z 1, Dξ z I)⟫_ℝ =
      ∫ z, ⟪(Φ : ℂ → WithLp 2 (V × V)) z,
        WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))⟫_ℝ := by
  intro e
  let φ₁ : 𝓓(Ω, V) := TestFunction.postcompCLM (WithLp.fstL 2 ℝ V V) Φ
  let φ₂ : 𝓓(Ω, V) := TestFunction.postcompCLM (WithLp.sndL 2 ℝ V V) Φ
  have hloc := Ω.isOpen.isLocallyClosed
  have hDξq : MemLpLoc q Ω Dξ := memWkpLoc_zero_iff.1 (hξ.memWkpLoc_of_hasWeakFDerivOn hDξ)
  have hDξv (v : ℂ) : MemLpLoc q Ω (fun z => Dξ z v) :=
    hDξq.clm_comp (ContinuousLinearMap.apply ℝ V v)
  have iA (v : ℂ) (φ : 𝓓(Ω, V)) := hc.integrable_inner_crFormalAdjoint hpq (hDξv v) φ
  have iB (v : ℂ) (φ : 𝓓(Ω, V)) : Integrable (fun z => ⟪(φ : ℂ → V) z, DJ z v (Dξ z I)⟫_ℝ) :=
    φ.integrable_inner ((hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) v)
      ).locallyIntegrableOn_clm_apply (hDξv I) hpq hloc)
  have hlhs : ∫ z, ⟪crFormalAdjoint (fun w => (J w).withLpProdMap 2 (J w))
        (fun w => (ContinuousLinearMap.withLpDiagL 2 ℝ V V).comp (DJ w))
        (fun w => e.arrowCongr e (differentiatedCRCoefficient (S w) (DJ w))) Φ z,
        WithLp.toLp 2 (Dξ z 1, Dξ z I)⟫_ℝ =
      ((∫ z, ⟪crFormalAdjoint J DJ S φ₁ z, Dξ z 1⟫_ℝ) +
        ∫ z, ⟪(φ₁ : ℂ → V) z, DJ z 1 (Dξ z I)⟫_ℝ) +
      ((∫ z, ⟪crFormalAdjoint J DJ S φ₂ z, Dξ z I⟫_ℝ) +
        ∫ z, ⟪(φ₂ : ℂ → V) z, DJ z I (Dξ z I)⟫_ℝ) :=
    (integral_congr_ae (.of_forall fun z =>
      inner_crFormalAdjoint_withLp_eq Φ z (Dξ z 1) (Dξ z I))).trans
      ((integral_add ((iA 1 φ₁).add (iB 1 φ₁)) ((iA I φ₂).add (iB I φ₂))).trans
        (congrArg₂ (· + ·) (integral_add (iA 1 φ₁) (iB 1 φ₁))
          (integral_add (iA I φ₂) (iB I φ₂))))
  have hrow1 : (∫ z, ⟪crFormalAdjoint J DJ S φ₁ z, Dξ z 1⟫_ℝ) +
      (∫ z, ⟪(φ₁ : ℂ → V) z, DJ z 1 (Dξ z I)⟫_ℝ) =
      ∫ z, ⟪(φ₁ : ℂ → V) z, Dη z 1 - DS z 1 (ξ z)⟫_ℝ := by
    rw [hc.integral_inner_crFormalAdjoint_eq_sub_add hpq (hDξv 1) φ₁]
    linarith [integral_commutator_of_hasWeakFDerivOn hp hq hpq hc hDξ hξ.memLpLoc hDξq φ₁,
      integral_lineDeriv_crEquation hp hq hpq hc hS hDS hξ hDξ hDη heq 1 φ₁]
  have hrow2 : (∫ z, ⟪crFormalAdjoint J DJ S φ₂ z, Dξ z I⟫_ℝ) +
      (∫ z, ⟪(φ₂ : ℂ → V) z, DJ z I (Dξ z I)⟫_ℝ) =
      ∫ z, ⟪(φ₂ : ℂ → V) z, Dη z I - DS z I (ξ z)⟫_ℝ := by
    rw [hc.integral_inner_crFormalAdjoint_eq_sub_add hpq (hDξv I) φ₂,
      hDξ.integral_inner_fderiv_comm 1 I φ₂]
    linarith [integral_lineDeriv_crEquation hp hq hpq hc hS hDS hξ hDξ hDη heq I φ₂]
  have hpt (z : ℂ) : ⟪(Φ : ℂ → WithLp 2 (V × V)) z,
        WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))⟫_ℝ =
      ⟪(φ₁ : ℂ → V) z, Dη z 1 - DS z 1 (ξ z)⟫_ℝ +
        ⟪(φ₂ : ℂ → V) z, Dη z I - DS z I (ξ z)⟫_ℝ := by simp [φ₁, φ₂]
  rw [hlhs, hrow1, hrow2]
  simp_rw [hpt]
  exact (integral_add
    (φ₁.integrable_inner (locallyIntegrableOn_differentiatedCR_coord hpq hS hDS hξ.memLpLoc hDη 1))
    (φ₂.integrable_inner
      (locallyIntegrableOn_differentiatedCR_coord hpq hS hDS hξ.memLpLoc hDη I))).symm

/-- **The weak differentiated Cauchy–Riemann system.** Let `p, q < ∞` satisfy `p⁻¹ + q⁻¹ ≤ 1`. If
`J, S ∈ W^{1,p}_loc(Ω)` with weak derivatives `DJ, DS`, `ξ ∈ W^{1,q}_loc(Ω)` with weak derivative
`Dξ`, and `η` has weak derivative `Dη` on `Ω` such that `∂_s ξ + J ∂_t ξ + S ξ = η` almost
everywhere on `Ω`, then `Ξ = (∂_s ξ, ∂_t ξ)` valued in the Hilbert product `WithLp 2 (V × V)` is a
weak solution (`TauCeti.IsWeakCRSolution`) of
`∂_s Ξ + diag(J, J) ∂_t Ξ + S₂ Ξ = (∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)` with
`S₂ = TauCeti.differentiatedCRCoefficient S DJ`. -/
theorem isWeakCRSolution_differentiated [FiniteDimensional ℝ V] {p q : ℝ≥0∞}
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {J S : ℂ → V →L[ℝ] V} {DJ DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    {ξ η : ℂ → V} {Dξ Dη : ℂ → ℂ →L[ℝ] V}
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hDη : HasWeakFDerivOn volume Ω η Dη)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z) :
    IsWeakCRSolution q Ω
      (fun z => (J z).withLpProdMap 2 (J z))
      (fun z => (ContinuousLinearMap.withLpDiagL 2 ℝ V V).comp (DJ z))
      (fun z => (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm.arrowCongr
        (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm
        (differentiatedCRCoefficient (S z) (DJ z)))
      (fun z => WithLp.toLp 2 (Dξ z 1, Dξ z I))
      (fun z => WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) := by
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm
  let diagL := ContinuousLinearMap.withLpDiagL 2 ℝ V V
  have hDJ₂ : HasWeakFDerivOn volume Ω (fun z => (J z).withLpProdMap 2 (J z))
      (fun z => diagL.comp (DJ z)) := by
    simpa [diagL] using hDJ.clm_comp diagL
  have hJ₂ : MemWkpLoc p Ω 1 (fun z => (J z).withLpProdMap 2 (J z)) := by
    simpa [diagL] using hJ.clm_comp diagL
  have hDJp : MemLpLoc p Ω DJ := memWkpLoc_zero_iff.1 (hJ.memWkpLoc_of_hasWeakFDerivOn hDJ)
  have hc : IsSobolevCRCoefficients p Ω J DJ S := ⟨hDJ, hJ.memLpLoc, hDJp, hS.memLpLoc⟩
  have hc₂ : IsSobolevCRCoefficients p Ω (fun z => (J z).withLpProdMap 2 (J z))
      (fun z => diagL.comp (DJ z))
      (fun z => e.arrowCongr e (differentiatedCRCoefficient (S z) (DJ z))) :=
    ⟨hDJ₂, hJ₂.memLpLoc, memWkpLoc_zero_iff.1 (hJ₂.memWkpLoc_of_hasWeakFDerivOn hDJ₂),
      (memWkpLoc_zero_iff.1 ((memWkpLoc_zero_iff.2 hS.memLpLoc).differentiatedCRCoefficient
        hJ hDJ)).clm_comp (e.arrowCongr e).toContinuousLinearMap⟩
  have hΞq : MemLpLoc q Ω (fun z => WithLp.toLp 2 (Dξ z 1, Dξ z I)) :=
    e.comp_memLpLoc_iff.2 (memWkpLoc_zero_iff.1 (hξ.memWkpLoc_partials_of_hasWeakFDerivOn hDξ))
  have hloc1 := locallyIntegrableOn_differentiatedCR_coord hpq hS hDS hξ.memLpLoc hDη 1
  have hlocI := locallyIntegrableOn_differentiatedCR_coord hpq hS hDS hξ.memLpLoc hDη I
  have hHloc : LocallyIntegrableOn
      (fun z => WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) Ω volume := by
    rw [TauCeti.toLp_prodMk_eq_add (𝕜 := ℝ)]
    exact ((e.toContinuousLinearMap.comp (.inl ℝ V V)).locallyIntegrableOn_comp hloc1).add
      ((e.toContinuousLinearMap.comp (.inr ℝ V V)).locallyIntegrableOn_comp hlocI)
  exact isWeakCRSolution_iff.2 ⟨hΞq, hHloc, fun Φ =>
    ⟨hc₂.integrable_inner_crFormalAdjoint hpq hΞq Φ,
      integral_inner_crFormalAdjoint_differentiated_aux hp hq hpq hc hS hDS hξ hDξ hDη heq Φ⟩⟩

end WeakDifferentiated

/-! ### Higher-order interior regularity -/

section HigherRegularity

section Step

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ}

private local instance : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup (V × V →L[ℝ] V × V) := inferInstance
private local instance : NormedSpace ℝ (V × V →L[ℝ] V × V) := inferInstance
private local instance :
    NormedAddCommGroup (WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) := inferInstance
private local instance :
    NormedSpace ℝ (WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) := inferInstance

/-- Inductive step of `IsWeakCRSolution.memWkpLoc_succ_of_memWkpLoc`: upgrades
`ξ ∈ W^{m+1,r}_loc(Ω)` to `ξ ∈ W^{m+2,r}_loc(Ω)` without assuming `p⁻¹ + r⁻¹ < 1` by entering the
weak differentiated system at an intermediate exponent `r₁` where `p⁻¹ + r₁⁻¹ < 1` and applying the
order-`m` exponent-raising induction hypothesis on `WithLp 2 (V × V)`. -/
private theorem memWkpLoc_succ_of_memWkpLoc_step {p r : ℝ≥0} {q : ℝ≥0∞} {m : ℕ}
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    (hp : 2 < p) (hr : 1 < r) (hrp : r ≤ p) (hpq : (p : ℝ≥0∞)⁻¹ + q⁻¹ < 1)
    (hJm1 : MemWkpLoc p Ω (m + 1) J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω (m + 1) S) (hη : MemWkpLoc r Ω (m + 1) η)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hξm : MemWkpLoc r Ω (m + 1) ξ)
    (ih_prod : ∀ {q₂ : ℝ≥0∞}
      {J₂ S₂ : ℂ → WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)}
      {DJ₂ : ℂ → ℂ →L[ℝ] WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)}
      {Ξ H : ℂ → WithLp 2 (V × V)},
      (p : ℝ≥0∞)⁻¹ + q₂⁻¹ < 1 →
      MemWkpLoc p Ω (max 1 m) J₂ → HasWeakFDerivOn volume Ω J₂ DJ₂ →
      (∀ᵐ z ∂volume.restrict Ω, J₂ z * J₂ z = -1) →
      MemWkpLoc p Ω m S₂ → MemWkpLoc r Ω m H →
      IsWeakCRSolution q₂ Ω J₂ DJ₂ S₂ Ξ H → MemWkpLoc r Ω (m + 1) Ξ) :
    MemWkpLoc r Ω (m + 2) ξ := by
  have h1le : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
  have hmax : max 1 m ≤ m + 1 := max_le h1le (Nat.le_succ m)
  obtain ⟨r₁, hr₁p, hpr₁, hη_r₁⟩ :=
    (hη.of_le h1le).exists_le_and_inv_add_inv_lt_one_and_memLpLoc hp hr hrp
  have hr₁_enn : 1 < (r₁ : ℝ≥0∞) := ENNReal.one_lt_of_inv_add_inv_le_one ENNReal.coe_ne_top hpr₁.le
  obtain ⟨Dξ, hDξ, -⟩ := hξm.exists_weakFDeriv_of_isOpen
  obtain ⟨DS, hDS, -⟩ := hS.exists_weakFDeriv_of_isOpen
  obtain ⟨Dη, hDη, -⟩ := hη.exists_weakFDeriv_of_isOpen
  have hc : IsSobolevCRCoefficients p Ω J DJ S :=
    ⟨hDJ, (hJm1.of_le h1le).memLpLoc,
      memWkpLoc_zero_iff.1 ((hJm1.of_le h1le).memWkpLoc_of_hasWeakFDerivOn hDJ), hS.memLpLoc⟩
  have hξ_r₁ : MemWkpLoc r₁ Ω 1 ξ :=
    hsol.memWkpLoc_one_of_memLpLoc (by exact_mod_cast hp) hr₁_enn ENNReal.coe_ne_top
      (by exact_mod_cast hr₁p) hpq hc hJsq hη_r₁
  have hDξ_r₁ : MemLpLoc r₁ Ω Dξ := memWkpLoc_zero_iff.1 (hξ_r₁.memWkpLoc_of_hasWeakFDerivOn hDξ)
  have heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z :=
    (hc.isWeakCRSolution_iff_ae hpr₁.le ENNReal.coe_ne_top ENNReal.coe_ne_top hDξ hξ_r₁.memLpLoc
      hDξ_r₁ hsol.locallyIntegrableOn).1 (hsol.of_memLpLoc hξ_r₁.memLpLoc)
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm
  let diagL := ContinuousLinearMap.withLpDiagL 2 ℝ V V
  have hDJ₂ : HasWeakFDerivOn volume Ω (fun z => (J z).withLpProdMap 2 (J z))
      (fun z => diagL.comp (DJ z)) := by
    simpa [diagL] using hDJ.clm_comp diagL
  have hsol₂ := isWeakCRSolution_differentiated ENNReal.coe_ne_top ENNReal.coe_ne_top hpr₁.le
    (hJm1.of_le h1le) hDJ (hS.of_le h1le) hDS hξ_r₁ hDξ hDη heq
  have hJ₂sq : ∀ᵐ z ∂volume.restrict Ω,
      (J z).withLpProdMap 2 (J z) * (J z).withLpProdMap 2 (J z) = -1 := by
    filter_upwards [hJsq] with z hz
    refine ContinuousLinearMap.ext fun w => ?_
    have h := congr($(prodMap_mul_self_eq_neg_one hz) (w.fst, w.snd))
    simpa [ContinuousLinearMap.mul_def, WithLp.ext_iff, Prod.ext_iff] using h
  have hJ₂ : MemWkpLoc p Ω (max 1 m) (fun z => (J z).withLpProdMap 2 (J z)) := by
    simpa [diagL] using (hJm1.of_le hmax).clm_comp diagL
  have hS₂ : MemWkpLoc p Ω m
      (fun z => e.arrowCongr e (differentiatedCRCoefficient (S z) (DJ z))) :=
    (hS.of_succ.differentiatedCRCoefficient hJm1 hDJ).clm_comp
      (e.arrowCongr e).toContinuousLinearMap
  have hH₂ : MemWkpLoc r Ω m
      (fun z => WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) :=
    (memWkpLoc_differentiatedCR_rightSide hp hr hrp hS hDS (hξm.of_le hmax) hη hDη).clm_comp
      e.toContinuousLinearMap
  have hΞm := ih_prod hpr₁ hJ₂ hDJ₂ hJ₂sq hS₂ hH₂ hsol₂
  have hDξ' : HasWeakFDerivOn volume (Opens.interior (Ω : Set ℂ)) ξ Dξ := by
    rwa [Opens.interior_coe]
  exact hξm.memLpLoc.memWkpLoc_succ_of_hasWeakFDerivOn hDξ'
    (hΞm.clm_comp (WithLp.fstL 2 ℝ V V)) (hΞm.clm_comp (WithLp.sndL 2 ℝ V V))

end Step

/-- Finite-exponent (`ℝ≥0`) induction core for `IsWeakCRSolution.memWkpLoc_succ_of_memWkpLoc`. -/
private theorem memWkpLoc_succ_of_memWkpLoc_nnreal {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ} {p r : ℝ≥0} {q : ℝ≥0∞} {k : ℕ}
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    (hp : 2 < p) (hr : 1 < r) (hrp : r ≤ p) (hpq : (p : ℝ≥0∞)⁻¹ + q⁻¹ < 1)
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω k S) (hη : MemWkpLoc r Ω k η)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    MemWkpLoc r Ω (k + 1) ξ := by
  induction k generalizing V q with
  | zero =>
    have hc : IsSobolevCRCoefficients p Ω J DJ S :=
      ⟨hDJ, hJ.memLpLoc, memWkpLoc_zero_iff.1 (hJ.memWkpLoc_of_hasWeakFDerivOn hDJ),
        memWkpLoc_zero_iff.1 hS⟩
    exact hsol.memWkpLoc_one_of_memLpLoc (by exact_mod_cast hp) (by exact_mod_cast hr)
      ENNReal.coe_ne_top (by exact_mod_cast hrp) hpq hc hJsq (memWkpLoc_zero_iff.1 hη)
  | succ m ih =>
    have hJm1 : MemWkpLoc p Ω (m + 1) J := by simpa using hJ
    have hmax : max 1 m ≤ m + 1 := max_le (Nat.succ_le_succ (Nat.zero_le m)) (Nat.le_succ m)
    exact memWkpLoc_succ_of_memWkpLoc_step hp hr hrp hpq hJm1 hDJ hJsq hS hη hsol
      (ih hpq (hJm1.of_le hmax) hDJ hJsq hS.of_succ hη.of_succ hsol)
      fun hpr₁ hJ₂ hDJ₂ hJ₂sq hS₂ hH₂ hsol₂ => ih hpr₁ hJ₂ hDJ₂ hJ₂sq hS₂ hH₂ hsol₂

/-- **Higher-order interior regularity with exponent raising** (McDuff–Salamon, Proposition
B.4.9). If `2 < p ≤ ∞`, `1 < r < ∞`, `r ≤ p`, `p⁻¹ + q⁻¹ < 1` (allowing `p = ∞` and `q = ∞`),
`J ∈ W^{max 1 k, p}_loc(Ω)` with `J² = -1` almost everywhere on `Ω`, `S ∈ W^{k,p}_loc(Ω)`, and
`η ∈ W^{k,r}_loc(Ω)`, then every weak solution `ξ ∈ L^q_loc(Ω)` of `∂_s ξ + J ∂_t ξ + S ξ = η`
lies in `W^{k+1,r}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc_succ_of_memWkpLoc {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ} {p q r : ℝ≥0∞} {k : ℕ}
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    (hp : 2 < p) (hr : 1 < r) (hr_top : r ≠ ⊤) (hrp : r ≤ p) (hpq : p⁻¹ + q⁻¹ < 1)
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω k S) (hη : MemWkpLoc r Ω k η)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    MemWkpLoc r Ω (k + 1) ξ := by
  obtain ⟨p₀, hp₀, hrp₀, hp₀p, hp₀q⟩ :=
    ENNReal.exists_nnreal_two_lt_and_le_and_inv_add_inv_lt_one hp hr_top hrp hpq
  lift r to ℝ≥0 using hr_top
  exact memWkpLoc_succ_of_memWkpLoc_nnreal hp₀ (by exact_mod_cast hr) (ENNReal.coe_le_coe.1 hrp₀)
    hp₀q (hJ.mono_exponent hp₀p) hDJ hJsq (hS.mono_exponent hp₀p) hη hsol

/-- **Higher-order interior regularity** (McDuff–Salamon, Proposition B.4.9). Let `k : ℕ`,
`2 < p ≤ ∞`, `q < ∞`, `q ≤ p`, and `p⁻¹ + q⁻¹ < 1` (which forces `1 < q`). If
`J ∈ W^{max 1 k, p}_loc(Ω)` has weak derivative `DJ` with `J² = -1` almost everywhere on `Ω`,
`S ∈ W^{k,p}_loc(Ω)`, and `η ∈ W^{k,q}_loc(Ω)`, then every weak solution `ξ ∈ L^q_loc(Ω)` of
`∂_s ξ + J ∂_t ξ + S ξ = η` belongs to `W^{k+1,q}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc_succ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {Ω : Opens ℂ} {p q : ℝ≥0∞} {k : ℕ}
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    (hp : 2 < p) (hq_top : q ≠ ⊤) (hqp : q ≤ p) (hpq : p⁻¹ + q⁻¹ < 1)
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω k S) (hη : MemWkpLoc q Ω k η)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    MemWkpLoc q Ω (k + 1) ξ :=
  hsol.memWkpLoc_succ_of_memWkpLoc hp (ENNReal.inv_lt_one.1 (le_add_self.trans_lt hpq)) hq_top hqp
    hpq hJ hDJ hJsq hS hη

/-- **Higher-order interior regularity at a finite coefficient exponent `p`.** When `2 < p < ∞`,
`p⁻¹ + q⁻¹ < 1`, `J ∈ W^{max 1 k, p}_loc(Ω)` with `J² = -1` almost everywhere,
`S ∈ W^{k,p}_loc(Ω)`, and `η ∈ W^{k,p}_loc(Ω)`, every weak solution `ξ ∈ L^q_loc(Ω)` lies in
`W^{k+1,p}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc_succ_self {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ} {p q : ℝ≥0∞} {k : ℕ}
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ < 1)
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω k S) (hη : MemWkpLoc p Ω k η)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    MemWkpLoc p Ω (k + 1) ξ :=
  hsol.memWkpLoc_succ_of_memWkpLoc hp ((by norm_num : (1 : ℝ≥0∞) < 2).trans hp) hp_top le_rfl hpq
    hJ hDJ hJsq hS hη

/-- **Existence of a `C^k` representative.** Let `2 < r ≤ p` and `p⁻¹ + q⁻¹ < 1` (allowing `p = ∞`,
`r = ∞`, and `q = ∞`). If `J ∈ W^{max 1 k, p}_loc(Ω)` has weak derivative `DJ` with `J² = -1`
almost everywhere on `Ω`, `S ∈ W^{k,p}_loc(Ω)`, and `η ∈ W^{k,r}_loc(Ω)`, then every weak solution
`ξ ∈ L^q_loc(Ω)` agrees almost everywhere on `Ω` with a `C^k` map on `Ω`. -/
theorem IsWeakCRSolution.exists_contDiffOn_ae_eq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ} {p q r : ℝ≥0∞} {k : ℕ}
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    (hr : 2 < r) (hrp : r ≤ p) (hpq : p⁻¹ + q⁻¹ < 1)
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω k S) (hη : MemWkpLoc r Ω k η)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    ∃ g : ℂ → V, ContDiffOn ℝ k g Ω ∧ ξ =ᵐ[volume.restrict Ω] g := by
  set r₀ : ℝ≥0∞ := min r 3
  have hr₀ : 2 < r₀ := lt_min hr (by norm_num)
  have hr₀_top : r₀ ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) (min_le_right _ _)
  exact (hsol.memWkpLoc_succ_of_memWkpLoc (hr.trans_le hrp)
    ((by norm_num : (1 : ℝ≥0∞) < 2).trans hr₀) hr₀_top ((min_le_left _ _).trans hrp) hpq hJ hDJ
    hJsq hS (hη.mono_exponent (min_le_left _ _))).exists_contDiffOn_ae_eq hr₀

end HigherRegularity

/-! ### Weak linear Cauchy–Riemann solutions in finite-dimensional normed spaces -/

section NormedSpace

/-- On a finite-dimensional real inner product space, any `W^{1,q₀}_loc(Ω)` map (`1 < q₀ ≤ p`)
satisfying `∂_s ξ + J ∂_t ξ + S ξ = η` almost everywhere on `Ω` embeds via Sobolev gain into an
exponent `s` with `(p : ℝ≥0∞)⁻¹ + s⁻¹ < 1` and satisfies `IsWeakCRSolution s Ω J DJ S ξ η`. -/
private theorem isWeakCRSolution_of_hasWeakFDerivOn_ae {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {Ω : Opens ℂ} {p q₀ : ℝ≥0}
    (hp : 2 < p) (hq₀ : 1 < q₀) (hq₀p : q₀ ≤ p)
    {J S : ℂ → E →L[ℝ] E} {DJ : ℂ → ℂ →L[ℝ] E →L[ℝ] E} {ξ η : ℂ → E} {Dξ : ℂ → ℂ →L[ℝ] E}
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJ1 : MemWkpLoc p Ω 1 J)
    (hξ : MemWkpLoc q₀ Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hη : LocallyIntegrableOn η Ω volume)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z) :
    ∃ s : ℝ≥0∞, (p : ℝ≥0∞)⁻¹ + s⁻¹ < 1 ∧ IsWeakCRSolution s Ω J DJ S ξ η := by
  have hloc := Ω.isOpen.isLocallyClosed
  have hq₀1 : (1 : ℝ≥0∞) ≤ q₀ := by exact_mod_cast hq₀.le
  let _ : Fact (1 ≤ (q₀ : ℝ≥0∞)) := ⟨hq₀1⟩
  let _ : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hq₀.le.trans hq₀p⟩
  set s := ((q₀ : ℝ≥0∞)⁻¹ - (p : ℝ≥0∞)⁻¹)⁻¹
  let _ : ENNReal.HolderTriple p s q₀ :=
    ENNReal.HolderTriple.of_le (p := (p : ℝ≥0∞)) (q := q₀) (by exact_mod_cast hq₀p)
  have hps : (p : ℝ≥0∞)⁻¹ + s⁻¹ < 1 :=
    (ENNReal.HolderTriple.inv_add_inv_eq_inv (p : ℝ≥0∞) s q₀).trans_lt
      (ENNReal.inv_lt_one.2 (by exact_mod_cast hq₀))
  have hξs : MemLpLoc s Ω ξ := hξ.memLpLoc_of_holderTriple hp hq₀p
  have hDξq₀ : MemLpLoc q₀ Ω Dξ := memWkpLoc_zero_iff.1 (hξ.memWkpLoc_of_hasWeakFDerivOn hDξ)
  have hJ_top : MemLpLoc ⊤ Ω J := hJ1.memLpLoc_of_holderTriple hp le_rfl
  have hJξ_I : HasWeakLineDerivOn volume Ω (fun z => J z (ξ z))
      (fun z => DJ z I (ξ z) + J z (Dξ z I)) I := by
    simpa using (hc.hasWeakFDerivOn.bilin_of_memLpLoc (ContinuousLinearMap.id ℝ (E →L[ℝ] E))
      hp hq₀ hq₀p (hJ_top.mono_exponent le_top) hc.memLpLoc_deriv hDξ hξ.memLpLoc
      hDξq₀).hasWeakLineDerivOn I
  refine ⟨s, hps, isWeakCRSolution_iff.2 ⟨hξs, hη, fun φ =>
    ⟨hc.integrable_inner_crFormalAdjoint hps.le hξs φ, ?_⟩⟩⟩
  rw [hc.integral_inner_crFormalAdjoint_eq_sub_add hps.le hξs φ]
  have ibp1 := (hDξ.hasWeakLineDerivOn 1).integral_inner_lineDeriv_eq_neg φ
  have ibpI := hJξ_I.integral_inner_lineDeriv_eq_neg φ
  simp only [TestFunction.lineDeriv_eq_fderiv] at ibp1 ibpI
  have iD1 : Integrable (fun z => ⟪(φ : ℂ → E) z, Dξ z 1⟫_ℝ) :=
    φ.integrable_inner ((hDξq₀.clm_comp (ContinuousLinearMap.apply ℝ E 1)).locallyIntegrableOn
      hq₀1 hloc)
  have iJD : Integrable (fun z => ⟪(φ : ℂ → E) z, J z (Dξ z I)⟫_ℝ) :=
    φ.integrable_inner ((hJ_top.clm_apply_of_inv_add_inv_le
      (hDξq₀.clm_comp (ContinuousLinearMap.apply ℝ E I)) (by simp)).locallyIntegrableOn hq₀1 hloc)
  have iDJξ : Integrable (fun z => ⟪(φ : ℂ → E) z, DJ z I (ξ z)⟫_ℝ) :=
    φ.integrable_inner ((hc.memLpLoc_deriv.clm_comp
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] E) I)).locallyIntegrableOn_clm_apply hξs hps.le hloc)
  have iSξ : Integrable (fun z => ⟪(φ : ℂ → E) z, S z (ξ z)⟫_ℝ) :=
    φ.integrable_inner (hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hξs hps.le hloc)
  simp only [inner_add_right, integral_add iDJξ iJD] at ibpI
  have hpde : (∫ z, ⟪(φ : ℂ → E) z, Dξ z 1⟫_ℝ) + (∫ z, ⟪(φ : ℂ → E) z, J z (Dξ z I)⟫_ℝ) +
      (∫ z, ⟪(φ : ℂ → E) z, S z (ξ z)⟫_ℝ) = ∫ z, ⟪(φ : ℂ → E) z, η z⟫_ℝ := by
    rw [← integral_add iD1 iJD]
    refine (integral_add (iD1.add iJD) iSξ).symm.trans
      (integral_congr_ae ((ae_imp_of_ae_restrict heq).mono fun z hz => ?_))
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · simp only [Pi.add_apply, ← inner_add_right, hz hzΩ]
    · simp [image_eq_zero_of_notMem_tsupport fun h => hzΩ (φ.tsupport_subset h)]
  linarith

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ}

/-- Finite-exponent (`ℝ≥0`) core for `HasWeakFDerivOn.memWkpLoc_succ_of_ae_cauchyRiemann`. -/
private theorem memWkpLoc_succ_of_ae_cauchyRiemann_nnreal {p r : ℝ≥0} {q : ℝ≥0∞} {k : ℕ}
    {J S : ℂ → V →L[ℝ] V} {ξ η : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V}
    (hp : 2 < p) (hq : 1 < q) (hr : 1 < r) (hrp : r ≤ p)
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω k S) (hη : MemWkpLoc r Ω k η)
    (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z) :
    MemWkpLoc r Ω (k + 1) ξ := by
  have hq₀_t : min q (p : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  let q₀ : ℝ≥0 := (min q (p : ℝ≥0∞)).toNNReal
  have hq₀_coe : (q₀ : ℝ≥0∞) = min q p := ENNReal.coe_toNNReal hq₀_t
  have hq₀ : 1 < q₀ := by
    have : (1 : ℝ≥0∞) < min q p := lt_min hq (by exact_mod_cast one_lt_two.trans hp)
    exact_mod_cast this.trans_eq hq₀_coe.symm
  have hq₀p : q₀ ≤ p := ENNReal.coe_le_coe.1 (hq₀_coe.trans_le (min_le_right _ _))
  have hξ₀ : MemWkpLoc q₀ Ω 1 ξ := hξ.mono_exponent (hq₀_coe.trans_le (min_le_left _ _))
  let E := EuclideanSpace ℝ (Fin (Module.finrank ℝ V))
  let A : V ≃L[ℝ] E := (LinearEquiv.ofFinrankEq V E (by simp [E])).toContinuousLinearEquiv
  let conjA : (V →L[ℝ] V) ≃L[ℝ] E →L[ℝ] E := A.arrowCongr A
  have hJ' : MemWkpLoc p Ω (max 1 k) (fun z => conjA (J z)) := conjA.comp_memWkpLoc_iff.2 hJ
  have hS' : MemWkpLoc p Ω k (fun z => conjA (S z)) := conjA.comp_memWkpLoc_iff.2 hS
  have hη' : MemWkpLoc r Ω k (fun z => A (η z)) := A.comp_memWkpLoc_iff.2 hη
  have hξ' : MemWkpLoc q₀ Ω 1 (fun z => A (ξ z)) := A.comp_memWkpLoc_iff.2 hξ₀
  have hDξ' : HasWeakFDerivOn volume Ω (fun z => A (ξ z))
      (fun z => (A : V →L[ℝ] E).comp (Dξ z)) := hDξ.clm_comp (A : V →L[ℝ] E)
  obtain ⟨DJ', hDJ', hDJ'0⟩ := (hJ'.of_le (le_max_left 1 k)).exists_weakFDeriv_of_isOpen
  have hc' : IsSobolevCRCoefficients p Ω (fun z => conjA (J z)) DJ' (fun z => conjA (S z)) :=
    ⟨hDJ', (hJ'.of_le (le_max_left 1 k)).memLpLoc, memWkpLoc_zero_iff.1 hDJ'0, hS'.memLpLoc⟩
  have heq' : ∀ᵐ z ∂volume.restrict Ω,
      ((A : V →L[ℝ] E).comp (Dξ z)) 1 + conjA (J z) (((A : V →L[ℝ] E).comp (Dξ z)) I) +
        conjA (S z) (A (ξ z)) = A (η z) := by
    filter_upwards [heq] with z hz
    simpa [conjA, map_add] using congrArg A hz
  obtain ⟨s, hps, hsol'⟩ := isWeakCRSolution_of_hasWeakFDerivOn_ae hp hq₀ hq₀p hc'
    (hJ'.of_le (le_max_left 1 k)) hξ' hDξ'
    (hη'.memLpLoc.locallyIntegrableOn (by exact_mod_cast hr.le) Ω.isOpen.isLocallyClosed) heq'
  have hJsq' : ∀ᵐ z ∂volume.restrict Ω, conjA (J z) * conjA (J z) = -1 := by
    filter_upwards [hJsq] with z hz
    refine ContinuousLinearMap.ext fun y => ?_
    have hy : J z (J z (A.symm y)) = -A.symm y := by simpa using congr($hz (A.symm y))
    simp [conjA, ContinuousLinearMap.mul_def, hy]
  exact A.comp_memWkpLoc_iff.1
    (memWkpLoc_succ_of_memWkpLoc_nnreal hp hr hrp hps hJ' hDJ' hJsq' hS' hη' hsol')

/-- **Inhomogeneous interior Sobolev regularity on a finite-dimensional real normed space.** Let
`2 < p ≤ ∞`, `1 < q ≤ ∞`, `1 < r < ∞`, and `r ≤ p`. If `J ∈ W^{max 1 k, p}_loc(Ω)` with
`J² = -1` almost everywhere on `Ω`, `S ∈ W^{k,p}_loc(Ω)`, `η ∈ W^{k,r}_loc(Ω)`, and
`ξ ∈ W^{1,q}_loc(Ω)` has weak derivative `Dξ` satisfying `Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z`
almost everywhere on `Ω`, then `ξ ∈ W^{k+1,r}_loc(Ω)`. -/
theorem HasWeakFDerivOn.memWkpLoc_succ_of_ae_cauchyRiemann {p q r : ℝ≥0∞} {k : ℕ}
    {J S : ℂ → V →L[ℝ] V} {ξ η : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V}
    (hp : 2 < p) (hq : 1 < q) (hr : 1 < r) (hr_top : r ≠ ⊤) (hrp : r ≤ p)
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω k S) (hη : MemWkpLoc r Ω k η)
    (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z) :
    MemWkpLoc r Ω (k + 1) ξ := by
  have hp_top_inv : p⁻¹ + (⊤ : ℝ≥0∞)⁻¹ < 1 := by
    simpa using ENNReal.inv_lt_one.2 ((by norm_num : (1 : ℝ≥0∞) < 2).trans hp)
  obtain ⟨p₀, hp₀, hrp₀, hp₀p, -⟩ :=
    ENNReal.exists_nnreal_two_lt_and_le_and_inv_add_inv_lt_one hp hr_top hrp hp_top_inv
  lift r to ℝ≥0 using hr_top
  exact memWkpLoc_succ_of_ae_cauchyRiemann_nnreal hp₀ hq (by exact_mod_cast hr)
    (ENNReal.coe_le_coe.1 hrp₀) (hJ.mono_exponent hp₀p) hJsq (hS.mono_exponent hp₀p) hη hξ hDξ heq

/-- **Interior Sobolev regularity for `TauCeti.IsWeakLinearCauchyRiemannOn` on a finite-dimensional
real normed space.** If `2 < p < ∞`, `1 < q ≤ ∞`, `J ∈ W^{max 1 k, p}_loc(Ω)` with `J² = -1` almost
everywhere on `Ω`, and `S ∈ W^{k,p}_loc(Ω)`, then every weak solution `ξ` of
`∂_s ξ + J ∂_t ξ + S ξ = 0` on `Ω` at exponent `q` lies in `W^{k+1,p}_loc(Ω)`. -/
theorem IsWeakLinearCauchyRiemannOn.memWkpLoc_succ {p q : ℝ≥0∞} {k : ℕ}
    {J S : ℂ → V →L[ℝ] V} {ξ : ℂ → V} (hp : 2 < p) (hp_top : p ≠ ⊤) (hq : 1 < q)
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω k S) (h : IsWeakLinearCauchyRiemannOn q Ω J S ξ) :
    MemWkpLoc p Ω (k + 1) ξ := by
  obtain ⟨-, hξq, Dξ, hDξ, hDξq, heq⟩ := isWeakLinearCauchyRiemannOn_iff_of_isOpen.1 h
  have hξ1 : MemWkpLoc q Ω 1 ξ :=
    memWkpLoc_succ_iff_of_isOpen.2 ⟨hξq, Dξ, hDξ, memWkpLoc_zero_iff.2 hDξq⟩
  exact hDξ.memWkpLoc_succ_of_ae_cauchyRiemann hp hq ((by norm_num : (1 : ℝ≥0∞) < 2).trans hp)
    hp_top le_rfl hJ hJsq hS memWkpLoc_zero_fun hξ1 heq

/-- **`C^k` interior regularity for `TauCeti.IsWeakLinearCauchyRiemannOn`.** If `2 < p ≤ ∞`
(allowing `p = ∞`), `1 < q ≤ ∞`, `J ∈ W^{max 1 k, p}_loc(Ω)` with `J² = -1` almost everywhere on
`Ω`, and `S ∈ W^{k,p}_loc(Ω)`, then every continuous weak solution `ξ` of
`∂_s ξ + J ∂_t ξ + S ξ = 0` on `Ω` at exponent `q` is of class `C^k` on `Ω`. -/
theorem IsWeakLinearCauchyRiemannOn.contDiffOn {p q : ℝ≥0∞} {k : ℕ}
    {J S : ℂ → V →L[ℝ] V} {ξ : ℂ → V} (hp : 2 < p) (hq : 1 < q)
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω k S) (h : IsWeakLinearCauchyRiemannOn q Ω J S ξ) :
    ContDiffOn ℝ k ξ Ω := by
  set p₀ : ℝ≥0∞ := min p 3
  have hp₀ : 2 < p₀ := lt_min hp (by norm_num)
  have hp₀_top : p₀ ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) (min_le_right _ _)
  have hW : MemWkpLoc p₀ Ω (k + 1) ξ :=
    h.memWkpLoc_succ hp₀ hp₀_top hq (hJ.mono_exponent (min_le_left _ _)) hJsq
      (hS.mono_exponent (min_le_left _ _))
  obtain ⟨g, hg, hae⟩ := hW.exists_contDiffOn_ae_eq hp₀
  exact hg.congr (Measure.eqOn_open_of_ae_eq hae Ω.isOpen h.continuousOn hg.continuousOn)

/-- **`C^∞` interior regularity for `TauCeti.IsWeakLinearCauchyRiemannOn` with smooth
coefficients.** If `1 < q ≤ ∞`, `J` and `S` are `C^∞` on `Ω`, and `J² = -1` almost everywhere on
`Ω`, then every weak solution `ξ` of `∂_s ξ + J ∂_t ξ + S ξ = 0` at exponent `q` is `C^∞` on `Ω`. -/
theorem IsWeakLinearCauchyRiemannOn.contDiffOn_infty {q : ℝ≥0∞} (hq : 1 < q)
    {J S : ℂ → V →L[ℝ] V} {ξ : ℂ → V} (hJ : ContDiffOn ℝ ∞ J Ω)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) (hS : ContDiffOn ℝ ∞ S Ω)
    (h : IsWeakLinearCauchyRiemannOn q Ω J S ξ) :
    ContDiffOn ℝ ∞ ξ Ω :=
  _root_.contDiffOn_infty.2 fun k =>
    h.contDiffOn (p := ⊤) (by simp) hq ((hJ.of_le (by simp)).memWkpLoc subset_rfl) hJsq
      ((hS.of_le (by simp)).memWkpLoc subset_rfl)

end NormedSpace

end TauCeti
