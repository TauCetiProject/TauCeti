/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Regularity.OrderZero
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.ProdLp
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Differentiated
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Regularity.Mollify
import TauCeti.Analysis.Complex.OperatorNorm
import TauCeti.Analysis.Distribution.TestFunction.Basic
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.Local.Morrey.Higher
import TauCeti.Analysis.Sobolev.Local.Multiplication.Higher
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder

/-!
# Higher-order interior Sobolev regularity for rough-coefficient Cauchy–Riemann operators

Let `Ω ⊆ ℂ` be open and let `V` be a finite-dimensional real Hilbert space (or finite-dimensional
real normed space for the strong and homogeneous linear corollaries). Consider the linear
Cauchy–Riemann operator `D ξ = ∂_s ξ + J ∂_t ξ + S ξ` with Sobolev coefficients
`J ∈ W^{max 1 k, p}_loc(Ω)` and `S ∈ W^{k,p}_loc(Ω)` satisfying `J² = -1` almost everywhere on `Ω`.

Building on the order-zero interior regularity proved in
`TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Regularity.OrderZero` (McDuff–Salamon,
Lemma B.4.6), which this module re-exports, this file proves higher-order interior Sobolev
regularity (McDuff–Salamon, Proposition B.4.9) and its corollaries:

1. **Higher-order regularity (Proposition B.4.9)**
   (`TauCeti.memWkpLoc_succ_of_isWeakCRSolution`).
   For `k ≥ 1`, knowing `ξ ∈ W^{k,q}_loc(Ω)` implies `ξ ∈ W^{1,q}_loc(Ω)` satisfies the strong
   equation almost everywhere. Testing against `J_nᵀ φ` and mollifying shows that the partial
   derivative pair `Ξ = (∂_s ξ, ∂_t ξ)` in `WithLp 2 (V × V)` is itself a weak solution of the
   differentiated system `∂_s Ξ + diag(J, J) ∂_t Ξ + S₂ Ξ = η₂` without requiring a priori `W^{2,q}`
   regularity. Induction on `k` then gives `ξ ∈ W^{k+1,q}_loc(Ω)`.
2. **Normed-space and smooth-coefficient corollaries.**
   Transporting along a continuous linear equivalence `V ≃L[ℝ] EuclideanSpace ℝ (Fin d)` removes
   the Hilbert-space hypothesis for `W^{1,q}_loc` strong solutions
   (`TauCeti.memWkpLoc_succ_of_ae_cauchyRiemann`) and homogeneous linear weak solutions
   (`TauCeti.IsWeakLinearCauchyRiemannOn.memWkpLoc_succ`). For smooth `J, S, η`, combining all
   orders with Morrey's embedding gives a `C^∞` representative
   (`TauCeti.exists_contDiffOn_infty_ae_eq_of_isWeakCRSolution`).

## Main declarations

* `TauCeti.memWkpLoc_succ_of_isWeakCRSolution`: McDuff–Salamon Proposition B.4.9.
* `TauCeti.memWkpLoc_succ_of_ae_cauchyRiemann`: higher-order regularity for `W^{1,q}_loc` strong
  solutions in an arbitrary finite-dimensional real normed space.
* `TauCeti.IsWeakLinearCauchyRiemannOn.memWkpLoc_succ`: higher-order regularity for homogeneous
  linear weak solutions.
* `TauCeti.exists_contDiffOn_infty_ae_eq_of_isWeakCRSolution`: smooth-coefficient hypoellipticity.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Proposition B.4.9).
-/

public noncomputable section

open Complex Filter MeasureTheory Set TopologicalSpace
open scoped Convolution ContDiff Distributions ENNReal InnerProductSpace LineDeriv NNReal Topology

namespace TauCeti

/-! ### The weak differentiated system and higher-order regularity -/

section HigherOrder

section ProdL2

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Conjugating an operator on `V × V` by `WithLp.prodContinuousLinearEquiv 2 ℝ V V`. -/
private def conjProdL2L :
    (V × V →L[ℝ] V × V) →L[ℝ] (WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) :=
  (ContinuousLinearMap.compL ℝ (WithLp 2 (V × V)) (V × V) (WithLp 2 (V × V))
    (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm.toContinuousLinearMap).comp
    ((ContinuousLinearMap.compL ℝ (WithLp 2 (V × V)) (V × V) (V × V)).flip
      (WithLp.prodContinuousLinearEquiv 2 ℝ V V).toContinuousLinearMap)

private theorem conjProdL2L_apply {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A : V × V →L[ℝ] V × V) (x : WithLp 2 (V × V)) :
    conjProdL2L V A x = WithLp.toLp 2 (A (WithLp.ofLp x)) := rfl

/-- The diagonal map `A ↦ conjProdL2L (A.prodMap A)` as a continuous linear map. -/
private def diagProdL2L :
    (V →L[ℝ] V) →L[ℝ] (WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) :=
  (conjProdL2L V).comp ((ContinuousLinearMap.prodMapL ℝ V V V V).comp
    ((ContinuousLinearMap.id ℝ (V →L[ℝ] V)).prod (ContinuousLinearMap.id ℝ (V →L[ℝ] V))))

private theorem diagProdL2L_apply {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A : V →L[ℝ] V) (x : WithLp 2 (V × V)) :
    diagProdL2L V A x = WithLp.toLp 2 (A x.ofLp.1, A x.ofLp.2) := rfl

end ProdL2

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Opens ℂ}

omit [CompleteSpace V] in
/-- For any test function `ψ ∈ 𝓓(Ω, V)` and any weakly differentiable field `ξ` with weak
derivative `Dξ`, `∫ ⟪∂_s ψ, ∂_t ξ⟫ = ∫ ⟪∂_t ψ, ∂_s ξ⟫`. -/
private theorem integral_inner_fderiv_one_eq_fderiv_I [FiniteDimensional ℝ V]
    {ξ : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V} (hξ : HasWeakFDerivOn volume Ω ξ Dξ) (ψ : 𝓓(Ω, V)) :
    ∫ z, ⟪fderiv ℝ (ψ : ℂ → V) z 1, Dξ z I⟫_ℝ =
      ∫ z, ⟪fderiv ℝ (ψ : ℂ → V) z I, Dξ z 1⟫_ℝ := by
  have h1 := (hξ.hasWeakLineDerivOn I).integral_inner_lineDeriv_eq_neg (∂_{(1 : ℂ)} ψ)
  have h2 := (hξ.hasWeakLineDerivOn 1).integral_inner_lineDeriv_eq_neg (∂_{I} ψ)
  simp only [TestFunction.lineDerivOp_apply_eq_fderiv] at h1 h2
  simp_rw [← TestFunction.lineDerivOp_apply] at h1 h2
  rw [TestFunction.lineDerivOp_comm] at h1
  linarith

/-- Scalar-test-function form of the commutator identity: for `α ∈ 𝓓(Ω, ℝ)` and `v ∈ V`,
`∫ ⟪(∂_s α) v, J ∂_t ξ⟫ + ∫ ⟪α v, (∂_s J) ∂_t ξ⟫ =
∫ ⟪(∂_t α) v, J ∂_s ξ⟫ + ∫ ⟪α v, (∂_t J) ∂_s ξ⟫`. -/
private theorem integral_comm_differentiated_smul [FiniteDimensional ℝ V] {p q : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {J : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (hJ : HasWeakFDerivOn volume Ω J DJ) (hJinf : MemLpLoc ∞ Ω J) (hDJp : MemLpLoc p Ω DJ)
    {ξ : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V} (hξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hDξq : MemLpLoc q Ω Dξ) (α : 𝓓(Ω, ℝ)) (v : V) :
    (∫ z, ⟪fderiv ℝ (α : ℂ → ℝ) z 1 • v, J z (Dξ z I)⟫_ℝ) +
      (∫ z, ⟪(α : ℂ → ℝ) z • v, DJ z 1 (Dξ z I)⟫_ℝ) =
    (∫ z, ⟪fderiv ℝ (α : ℂ → ℝ) z I • v, J z (Dξ z 1)⟫_ℝ) +
      ∫ z, ⟪(α : ℂ → ℝ) z • v, DJ z I (Dξ z 1)⟫_ℝ := by
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hloc := Ω.isOpen.isLocallyClosed
  obtain ⟨W, hαW, hWΩ, hWc⟩ :=
    Opens.exists_between_and_isCompact_closure α.hasCompactSupport α.tsupport_subset
  obtain ⟨W', hWW', hW'Ω, hW'c⟩ := Opens.exists_between_and_isCompact_closure hWc hWΩ
  obtain ⟨ρ, hρ, hsupp⟩ := ContDiffBump.exists_seq_sub_tsupport_subset (μ := volume) hWc hWW'
  have hWsubW' : (W : Set ℂ) ⊆ W' := subset_closure.trans hWW'
  let Jn : ℕ → ℂ → V →L[ℝ] V := fun n =>
    (ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((W' : Set ℂ).indicator J)
  have hJW'_inf : MemLp J ∞ (volume.restrict (W' : Set ℂ)) :=
    hJinf.memLp_of_closure_subset hW'c hW'Ω
  have hJn_smooth (n : ℕ) : ContDiff ℝ ∞ (Jn n) :=
    ((ρ n).hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) ((ρ n).contDiff_normed (n := (⊤ : ℕ∞)))
      (((memLp_indicator_iff_restrict W'.isOpen.measurableSet.nullMeasurableSet).2
        hJW'_inf).locallyIntegrable le_top)
  let adjV : (V →L[ℝ] V) →L[ℝ] V :=
    (ContinuousLinearMap.apply ℝ V v).comp
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := V)
        (F := V)).toContinuousLinearEquiv.toContinuousLinearMap
  have hadjV (A : V →L[ℝ] V) : adjV A = ContinuousLinearMap.adjoint A v := rfl
  let ψ : ℕ → 𝓓(Ω, V) := fun n =>
    { toFun := fun z => (α : ℂ → ℝ) z • ContinuousLinearMap.adjoint (Jn n z) v
      contDiff' := α.contDiff.smul (adjV.contDiff.comp (hJn_smooth n))
      hasCompactSupport' := α.hasCompactSupport.smul_right
      tsupport_subset' := (tsupport_smul_subset_left _ _).trans α.tsupport_subset }
  have hDξ1q : MemLpLoc q Ω (fun z => Dξ z 1) := hDξq.clm_comp (ContinuousLinearMap.apply ℝ V 1)
  have hDξIq : MemLpLoc q Ω (fun z => Dξ z I) := hDξq.clm_comp (ContinuousLinearMap.apply ℝ V I)
  have hDξ1_loc := hDξ1q.locallyIntegrableOn hq1 hloc
  have hDξI_loc := hDξIq.locallyIntegrableOn hq1 hloc
  have hfderiv_ψ (n : ℕ) (z w : ℂ) :
      fderiv ℝ (ψ n : ℂ → V) z w =
        (α : ℂ → ℝ) z • ContinuousLinearMap.adjoint (fderiv ℝ (Jn n) z w) v +
          fderiv ℝ (α : ℂ → ℝ) z w • ContinuousLinearMap.adjoint (Jn n z) v := by
    have h1 := (α.contDiff.differentiable (by simp) z).hasFDerivAt
    have h2 := adjV.hasFDerivAt.comp z
      ((hJn_smooth n).differentiable (by simp) z).hasFDerivAt
    have hfun : ((α : ℂ → ℝ) • (adjV ∘ Jn n)) = (ψ n : ℂ → V) := rfl
    have h3 := (hfun ▸ (h1.smul h2)).fderiv
    simpa [hadjV] using congr($h3 w)
  let α1 : 𝓓(Ω, ℝ) := ∂_{(1 : ℂ)} α
  let αI : 𝓓(Ω, ℝ) := ∂_{I} α
  have hintI (β : 𝓓(Ω, ℝ)) {u : ℂ → V} (hu : LocallyIntegrableOn u Ω volume) :
      Integrable (fun z => ⟪(β : ℂ → ℝ) z • v, u z⟫_ℝ) volume :=
    (TestFunction.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ v) β).integrable_inner hu
  have hEq (n : ℕ) :
      (∫ z, ⟪(α1 : ℂ → ℝ) z • v, Jn n z (Dξ z I)⟫_ℝ) +
        (∫ z, ⟪(α : ℂ → ℝ) z • v, fderiv ℝ (Jn n) z 1 (Dξ z I)⟫_ℝ) =
      (∫ z, ⟪(αI : ℂ → ℝ) z • v, Jn n z (Dξ z 1)⟫_ℝ) +
        ∫ z, ⟪(α : ℂ → ℝ) z • v, fderiv ℝ (Jn n) z I (Dξ z 1)⟫_ℝ := by
    have hcomm := integral_inner_fderiv_one_eq_fderiv_I hξ (ψ n)
    have hJn_loc {u : ℂ → V} (hu : LocallyIntegrableOn u Ω volume) :
        LocallyIntegrableOn (fun z => Jn n z (u z)) Ω volume :=
      ((hJn_smooth n).continuous.continuousOn.memLpLoc (p := ∞)).locallyIntegrableOn_clm_apply
        ((memLpLoc_one_iff_locallyIntegrableOn hloc).2 hu) (by simp) hloc
    have hfJn_loc (w : ℂ) {u : ℂ → V} (hu : LocallyIntegrableOn u Ω volume) :
        LocallyIntegrableOn (fun z => fderiv ℝ (Jn n) z w (u z)) Ω volume :=
      ((((hJn_smooth n).fderiv_right (m := ∞) (by simp)).continuous.clm_apply
        (continuous_const (y := w))).continuousOn.memLpLoc (p := ∞)).locallyIntegrableOn_clm_apply
        ((memLpLoc_one_iff_locallyIntegrableOn hloc).2 hu) (by simp) hloc
    have hdir (w : ℂ) (β : 𝓓(Ω, ℝ)) (hβ : ∀ z, (β : ℂ → ℝ) z = fderiv ℝ (α : ℂ → ℝ) z w)
        {u : ℂ → V} (hu : LocallyIntegrableOn u Ω volume) :
        ∫ z, ⟪fderiv ℝ (ψ n : ℂ → V) z w, u z⟫_ℝ =
          (∫ z, ⟪(α : ℂ → ℝ) z • v, fderiv ℝ (Jn n) z w (u z)⟫_ℝ) +
            ∫ z, ⟪(β : ℂ → ℝ) z • v, Jn n z (u z)⟫_ℝ := by
      have hpt (z : ℂ) : ⟪fderiv ℝ (ψ n : ℂ → V) z w, u z⟫_ℝ =
          ⟪(α : ℂ → ℝ) z • v, fderiv ℝ (Jn n) z w (u z)⟫_ℝ +
            ⟪(β : ℂ → ℝ) z • v, Jn n z (u z)⟫_ℝ := by
        simp only [hfderiv_ψ, inner_add_left, inner_smul_left, RCLike.conj_to_real,
          ContinuousLinearMap.adjoint_inner_left, hβ]
      simp_rw [hpt]
      exact integral_add (hintI α (hfJn_loc w hu)) (hintI β (hJn_loc hu))
    have hL := hdir 1 α1 (TestFunction.lineDerivOp_apply_eq_fderiv α 1) hDξI_loc
    have hR := hdir I αI (TestFunction.lineDerivOp_apply_eq_fderiv α I) hDξ1_loc
    linarith
  have l1 := tendsto_integral_smul_inner_mollify hWsubW' hρ hJW'_inf α1
    ((TestFunction.tsupport_lineDerivOp_subset α 1).trans hαW) v hDξI_loc
  have l2 := tendsto_integral_smul_inner_fderiv_mollify hWsubW' hp1 hpq hρ hsupp hW'c hW'Ω
    hJ hJW'_inf hDJp α hαW v hDξIq 1
  have l3 := tendsto_integral_smul_inner_mollify hWsubW' hρ hJW'_inf αI
    ((TestFunction.tsupport_lineDerivOp_subset α I).trans hαW) v hDξ1_loc
  have l4 := tendsto_integral_smul_inner_fderiv_mollify hWsubW' hp1 hpq hρ hsupp hW'c hW'Ω
    hJ hJW'_inf hDJp α hαW v hDξ1q I
  have hlim := tendsto_nhds_unique (l1.add l2) ((funext hEq) ▸ (l3.add l4))
  simpa only [α1, αI, TestFunction.lineDerivOp_apply_eq_fderiv] using hlim

/-- Key commutator identity for the first component of the weak differentiated system:
`∫ ⟪∂_s φ, J ∂_t ξ⟫ + ∫ ⟪φ, (∂_s J) ∂_t ξ⟫ = ∫ ⟪∂_t φ, J ∂_s ξ⟫ + ∫ ⟪φ, (∂_t J) ∂_s ξ⟫`. -/
private theorem integral_comm_differentiated [FiniteDimensional ℝ V] {p q : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {J : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (hJ : HasWeakFDerivOn volume Ω J DJ) (hJinf : MemLpLoc ∞ Ω J) (hDJp : MemLpLoc p Ω DJ)
    {ξ : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V} (hξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hDξq : MemLpLoc q Ω Dξ) (φ : 𝓓(Ω, V)) :
    (∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1, J z (Dξ z I)⟫_ℝ) +
      (∫ z, ⟪(φ : ℂ → V) z, DJ z 1 (Dξ z I)⟫_ℝ) =
    (∫ z, ⟪fderiv ℝ (φ : ℂ → V) z I, J z (Dξ z 1)⟫_ℝ) +
      ∫ z, ⟪(φ : ℂ → V) z, DJ z I (Dξ z 1)⟫_ℝ := by
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hloc := Ω.isOpen.isLocallyClosed
  let b := stdOrthonormalBasis ℝ V
  let α : Fin (Module.finrank ℝ V) → 𝓓(Ω, ℝ) :=
    fun i => TestFunction.postcompCLM (innerSL ℝ (b i)) φ
  have hφ_eq (z : ℂ) : (φ : ℂ → V) z = ∑ i, (α i : ℂ → ℝ) z • b i := by
    simpa [α, TestFunction.postcompCLM_apply] using (b.sum_repr' ((φ : ℂ → V) z)).symm
  have hfderiv_α (i : Fin (Module.finrank ℝ V)) (z w : ℂ) :
      fderiv ℝ (α i : ℂ → ℝ) z w = ⟪b i, fderiv ℝ (φ : ℂ → V) z w⟫_ℝ := by
    have h := ((innerSL ℝ (b i)).hasFDerivAt.comp z
      (φ.contDiff.differentiable (by simp) z).hasFDerivAt).fderiv
    simpa [α, TestFunction.postcompCLM_apply] using congr($h w)
  have hfderiv_φ_eq (z w : ℂ) :
      fderiv ℝ (φ : ℂ → V) z w = ∑ i, fderiv ℝ (α i : ℂ → ℝ) z w • b i := by
    simpa [hfderiv_α] using (b.sum_repr' (fderiv ℝ (φ : ℂ → V) z w)).symm
  have hDξ1q : MemLpLoc q Ω (fun z => Dξ z 1) := hDξq.clm_comp (ContinuousLinearMap.apply ℝ V 1)
  have hDξIq : MemLpLoc q Ω (fun z => Dξ z I) := hDξq.clm_comp (ContinuousLinearMap.apply ℝ V I)
  have hDJ1p : MemLpLoc p Ω (fun z => DJ z 1) :=
    hDJp.clm_comp (G := V →L[ℝ] V) (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) 1)
  have hDJIp : MemLpLoc p Ω (fun z => DJ z I) :=
    hDJp.clm_comp (G := V →L[ℝ] V) (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)
  have hloc_JDξ1 := hJinf.locallyIntegrableOn_clm_apply
    ((memLpLoc_one_iff_locallyIntegrableOn hloc).2 (hDξ1q.locallyIntegrableOn hq1 hloc))
    (by simp) hloc
  have hloc_JDξI := hJinf.locallyIntegrableOn_clm_apply
    ((memLpLoc_one_iff_locallyIntegrableOn hloc).2 (hDξIq.locallyIntegrableOn hq1 hloc))
    (by simp) hloc
  have hloc_DJ1DξI := hDJ1p.locallyIntegrableOn_clm_apply hDξIq hpq hloc
  have hloc_DJIDξ1 := hDJIp.locallyIntegrableOn_clm_apply hDξ1q hpq hloc
  have hint_smul (i : Fin (Module.finrank ℝ V)) {u : ℂ → V}
      (hu : LocallyIntegrableOn u Ω volume) :
      Integrable (fun z => ⟪(α i : ℂ → ℝ) z • b i, u z⟫_ℝ) volume :=
    (TestFunction.postcompCLM
      (ContinuousLinearMap.toSpanSingleton ℝ (b i)) (α i)).integrable_inner hu
  have hint_deriv (i : Fin (Module.finrank ℝ V)) (w : ℂ) {u : ℂ → V}
      (hu : LocallyIntegrableOn u Ω volume) :
      Integrable (fun z => ⟪fderiv ℝ (α i : ℂ → ℝ) z w • b i, u z⟫_ℝ) volume := by
    simpa only [TestFunction.postcompCLM_apply, Function.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, TestFunction.lineDerivOp_apply_eq_fderiv] using
      (TestFunction.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (b i))
        (∂_{w} (α i))).integrable_inner hu
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl fun i _ =>
    integral_comm_differentiated_smul hp1 hpq hJ hJinf hDJp hξ hDξq (α i) (b i)
  simp only [Finset.sum_add_distrib] at hsum
  rw [← integral_finsetSum _ fun i _ => hint_deriv i 1 hloc_JDξI,
    ← integral_finsetSum _ fun i _ => hint_smul i hloc_DJ1DξI,
    ← integral_finsetSum _ fun i _ => hint_deriv i I hloc_JDξ1,
    ← integral_finsetSum _ fun i _ => hint_smul i hloc_DJIDξ1] at hsum
  simpa only [← sum_inner, ← hφ_eq, ← hfderiv_φ_eq] using hsum

/-- **The weak differentiated system (assuming only `ξ ∈ W^{1,q}_loc`).** Let `2 < p < ∞`,
`1/p + 1/q ≤ 1`, `1 < q ≤ p`, `J, S ∈ W^{1,p}_loc`, `ξ, η ∈ W^{1,q}_loc` with weak derivatives
`DJ, DS, Dξ, Dη`, and `∂_s ξ + J ∂_t ξ + S ξ = η` almost everywhere on `Ω`. Then
`Ξ = toLp 2 (∂_s ξ, ∂_t ξ)` is a weak solution on `WithLp 2 (V × V)` of the differentiated system
with `J₂ = diag(J, J)`, `S₂ = [[S, ∂_s J], [0, S + ∂_t J]]`, and
`η₂ = toLp 2 (∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)`. -/
private theorem isWeakCRSolution_differentiated [FiniteDimensional ℝ V] {p q : ℝ≥0}
    (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p) (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ ≤ 1)
    {J S : ℂ → V →L[ℝ] V} {DJ DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    {ξ η : ℂ → V} {Dξ Dη : ℂ → ℂ →L[ℝ] V}
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hη : MemWkpLoc q Ω 1 η) (hDη : HasWeakFDerivOn volume Ω η Dη)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z) :
    IsWeakCRSolution q Ω
      (fun z => diagProdL2L V (J z))
      (fun z => (diagProdL2L V).comp (DJ z))
      (fun z => conjProdL2L V (differentiatedCRCoefficient (S z) (DJ z)))
      (fun z => WithLp.toLp 2 (Dξ z 1, Dξ z I))
      (fun z => WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) := by
  -- Step 1: Verify Sobolev regularity of the differentiated coefficients, `Ξ`, and `η₂`.
  have : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast (one_lt_two.trans hp).le⟩
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq.le⟩
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hq1 : (1 : ℝ≥0∞) ≤ q := Fact.out
  have hloc := Ω.isOpen.isLocallyClosed
  have hJinf : MemLpLoc ∞ Ω J := hJ.memLpLoc_of_holderTriple hp le_rfl
  have hSinf : MemLpLoc ∞ Ω S := hS.memLpLoc_of_holderTriple hp le_rfl
  have hDJp := hJ.memLpLoc_of_hasWeakFDerivOn hDJ
  have hDSp := hS.memLpLoc_of_hasWeakFDerivOn hDS
  have hDξq := hξ.memLpLoc_of_hasWeakFDerivOn hDξ
  have hDηq := hη.memLpLoc_of_hasWeakFDerivOn hDη
  let eL2 : (V × V) ≃L[ℝ] WithLp 2 (V × V) := (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm
  have hΞq : MemLpLoc q Ω (fun z => WithLp.toLp 2 (Dξ z 1, Dξ z I)) :=
    (memWkpLoc_zero_iff.1 (hξ.memWkpLoc_partials_of_hasWeakFDerivOn hDξ)).clm_comp
      eL2.toContinuousLinearMap
  have hEtaTilde_q : MemLpLoc q Ω
      (fun z => WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) :=
    (memLpLoc_differentiatedCR_rightSide hp hq.le hqp hS hDS hξ hη hDη).clm_comp
      eL2.toContinuousLinearMap
  have hS2p : MemLpLoc p Ω (fun z => differentiatedCRCoefficient (S z) (DJ z)) :=
    memWkpLoc_zero_iff.1 (hS.of_succ.differentiatedCRCoefficient hJ hDJ)
  have hJ_tilde : MemWkpLoc p Ω 1 (fun z => diagProdL2L V (J z)) :=
    hJ.clm_comp (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) (diagProdL2L V)
  have hDJ_tilde : HasWeakFDerivOn volume Ω (fun z => diagProdL2L V (J z))
      (fun z => (diagProdL2L V).comp (DJ z)) :=
    hDJ.clm_comp (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) (diagProdL2L V)
  have hc2 : IsSobolevCRCoefficients p Ω
      (fun z => diagProdL2L V (J z))
      (fun z => (diagProdL2L V).comp (DJ z))
      (fun z => conjProdL2L V (differentiatedCRCoefficient (S z) (DJ z))) :=
    ⟨hDJ_tilde, hJ_tilde.memLpLoc, hJ_tilde.memLpLoc_of_hasWeakFDerivOn hDJ_tilde,
      hS2p.clm_comp (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) (conjProdL2L V)⟩
  have hSξ_weak : HasWeakFDerivOn volume Ω (fun z => S z (ξ z))
      (fun z => (ContinuousLinearMap.id ℝ (V →L[ℝ] V)).precompL ℂ (DS z) (ξ z) +
        (ContinuousLinearMap.id ℝ (V →L[ℝ] V)).precompR ℂ (S z) (Dξ z)) :=
    hDS.bilin_of_memLpLoc (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hq hqp
      (hSinf.mono_exponent le_top) hDSp hDξ hξ.memLpLoc hDξq
  -- Step 2: Record local integrability of every partial term and decompose `Φ = (φ₁, φ₂)`.
  have hDξq_w (w : ℂ) : MemLpLoc q Ω (fun z => Dξ z w) :=
    hDξq.clm_comp (ContinuousLinearMap.apply ℝ V w)
  have hDJp_w (w : ℂ) : MemLpLoc p Ω (fun z => DJ z w) :=
    hDJp.clm_comp (G := V →L[ℝ] V) (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) w)
  have hDSp_w (w : ℂ) : MemLpLoc p Ω (fun z => DS z w) :=
    hDSp.clm_comp (G := V →L[ℝ] V) (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) w)
  have hDηq_w (w : ℂ) : MemLpLoc q Ω (fun z => Dη z w) :=
    hDηq.clm_comp (ContinuousLinearMap.apply ℝ V w)
  have hloc_Dξ (w : ℂ) := (hDξq_w w).locallyIntegrableOn hq1 hloc
  have hloc_JDξ (w : ℂ) := hJ.memLpLoc.locallyIntegrableOn_clm_apply (hDξq_w w) hpq hloc
  have hloc_DJDξ (w₁ w₂ : ℂ) := (hDJp_w w₁).locallyIntegrableOn_clm_apply (hDξq_w w₂) hpq hloc
  have hloc_SDξ (w : ℂ) := hS.memLpLoc.locallyIntegrableOn_clm_apply (hDξq_w w) hpq hloc
  have hloc_Sξ := hS.memLpLoc.locallyIntegrableOn_clm_apply hξ.memLpLoc hpq hloc
  have hloc_η := hη.memLpLoc.locallyIntegrableOn hq1 hloc
  have hloc_Dη (w : ℂ) := (hDηq_w w).locallyIntegrableOn hq1 hloc
  have hloc_DSξ (w : ℂ) := (hDSp_w w).locallyIntegrableOn_clm_apply hξ.memLpLoc hpq hloc
  refine isWeakCRSolution_iff.2 ⟨hΞq, hEtaTilde_q.locallyIntegrableOn hq1 hloc, fun Φ =>
    ⟨hc2.integrable_inner_crFormalAdjoint hpq hΞq Φ, ?_⟩⟩
  let p₁ : WithLp 2 (V × V) →L[ℝ] V :=
    (ContinuousLinearMap.fst ℝ V V).comp eL2.symm.toContinuousLinearMap
  let p₂ : WithLp 2 (V × V) →L[ℝ] V :=
    (ContinuousLinearMap.snd ℝ V V).comp eL2.symm.toContinuousLinearMap
  let φ₁ : 𝓓(Ω, V) := TestFunction.postcompCLM p₁ Φ
  let φ₂ : 𝓓(Ω, V) := TestFunction.postcompCLM p₂ Φ
  have hfderiv_φ₁ (z w : ℂ) : fderiv ℝ (φ₁ : ℂ → V) z w = p₁ (fderiv ℝ (Φ : ℂ → _) z w) := by
    have h := (p₁.hasFDerivAt.comp z (Φ.contDiff.differentiable (by simp) z).hasFDerivAt).fderiv
    simpa [φ₁, TestFunction.postcompCLM_apply] using congr($h w)
  have hfderiv_φ₂ (z w : ℂ) : fderiv ℝ (φ₂ : ℂ → V) z w = p₂ (fderiv ℝ (Φ : ℂ → _) z w) := by
    have h := (p₂.hasFDerivAt.comp z (Φ.contDiff.differentiable (by simp) z).hasFDerivAt).fderiv
    simpa [φ₂, TestFunction.postcompCLM_apply] using congr($h w)
  have hLHS_pt (z : ℂ) :
      ⟪crFormalAdjoint (fun z => diagProdL2L V (J z)) (fun z => (diagProdL2L V).comp (DJ z))
        (fun z => conjProdL2L V (differentiatedCRCoefficient (S z) (DJ z))) Φ z,
        WithLp.toLp 2 (Dξ z 1, Dξ z I)⟫_ℝ =
      (-⟪fderiv ℝ (φ₁ : ℂ → V) z 1, Dξ z 1⟫_ℝ - ⟪fderiv ℝ (φ₁ : ℂ → V) z I, J z (Dξ z 1)⟫_ℝ -
        ⟪(φ₁ : ℂ → V) z, DJ z I (Dξ z 1)⟫_ℝ + ⟪(φ₁ : ℂ → V) z, S z (Dξ z 1)⟫_ℝ +
        ⟪(φ₁ : ℂ → V) z, DJ z 1 (Dξ z I)⟫_ℝ) +
      (-⟪fderiv ℝ (φ₂ : ℂ → V) z 1, Dξ z I⟫_ℝ - ⟪fderiv ℝ (φ₂ : ℂ → V) z I, J z (Dξ z I)⟫_ℝ +
        ⟪(φ₂ : ℂ → V) z, S z (Dξ z I)⟫_ℝ) := by
    rw [inner_crFormalAdjoint]
    simp only [hfderiv_φ₁, hfderiv_φ₂]
    simp only [diagProdL2L_apply, conjProdL2L_apply, ContinuousLinearMap.comp_apply,
      differentiatedCRCoefficient_apply, WithLp.prod_inner_apply, inner_add_right,
      p₁, p₂, φ₁, φ₂, eL2, TestFunction.postcompCLM_apply, Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_symm,
      WithLp.prodContinuousLinearEquiv_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd']
    ring
  have hRHS_pt (z : ℂ) :
      ⟪(Φ : ℂ → _) z, WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))⟫_ℝ =
      (⟪(φ₁ : ℂ → V) z, Dη z 1⟫_ℝ - ⟪(φ₁ : ℂ → V) z, DS z 1 (ξ z)⟫_ℝ) +
      (⟪(φ₂ : ℂ → V) z, Dη z I⟫_ℝ - ⟪(φ₂ : ℂ → V) z, DS z I (ξ z)⟫_ℝ) := by
    simp only [WithLp.prod_inner_apply, inner_sub_right, φ₁, φ₂, p₁, p₂, eL2,
      TestFunction.postcompCLM_apply, Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_symm,
      WithLp.prodContinuousLinearEquiv_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd']
  -- Step 3: Prove the `φ₁` and `φ₂` weak identities via `heq`, weak Leibniz on `S ξ`, and
  -- `integral_comm_differentiated`.
  have hSξ_ibp (w : ℂ) (φ : 𝓓(Ω, V)) :
      ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z w, S z (ξ z)⟫_ℝ =
        -((∫ z, ⟪(φ : ℂ → V) z, DS z w (ξ z)⟫_ℝ) + ∫ z, ⟪(φ : ℂ → V) z, S z (Dξ z w)⟫_ℝ) := by
    have h := (hSξ_weak.hasWeakLineDerivOn w).integral_inner_lineDeriv_eq_neg φ
    simp only [TestFunction.lineDeriv_eq_fderiv, add_apply, ContinuousLinearMap.precompL_apply,
      ContinuousLinearMap.precompR_apply, ContinuousLinearMap.id_apply, inner_add_right] at h
    exact h.trans (congrArg Neg.neg
      (integral_add (φ.integrable_inner (hloc_DSξ w)) (φ.integrable_inner (hloc_SDξ w))))
  have hcomp1 :
      -(∫ z, ⟪fderiv ℝ (φ₁ : ℂ → V) z 1, Dξ z 1⟫_ℝ) -
      (∫ z, ⟪fderiv ℝ (φ₁ : ℂ → V) z I, J z (Dξ z 1)⟫_ℝ) -
      (∫ z, ⟪(φ₁ : ℂ → V) z, DJ z I (Dξ z 1)⟫_ℝ) +
      (∫ z, ⟪(φ₁ : ℂ → V) z, S z (Dξ z 1)⟫_ℝ) +
      (∫ z, ⟪(φ₁ : ℂ → V) z, DJ z 1 (Dξ z I)⟫_ℝ) =
      (∫ z, ⟪(φ₁ : ℂ → V) z, Dη z 1⟫_ℝ) - ∫ z, ⟪(φ₁ : ℂ → V) z, DS z 1 (ξ z)⟫_ℝ := by
    have hsubst : ∫ z, ⟪fderiv ℝ (φ₁ : ℂ → V) z 1, Dξ z 1⟫_ℝ =
        (∫ z, ⟪fderiv ℝ (φ₁ : ℂ → V) z 1, η z⟫_ℝ) -
        (∫ z, ⟪fderiv ℝ (φ₁ : ℂ → V) z 1, J z (Dξ z I)⟫_ℝ) -
        ∫ z, ⟪fderiv ℝ (φ₁ : ℂ → V) z 1, S z (ξ z)⟫_ℝ := by
      have k1 := φ₁.integrable_inner_fderiv hloc_η 1
      have k2 := φ₁.integrable_inner_fderiv (hloc_JDξ I) 1
      have k3 := φ₁.integrable_inner_fderiv hloc_Sξ 1
      rw [← integral_sub k1 k2, ← integral_sub _ k3]
      · refine integral_congr_ae ?_
        filter_upwards [ae_imp_of_ae_restrict heq] with z hz
        by_cases hzΩ : z ∈ (Ω : Set ℂ)
        · have he : Dξ z 1 = η z - J z (Dξ z I) - S z (ξ z) := by rw [← hz hzΩ]; abel
          simp [he, inner_sub_right]
        · simp [fderiv_of_notMem_tsupport ℝ (fun h => hzΩ (φ₁.tsupport_subset h))]
      · exact k1.sub k2
    have hη1 : ∫ z, ⟪fderiv ℝ (φ₁ : ℂ → V) z 1, η z⟫_ℝ = -∫ z, ⟪(φ₁ : ℂ → V) z, Dη z 1⟫_ℝ := by
      simpa only [TestFunction.lineDeriv_eq_fderiv] using
        (hDη.hasWeakLineDerivOn 1).integral_inner_lineDeriv_eq_neg φ₁
    have hSξ1 := hSξ_ibp 1 φ₁
    have hcomm := integral_comm_differentiated hp1 hpq hDJ hJinf hDJp hDξ hDξq φ₁
    linarith
  have hcomp2 :
      -(∫ z, ⟪fderiv ℝ (φ₂ : ℂ → V) z 1, Dξ z I⟫_ℝ) -
      (∫ z, ⟪fderiv ℝ (φ₂ : ℂ → V) z I, J z (Dξ z I)⟫_ℝ) +
      (∫ z, ⟪(φ₂ : ℂ → V) z, S z (Dξ z I)⟫_ℝ) =
      (∫ z, ⟪(φ₂ : ℂ → V) z, Dη z I⟫_ℝ) - ∫ z, ⟪(φ₂ : ℂ → V) z, DS z I (ξ z)⟫_ℝ := by
    have hswap := integral_inner_fderiv_one_eq_fderiv_I hDξ φ₂
    have hsubst : (∫ z, ⟪fderiv ℝ (φ₂ : ℂ → V) z I, Dξ z 1⟫_ℝ) +
        (∫ z, ⟪fderiv ℝ (φ₂ : ℂ → V) z I, J z (Dξ z I)⟫_ℝ) =
        (∫ z, ⟪fderiv ℝ (φ₂ : ℂ → V) z I, η z⟫_ℝ) -
        ∫ z, ⟪fderiv ℝ (φ₂ : ℂ → V) z I, S z (ξ z)⟫_ℝ := by
      rw [← integral_add (φ₂.integrable_inner_fderiv (hloc_Dξ 1) I)
          (φ₂.integrable_inner_fderiv (hloc_JDξ I) I),
        ← integral_sub (φ₂.integrable_inner_fderiv hloc_η I)
          (φ₂.integrable_inner_fderiv hloc_Sξ I)]
      refine integral_congr_ae ?_
      filter_upwards [ae_imp_of_ae_restrict heq] with z hz
      by_cases hzΩ : z ∈ (Ω : Set ℂ)
      · rw [← inner_add_right, eq_sub_of_add_eq (hz hzΩ), inner_sub_right]
      · simp [fderiv_of_notMem_tsupport ℝ (fun h => hzΩ (φ₂.tsupport_subset h))]
    have hηI : ∫ z, ⟪fderiv ℝ (φ₂ : ℂ → V) z I, η z⟫_ℝ = -∫ z, ⟪(φ₂ : ℂ → V) z, Dη z I⟫_ℝ := by
      simpa only [TestFunction.lineDeriv_eq_fderiv] using
        (hDη.hasWeakLineDerivOn I).integral_inner_lineDeriv_eq_neg φ₂
    have hSξI := hSξ_ibp I φ₂
    linarith
  simp_rw [hLHS_pt, hRHS_pt]
  have i1 := φ₁.integrable_inner_fderiv (hloc_Dξ 1) 1
  have i2 := φ₁.integrable_inner_fderiv (hloc_JDξ 1) I
  have i3 := φ₁.integrable_inner (hloc_DJDξ I 1)
  have i4 := φ₁.integrable_inner (hloc_SDξ 1)
  have i5 := φ₁.integrable_inner (hloc_DJDξ 1 I)
  have j1 := φ₂.integrable_inner_fderiv (hloc_Dξ I) 1
  have j2 := φ₂.integrable_inner_fderiv (hloc_JDξ I) I
  have j3 := φ₂.integrable_inner (hloc_SDξ I)
  have r1 := φ₁.integrable_inner (hloc_Dη 1)
  have r2 := φ₁.integrable_inner (hloc_DSξ 1)
  have r3 := φ₂.integrable_inner (hloc_Dη I)
  have r4 := φ₂.integrable_inner (hloc_DSξ I)
  rw [integral_add _ _, integral_add _ i5, integral_add _ i4, integral_sub _ i3,
    integral_sub _ i2, integral_neg, integral_add _ j3, integral_sub _ j2, integral_neg,
    integral_add _ _, integral_sub r1 r2, integral_sub r3 r4, hcomp1, hcomp2]
  all_goals fun_prop

/-- Regularity of the differentiated right-hand side `(∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)` at
arbitrary order `k ≥ 0`. -/
private theorem memWkpLoc_differentiated_rightSide [FiniteDimensional ℝ V] {p q : ℝ≥0}
    (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p) {k : ℕ}
    {S : ℂ → V →L[ℝ] V} {DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    {ξ η : ℂ → V} {Dη : ℂ → ℂ →L[ℝ] V}
    (hS : MemWkpLoc p Ω (k + 1) S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω (k + 1) ξ) (hη : MemWkpLoc q Ω (k + 1) η)
    (hDη : HasWeakFDerivOn volume Ω η Dη) :
    MemWkpLoc q Ω k (fun z => WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) := by
  let eL2 : (V × V) ≃L[ℝ] WithLp 2 (V × V) := (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm
  cases k with
  | zero =>
    exact memWkpLoc_zero_iff.2
      ((memLpLoc_differentiatedCR_rightSide hp hq.le hqp hS hDS hξ hη hDη).clm_comp
        eL2.toContinuousLinearMap)
  | succ k =>
    have hDSk := hS.memWkpLoc_of_hasWeakFDerivOn hDS
    have hDηk := hη.memWkpLoc_of_hasWeakFDerivOn hDη
    have hcomp (w : ℂ) : MemWkpLoc q Ω (k + 1) (fun z => Dη z w - DS z w (ξ z)) :=
      (hDηk.clm_comp (ContinuousLinearMap.apply ℝ V w)).sub
        ((hDSk.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) w)).clm_apply_succ hp hq hqp
          hξ.of_succ)
    exact ((hcomp 1).prodMk (hcomp I)).clm_comp eL2.toContinuousLinearMap

/-- **Higher-order interior weak regularity (McDuff–Salamon Proposition B.4.9).** Let `2 < p < ∞`,
`1/p + 1/q₀ < 1`, `1/p + 1/q < 1`, `q ≤ p`, and `k ≥ 0`. Suppose `J ∈ W^{max 1 k, p}_loc(Ω)` has
weak derivative `DJ` and satisfies `J² = -1` almost everywhere, `S ∈ W^{k,p}_loc(Ω)`, and
`η ∈ W^{k,q}_loc(Ω)`. Then any weak solution `ξ ∈ L^{q₀}_loc(Ω)` of `∂_s ξ + J ∂_t ξ + S ξ = η`
belongs to `W^{k+1,q}_loc(Ω)`. -/
theorem memWkpLoc_succ_of_isWeakCRSolution {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ} {p q q₀ : ℝ≥0∞}
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hpq₀ : p⁻¹ + q₀⁻¹ < 1) (hpq : p⁻¹ + q⁻¹ < 1) (hqp : q ≤ p)
    {k : ℕ} {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hS : MemWkpLoc p Ω k S)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hsol : IsWeakCRSolution q₀ Ω J DJ S ξ η) (hη : MemWkpLoc q Ω k η) :
    MemWkpLoc q Ω (k + 1) ξ := by
  have hq1 : 1 < q := by
    have hq_inv : q⁻¹ < 1 := le_add_self.trans_lt hpq
    rwa [← inv_one, ENNReal.inv_lt_inv] at hq_inv
  have hq_top : q ≠ ⊤ := ne_top_of_le_ne_top hp_top hqp
  induction k generalizing V q₀ J DJ S ξ η with
  | zero =>
    have hc : IsSobolevCRCoefficients p Ω J DJ S :=
      ⟨hDJ, hJ.memLpLoc, hJ.memLpLoc_of_hasWeakFDerivOn hDJ, memWkpLoc_zero_iff.1 hS⟩
    exact hc.memWkpLoc_one_of_isWeakCRSolution hp hp_top hpq₀ hq1 hqp hJsq hsol
      (memWkpLoc_zero_iff.1 hη)
  | succ k ih =>
    rw [Nat.max_eq_right (Nat.succ_pos k)] at hJ
    have hJ' : MemWkpLoc p Ω (max 1 k) J := hJ.of_le (by omega)
    have hξk : MemWkpLoc q Ω (k + 1) ξ :=
      ih hpq₀ hJ' hDJ hS.of_succ hJsq hsol hη.of_succ
    have hξ1 : MemWkpLoc q Ω 1 ξ := hξk.of_le (Nat.succ_pos k)
    obtain ⟨Dξ, hDξ, -⟩ := hξ1.exists_weakFDeriv_of_isOpen
    obtain ⟨DS, hDS, -⟩ := (hS.of_le (Nat.succ_pos k)).exists_weakFDeriv_of_isOpen
    obtain ⟨Dη, hDη, -⟩ := (hη.of_le (Nat.succ_pos k)).exists_weakFDeriv_of_isOpen
    have hJ1 : MemWkpLoc p Ω 1 J := hJ.of_le (Nat.succ_pos k)
    have hS1 : MemWkpLoc p Ω 1 S := hS.of_le (Nat.succ_pos k)
    have hη1 : MemWkpLoc q Ω 1 η := hη.of_le (Nat.succ_pos k)
    have hc : IsSobolevCRCoefficients p Ω J DJ S :=
      ⟨hDJ, hJ1.memLpLoc, hJ1.memLpLoc_of_hasWeakFDerivOn hDJ, hS1.memLpLoc⟩
    have hsol_q : IsWeakCRSolution q Ω J DJ S ξ η :=
      isWeakCRSolution_iff.2 ⟨hξ1.memLpLoc, hsol.locallyIntegrableOn,
        (isWeakCRSolution_iff.1 hsol).2.2⟩
    have heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z :=
      (hc.isWeakCRSolution_iff_ae hpq.le hp_top hq_top hDξ hξ1.memLpLoc
        (hξ1.memLpLoc_of_hasWeakFDerivOn hDξ) hsol.locallyIntegrableOn).1 hsol_q
    lift p to ℝ≥0 using hp_top
    lift q to ℝ≥0 using hq_top
    have hpR : 2 < p := by exact_mod_cast hp
    have hqR : 1 < q := by exact_mod_cast hq1
    have hqpR : q ≤ p := by exact_mod_cast hqp
    have hsol_diff := isWeakCRSolution_differentiated hpR hqR hqpR hpq.le hJ1 hDJ hS1 hDS hξ1 hDξ
      hη1 hDη heq
    have hJTilde : MemWkpLoc p Ω (max 1 k) (fun z => diagProdL2L V (J z)) :=
      hJ'.clm_comp (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) (diagProdL2L V)
    have hDJTilde : HasWeakFDerivOn volume Ω (fun z => diagProdL2L V (J z))
        (fun z => (diagProdL2L V).comp (DJ z)) :=
      hDJ.clm_comp (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) (diagProdL2L V)
    have hSTilde : MemWkpLoc p Ω k
        (fun z => conjProdL2L V (differentiatedCRCoefficient (S z) (DJ z))) :=
      (hS.of_succ.differentiatedCRCoefficient hJ hDJ).clm_comp
        (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) (conjProdL2L V)
    have hJTilde_sq : ∀ᵐ z ∂volume.restrict Ω,
        diagProdL2L V (J z) * diagProdL2L V (J z) = -1 := by
      filter_upwards [hJsq] with z hz
      ext x
      have h1 : J z (J z x.ofLp.1) = -x.ofLp.1 := by simpa using congr($hz x.ofLp.1)
      have h2 : J z (J z x.ofLp.2) = -x.ofLp.2 := by simpa using congr($hz x.ofLp.2)
      simp only [mul_apply_eq_comp, diagProdL2L_apply, neg_apply, one_apply_eq_self]
      exact congrArg (WithLp.toLp 2) (Prod.ext h1 h2)
    have hEtaTilde := memWkpLoc_differentiated_rightSide hpR hqR hqpR hS hDS hξk hη hDη
    have hΞ : MemWkpLoc q Ω (k + 1) (fun z => WithLp.toLp 2 (Dξ z 1, Dξ z I)) :=
      ih (V := WithLp 2 (V × V)) hpq hJTilde hDJTilde hSTilde hJTilde_sq hsol_diff hEtaTilde
    have hDξ1 : MemWkpLoc q Ω (k + 1) (fun z => Dξ z 1) :=
      hΞ.clm_comp ((ContinuousLinearMap.fst ℝ V V).comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ V V).toContinuousLinearMap)
    have hDξI : MemWkpLoc q Ω (k + 1) (fun z => Dξ z I) :=
      hΞ.clm_comp ((ContinuousLinearMap.snd ℝ V V).comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ V V).toContinuousLinearMap)
    have hDξ_reg : MemWkpLoc q Ω (k + 1) Dξ := by
      rw [ContinuousLinearMap.fun_eq_smulRightL_reCLM_add_smulRightL_imCLM Dξ]
      exact (hDξ1.clm_comp (ContinuousLinearMap.smulRightL ℝ ℂ V Complex.reCLM)).add
        (hDξI.clm_comp (ContinuousLinearMap.smulRightL ℝ ℂ V Complex.imCLM))
    exact memWkpLoc_succ_iff_of_isOpen.2 ⟨hξ1.memLpLoc, Dξ, hDξ, hDξ_reg⟩

/-- **Higher-order interior regularity for `W^{1,q}_loc` solutions in an arbitrary
finite-dimensional real normed space.** Let `2 < p < ∞`, `1/p + 1/q < 1`, `q ≤ p`, and `k ≥ 0`.
If `J ∈ W^{max 1 k, p}_loc(Ω)` satisfies `J² = -1` almost everywhere, `S ∈ W^{k,p}_loc(Ω)`,
`η ∈ W^{k,q}_loc(Ω)`, and `ξ ∈ W^{1,q}_loc(Ω)` satisfies `∂_s ξ + J ∂_t ξ + S ξ = η` almost
everywhere on `Ω`, then `ξ ∈ W^{k+1,q}_loc(Ω)`. -/
theorem memWkpLoc_succ_of_ae_cauchyRiemann {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {Ω : Opens ℂ} {p q : ℝ≥0∞}
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ < 1) (hqp : q ≤ p) {k : ℕ}
    {J S : ℂ → V →L[ℝ] V} {ξ η : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V}
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hS : MemWkpLoc p Ω k S)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hη : MemWkpLoc q Ω k η)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z) :
    MemWkpLoc q Ω (k + 1) ξ := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  have hq1 : 1 < q := by
    have hq_inv : q⁻¹ < 1 := le_add_self.trans_lt hpq
    rwa [← inv_one, ENNReal.inv_lt_inv] at hq_inv
  have hq_top : q ≠ ⊤ := ne_top_of_le_ne_top hp_top hqp
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let conj : (V →L[ℝ] V) →L[ℝ]
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ]
        EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) :=
    (ContinuousLinearMap.compL ℝ _ V _ e.toContinuousLinearMap).comp
      ((ContinuousLinearMap.compL ℝ _ V V).flip e.symm.toContinuousLinearMap)
  have hconj (A : V →L[ℝ] V) (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) :
      conj A x = e (A (e.symm x)) := rfl
  let Je := fun z => conj (J z)
  let Se := fun z => conj (S z)
  let ξe := fun z => e (ξ z)
  let ηe := fun z => e (η z)
  let Dξe := fun z => e.toContinuousLinearMap.comp (Dξ z)
  have hJe : MemWkpLoc p Ω (max 1 k) Je :=
    hJ.clm_comp (G := EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) conj
  have hJe1 : MemWkpLoc p Ω 1 Je := hJe.of_le (le_max_left 1 k)
  obtain ⟨DJe, hDJe, -⟩ := hJe1.exists_weakFDeriv_of_isOpen
  have hSe : MemWkpLoc p Ω k Se :=
    hS.clm_comp (G := EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) conj
  have hηe : MemWkpLoc q Ω k ηe := hη.clm_comp e.toContinuousLinearMap
  have hξe : MemWkpLoc q Ω 1 ξe := hξ.clm_comp e.toContinuousLinearMap
  have hDξe : HasWeakFDerivOn volume Ω ξe Dξe := hDξ.clm_comp e.toContinuousLinearMap
  have hc : IsSobolevCRCoefficients p Ω Je DJe Se :=
    ⟨hDJe, hJe1.memLpLoc, hJe1.memLpLoc_of_hasWeakFDerivOn hDJe, hSe.memLpLoc⟩
  have heq_e : ∀ᵐ z ∂volume.restrict Ω, Dξe z 1 + Je z (Dξe z I) + Se z (ξe z) = ηe z := by
    filter_upwards [heq] with z hz
    simp only [Dξe, Je, Se, ξe, ηe, hconj, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
    rw [← map_add, ← map_add, hz]
  have hsol : IsWeakCRSolution q Ω Je DJe Se ξe ηe :=
    (hc.isWeakCRSolution_iff_ae hpq.le hp_top hq_top hDξe hξe.memLpLoc
      (hξe.memLpLoc_of_hasWeakFDerivOn hDξe)
      (hηe.memLpLoc.locallyIntegrableOn hq1.le Ω.isOpen.isLocallyClosed)).2 heq_e
  have hJesq : ∀ᵐ z ∂volume.restrict Ω, Je z * Je z = -1 := by
    filter_upwards [hJsq] with z hz
    ext x
    simp only [Je, hconj, mul_apply_eq_comp, ContinuousLinearEquiv.symm_apply_apply,
      neg_apply, one_apply_eq_self]
    have h := congr($hz (e.symm x))
    simp only [mul_apply_eq_comp, neg_apply, one_apply_eq_self] at h
    rw [h, map_neg, ContinuousLinearEquiv.apply_symm_apply]
  exact e.comp_memWkpLoc_iff.1
    (memWkpLoc_succ_of_isWeakCRSolution hp hp_top hpq hpq hqp hJe hDJe hSe hJesq hsol hηe)

/-- **Higher-order regularity for homogeneous linear weak solutions.** Let `2 < p < ∞`,
`1/p + 1/q < 1`, `q ≤ p`, and `k ≥ 0`. If `J ∈ W^{max 1 k, p}_loc(Ω)` satisfies `J² = -1` almost
everywhere and `S ∈ W^{k,p}_loc(Ω)`, then any solution of `TauCeti.IsWeakLinearCauchyRiemannOn`
for `(q, Ω, J, S)` belongs to `W^{k+1,q}_loc(Ω)`. -/
theorem IsWeakLinearCauchyRiemannOn.memWkpLoc_succ {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ} {p q : ℝ≥0∞}
    {J S : ℂ → V →L[ℝ] V} {ξ : ℂ → V} (hξ : IsWeakLinearCauchyRiemannOn q Ω J S ξ)
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ < 1) (hqp : q ≤ p) {k : ℕ}
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hS : MemWkpLoc p Ω k S)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) :
    MemWkpLoc q Ω (k + 1) ξ := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  obtain ⟨-, -, D, hD, -, hae⟩ := isWeakLinearCauchyRiemannOn_iff_of_isOpen.1 hξ
  exact memWkpLoc_succ_of_ae_cauchyRiemann hp hp_top hpq hqp hJ hS hJsq hξ.memWkpLoc_one hD
    memWkpLoc_zero_fun hae

/-- **Smooth-coefficient interior regularity (hypoellipticity).** If `J`, `S`, and `η` are smooth
on `Ω` with `J² = -1` on `Ω`, and `ξ ∈ L^{q₀}_loc(Ω)` (`1 < q₀`) is a weak solution of
`∂_s ξ + J ∂_t ξ + S ξ = η`, then `ξ` agrees almost everywhere on `Ω` with a smooth function on
`Ω`. -/
theorem exists_contDiffOn_infty_ae_eq_of_isWeakCRSolution {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ} {q₀ : ℝ≥0∞}
    (hq₀ : 1 < q₀) {J S : ℂ → V →L[ℝ] V} {ξ η : ℂ → V}
    (hJ : ContDiffOn ℝ ∞ J Ω) (hS : ContDiffOn ℝ ∞ S Ω) (hη : ContDiffOn ℝ ∞ η Ω)
    (hJsq : ∀ z ∈ (Ω : Set ℂ), J z * J z = -1)
    (hsol : IsWeakCRSolution q₀ Ω J (fderiv ℝ J) S ξ η) :
    ∃ g : ℂ → V, ContDiffOn ℝ ∞ g Ω ∧ ξ =ᵐ[volume.restrict Ω] g := by
  have hq₀_inv : q₀⁻¹ < 1 := by rw [← inv_one]; exact ENNReal.inv_lt_inv.2 hq₀
  have hgap : (0 : ℝ) < 1 - q₀⁻¹.toReal := by
    have hlt : q₀⁻¹.toReal < 1 := by
      simpa using (ENNReal.toReal_lt_toReal (ne_top_of_lt hq₀_inv) ENNReal.one_ne_top).2 hq₀_inv
    linarith
  set p : ℝ≥0 := ⟨max 3 ((1 - q₀⁻¹.toReal)⁻¹ + 1), by positivity⟩
  have hp2 : (2 : ℝ≥0∞) < p := by
    have : (2 : ℝ) < p := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    exact_mod_cast this
  have hp_inv : (p : ℝ≥0∞)⁻¹ + q₀⁻¹ < 1 := by
    have hp_pos : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have h1 : (1 - q₀⁻¹.toReal)⁻¹ < (p : ℝ) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have h2 : (p : ℝ)⁻¹ < 1 - q₀⁻¹.toReal := by
      rw [← inv_inv (1 - q₀⁻¹.toReal)]; exact inv_strictAnti₀ (by positivity) h1
    have hne : (p : ℝ≥0∞)⁻¹ + q₀⁻¹ ≠ ⊤ :=
      ENNReal.add_ne_top.2
        ⟨ENNReal.inv_ne_top.2 (by exact_mod_cast hp_pos.ne'), ne_top_of_lt hq₀_inv⟩
    exact (ENNReal.toReal_lt_toReal hne ENNReal.one_ne_top).1 (by
      rw [ENNReal.toReal_add (ENNReal.inv_ne_top.2 (by exact_mod_cast hp_pos.ne'))
        (ne_top_of_lt hq₀_inv), ENNReal.toReal_inv, ENNReal.coe_toReal, ENNReal.toReal_one]
      linarith)
  have hpp : (p : ℝ≥0∞)⁻¹ + (p : ℝ≥0∞)⁻¹ < 1 := by
    have hlt : (p : ℝ≥0∞)⁻¹ < (2 : ℝ≥0∞)⁻¹ := ENNReal.inv_lt_inv.2 hp2
    exact (ENNReal.add_lt_add hlt hlt).trans_eq ENNReal.inv_two_add_inv_two
  have hJ1 : ContDiffOn ℝ 1 J Ω := hJ.of_le (by simp)
  have hDJ : HasWeakFDerivOn volume Ω J (fderiv ℝ J) :=
    hasWeakFDerivOn_of_differentiableOn
      ((hJ1.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl).locallyIntegrableOn
        Ω.isOpen.measurableSet)
      fun z hz => (hJ1.differentiableOn one_ne_zero z hz).differentiableAt (Ω.isOpen.mem_nhds hz)
  have hJsq_ae : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1 :=
    (ae_restrict_iff' Ω.isOpen.measurableSet).2 (.of_forall hJsq)
  have hall (k : ℕ) : MemWkpLoc p Ω (k + 1) ξ :=
    memWkpLoc_succ_of_isWeakCRSolution hp2 ENNReal.coe_ne_top hp_inv hpp le_rfl
      ((hJ.of_le (by simp)).memWkpLoc subset_rfl) hDJ
      ((hS.of_le (by simp)).memWkpLoc subset_rfl) hJsq_ae hsol
      ((hη.of_le (by simp)).memWkpLoc subset_rfl)
  obtain ⟨g, hg0, hξg⟩ := (hall 0).exists_contDiffOn_ae_eq hp2
  refine ⟨g, contDiffOn_infty.2 fun k => ?_, hξg⟩
  obtain ⟨gk, hgk, hξgk⟩ := (hall k).exists_contDiffOn_ae_eq hp2
  have heq : EqOn gk g Ω :=
    Measure.eqOn_open_of_ae_eq (hξgk.symm.trans hξg) Ω.isOpen hgk.continuousOn hg0.continuousOn
  exact hgk.congr fun z hz => (heq hz).symm

end HigherOrder

end TauCeti
