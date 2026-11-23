/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Beurling.Lp
public import TauCeti.Analysis.Complex.Wirtinger.Lp
public import TauCeti.Analysis.Sobolev.GraphStep.Coordinates
public import TauCeti.Analysis.Sobolev.WeakDeriv.Local
public import TauCeti.MeasureTheory.Function.Lp.ExtendByZero
public import TauCeti.MeasureTheory.Function.Lp.CastMeasure
public import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
public import TauCeti.Analysis.Complex.Wirtinger.Beurling.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Cauchy and Beurling operators in finite-dimensional complex norms

For every finite-dimensional complex normed target and `1 < p < ∞`,
`TauCeti.beurlingL` is a bounded complex-linear operator on whole-plane `Lᵖ`.
`TauCeti.CauchyTransform.graphL` maps data supported in a fixed closed disc to the native
real weak-derivative graph on any bounded open output disc, with its original target norm.
Its value is the Cauchy integral with kernel `π⁻¹ (w - z)⁻¹` and its weak derivative is
`v ↦ v • B f + conj v • f`.

## Main results

* `graphL_prev`, `graphL_weakFDeriv`: the value and derivative projections.
* `norm_global_jet_le`, `norm_graphL_le`: one global derivative constant and the graph bound
  `‖T f‖ ≤ (2 (r + R) + C) ‖f‖`, where `C = ‖jetL (beurlingL hp hp_top)‖`.
* `functional_beurling`, `beurling_naturality`, `graphL_prev_naturality`,
  `graphL_weakFDeriv_naturality`: complex coefficient and constant-frame compatibility.
* `graphL_prev_smul`, `graphL_weakFDeriv_smul`: complex homogeneity of both projections.
* `global_jet_exponent_ae`, `beurling_exponent_ae`: agreement across finite exponents.
* `graphL_center_overlap`: agreement on overlapping discs with different centres.

The input and output radii may be zero, and the coefficient space may have dimension zero.
The global bound is for the derivative; the Cauchy integral itself need not be globally `Lᵖ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.2.
-/

public noncomputable section

open MeasureTheory Complex ComplexConjugate Metric Set TopologicalSpace Function
open scoped ENNReal NNReal

namespace TauCeti.CauchyTransform

open Wirtinger

section Scalar

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The output disc as a open set. -/
def disc (c : ℂ) (R : ℝ≥0) : Opens ℂ := ⟨ball c R, isOpen_ball⟩

/-- The output disc has its stated points. -/
@[simp]
theorem coe_disc (c : ℂ) (R : ℝ≥0) : (disc c R : Set ℂ) = ball c R := by
  rw [disc]
  rfl

/-- Membership in the open output disc is membership in its metric ball. -/
@[simp]
theorem mem_disc (c : ℂ) (R : ℝ≥0) (z : ℂ) : z ∈ disc c R ↔ z ∈ ball c R :=
  Iff.rfl

/-- The first-order vector weak-derivative graph. -/
abbrev Graph (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (Ω : Opens ℂ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :=
  WeakDerivStep (volume :
    Measure ℂ) Ω p (ContinuousLinearMap.id ℝ (Lp F p ((volume : Measure ℂ).restrict (Ω : Set ℂ))))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Extension from the input disc to the whole-plane `Lp` carrier. -/
def zeroExtend (c : ℂ) (r : ℝ≥0) :
    Lp F p ((volume :
    Measure ℂ).restrict (closedBall c (r : ℝ))) →ₗᵢ[ℂ] Lp F p (volume : Measure ℂ) :=
  ((castLpₗᵢ (𝕜 := ℂ) (E := F) (p := p)
    (Measure.restrict_univ : (volume : Measure ℂ).restrict univ = volume)).toLinearIsometry).comp
    (extendByZeroLpₗᵢ (F := F) (p := p) ℂ (volume : Measure ℂ)
      measurableSet_closedBall.nullMeasurableSet
      (subset_univ (closedBall c (r : ℝ))))

/-- The zero-extended representative. -/
def zeroExtendFn (c : ℂ) (r : ℝ≥0)
    (u : Lp F p ((volume : Measure ℂ).restrict (closedBall c (r : ℝ)))) : ℂ → F :=
  (closedBall c (r : ℝ)).indicator u

omit [Fact (1 ≤ p)] [NormedSpace ℂ F] in
/-- The zero-extended representative is the indicator of the input disc. -/
theorem zeroExtendFn_def (c : ℂ) (r : ℝ≥0)
    (u : Lp F p (volume.restrict (closedBall c (r : ℝ)))) :
    zeroExtendFn c r u = (closedBall c (r : ℝ)).indicator u := by
  rfl

/-- Zero extension has the indicator representative. -/
theorem coe_zeroExtend (c : ℂ) (r : ℝ≥0)
    (u : Lp F p ((volume : Measure ℂ).restrict (closedBall c (r : ℝ)))) :
    zeroExtend c r u =ᵐ[(volume : Measure ℂ)] zeroExtendFn c r u := by
  have h := coeFn_extendByZeroLpₗᵢ (F := F) (p := p) ℂ
    measurableSet_closedBall.nullMeasurableSet
    (subset_univ (closedBall c (r : ℝ))) u
  have h' := h.filter_mono (show ae (volume : Measure ℂ) ≤
    ae ((volume : Measure ℂ).restrict univ) by rw [Measure.restrict_univ])
  filter_upwards [h'] with x hx
  -- Expose the native cast from restriction to `univ` before its representative law.
  change ((castLpₗᵢ (𝕜 := ℂ) (E := F) (p := p) Measure.restrict_univ)
    ((extendByZeroLpₗᵢ ℂ volume measurableSet_closedBall.nullMeasurableSet
      (subset_univ (closedBall c (r : ℝ)))) u) : ℂ → F) x = _
  rw [coeFn_castLpₗᵢ]
  exact hx

omit [Fact (1 ≤ p)] [NormedSpace ℂ F] in
/-- The zero-extended representative is in whole-plane `Lp`. -/
theorem memLp_zeroExtendFn (c : ℂ) (r : ℝ≥0)
    (u : Lp F p ((volume : Measure ℂ).restrict (closedBall c (r : ℝ)))) :
    MemLp (zeroExtendFn c r u) p (volume : Measure ℂ) :=
  (memLp_indicator_iff_restrict measurableSet_closedBall.nullMeasurableSet).2 (Lp.memLp u)

/-- The a.e. class of the explicit indicator is the extension operator. -/
theorem toLp_zeroExtendFn (c : ℂ) (r : ℝ≥0)
    (u : Lp F p ((volume : Measure ℂ).restrict (closedBall c (r : ℝ)))) :
    (memLp_zeroExtendFn c r u).toLp _ = zeroExtend c r u :=
  Lp.ext ((memLp_zeroExtendFn c r u).coeFn_toLp.trans (coe_zeroExtend c r u).symm)

omit [Fact (1 ≤ p)] [NormedSpace ℂ F] in
/-- A supported datum is recovered a.e. from the restricted class by zero extension. -/
theorem zeroExtendFn_toLp_ae {f : ℂ → F} (hf : MemLp f p (volume : Measure ℂ))
    {c : ℂ} {r : ℝ≥0} (hs : support f ⊆ closedBall c (r : ℝ)) :
    zeroExtendFn c r ((hf.restrict (closedBall c (r : ℝ))).toLp f) =ᵐ[volume] f := by
  have h := (ae_restrict_iff' measurableSet_closedBall).mp
    (hf.restrict (closedBall c (r : ℝ))).coeFn_toLp
  filter_upwards [h] with w hw
  by_cases hin : w ∈ closedBall c (r : ℝ)
  · simp only [zeroExtendFn_def, indicator_of_mem hin, hw hin]
  · rw [zeroExtendFn_def, indicator_of_notMem hin]
    exact (notMem_support.mp (fun h ↦ hin (hs h))).symm

/-- The whole-plane class is recovered from a supported datum. -/
theorem zeroExtend_toLp {f : ℂ → F} (hf : MemLp f p (volume : Measure ℂ))
    {c : ℂ} {r : ℝ≥0} (hs : support f ⊆ closedBall c (r : ℝ)) :
    zeroExtend c r ((hf.restrict (closedBall c (r : ℝ))).toLp f) = hf.toLp f := by
  apply Lp.ext
  exact (coe_zeroExtend _ _ _).trans ((zeroExtendFn_toLp_ae hf hs).trans hf.coeFn_toLp.symm)

/-- The value operator on the open output disc. -/
def valueL (c : ℂ) (r R : ℝ≥0) :
    Lp F p (volume.restrict (closedBall c (r : ℝ))) →L[ℂ]
      Lp F p (volume.restrict (disc c R : Set ℂ)) :=
  ((castLpₗᵢ (𝕜 := ℂ) (E := F) (p := p)
    (volume.restrict_closedBall_eq_restrict_ball c (R :
      ℝ))).toLinearIsometry.toContinuousLinearMap).comp (cauchyTransformLp c r R p)

/-- The value bound in the original norm retains its explicit disc radii. -/
theorem norm_valueL_apply (c : ℂ) (r R : ℝ≥0)
    (u : Lp F p (volume.restrict (closedBall c (r : ℝ)))) :
    ‖valueL c r R u‖ ≤ (2 * ((r : ℝ) + R)) * ‖u‖ := by
  -- The output restriction is an isometric cast between equal restricted measures.
  change ‖castLpₗᵢ (𝕜 := ℂ) (E := F) (p := p)
    (volume.restrict_closedBall_eq_restrict_ball c (R : ℝ))
      (cauchyTransformLp c r R p u)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact ((cauchyTransformLp c r R p).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (norm_cauchyTransformLp_le c r R p) (norm_nonneg u))

/-- The value operator evaluates the Cauchy transform of the zero extension. -/
theorem coe_valueL (c : ℂ) (r R : ℝ≥0)
    (u : Lp F p ((volume : Measure ℂ).restrict (closedBall c (r : ℝ)))) :
    valueL c r R u =ᵐ[(volume :
    Measure ℂ).restrict (disc c R : Set ℂ)] cauchyTransform (zeroExtendFn c r u) := by
  -- Cast along the null-circle measure equality, preserving representatives pointwise.
  change (fun w ↦ castLpₗᵢ (𝕜 := ℂ) (E := F) (p := p)
    (volume.restrict_closedBall_eq_restrict_ball c (R : ℝ))
      (cauchyTransformLp c r R p u) w) =ᵐ[_] _
  simp only [coeFn_castLpₗᵢ]
  have ht := (coeFn_cauchyTransformLp c r R p u).filter_mono
    (show ae (volume.restrict (disc c R : Set ℂ)) ≤
      ae (volume.restrict (closedBall c (R : ℝ))) by
        rw [coe_disc, volume.restrict_closedBall_eq_restrict_ball])
  refine ht.trans (.of_forall fun w ↦ ?_)
  rw [cauchyTransform_apply, zeroExtendFn_def]
  apply congrArg fun t : F ↦ (Real.pi : ℂ)⁻¹ • t
  rw [← integral_indicator measurableSet_closedBall]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ closedBall c (r : ℝ)
  · simp only [indicator_of_mem hz]
  · simp only [indicator_of_notMem hz, smul_zero]

section Naturality

variable [CompleteSpace F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace F] [CompleteSpace G] in
/-- Taking a complex-linear coefficient map commutes with zero extension a.e. -/
theorem zeroExtendFn_comp_ae (L : F →L[ℂ] G) (c : ℂ) (r : ℝ≥0)
    (u : Lp F p (volume.restrict (closedBall c (r : ℝ)))) :
    zeroExtendFn c r (L.compLpL p (volume.restrict (closedBall c (r : ℝ))) u) =ᵐ[volume]
      fun z ↦ L (zeroExtendFn c r u z) := by
  have h := (ae_restrict_iff' measurableSet_closedBall).mp (L.coeFn_compLpL u)
  filter_upwards [h] with z hz
  by_cases hin : z ∈ closedBall c (r : ℝ)
  · simp only [zeroExtendFn_def, indicator_of_mem hin, hz hin]
  · simp only [zeroExtendFn_def, indicator_of_notMem hin, map_zero]

omit [CompleteSpace F] [CompleteSpace G] in
/-- The zero-extension operator commutes with coefficient maps. -/
theorem zeroExtend_comp (L : F →L[ℂ] G) (c : ℂ) (r : ℝ≥0)
    (u : Lp F p (volume.restrict (closedBall c (r : ℝ)))) :
    zeroExtend c r (L.compLpL p (volume.restrict (closedBall c (r : ℝ))) u) =
      L.compLpL p volume (zeroExtend c r u) := by
  apply Lp.ext
  filter_upwards [coe_zeroExtend c r (L.compLpL p _ u), coe_zeroExtend c r u,
    L.coeFn_compLpL (zeroExtend c r u), zeroExtendFn_comp_ae L c r u] with w h₁ h₂ h₃ h₄
  rw [h₁, h₃, h₂, h₄]

/-- The fixed-disc value operator is natural for coefficient maps in the original norms. -/
theorem valueL_comp (L : F →L[ℂ] G) (c : ℂ) (r R : ℝ≥0)
    (u : Lp F p (volume.restrict (closedBall c (r : ℝ)))) :
    valueL c r R (L.compLpL p (volume.restrict (closedBall c (r : ℝ))) u) =
      L.compLpL p (volume.restrict (disc c R : Set ℂ)) (valueL c r R u) := by
  apply Lp.ext
  have hT := (cauchyTransform_comp_ae (R := R) L
    ((memLp_zeroExtendFn c r u).restrict _) support_indicator_subset).filter_mono
      (ae_mono (Measure.restrict_mono_set volume ball_subset_closedBall))
  have heq := cauchyTransform_congr_ae (zeroExtendFn_comp_ae L c r u)
  filter_upwards [coe_valueL c r R (L.compLpL p _ u), coe_valueL c r R u,
    L.coeFn_compLpL (valueL c r R u), hT] with w hv hu hL hT
  rw [hv, heq, hT, hL, hu]

end Naturality

/-- The scalar value and global jet form a weak derivative on each output disc. -/
private theorem scalar_weak (hp : 1 < p) (hp_top : p ≠ ∞) (c : ℂ) (r R : ℝ≥0)
    (u : Lp ℂ p ((volume : Measure ℂ).restrict (closedBall c (r : ℝ)))) :
    HasWeakFDerivOn volume (disc c R) (valueL c r R u)
      ((LpToLpRestrictCLM ℂ (ℂ →L[ℝ] ℂ) ℂ volume p (disc c R))
        ((jetL (beurlingLp (F := ℂ) p hp hp_top)) (zeroExtend c r u))) := by
  have h := hasWeakFDerivOn_cauchyTransform_of_memLp hp hp_top
    (memLp_zeroExtendFn c r u)
    (support_indicator_subset : support (zeroExtendFn c r u) ⊆ closedBall c (r : ℝ))
    (disc c R)
  rw [toLp_zeroExtendFn] at h
  refine (h.congr_ae (coe_valueL c r R u).symm).congr_ae_deriv ?_
  have hj := (coe_jetL (beurlingLp (F := ℂ) p hp hp_top) (zeroExtend c r u)).filter_mono
    (ae_mono (Measure.restrict_le_self (s := (disc c R : Set ℂ))))
  have hz := (coe_zeroExtend c r u).filter_mono
    (ae_mono (Measure.restrict_le_self (s := (disc c R : Set ℂ))))
  filter_upwards [(LpToLpRestrictCLM_coeFn ℂ ((disc c R) : Set ℂ) ((jetL (beurlingLp (F := ℂ) p hp
    hp_top)) (zeroExtend c r u))), hj, hz] with w hr hj hz
  rw [hr, hj, hz]

/-- The scalar Cauchy operator into the original weak-derivative graph. -/
private def scalarL (hp : 1 < p) (hp_top : p ≠ ∞) (c : ℂ) (r R : ℝ≥0) :
    Lp ℂ p ((volume : Measure ℂ).restrict (closedBall c (r : ℝ))) →L[ℝ]
      Graph ℂ (disc c R) p :=
  ContinuousLinearMap.codRestrict
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
      (((valueL c r R).restrictScalars ℝ).prod
        (((LpToLpRestrictCLM ℂ (ℂ →L[ℝ] ℂ) ℂ volume p (disc c R)).restrictScalars ℝ).comp
          (((jetL (beurlingLp (F := ℂ) p hp hp_top))).comp ((zeroExtend c
            r).toContinuousLinearMap.restrictScalars ℝ)))))
    _ fun u ↦ (mem_weakDerivStepSubmodule_iff_hasWeakFDerivOn _ _).mpr
      (scalar_weak hp hp_top c r R u)

/-- The scalar graph has the value operator as its value projection. -/
@[simp]
private theorem scalarL_prev (hp : 1 < p) (hp_top : p ≠ ∞) (c : ℂ) (r R : ℝ≥0)
    (u : Lp ℂ p ((volume : Measure ℂ).restrict (closedBall c (r : ℝ)))) :
    WeakDerivStep.prev _ (scalarL hp hp_top c r R u) = valueL c r R u := by
  simp [scalarL, WeakDerivStep.prev_coe]

/-- The scalar graph has the restriction of its single global weak jet. -/
@[simp]
private theorem scalarL_weakFDeriv (hp : 1 < p) (hp_top : p ≠ ∞) (c : ℂ) (r R : ℝ≥0)
    (u : Lp ℂ p ((volume : Measure ℂ).restrict (closedBall c (r : ℝ)))) :
    WeakDerivStep.weakFDeriv _ (scalarL hp hp_top c r R u) =
      (LpToLpRestrictCLM ℂ (ℂ →L[ℝ] ℂ) ℂ volume p (disc c R))
        ((jetL (beurlingLp (F := ℂ) p hp hp_top)) (zeroExtend c r u)) := by
  simp [scalarL, WeakDerivStep.weakFDeriv_coe]

end Scalar

section Jet

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Compose a scalar real derivative with multiplication by a coefficient vector. -/
private def lineJetL (v : F) : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ →L[ℝ] F :=
  ContinuousLinearMap.compL ℝ ℂ ℂ F
    ((ContinuousLinearMap.toSpanSingleton ℂ v).restrictScalars ℝ)

/-- The line jet is complex multiplication in the original fibre. -/
@[simp]
private theorem lineJetL_apply (v : F) (D : ℂ →L[ℝ] ℂ) (e : ℂ) :
    lineJetL v D e = D e • v := by
  simp [lineJetL]

variable [FiniteDimensional ℂ F] {ι : Type*} [Fintype ι]

/-- Finite reconstruction of the scalar global weak jets. -/
private def jetWithBasis (b : Module.Basis ι ℂ F) (hp : 1 < p) (hp_top : p ≠ ∞) :
    Lp F p (volume : Measure ℂ) →L[ℝ] Lp (ℂ →L[ℝ] F) p (volume : Measure ℂ) :=
  ∑ i, ((lineJetL (b i)).compLpL p volume).comp
    ((jetL (beurlingLp (F := ℂ) p hp hp_top)).comp
      (((b.coord i).toContinuousLinearMap.compLpL p volume).restrictScalars ℝ))

/-- The global reconstructed derivative evaluates as the finite sum of scalar jets. -/
private theorem coe_jetWithBasis (b : Module.Basis ι ℂ F) (hp : 1 < p) (hp_top : p ≠ ∞)
    (u : Lp F p (volume : Measure ℂ)) :
    jetWithBasis b hp hp_top u =ᵐ[volume] fun w ↦
      ∑ i, lineJetL (b i) (jetL (beurlingLp (F := ℂ) p hp hp_top)
        ((b.coord i).toContinuousLinearMap.compLpL p volume u) w) := by
  classical
  simp only [jetWithBasis, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars']
  have hi (i : ι) := (lineJetL (b i)).coeFn_compLpL
    (jetL (beurlingLp (F := ℂ) p hp hp_top)
      ((b.coord i).toContinuousLinearMap.compLpL p volume u))
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦
    (lineJetL (b i)).compLpL p volume
      (jetL (beurlingLp (F := ℂ) p hp hp_top)
      ((b.coord i).toContinuousLinearMap.compLpL p volume u))),
    ae_all_iff.mpr hi] with w hsum hcoords
  simp only [hsum, hcoords]

/-- The reconstructed global derivative is exactly the Wirtinger jet of the same Beurling map. -/
private theorem jetWithBasis_eq (b : Module.Basis ι ℂ F) (hp : 1 < p) (hp_top : p ≠ ∞) :
    jetWithBasis b hp hp_top = jetL (beurlingWithBasis b hp hp_top) := by
  classical
  ext1 u
  apply Lp.ext
  have hj (i : ι) := coe_jetL (beurlingLp (F := ℂ) p hp hp_top)
    (((b.coord i).toContinuousLinearMap).compLpL p volume u)
  have hc (i : ι) := ((b.coord i).toContinuousLinearMap).coeFn_compLpL u
  filter_upwards [coe_jetWithBasis b hp hp_top u,
    coe_jetL (beurlingWithBasis b hp hp_top) u,
    coe_beurlingWithBasis b hp hp_top u, ae_all_iff.mpr hj, ae_all_iff.mpr hc]
      with w hsum hjet hB hscalar hcoord
  rw [hsum, hjet]
  ext v
  simp only [sum_apply, lineJetL_apply,  hscalar, wirtingerPartsCLM_apply,
    smul_eq_mul, hcoord, add_smul, mul_smul, Finset.sum_add_distrib,
    ← Finset.smul_sum]
  rw [← hB]
  congr 1
  simpa only [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    using congrArg (fun x : F ↦ conj v • x) (b.sum_repr (u w))

/-- The single global jet commutes with complex-linear coefficient maps. -/
theorem jet_naturality {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [FiniteDimensional ℂ G] (hp : 1 < p) (hp_top : p ≠ ∞) (L : F →L[ℂ] G)
    (u : Lp F p (volume : Measure ℂ)) :
    (fun w ↦ (L.restrictScalars ℝ).comp (jetL (beurlingL hp hp_top) u w)) =ᵐ[volume]
      jetL (beurlingL hp hp_top) (L.compLpL p volume u) := by
  have hB := L.coeFn_compLpL (beurlingL hp hp_top u)
  rw [beurling_naturality hp hp_top L u] at hB
  filter_upwards [coe_jetL (beurlingL hp hp_top) u,
    coe_jetL (beurlingL hp hp_top) (L.compLpL p volume u),
    L.coeFn_compLpL u, hB] with w hF hG hL hB
  rw [hF, hG]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    wirtingerPartsCLM_apply, map_add, map_smul, hL, hB]

end Jet

section Native

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

variable {ι : Type*} [Fintype ι]

/-- Reconstruct the scalar complex Cauchy graphs in the original finite-dimensional norm. -/
private def graphWithBasis (b : Module.Basis ι ℂ F) (hp : 1 < p) (hp_top : p ≠ ∞)
    (c : ℂ) (r R : ℝ≥0) :
    Lp F p (volume.restrict (closedBall c (r : ℝ))) →L[ℝ] Graph F (disc c R) p :=
  ∑ i, (WeakDerivStep.smulRightComplexL (disc c R) (b i)).comp
    ((scalarL hp hp_top c r R).comp
      (((b.coord i).toContinuousLinearMap.compLpL p
        (volume.restrict (closedBall c (r : ℝ)))).restrictScalars ℝ))

/-- reconstruction has exactly the original-norm Cauchy value operator. -/
private theorem graphWithBasis_prev (b : Module.Basis ι ℂ F) (hp : 1 < p) (hp_top : p ≠ ∞)
    (c : ℂ) (r R : ℝ≥0)
    (u : Lp F p (volume.restrict (closedBall c (r : ℝ)))) :
    WeakDerivStep.prev _ (graphWithBasis b hp hp_top c r R u) = valueL c r R u := by
  classical
  rw [graphWithBasis]
  simp only [sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars']
  rw [← WeakDerivStep.prevL_apply, map_sum]
  simp only [WeakDerivStep.prevL_apply, WeakDerivStep.prev_smulRightComplexL, scalarL_prev]
  simp_rw [← valueL_comp (ContinuousLinearMap.toSpanSingleton ℂ _) c r R]
  rw [← map_sum]
  congr 1
  exact (eq_sum_basis_compLpL b u).symm

/-- The reconstructed graph uses the restriction of one global original-norm weak jet. -/
private theorem graphWithBasis_weakFDeriv (b : Module.Basis ι ℂ F) (hp : 1 < p) (hp_top : p ≠ ∞)
    (c : ℂ) (r R : ℝ≥0)
    (u : Lp F p (volume.restrict (closedBall c (r : ℝ)))) :
    WeakDerivStep.weakFDeriv _ (graphWithBasis b hp hp_top c r R u) =
      (LpToLpRestrictCLM ℂ (ℂ →L[ℝ] F) ℂ volume p (disc c R))
        (jetL (beurlingWithBasis b hp hp_top) (zeroExtend c r u)) := by
  classical
  rw [← jetWithBasis_eq b hp hp_top, graphWithBasis]
  simp only [sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars']
  rw [← WeakDerivStep.weakFDerivL_apply, map_sum]
  simp only [WeakDerivStep.weakFDerivL_apply]
  let a (i : ι) := (b.coord i).toContinuousLinearMap.compLpL p
    (volume.restrict (closedBall c (r : ℝ))) u
  have hl (i : ι) := WeakDerivStep.weakFDeriv_smulRightComplexL_ae (disc c R) (b i)
    (scalarL hp hp_top c r R (a i))
  have hr (i : ι) := (LpToLpRestrictCLM_coeFn ℂ ((disc c R) : Set ℂ) (jetL (beurlingLp (F := ℂ) p
    hp hp_top) (zeroExtend c r (a i))))
  have hg := (coe_jetWithBasis b hp hp_top (zeroExtend c r u)).filter_mono
    (ae_mono (Measure.restrict_le_self (s := (disc c R : Set ℂ))))
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦
    WeakDerivStep.weakFDeriv _ (WeakDerivStep.smulRightComplexL (disc c R) (b i)
      (scalarL hp hp_top c r R (a i)))), ae_all_iff.mpr hl, ae_all_iff.mpr hr,
    (LpToLpRestrictCLM_coeFn ℂ ((disc c R) : Set ℂ) (jetWithBasis b hp hp_top (zeroExtend c r
      u))), hg]
      with w hsum hline hrestrict hout hglobal
  rw [hsum, hout, hglobal]
  apply Finset.sum_congr rfl
  intro i _
  rw [hline i, scalarL_weakFDeriv, hrestrict i]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.coe_restrictScalars', lineJetL_apply]
  dsimp only [a]
  rw [zeroExtend_comp]

/-- The intrinsic Cauchy operator into the original finite-dimensional graph. -/
def graphL (hp : 1 < p) (hp_top : p ≠ ∞) (c : ℂ) (r R : ℝ≥0) :
    Lp F p (volume.restrict (closedBall c (r : ℝ))) →L[ℝ] Graph F (disc c R) p :=
  graphWithBasis (Module.finBasis ℂ F) hp hp_top c r R

/-- The intrinsic graph has the original-norm Cauchy value class. -/
@[simp]
theorem graphL_prev (hp : 1 < p) (hp_top : p ≠ ∞) (c : ℂ) (r R : ℝ≥0)
    (u : Lp F p (volume.restrict (closedBall c (r : ℝ)))) :
    WeakDerivStep.prev _ (graphL hp hp_top c r R u) = valueL c r R u := by
  rw [graphL, graphWithBasis_prev]

/-- The intrinsic graph uses the restriction of its single global weak jet. -/
@[simp]
theorem graphL_weakFDeriv (hp : 1 < p) (hp_top : p ≠ ∞) (c : ℂ) (r R : ℝ≥0)
    (u : Lp F p (volume.restrict (closedBall c (r : ℝ)))) :
    WeakDerivStep.weakFDeriv _ (graphL hp hp_top c r R u) =
      (LpToLpRestrictCLM ℂ (ℂ →L[ℝ] F) ℂ volume p (disc c R))
        (jetL (beurlingL hp hp_top) (zeroExtend c r u)) := by
  rw [graphL, graphWithBasis_weakFDeriv,
    ← beurling_eq_withBasis (Module.finBasis ℂ F) hp hp_top]

/-- One coefficient constant controls the global weak derivative. -/
theorem norm_global_jet_le (hp : 1 < p) (hp_top : p ≠ ∞) (c : ℂ) (r : ℝ≥0)
    (u : Lp F p (volume.restrict (closedBall c (r : ℝ)))) :
    ‖jetL (beurlingL hp hp_top) (zeroExtend c r u)‖ ≤
      ‖jetL (beurlingL (F := F) hp hp_top)‖ * ‖u‖ := by
  simpa only [LinearIsometry.norm_map] using
    (jetL (beurlingL (F := F) hp hp_top)).le_opNorm (zeroExtend c r u)

/-- The full graph norm has explicit radii and one constant independent of the datum. -/
theorem norm_graphL_le (hp : 1 < p) (hp_top : p ≠ ∞) (c : ℂ) (r R : ℝ≥0)
    (u : Lp F p (volume.restrict (closedBall c (r : ℝ)))) :
    ‖graphL hp hp_top c r R u‖ ≤
      (2 * ((r : ℝ) + R) + ‖jetL (beurlingL (F := F) hp hp_top)‖) * ‖u‖ := by
  calc _ ≤ ‖WeakDerivStep.prev _ (graphL hp hp_top c r R u)‖ +
      ‖WeakDerivStep.weakFDeriv _ (graphL hp hp_top c r R u)‖ :=
      WeakDerivStep.norm_le_norm_prev_add_norm_weakFDeriv _ _
    _ ≤ (2 * ((r : ℝ) + R)) * ‖u‖ +
        ‖jetL (beurlingL (F := F) hp hp_top)‖ * ‖u‖ := by
      rw [graphL_prev, graphL_weakFDeriv]
      exact add_le_add (norm_valueL_apply c r R u)
        ((norm_Lp_toLp_restrict_le (disc c R : Set ℂ)
          (jetL (beurlingL hp hp_top) (zeroExtend c r u))).trans (norm_global_jet_le hp hp_top c r
            u))
    _ = _ := (add_mul _ _ _).symm

/-- The value projection preserves the full complex scalar behavior. -/
theorem graphL_prev_smul (hp : 1 < p) (hp_top : p ≠ ∞) (c : ℂ) (r R : ℝ≥0)
    (a : ℂ) (u : Lp F p (volume.restrict (closedBall c (r : ℝ)))) :
    WeakDerivStep.prev _ (graphL hp hp_top c r R (a • u)) =
      a • WeakDerivStep.prev _ (graphL hp hp_top c r R u) := by
  rw [graphL_prev, graphL_prev, map_smul]

/-- The weak-derivative projection preserves the full complex scalar behavior. -/
theorem graphL_weakFDeriv_smul (hp : 1 < p) (hp_top : p ≠ ∞) (c : ℂ) (r R : ℝ≥0)
    (a : ℂ) (u : Lp F p (volume.restrict (closedBall c (r : ℝ)))) :
    WeakDerivStep.weakFDeriv _ (graphL hp hp_top c r R (a • u)) =
      a • WeakDerivStep.weakFDeriv _ (graphL hp hp_top c r R u) := by
  rw [graphL_weakFDeriv, graphL_weakFDeriv, map_smul, jetL_smul, map_smul]

end Native

section Coherence

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The graph of a supported datum has exactly its original Cauchy integral as value. -/
theorem graphL_toLp_prev_ae (hp : 1 < p) (hp_top : p ≠ ∞) {f : ℂ → F}
    (hf : MemLp f p (volume : Measure ℂ)) {c : ℂ} {r : ℝ≥0}
    (hs : support f ⊆ closedBall c (r : ℝ)) (R : ℝ≥0) :
    WeakDerivStep.prev _
      (graphL hp hp_top c r R ((hf.restrict (closedBall c (r : ℝ))).toLp f))
        =ᵐ[volume.restrict (disc c R : Set ℂ)] cauchyTransform f := by
  rw [graphL_prev]
  exact (coe_valueL _ _ _ _).trans (.of_forall fun w ↦
    congrFun (cauchyTransform_congr_ae (zeroExtendFn_toLp_ae hf hs)) w)

/-- The graph of a supported datum restricts one original whole-plane derivative class. -/
theorem graphL_toLp_weakFDeriv (hp : 1 < p) (hp_top : p ≠ ∞) {f : ℂ → F}
    (hf : MemLp f p (volume : Measure ℂ)) {c : ℂ} {r : ℝ≥0}
    (hs : support f ⊆ closedBall c (r : ℝ)) (R : ℝ≥0) :
    WeakDerivStep.weakFDeriv _
      (graphL hp hp_top c r R ((hf.restrict (closedBall c (r : ℝ))).toLp f)) =
        (LpToLpRestrictCLM ℂ (ℂ →L[ℝ] F) ℂ volume p (disc c R)) (jetL (beurlingL hp hp_top)
          (hf.toLp f)) := by
  rw [graphL_weakFDeriv, zeroExtend_toLp hf hs]

/-- The original-norm Cauchy integral has the single global weak jet on every open set. -/
theorem hasWeakFDerivOn_cauchy (hp : 1 < p) (hp_top : p ≠ ∞) {f : ℂ → F}
    (hf : MemLp f p (volume : Measure ℂ)) {c : ℂ} {r : ℝ≥0}
    (hs : support f ⊆ closedBall c (r : ℝ)) (Ω : Opens ℂ) :
    HasWeakFDerivOn volume Ω (cauchyTransform f) (jetL (beurlingL hp hp_top) (hf.toLp f)) := by
  have hlocal (R : ℝ≥0) : HasWeakFDerivOn volume (disc c R) (cauchyTransform f)
      (jetL (beurlingL hp hp_top) (hf.toLp f)) := by
    have h := WeakDerivStep.hasWeakFDerivOn_base_prev _
      (graphL hp hp_top c r R ((hf.restrict (closedBall c (r : ℝ))).toLp f))
    simp only [ContinuousLinearMap.id_apply] at h
    refine (h.congr_ae (graphL_toLp_prev_ae hp hp_top hf hs R)).congr_ae_deriv ?_
    rw [graphL_toLp_weakFDeriv hp hp_top hf hs R]
    exact (LpToLpRestrictCLM_coeFn ℂ (_ : Set ℂ) _)
  refine hasWeakFDerivOn_iff_locally.2 fun x _ ↦
    ⟨disc c ((‖x - c‖₊ + 1 : ℝ≥0)), ?_, hlocal _⟩
  rw [mem_disc, mem_ball, dist_eq_norm]
  push_cast
  linarith

/-- The single global derivative has exactly the Beurling and source parts. -/
theorem coe_global_jet (hp : 1 < p) (hp_top : p ≠ ∞) {f : ℂ → F}
    (hf : MemLp f p (volume : Measure ℂ)) :
    jetL (beurlingL hp hp_top) (hf.toLp f) =ᵐ[volume]
      fun w ↦ wirtingerPartsCLM (beurlingL hp hp_top (hf.toLp f) w) (f w) := by
  filter_upwards [coe_jetL (beurlingL hp hp_top) (hf.toLp f), hf.coeFn_toLp] with w hj hf
  rw [hj, hf]

/-- Compactly supported common data have the same weak derivative at all finite exponents. -/
theorem global_jet_exponent_ae {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hp : 1 < p) (hp_top : p ≠ ∞) (hq : 1 < q) (hq_top : q ≠ ∞) {f : ℂ → F}
    (hfp : MemLp f p (volume : Measure ℂ)) (hfq : MemLp f q (volume : Measure ℂ))
    {c : ℂ} {r : ℝ≥0} (hs : support f ⊆ closedBall c (r : ℝ)) :
    jetL (beurlingL hp hp_top) (hfp.toLp f) =ᵐ[volume]
      jetL (beurlingL hq hq_top) (hfq.toLp f) := by
  simpa only [Opens.coe_top, Measure.restrict_univ] using
    (hasWeakFDerivOn_cauchy hp hp_top hfp hs ⊤).ae_eq
      (hasWeakFDerivOn_cauchy hq hq_top hfq hs ⊤)

/-- Compactly supported common data have the same Beurling value at every finite exponent. -/
theorem beurling_exponent_ae {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hp : 1 < p) (hp_top : p ≠ ∞) (hq : 1 < q) (hq_top : q ≠ ∞) {f : ℂ → F}
    (hfp : MemLp f p (volume : Measure ℂ)) (hfq : MemLp f q (volume : Measure ℂ))
    {c : ℂ} {r : ℝ≥0} (hs : support f ⊆ closedBall c (r : ℝ)) :
    beurlingL hp hp_top (hfp.toLp f) =ᵐ[volume]
      beurlingL hq hq_top (hfq.toLp f) := by
  filter_upwards [global_jet_exponent_ae hp hp_top hq hq_top hfp hfq hs,
    coe_global_jet hp hp_top hfp, coe_global_jet hq hq_top hfq] with w hD hp hq
  rw [hp, hq] at hD
  exact (wirtingerPartsCLM_inj.mp hD).1

/-- Enlarging the input support disc leaves the output graph unchanged. -/
theorem graphL_support_radius_eq (hp : 1 < p) (hp_top : p ≠ ∞) {f : ℂ → F}
    (hf : MemLp f p (volume : Measure ℂ)) {c : ℂ} {r s : ℝ≥0}
    (hr : support f ⊆ closedBall c (r : ℝ))
    (hs : support f ⊆ closedBall c (s : ℝ)) (R : ℝ≥0) :
    graphL hp hp_top c r R ((hf.restrict (closedBall c (r : ℝ))).toLp f) =
      graphL hp hp_top c s R ((hf.restrict (closedBall c (s : ℝ))).toLp f) := by
  apply WeakDerivStep.ext
  apply Lp.ext
  exact (graphL_toLp_prev_ae hp hp_top hf hr R).trans
    (graphL_toLp_prev_ae hp hp_top hf hs R).symm

/-- Actual value projections are natural for arbitrary complex-linear coefficient maps. -/
theorem graphL_prev_naturality {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [FiniteDimensional ℂ G] (hp : 1 < p) (hp_top : p ≠ ∞) (L : F →L[ℂ] G)
    (c : ℂ) (r R : ℝ≥0) (u : Lp F p (volume.restrict (closedBall c (r : ℝ)))) :
    WeakDerivStep.prev _
      (graphL hp hp_top c r R (L.compLpL p (volume.restrict (closedBall c (r : ℝ))) u)) =
        L.compLpL p (volume.restrict (disc c R : Set ℂ))
          (WeakDerivStep.prev _ (graphL hp hp_top c r R u)) := by
  rw [graphL_prev, graphL_prev, valueL_comp]

/-- The weak-derivative projections are natural on the same original fibres. -/
theorem graphL_weakFDeriv_naturality {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [FiniteDimensional ℂ G] (hp : 1 < p) (hp_top : p ≠ ∞) (L : F →L[ℂ] G)
    (c : ℂ) (r R : ℝ≥0) (u : Lp F p (volume.restrict (closedBall c (r : ℝ)))) :
    (fun w ↦ (L.restrictScalars ℝ).comp
      (WeakDerivStep.weakFDeriv _ (graphL hp hp_top c r R u) w))
        =ᵐ[volume.restrict (disc c R : Set ℂ)]
      WeakDerivStep.weakFDeriv _
        (graphL hp hp_top c r R (L.compLpL p (volume.restrict (closedBall c (r : ℝ))) u)) := by
  rw [graphL_weakFDeriv, graphL_weakFDeriv, zeroExtend_comp]
  have hj := (jet_naturality hp hp_top L (zeroExtend c r u)).filter_mono
    (ae_mono (Measure.restrict_le_self (s := (disc c R : Set ℂ))))
  filter_upwards [(LpToLpRestrictCLM_coeFn ℂ ((disc c R) : Set ℂ) (jetL (beurlingL hp hp_top)
    (zeroExtend c r u))),
    (LpToLpRestrictCLM_coeFn ℂ ((disc c R) : Set ℂ) (jetL (beurlingL hp hp_top) (L.compLpL p
      volume (zeroExtend c r u)))), hj]
        with w hF hG hj
  rw [hF, hG]
  exact hj

/-- Values on two output discs agree on their common smaller disc. -/
theorem graphL_output_radius_value (hp : 1 < p) (hp_top : p ≠ ∞)
    (c : ℂ) (r R S : ℝ≥0) (u : Lp F p (volume.restrict (closedBall c (r : ℝ)))) :
    (WeakDerivStep.prev (X := Lp F p (volume.restrict (disc c R : Set ℂ)))
      _ (graphL hp hp_top c r R u) : ℂ → F)
      =ᵐ[volume.restrict (disc c (min R S) : Set ℂ)]
        (WeakDerivStep.prev (X := Lp F p (volume.restrict (disc c S : Set ℂ)))
          _ (graphL hp hp_top c r S u) : ℂ → F) := by
  rw [graphL_prev, graphL_prev]
  have hRle : ((min R S : ℝ≥0) : ℝ) ≤ R := by exact_mod_cast min_le_left R S
  have hSle : ((min R S : ℝ≥0) : ℝ) ≤ S := by exact_mod_cast min_le_right R S
  exact Filter.EventuallyEq.trans
    (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hRle)
    (coe_valueL c r R u))
      (Filter.EventuallyEq.symm
        (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hSle) (coe_valueL c r S u)))

/-- Weak derivatives on two output discs restrict the same single global jet. -/
theorem graphL_output_radius_derivative (hp : 1 < p) (hp_top : p ≠ ∞)
    (c : ℂ) (r R S : ℝ≥0) (u : Lp F p (volume.restrict (closedBall c (r : ℝ)))) :
    WeakDerivStep.weakFDeriv _ (graphL hp hp_top c r R u)
      =ᵐ[volume.restrict (disc c (min R S) : Set ℂ)]
        WeakDerivStep.weakFDeriv _ (graphL hp hp_top c r S u) := by
  rw [graphL_weakFDeriv, graphL_weakFDeriv]
  have hRle : ((min R S : ℝ≥0) : ℝ) ≤ R := by exact_mod_cast min_le_left R S
  have hSle : ((min R S : ℝ≥0) : ℝ) ≤ S := by exact_mod_cast min_le_right R S
  exact Filter.EventuallyEq.trans
    (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hRle)
    (LpToLpRestrictCLM_coeFn ℂ (disc c R : Set ℂ)
      (jetL (beurlingL hp hp_top) (zeroExtend c r u))))
        (Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hSle)
          (LpToLpRestrictCLM_coeFn ℂ (disc c S : Set ℂ)
            (jetL (beurlingL hp hp_top) (zeroExtend c r u)))))

end Coherence

section Center

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Different source and output centres give the same values and weak jets on overlaps. -/
theorem graphL_center_overlap (hp : 1 < p) (hp_top : p ≠ ∞) {f : ℂ → F}
    (hf : MemLp f p (volume : Measure ℂ)) (c d : ℂ) (r s R S : ℝ≥0)
    (hc : support f ⊆ closedBall c (r : ℝ))
    (hd : support f ⊆ closedBall d (s : ℝ)) :
    let u := graphL hp hp_top c r R ((hf.restrict (closedBall c (r : ℝ))).toLp f)
    let v := graphL hp hp_top d s S ((hf.restrict (closedBall d (s : ℝ))).toLp f)
    ((WeakDerivStep.prev (X := Lp F p (volume.restrict (disc c R : Set ℂ))) _ u : ℂ → F)
      =ᵐ[volume.restrict ((disc c R : Set ℂ) ∩ (disc d S : Set ℂ))]
        (WeakDerivStep.prev (X := Lp F p (volume.restrict (disc d S : Set ℂ))) _ v : ℂ → F)) ∧
    ((WeakDerivStep.weakFDeriv _ u : ℂ → ℂ →L[ℝ] F)
      =ᵐ[volume.restrict ((disc c R : Set ℂ) ∩ (disc d S : Set ℂ))]
        (WeakDerivStep.weakFDeriv _ v : ℂ → ℂ →L[ℝ] F)) := by
  dsimp only
  have hmC : volume.restrict ((disc c R : Set ℂ) ∩ (disc d S : Set ℂ)) ≤
      volume.restrict (disc c R : Set ℂ) := Measure.restrict_mono_set volume inter_subset_left
  have hmD : volume.restrict ((disc c R : Set ℂ) ∩ (disc d S : Set ℂ)) ≤
      volume.restrict (disc d S : Set ℂ) := Measure.restrict_mono_set volume inter_subset_right
  refine ⟨((graphL_toLp_prev_ae hp hp_top hf hc R).filter_mono (ae_mono hmC)).trans
    ((graphL_toLp_prev_ae hp hp_top hf hd S).filter_mono (ae_mono hmD)).symm, ?_⟩
  rw [graphL_toLp_weakFDeriv hp hp_top hf hc R,
    graphL_toLp_weakFDeriv hp hp_top hf hd S]
  exact (((LpToLpRestrictCLM_coeFn ℂ ((disc c R) : Set ℂ) (jetL (beurlingL hp hp_top) (hf.toLp
    f)))).filter_mono (ae_mono hmC)).trans
      (((LpToLpRestrictCLM_coeFn ℂ ((disc d S) : Set ℂ) (jetL (beurlingL hp hp_top) (hf.toLp
        f)))).filter_mono (ae_mono hmD)).symm

end Center

end TauCeti.CauchyTransform
