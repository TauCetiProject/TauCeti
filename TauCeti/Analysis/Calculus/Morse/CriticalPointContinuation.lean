/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
import Mathlib.Analysis.Calculus.ImplicitContDiff
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Matrix.HermitianSignature.Continuity

/-!
# Continuation of a nondegenerate critical point

A nondegenerate critical point of a C³ finite-dimensional family persists uniquely under a
small change of the parameter.  The critical point is obtained by applying the implicit function
theorem to the spatial differential of the family.  It depends locally C² on the parameter,
remains nondegenerate with unchanged Morse index, and its critical value has the same first
derivative as the family with the spatial variable held fixed at the original critical point.

The uniqueness assertion is local jointly in the parameter and spatial variables.  Thus it rules
out other critical points only in the neighbourhood on which the implicit function theorem applies;
it makes no global assertion about the critical locus of a member of the family.

## Main declaration

* `TauCeti.IsNondegenerateCriticalPoint.exists_contDiffAt_criticalPoint_continuation`: a local
  C² branch of nondegenerate critical points, unique near its base point.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1.
-/

public section

open Filter Function
open scoped ContDiff Topology

noncomputable section

namespace TauCeti.IsNondegenerateCriticalPoint

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : P × E → ℝ} {p : P} {x : E}

omit [CompleteSpace P] in
/-- Near the base point, the continued critical points are nondegenerate. -/
private theorem eventually_isNondegenerateCriticalPoint_graph
    {G : P × E → E →L[ℝ] ℝ} {ψ : P → E}
    (hGF : G = fun q ↦ fderiv ℝ (fun y ↦ F (q.1, y)) q.2)
    (hF : ContDiffAt ℝ 2 F (p, ψ p)) (hψ : ContinuousAt ψ p)
    (hinv : ((fderiv ℝ G (p, ψ p)).comp (ContinuousLinearMap.inr ℝ P E)).IsInvertible)
    (hcrit : ∀ᶠ q in 𝓝 p, G (q, ψ q) = 0) :
    ∀ᶠ q in 𝓝 p, IsNondegenerateCriticalPoint (fun y ↦ F (q, y)) (ψ q) := by
  subst hGF
  have hG : ContDiffAt ℝ 1 (fun q : P × E ↦ fderiv ℝ (fun y ↦ F (q.1, y)) q.2) (p, ψ p) :=
    hF.fderiv_slice (by norm_num)
  filter_upwards [hcrit,
    (hG.continuousAt_fderiv_comp_inr hψ).eventually hinv.eventually_nhds,
    hF.eventually_contDiffAt_graph hψ, hG.eventually_contDiffAt_graph hψ] with
    q hqcrit hqinv hFq hGq
  refine ⟨?_, hqcrit, ?_⟩
  · exact hFq.comp (ψ q) (contDiffAt_const.prodMk contDiffAt_id) |>.of_le (by norm_num)
  · rw [← fderiv_slice_right (hGq.differentiableAt (by norm_num))] at hqinv
    exact hqinv

omit [CompleteSpace P] in
/-- Near the base point, the Morse index of the continued critical points is constant. -/
private theorem eventually_morseIndex_graph {G : P × E → E →L[ℝ] ℝ} {ψ : P → E}
    (hGF : G = fun q ↦ fderiv ℝ (fun y ↦ F (q.1, y)) q.2)
    (h : IsNondegenerateCriticalPoint (fun y ↦ F (p, y)) x) (hF : ContDiffAt ℝ 2 F (p, ψ p))
    (hψp : ψ p = x) (hψ : ContinuousAt ψ p) :
    ∀ᶠ q in 𝓝 p,
      morseIndex (fun y ↦ F (q, y)) (ψ q) = morseIndex (fun y ↦ F (p, y)) x := by
  have hG : ContDiffAt ℝ 1 G (p, ψ p) := by
    rw [hGF]
    exact hF.fderiv_slice (by norm_num)
  have hGhess (q : P) (hd : DifferentiableAt ℝ G (q, ψ q)) :
      (fderiv ℝ G (q, ψ q)).comp (ContinuousLinearMap.inr ℝ P E) =
        fderiv ℝ (fderiv ℝ (fun y ↦ F (q, y))) (ψ q) := by
    rw [← fderiv_slice_right hd]
    congr 1
    funext y
    rw [hGF]
  have hGAlong := hG.eventually_contDiffAt_graph hψ
  have hsymm : ∀ᶠ q in 𝓝 p,
      ((fderiv ℝ G (q, ψ q)).comp (ContinuousLinearMap.inr ℝ P E)).toBilinForm.IsSymm := by
    filter_upwards [hF.eventually_contDiffAt_graph hψ, hGAlong] with q hFq hGq
    have hslice : ContDiffAt ℝ 2 (fun y ↦ F (q, y)) (ψ q) :=
      hFq.comp (ψ q) (contDiffAt_const.prodMk contDiffAt_id) |>.of_le (by norm_num)
    refine ⟨fun u v ↦ ?_⟩
    simp only [ContinuousLinearMap.toBilinForm_apply,
      hGhess q (hGq.differentiableAt (by norm_num))]
    exact hslice.isSymmSndFDerivAt (by norm_num) u v
  have hnd :
      ((fderiv ℝ G (p, ψ p)).comp (ContinuousLinearMap.inr ℝ P E)).toBilinForm.Nondegenerate := by
    apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    rw [hGhess p (hG.differentiableAt (by norm_num)), hψp]
    exact h.separatingLeft
  have hmorseIndex (q : P) (hGq : ContDiffAt ℝ 1 G (q, ψ q)) :
      morseIndex (fun y ↦ F (q, y)) (ψ q) =
        sigNeg ((fderiv ℝ G (q, ψ q)).comp
          (ContinuousLinearMap.inr ℝ P E)).toBilinForm.toQuadraticMap := by
    rw [morseIndex_def, hessianQuadraticForm_def, hGhess q (hGq.differentiableAt (by norm_num))]
  filter_upwards [ContinuousLinearMap.eventually_sigNeg_toBilinForm_eq_of_continuousAt hsymm
    (hG.continuousAt_fderiv_comp_inr hψ) hnd, hGAlong] with q hq hGq
  rw [hmorseIndex q hGq, hq, ← hmorseIndex p hG, hψp]

/-- **Continuation of a nondegenerate critical point.**

Let `F p x` be a `C³` family of real functions.  A nondegenerate critical point `x` of the
member at `p` extends to a `C²` branch `ψ` of nondegenerate critical points near `p`.  This branch
is the unique critical point near `(p, x)`, and its Morse index is locally constant.  The
corresponding critical value is `C²`, and its derivative at `p` is the derivative obtained by
freezing the spatial variable at `x`.

The continuation function is total, as is Mathlib's implicit function, but all its characteristic
properties are local at the base parameter. -/
theorem exists_contDiffAt_criticalPoint_continuation
    (h : IsNondegenerateCriticalPoint (fun y ↦ F (p, y)) x) (hF : ContDiffAt ℝ 3 F (p, x)) :
    ∃ ψ : P → E,
      ψ p = x ∧
      ContDiffAt ℝ 2 ψ p ∧
      (∀ᶠ q in 𝓝 p, IsNondegenerateCriticalPoint (fun y ↦ F (q, y)) (ψ q)) ∧
      (∀ᶠ q in 𝓝 p,
        morseIndex (fun y ↦ F (q, y)) (ψ q) = morseIndex (fun y ↦ F (p, y)) x) ∧
      (∀ᶠ q in 𝓝 (p, x),
        fderiv ℝ (fun y ↦ F (q.1, y)) q.2 = 0 ↔ ψ q.1 = q.2) ∧
      ContDiffAt ℝ 2 (fun q ↦ F (q, ψ q)) p ∧
      fderiv ℝ (fun q ↦ F (q, ψ q)) p = fderiv ℝ (fun q ↦ F (q, x)) p := by
  let G : P × E → E →L[ℝ] ℝ := fun q ↦ fderiv ℝ (fun y ↦ F (q.1, y)) q.2
  have hG : ContDiffAt ℝ 2 G (p, x) := hF.fderiv_slice (by norm_num)
  have hbase : G (p, x) = 0 := by
    simpa only [G] using h.fderiv_eq_zero
  have hinv :
      ((fderiv ℝ G (p, x)).comp (ContinuousLinearMap.inr ℝ P E)).IsInvertible := by
    rw [← fderiv_slice_right (hG.differentiableAt (by norm_num))]
    exact h.isInvertible
  let ψ : P → E := hG.implicitFunction (by norm_num) hinv
  have hψp : ψ p = x := hG.implicitFunction_apply_self (by norm_num) hinv
  have hψ : ContDiffAt ℝ 2 ψ p := hG.contDiffAt_implicitFunction (by norm_num) hinv
  have hFbase : ContDiffAt ℝ 3 F (p, ψ p) := by simpa only [hψp] using hF
  have hF2 : ContDiffAt ℝ 2 F (p, ψ p) := hFbase.of_le (by norm_num)
  have hcrit : ∀ᶠ q in 𝓝 p, G (q, ψ q) = 0 := by
    simpa only [hbase] using hG.eventually_apply_implicitFunction (by norm_num) hinv
  have hunique : ∀ᶠ q in 𝓝 (p, x), G q = 0 ↔ ψ q.1 = q.2 := by
    simpa only [hbase] using hG.eventually_apply_eq_iff_implicitFunction (by norm_num) hinv
  have hinv' : ((fderiv ℝ G (p, ψ p)).comp (ContinuousLinearMap.inr ℝ P E)).IsInvertible := by
    rwa [hψp]
  have hfamilyAt : HasFDerivAt F (fderiv ℝ F (p, ψ p)) (p, ψ p) :=
    (hFbase.differentiableAt (by norm_num)).hasFDerivAt
  have hvalueDeriv :
      fderiv ℝ (fun q ↦ F (q, ψ q)) p = fderiv ℝ (fun q ↦ F (q, x)) p := by
    have hcritical : fderiv ℝ (fun y ↦ F (p, y)) (ψ p) = 0 := by
      simpa only [hψp] using h.fderiv_eq_zero
    simpa only [hψp] using
      hfamilyAt.fderiv_comp_graph_eq_fderiv_slice_of_fderiv_right_eq_zero
        (hψ.differentiableAt (by norm_num)) hcritical
  refine ⟨ψ, hψp, hψ,
    eventually_isNondegenerateCriticalPoint_graph rfl hF2 hψ.continuousAt hinv' hcrit,
    eventually_morseIndex_graph rfl h hF2 hψp hψ.continuousAt, ?_,
    (hFbase.of_le (by norm_num)).comp p (contDiffAt_id.prodMk hψ), hvalueDeriv⟩
  simpa only [G] using hunique

end TauCeti.IsNondegenerateCriticalPoint
