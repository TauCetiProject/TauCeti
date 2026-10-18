/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
import Mathlib.Analysis.Calculus.ImplicitContDiff
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
  have hG : ContDiffAt ℝ 2 G (p, x) := by
    apply ContDiffAt.fderiv (n := 3) (m := 2) (x₀ := (p, x))
      (f := fun q : P × E ↦ fun y : E ↦ F (q.1, y)) (g := fun q : P × E ↦ q.2)
    · exact hF.comp ((p, x), x) (by fun_prop)
    · fun_prop
    · norm_num
  have hvertical (q : P) (y : E) (hGqy : DifferentiableAt ℝ G (q, y)) :
      (fderiv ℝ G (q, y)).comp (ContinuousLinearMap.inr ℝ P E) =
        fderiv ℝ (fderiv ℝ (fun z ↦ F (q, z))) y := by
    have hslice := hGqy.hasFDerivAt.comp y
      (hasFDerivAt_prodMk_right q y)
    have hsliceFun : G ∘ Prod.mk q = fderiv ℝ (fun z ↦ F (q, z)) := rfl
    rw [hsliceFun] at hslice
    exact hslice.fderiv.symm
  have hbase : G (p, x) = 0 := by
    simpa only [G] using h.fderiv_eq_zero
  have hinv :
      ((fderiv ℝ G (p, x)).comp (ContinuousLinearMap.inr ℝ P E)).IsInvertible := by
    rw [hvertical p x (hG.differentiableAt (by norm_num))]
    exact h.isInvertible
  let ψ : P → E := hG.implicitFunction (by norm_num) hinv
  have hψp : ψ p = x := hG.implicitFunction_apply_self (by norm_num) hinv
  have hψ : ContDiffAt ℝ 2 ψ p :=
    hG.contDiffAt_implicitFunction (by norm_num) hinv
  have hFbase : ContDiffAt ℝ 3 F (p, ψ p) := by simpa only [hψp] using hF
  have hGbase : ContDiffAt ℝ 2 G (p, ψ p) := by simpa only [hψp] using hG
  have hcrit : ∀ᶠ q in 𝓝 p, G (q, ψ q) = 0 := by
    simpa only [hbase] using
      hG.eventually_apply_implicitFunction (by norm_num) hinv
  have hunique : ∀ᶠ q in 𝓝 (p, x), G q = 0 ↔ ψ q.1 = q.2 := by
    simpa only [hbase] using
      hG.eventually_apply_eq_iff_implicitFunction (by norm_num) hinv
  have hverticalContinuous : ContinuousAt
      (fun q ↦ (fderiv ℝ G (q, ψ q)).comp (ContinuousLinearMap.inr ℝ P E)) p := by
    have hfd : ContinuousAt (fun q ↦ fderiv ℝ G (q, ψ q)) p :=
      (hG.continuousAt_fderiv (by norm_num)).comp_of_eq
        (f := fun q ↦ (q, ψ q)) (continuousAt_id.prodMk hψ.continuousAt) (by simp [hψp])
    exact hfd.clm_comp continuousAt_const
  have hFAlong : ∀ᶠ q in nhds p, ContDiffAt ℝ 3 F (q, ψ q) :=
    (continuousAt_id.prodMk hψ.continuousAt).eventually (hFbase.eventually (by norm_num))
  have hGAlong : ∀ᶠ q in nhds p, ContDiffAt ℝ 2 G (q, ψ q) :=
    (continuousAt_id.prodMk hψ.continuousAt).eventually (hGbase.eventually (by norm_num))
  have hinvEventually : ∀ᶠ q in 𝓝 p,
      ((fderiv ℝ G (q, ψ q)).comp (ContinuousLinearMap.inr ℝ P E)).IsInvertible :=
    hverticalContinuous.eventually (by
      have hinv' :
          ((fderiv ℝ G (p, ψ p)).comp (ContinuousLinearMap.inr ℝ P E)).IsInvertible := by
        rw [hψp]
        exact hinv
      exact hinv'.eventually_nhds)
  have hnondegenerate : ∀ᶠ q in 𝓝 p,
      IsNondegenerateCriticalPoint (fun y ↦ F (q, y)) (ψ q) := by
    filter_upwards [hcrit, hinvEventually, hFAlong, hGAlong] with q hqcrit hqinv hFq hGq
    refine ⟨?_, ?_, ?_⟩
    · exact hFq.comp (ψ q) (contDiffAt_const.prodMk contDiffAt_id) |>.of_le (by norm_num)
    · simpa only [G] using hqcrit
    · rw [← hvertical q (ψ q) (hGq.differentiableAt (by norm_num))]
      exact hqinv
  let V : P → E →L[ℝ] E →L[ℝ] ℝ := fun q ↦
    (fderiv ℝ G (q, ψ q)).comp (ContinuousLinearMap.inr ℝ P E)
  have hVhessian (q : P) (hGq : ContDiffAt ℝ 2 G (q, ψ q)) :
      V q = fderiv ℝ (fderiv ℝ (fun y ↦ F (q, y))) (ψ q) :=
    hvertical q (ψ q) (hGq.differentiableAt (by norm_num))
  have hsymm : ∀ᶠ q in 𝓝 p, (V q).toBilinForm.IsSymm := by
    filter_upwards [hFAlong, hGAlong] with q hFq hGq
    have hslice : ContDiffAt ℝ 2 (fun y ↦ F (q, y)) (ψ q) :=
      hFq.comp (ψ q) (contDiffAt_const.prodMk contDiffAt_id) |>.of_le (by norm_num)
    refine ⟨fun u v ↦ ?_⟩
    simp only [ContinuousLinearMap.toBilinForm_apply, hVhessian q hGq]
    exact hslice.isSymmSndFDerivAt (by norm_num) u v
  have hnd : (V p).toBilinForm.Nondegenerate := by
    apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    rw [hVhessian p hGbase, hψp]
    exact h.separatingLeft
  have hmorseIndex (q : P) (hGq : ContDiffAt ℝ 2 G (q, ψ q)) :
      morseIndex (fun y ↦ F (q, y)) (ψ q) = sigNeg (V q).toBilinForm.toQuadraticMap := by
    rw [morseIndex_def]
    congr 1
    ext v
    rw [LinearMap.BilinMap.toQuadraticMap_apply, hessianQuadraticForm_apply,
      ContinuousLinearMap.toBilinForm_apply, hVhessian q hGq]
  have hindex : ∀ᶠ q in 𝓝 p,
      morseIndex (fun y ↦ F (q, y)) (ψ q) = morseIndex (fun y ↦ F (p, y)) x := by
    filter_upwards [ContinuousLinearMap.eventually_sigNeg_toBilinForm_eq_of_continuousAt hsymm
      hverticalContinuous hnd, hGAlong] with q hq hGq
    rw [hmorseIndex q hGq, hq, ← hmorseIndex p hGbase, hψp]
  have hvalue : ContDiffAt ℝ 2 (fun q ↦ F (q, ψ q)) p :=
    (hFbase.of_le (by norm_num)).comp p (contDiffAt_id.prodMk hψ)
  have hfamilyAt : HasFDerivAt F (fderiv ℝ F (p, x)) (p, x) :=
    (hF.differentiableAt (by norm_num)).hasFDerivAt
  have hvalueDeriv :
      fderiv ℝ (fun q ↦ F (q, ψ q)) p = fderiv ℝ (fun q ↦ F (q, x)) p := by
    have hfamilyAt' : HasFDerivAt F (fderiv ℝ F (p, x)) (p, ψ p) := by
      rw [hψp]
      exact hfamilyAt
    have hcritical : fderiv ℝ (fun y ↦ F (p, y)) (ψ p) = 0 := by
      simpa only [hψp] using h.fderiv_eq_zero
    simpa only [hψp] using
      hfamilyAt'.fderiv_comp_graph_eq_fderiv_slice_of_fderiv_right_eq_zero
        (hψ.differentiableAt (by norm_num)) hcritical
  refine ⟨ψ, hψp, hψ, hnondegenerate, hindex, ?_, hvalue, hvalueDeriv⟩
  simpa only [G] using hunique

end TauCeti.IsNondegenerateCriticalPoint
