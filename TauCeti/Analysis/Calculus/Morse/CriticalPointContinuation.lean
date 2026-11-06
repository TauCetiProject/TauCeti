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

omit [CompleteSpace P] [FiniteDimensional ℝ E] in
/-- The spatial differential of a `C^n` family is `C^m` jointly in the parameter and the spatial
variable, for `m + 1 ≤ n`. -/
theorem _root_.TauCeti.contDiffAt_fderiv_slice {n m : WithTop ℕ∞}
    (hF : ContDiffAt ℝ n F (p, x)) (hmn : m + 1 ≤ n) :
    ContDiffAt ℝ m (fun q : P × E ↦ fderiv ℝ (fun y ↦ F (q.1, y)) q.2) (p, x) := by
  apply ContDiffAt.fderiv (n := n) (m := m) (x₀ := (p, x))
    (f := fun q : P × E ↦ fun y : E ↦ F (q.1, y)) (g := fun q : P × E ↦ q.2)
  · exact hF.comp ((p, x), x) (by fun_prop)
  · fun_prop
  · exact hmn

omit [CompleteSpace P] [FiniteDimensional ℝ E] in
/-- A function that is `C^n` at `(p, ψ p)` is `C^n` at `(q, ψ q)` for `q` near `p`, when `ψ` is
continuous at `p`. -/
theorem _root_.TauCeti.eventually_contDiffAt_graph {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {f : P × E → X} {ψ : P → E} {n : ℕ} (hf : ContDiffAt ℝ n f (p, ψ p))
    (hψ : ContinuousAt ψ p) : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ n f (q, ψ q) :=
  (continuousAt_id.prodMk hψ).eventually (hf.eventually (by norm_num))

omit [CompleteSpace P] [FiniteDimensional ℝ E] in
/-- The vertical part of the derivative of a `C²` map is continuous along a `C²` graph. -/
theorem _root_.TauCeti.continuousAt_fderiv_comp_inr {G : P × E → E →L[ℝ] ℝ} {ψ : P → E}
    (hG : ContDiffAt ℝ 2 G (p, ψ p)) (hψ : ContDiffAt ℝ 2 ψ p) :
    ContinuousAt (fun q ↦ (fderiv ℝ G (q, ψ q)).comp (ContinuousLinearMap.inr ℝ P E)) p :=
  ((hG.continuousAt_fderiv (by norm_num)).comp_of_eq
    (f := fun q ↦ (q, ψ q)) (continuousAt_id.prodMk hψ.continuousAt) rfl).clm_comp
    continuousAt_const

omit [CompleteSpace P] [FiniteDimensional ℝ E] in
/-- The vertical part of the derivative of the spatial differential is the Hessian of the slice. -/
private theorem fderiv_comp_inr_eq_hessian {G : P × E → E →L[ℝ] ℝ} {q : P}
    (hGF : G = fun q ↦ fderiv ℝ (fun y ↦ F (q.1, y)) q.2) (hG : DifferentiableAt ℝ G (q, x)) :
    (fderiv ℝ G (q, x)).comp (ContinuousLinearMap.inr ℝ P E) =
      fderiv ℝ (fderiv ℝ (fun y ↦ F (q, y))) x := by
  subst hGF
  exact (fderiv_slice_right hG).symm

omit [CompleteSpace P] in
/-- Near the base point, the continued critical points are nondegenerate. -/
private theorem eventually_isNondegenerateCriticalPoint_graph
    {G : P × E → E →L[ℝ] ℝ} {ψ : P → E}
    (hGF : G = fun q ↦ fderiv ℝ (fun y ↦ F (q.1, y)) q.2)
    (hF : ContDiffAt ℝ 3 F (p, ψ p)) (hψ : ContDiffAt ℝ 2 ψ p)
    (hinv : ((fderiv ℝ G (p, ψ p)).comp (ContinuousLinearMap.inr ℝ P E)).IsInvertible)
    (hcrit : ∀ᶠ q in 𝓝 p, G (q, ψ q) = 0) :
    ∀ᶠ q in 𝓝 p, IsNondegenerateCriticalPoint (fun y ↦ F (q, y)) (ψ q) := by
  have hG : ContDiffAt ℝ 2 G (p, ψ p) := by
    rw [hGF]
    exact contDiffAt_fderiv_slice hF (by norm_num)
  filter_upwards [hcrit, (continuousAt_fderiv_comp_inr hG hψ).eventually hinv.eventually_nhds,
    eventually_contDiffAt_graph hF hψ.continuousAt,
    eventually_contDiffAt_graph hG hψ.continuousAt] with q hqcrit hqinv hFq hGq
  refine ⟨?_, by simpa only [hGF] using hqcrit, ?_⟩
  · exact hFq.comp (ψ q) (contDiffAt_const.prodMk contDiffAt_id) |>.of_le (by norm_num)
  · rw [← fderiv_comp_inr_eq_hessian hGF (hGq.differentiableAt (by norm_num))]
    exact hqinv

omit [CompleteSpace P] in
/-- Near the base point, the Morse index of the continued critical points is constant. -/
private theorem eventually_morseIndex_graph {G : P × E → E →L[ℝ] ℝ} {ψ : P → E}
    (hGF : G = fun q ↦ fderiv ℝ (fun y ↦ F (q.1, y)) q.2)
    (h : IsNondegenerateCriticalPoint (fun y ↦ F (p, y)) x) (hF : ContDiffAt ℝ 3 F (p, ψ p))
    (hψp : ψ p = x) (hψ : ContDiffAt ℝ 2 ψ p) :
    ∀ᶠ q in 𝓝 p,
      morseIndex (fun y ↦ F (q, y)) (ψ q) = morseIndex (fun y ↦ F (p, y)) x := by
  have hG : ContDiffAt ℝ 2 G (p, ψ p) := by
    rw [hGF]
    exact contDiffAt_fderiv_slice hF (by norm_num)
  have hGAlong := eventually_contDiffAt_graph hG hψ.continuousAt
  have hsymm : ∀ᶠ q in 𝓝 p,
      ((fderiv ℝ G (q, ψ q)).comp (ContinuousLinearMap.inr ℝ P E)).toBilinForm.IsSymm := by
    filter_upwards [eventually_contDiffAt_graph hF hψ.continuousAt, hGAlong] with q hFq hGq
    have hslice : ContDiffAt ℝ 2 (fun y ↦ F (q, y)) (ψ q) :=
      hFq.comp (ψ q) (contDiffAt_const.prodMk contDiffAt_id) |>.of_le (by norm_num)
    refine ⟨fun u v ↦ ?_⟩
    simp only [ContinuousLinearMap.toBilinForm_apply,
      fderiv_comp_inr_eq_hessian hGF (hGq.differentiableAt (by norm_num))]
    exact hslice.isSymmSndFDerivAt (by norm_num) u v
  have hnd :
      ((fderiv ℝ G (p, ψ p)).comp (ContinuousLinearMap.inr ℝ P E)).toBilinForm.Nondegenerate := by
    apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    rw [fderiv_comp_inr_eq_hessian hGF (hG.differentiableAt (by norm_num)), hψp]
    exact h.separatingLeft
  have hmorseIndex (q : P) (hGq : ContDiffAt ℝ 2 G (q, ψ q)) :
      morseIndex (fun y ↦ F (q, y)) (ψ q) =
        sigNeg ((fderiv ℝ G (q, ψ q)).comp
          (ContinuousLinearMap.inr ℝ P E)).toBilinForm.toQuadraticMap := by
    rw [morseIndex_def]
    congr 1
    ext v
    rw [LinearMap.BilinMap.toQuadraticMap_apply, hessianQuadraticForm_apply,
      ContinuousLinearMap.toBilinForm_apply,
      fderiv_comp_inr_eq_hessian hGF (hGq.differentiableAt (by norm_num))]
  filter_upwards [ContinuousLinearMap.eventually_sigNeg_toBilinForm_eq_of_continuousAt hsymm
    (continuousAt_fderiv_comp_inr hG hψ) hnd, hGAlong] with q hq hGq
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
  have hG : ContDiffAt ℝ 2 G (p, x) := contDiffAt_fderiv_slice hF (by norm_num)
  have hbase : G (p, x) = 0 := by
    simpa only [G] using h.fderiv_eq_zero
  have hinv :
      ((fderiv ℝ G (p, x)).comp (ContinuousLinearMap.inr ℝ P E)).IsInvertible := by
    rw [fderiv_comp_inr_eq_hessian rfl (hG.differentiableAt (by norm_num))]
    exact h.isInvertible
  let ψ : P → E := hG.implicitFunction (by norm_num) hinv
  have hψp : ψ p = x := hG.implicitFunction_apply_self (by norm_num) hinv
  have hψ : ContDiffAt ℝ 2 ψ p := hG.contDiffAt_implicitFunction (by norm_num) hinv
  have hFbase : ContDiffAt ℝ 3 F (p, ψ p) := by simpa only [hψp] using hF
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
  refine ⟨ψ, hψp, hψ, eventually_isNondegenerateCriticalPoint_graph rfl hFbase hψ hinv' hcrit,
    eventually_morseIndex_graph rfl h hFbase hψp hψ, ?_,
    (hFbase.of_le (by norm_num)).comp p (contDiffAt_id.prodMk hψ), hvalueDeriv⟩
  simpa only [G] using hunique

end TauCeti.IsNondegenerateCriticalPoint
