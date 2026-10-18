/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
import Mathlib.Analysis.Calculus.ImplicitContDiff
import TauCeti.Analysis.Matrix.HermitianSignature.Continuity

/-!
# Continuation of a nondegenerate critical point

A nondegenerate critical point of a smooth finite-dimensional family persists uniquely under a
small change of the parameter.  The critical point is obtained by applying the implicit function
theorem to the spatial differential of the family.  It depends smoothly on the parameter, remains
nondegenerate with unchanged Morse index, and its critical value has the same first derivative as
the family with the spatial variable held fixed at the original critical point.

The uniqueness assertion is local jointly in the parameter and spatial variables.  Thus it rules
out other critical points only in the neighbourhood on which the implicit function theorem applies;
it makes no global assertion about the critical locus of a member of the family.

## Main declaration

* `TauCeti.IsNondegenerateCriticalPoint.exists_contDiffAt_criticalPoint_continuation`: a local
  smooth branch of nondegenerate critical points, unique near its base point.

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

omit [FiniteDimensional ℝ E] in
private theorem sigNeg_toMatrix {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I ℝ E) (B : LinearMap.BilinForm ℝ E) :
    sigNeg ((B.toMatrix b).toQuadraticForm') = sigNeg B.toQuadraticMap := by
  apply QuadraticMap.Equivalent.sigNeg_eq
  refine ⟨{
    toLinearEquiv := b.equivFun.symm
    map_app' := fun v ↦ ?_ }⟩
  rw [Matrix.toQuadraticForm'_apply, LinearMap.BilinMap.toQuadraticMap_apply]
  exact (B.dotProduct_toMatrix_mulVec b v v).symm

/-- **Continuation of a nondegenerate critical point.**

Let `F p x` be a `C³` family of real functions.  A nondegenerate critical point `x` of the
member at `p` extends to a `C²` branch `ψ` of nondegenerate critical points near `p`.  This branch
is the unique critical point near `(p, x)`, and its Morse index is locally constant.  The
corresponding critical value is `C²`, and its derivative at `p` is the derivative obtained by
freezing the spatial variable at `x`.

The continuation function is total, as is Mathlib's implicit function, but all its characteristic
properties are local at the base parameter. -/
theorem exists_contDiffAt_criticalPoint_continuation
    (h : IsNondegenerateCriticalPoint (fun y ↦ F (p, y)) x) (hF : ContDiff ℝ 3 F) :
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
  have hG : ContDiff ℝ 2 G := by
    apply ContDiff.fderiv (f := fun q : P × E ↦ fun y : E ↦ F (q.1, y))
      (g := fun q : P × E ↦ q.2)
    · exact hF.comp (by fun_prop)
    · fun_prop
    · norm_num
  have hvertical (q : P) (y : E) :
      (fderiv ℝ G (q, y)).comp (ContinuousLinearMap.inr ℝ P E) =
        fderiv ℝ (fderiv ℝ (fun z ↦ F (q, z))) y := by
    have hslice := (hG.differentiable (by norm_num) (q, y)).hasFDerivAt.comp y
      (hasFDerivAt_prodMk_right q y)
    have hsliceFun : G ∘ Prod.mk q = fderiv ℝ (fun z ↦ F (q, z)) := rfl
    rw [hsliceFun] at hslice
    exact hslice.fderiv.symm
  have hbase : G (p, x) = 0 := by
    simpa only [G] using h.fderiv_eq_zero
  have hinv :
      ((fderiv ℝ G (p, x)).comp (ContinuousLinearMap.inr ℝ P E)).IsInvertible := by
    rw [hvertical]
    exact h.isInvertible
  let ψ : P → E := hG.contDiffAt.implicitFunction (by norm_num) hinv
  have hψp : ψ p = x := hG.contDiffAt.implicitFunction_apply_self (by norm_num) hinv
  have hψ : ContDiffAt ℝ 2 ψ p :=
    hG.contDiffAt.contDiffAt_implicitFunction (by norm_num) hinv
  have hcrit : ∀ᶠ q in 𝓝 p, G (q, ψ q) = 0 := by
    simpa only [hbase] using
      hG.contDiffAt.eventually_apply_implicitFunction (by norm_num) hinv
  have hunique : ∀ᶠ q in 𝓝 (p, x), G q = 0 ↔ ψ q.1 = q.2 := by
    simpa only [hbase] using
      hG.contDiffAt.eventually_apply_eq_iff_implicitFunction (by norm_num) hinv
  have hverticalContinuous : ContinuousAt
      (fun q ↦ (fderiv ℝ G (q, ψ q)).comp (ContinuousLinearMap.inr ℝ P E)) p := by
    exact ((hG.continuous_fderiv (by norm_num)).continuousAt.comp
      (continuousAt_id.prodMk hψ.continuousAt)).clm_comp continuousAt_const
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
    filter_upwards [hcrit, hinvEventually] with q hqcrit hqinv
    refine ⟨?_, ?_, ?_⟩
    · exact hF.contDiffAt.comp (ψ q) (contDiffAt_const.prodMk contDiffAt_id) |>.of_le (by norm_num)
    · simpa only [G] using hqcrit
    · rw [← hvertical]
      exact hqinv
  let b := Module.finBasis ℝ E
  let V : P → E →L[ℝ] E →L[ℝ] ℝ := fun q ↦
    (fderiv ℝ G (q, ψ q)).comp (ContinuousLinearMap.inr ℝ P E)
  let A : P → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun q ↦ (V q).toBilinForm.toMatrix b
  have hAContinuous : ContinuousAt A p := by
    apply continuousAt_pi.2
    intro i
    apply continuousAt_pi.2
    intro j
    simpa only [A, V, LinearMap.BilinForm.toMatrix_apply,
      ContinuousLinearMap.toBilinForm_apply] using
      (hverticalContinuous.clm_apply continuousAt_const).clm_apply continuousAt_const
  have hAHermitian (q : P) : (A q).IsHermitian := by
    have hslice : ContDiffAt ℝ 2 (fun y ↦ F (q, y)) (ψ q) :=
      hF.contDiffAt.comp (ψ q) (contDiffAt_const.prodMk contDiffAt_id) |>.of_le (by norm_num)
    have hsymm : (V q).toBilinForm.IsSymm := by
      refine ⟨?_⟩
      intro u v
      simp only [V, ContinuousLinearMap.toBilinForm_apply]
      rw [hvertical]
      exact hslice.isSymmSndFDerivAt (by norm_num) u v
    have hmatrixSymm : (A q).IsSymm := by
      exact ((V q).toBilinForm.isSymm_toMatrix_iff_isSymm b).mpr hsymm
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.IsSymm] using hmatrixSymm
  have hdet : IsUnit (A p).det := by
    rw [isUnit_iff_ne_zero]
    apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp
    apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    have hVbase : V p = fderiv ℝ (fderiv ℝ (fun y ↦ F (p, y))) x := by
      simp only [V, hψp]
      exact hvertical p x
    rw [hVbase]
    exact h.separatingLeft
  have hmatrixIndex (q : P) :
      sigNeg ((A q).toQuadraticForm') = morseIndex (fun y ↦ F (q, y)) (ψ q) := by
    rw [sigNeg_toMatrix b, morseIndex_def]
    congr 1
    ext v
    rw [LinearMap.BilinMap.toQuadraticMap_apply, hessianQuadraticForm_apply]
    simp only [V, ContinuousLinearMap.toBilinForm_apply]
    rw [hvertical]
  have hindex : ∀ᶠ q in 𝓝 p,
      morseIndex (fun y ↦ F (q, y)) (ψ q) = morseIndex (fun y ↦ F (p, y)) x := by
    have hcongr := hAContinuous.eventually
      ((hAHermitian p).eventually_exists_conjTranspose_mul_mul_eq hdet)
    filter_upwards [hcongr] with q hq
    obtain ⟨R, hR, hRA⟩ := hq (hAHermitian q)
    have hRA' : R.transpose * A p * R.transpose.transpose = A q := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using
        hRA
    have hequiv : (A q).toQuadraticForm'.Equivalent (A p).toQuadraticForm' := by
      rw [← hRA']
      exact ⟨Matrix.isometryEquivCongr (by simpa using hR) (A p)⟩
    rw [← hmatrixIndex q, ← hψp, ← hmatrixIndex p]
    exact QuadraticMap.Equivalent.sigNeg_eq hequiv
  have hvalue : ContDiffAt ℝ 2 (fun q ↦ F (q, ψ q)) p :=
    (hF.of_le (by norm_num)).contDiffAt.comp p (contDiffAt_id.prodMk hψ)
  have hfamilyAt : HasFDerivAt F (fderiv ℝ F (p, x)) (p, x) :=
    (hF.differentiable (by norm_num) (p, x)).hasFDerivAt
  have hvalueDeriv :
      fderiv ℝ (fun q ↦ F (q, ψ q)) p = fderiv ℝ (fun q ↦ F (q, x)) p := by
    have hfamilyAt' : HasFDerivAt F (fderiv ℝ F (p, x)) (p, ψ p) := by
      rw [hψp]
      exact hfamilyAt
    have hleft := hfamilyAt'.comp p
      ((hasFDerivAt_id p).prodMk (hψ.differentiableAt (by norm_num)).hasFDerivAt)
    have hleftFun : F ∘ (fun q ↦ (id q, ψ q)) = fun q ↦ F (q, ψ q) := rfl
    rw [hleftFun] at hleft
    have hright : HasFDerivAt (fun q ↦ F (q, x))
        ((fderiv ℝ F (p, x)).comp (ContinuousLinearMap.inl ℝ P E)) p :=
      hfamilyAt.comp p (hasFDerivAt_prodMk_left p x)
    have hleftDeriv : fderiv ℝ (fun q ↦ F (q, ψ q)) p =
        (fderiv ℝ F (p, x)).comp
          ((ContinuousLinearMap.id ℝ P).prod (fderiv ℝ ψ p)) := by
      simpa only [Function.comp_apply, id_eq] using hleft.fderiv
    rw [hleftDeriv, hright.fderiv]
    apply ContinuousLinearMap.ext
    intro v
    have hcritical : fderiv ℝ F (p, x) (0, fderiv ℝ ψ p v) = 0 := by
      have hslice : HasFDerivAt (fun y ↦ F (p, y))
          ((fderiv ℝ F (p, x)).comp (ContinuousLinearMap.inr ℝ P E)) x :=
        hfamilyAt.comp x (hasFDerivAt_prodMk_right p x)
      have hzero : (fderiv ℝ F (p, x)).comp (ContinuousLinearMap.inr ℝ P E) = 0 :=
        hslice.fderiv.symm.trans h.fderiv_eq_zero
      simpa using congrArg (fun L : E →L[ℝ] ℝ ↦ L (fderiv ℝ ψ p v)) hzero
    calc
      fderiv ℝ F (p, x) (v, fderiv ℝ ψ p v) =
          fderiv ℝ F (p, x) (v, 0) +
            fderiv ℝ F (p, x) (0, fderiv ℝ ψ p v) := by
        rw [← map_add]
        congr 1
        ext <;> simp
      _ = fderiv ℝ F (p, x) (v, 0) := by rw [hcritical, add_zero]
  refine ⟨ψ, hψp, hψ, hnondegenerate, hindex, ?_, hvalue, hvalueDeriv⟩
  simpa only [G] using hunique

end TauCeti.IsNondegenerateCriticalPoint
