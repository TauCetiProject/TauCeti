/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Strip.Jet
public import TauCeti.Analysis.Sobolev.JetOperator
public import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Changes of frame acting on jets

Let `Φ : ℝ × ℝ → L(V, W)` be a differentiable family of linear maps, a *frame* in which sections
of the trivial bundle with fibre `V` over a domain of the plane are read as sections with fibre
`W`. By the product rule the jet of `w ↦ Φ w (ξ w)` is
`(Φ ξ, Φ ∂s ξ + (∂s Φ) ξ, Φ ∂t ξ + (∂t Φ) ξ)`, a pointwise linear function of the jet
`(ξ, ∂s ξ, ∂t ξ)` of `ξ`. This file names that coefficient field,
`TauCeti.StripSobolev.frameJetCoeff Φ` (`TauCeti.StripSobolev.jet_frame_eq_frameJetCoeff`), and
proves the properties that let it act on Sobolev spaces of jets:

* composing two changes of frame is the change of frame by the pointwise composite
  (`TauCeti.StripSobolev.frameJetCoeff_comp_frameJetCoeff`), and the constant identity frame acts
  as the identity (`TauCeti.StripSobolev.frameJetCoeff_const_id`);
* the coefficient field is bounded by `‖Φ‖ + ‖dΦ‖`
  (`TauCeti.StripSobolev.norm_frameJetCoeff_le`), so it is essentially bounded on the strip when `Φ`
  is `C¹` with `Φ` and `dΦ` bounded (`TauCeti.StripSobolev.memLp_frameJetCoeff`);
* first-order operators `∂s + A ∂t + C` (`TauCeti.firstOrderJetCoeff`) are carried to operators of
  the same form: if `Ψ z` is a left inverse of `Φ z`, then reading `∂s + A ∂t + C` in the frame
  gives `∂s + (Ψ A Φ) ∂t + Ψ (C Φ + ∂s Φ + A ∂t Φ)`
  (`TauCeti.StripSobolev.comp_firstOrderJetCoeff_comp_frameJetCoeff`). For `A = J` the new
  zeroth-order coefficient is the one that `TauCeti.frameCoeff` records for Cauchy–Riemann
  operators on domains of `ℂ`.

Multiplication by a differentiable function `β(s)`, `TauCeti.StripSobolev.cutoffCoeff`, is the
change of frame by the scalar frame `β(s) • id`
(`TauCeti.StripSobolev.cutoffCoeff_eq_frameJetCoeff`).

Changes of frame are how a linearized Floer operator along a map is read in a trivialization of
the pulled-back tangent bundle, and how two trivializations are compared; the action of frames
on the Sobolev space of the cylinder is in `TauCeti.Analysis.Sobolev.Cylinder.Frame`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1,
  on real Cauchy–Riemann operators read in trivializations.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace TauCeti

variable {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup U] [NormedSpace ℝ U]

namespace StripSobolev

/-- The coefficient field of the change of frame `ξ ↦ (w ↦ Φ w (ξ w))`, acting on jets:
`(a, b, c) ↦ (Φ a, Φ b + (∂s Φ) a, Φ c + (∂t Φ) a)`. On the jet of a section `ξ` it is the jet of
`w ↦ Φ w (ξ w)` (`TauCeti.StripSobolev.jet_frame_eq_frameJetCoeff`). -/
def frameJetCoeff (Φ : ℝ × ℝ → V →L[ℝ] W) (z : ℝ × ℝ) : V × V × V →L[ℝ] W × W × W :=
  (Φ z).prodMap ((Φ z).prodMap (Φ z)) +
    (ContinuousLinearMap.inr ℝ W (W × W)).comp
      (((fderiv ℝ Φ z (1, 0)).prod (fderiv ℝ Φ z (0, 1))).comp
        (ContinuousLinearMap.fst ℝ V (V × V)))

/-- The components of `frameJetCoeff Φ z v`. -/
@[simp]
theorem frameJetCoeff_apply (Φ : ℝ × ℝ → V →L[ℝ] W) (z : ℝ × ℝ) (v : V × V × V) :
    frameJetCoeff Φ z v = (Φ z v.1, Φ z v.2.1 + fderiv ℝ Φ z (1, 0) v.1,
      Φ z v.2.2 + fderiv ℝ Φ z (0, 1) v.1) := by
  obtain ⟨a, b, c⟩ := v
  simp [frameJetCoeff]

/-- **The jet in a frame.** The jet of `w ↦ Φ w (ξ w)` is `frameJetCoeff Φ` applied to the jet of
`ξ`. -/
theorem jet_frame_eq_frameJetCoeff {Φ : ℝ × ℝ → V →L[ℝ] W} {ξ : ℝ × ℝ → V} {z : ℝ × ℝ}
    (hΦ : DifferentiableAt ℝ Φ z) (hξ : DifferentiableAt ℝ ξ z) :
    jet (fun w ↦ Φ w (ξ w)) z = frameJetCoeff Φ z (jet ξ z) := by
  simp [jet_apply, fderiv_clm_apply hΦ hξ]

/-- **Composition of changes of frame.** Changing the frame by `Φ` and then by `Ψ` is changing it
by the pointwise composite `Ψ Φ`. -/
theorem frameJetCoeff_comp_frameJetCoeff {Ψ : ℝ × ℝ → W →L[ℝ] U} {Φ : ℝ × ℝ → V →L[ℝ] W}
    {z : ℝ × ℝ} (hΨ : DifferentiableAt ℝ Ψ z) (hΦ : DifferentiableAt ℝ Φ z) :
    (frameJetCoeff Ψ z).comp (frameJetCoeff Φ z) = frameJetCoeff (fun w ↦ (Ψ w).comp (Φ w)) z := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, frameJetCoeff_apply, fderiv_clm_comp hΨ hΦ,
    add_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, map_add, Prod.mk.injEq, true_and]
  constructor <;> abel

/-- The change of frame by a constant family of maps `A` acts on each component of a jet by `A`. -/
@[simp]
theorem frameJetCoeff_const (A : V →L[ℝ] W) (z : ℝ × ℝ) :
    frameJetCoeff (fun _ ↦ A) z = A.prodMap (A.prodMap A) := by
  refine ContinuousLinearMap.ext fun ⟨a, b, c⟩ ↦ ?_
  simp

/-- The change of frame by the constant identity frame is the identity. -/
theorem frameJetCoeff_const_id (z : ℝ × ℝ) :
    frameJetCoeff (fun _ ↦ ContinuousLinearMap.id ℝ V) z =
      ContinuousLinearMap.id ℝ (V × V × V) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp

/-- **Multiplication by `β(s)` is a change of frame.** For `β` differentiable at `s`, the
coefficient field of multiplication by `β(s)` is that of the change of frame by `β(s) • id`. -/
theorem cutoffCoeff_eq_frameJetCoeff {β : ℝ → ℝ} {z : ℝ × ℝ} (hβ : DifferentiableAt ℝ β z.1) :
    cutoffCoeff V β z = frameJetCoeff (fun w ↦ β w.1 • ContinuousLinearMap.id ℝ V) z := by
  have hβ' : HasFDerivAt (fun w : ℝ × ℝ ↦ β w.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ (deriv β z.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)) z :=
    hβ.hasDerivAt.hasFDerivAt.comp z hasFDerivAt_fst
  have hd := hβ'.smul_const (ContinuousLinearMap.id ℝ V)
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp [hd.fderiv]

/-- The coefficient field of a change of frame has norm at most `‖Φ z‖ + ‖dΦ z‖`. -/
theorem norm_frameJetCoeff_le (Φ : ℝ × ℝ → V →L[ℝ] W) (z : ℝ × ℝ) :
    ‖frameJetCoeff Φ z‖ ≤ ‖Φ z‖ + ‖fderiv ℝ Φ z‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  -- The jet `v` bounds each of its components, and `(1, 0)`, `(0, 1)` have norm `1`.
  have h₁ : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
  have h₂ : ‖v.2.1‖ ≤ ‖v‖ := (norm_fst_le v.2).trans (norm_snd_le v)
  have h₃ : ‖v.2.2‖ ≤ ‖v‖ := (norm_snd_le v.2).trans (norm_snd_le v)
  have hd (e : ℝ × ℝ) (he : ‖e‖ ≤ 1) : ‖fderiv ℝ Φ z e v.1‖ ≤ ‖fderiv ℝ Φ z‖ * ‖v‖ :=
    calc ‖fderiv ℝ Φ z e v.1‖ ≤ ‖fderiv ℝ Φ z e‖ * ‖v.1‖ := (fderiv ℝ Φ z e).le_opNorm _
      _ ≤ (‖fderiv ℝ Φ z‖ * ‖e‖) * ‖v‖ :=
          mul_le_mul ((fderiv ℝ Φ z).le_opNorm e) h₁ (norm_nonneg _) (by positivity)
      _ ≤ ‖fderiv ℝ Φ z‖ * ‖v‖ :=
          mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) he) (norm_nonneg _)
  have hΦv (a : V) (ha : ‖a‖ ≤ ‖v‖) : ‖Φ z a‖ ≤ ‖Φ z‖ * ‖v‖ :=
    ((Φ z).le_opNorm a).trans (by gcongr)
  have hd₁ := hd (1, 0) (by simp [Prod.norm_def])
  have hd₂ := hd (0, 1) (by simp [Prod.norm_def])
  rw [frameJetCoeff_apply, add_mul]
  refine norm_prod_le_iff.2 ⟨(hΦv _ h₁).trans (le_add_of_nonneg_right (by positivity)),
    norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
  · exact (norm_add_le _ _).trans (add_le_add (hΦv _ h₂) hd₁)
  · exact (norm_add_le _ _).trans (add_le_add (hΦv _ h₃) hd₂)

/-- The coefficient field of a change of frame by a `C¹` family is continuous. -/
theorem continuous_frameJetCoeff {Φ : ℝ × ℝ → V →L[ℝ] W} (hΦ : ContDiff ℝ 1 Φ) :
    Continuous (frameJetCoeff Φ) := by
  have hd := hΦ.continuous_fderiv one_ne_zero
  refine ((hΦ.continuous.prod_mapL ℝ) (hΦ.continuous.prod_mapL ℝ hΦ.continuous)).add ?_
  have hprod : Continuous fun z ↦ (fderiv ℝ Φ z (1, 0)).prod (fderiv ℝ Φ z (0, 1)) :=
    (ContinuousLinearMap.prodL ℝ).continuous.comp
      ((hd.clm_apply continuous_const).prodMk (hd.clm_apply continuous_const))
  exact continuous_const.clm_comp (hprod.clm_comp continuous_const)

/-- For a `C¹` frame `Φ` with `Φ` and `dΦ` bounded, the coefficient field of the change of frame
is essentially bounded. -/
theorem memLp_frameJetCoeff {Φ : ℝ × ℝ → V →L[ℝ] W} (hΦ : ContDiff ℝ 1 Φ) {B : ℝ}
    (hΦB : ∀ z, ‖Φ z‖ ≤ B) (hΦ'B : ∀ z, ‖fderiv ℝ Φ z‖ ≤ B) :
    MemLp (frameJetCoeff Φ) ∞ stripMeasure :=
  memLp_top_of_bound (continuous_frameJetCoeff hΦ).aestronglyMeasurable (B + B)
    (ae_of_all _ fun z ↦ (norm_frameJetCoeff_le Φ z).trans (add_le_add (hΦB z) (hΦ'B z)))

/-- **First-order operators in a frame.** Let `Ψ z` be a left inverse of `Φ z`. Reading the
operator `∂s + A ∂t + C` in the frame `Φ`, that is, composing its coefficient field with the change
of frame by `Φ` and then applying `Ψ`, gives the operator
`∂s + (Ψ A Φ) ∂t + Ψ (C Φ + ∂s Φ + A ∂t Φ)`. -/
theorem comp_firstOrderJetCoeff_comp_frameJetCoeff {Φ : ℝ × ℝ → V →L[ℝ] W}
    {Ψ : ℝ × ℝ → W →L[ℝ] V} {A C : ℝ × ℝ → W →L[ℝ] W} {z : ℝ × ℝ}
    (hΨΦ : (Ψ z).comp (Φ z) = ContinuousLinearMap.id ℝ V) :
    ((Ψ z).comp (firstOrderJetCoeff (A z) (C z))).comp (frameJetCoeff Φ z) =
      firstOrderJetCoeff ((Ψ z).comp ((A z).comp (Φ z)))
        ((Ψ z).comp ((C z).comp (Φ z) + fderiv ℝ Φ z (1, 0) +
          (A z).comp (fderiv ℝ Φ z (0, 1)))) := by
  have h (v : V) : Ψ z (Φ z v) = v := by
    rw [← ContinuousLinearMap.comp_apply, hΨΦ, ContinuousLinearMap.id_apply]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, frameJetCoeff_apply, firstOrderJetCoeff_apply,
    add_apply, map_add, h]
  abel

end StripSobolev

end TauCeti
