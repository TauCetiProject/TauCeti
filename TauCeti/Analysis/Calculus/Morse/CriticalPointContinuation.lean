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
import TauCeti.Analysis.Calculus.ImplicitFunctionTheorem
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

The construction only needs the critical point to be nondegenerate in the fibre direction, and
works for a `C^{n+1}` family on a neighbourhood: it gives a `C^n` section `h` of critical points
of the fibre restrictions `v ↦ f (b, v)`, unique near the base point, over an arbitrary complete
base and fibre.  Along such a section, the critical points of the whole function `f (b, v)` are
the points `(b, h b)` at which the reduced function `b ↦ f (b, h b)` is critical, since the
derivative of the reduced function is the base derivative of `f` along the graph.

## Main declarations

* `TauCeti.exists_vertical_critical_section_of_contDiffOn`: the section of vertical critical
  points, unique near the base point.
* `TauCeti.eventually_fderiv_eq_zero_iff_snd_eq_and_fderiv_comp_graph_eq_zero`: the critical
  points of `f` are the critical points of the reduced function, lifted along the section.
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

namespace TauCeti

section VerticalCritical

open Set

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : P × F → ℝ} {a : P}

/-- **The section of vertical critical points.** Let `f` be `C^{n+1}` on a neighbourhood `W` of
`(a, c)`, with `n ≠ 0`, such that `v ↦ f (a, v)` is critical at `c` with invertible Hessian. Then
there is a section `h`, `C^n` on an open neighbourhood `U` of `a` and with `h a = c`, whose graph
over `U` lies in `W` and consists of critical points of the fibre restrictions `v ↦ f (b, v)`;
near `(a, c)`, these vertical critical points are exactly the points of the graph. -/
theorem exists_vertical_critical_section_of_contDiffOn [CompleteSpace P] [CompleteSpace F]
    {n : WithTop ℕ∞} {c : F}
    {W : Set (P × F)} (hW : W ∈ 𝓝 (a, c)) (hf : ContDiffOn ℝ (n + 1) f W)
    (hcrit : fderiv ℝ (fun v ↦ f (a, v)) c = 0)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ f (a, v))) c).IsInvertible) (hn : n ≠ 0) :
    ∃ (h : P → F) (U : Set P), IsOpen U ∧ a ∈ U ∧ h a = c ∧ ContDiffOn ℝ n h U ∧
      (∀ b ∈ U, (b, h b) ∈ W) ∧ (∀ b ∈ U, fderiv ℝ (fun v ↦ f (b, v)) (h b) = 0) ∧
      ∀ᶠ z in 𝓝 (a, c), fderiv ℝ (fun v ↦ f (z.1, v)) z.2 = 0 ↔ z.2 = h z.1 := by
  have hs : IsOpen (interior W) := isOpen_interior
  have hacs : (a, c) ∈ interior W := mem_interior_iff_mem_nhds.2 hW
  -- The vertical derivative, whose zeros are the vertical critical points.
  let G : P × F → F →L[ℝ] ℝ := fun z ↦ fderiv ℝ (fun v ↦ f (z.1, v)) z.2
  have hG : ContDiffOn ℝ n G (interior W) := fun z hz ↦
    ((hf.contDiffAt (mem_interior_iff_mem_nhds.1 hz)).fderiv_slice le_rfl).contDiffWithinAt
  have hGac : ContDiffAt ℝ n G (a, c) := hG.contDiffAt (hs.mem_nhds hacs)
  -- Its derivative along the fibre at `(a, c)` is the vertical Hessian.
  have hinv : (fderiv ℝ G (a, c) ∘L ContinuousLinearMap.inr ℝ P F).IsInvertible := by
    rw [← fderiv_slice_right (hGac.differentiableAt hn)]
    exact hH
  let h : P → F := hGac.implicitFunction hn hinv
  have hha : h a = c := hGac.implicitFunction_apply_self hn hinv
  obtain ⟨U₁, hU₁, haU₁, hh⟩ := hG.exists_isOpen_contDiffOn_implicitFunction hs hacs hn hinv
  have hhc : ContinuousAt h a := hh.continuousOn.continuousAt (hU₁.mem_nhds haU₁)
  have hgraph : ∀ᶠ b in 𝓝 a, (b, h b) ∈ interior W := by
    have ht : Tendsto (fun b ↦ (b, h b)) (𝓝 a) (𝓝 (a, h a)) := tendsto_id.prodMk_nhds hhc
    rw [hha] at ht
    exact ht (hs.mem_nhds hacs)
  have hcritG : ∀ᶠ b in 𝓝 a, G (b, h b) = 0 := by
    simpa only [G, hcrit] using hGac.eventually_apply_implicitFunction hn hinv
  obtain ⟨U, hUsub, hU, haU⟩ :=
    _root_.mem_nhds_iff.1 (inter_mem (hU₁.mem_nhds haU₁) (hgraph.and hcritG))
  refine ⟨h, U, hU, haU, hha, hh.mono fun b hb ↦ (hUsub hb).1,
    fun b hb ↦ interior_subset (hUsub hb).2.1, fun b hb ↦ (hUsub hb).2.2, ?_⟩
  filter_upwards [hGac.eventually_apply_eq_iff_implicitFunction hn hinv] with z hz
  rw [eq_comm (a := z.2)]
  simpa only [G, hcrit] using hz

/-- **Critical points along a section of vertical critical points.** Let `f` be differentiable
near `(a, h a)` and `h` differentiable near `a`, and suppose that near `(a, h a)` the critical
points of the fibre restrictions `v ↦ f (b, v)` are exactly the points of the graph of `h`. Then
near `(a, h a)` the critical points of `f` are exactly the points `(b, h b)` at which the reduced
function `b ↦ f (b, h b)` is critical. -/
theorem eventually_fderiv_eq_zero_iff_snd_eq_and_fderiv_comp_graph_eq_zero {h : P → F}
    (hf : ∀ᶠ z in 𝓝 (a, h a), DifferentiableAt ℝ f z)
    (hh : ∀ᶠ b in 𝓝 a, DifferentiableAt ℝ h b)
    (hsec : ∀ᶠ z in 𝓝 (a, h a), fderiv ℝ (fun v ↦ f (z.1, v)) z.2 = 0 ↔ z.2 = h z.1) :
    ∀ᶠ z in 𝓝 (a, h a),
      fderiv ℝ f z = 0 ↔ z.2 = h z.1 ∧ fderiv ℝ (fun b ↦ f (b, h b)) z.1 = 0 := by
  have hgraph : ∀ᶠ z in 𝓝 (a, h a), DifferentiableAt ℝ f (z.1, h z.1) :=
    (continuousAt_fst.prodMk (hh.self_of_nhds.continuousAt.comp continuousAt_fst)).eventually hf
  have hh' : ∀ᶠ z in 𝓝 (a, h a), DifferentiableAt ℝ h z.1 := continuousAt_fst.eventually hh
  filter_upwards [hf, hsec, hgraph, hh'] with ⟨x, y⟩ hfz hsecz hgz hhz
  dsimp only at hsecz hgz hhz ⊢
  -- Along the graph, the reduced function has the base derivative of `f`.
  have hred (hzero : fderiv ℝ (fun v ↦ f (x, v)) (h x) = 0) :
      fderiv ℝ (fun b ↦ f (b, h b)) x =
        (fderiv ℝ f (x, h x)).comp (ContinuousLinearMap.inl ℝ P F) := by
    rw [hgz.hasFDerivAt.fderiv_comp_graph_eq_fderiv_slice_of_fderiv_right_eq_zero hhz hzero,
      fderiv_slice_left hgz]
  constructor
  · intro h0
    obtain rfl : y = h x :=
      hsecz.1 (by rw [fderiv_slice_right hfz, h0, ContinuousLinearMap.zero_comp])
    exact ⟨rfl, by rw [hred (hsecz.2 rfl), h0, ContinuousLinearMap.zero_comp]⟩
  · rintro ⟨rfl, h0⟩
    have hv := hsecz.2 rfl
    rw [hred hv] at h0
    refine ContinuousLinearMap.ext fun w ↦ ?_
    rw [fderiv_apply_eq_fderiv_slice_left_add_fderiv_slice_right hfz, fderiv_slice_left hfz, h0, hv]
    simp

end VerticalCritical

namespace IsNondegenerateCriticalPoint

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
  have hsymm :
      ((fderiv ℝ G (p, ψ p)).comp (ContinuousLinearMap.inr ℝ P E)).toBilinForm.IsSymm := by
    have hslice : ContDiffAt ℝ 2 (fun y ↦ F (p, y)) (ψ p) :=
      hF.comp (ψ p) (contDiffAt_const.prodMk contDiffAt_id)
    refine ⟨fun u v ↦ ?_⟩
    simp only [ContinuousLinearMap.toBilinForm_apply,
      hGhess p (hG.differentiableAt (by norm_num))]
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
  obtain ⟨W, hW, hFW⟩ := hF.contDiffOn (m := 2 + 1) (by norm_num) (by norm_num)
  obtain ⟨ψ, U, hU, hpU, hψp, hψU, -, hcritU, hunique⟩ :=
    exists_vertical_critical_section_of_contDiffOn hW hFW h.fderiv_eq_zero h.isInvertible
      (by norm_num)
  have hψ : ContDiffAt ℝ 2 ψ p := hψU.contDiffAt (hU.mem_nhds hpU)
  let G : P × E → E →L[ℝ] ℝ := fun q ↦ fderiv ℝ (fun y ↦ F (q.1, y)) q.2
  have hG : ContDiffAt ℝ 2 G (p, x) := hF.fderiv_slice (by norm_num)
  have hinv :
      ((fderiv ℝ G (p, x)).comp (ContinuousLinearMap.inr ℝ P E)).IsInvertible := by
    rw [← fderiv_slice_right (hG.differentiableAt (by norm_num))]
    exact h.isInvertible
  have hFbase : ContDiffAt ℝ 3 F (p, ψ p) := by simpa only [hψp] using hF
  have hF2 : ContDiffAt ℝ 2 F (p, ψ p) := hFbase.of_le (by norm_num)
  have hcrit : ∀ᶠ q in 𝓝 p, G (q, ψ q) = 0 :=
    eventually_of_mem (hU.mem_nhds hpU) hcritU
  have hinv' : ((fderiv ℝ G (p, ψ p)).comp (ContinuousLinearMap.inr ℝ P E)).IsInvertible := by
    rwa [hψp]
  have hfamilyAt : HasFDerivAt F (fderiv ℝ F (p, ψ p)) (p, ψ p) :=
    (hFbase.differentiableAt (by norm_num)).hasFDerivAt
  have hvalueDeriv :
      fderiv ℝ (fun q ↦ F (q, ψ q)) p = fderiv ℝ (fun q ↦ F (q, x)) p := by
    simpa only [hψp] using
      hfamilyAt.fderiv_comp_graph_eq_fderiv_slice_of_fderiv_right_eq_zero
        (hψ.differentiableAt (by norm_num)) (hcritU p hpU)
  refine ⟨ψ, hψp, hψ,
    eventually_isNondegenerateCriticalPoint_graph rfl hF2 hψ.continuousAt hinv' hcrit,
    eventually_morseIndex_graph rfl h hF2 hψp hψ.continuousAt, ?_,
    (hFbase.of_le (by norm_num)).comp p (contDiffAt_id.prodMk hψ), hvalueDeriv⟩
  exact hunique.mono fun q hq ↦ hq.trans eq_comm

end IsNondegenerateCriticalPoint

end TauCeti
