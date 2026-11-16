/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.Composition.Basic
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Calculus.ContDiff.Differentiable

/-!
# Simultaneous stationary elimination for three generating functions

For three generating functions `S(q,a)`, `T(a,b)` and `R(b,Q)`, the open-chain action is
`S(q,a) + T(a,b) + R(b,Q)`. Its stationary equations in `(a,b)` are precisely the two
intermediate cotangent matching equations. If the full Hessian in `(a,b)` is invertible,
the implicit function theorem eliminates both intermediate positions simultaneously.
The resulting critical value has source covector `d_q S` and target covector `-d_Q R`.

Unlike successive two-function elimination, this construction does not require an invertible
Hessian in either intermediate position separately. Local uniqueness is joint in the endpoint
and intermediate positions; no global uniqueness of stationary configurations is asserted.
The endpoint formulas identify the resulting relation with the matched three-edge relation
along the selected branch. When all three edge mixed Hessians are invertible, so is the reduced
mixed Hessian. Together with the regularity of the critical value, this
supplies the hypotheses of `TauCeti.cotangentGeneratedMap`.

The endpoint/internal-variable packaging and elimination construction follow
`TauCeti.exists_cotangentGeneratingComposition` in
`TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.Composition.Basic`. Here that theorem is
applied with the two internal positions grouped into a single product space.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Section 5.1, Proposition 5.2 and
  the following exercise (generating functions of second and third iterates).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, §48.
-/

public section

noncomputable section

open ContinuousLinearMap Filter
open scoped Topology

namespace TauCeti

variable {V W U Z : Type*}

/-- The three-edge open-chain action, with endpoint positions `(q,Q)` as parameters and
intermediate positions `(a,b)` as the variables to eliminate. -/
def cotangentGeneratingTripleSum (S : V × W → ℝ) (T : W × U → ℝ) (R : U × Z → ℝ)
    (x : (V × Z) × (W × U)) : ℝ :=
  S (x.1.1, x.2.1) + T x.2 + R (x.2.2, x.1.2)

@[simp]
theorem cotangentGeneratingTripleSum_apply (S : V × W → ℝ) (T : W × U → ℝ)
    (R : U × Z → ℝ) (q : V) (Q : Z) (a : W) (b : U) :
    cotangentGeneratingTripleSum S T R ((q, Q), (a, b)) = S (q, a) + T (a, b) + R (b, Q) :=
  (rfl)

/-- Evaluation of the three-edge action at an arbitrary configuration. -/
theorem cotangentGeneratingTripleSum_def (S : V × W → ℝ) (T : W × U → ℝ)
    (R : U × Z → ℝ) (x : (V × Z) × (W × U)) :
    cotangentGeneratingTripleSum S T R x =
      S (x.1.1, x.2.1) + T x.2 + R (x.2.2, x.1.2) :=
  (rfl)

/-- Grouping the internal positions expresses the action as a two-function sum. -/
private theorem cotangentGeneratingTripleSum_eq_cotangentGeneratingSum (S : V × W → ℝ)
    (T : W × U → ℝ) (R : U × Z → ℝ) :
    cotangentGeneratingTripleSum S T R = cotangentGeneratingSum
      (fun p ↦ S (p.1, p.2.1) + T p.2) (fun p ↦ R (p.1.2, p.2)) := by
  funext ⟨⟨q, Q⟩, a, b⟩
  simp

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {S : V × W → ℝ} {T : W × U → ℝ} {R : U × Z → ℝ}

/-- The open-chain action is as smooth as its three summands. -/
theorem contDiffAt_cotangentGeneratingTripleSum {x : (V × Z) × (W × U)} {n : WithTop ℕ∞}
    (hS : ContDiffAt ℝ n S (x.1.1, x.2.1)) (hT : ContDiffAt ℝ n T x.2)
    (hR : ContDiffAt ℝ n R (x.2.2, x.1.2)) :
    ContDiffAt ℝ n (cotangentGeneratingTripleSum S T R) x :=
  ((hS.comp x (contDiffAt_fst.fst.prodMk contDiffAt_snd.fst)).add
    (hT.comp x contDiffAt_snd)).add
      (hR.comp x (contDiffAt_snd.snd.prodMk contDiffAt_fst.snd))

/-- The three-edge action is differentiable when its summands are differentiable. -/
theorem differentiableAt_cotangentGeneratingTripleSum {x : (V × Z) × (W × U)}
    (hS : DifferentiableAt ℝ S (x.1.1, x.2.1)) (hT : DifferentiableAt ℝ T x.2)
    (hR : DifferentiableAt ℝ R (x.2.2, x.1.2)) :
    DifferentiableAt ℝ (cotangentGeneratingTripleSum S T R) x :=
  ((hS.comp x (differentiableAt_fst.fst.prodMk differentiableAt_snd.fst)).add
    (hT.comp x differentiableAt_snd)).add
      (hR.comp x (differentiableAt_snd.snd.prodMk differentiableAt_fst.snd))

/-- The differential of the open-chain action, with all four position variations explicit. -/
theorem fderiv_cotangentGeneratingTripleSum_apply {x : (V × Z) × (W × U)}
    (hS : DifferentiableAt ℝ S (x.1.1, x.2.1)) (hT : DifferentiableAt ℝ T x.2)
    (hR : DifferentiableAt ℝ R (x.2.2, x.1.2)) (v : (V × Z) × (W × U)) :
    fderiv ℝ (cotangentGeneratingTripleSum S T R) x v =
      fderiv ℝ S (x.1.1, x.2.1) (v.1.1, v.2.1) + fderiv ℝ T x.2 v.2 +
        fderiv ℝ R (x.2.2, x.1.2) (v.2.2, v.1.2) := by
  have hd := ((hS.hasFDerivAt.comp x
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).fst.prodMk
      (hasFDerivAt_snd (𝕜 := ℝ) (p := x)).fst)).add
      (hT.hasFDerivAt.comp x hasFDerivAt_snd)).add
        (hR.hasFDerivAt.comp x
          ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).snd.prodMk
            (hasFDerivAt_fst (𝕜 := ℝ) (p := x)).snd))
  exact congrArg (fun L ↦ L v) hd.fderiv

/-- The full internal negative Hessian consists of the first edge's negative internal Hessian,
minus the middle edge's full Hessian and the last edge's first-variable Hessian. -/
theorem cotangentLegendreHessian_cotangentGeneratingTripleSum_apply_apply
    {x : (V × Z) × (W × U)}
    (hS : ContDiffAt ℝ 2 S (x.1.1, x.2.1)) (hT : ContDiffAt ℝ 2 T x.2)
    (hR : ContDiffAt ℝ 2 R (x.2.2, x.1.2)) (u v : W × U) :
    cotangentLegendreHessian (cotangentGeneratingTripleSum S T R) x u v =
      cotangentLegendreHessian S (x.1.1, x.2.1) u.1 v.1 -
        fderiv ℝ (fderiv ℝ T) x.2 u v -
        fderiv ℝ (fderiv ℝ R) (x.2.2, x.1.2) (u.2, 0) (v.2, 0) := by
  have hds := (hS.hasFDerivAt_fderiv_apply le_rfl (0, v.1)).comp x
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).fst.prodMk
      (hasFDerivAt_snd (𝕜 := ℝ) (p := x)).fst)
  have hdt := (hT.hasFDerivAt_fderiv_apply le_rfl v).comp x hasFDerivAt_snd
  have hdr := (hR.hasFDerivAt_fderiv_apply le_rfl (v.2, 0)).comp x
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).snd.prodMk
      (hasFDerivAt_fst (𝕜 := ℝ) (p := x)).snd)
  have heq : (fun z ↦ fderiv ℝ (cotangentGeneratingTripleSum S T R) z (0, v)) =ᶠ[𝓝 x]
      fun z ↦ fderiv ℝ S (z.1.1, z.2.1) (0, v.1) + fderiv ℝ T z.2 v +
        fderiv ℝ R (z.2.2, z.1.2) (v.2, 0) := by
    have hsc : ContinuousAt (fun z : (V × Z) × (W × U) ↦ (z.1.1, z.2.1)) x := by fun_prop
    have hrc : ContinuousAt (fun z : (V × Z) × (W × U) ↦ (z.2.2, z.1.2)) x := by fun_prop
    filter_upwards [hsc.eventually (hS.eventually_differentiableAt (by norm_num)),
      continuousAt_snd.eventually (hT.eventually_differentiableAt (by norm_num)),
      hrc.eventually (hR.eventually_differentiableAt (by norm_num))] with z hzS hzT hzR
    simpa using fderiv_cotangentGeneratingTripleSum_apply hzS hzT hzR (0, v)
  have hd := ((hds.add hdt).add hdr).congr_of_eventuallyEq heq
  have ha := ((contDiffAt_cotangentGeneratingTripleSum hS hT hR).hasFDerivAt_fderiv_apply
    le_rfl (0, v)).unique hd
  have hu := congrArg (fun L ↦ L (0, u)) ha
  simp only [cotangentLegendreHessian_apply_apply]
  simpa [sub_eq_add_neg, neg_add, add_comm, add_left_comm, add_assoc] using congrArg Neg.neg hu

/-- Stationarity in both intermediate positions is exactly matching at both intermediate
cotangent points. No nondegeneracy assumption is needed for this equivalence. -/
theorem cotangentGeneratingTarget_tripleSum_snd_eq_zero_iff {x : (V × Z) × (W × U)}
    (hS : DifferentiableAt ℝ S (x.1.1, x.2.1)) (hT : DifferentiableAt ℝ T x.2)
    (hR : DifferentiableAt ℝ R (x.2.2, x.1.2)) :
    (cotangentGeneratingTarget (cotangentGeneratingTripleSum S T R) x).2 = 0 ↔
      cotangentGeneratingTarget S (x.1.1, x.2.1) = cotangentGeneratingSource T x.2 ∧
      cotangentGeneratingTarget T x.2 = cotangentGeneratingSource R (x.2.2, x.1.2) := by
  constructor
  · intro h
    constructor
    · apply Prod.ext (by simp)
      ext w
      have hw := congrArg (fun p : StrongDual ℝ (W × U) ↦ p (w, 0)) h
      simp only [cotangentGeneratingTarget_snd_apply,
        fderiv_cotangentGeneratingTripleSum_apply hS hT hR, Prod.fst_zero, Prod.snd_zero,
        ← Prod.zero_eq_mk, map_zero, add_zero, _root_.zero_apply,
        cotangentGeneratingSource_snd_apply] at hw ⊢
      linarith
    · apply Prod.ext (by simp)
      ext u
      have hu := congrArg (fun p : StrongDual ℝ (W × U) ↦ p (0, u)) h
      simp only [cotangentGeneratingTarget_snd_apply,
        fderiv_cotangentGeneratingTripleSum_apply hS hT hR, Prod.fst_zero, Prod.snd_zero,
        ← Prod.zero_eq_mk, map_zero, zero_add, _root_.zero_apply,
        cotangentGeneratingSource_snd_apply] at hu ⊢
      linarith
  · rintro ⟨h₁, h₂⟩
    apply ContinuousLinearMap.ext
    rintro ⟨w, u⟩
    have hw := congrArg (fun p : W × StrongDual ℝ W ↦ p.2 w) h₁
    have hu := congrArg (fun p : U × StrongDual ℝ U ↦ p.2 u) h₂
    have hadd := (fderiv ℝ T x.2).map_add (w, 0) (0, u)
    simp only [Prod.mk_add_mk, add_zero, zero_add] at hadd
    simp only [cotangentGeneratingTarget_snd_apply, cotangentGeneratingSource_snd_apply] at hw hu
    simp only [cotangentGeneratingTarget_snd_apply,
      fderiv_cotangentGeneratingTripleSum_apply hS hT hR, Prod.fst_zero, Prod.snd_zero,
      _root_.zero_apply]
    linarith

/-- The two intermediate cotangent points match exactly when `(a,b)` is a critical point of
`(a',b') ↦ S(q,a') + T(a',b') + R(b',Q)`. -/
theorem cotangentGeneratingTarget_eq_cotangentGeneratingSource_triple_iff
    {q : V} {a : W} {b : U} {Q : Z}
    (hS : DifferentiableAt ℝ S (q, a)) (hT : DifferentiableAt ℝ T (a, b))
    (hR : DifferentiableAt ℝ R (b, Q)) :
    cotangentGeneratingTarget S (q, a) = cotangentGeneratingSource T (a, b) ∧
        cotangentGeneratingTarget T (a, b) = cotangentGeneratingSource R (b, Q) ↔
      fderiv ℝ (fun p : W × U ↦ S (q, p.1) + T p + R (p.2, Q)) (a, b) = 0 := by
  have hF := differentiableAt_cotangentGeneratingTripleSum (x := ((q, Q), (a, b))) hS hT hR
  rw [← cotangentGeneratingTarget_tripleSum_snd_eq_zero_iff (x := ((q, Q), (a, b))) hS hT hR,
    cotangentGeneratingTarget_snd_eq_neg_fderiv_slice hF, neg_eq_zero]
  simp only [cotangentGeneratingTripleSum_def]

/-- Along a differentiable matched branch the internal derivatives cancel, leaving just the
two endpoint derivatives of the first and last generating functions. -/
theorem fderiv_cotangentGeneratingTripleSum_comp_graph_apply
    {c : V × Z → W × U} {y : V × Z}
    (hS : DifferentiableAt ℝ S (y.1, (c y).1)) (hT : DifferentiableAt ℝ T (c y))
    (hR : DifferentiableAt ℝ R ((c y).2, y.2)) (hc : DifferentiableAt ℝ c y)
    (h₁ : cotangentGeneratingTarget S (y.1, (c y).1) = cotangentGeneratingSource T (c y))
    (h₂ : cotangentGeneratingTarget T (c y) = cotangentGeneratingSource R ((c y).2, y.2))
    (v : V × Z) :
    fderiv ℝ (fun z ↦ cotangentGeneratingTripleSum S T R (z, c z)) y v =
      fderiv ℝ S (y.1, (c y).1) (v.1, 0) +
        fderiv ℝ R ((c y).2, y.2) (0, v.2) := by
  have hF := differentiableAt_cotangentGeneratingTripleSum (x := (y, c y)) hS hT hR
  have hzero : fderiv ℝ (fun z ↦ cotangentGeneratingTripleSum S T R (y, z)) (c y) = 0 := by
    simpa only [cotangentGeneratingTripleSum_def] using
      (cotangentGeneratingTarget_eq_cotangentGeneratingSource_triple_iff hS hT hR).1 ⟨h₁, h₂⟩
  rw [hF.hasFDerivAt.fderiv_comp_graph_eq_fderiv_slice_of_fderiv_right_eq_zero hc hzero,
    fderiv_slice_left hF, ContinuousLinearMap.comp_apply, inl_apply,
    fderiv_cotangentGeneratingTripleSum_apply hS hT hR]
  simp

/-- Along a differentiable matched branch, the critical value of the three-edge action has the
source covector of the first edge. -/
theorem cotangentGeneratingSource_cotangentGeneratingTripleSum_comp_graph
    {c : V × Z → W × U} {y : V × Z}
    (hS : DifferentiableAt ℝ S (y.1, (c y).1)) (hT : DifferentiableAt ℝ T (c y))
    (hR : DifferentiableAt ℝ R ((c y).2, y.2)) (hc : DifferentiableAt ℝ c y)
    (h₁ : cotangentGeneratingTarget S (y.1, (c y).1) = cotangentGeneratingSource T (c y))
    (h₂ : cotangentGeneratingTarget T (c y) = cotangentGeneratingSource R ((c y).2, y.2)) :
    cotangentGeneratingSource (fun z ↦ cotangentGeneratingTripleSum S T R (z, c z)) y =
      cotangentGeneratingSource S (y.1, (c y).1) := by
  apply Prod.ext (by simp)
  ext u
  simp [cotangentGeneratingSource_snd_apply,
    fderiv_cotangentGeneratingTripleSum_comp_graph_apply hS hT hR hc h₁ h₂, ← Prod.zero_eq_mk]

/-- Along a differentiable matched branch, the critical value of the three-edge action has the
target covector of the last edge. -/
theorem cotangentGeneratingTarget_cotangentGeneratingTripleSum_comp_graph
    {c : V × Z → W × U} {y : V × Z}
    (hS : DifferentiableAt ℝ S (y.1, (c y).1)) (hT : DifferentiableAt ℝ T (c y))
    (hR : DifferentiableAt ℝ R ((c y).2, y.2)) (hc : DifferentiableAt ℝ c y)
    (h₁ : cotangentGeneratingTarget S (y.1, (c y).1) = cotangentGeneratingSource T (c y))
    (h₂ : cotangentGeneratingTarget T (c y) = cotangentGeneratingSource R ((c y).2, y.2)) :
    cotangentGeneratingTarget (fun z ↦ cotangentGeneratingTripleSum S T R (z, c z)) y =
      cotangentGeneratingTarget R ((c y).2, y.2) := by
  apply Prod.ext (by simp)
  ext u
  simp [cotangentGeneratingTarget_snd_apply,
    fderiv_cotangentGeneratingTripleSum_comp_graph_apply hS hT hR hc h₁ h₂, ← Prod.zero_eq_mk]

private theorem grouped_cotangentGeneratingTarget_eq_iff {x : (V × Z) × (W × U)}
    (hS : DifferentiableAt ℝ S (x.1.1, x.2.1)) (hT : DifferentiableAt ℝ T x.2)
    (hR : DifferentiableAt ℝ R (x.2.2, x.1.2)) :
    cotangentGeneratingTarget (fun p : V × (W × U) ↦ S (p.1, p.2.1) + T p.2)
        (x.1.1, x.2) =
      cotangentGeneratingSource (fun p : (W × U) × Z ↦ R (p.1.2, p.2)) (x.2, x.1.2) ↔
      cotangentGeneratingTarget S (x.1.1, x.2.1) = cotangentGeneratingSource T x.2 ∧
      cotangentGeneratingTarget T x.2 = cotangentGeneratingSource R (x.2.2, x.1.2) := by
  have hL : DifferentiableAt ℝ (fun p : V × (W × U) ↦ S (p.1, p.2.1) + T p.2)
      (x.1.1, x.2) := (hS.comp (x.1.1, x.2)
    (differentiableAt_fst.prodMk differentiableAt_snd.fst)).add
      (hT.comp (x.1.1, x.2) differentiableAt_snd)
  have hM : DifferentiableAt ℝ (fun p : (W × U) × Z ↦ R (p.1.2, p.2))
      (x.2, x.1.2) := hR.comp (x.2, x.1.2) (differentiableAt_fst.snd.prodMk differentiableAt_snd)
  have h := cotangentGeneratingTarget_sum_snd_eq_zero_iff hL hM
  rw [← cotangentGeneratingTripleSum_eq_cotangentGeneratingSum] at h
  exact h.symm.trans (cotangentGeneratingTarget_tripleSum_snd_eq_zero_iff hS hT hR)

private theorem cotangentGeneratingSource_grouped {x : V × (W × U)}
    (hS : DifferentiableAt ℝ S (x.1, x.2.1)) (hT : DifferentiableAt ℝ T x.2) :
    cotangentGeneratingSource (fun p : V × (W × U) ↦ S (p.1, p.2.1) + T p.2) x =
      cotangentGeneratingSource S (x.1, x.2.1) := by
  have hd : fderiv ℝ (fun p : V × (W × U) ↦ S (p.1, p.2.1) + T p.2) x = _ :=
    ((hS.hasFDerivAt.comp x (hasFDerivAt_fst.prodMk hasFDerivAt_snd.fst)).add
      (hT.hasFDerivAt.comp x hasFDerivAt_snd)).fderiv
  refine Prod.ext (by simp) (ContinuousLinearMap.ext fun v ↦ ?_)
  simp [cotangentGeneratingSource_snd_apply, hd]

private theorem cotangentGeneratingTarget_grouped {x : (W × U) × Z}
    (hR : DifferentiableAt ℝ R (x.1.2, x.2)) :
    cotangentGeneratingTarget (fun p : (W × U) × Z ↦ R (p.1.2, p.2)) x =
      cotangentGeneratingTarget R (x.1.2, x.2) := by
  have hd : fderiv ℝ (fun p : (W × U) × Z ↦ R (p.1.2, p.2)) x = _ :=
    (hR.hasFDerivAt.comp x (hasFDerivAt_fst.snd.prodMk hasFDerivAt_snd)).fderiv
  refine Prod.ext (by simp) (ContinuousLinearMap.ext fun v ↦ ?_)
  simp [cotangentGeneratingTarget_snd_apply, hd]

/-- A linearized matched configuration with source variation `0` and target variation `δQ` has
internal negative Hessian given by the last edge's mixed Hessian applied to `δQ`. -/
private theorem cotangentLegendreHessian_cotangentGeneratingTripleSum_apply_of_fderiv_eq
    {x : (V × Z) × (W × U)}
    (hS : ContDiffAt ℝ 2 S (x.1.1, x.2.1)) (hT : ContDiffAt ℝ 2 T x.2)
    (hR : ContDiffAt ℝ 2 R (x.2.2, x.1.2)) {z : W × U} {δQ : Z}
    (h₁ : fderiv ℝ (cotangentGeneratingTarget S) (x.1.1, x.2.1) (0, z.1) =
      fderiv ℝ (cotangentGeneratingSource T) x.2 z)
    (h₂ : fderiv ℝ (cotangentGeneratingTarget T) x.2 z =
      fderiv ℝ (cotangentGeneratingSource R) (x.2.2, x.1.2) (z.2, δQ)) (e : W × U) :
    cotangentLegendreHessian (cotangentGeneratingTripleSum S T R) x z e =
      cotangentMixedHessian R (x.2.2, x.1.2) δQ e.2 := by
  have he₁ := congrArg (fun p : W × StrongDual ℝ W ↦ p.2 e.1) h₁
  have he₂ := congrArg (fun p : U × StrongDual ℝ U ↦ p.2 e.2) h₂
  simp only [fderiv_cotangentGeneratingTarget_apply
      (hS.hasFDerivAt_fderiv le_rfl).differentiableAt,
    fderiv_cotangentGeneratingSource_apply (hT.hasFDerivAt_fderiv le_rfl).differentiableAt,
    fderiv_cotangentGeneratingTarget_apply (hT.hasFDerivAt_fderiv le_rfl).differentiableAt,
    fderiv_cotangentGeneratingSource_apply (hR.hasFDerivAt_fderiv le_rfl).differentiableAt,
    _root_.neg_apply, ContinuousLinearMap.comp_apply, inl_apply, inr_apply] at he₁ he₂
  have hTe : fderiv ℝ (fderiv ℝ T) x.2 z e =
      fderiv ℝ (fderiv ℝ T) x.2 z (e.1, 0) + fderiv ℝ (fderiv ℝ T) x.2 z (0, e.2) := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have hRz : fderiv ℝ (fderiv ℝ R) (x.2.2, x.1.2) (z.2, δQ) (e.2, 0) =
      fderiv ℝ (fderiv ℝ R) (x.2.2, x.1.2) (z.2, 0) (e.2, 0) +
        fderiv ℝ (fderiv ℝ R) (x.2.2, x.1.2) (0, δQ) (e.2, 0) := by
    rw [← _root_.add_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  rw [cotangentLegendreHessian_cotangentGeneratingTripleSum_apply_apply hS hT hR,
    cotangentLegendreHessian_apply_apply, cotangentMixedHessian_apply_apply]
  linarith

/-- **The reduced mixed Hessian is nondegenerate.** A generating function for a differentiable
matched three-edge branch has invertible mixed Hessian if all three edges and the full internal
negative Hessian do. Each final variation determines the internal response through the three
edges, and the internal Hessian identifies that response with the derivative of the branch. The
local source and matching identities are supplied by `exists_cotangentGeneratingTripleComposition`;
no separate elimination at either internal position is required. -/
theorem isInvertible_cotangentMixedHessian_of_triple_relations
    {c : V × Z → W × U} {F : V × Z → ℝ} {y : V × Z}
    (hS : ContDiffAt ℝ 2 S (y.1, (c y).1)) (hT : ContDiffAt ℝ 2 T (c y))
    (hR : ContDiffAt ℝ 2 R ((c y).2, y.2)) (hF : DifferentiableAt ℝ (fderiv ℝ F) y)
    (hc : DifferentiableAt ℝ c y)
    (hH : (cotangentLegendreHessian (cotangentGeneratingTripleSum S T R) (y, c y)).IsInvertible)
    (hHS : (cotangentMixedHessian S (y.1, (c y).1)).IsInvertible)
    (hHT : (cotangentMixedHessian T (c y)).IsInvertible)
    (hHR : (cotangentMixedHessian R ((c y).2, y.2)).IsInvertible)
    (hsrc : cotangentGeneratingSource F =ᶠ[𝓝 y]
      fun z ↦ cotangentGeneratingSource S (z.1, (c z).1))
    (h₁ : (fun z ↦ cotangentGeneratingTarget S (z.1, (c z).1)) =ᶠ[𝓝 y]
      fun z ↦ cotangentGeneratingSource T (c z))
    (h₂ : (fun z ↦ cotangentGeneratingTarget T (c z)) =ᶠ[𝓝 y]
      fun z ↦ cotangentGeneratingSource R ((c z).2, z.2)) :
    (cotangentMixedHessian F y).IsInvertible := by
  have hS' := (hS.hasFDerivAt_fderiv le_rfl).differentiableAt
  have hT' := (hT.hasFDerivAt_fderiv le_rfl).differentiableAt
  have hR' := (hR.hasFDerivAt_fderiv le_rfl).differentiableAt
  have hE₁ : HasFDerivAt (fun z : V × Z ↦ (z.1, (c z).1))
      ((fst ℝ V Z).prod (fst ℝ W U ∘L fderiv ℝ c y)) y :=
    hasFDerivAt_fst.prodMk hc.hasFDerivAt.fst
  have hE₃ : HasFDerivAt (fun z : V × Z ↦ ((c z).2, z.2))
      ((snd ℝ W U ∘L fderiv ℝ c y).prod (snd ℝ V Z)) y :=
    hc.hasFDerivAt.snd.prodMk hasFDerivAt_snd
  have hDs := (hsrc.fderiv_eq (𝕜 := ℝ)).trans
    ((hasFDerivAt_cotangentGeneratingSource hS').differentiableAt.hasFDerivAt.comp y hE₁).fderiv
  have hD₁ := ((hasFDerivAt_cotangentGeneratingTarget hS').differentiableAt.hasFDerivAt.comp
    y hE₁).fderiv.symm.trans
    ((h₁.fderiv_eq (𝕜 := ℝ)).trans
      ((hasFDerivAt_cotangentGeneratingSource hT').differentiableAt.hasFDerivAt.comp
        y hc.hasFDerivAt).fderiv)
  have hD₂ := ((hasFDerivAt_cotangentGeneratingTarget hT').differentiableAt.hasFDerivAt.comp
    y hc.hasFDerivAt).fderiv.symm.trans
    ((h₂.fderiv_eq (𝕜 := ℝ)).trans
      ((hasFDerivAt_cotangentGeneratingSource hR').differentiableAt.hasFDerivAt.comp y hE₃).fderiv)
  -- The branch derivative solves the linearized matching equations for a final variation `δQ`.
  have hlin (δQ : Z) :
      fderiv ℝ (cotangentGeneratingTarget S) (y.1, (c y).1) (0, (fderiv ℝ c y (0, δQ)).1) =
          fderiv ℝ (cotangentGeneratingSource T) (c y) (fderiv ℝ c y (0, δQ)) ∧
        fderiv ℝ (cotangentGeneratingTarget T) (c y) (fderiv ℝ c y (0, δQ)) =
          fderiv ℝ (cotangentGeneratingSource R) ((c y).2, y.2)
            ((fderiv ℝ c y (0, δQ)).2, δQ) := by
    constructor
    · simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, coe_fst',
        coe_snd'] using congrArg (fun L ↦ L (0, δQ)) hD₁
    · simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, coe_fst',
        coe_snd'] using congrArg (fun L ↦ L (0, δQ)) hD₂
  obtain ⟨eT, heT⟩ := (isInvertible_fderiv_cotangentGeneratingSource_iff hT').2 hHT
  obtain ⟨eR, heR⟩ := (isInvertible_fderiv_cotangentGeneratingSource_iff hR').2 hHR
  have heT' (v : W × U) : eT v = fderiv ℝ (cotangentGeneratingSource T) (c y) v :=
    DFunLike.congr_fun heT v
  have heR' (v : U × Z) : eR v = fderiv ℝ (cotangentGeneratingSource R) ((c y).2, y.2) v :=
    DFunLike.congr_fun heR v
  -- The mixed Hessian of `F` factors through the response `K` of the first internal position.
  let K : Z →L[ℝ] W := fst ℝ W U ∘L fderiv ℝ c y ∘L inr ℝ V Z
  have hMF : cotangentMixedHessian F y = cotangentMixedHessian S (y.1, (c y).1) ∘L K := by
    ext δQ v
    simpa [K, hF, hS'] using congrArg (fun L ↦ (L (0, δQ)).2 v) hDs
  rw [hMF]
  refine hHS.comp (IsInvertible.of_inverse (g := snd ℝ U Z ∘L (eR.symm : _ →L[ℝ] U × Z) ∘L
    fderiv ℝ (cotangentGeneratingTarget T) (c y) ∘L (eT.symm : _ →L[ℝ] W × U) ∘L
    fderiv ℝ (cotangentGeneratingTarget S) (y.1, (c y).1) ∘L inr ℝ V W)
    (ContinuousLinearMap.ext fun δa ↦ ?_) (ContinuousLinearMap.ext fun δQ ↦ ?_))
  · -- Propagate `δa` through the middle and last edges, then use the internal Hessian.
    set z := eT.symm (fderiv ℝ (cotangentGeneratingTarget S) (y.1, (c y).1) (0, δa))
    have hz : fderiv ℝ (cotangentGeneratingSource T) (c y) z =
        fderiv ℝ (cotangentGeneratingTarget S) (y.1, (c y).1) (0, δa) := by
      rw [← heT', eT.apply_symm_apply]
    have hz₁ : z.1 = δa := by
      simpa [hT', hS'] using congrArg Prod.fst hz
    set p := eR.symm (fderiv ℝ (cotangentGeneratingTarget T) (c y) z)
    have hp : fderiv ℝ (cotangentGeneratingSource R) ((c y).2, y.2) p =
        fderiv ℝ (cotangentGeneratingTarget T) (c y) z := by
      rw [← heR', eR.apply_symm_apply]
    have hp₁ : p.1 = z.2 := by
      simpa [hT', hR'] using congrArg Prod.fst hp
    have hw : fderiv ℝ c y (0, p.2) = z := by
      refine hH.injective (ContinuousLinearMap.ext fun e ↦ ?_)
      rw [cotangentLegendreHessian_cotangentGeneratingTripleSum_apply_of_fderiv_eq (x := (y, c y))
          hS hT hR (hlin p.2).1 (hlin p.2).2 e,
        cotangentLegendreHessian_cotangentGeneratingTripleSum_apply_of_fderiv_eq (x := (y, c y))
          hS hT hR (z := z) (δQ := p.2) (by rw [hz₁, hz]) (by rw [← hp₁, Prod.mk.eta, hp]) e]
    simp only [K, ContinuousLinearMap.comp_apply, inr_apply, coe_fst', coe_snd',
      ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.id_apply]
    exact (congrArg Prod.fst hw).trans hz₁
  · -- A final variation is recovered from the response of the internal positions.
    obtain ⟨hA, hB⟩ := hlin δQ
    have h₁' : eT.symm (fderiv ℝ (cotangentGeneratingTarget S) (y.1, (c y).1)
        (0, (fderiv ℝ c y (0, δQ)).1)) = fderiv ℝ c y (0, δQ) := by
      rw [hA, ← heT', eT.symm_apply_apply]
    have h₂' : eR.symm (fderiv ℝ (cotangentGeneratingTarget T) (c y) (fderiv ℝ c y (0, δQ))) =
        ((fderiv ℝ c y (0, δQ)).2, δQ) := by
      rw [hB, ← heR', eR.symm_apply_apply]
    simp [K, h₁', h₂']

section Elimination

variable [CompleteSpace V] [CompleteSpace W] [CompleteSpace U] [CompleteSpace Z]
  {q : V} {a : W} {b : U} {Q : Z}

/-- **Simultaneous stationary elimination for three generating functions.** An invertible full
negative Hessian in `(a,b)` gives a locally unique branch of matched intermediate positions.
Evaluating the three-edge action on it gives a generating function whose endpoint covectors
are those of the first and last edges. For `C^(n+2)` inputs the branch and critical value are
`C^(n+1)` and `C^(n+2)`, respectively, including the smooth case. The set `D` is an open
neighborhood of the endpoints; uniqueness holds on a joint neighborhood of all four positions. -/
theorem exists_cotangentGeneratingTripleComposition {n : WithTop ℕ∞}
    (hS : ContDiffAt ℝ (n + 2) S (q, a)) (hT : ContDiffAt ℝ (n + 2) T (a, b))
    (hR : ContDiffAt ℝ (n + 2) R (b, Q))
    (h₁ : cotangentGeneratingTarget S (q, a) = cotangentGeneratingSource T (a, b))
    (h₂ : cotangentGeneratingTarget T (a, b) = cotangentGeneratingSource R (b, Q))
    (hH : (cotangentLegendreHessian (cotangentGeneratingTripleSum S T R)
      ((q, Q), (a, b))).IsInvertible) :
    ∃ (c : V × Z → W × U) (F : V × Z → ℝ) (D : Set (V × Z)),
      IsOpen D ∧ (q, Q) ∈ D ∧ c (q, Q) = (a, b) ∧
      (∀ y, F y = S (y.1, (c y).1) + T (c y) + R ((c y).2, y.2)) ∧
      ContDiffAt ℝ (n + 1) c (q, Q) ∧ ContDiffAt ℝ (n + 2) F (q, Q) ∧
      (∀ y ∈ D,
        cotangentGeneratingTarget S (y.1, (c y).1) = cotangentGeneratingSource T (c y) ∧
        cotangentGeneratingTarget T (c y) = cotangentGeneratingSource R ((c y).2, y.2) ∧
        cotangentGeneratingSource F y = cotangentGeneratingSource S (y.1, (c y).1) ∧
        cotangentGeneratingTarget F y = cotangentGeneratingTarget R ((c y).2, y.2)) ∧
      (∀ᶠ x in 𝓝 ((q, Q), (a, b)),
        (cotangentGeneratingTarget S (x.1.1, x.2.1) = cotangentGeneratingSource T x.2 ∧
          cotangentGeneratingTarget T x.2 = cotangentGeneratingSource R (x.2.2, x.1.2)) ↔
            c x.1 = x.2) := by
  let L : V × (W × U) → ℝ := fun p ↦ S (p.1, p.2.1) + T p.2
  let M : (W × U) × Z → ℝ := fun p ↦ R (p.1.2, p.2)
  have hL : ContDiffAt ℝ (n + 2) L (q, (a, b)) :=
    (hS.comp (q, (a, b)) (contDiffAt_fst.prodMk contDiffAt_snd.fst)).add
      (hT.comp (q, (a, b)) contDiffAt_snd)
  have hM : ContDiffAt ℝ (n + 2) M ((a, b), Q) :=
    hR.comp ((a, b), Q) (contDiffAt_fst.snd.prodMk contDiffAt_snd)
  have hmatch := (grouped_cotangentGeneratingTarget_eq_iff (x := ((q, Q), (a, b)))
    (hS.differentiableAt (by simp)) (hT.differentiableAt (by simp))
    (hR.differentiableAt (by simp))).2 ⟨h₁, h₂⟩
  rw [cotangentGeneratingTripleSum_eq_cotangentGeneratingSum] at hH
  -- Group both internal positions: this uses the full Hessian, not successive elimination.
  obtain ⟨c, F, D, hD, hDmem, hc₀, hvalue, hc, hF, hrel, huniq⟩ :=
    exists_cotangentGeneratingComposition hL hM hmatch hH
  have hs : ∀ᶠ x in 𝓝 ((q, Q), (a, b)),
      DifferentiableAt ℝ S (x.1.1, x.2.1) ∧ DifferentiableAt ℝ T x.2 ∧
        DifferentiableAt ℝ R (x.2.2, x.1.2) := by
    have hsc : ContinuousAt (fun x : (V × Z) × (W × U) ↦ (x.1.1, x.2.1))
        ((q, Q), (a, b)) := by fun_prop
    have hrc : ContinuousAt (fun x : (V × Z) × (W × U) ↦ (x.2.2, x.1.2))
        ((q, Q), (a, b)) := by fun_prop
    exact (hsc.eventually (hS.eventually_differentiableAt (by
        exact le_trans (by norm_num : (1 : WithTop ℕ∞) ≤ 2) le_add_self))).and
      ((continuousAt_snd.eventually (hT.eventually_differentiableAt (by
        exact le_trans (by norm_num : (1 : WithTop ℕ∞) ≤ 2) le_add_self))).and
        (hrc.eventually (hR.eventually_differentiableAt (by
        exact le_trans (by norm_num : (1 : WithTop ℕ∞) ≤ 2) le_add_self))))
  have hmatching : ∀ᶠ x in 𝓝 ((q, Q), (a, b)),
      (cotangentGeneratingTarget S (x.1.1, x.2.1) = cotangentGeneratingSource T x.2 ∧
        cotangentGeneratingTarget T x.2 = cotangentGeneratingSource R (x.2.2, x.1.2)) ↔
          c x.1 = x.2 := by
    filter_upwards [hs, huniq] with x hx hxu
    exact (grouped_cotangentGeneratingTarget_eq_iff hx.1 hx.2.1 hx.2.2).symm.trans hxu
  -- Read the grouped endpoint relations of the two-function elimination edge by edge.
  have hto : Tendsto (fun y ↦ (y, c y)) (𝓝 (q, Q)) (𝓝 ((q, Q), (a, b))) := by
    simpa only [hc₀, id_eq] using (continuousAt_id.prodMk hc.continuousAt).tendsto
  obtain ⟨E, hE, hopen, hmem⟩ :=
    mem_nhds_iff.1 (inter_mem (hD.mem_nhds hDmem) (hto.eventually hs))
  refine ⟨c, F, E, hopen, hmem, hc₀, hvalue, hc, hF, fun y hy ↦ ?_, hmatching⟩
  obtain ⟨hyD, hSy, hTy, hRy⟩ := hE hy
  obtain ⟨hm, hsrc, htgt⟩ := hrel y hyD
  obtain ⟨hm₁, hm₂⟩ := (grouped_cotangentGeneratingTarget_eq_iff (x := (y, c y)) hSy hTy hRy).1 hm
  exact ⟨hm₁, hm₂, hsrc.trans (cotangentGeneratingSource_grouped hSy hTy),
    htgt.trans (cotangentGeneratingTarget_grouped hRy)⟩

end Elimination

variable {q : V} {a : W} {b : U} {Q : Z}

/-- **Simultaneous elimination with invertible reduced mixed Hessian.** When `V` is complete and
the full internal Hessian and three edge mixed Hessians are invertible,
`C^(n+2)` inputs give a `C^(n+1)` branch and a `C^(n+2)` critical value with invertible mixed
Hessian, including `C²` inputs. The local relation has the source of the first edge and target
of the last edge. Its intermediate positions are unique near the chosen configuration. -/
theorem exists_cotangentGeneratingTripleComposition_isInvertible_cotangentMixedHessian
    [CompleteSpace V] {n : WithTop ℕ∞}
    (hS : ContDiffAt ℝ (n + 2) S (q, a)) (hT : ContDiffAt ℝ (n + 2) T (a, b))
    (hR : ContDiffAt ℝ (n + 2) R (b, Q))
    (h₁ : cotangentGeneratingTarget S (q, a) = cotangentGeneratingSource T (a, b))
    (h₂ : cotangentGeneratingTarget T (a, b) = cotangentGeneratingSource R (b, Q))
    (hH : (cotangentLegendreHessian (cotangentGeneratingTripleSum S T R)
      ((q, Q), (a, b))).IsInvertible)
    (hHS : (cotangentMixedHessian S (q, a)).IsInvertible)
    (hHT : (cotangentMixedHessian T (a, b)).IsInvertible)
    (hHR : (cotangentMixedHessian R (b, Q)).IsInvertible) :
    ∃ (c : V × Z → W × U) (F : V × Z → ℝ),
      c (q, Q) = (a, b) ∧
      (∀ y, F y = S (y.1, (c y).1) + T (c y) + R ((c y).2, y.2)) ∧
      ContDiffAt ℝ (n + 1) c (q, Q) ∧ ContDiffAt ℝ (n + 2) F (q, Q) ∧
      (cotangentMixedHessian F (q, Q)).IsInvertible ∧
      (∀ᶠ y in 𝓝 (q, Q),
        cotangentGeneratingTarget S (y.1, (c y).1) = cotangentGeneratingSource T (c y) ∧
        cotangentGeneratingTarget T (c y) = cotangentGeneratingSource R ((c y).2, y.2) ∧
        cotangentGeneratingSource F y = cotangentGeneratingSource S (y.1, (c y).1) ∧
        cotangentGeneratingTarget F y = cotangentGeneratingTarget R ((c y).2, y.2)) ∧
      (∀ᶠ x in 𝓝 ((q, Q), (a, b)),
        (cotangentGeneratingTarget S (x.1.1, x.2.1) = cotangentGeneratingSource T x.2 ∧
          cotangentGeneratingTarget T x.2 = cotangentGeneratingSource R (x.2.2, x.1.2)) ↔
            c x.1 = x.2) := by
  -- The edge mixed Hessians identify `W`, `U` and `Z` with dual spaces, which are complete.
  have : CompleteSpace W := by
    obtain ⟨e, -⟩ := hHS
    exact (completeSpace_congr (e := e.toEquiv) e.isUniformEmbedding).2 inferInstance
  have : CompleteSpace U := by
    obtain ⟨e, -⟩ := hHT
    exact (completeSpace_congr (e := e.toEquiv) e.isUniformEmbedding).2 inferInstance
  have : CompleteSpace Z := by
    obtain ⟨e, -⟩ := hHR
    exact (completeSpace_congr (e := e.toEquiv) e.isUniformEmbedding).2 inferInstance
  obtain ⟨c, F, D, hD, hmem, hc₀, hvalue, hc, hF, hrel, huniq⟩ :=
    exists_cotangentGeneratingTripleComposition hS hT hR h₁ h₂ hH
  have hnear : ∀ᶠ y in 𝓝 (q, Q),
      cotangentGeneratingTarget S (y.1, (c y).1) = cotangentGeneratingSource T (c y) ∧
      cotangentGeneratingTarget T (c y) = cotangentGeneratingSource R ((c y).2, y.2) ∧
      cotangentGeneratingSource F y = cotangentGeneratingSource S (y.1, (c y).1) ∧
      cotangentGeneratingTarget F y = cotangentGeneratingTarget R ((c y).2, y.2) :=
    eventually_of_mem (hD.mem_nhds hmem) fun y hy ↦ hrel y hy
  refine ⟨c, F, hc₀, hvalue, hc, hF, ?_, hnear, huniq⟩
  apply isInvertible_cotangentMixedHessian_of_triple_relations
    (c := c) (hF := (hF.hasFDerivAt_fderiv (by simp)).differentiableAt)
    (hc := hc.differentiableAt (by simp))
    (hsrc := hnear.mono fun _ h ↦ h.2.2.1)
    (h₁ := hnear.mono fun _ h ↦ h.1) (h₂ := hnear.mono fun _ h ↦ h.2.1)
  all_goals simp only [hc₀]
  · exact hS.of_le le_add_self
  · exact hT.of_le le_add_self
  · exact hR.of_le le_add_self
  · exact hH
  · exact hHS
  · exact hHT
  · exact hHR

end TauCeti
