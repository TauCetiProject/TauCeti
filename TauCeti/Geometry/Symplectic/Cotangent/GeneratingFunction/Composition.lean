/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.Legendre
import TauCeti.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Composition of generating functions

For generating functions `S(q, a)` and `T(a, Q)`, composition eliminates the intermediate
position `a` from `S(q, a) + T(a, Q)` by the stationary equation
`∂ₐS + ∂ₐT = 0`. This is precisely equality of the intermediate cotangent points, with
the convention `p = ∂qS`, `P = -∂QS`.

`exists_cotangentGeneratingComposition` constructs the local stationary branch when the
intermediate Hessian is invertible. The resulting generating function has the source of `S`
and the target of `T`. Its domain is an open neighborhood of the chosen outer positions;
uniqueness concerns stationary branches through the chosen intermediate position, not other
critical points elsewhere. The construction applies Mathlib’s smooth implicit function theorem
to the intermediate momentum, using `cotangentLegendreHessian` for its spatial derivative.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition,
  Springer, 1989, §48 (composition of canonical transformations).
-/

public section

noncomputable section

open ContinuousLinearMap Filter
open scoped Topology

namespace TauCeti

variable {V W U : Type*}

/-- The sum `S(q,a) + T(a,Q)`, with outer positions `(q,Q)` as parameters and
intermediate position `a` as the variable to eliminate. -/
def cotangentGeneratingSum (S : V × W → ℝ) (T : W × U → ℝ) (x : (V × U) × W) : ℝ :=
  S (x.1.1, x.2) + T (x.2, x.1.2)

@[simp]
theorem cotangentGeneratingSum_apply (S : V × W → ℝ) (T : W × U → ℝ)
    (q : V) (Q : U) (a : W) :
    cotangentGeneratingSum S T ((q, Q), a) = S (q, a) + T (a, Q) :=
  (rfl)

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- Smoothness of the sum before stationary elimination. -/
theorem contDiffAt_cotangentGeneratingSum {S : V × W → ℝ} {T : W × U → ℝ}
    {x : (V × U) × W} {n : WithTop ℕ∞}
    (hS : ContDiffAt ℝ n S (x.1.1, x.2)) (hT : ContDiffAt ℝ n T (x.2, x.1.2)) :
    ContDiffAt ℝ n (cotangentGeneratingSum S T) x :=
  (hS.comp x (contDiffAt_fst.fst.prodMk contDiffAt_snd)).add
    (hT.comp x (contDiffAt_snd.prodMk contDiffAt_fst.snd))

/-- The differential of the sum, keeping all three position variations explicit. -/
theorem fderiv_cotangentGeneratingSum_apply {S : V × W → ℝ} {T : W × U → ℝ}
    {x : (V × U) × W} (hS : DifferentiableAt ℝ S (x.1.1, x.2))
    (hT : DifferentiableAt ℝ T (x.2, x.1.2)) (u : (V × U) × W) :
    fderiv ℝ (cotangentGeneratingSum S T) x u =
      fderiv ℝ S (x.1.1, x.2) (u.1.1, u.2) +
        fderiv ℝ T (x.2, x.1.2) (u.2, u.1.2) := by
  have hd := (hS.hasFDerivAt.comp x
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).fst.prodMk (hasFDerivAt_snd (𝕜 := ℝ)))).add
      (hT.hasFDerivAt.comp x
        ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).prodMk (hasFDerivAt_fst (𝕜 := ℝ)).snd))
  exact congrArg (fun L ↦ L u) hd.fderiv

/-- Zero intermediate momentum for the sum is equality of the intermediate
cotangent points of the two relations. -/
theorem cotangentGeneratingTarget_sum_snd_eq_zero_iff
    {S : V × W → ℝ} {T : W × U → ℝ} {x : (V × U) × W}
    (hS : DifferentiableAt ℝ S (x.1.1, x.2))
    (hT : DifferentiableAt ℝ T (x.2, x.1.2)) :
    (cotangentGeneratingTarget (cotangentGeneratingSum S T) x).2 = 0 ↔
      cotangentGeneratingTarget S (x.1.1, x.2) =
        cotangentGeneratingSource T (x.2, x.1.2) := by
  constructor
  · intro h
    apply Prod.ext (by simp)
    ext b
    have hb := congrArg (fun p : StrongDual ℝ W ↦ p b) h
    simp only [cotangentGeneratingTarget_snd_apply,
      fderiv_cotangentGeneratingSum_apply hS hT, _root_.zero_apply,
      cotangentGeneratingSource_snd_apply, Prod.fst_zero, Prod.snd_zero] at hb ⊢
    linarith
  · intro h
    ext b
    have hb := congrArg (fun p : W × StrongDual ℝ W ↦ p.2 b) h
    simp only [cotangentGeneratingTarget_snd_apply,
      fderiv_cotangentGeneratingSum_apply hS hT, _root_.zero_apply,
      cotangentGeneratingSource_snd_apply, Prod.fst_zero, Prod.snd_zero] at hb ⊢
    linarith

/-- Along a differentiable stationary branch, the intermediate derivatives cancel.
The differential of the critical value is the sum of the two outer derivatives. -/
theorem fderiv_cotangentGeneratingSum_comp_graph_apply
    {S : V × W → ℝ} {T : W × U → ℝ} {b : V × U → W} {y : V × U}
    (hS : DifferentiableAt ℝ S (y.1, b y)) (hT : DifferentiableAt ℝ T (b y, y.2))
    (hb : DifferentiableAt ℝ b y)
    (hmatch : cotangentGeneratingTarget S (y.1, b y) =
      cotangentGeneratingSource T (b y, y.2)) (u : V × U) :
    fderiv ℝ (fun z ↦ cotangentGeneratingSum S T (z, b z)) y u =
      fderiv ℝ S (y.1, b y) (u.1, 0) + fderiv ℝ T (b y, y.2) (0, u.2) := by
  have hF : DifferentiableAt ℝ (cotangentGeneratingSum S T) (y, b y) :=
    (hS.comp (y, b y) (differentiableAt_fst.fst.prodMk differentiableAt_snd)).add
      (hT.comp (y, b y) (differentiableAt_snd.prodMk differentiableAt_fst.snd))
  have hzero : fderiv ℝ (fun z ↦ cotangentGeneratingSum S T (y, z)) (b y) = 0 := by
    rw [fderiv_slice_right hF]
    ext z
    have hcrit := (cotangentGeneratingTarget_sum_snd_eq_zero_iff
      (x := (y, b y)) hS hT).2 hmatch
    have hh := congrArg (fun p : StrongDual ℝ W ↦ p z) hcrit
    simpa only [cotangentGeneratingTarget_snd_apply, _root_.zero_apply,
      ContinuousLinearMap.comp_apply, inr_apply, neg_eq_zero] using hh
  rw [hF.hasFDerivAt.fderiv_comp_graph_eq_fderiv_slice_of_fderiv_right_eq_zero hb hzero,
    fderiv_slice_left hF, ContinuousLinearMap.comp_apply, inl_apply,
    fderiv_cotangentGeneratingSum_apply hS hT]

section Elimination

variable [CompleteSpace V] [CompleteSpace W] [CompleteSpace U]
  {S : V × W → ℝ} {T : W × U → ℝ} {q : V} {a : W} {Q : U}

/-- **Composition by stationary elimination.** Near a matched pair of cotangent relations,
an invertible negative intermediate Hessian of `S(q,a) + T(a,Q)` gives a stationary
branch `b(q,Q)` and the generating function `R(q,Q) = S(q,b) + T(b,Q)` of their composition.
For `C^(n+2)` inputs the branch and critical value are `C^(n+1)`, including the smooth case.
The stationary equation characterizes this branch on a joint neighborhood of `((q,Q),a)`.

Only local smoothness is required. In particular, no assertion of a globally defined
canonical transformation or of a unique critical point outside this neighborhood is made. -/
theorem exists_cotangentGeneratingComposition {n : WithTop ℕ∞}
    (hS : ContDiffAt ℝ (n + 2) S (q, a)) (hT : ContDiffAt ℝ (n + 2) T (a, Q))
    (hmatch : cotangentGeneratingTarget S (q, a) = cotangentGeneratingSource T (a, Q))
    (hH : (cotangentLegendreHessian (cotangentGeneratingSum S T) ((q, Q), a)).IsInvertible) :
    ∃ (b : V × U → W) (R : V × U → ℝ) (D : Set (V × U)),
      IsOpen D ∧ (q, Q) ∈ D ∧ b (q, Q) = a ∧
      (∀ y, R y = S (y.1, b y) + T (b y, y.2)) ∧
      ContDiffAt ℝ (n + 1) b (q, Q) ∧ ContDiffAt ℝ (n + 1) R (q, Q) ∧
      (∀ y ∈ D,
        cotangentGeneratingTarget S (y.1, b y) = cotangentGeneratingSource T (b y, y.2) ∧
        cotangentGeneratingSource R y = cotangentGeneratingSource S (y.1, b y) ∧
        cotangentGeneratingTarget R y = cotangentGeneratingTarget T (b y, y.2)) ∧
      (∀ᶠ x in 𝓝 ((q, Q), a),
        cotangentGeneratingTarget S (x.1.1, x.2) =
          cotangentGeneratingSource T (x.2, x.1.2) ↔ b x.1 = x.2) := by
  let F := cotangentGeneratingSum S T
  have hS₂ : ContDiffAt ℝ 2 S (q, a) := hS.of_le (by simp)
  have hT₂ : ContDiffAt ℝ 2 T (a, Q) := hT.of_le (by simp)
  have hF : ContDiffAt ℝ (n + 2) F ((q, Q), a) := contDiffAt_cotangentGeneratingSum hS hT
  have hF₂ : ContDiffAt ℝ 2 F ((q, Q), a) := hF.of_le (by simp)
  let G : (V × U) × W → StrongDual ℝ W := fun x ↦ (cotangentGeneratingTarget F x).2
  have hG : ContDiffAt ℝ (n + 1) G ((q, Q), a) :=
    (contDiffAt_cotangentGeneratingTarget (n := n + 1)
      (by convert hF using 1; norm_num [add_assoc])).snd
  have hz : G ((q, Q), a) = 0 :=
    (cotangentGeneratingTarget_sum_snd_eq_zero_iff
      (hS₂.differentiableAt two_ne_zero) (hT₂.differentiableAt two_ne_zero)).2 hmatch
  have hGder := (hasFDerivAt_cotangentGeneratingTarget
    ((hF₂.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero)).snd.fderiv
  -- The negative intermediate Hessian is the spatial derivative of the matching equation.
  have hinv : (fderiv ℝ G ((q, Q), a) ∘L inr ℝ (V × U) W).IsInvertible := by
    convert hH using 1
    ext v w
    simp only [G, hGder, ContinuousLinearMap.comp_apply, coe_snd',
      ContinuousLinearMap.prod_apply, _root_.neg_apply, precomp_apply, inr_apply,
      cotangentLegendreHessian_apply_apply]
    rfl
  -- Solve the matching equation and retain its local uniqueness in both variables.
  let b := hG.implicitFunction (by simp) hinv
  have hb₀ : b (q, Q) = a := hG.implicitFunction_apply_self (by simp) hinv
  have hb : ContDiffAt ℝ (n + 1) b (q, Q) := hG.contDiffAt_implicitFunction (by simp) hinv
  have hcrit : ∀ᶠ y in 𝓝 (q, Q), G (y, b y) = 0 := by
    simpa only [hz] using hG.eventually_apply_implicitFunction (by simp) hinv
  have hunique : ∀ᶠ x in 𝓝 ((q, Q), a), G x = 0 ↔ b x.1 = x.2 := by
    simpa only [hz] using hG.eventually_apply_eq_iff_implicitFunction (by simp) hinv
  let R : V × U → ℝ := fun y ↦ F (y, b y)
  have hFat : ContDiffAt ℝ (n + 2) F ((q, Q), b (q, Q)) := by
    simpa only [hb₀] using hF
  have hR : ContDiffAt ℝ (n + 1) R (q, Q) := by
    simpa only [R, Function.comp_def, id_eq] using
      (hFat.of_le (by gcongr; norm_num : n + 1 ≤ n + 2)).comp (q, Q)
        (contDiffAt_id.prodMk hb)
  have hs : ∀ᶠ x in 𝓝 ((q, Q), a),
      DifferentiableAt ℝ S (x.1.1, x.2) ∧ DifferentiableAt ℝ T (x.2, x.1.2) := by
    have h₁ := ((continuousAt_fst (p := ((q, Q), a))).fst.prodMk continuousAt_snd).eventually
      (hS₂.eventually (by simp))
    have h₂ := ((continuousAt_snd (p := ((q, Q), a))).prodMk continuousAt_fst.snd).eventually
      (hT₂.eventually (by simp))
    exact (h₁.mono fun _ h ↦ h.differentiableAt two_ne_zero).and
      (h₂.mono fun _ h ↦ h.differentiableAt two_ne_zero)
  have hto : Tendsto (fun y ↦ (y, b y)) (𝓝 (q, Q)) (𝓝 ((q, Q), a)) := by
    simpa only [hb₀, id_eq] using (continuousAt_id.prodMk hb.continuousAt).tendsto
  -- Along the constructed branch, the critical-value derivative gives both endpoint covectors.
  have hrelations : ∀ᶠ y in 𝓝 (q, Q),
      cotangentGeneratingTarget S (y.1, b y) = cotangentGeneratingSource T (b y, y.2) ∧
      cotangentGeneratingSource R y = cotangentGeneratingSource S (y.1, b y) ∧
      cotangentGeneratingTarget R y = cotangentGeneratingTarget T (b y, y.2) := by
    filter_upwards [hcrit, hto.eventually hs,
      (hb.of_le (by simp : (1 : WithTop ℕ∞) ≤ n + 1)).eventually (by simp)] with y hcy hsy hby
    have hmatchy := (cotangentGeneratingTarget_sum_snd_eq_zero_iff
      (x := (y, b y)) hsy.1 hsy.2).1 hcy
    have hd := fderiv_cotangentGeneratingSum_comp_graph_apply hsy.1 hsy.2
      (hby.differentiableAt one_ne_zero) hmatchy
    refine ⟨hmatchy, ?_, ?_⟩
    · apply Prod.ext (by simp)
      ext u
      simp [cotangentGeneratingSource_snd_apply, R, F, hd, ← Prod.zero_eq_mk]
    · apply Prod.ext (by simp)
      ext u
      simp [cotangentGeneratingTarget_snd_apply, R, F, hd, ← Prod.zero_eq_mk]
  obtain ⟨D, hD, hopen, hmem⟩ := mem_nhds_iff.1 hrelations
  refine ⟨b, R, D, hopen, hmem, hb₀, fun _ ↦ rfl, hb, hR,
    fun y hy ↦ hD hy, ?_⟩
  filter_upwards [hunique, hs] with x hx hxs
  exact (cotangentGeneratingTarget_sum_snd_eq_zero_iff hxs.1 hxs.2).symm.trans hx

end Elimination

end TauCeti
