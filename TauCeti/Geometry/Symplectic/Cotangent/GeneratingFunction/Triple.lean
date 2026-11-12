/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.Legendre
import TauCeti.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Calculus.ContDiff.Differentiable
import TauCeti.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ImplicitContDiff

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
along the selected branch. When all three edge mixed Hessians are invertible in finite dimensions,
so is the reduced mixed Hessian; thus the critical value generates a local canonical transformation.

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
    (R : U × Z → ℝ) (q : V) (a : W) (b : U) (Q : Z) :
    cotangentGeneratingTripleSum S T R ((q, Q), (a, b)) = S (q, a) + T (a, b) + R (b, Q) :=
  (rfl)

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
  have hF : DifferentiableAt ℝ (cotangentGeneratingTripleSum S T R) (y, c y) :=
    ((hS.comp (y, c y) (differentiableAt_fst.fst.prodMk differentiableAt_snd.fst)).add
      (hT.comp (y, c y) differentiableAt_snd)).add
        (hR.comp (y, c y) (differentiableAt_snd.snd.prodMk differentiableAt_fst.snd))
  have hzero : fderiv ℝ (fun a ↦ cotangentGeneratingTripleSum S T R (y, a)) (c y) = 0 := by
    rw [fderiv_slice_right hF]
    apply ContinuousLinearMap.ext
    intro a
    have ha := congrArg (fun p : StrongDual ℝ (W × U) ↦ p a)
      ((cotangentGeneratingTarget_tripleSum_snd_eq_zero_iff (x := (y, c y)) hS hT hR).2 ⟨h₁, h₂⟩)
    simpa only [cotangentGeneratingTarget_snd_apply, _root_.zero_apply,
      ContinuousLinearMap.comp_apply, inr_apply, neg_eq_zero] using ha
  rw [hF.hasFDerivAt.fderiv_comp_graph_eq_fderiv_slice_of_fderiv_right_eq_zero hc hzero,
    fderiv_slice_left hF, ContinuousLinearMap.comp_apply, inl_apply,
    fderiv_cotangentGeneratingTripleSum_apply hS hT hR]
  simp

/-- If three edges have invertible mixed Hessians, every differentiable matched branch whose
source covectors come from a generating function has an injective source differential. -/
private theorem injective_fderiv_cotangentGeneratingSource_of_triple_relations
    {c : V × Z → W × U} {F : V × Z → ℝ} {y : V × Z}
    (hS : ContDiffAt ℝ 2 S (y.1, (c y).1)) (hT : ContDiffAt ℝ 2 T (c y))
    (hR : ContDiffAt ℝ 2 R ((c y).2, y.2))
    (hc : DifferentiableAt ℝ c y)
    (hHS : (cotangentMixedHessian S (y.1, (c y).1)).IsInvertible)
    (hHT : (cotangentMixedHessian T (c y)).IsInvertible)
    (hHR : (cotangentMixedHessian R ((c y).2, y.2)).IsInvertible)
    (hsrc : cotangentGeneratingSource F =ᶠ[𝓝 y]
      fun z ↦ cotangentGeneratingSource S (z.1, (c z).1))
    (h₁ : (fun z ↦ cotangentGeneratingTarget S (z.1, (c z).1)) =ᶠ[𝓝 y]
      fun z ↦ cotangentGeneratingSource T (c z))
    (h₂ : (fun z ↦ cotangentGeneratingTarget T (c z)) =ᶠ[𝓝 y]
      fun z ↦ cotangentGeneratingSource R ((c z).2, z.2)) :
    Function.Injective (fderiv ℝ (cotangentGeneratingSource F) y) := by
  have hSd := (hS.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  have hTd := (hT.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  have hRd := (hR.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  have hE₁ : HasFDerivAt (fun z : V × Z ↦ (z.1, (c z).1))
      ((fst ℝ V Z).prod (fst ℝ W U ∘L fderiv ℝ c y)) y :=
    hasFDerivAt_fst.prodMk hc.hasFDerivAt.fst
  have hE₃ : HasFDerivAt (fun z : V × Z ↦ ((c z).2, z.2))
      ((snd ℝ W U ∘L fderiv ℝ c y).prod (snd ℝ V Z)) y :=
    hc.hasFDerivAt.snd.prodMk hasFDerivAt_snd
  have hDs := (hsrc.fderiv_eq (𝕜 := ℝ)).trans
    ((hasFDerivAt_cotangentGeneratingSource hSd).differentiableAt.hasFDerivAt.comp y hE₁).fderiv
  have hD₁ := ((hasFDerivAt_cotangentGeneratingTarget hSd).differentiableAt.hasFDerivAt.comp
    y hE₁).fderiv.symm.trans
    ((h₁.fderiv_eq (𝕜 := ℝ)).trans
      ((hasFDerivAt_cotangentGeneratingSource hTd).differentiableAt.hasFDerivAt.comp
        y hc.hasFDerivAt).fderiv)
  have hD₂ := ((hasFDerivAt_cotangentGeneratingTarget hTd).differentiableAt.hasFDerivAt.comp
    y hc.hasFDerivAt).fderiv.symm.trans
    ((h₂.fderiv_eq (𝕜 := ℝ)).trans
      ((hasFDerivAt_cotangentGeneratingSource hRd).differentiableAt.hasFDerivAt.comp y hE₃).fderiv)
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  -- A zero source variation propagates successively through all three edges.
  have hv₁ : (v.1, (fderiv ℝ c y v).1) = (0 : V × W) := by
    apply ((isInvertible_fderiv_cotangentGeneratingSource_iff hSd).2 hHS).injective
    simpa only [map_zero, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      coe_fst', coe_snd'] using (congrArg (fun L ↦ L v) hDs).symm.trans hv
  have hv₂ : fderiv ℝ c y v = 0 := by
    apply ((isInvertible_fderiv_cotangentGeneratingSource_iff hTd).2 hHT).injective
    have h := congrArg (fun L ↦ L v) hD₁
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, coe_fst',
      hv₁, map_zero] using h.symm
  have hv₃ : ((fderiv ℝ c y v).2, v.2) = (0 : U × Z) := by
    apply ((isInvertible_fderiv_cotangentGeneratingSource_iff hRd).2 hHR).injective
    have h := congrArg (fun L ↦ L v) hD₂
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, coe_snd',
      hv₂, map_zero, Prod.snd_zero] using h.symm
  exact Prod.ext (by simpa only [Prod.fst_zero] using congrArg Prod.fst hv₁)
    (by simpa only [Prod.snd_zero] using congrArg Prod.snd hv₃)

/-- **The reduced mixed Hessian is nondegenerate.** On finite-dimensional spaces, a `C²`
generating function for a differentiable matched three-edge branch has invertible mixed
Hessian if all three edges do. The local source and matching identities are the ones supplied
by `exists_cotangentGeneratingTripleComposition`; no separate elimination at either internal
position is required. -/
theorem isInvertible_cotangentMixedHessian_of_triple_relations
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] [FiniteDimensional ℝ U]
    [FiniteDimensional ℝ Z]
    {c : V × Z → W × U} {F : V × Z → ℝ} {y : V × Z}
    (hS : ContDiffAt ℝ 2 S (y.1, (c y).1)) (hT : ContDiffAt ℝ 2 T (c y))
    (hR : ContDiffAt ℝ 2 R ((c y).2, y.2)) (hF : ContDiffAt ℝ 2 F y)
    (hc : DifferentiableAt ℝ c y)
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
  have hinj := injective_fderiv_cotangentGeneratingSource_of_triple_relations
    hS hT hR hc hHS hHT hHR hsrc h₁ h₂
  have hFd := (hF.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  have hdim : Module.finrank ℝ Z = Module.finrank ℝ V := by
    obtain ⟨eS, _⟩ := hHS
    obtain ⟨eT, _⟩ := hHT
    obtain ⟨eR, _⟩ := hHR
    have hSW := eS.toLinearEquiv.finrank_eq
    have hTU := eT.toLinearEquiv.finrank_eq
    have hRZ := eR.toLinearEquiv.finrank_eq
    simp only [ContinuousLinearMap.dual_finrank_eq] at hSW hTU hRZ
    omega
  have hdim' : Module.finrank ℝ (V × Z) = Module.finrank ℝ (V × StrongDual ℝ V) := by
    simp [Module.finrank_prod, ContinuousLinearMap.dual_finrank_eq, hdim]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').mp hinj
  exact (isInvertible_fderiv_cotangentGeneratingSource_iff hFd).1
    ⟨ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.mpr hinj)
      (LinearMap.range_eq_top.mpr hsurj), rfl⟩

section Elimination

variable [CompleteSpace V] [CompleteSpace W] [CompleteSpace U] [CompleteSpace Z]
  {q : V} {a : W} {b : U} {Q : Z}

/-- **Simultaneous stationary elimination for three generating functions.** An invertible full
negative Hessian in `(a,b)` gives a locally unique branch of matched intermediate positions.
Evaluating the three-edge action on it gives a generating function whose endpoint covectors
are those of the first and last edges. For `C^(n+2)` inputs the branch and critical value are
`C^(n+1)`, including the smooth case. The set `D` is an open neighborhood of the endpoints;
the uniqueness assertion holds on a joint neighborhood of all four positions. -/
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
      ContDiffAt ℝ (n + 1) c (q, Q) ∧ ContDiffAt ℝ (n + 1) F (q, Q) ∧
      (∀ y ∈ D,
        cotangentGeneratingTarget S (y.1, (c y).1) = cotangentGeneratingSource T (c y) ∧
        cotangentGeneratingTarget T (c y) = cotangentGeneratingSource R ((c y).2, y.2) ∧
        cotangentGeneratingSource F y = cotangentGeneratingSource S (y.1, (c y).1) ∧
        cotangentGeneratingTarget F y = cotangentGeneratingTarget R ((c y).2, y.2)) ∧
      (∀ᶠ x in 𝓝 ((q, Q), (a, b)),
        (cotangentGeneratingTarget S (x.1.1, x.2.1) = cotangentGeneratingSource T x.2 ∧
          cotangentGeneratingTarget T x.2 = cotangentGeneratingSource R (x.2.2, x.1.2)) ↔
            c x.1 = x.2) := by
  let A := cotangentGeneratingTripleSum S T R
  have hA : ContDiffAt ℝ (n + 2) A ((q, Q), (a, b)) :=
    contDiffAt_cotangentGeneratingTripleSum hS hT hR
  have hA₂ : ContDiffAt ℝ 2 A ((q, Q), (a, b)) := hA.of_le (by simp)
  let G : (V × Z) × (W × U) → StrongDual ℝ (W × U) :=
    fun x ↦ (cotangentGeneratingTarget A x).2
  have hG : ContDiffAt ℝ (n + 1) G ((q, Q), (a, b)) :=
    (contDiffAt_cotangentGeneratingTarget (n := n + 1)
      (by convert hA using 1; norm_num [add_assoc])).snd
  have hz : G ((q, Q), (a, b)) = 0 :=
    (cotangentGeneratingTarget_tripleSum_snd_eq_zero_iff
      (hS.differentiableAt (by simp)) (hT.differentiableAt (by simp))
      (hR.differentiableAt (by simp))).2 ⟨h₁, h₂⟩
  have hGder := (hasFDerivAt_cotangentGeneratingTarget
    ((hA₂.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero)).snd.fderiv
  have hinv : (fderiv ℝ G ((q, Q), (a, b)) ∘L inr ℝ (V × Z) (W × U)).IsInvertible := by
    suffices heq : fderiv ℝ G ((q, Q), (a, b)) ∘L inr ℝ (V × Z) (W × U) =
        cotangentLegendreHessian (cotangentGeneratingTripleSum S T R) ((q, Q), (a, b)) by
      rwa [heq]
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simp only [G, hGder, ContinuousLinearMap.comp_apply, coe_snd',
      ContinuousLinearMap.prod_apply, _root_.neg_apply, precomp_apply, inr_apply,
      cotangentLegendreHessian_apply_apply]
    rfl
  -- The full internal Hessian solves for both positions at once.
  let c := hG.implicitFunction (by simp) hinv
  have hc₀ : c (q, Q) = (a, b) := hG.implicitFunction_apply_self (by simp) hinv
  have hc : ContDiffAt ℝ (n + 1) c (q, Q) := hG.contDiffAt_implicitFunction (by simp) hinv
  have hunique : ∀ᶠ x in 𝓝 ((q, Q), (a, b)), G x = 0 ↔ c x.1 = x.2 := by
    simpa only [hz] using hG.eventually_apply_eq_iff_implicitFunction (by simp) hinv
  let F : V × Z → ℝ := fun y ↦ A (y, c y)
  have hF : ContDiffAt ℝ (n + 1) F (q, Q) := by
    have hAc : ContDiffAt ℝ (n + 2) A ((q, Q), c (q, Q)) := by rwa [hc₀]
    exact (hAc.of_le (by gcongr; norm_num : n + 1 ≤ n + 2)).comp (q, Q)
      (contDiffAt_id.prodMk hc)
  have hs : ∀ᶠ x in 𝓝 ((q, Q), (a, b)),
      DifferentiableAt ℝ S (x.1.1, x.2.1) ∧ DifferentiableAt ℝ T x.2 ∧
        DifferentiableAt ℝ R (x.2.2, x.1.2) := by
    have hsc : ContinuousAt (fun x : (V × Z) × (W × U) ↦ (x.1.1, x.2.1))
        ((q, Q), (a, b)) := by fun_prop
    have hrc : ContinuousAt (fun x : (V × Z) × (W × U) ↦ (x.2.2, x.1.2))
        ((q, Q), (a, b)) := by fun_prop
    have hS₂ := hS.of_le (by simp : 2 ≤ n + 2)
    have hT₂ := hT.of_le (by simp : 2 ≤ n + 2)
    have hR₂ := hR.of_le (by simp : 2 ≤ n + 2)
    exact (hsc.eventually (hS₂.eventually_differentiableAt (by norm_num))).and
      ((continuousAt_snd.eventually (hT₂.eventually_differentiableAt (by norm_num))).and
        (hrc.eventually (hR₂.eventually_differentiableAt (by norm_num))))
  have hmatching : ∀ᶠ x in 𝓝 ((q, Q), (a, b)),
      (cotangentGeneratingTarget S (x.1.1, x.2.1) = cotangentGeneratingSource T x.2 ∧
        cotangentGeneratingTarget T x.2 = cotangentGeneratingSource R (x.2.2, x.1.2)) ↔
          c x.1 = x.2 := by
    filter_upwards [hunique, hs] with x hx hxs
    exact (cotangentGeneratingTarget_tripleSum_snd_eq_zero_iff hxs.1 hxs.2.1 hxs.2.2).symm.trans hx
  -- Along this branch all internal terms cancel in the derivative of the critical value.
  have hto : Tendsto (fun y ↦ (y, c y)) (𝓝 (q, Q)) (𝓝 ((q, Q), (a, b))) := by
    simpa only [hc₀, id_eq] using (continuousAt_id.prodMk hc.continuousAt).tendsto
  have hrelations : ∀ᶠ y in 𝓝 (q, Q),
      cotangentGeneratingTarget S (y.1, (c y).1) = cotangentGeneratingSource T (c y) ∧
      cotangentGeneratingTarget T (c y) = cotangentGeneratingSource R ((c y).2, y.2) ∧
      cotangentGeneratingSource F y = cotangentGeneratingSource S (y.1, (c y).1) ∧
      cotangentGeneratingTarget F y = cotangentGeneratingTarget R ((c y).2, y.2) := by
    filter_upwards [hto.eventually (hmatching.and hs),
      (hc.of_le (by simp : 1 ≤ n + 1)).eventually (by simp)] with y hy hcy
    obtain ⟨h₁y, h₂y⟩ := hy.1.2 rfl
    have hd := fderiv_cotangentGeneratingTripleSum_comp_graph_apply hy.2.1 hy.2.2.1 hy.2.2.2
      (hcy.differentiableAt (by simp)) h₁y h₂y
    refine ⟨h₁y, h₂y, ?_, ?_⟩
    · apply Prod.ext (by simp)
      ext v
      simp [cotangentGeneratingSource_snd_apply, F, A, hd, ← Prod.zero_eq_mk]
    · apply Prod.ext (by simp)
      ext v
      simp [cotangentGeneratingTarget_snd_apply, F, A, hd, ← Prod.zero_eq_mk]
  obtain ⟨D, hD, hopen, hmem⟩ := mem_nhds_iff.1 hrelations
  exact ⟨c, F, D, hopen, hmem, hc₀, fun _ ↦ rfl, hc, hF, fun y hy ↦ hD hy, hmatching⟩

end Elimination

variable {q : V} {a : W} {b : U} {Q : Z}

/-- **The three-edge critical value generates a local canonical transformation.** If the full
internal Hessian and the three edge mixed Hessians are invertible, simultaneous elimination
gives a critical-value generating function with invertible mixed Hessian. The resulting local
relation has exactly the source of the first edge and target of the last edge. Its intermediate
positions are unique near the chosen configuration. -/
theorem exists_cotangentGeneratingTripleComposition_of_isInvertible_mixedHessian
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] [FiniteDimensional ℝ U]
    [FiniteDimensional ℝ Z] {n : WithTop ℕ∞} (hn : 1 ≤ n)
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
      ContDiffAt ℝ (n + 1) c (q, Q) ∧ ContDiffAt ℝ (n + 1) F (q, Q) ∧
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
  obtain ⟨c, F, D, hD, hmem, hc₀, hvalue, hc, hF, hrel, huniq⟩ :=
    exists_cotangentGeneratingTripleComposition hS hT hR h₁ h₂ hH
  have hnear : ∀ᶠ y in 𝓝 (q, Q),
      cotangentGeneratingTarget S (y.1, (c y).1) = cotangentGeneratingSource T (c y) ∧
      cotangentGeneratingTarget T (c y) = cotangentGeneratingSource R ((c y).2, y.2) ∧
      cotangentGeneratingSource F y = cotangentGeneratingSource S (y.1, (c y).1) ∧
      cotangentGeneratingTarget F y = cotangentGeneratingTarget R ((c y).2, y.2) :=
    eventually_of_mem (hD.mem_nhds hmem) fun y hy ↦ hrel y hy
  have htwo : (2 : WithTop ℕ∞) ≤ n + 1 := by
    calc 2 = 1 + 1 := by norm_num
         _ ≤ n + 1 := by gcongr
  refine ⟨c, F, hc₀, hvalue, hc, hF, ?_, hnear, huniq⟩
  apply isInvertible_cotangentMixedHessian_of_triple_relations
    (c := c) (hF := hF.of_le htwo) (hc := hc.differentiableAt (by simp))
    (hsrc := hnear.mono fun _ h ↦ h.2.2.1)
    (h₁ := hnear.mono fun _ h ↦ h.1) (h₂ := hnear.mono fun _ h ↦ h.2.1)
  all_goals simp only [hc₀]
  · exact hS.of_le (by simp)
  · exact hT.of_le (by simp)
  · exact hR.of_le (by simp)
  · exact hHS
  · exact hHT
  · exact hHR

end TauCeti
