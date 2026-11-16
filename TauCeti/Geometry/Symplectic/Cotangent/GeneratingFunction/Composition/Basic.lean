/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.Legendre
import TauCeti.Analysis.Calculus.ContDiff.Differentiable
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.SecondDerivative
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Composition of generating functions

For generating functions `S(q, a)` and `T(a, Q)`, composition eliminates the intermediate
position `a` from `S(q, a) + T(a, Q)` by the stationary equation
`∂ₐS + ∂ₐT = 0`. This is precisely equality of the intermediate cotangent points, with
the convention `p = ∂qS`, `P = -∂QS`
(`cotangentGeneratingTarget_eq_cotangentGeneratingSource_iff`).

`exists_cotangentGeneratingComposition` constructs the local stationary branch when the
intermediate Hessian is invertible. The resulting generating function has the source of `S`
and the target of `T`. Its domain is an open neighborhood of the chosen outer positions;
uniqueness concerns stationary branches through the chosen intermediate position, not other
critical points elsewhere. The construction applies Mathlib’s smooth implicit function theorem
to the intermediate momentum, using `cotangentLegendreHessian` for its spatial derivative.
For `C^(n+2)` inputs the branch is `C^(n+1)`, and the resulting generating function keeps the
regularity `C^(n+2)` of the inputs, since its derivative is read off the covectors of `S` and `T`
along the branch.

`fderiv_fderiv_cotangentGeneratingSum_apply` splits the second derivative of the sum into those
of `S` and `T`; in particular the negative intermediate Hessian is the sum of the negative
`a`-Hessians of `S` and of `T` (`cotangentLegendreHessian_cotangentGeneratingSum_apply_apply`).

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

/-- The second derivative of `S(q, a) + T(a, Q)` in the variables `((q, Q), a)` is the sum of the
second derivatives of `S` and `T`, each read on its own pair of variables. -/
theorem fderiv_fderiv_cotangentGeneratingSum_apply {S : V × W → ℝ} {T : W × U → ℝ}
    {x : (V × U) × W} (hS : ContDiffAt ℝ 2 S (x.1.1, x.2)) (hT : ContDiffAt ℝ 2 T (x.2, x.1.2))
    (u v : (V × U) × W) :
    fderiv ℝ (fderiv ℝ (cotangentGeneratingSum S T)) x u v =
      fderiv ℝ (fderiv ℝ S) (x.1.1, x.2) (u.1.1, u.2) (v.1.1, v.2) +
        fderiv ℝ (fderiv ℝ T) (x.2, x.1.2) (u.2, u.1.2) (v.2, v.1.2) := by
  -- The two summands are `S` and `T` composed with continuous linear maps.
  let P₁ : (V × U) × W →L[ℝ] V × W := ((fst ℝ V U).comp (fst ℝ (V × U) W)).prod (snd ℝ (V × U) W)
  let P₂ : (V × U) × W →L[ℝ] W × U := (snd ℝ (V × U) W).prod ((snd ℝ V U).comp (fst ℝ (V × U) W))
  have hsum : cotangentGeneratingSum S T = (fun y ↦ (S ∘ P₁) y) + fun y ↦ (T ∘ P₂) y := by
    funext ⟨⟨_, _⟩, _⟩
    simp [P₁, P₂]
  -- At `x` the two projections read off the arguments of `S` and of `T`.
  have hP₁x : P₁ x = (x.1.1, x.2) := by simp [P₁]
  have hP₂x : P₂ x = (x.2, x.1.2) := by simp [P₂]
  have hS' : ContDiffAt ℝ 2 S (P₁ x) := hP₁x ▸ hS
  have hT' : ContDiffAt ℝ 2 T (P₂ x) := hP₂x ▸ hT
  have h₁ : ContDiffAt ℝ 2 (S ∘ P₁) x := hS'.comp x P₁.contDiff.contDiffAt
  have h₂ : ContDiffAt ℝ 2 (T ∘ P₂) x := hT'.comp x P₂.contDiff.contDiffAt
  -- Near `x` both summands are differentiable, so the first derivative splits.
  have hev : fderiv ℝ (cotangentGeneratingSum S T) =ᶠ[𝓝 x]
      fun y ↦ fderiv ℝ (S ∘ P₁) y + fderiv ℝ (T ∘ P₂) y := by
    filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with y hy₁ hy₂
    rw [hsum]
    exact fderiv_add (hy₁.differentiableAt two_ne_zero) (hy₂.differentiableAt two_ne_zero)
  have hd : HasFDerivAt (fun y ↦ fderiv ℝ (S ∘ P₁) y + fderiv ℝ (T ∘ P₂) y)
      (fderiv ℝ (fderiv ℝ (S ∘ P₁)) x + fderiv ℝ (fderiv ℝ (T ∘ P₂)) x) x :=
    (h₁.hasFDerivAt_fderiv le_rfl).add (h₂.hasFDerivAt_fderiv le_rfl)
  have hP₁ : fderiv ℝ P₁ = fun _ ↦ P₁ := funext fun _ ↦ P₁.fderiv
  have hP₂ : fderiv ℝ P₂ = fun _ ↦ P₂ := funext fun _ ↦ P₂.fderiv
  rw [hev.fderiv_eq, hd.fderiv, _root_.add_apply, _root_.add_apply,
    fderiv_fderiv_comp_apply hS' P₁.contDiff.contDiffAt,
    fderiv_fderiv_comp_apply hT' P₂.contDiff.contDiffAt, hP₁, hP₂, hP₁x, hP₂x]
  simp [P₁, P₂]

/-- The negative intermediate Hessian of `S(q, a) + T(a, Q)` is the sum of the negative
`a`-Hessians of `S` and of `T`. -/
theorem cotangentLegendreHessian_cotangentGeneratingSum_apply_apply
    {S : V × W → ℝ} {T : W × U → ℝ} {q : V} {a : W} {Q : U}
    (hS : ContDiffAt ℝ 2 S (q, a)) (hT : ContDiffAt ℝ 2 T (a, Q)) (c d : W) :
    cotangentLegendreHessian (cotangentGeneratingSum S T) ((q, Q), a) c d =
      -(fderiv ℝ (fderiv ℝ S) (q, a) (0, c) (0, d) +
        fderiv ℝ (fderiv ℝ T) (a, Q) (c, 0) (d, 0)) := by
  rw [cotangentLegendreHessian_apply_apply,
    fderiv_fderiv_cotangentGeneratingSum_apply (x := ((q, Q), a)) hS hT]
  simp

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

/-- The intermediate cotangent points of the two relations agree exactly when the intermediate
position is a critical point of `a ↦ S(q, a) + T(a, Q)`. -/
theorem cotangentGeneratingTarget_eq_cotangentGeneratingSource_iff
    {S : V × W → ℝ} {T : W × U → ℝ} {q : V} {a : W} {Q : U}
    (hS : DifferentiableAt ℝ S (q, a)) (hT : DifferentiableAt ℝ T (a, Q)) :
    cotangentGeneratingTarget S (q, a) = cotangentGeneratingSource T (a, Q) ↔
      fderiv ℝ (fun a' ↦ S (q, a') + T (a', Q)) a = 0 := by
  have hF : DifferentiableAt ℝ (cotangentGeneratingSum S T) ((q, Q), a) :=
    (hS.comp ((q, Q), a) (differentiableAt_fst.fst.prodMk differentiableAt_snd)).add
      (hT.comp ((q, Q), a) (differentiableAt_snd.prodMk differentiableAt_fst.snd))
  rw [← cotangentGeneratingTarget_sum_snd_eq_zero_iff (x := ((q, Q), a)) hS hT]
  have hslice := fderiv_slice_right hF
  simp only [cotangentGeneratingSum_apply] at hslice
  simp only [hslice, ContinuousLinearMap.ext_iff, cotangentGeneratingTarget_snd_apply,
    ContinuousLinearMap.comp_apply, inr_apply, _root_.zero_apply, neg_eq_zero]

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

private theorem eventually_cotangentGeneratingSum_comp_graph_relations
    {S : V × W → ℝ} {T : W × U → ℝ} {b : V × U → W}
    {q : V} {a : W} {Q : U}
    (hs : ∀ᶠ x in 𝓝 ((q, Q), a),
      DifferentiableAt ℝ S (x.1.1, x.2) ∧ DifferentiableAt ℝ T (x.2, x.1.2))
    (hb : ContDiffAt ℝ 1 b (q, Q)) (hb₀ : b (q, Q) = a)
    (hunique : ∀ᶠ x in 𝓝 ((q, Q), a),
      cotangentGeneratingTarget S (x.1.1, x.2) =
        cotangentGeneratingSource T (x.2, x.1.2) ↔ b x.1 = x.2) :
    ∀ᶠ y in 𝓝 (q, Q),
      cotangentGeneratingTarget S (y.1, b y) = cotangentGeneratingSource T (b y, y.2) ∧
      cotangentGeneratingSource (fun z ↦ cotangentGeneratingSum S T (z, b z)) y =
        cotangentGeneratingSource S (y.1, b y) ∧
      cotangentGeneratingTarget (fun z ↦ cotangentGeneratingSum S T (z, b z)) y =
        cotangentGeneratingTarget T (b y, y.2) := by
  have hto : Tendsto (fun y ↦ (y, b y)) (𝓝 (q, Q)) (𝓝 ((q, Q), a)) := by
    simpa only [hb₀, id_eq] using (continuousAt_id.prodMk hb.continuousAt).tendsto
  filter_upwards [hto.eventually (hunique.and hs), hb.eventually (by simp)] with y hy hby
  have hmatch := hy.1.2 rfl
  have hd := fderiv_cotangentGeneratingSum_comp_graph_apply hy.2.1 hy.2.2
    (hby.differentiableAt one_ne_zero) hmatch
  refine ⟨hmatch, ?_, ?_⟩
  · apply Prod.ext (by simp)
    ext u
    simp [cotangentGeneratingSource_snd_apply, hd, ← Prod.zero_eq_mk]
  · apply Prod.ext (by simp)
    ext u
    simp [cotangentGeneratingTarget_snd_apply, hd, ← Prod.zero_eq_mk]

/-- A function `R(q, Q)` whose source covector is that of `S` and whose target covector is that of
`T` along a `C^(n+1)` branch `b` is `C^(n+2)` when `S` and `T` are: its derivative is
`(δq, δQ) ↦ ∂_q S(q, b) δq + ∂_Q T(b, Q) δQ`, which is `C^(n+1)`. -/
private theorem contDiffAt_add_two_of_cotangentGeneratingSource_eq
    {S : V × W → ℝ} {T : W × U → ℝ} {b : V × U → W} {R : V × U → ℝ}
    {q : V} {a : W} {Q : U} {n : WithTop ℕ∞}
    (hS : ContDiffAt ℝ (n + 2) S (q, a)) (hT : ContDiffAt ℝ (n + 2) T (a, Q))
    (hb : ContDiffAt ℝ (n + 1) b (q, Q)) (hb₀ : b (q, Q) = a)
    (hR : ContDiffAt ℝ (n + 1) R (q, Q))
    (hrel : ∀ᶠ y in 𝓝 (q, Q),
      cotangentGeneratingSource R y = cotangentGeneratingSource S (y.1, b y) ∧
      cotangentGeneratingTarget R y = cotangentGeneratingTarget T (b y, y.2)) :
    ContDiffAt ℝ (n + 2) R (q, Q) := by
  -- The derivative of `R`, written through the source and target covectors of `S` and `T`.
  let R' : V × U → V × U →L[ℝ] ℝ := fun y ↦
    (cotangentGeneratingSource S (y.1, b y)).2 ∘L fst ℝ V U -
      (cotangentGeneratingTarget T (b y, y.2)).2 ∘L snd ℝ V U
  have hn : n + 2 = n + 1 + 1 := by rw [add_assoc, one_add_one_eq_two]
  have hS₁ : ContDiffAt ℝ (n + 1) (cotangentGeneratingSource S) (q, b (q, Q)) := by
    rw [hb₀]
    exact contDiffAt_cotangentGeneratingSource (hn ▸ hS)
  have hT₁ : ContDiffAt ℝ (n + 1) (cotangentGeneratingTarget T) (b (q, Q), Q) := by
    rw [hb₀]
    exact contDiffAt_cotangentGeneratingTarget (hn ▸ hT)
  have hR' : ContDiffAt ℝ (n + 1) R' (q, Q) :=
    ((hS₁.comp (q, Q) (contDiffAt_fst.prodMk hb)).snd.clm_comp contDiffAt_const).sub
      ((hT₁.comp (q, Q) (hb.prodMk contDiffAt_snd)).snd.clm_comp contDiffAt_const)
  -- Near `(q₀, Q₀)` the map `R'` is the derivative of `R`.
  have hderiv : ∃ D ∈ 𝓝 (q, Q), ∀ y ∈ D, HasFDerivAt R (R' y) y := by
    obtain ⟨D, hD, hDR⟩ := (hrel.and (hR.eventually_differentiableAt (by simp))).exists_mem
    refine ⟨D, hD, fun y hy ↦ ?_⟩
    obtain ⟨⟨hsrc, htgt⟩, hRy⟩ := hDR y hy
    have hd := hRy.hasFDerivAt
    convert hd using 1
    refine ContinuousLinearMap.ext fun u ↦ ?_
    have h₁ := congrArg (fun p ↦ p.2 u.1) hsrc
    have h₂ := congrArg (fun p ↦ p.2 u.2) htgt
    simp only [cotangentGeneratingSource_snd_apply, cotangentGeneratingTarget_snd_apply] at h₁ h₂
    simp only [R', _root_.sub_apply, ContinuousLinearMap.comp_apply, coe_fst', coe_snd',
      cotangentGeneratingSource_snd_apply, cotangentGeneratingTarget_snd_apply]
    rw [← h₁, ← h₂, sub_neg_eq_add, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  -- For infinite `n` the order `n + 2` is `n + 1`; for finite `n` integrate `R'` once.
  induction n using WithTop.recTopCoe with
  | top => simpa using hR
  | coe m =>
    induction m using ENat.recTopCoe with
    | top =>
      have h : ((⊤ : ℕ∞) : WithTop ℕ∞) + 2 = ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 := by norm_cast
      exact h ▸ hR
    | coe k =>
      have hk : ((k : ℕ∞) : WithTop ℕ∞) + 2 = ((k + 1 : ℕ) : WithTop ℕ∞) + 1 := by
        push_cast
        rw [add_assoc, one_add_one_eq_two]
      rw [hk]
      exact contDiffAt_succ_iff_hasFDerivAt.2 ⟨R', hderiv, by exact_mod_cast hR'⟩

section Elimination

variable [CompleteSpace V] [CompleteSpace W] [CompleteSpace U]
  {S : V × W → ℝ} {T : W × U → ℝ} {q : V} {a : W} {Q : U}

/-- **Composition by stationary elimination.** Near a matched pair of cotangent relations,
an invertible negative intermediate Hessian of `S(q,a) + T(a,Q)` gives a stationary
branch `b(q,Q)` and the generating function `R(q,Q) = S(q,b) + T(b,Q)` of their composition.
For `C^(n+2)` inputs the branch is `C^(n+1)` and the critical value is `C^(n+2)`, including the
smooth case.
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
      ContDiffAt ℝ (n + 1) b (q, Q) ∧ ContDiffAt ℝ (n + 2) R (q, Q) ∧
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
  have hunique : ∀ᶠ x in 𝓝 ((q, Q), a), G x = 0 ↔ b x.1 = x.2 := by
    simpa only [hz] using hG.eventually_apply_eq_iff_implicitFunction (by simp) hinv
  let R : V × U → ℝ := fun y ↦ F (y, b y)
  have hFat : ContDiffAt ℝ (n + 2) F ((q, Q), b (q, Q)) := hb₀ ▸ hF
  have hR : ContDiffAt ℝ (n + 1) R (q, Q) := by
    simpa only [R, Function.comp_def, id_eq] using
      (hFat.of_le (by gcongr; norm_num : n + 1 ≤ n + 2)).comp (q, Q)
        (contDiffAt_id.prodMk hb)
  have hg₁ : ContinuousAt (fun x : (V × U) × W ↦ (x.1.1, x.2)) ((q, Q), a) := by fun_prop
  have hg₂ : ContinuousAt (fun x : (V × U) × W ↦ (x.2, x.1.2)) ((q, Q), a) := by fun_prop
  have hs := (hg₁.eventually (hS₂.eventually_differentiableAt (by norm_num))).and
    (hg₂.eventually (hT₂.eventually_differentiableAt (by norm_num)))
  have hmatching : ∀ᶠ x in 𝓝 ((q, Q), a),
      cotangentGeneratingTarget S (x.1.1, x.2) =
        cotangentGeneratingSource T (x.2, x.1.2) ↔ b x.1 = x.2 := by
    filter_upwards [hunique, hs] with x hx hxs
    exact (cotangentGeneratingTarget_sum_snd_eq_zero_iff hxs.1 hxs.2).symm.trans hx
  -- Along the stationary branch, differentiation gives both endpoint covectors.
  have hrelations := eventually_cotangentGeneratingSum_comp_graph_relations hs
    (hb.of_le (by simp : (1 : WithTop ℕ∞) ≤ n + 1)) hb₀ hmatching
  have hR₂ := contDiffAt_add_two_of_cotangentGeneratingSource_eq hS hT hb hb₀ hR
    (hrelations.mono fun _ h ↦ h.2)
  obtain ⟨D, hD, hopen, hmem⟩ := mem_nhds_iff.1 hrelations
  exact ⟨b, R, D, hopen, hmem, hb₀, fun _ ↦ rfl, hb, hR₂, fun y hy ↦ hD hy, hmatching⟩

end Elimination

end TauCeti
