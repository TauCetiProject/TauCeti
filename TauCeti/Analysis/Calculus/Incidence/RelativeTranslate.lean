/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Incidence.FiniteDimensional
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.OpenPos
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Relative translation families and small transverse perturbations

Let `f : E → V` be a map into a real normed space and `β : E → ℝ` a scalar cutoff vanishing on a
set `C ⊆ E`. The **relative translation family**

  `TauCeti.relativeTranslate f β p x = f x + β x • p`

leaves `f` unchanged on `C`, varies linearly with `p` in every higher `C^k` norm on compact sets,
and connects `f` to `relativeTranslate f β p` via the straight-line homotopy
`t ↦ relativeTranslate f β (t • p)` fixing `C`.

Suppose now that `f`, `β`, and `j : W → V` are differentiable and that `fderiv ℝ β x = 0` whenever
`β x = 0` (for instance, whenever `β` is locally nonnegative near its zeros, since every zero is a
local minimum and `fderiv ℝ β x = 0` by Fermat's theorem). Consequently:
1. Where `β x ≠ 0`, differentiating `relativeTranslate f β p x` in the parameter `p` gives the
   surjective scaling `q ↦ β x • q` onto `V`.
2. Where `β x = 0`, we have `relativeTranslate f β p x = f x`, and the parameter derivative
   vanishes while the spatial derivative agrees with `fderiv ℝ f x`.

Therefore, if `f` is already transverse to `j` along the zero set `{x | β x = 0}` (in particular,
along `C` when `β x = 0 ↔ x ∈ C`), the incidence equation of
`(x, p) ↦ relativeTranslate f β p x` against `j` has surjective total derivative at every
incidence point `((x, y), p)` with `relativeTranslate f β p x = j y`.
Applying the finite-dimensional parametric transversality theorem from
`TauCeti.Analysis.Calculus.Incidence.FiniteDimensional` (under `C^n` smoothness above the
Morse--Sard threshold) then yields that almost every parameter
`p : V` (for additive Haar measure), and in particular arbitrarily small parameters `‖p‖ < r`,
makes `relativeTranslate f β p` transverse to `j` while agreeing with `f` on `C`. Combining this
with `IsOpen.exists_contDiff_support_eq` on `Cᶜ` constructs a smooth nonnegative cutoff with
`β x = 0 ↔ x ∈ C`, eliminating the external cutoff altogether for any closed set `C` in a
finite-dimensional real normed space.

## Main declarations

* `TauCeti.relativeTranslate`: the family `f x + β x • p`, defined with minimal algebraic
  typeclasses so that it applies unchanged to arbitrary source types (including manifolds).
* `TauCeti.fderiv_relativeTranslate_of_hasFDerivAt_zero`,
  `TauCeti.fderiv_relativeTranslate_snd_fst_of_hasFDerivAt_zero_of_eq_zero`, and the
  nonnegative-cutoff corollary `TauCeti.fderiv_relativeTranslate_of_eventually_nonneg_of_eq_zero`:
  at a point `x` where `β` has zero derivative (in particular at a zero of a locally nonnegative
  differentiable cutoff), `relativeTranslate f β p` has Fréchet derivative `fderiv ℝ f x`, and if
  also `β x = 0` then `(x', p') ↦ relativeTranslate f β p' x'` has Fréchet derivative
  `(fderiv ℝ f x).comp fst`.
* `TauCeti.exists_norm_iteratedFDeriv_relativeTranslate_sub_le`: uniform linear `O(‖p‖)` control of
  all derivatives up to order `k` of `relativeTranslate f β p - f` on compact sets.
* `TauCeti.surjective_fderiv_incidenceEquation_relativeTranslate_iff`: characterizes surjectivity of
  the total derivative of the incidence equation of `relativeTranslate f β` against `j` at
  `((x, y), p)` under differentiability at `x` and `y` and `β x = 0 → fderiv ℝ β x = 0`.
* `TauCeti.addHaar_setOf_not_isRegularIncidenceParameterOn_relativeTranslate_eq_zero`,
  `TauCeti.exists_forall_isRegularIncidenceParameterOn_relativeTranslate`,
  `TauCeti.exists_forall_isRegularIncidenceParameter_relativeTranslate`, and
  `TauCeti.exists_isRegularIncidenceParameter_relativeTranslate`: generic and arbitrarily small
  `C^n` relative transverse perturbations (localized on subsets `U i` under vanishing derivative of
  `β` at its zeros, or global for nonnegative cutoffs, against a countable family or a single map).
* `IsClosed.exists_forall_isRegularIncidenceParameter_relativeTranslate` and
  `IsClosed.exists_isRegularIncidenceParameter_relativeTranslate`: cutoff-free closed-set `C^n`
  relative transversality in finite dimensions, producing a single smooth cutoff `β` vanishing
  precisely on `C` that works for every radius `r > 0`.
* Concrete examples at the end of the file, including a counterexample for `f(x) = x ^ 2` and
  `β(x) = x ^ 2` demonstrating that transversality along `C` cannot be omitted even when `β`
  vanishes there.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2012, Chapter 6, Theorem 6.36 (Transversality Homotopy / Extension Theorem).
* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 3, Theorem 2.1.
-/

public section

open Filter Function MeasureTheory MeasureTheory.Measure Metric Module Set
open scoped ContDiff Topology

namespace TauCeti

section Algebraic

/-- The relative translation `f x + β x • p` of `f : E → V` in direction `p : V` modulated by a
cutoff `β : E → ℝ`. No topological or norm structure is assumed on `E`, so this definition applies
unchanged when `E` is a manifold or arbitrary set. -/
def relativeTranslate {E V : Type*} [Add V] [SMul ℝ V]
    (f : E → V) (β : E → ℝ) (p : V) (x : E) : V :=
  f x + β x • p

/-- Function-level unfolding of `TauCeti.relativeTranslate f β p`. -/
theorem relativeTranslate_def {E V : Type*} [Add V] [SMul ℝ V]
    (f : E → V) (β : E → ℝ) (p : V) :
    relativeTranslate f β p = fun x ↦ f x + β x • p :=
  (rfl)

/-- Pointwise evaluation of `TauCeti.relativeTranslate`. -/
@[simp, grind =]
theorem relativeTranslate_apply {E V : Type*} [Add V] [SMul ℝ V]
    (f : E → V) (β : E → ℝ) (p : V) (x : E) :
    relativeTranslate f β p x = f x + β x • p :=
  (rfl)

/-- Relative translation by the zero parameter is the identity on `f`. -/
@[simp]
theorem relativeTranslate_zero_right {E V : Type*} [AddZeroClass V] [SMulZeroClass ℝ V]
    (f : E → V) (β : E → ℝ) :
    relativeTranslate f β 0 = f := by
  ext x
  simp [relativeTranslate]

/-- Relative translation with the identically zero cutoff is the identity on `f`. -/
@[simp]
theorem relativeTranslate_zero_cutoff {E V : Type*} [AddZeroClass V] [SMulWithZero ℝ V]
    (f : E → V) (p : V) :
    relativeTranslate f 0 p = f := by
  ext x
  simp [relativeTranslate]

/-- At any point where the cutoff vanishes, `relativeTranslate f β p` agrees with `f`. -/
theorem relativeTranslate_apply_of_eq_zero {E V : Type*} [AddZeroClass V] [SMulWithZero ℝ V]
    {f : E → V} {β : E → ℝ} (p : V) {x : E} (hβ : β x = 0) :
    relativeTranslate f β p x = f x := by
  simp [relativeTranslate, hβ]

/-- `relativeTranslate f β p` agrees with `f` on any set `C` where `β` vanishes. -/
theorem eqOn_relativeTranslate_of_eq_zero {E V : Type*} [AddZeroClass V] [SMulWithZero ℝ V]
    {f : E → V} {β : E → ℝ} {C : Set E} (p : V) (hC : ∀ x ∈ C, β x = 0) :
    EqOn (relativeTranslate f β p) f C :=
  fun _ hx ↦ relativeTranslate_apply_of_eq_zero p (hC _ hx)

/-- The pointwise increment `relativeTranslate f β p x - f x` is `β x • p`. -/
theorem relativeTranslate_sub_self {E V : Type*} [AddCommGroup V] [SMul ℝ V]
    (f : E → V) (β : E → ℝ) (p : V) (x : E) :
    relativeTranslate f β p x - f x = β x • p :=
  add_sub_cancel_left (f x) (β x • p)

/-- Iterating relative translations with the same cutoff adds the parameters. -/
@[simp]
theorem relativeTranslate_relativeTranslate {E V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : E → V) (β : E → ℝ) (p q : V) :
    relativeTranslate (relativeTranslate f β p) β q = relativeTranslate f β (p + q) := by
  ext x
  simp [relativeTranslate, smul_add, add_assoc]

/-- Pointwise evaluation of the straight-line affine homotopy between `f x` and
`relativeTranslate f β p x` at time `t : ℝ`. -/
theorem lineMap_relativeTranslate_apply {E V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : E → V) (β : E → ℝ) (p : V) (x : E) (t : ℝ) :
    AffineMap.lineMap (f x) (relativeTranslate f β p x) t =
      relativeTranslate f β (t • p) x := by
  rw [AffineMap.lineMap_apply_module', relativeTranslate_sub_self, smul_comm, add_comm,
    ← relativeTranslate_apply]

/-- The straight-line affine homotopy between `f` and `relativeTranslate f β p` at time `t : ℝ` is
`relativeTranslate f β (t • p)`, which therefore also fixes `f` wherever `β` vanishes. -/
@[simp]
theorem lineMap_relativeTranslate {E V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : E → V) (β : E → ℝ) (p : V) (t : ℝ) :
    AffineMap.lineMap f (relativeTranslate f β p) t = relativeTranslate f β (t • p) := by
  ext x
  simpa [AffineMap.lineMap_apply_module'] using lineMap_relativeTranslate_apply f β p x t

end Algebraic

section Calculus

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Joint `C^n` smoothness at `(x, p)` of `(x', p') ↦ relativeTranslate f β p' x'`. -/
theorem contDiffAt_relativeTranslate_snd_fst {f : E → V} {β : E → ℝ} {n : ℕ∞ω} {x : E} {p : V}
    (hf : ContDiffAt ℝ n f x) (hβ : ContDiffAt ℝ n β x) :
    ContDiffAt ℝ n (fun z : E × V ↦ relativeTranslate f β z.2 z.1) (x, p) :=
  (hf.comp (x, p) contDiffAt_fst).add ((hβ.comp (x, p) contDiffAt_fst).smul contDiffAt_snd)

/-- Global joint `C^n` smoothness of `(x, p) ↦ relativeTranslate f β p x`. -/
theorem contDiff_relativeTranslate_snd_fst {f : E → V} {β : E → ℝ} {n : ℕ∞ω}
    (hf : ContDiff ℝ n f) (hβ : ContDiff ℝ n β) :
    ContDiff ℝ n (fun z : E × V ↦ relativeTranslate f β z.2 z.1) :=
  (hf.comp contDiff_fst).add ((hβ.comp contDiff_fst).smul contDiff_snd)

/-- Pointwise `C^n` smoothness of the fixed-parameter map `relativeTranslate f β p`. -/
theorem contDiffAt_relativeTranslate {f : E → V} {β : E → ℝ} {n : ℕ∞ω} {x : E}
    (hf : ContDiffAt ℝ n f x) (hβ : ContDiffAt ℝ n β x) (p : V) :
    ContDiffAt ℝ n (relativeTranslate f β p) x :=
  hf.add (hβ.smul contDiffAt_const)

/-- Global `C^n` smoothness of the fixed-parameter map `relativeTranslate f β p`. -/
theorem contDiff_relativeTranslate {f : E → V} {β : E → ℝ} {n : ℕ∞ω}
    (hf : ContDiff ℝ n f) (hβ : ContDiff ℝ n β) (p : V) :
    ContDiff ℝ n (relativeTranslate f β p) :=
  hf.add (hβ.smul contDiff_const)

/-- Total Fréchet derivative of `(x', p') ↦ relativeTranslate f β p' x'` at `(x, p)`. -/
theorem hasFDerivAt_relativeTranslate_snd_fst {f : E → V} {β : E → ℝ}
    {Df : E →L[ℝ] V} {Dβ : E →L[ℝ] ℝ} {x : E} (hf : HasFDerivAt f Df x)
    (hβ : HasFDerivAt β Dβ x) (p : V) :
    HasFDerivAt (fun z : E × V ↦ relativeTranslate f β z.2 z.1)
      (Df.comp (ContinuousLinearMap.fst ℝ E V) +
        (Dβ.comp (ContinuousLinearMap.fst ℝ E V)).smulRight p +
        β x • ContinuousLinearMap.snd ℝ E V) (x, p) := by
  have hf1 : HasFDerivAt (f ∘ Prod.fst) (Df.comp (ContinuousLinearMap.fst ℝ E V)) (x, p) :=
    HasFDerivAt.comp (x, p) hf hasFDerivAt_fst
  have hβ1 : HasFDerivAt (β ∘ Prod.fst) (Dβ.comp (ContinuousLinearMap.fst ℝ E V)) (x, p) :=
    HasFDerivAt.comp (x, p) hβ hasFDerivAt_fst
  refine (hf1.add (hβ1.smul hasFDerivAt_snd)).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun ⟨u, q⟩ ↦ ?_
  simp [add_assoc, add_left_comm, add_comm]

/-- Joint differentiability at `(x, p)` of `(x', p') ↦ relativeTranslate f β p' x'`. -/
theorem differentiableAt_relativeTranslate_snd_fst {f : E → V} {β : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hβ : DifferentiableAt ℝ β x) (p : V) :
    DifferentiableAt ℝ (fun z : E × V ↦ relativeTranslate f β z.2 z.1) (x, p) :=
  (hasFDerivAt_relativeTranslate_snd_fst hf.hasFDerivAt hβ.hasFDerivAt p).differentiableAt

/-- Global joint differentiability of `(x, p) ↦ relativeTranslate f β p x`. -/
theorem differentiable_relativeTranslate_snd_fst {f : E → V} {β : E → ℝ}
    (hf : Differentiable ℝ f) (hβ : Differentiable ℝ β) :
    Differentiable ℝ (fun z : E × V ↦ relativeTranslate f β z.2 z.1) :=
  fun ⟨x, p⟩ ↦ differentiableAt_relativeTranslate_snd_fst (hf x) (hβ x) p

/-- Total Fréchet derivative of `(x', p') ↦ relativeTranslate f β p' x'` at `(x, p)` as a
continuous linear map. -/
theorem fderiv_relativeTranslate_snd_fst {f : E → V} {β : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hβ : DifferentiableAt ℝ β x) (p : V) :
    fderiv ℝ (fun z : E × V ↦ relativeTranslate f β z.2 z.1) (x, p) =
      (fderiv ℝ f x).comp (ContinuousLinearMap.fst ℝ E V) +
        ((fderiv ℝ β x).comp (ContinuousLinearMap.fst ℝ E V)).smulRight p +
        β x • ContinuousLinearMap.snd ℝ E V :=
  (hasFDerivAt_relativeTranslate_snd_fst hf.hasFDerivAt hβ.hasFDerivAt p).fderiv

/-- Action of `fderiv ℝ (fun z : E × V ↦ relativeTranslate f β z.2 z.1) (x, p)` on `(u, q)`. -/
theorem fderiv_relativeTranslate_snd_fst_apply {f : E → V} {β : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hβ : DifferentiableAt ℝ β x) (p : V) (u : E) (q : V) :
    fderiv ℝ (fun z : E × V ↦ relativeTranslate f β z.2 z.1) (x, p) (u, q) =
      fderiv ℝ f x u + fderiv ℝ β x u • p + β x • q := by
  rw [fderiv_relativeTranslate_snd_fst hf hβ p]
  simp [add_assoc]

/-- When the cutoff `β` is differentiable at `x`, `relativeTranslate f β p` is differentiable at
`x` if and only if `f` is differentiable at `x`. -/
theorem differentiableAt_relativeTranslate_iff {f : E → V} {β : E → ℝ} {x : E}
    (hβ : DifferentiableAt ℝ β x) (p : V) :
    DifferentiableAt ℝ (relativeTranslate f β p) x ↔ DifferentiableAt ℝ f x := by
  rw [relativeTranslate_def, (hβ.smul_const p).fun_add_iff_left]

/-- Pointwise differentiability of the fixed-parameter slice `relativeTranslate f β p` at `x`. -/
theorem differentiableAt_relativeTranslate {f : E → V} {β : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hβ : DifferentiableAt ℝ β x) (p : V) :
    DifferentiableAt ℝ (relativeTranslate f β p) x :=
  (differentiableAt_relativeTranslate_iff hβ p).2 hf

/-- Global differentiability of the fixed-parameter slice `relativeTranslate f β p`. -/
theorem differentiable_relativeTranslate {f : E → V} {β : E → ℝ}
    (hf : Differentiable ℝ f) (hβ : Differentiable ℝ β) (p : V) :
    Differentiable ℝ (relativeTranslate f β p) :=
  fun x ↦ differentiableAt_relativeTranslate (hf x) (hβ x) p

/-- Fréchet derivative of the fixed-parameter slice `relativeTranslate f β p` at `x`. -/
theorem hasFDerivAt_relativeTranslate {f : E → V} {β : E → ℝ}
    {Df : E →L[ℝ] V} {Dβ : E →L[ℝ] ℝ} {x : E}
    (hf : HasFDerivAt f Df x) (hβ : HasFDerivAt β Dβ x) (p : V) :
    HasFDerivAt (relativeTranslate f β p) (Df + Dβ.smulRight p) x :=
  hf.add (hβ.smul_const p)

/-- Fréchet derivative of the fixed-parameter slice `relativeTranslate f β p` at `x` as a
continuous linear map. -/
theorem fderiv_relativeTranslate {f : E → V} {β : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hβ : DifferentiableAt ℝ β x) (p : V) :
    fderiv ℝ (relativeTranslate f β p) x =
      fderiv ℝ f x + (fderiv ℝ β x).smulRight p :=
  (hasFDerivAt_relativeTranslate hf.hasFDerivAt hβ.hasFDerivAt p).fderiv

/-- At a point `x` where `β` has zero Fréchet derivative, if `f` has Fréchet derivative `Df` at
`x`, then `relativeTranslate f β p` also has Fréchet derivative `Df` at `x`. -/
theorem hasFDerivAt_relativeTranslate_of_hasFDerivAt_zero {f : E → V} {β : E → ℝ}
    {Df : E →L[ℝ] V} {x : E} (hf : HasFDerivAt f Df x) (hβ : HasFDerivAt β (0 : E →L[ℝ] ℝ) x)
    (p : V) :
    HasFDerivAt (relativeTranslate f β p) Df x := by
  simpa using hasFDerivAt_relativeTranslate hf hβ p

/-- At a point `x` where `β` has zero Fréchet derivative, the Fréchet derivative of
`relativeTranslate f β p` equals `fderiv ℝ f x` (without assuming `f` is differentiable at `x`). -/
theorem fderiv_relativeTranslate_of_hasFDerivAt_zero {f : E → V} {β : E → ℝ} {x : E}
    (hβ : HasFDerivAt β (0 : E →L[ℝ] ℝ) x) (p : V) :
    fderiv ℝ (relativeTranslate f β p) x = fderiv ℝ f x := by
  by_cases hf : DifferentiableAt ℝ f x
  · exact (hasFDerivAt_relativeTranslate_of_hasFDerivAt_zero hf.hasFDerivAt hβ p).fderiv
  · have hnot : ¬ DifferentiableAt ℝ (relativeTranslate f β p) x :=
      mt (differentiableAt_relativeTranslate_iff hβ.differentiableAt p).1 hf
    rw [fderiv_zero_of_not_differentiableAt hnot, fderiv_zero_of_not_differentiableAt hf]

/-- At a zero `x` of `β` where `β` also has zero Fréchet derivative, if `f` has Fréchet derivative
`Df` at `x`, then `(x', p') ↦ relativeTranslate f β p' x'` has Fréchet derivative `Df.comp fst` at
`(x, p)`. -/
theorem hasFDerivAt_relativeTranslate_snd_fst_of_hasFDerivAt_zero_of_eq_zero
    {f : E → V} {β : E → ℝ} {Df : E →L[ℝ] V} {x : E}
    (hf : HasFDerivAt f Df x) (hβ : HasFDerivAt β (0 : E →L[ℝ] ℝ) x) (hx : β x = 0) (p : V) :
    HasFDerivAt (fun z : E × V ↦ relativeTranslate f β z.2 z.1)
      (Df.comp (ContinuousLinearMap.fst ℝ E V)) (x, p) := by
  simpa [hx] using hasFDerivAt_relativeTranslate_snd_fst hf hβ p

/-- At a zero `x` of `β` where `β` also has zero Fréchet derivative, the joint Fréchet derivative
of `(x', p') ↦ relativeTranslate f β p' x'` at `(x, p)` kills the parameter variation and reduces
to `(fderiv ℝ f x).comp fst` (without assuming `f` is differentiable at `x`). -/
theorem fderiv_relativeTranslate_snd_fst_of_hasFDerivAt_zero_of_eq_zero
    {f : E → V} {β : E → ℝ} {x : E}
    (hβ : HasFDerivAt β (0 : E →L[ℝ] ℝ) x) (hx : β x = 0) (p : V) :
    fderiv ℝ (fun z : E × V ↦ relativeTranslate f β z.2 z.1) (x, p) =
      (fderiv ℝ f x).comp (ContinuousLinearMap.fst ℝ E V) := by
  by_cases hf : DifferentiableAt ℝ f x
  · exact (hasFDerivAt_relativeTranslate_snd_fst_of_hasFDerivAt_zero_of_eq_zero
      hf.hasFDerivAt hβ hx p).fderiv
  · have hnot : ¬ DifferentiableAt ℝ (fun z : E × V ↦ relativeTranslate f β z.2 z.1) (x, p) :=
      fun hFd ↦ hf ((differentiableAt_relativeTranslate_iff hβ.differentiableAt p).1
        hFd.hasFDerivAt_slice_fst.differentiableAt)
    rw [fderiv_zero_of_not_differentiableAt hnot, fderiv_zero_of_not_differentiableAt hf,
      ContinuousLinearMap.zero_comp]

/-- At a zero `x` of a locally nonnegative differentiable cutoff `β`, the Fréchet derivative of
`relativeTranslate f β p` equals `fderiv ℝ f x` (without assuming `f` is differentiable at `x`). -/
theorem fderiv_relativeTranslate_of_eventually_nonneg_of_eq_zero {f : E → V} {β : E → ℝ} {x : E}
    (hβ : DifferentiableAt ℝ β x)
    (hnonneg : ∀ᶠ y in 𝓝 x, 0 ≤ β y) (hx : β x = 0) (p : V) :
    fderiv ℝ (relativeTranslate f β p) x = fderiv ℝ f x := by
  have hmin : IsLocalMin β x := hnonneg.mono fun _ hy ↦ by rwa [hx]
  exact fderiv_relativeTranslate_of_hasFDerivAt_zero (hmin.fderiv_eq_zero ▸ hβ.hasFDerivAt) p

/-- **Uniform `C^k` norm control on compact sets (localized form).** If `β : E → ℝ` is `C^n` on an
open neighbourhood `s` of a compact set `K ⊆ E`, then for any `f : E → V` (requiring no regularity
on `f`) and any integer order `k ≤ n`, there is a constant `B ≥ 0` such that all iterated
derivatives of `relativeTranslate f β p - f` of order `i ≤ k` on `K` are bounded by `B * ‖p‖`. -/
theorem exists_norm_iteratedFDeriv_relativeTranslate_sub_le_of_isOpen (f : E → V)
    {β : E → ℝ} {s K : Set E} {n : ℕ∞ω} {k : ℕ}
    (hβ : ContDiffOn ℝ n β s) (hs : IsOpen s) (hK : IsCompact K) (hKs : K ⊆ s)
    (hk : (k : ℕ∞ω) ≤ n) :
    ∃ B, 0 ≤ B ∧ ∀ (p : V) (i : ℕ), i ≤ k → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ i (fun y ↦ relativeTranslate f β p y - f y) x‖ ≤ B * ‖p‖ := by
  obtain ⟨B, hB0, hB⟩ :=
    (hβ.of_le hk).exists_nonneg_bound_iteratedFDeriv_of_isOpen hs hK hKs
  refine ⟨B, hB0, fun p i hi x hxK ↦ ?_⟩
  have hsub : (fun y ↦ relativeTranslate f β p y - f y) =
      (ContinuousLinearMap.toSpanSingleton ℝ p) ∘ β := by
    ext y
    simp
  have hβx : ContDiffAt ℝ k β x :=
    ((hβ.of_le hk) x (hKs hxK)).contDiffAt (hs.mem_nhds (hKs hxK))
  rw [hsub]
  refine ((ContinuousLinearMap.toSpanSingleton ℝ p).norm_iteratedFDeriv_comp_left hβx
    (by exact_mod_cast hi)).trans ?_
  rw [ContinuousLinearMap.norm_toSpanSingleton, mul_comm]
  exact mul_le_mul_of_nonneg_right (hB i hi x hxK) (norm_nonneg p)

/-- **Uniform `C^k` norm control on compact sets.** For any `f : E → V`, a `C^n` cutoff `β : E → ℝ`,
and a compact set `K ⊆ E`, small parameters `p : V` yield arbitrarily `C^k`-small perturbations
`relativeTranslate f β p - f` on `K` for every finite `k ≤ n`. -/
theorem exists_norm_iteratedFDeriv_relativeTranslate_sub_le (f : E → V)
    {β : E → ℝ} {K : Set E} {n : ℕ∞ω} {k : ℕ}
    (hβ : ContDiff ℝ n β) (hK : IsCompact K) (hk : (k : ℕ∞ω) ≤ n) :
    ∃ B, 0 ≤ B ∧ ∀ (p : V) (i : ℕ), i ≤ k → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ i (fun y ↦ relativeTranslate f β p y - f y) x‖ ≤ B * ‖p‖ :=
  exists_norm_iteratedFDeriv_relativeTranslate_sub_le_of_isOpen f
    hβ.contDiffOn isOpen_univ hK (subset_univ K) hk

end Calculus

section Transversality

variable {E W V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Universal transversality criterion for `relativeTranslate`.** Suppose `f : E → V` and
`β : E → ℝ` are differentiable at `x`, `j : W → V` is differentiable at `y`, and `fderiv ℝ β x = 0`
whenever `β x = 0`. Then the total Fréchet derivative of
`incidenceEquation (fun z : E × V ↦ relativeTranslate f β z.2 z.1) j` at `((x, y), p)` is
surjective if and only if `(fderiv ℝ f x).coprod (-fderiv ℝ j y)` is surjective whenever
`β x = 0`. -/
theorem surjective_fderiv_incidenceEquation_relativeTranslate_iff
    {f : E → V} {β : E → ℝ} {j : W → V} {x : E} {y : W} {p : V}
    (hf : DifferentiableAt ℝ f x) (hβ : DifferentiableAt ℝ β x) (hj : DifferentiableAt ℝ j y)
    (hβ0 : β x = 0 → fderiv ℝ β x = 0) :
    Surjective
        (fderiv ℝ (incidenceEquation (fun z : E × V ↦ relativeTranslate f β z.2 z.1) j)
          ((x, y), p)) ↔
      (β x = 0 → Surjective ((fderiv ℝ f x).coprod (-fderiv ℝ j y))) := by
  have hFd : DifferentiableAt ℝ (fun z : E × V ↦ relativeTranslate f β z.2 z.1) (x, p) :=
    differentiableAt_relativeTranslate_snd_fst hf hβ p
  by_cases hβx : β x = 0
  · rw [surjective_fderiv_incidenceEquation_iff_surjective_coprod hFd hj,
      fderiv_relativeTranslate_snd_fst_of_hasFDerivAt_zero_of_eq_zero
        (hβ0 hβx ▸ hβ.hasFDerivAt) hβx p]
    constructor
    · intro hsurj _ w
      obtain ⟨⟨⟨u, _⟩, v⟩, huv⟩ := hsurj w
      exact ⟨(u, v), by simpa using huv⟩
    · intro hgood w
      obtain ⟨⟨u, v⟩, huv⟩ := hgood hβx w
      exact ⟨((u, 0), v), by simpa using huv⟩
  · refine ⟨fun _ h0 ↦ False.elim (hβx h0), fun _ ↦ ?_⟩
    refine surjective_fderiv_incidenceEquation_of_surjective_comp_inr hj fun w ↦ ?_
    refine ⟨(β x)⁻¹ • w, ?_⟩
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      fderiv_relativeTranslate_snd_fst_apply hf hβ p 0 ((β x)⁻¹ • w), map_zero, zero_smul,
      zero_add, smul_smul, mul_inv_cancel₀ hβx, one_smul]

end Transversality

section FiniteDimensional

variable {E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- **Generic relative perturbations on a subset `U` (measure form).** For `C^n` data along the
incidence locus inside `U ⊆ (E × W) × V` above the Morse--Sard threshold
`finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 ≤ n`, if `fderiv ℝ β` vanishes and `f` is already
transverse to `j` at incidence points in `U` where `β` vanishes, then the parameters `p : V` failing
regularity on `U` have additive Haar measure zero. -/
theorem addHaar_setOf_not_isRegularIncidenceParameterOn_relativeTranslate_eq_zero
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [IsAddHaarMeasure μ]
    {f : E → V} {β : E → ℝ} {j : W → V} {U : Set ((E × W) × V)} {n : ℕ∞ω}
    (hf : ∀ z ∈ U, relativeTranslate f β z.2 z.1.1 = j z.1.2 → ContDiffAt ℝ n f z.1.1)
    (hβ : ∀ z ∈ U, relativeTranslate f β z.2 z.1.1 = j z.1.2 → ContDiffAt ℝ n β z.1.1)
    (hj : ∀ z ∈ U, relativeTranslate f β z.2 z.1.1 = j z.1.2 → ContDiffAt ℝ n j z.1.2)
    (hβ0 : ∀ z ∈ U, β z.1.1 = 0 → f z.1.1 = j z.1.2 → fderiv ℝ β z.1.1 = 0)
    (hgood : ∀ z ∈ U, β z.1.1 = 0 → f z.1.1 = j z.1.2 →
      Surjective ((fderiv ℝ f z.1.1).coprod (-fderiv ℝ j z.1.2)))
    (hn : ((finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) :
    μ {p | ¬ IsRegularIncidenceParameterOn
      (fun z : E × V ↦ relativeTranslate f β z.2 z.1) j U p} = 0 := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine addHaar_setOf_not_isRegularIncidenceParameterOn_eq_zero μ
    (fun z hzU hz0 ↦ ?_) (fun z hzU hz0 ↦ ?_) (fun ⟨⟨x, y⟩, p⟩ hzU hz0 ↦ ?_) hn
  · have hEq := incidenceEquation_eq_zero.1 hz0
    exact contDiffAt_relativeTranslate_snd_fst (hf z hzU hEq) (hβ z hzU hEq)
  · exact hj z hzU (incidenceEquation_eq_zero.1 hz0)
  · have hEq : relativeTranslate f β p x = j y := incidenceEquation_eq_zero.1 hz0
    exact (surjective_fderiv_incidenceEquation_relativeTranslate_iff
      ((hf _ hzU hEq).differentiableAt hn0) ((hβ _ hzU hEq).differentiableAt hn0)
      ((hj _ hzU hEq).differentiableAt hn0)
      fun h0 ↦ hβ0 _ hzU h0 (by rwa [relativeTranslate_apply_of_eq_zero p h0] at hEq)).2
      fun h0 ↦ hgood _ hzU h0 (by rwa [relativeTranslate_apply_of_eq_zero p h0] at hEq)

/-- Almost every parameter `p : V` for additive Haar measure is a regular incidence parameter on
`U` for `relativeTranslate f β` against `j`. -/
theorem ae_isRegularIncidenceParameterOn_relativeTranslate
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [IsAddHaarMeasure μ]
    {f : E → V} {β : E → ℝ} {j : W → V} {U : Set ((E × W) × V)} {n : ℕ∞ω}
    (hf : ∀ z ∈ U, relativeTranslate f β z.2 z.1.1 = j z.1.2 → ContDiffAt ℝ n f z.1.1)
    (hβ : ∀ z ∈ U, relativeTranslate f β z.2 z.1.1 = j z.1.2 → ContDiffAt ℝ n β z.1.1)
    (hj : ∀ z ∈ U, relativeTranslate f β z.2 z.1.1 = j z.1.2 → ContDiffAt ℝ n j z.1.2)
    (hβ0 : ∀ z ∈ U, β z.1.1 = 0 → f z.1.1 = j z.1.2 → fderiv ℝ β z.1.1 = 0)
    (hgood : ∀ z ∈ U, β z.1.1 = 0 → f z.1.1 = j z.1.2 →
      Surjective ((fderiv ℝ f z.1.1).coprod (-fderiv ℝ j z.1.2)))
    (hn : ((finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ∀ᵐ p ∂μ, IsRegularIncidenceParameterOn
      (fun z : E × V ↦ relativeTranslate f β z.2 z.1) j U p :=
  ae_iff.2 <|
    addHaar_setOf_not_isRegularIncidenceParameterOn_relativeTranslate_eq_zero μ
      hf hβ hj hβ0 hgood hn

/-- The parameters `p : V` that are regular on `U` for `relativeTranslate f β` against `j` are
dense in `V` (needing no measurable space on `V`). -/
theorem dense_setOf_isRegularIncidenceParameterOn_relativeTranslate
    {f : E → V} {β : E → ℝ} {j : W → V} {U : Set ((E × W) × V)} {n : ℕ∞ω}
    (hf : ∀ z ∈ U, relativeTranslate f β z.2 z.1.1 = j z.1.2 → ContDiffAt ℝ n f z.1.1)
    (hβ : ∀ z ∈ U, relativeTranslate f β z.2 z.1.1 = j z.1.2 → ContDiffAt ℝ n β z.1.1)
    (hj : ∀ z ∈ U, relativeTranslate f β z.2 z.1.1 = j z.1.2 → ContDiffAt ℝ n j z.1.2)
    (hβ0 : ∀ z ∈ U, β z.1.1 = 0 → f z.1.1 = j z.1.2 → fderiv ℝ β z.1.1 = 0)
    (hgood : ∀ z ∈ U, β z.1.1 = 0 → f z.1.1 = j z.1.2 →
      Surjective ((fderiv ℝ f z.1.1).coprod (-fderiv ℝ j z.1.2)))
    (hn : ((finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {p | IsRegularIncidenceParameterOn
      (fun z : E × V ↦ relativeTranslate f β z.2 z.1) j U p} := by
  borelize V
  exact Measure.dense_of_ae (μ := (addHaar : Measure V))
    (ae_isRegularIncidenceParameterOn_relativeTranslate addHaar hf hβ hj hβ0 hgood hn)

/-- **Generic relative perturbations (global `C^n` measure form).** For `C^n` maps `f`, `β`, and
`j` with `0 ≤ β` satisfying the Morse--Sard threshold
`finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 ≤ n`, if `f` is transverse to `j` whenever `β x = 0`
and `f x = j y`, then the parameters `p : V` failing incidence regularity for
`relativeTranslate f β` against `j` have additive Haar measure zero. -/
theorem addHaar_setOf_not_isRegularIncidenceParameter_relativeTranslate_eq_zero
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [IsAddHaarMeasure μ]
    {f : E → V} {β : E → ℝ} {j : W → V} {n : ℕ∞ω}
    (hf : ContDiff ℝ n f) (hβ : ContDiff ℝ n β) (hj : ContDiff ℝ n j)
    (hnonneg : ∀ x, 0 ≤ β x)
    (hgood : ∀ x y, β x = 0 → f x = j y →
      Surjective ((fderiv ℝ f x).coprod (-fderiv ℝ j y)))
    (hn : ((finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) :
    μ {p | ¬ IsRegularIncidenceParameter
      (fun z : E × V ↦ relativeTranslate f β z.2 z.1) j p} = 0 := by
  simpa only [isRegularIncidenceParameterOn_univ] using
    addHaar_setOf_not_isRegularIncidenceParameterOn_relativeTranslate_eq_zero (U := univ) μ
      (fun _ _ _ ↦ hf.contDiffAt) (fun _ _ _ ↦ hβ.contDiffAt) (fun _ _ _ ↦ hj.contDiffAt)
      (fun z _ h0 _ ↦ IsLocalMin.fderiv_eq_zero (Eventually.of_forall fun y ↦ h0.symm ▸ hnonneg y))
      (fun z _ ↦ hgood z.1.1 z.1.2) hn

/-- Almost every parameter `p : V` for additive Haar measure makes `relativeTranslate f β p`
transverse to `j`. -/
theorem ae_isRegularIncidenceParameter_relativeTranslate
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [IsAddHaarMeasure μ]
    {f : E → V} {β : E → ℝ} {j : W → V} {n : ℕ∞ω}
    (hf : ContDiff ℝ n f) (hβ : ContDiff ℝ n β) (hj : ContDiff ℝ n j)
    (hnonneg : ∀ x, 0 ≤ β x)
    (hgood : ∀ x y, β x = 0 → f x = j y →
      Surjective ((fderiv ℝ f x).coprod (-fderiv ℝ j y)))
    (hn : ((finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ∀ᵐ p ∂μ, IsRegularIncidenceParameter
      (fun z : E × V ↦ relativeTranslate f β z.2 z.1) j p :=
  ae_iff.2 <|
    addHaar_setOf_not_isRegularIncidenceParameter_relativeTranslate_eq_zero μ
      hf hβ hj hnonneg hgood hn

/-- The parameters `p : V` making `relativeTranslate f β p` transverse to `j` are dense in `V`
(needing no measurable space on `V`). -/
theorem dense_setOf_isRegularIncidenceParameter_relativeTranslate
    {f : E → V} {β : E → ℝ} {j : W → V} {n : ℕ∞ω}
    (hf : ContDiff ℝ n f) (hβ : ContDiff ℝ n β) (hj : ContDiff ℝ n j)
    (hnonneg : ∀ x, 0 ≤ β x)
    (hgood : ∀ x y, β x = 0 → f x = j y →
      Surjective ((fderiv ℝ f x).coprod (-fderiv ℝ j y)))
    (hn : ((finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {p | IsRegularIncidenceParameter
      (fun z : E × V ↦ relativeTranslate f β z.2 z.1) j p} := by
  simpa only [isRegularIncidenceParameterOn_univ] using
    dense_setOf_isRegularIncidenceParameterOn_relativeTranslate (U := univ)
      (fun _ _ _ ↦ hf.contDiffAt) (fun _ _ _ ↦ hβ.contDiffAt) (fun _ _ _ ↦ hj.contDiffAt)
      (fun z _ h0 _ ↦ IsLocalMin.fderiv_eq_zero (Eventually.of_forall fun y ↦ h0.symm ▸ hnonneg y))
      (fun z _ ↦ hgood z.1.1 z.1.2) hn

end FiniteDimensional

section CountableLocalized

variable {ι V : Type*} [Countable ι]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E W : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]
  [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)] [∀ i, FiniteDimensional ℝ (W i)]

/-- **Simultaneous generic relative perturbations on subsets `U i` (almost-everywhere form).**
For a countable family of incidence problems `(f i, β i, j i, U i)` sharing the parameter space `V`,
almost every `p : V` (for additive Haar measure) is simultaneously regular on `U i` for
`relativeTranslate (f i) (β i)` against `j i` for all `i : ι`. -/
theorem ae_forall_isRegularIncidenceParameterOn_relativeTranslate
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [IsAddHaarMeasure μ]
    {f : ∀ i, E i → V} {β : ∀ i, E i → ℝ} {j : ∀ i, W i → V}
    {U : ∀ i, Set ((E i × W i) × V)} {n : ι → ℕ∞ω}
    (hf : ∀ i, ∀ z ∈ U i, relativeTranslate (f i) (β i) z.2 z.1.1 = j i z.1.2 →
      ContDiffAt ℝ (n i) (f i) z.1.1)
    (hβ : ∀ i, ∀ z ∈ U i, relativeTranslate (f i) (β i) z.2 z.1.1 = j i z.1.2 →
      ContDiffAt ℝ (n i) (β i) z.1.1)
    (hj : ∀ i, ∀ z ∈ U i, relativeTranslate (f i) (β i) z.2 z.1.1 = j i z.1.2 →
      ContDiffAt ℝ (n i) (j i) z.1.2)
    (hβ0 : ∀ i, ∀ z ∈ U i, β i z.1.1 = 0 → f i z.1.1 = j i z.1.2 → fderiv ℝ (β i) z.1.1 = 0)
    (hgood : ∀ i, ∀ z ∈ U i, β i z.1.1 = 0 → f i z.1.1 = j i z.1.2 →
      Surjective ((fderiv ℝ (f i) z.1.1).coprod (-fderiv ℝ (j i) z.1.2)))
    (hn : ∀ i, ((finrank ℝ (E i) + finrank ℝ (W i) - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n i) :
    ∀ᵐ p ∂μ, ∀ i, IsRegularIncidenceParameterOn
      (fun z : E i × V ↦ relativeTranslate (f i) (β i) z.2 z.1) (j i) (U i) p :=
  ae_all_iff.2 fun i ↦
    ae_isRegularIncidenceParameterOn_relativeTranslate μ
      (hf i) (hβ i) (hj i) (hβ0 i) (hgood i) (hn i)

/-- Parameters `p : V` simultaneously regular on `U i` for `relativeTranslate (f i) (β i)` against
`j i` across a countable family are dense in `V` (needing no measurable space on `V`). -/
theorem dense_setOf_forall_isRegularIncidenceParameterOn_relativeTranslate
    {f : ∀ i, E i → V} {β : ∀ i, E i → ℝ} {j : ∀ i, W i → V}
    {U : ∀ i, Set ((E i × W i) × V)} {n : ι → ℕ∞ω}
    (hf : ∀ i, ∀ z ∈ U i, relativeTranslate (f i) (β i) z.2 z.1.1 = j i z.1.2 →
      ContDiffAt ℝ (n i) (f i) z.1.1)
    (hβ : ∀ i, ∀ z ∈ U i, relativeTranslate (f i) (β i) z.2 z.1.1 = j i z.1.2 →
      ContDiffAt ℝ (n i) (β i) z.1.1)
    (hj : ∀ i, ∀ z ∈ U i, relativeTranslate (f i) (β i) z.2 z.1.1 = j i z.1.2 →
      ContDiffAt ℝ (n i) (j i) z.1.2)
    (hβ0 : ∀ i, ∀ z ∈ U i, β i z.1.1 = 0 → f i z.1.1 = j i z.1.2 → fderiv ℝ (β i) z.1.1 = 0)
    (hgood : ∀ i, ∀ z ∈ U i, β i z.1.1 = 0 → f i z.1.1 = j i z.1.2 →
      Surjective ((fderiv ℝ (f i) z.1.1).coprod (-fderiv ℝ (j i) z.1.2)))
    (hn : ∀ i, ((finrank ℝ (E i) + finrank ℝ (W i) - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n i) :
    Dense {p | ∀ i, IsRegularIncidenceParameterOn
      (fun z : E i × V ↦ relativeTranslate (f i) (β i) z.2 z.1) (j i) (U i) p} := by
  borelize V
  exact Measure.dense_of_ae (μ := (addHaar : Measure V))
    (ae_forall_isRegularIncidenceParameterOn_relativeTranslate addHaar hf hβ hj hβ0 hgood hn)

/-- **Simultaneous small localized relative perturbations.** Under the hypotheses of
`TauCeti.dense_setOf_forall_isRegularIncidenceParameterOn_relativeTranslate`, if each cutoff `β i`
vanishes on `C i ⊆ E i`, then for every `r > 0` there exists `p : V` with `‖p‖ < r` that is
simultaneously regular on `U i` for all `i` and leaves each `f i` unchanged on `C i`. -/
theorem exists_forall_isRegularIncidenceParameterOn_relativeTranslate
    {f : ∀ i, E i → V} {β : ∀ i, E i → ℝ} {j : ∀ i, W i → V}
    {U : ∀ i, Set ((E i × W i) × V)} {C : ∀ i, Set (E i)} {n : ι → ℕ∞ω}
    (hf : ∀ i, ∀ z ∈ U i, relativeTranslate (f i) (β i) z.2 z.1.1 = j i z.1.2 →
      ContDiffAt ℝ (n i) (f i) z.1.1)
    (hβ : ∀ i, ∀ z ∈ U i, relativeTranslate (f i) (β i) z.2 z.1.1 = j i z.1.2 →
      ContDiffAt ℝ (n i) (β i) z.1.1)
    (hj : ∀ i, ∀ z ∈ U i, relativeTranslate (f i) (β i) z.2 z.1.1 = j i z.1.2 →
      ContDiffAt ℝ (n i) (j i) z.1.2)
    (hβ0 : ∀ i, ∀ z ∈ U i, β i z.1.1 = 0 → f i z.1.1 = j i z.1.2 → fderiv ℝ (β i) z.1.1 = 0)
    (hC : ∀ i, ∀ x ∈ C i, β i x = 0)
    (hgood : ∀ i, ∀ z ∈ U i, β i z.1.1 = 0 → f i z.1.1 = j i z.1.2 →
      Surjective ((fderiv ℝ (f i) z.1.1).coprod (-fderiv ℝ (j i) z.1.2)))
    (hn : ∀ i, ((finrank ℝ (E i) + finrank ℝ (W i) - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n i)
    {r : ℝ} (hr : 0 < r) :
    ∃ p : V, ‖p‖ < r ∧
      (∀ i, IsRegularIncidenceParameterOn
        (fun z : E i × V ↦ relativeTranslate (f i) (β i) z.2 z.1) (j i) (U i) p) ∧
      ∀ i, EqOn (relativeTranslate (f i) (β i) p) (f i) (C i) := by
  have hdense := dense_setOf_forall_isRegularIncidenceParameterOn_relativeTranslate
    hf hβ hj hβ0 hgood hn
  obtain ⟨p, hp_ball, hp_reg⟩ := Metric.dense_iff.1 hdense 0 r hr
  exact ⟨p, mem_ball_zero_iff.1 hp_ball, hp_reg,
    fun i ↦ eqOn_relativeTranslate_of_eq_zero p (hC i)⟩

end CountableLocalized

section CountableAndClosedSet

variable {ι E V : Type*} [Countable ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]
  [∀ i, FiniteDimensional ℝ (W i)]

/-- **Simultaneous small relative perturbation against a countable family of maps (`C^n` form).**
For a `C^n` map `f`, a nonnegative `C^k` cutoff `β` with zero set `C`, and a countable family of
`C^{m i}` maps `j i : W i → V` satisfying
`finrank ℝ E + finrank ℝ (W i) - finrank ℝ V + 1 ≤ min (min n k) (m i)`, if `f` is transverse on `C`
to every `j i`, then there exist arbitrarily small parameters `‖p‖ < r` making
`relativeTranslate f β p` simultaneously transverse to every `j i` while fixing `f` on `C`. -/
theorem exists_forall_isRegularIncidenceParameter_relativeTranslate
    {f : E → V} {β : E → ℝ} {j : ∀ i, W i → V} {C : Set E} {n k : ℕ∞ω} {m : ι → ℕ∞ω}
    (hf : ContDiff ℝ n f) (hβ : ContDiff ℝ k β) (hj : ∀ i, ContDiff ℝ (m i) (j i))
    (hnonneg : ∀ x, 0 ≤ β x) (hzero : ∀ x, β x = 0 ↔ x ∈ C)
    (hgood : ∀ i, ∀ x ∈ C, ∀ y, f x = j i y →
      Surjective ((fderiv ℝ f x).coprod (-fderiv ℝ (j i) y)))
    (hn : ∀ i, ((finrank ℝ E + finrank ℝ (W i) - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤
      min (min n k) (m i))
    {r : ℝ} (hr : 0 < r) :
    ∃ p : V, ‖p‖ < r ∧
      (∀ i, IsRegularIncidenceParameter
        (fun z : E × V ↦ relativeTranslate f β z.2 z.1) (j i) p) ∧
      EqOn (relativeTranslate f β p) f C := by
  obtain ⟨p, hpr, hpreg, -⟩ :=
    exists_forall_isRegularIncidenceParameterOn_relativeTranslate
      (E := fun _ ↦ E) (W := W) (f := fun _ ↦ f) (β := fun _ ↦ β) (j := j)
      (U := fun _ ↦ univ) (C := fun _ ↦ C) (n := fun i ↦ min (min n k) (m i))
      (fun _ _ _ _ ↦ (hf.of_le ((min_le_left _ _).trans (min_le_left _ _))).contDiffAt)
      (fun _ _ _ _ ↦ (hβ.of_le ((min_le_left _ _).trans (min_le_right _ _))).contDiffAt)
      (fun i _ _ _ ↦ ((hj i).of_le (min_le_right _ _)).contDiffAt)
      (fun _ z _ h0 _ ↦
        IsLocalMin.fderiv_eq_zero (Eventually.of_forall fun y ↦ h0.symm ▸ hnonneg y))
      (fun _ x hx ↦ (hzero x).2 hx)
      (fun i z _ hβ0 ↦ hgood i z.1.1 ((hzero z.1.1).1 hβ0) z.1.2) hn hr
  exact ⟨p, hpr, fun i ↦ isRegularIncidenceParameterOn_univ.1 (hpreg i),
    eqOn_relativeTranslate_of_eq_zero p fun x hx ↦ (hzero x).2 hx⟩

/-- **Cutoff-free closed-set relative transversality (countable-family `C^n` form).** Given a
closed subset `C ⊆ E` of a finite-dimensional real normed space, a `C^n` map `f : E → V`, and a
countable family of `C^{m i}` maps `j i : W i → V` satisfying the Morse--Sard threshold
`finrank ℝ E + finrank ℝ (W i) - finrank ℝ V + 1 ≤ min n (m i)` such that `f` is already transverse
on `C` to each `j i`, there exists a smooth cutoff `β : E → ℝ` with `range β ⊆ Icc 0 1` and
`{x | β x = 0} = C` such that for every `r > 0`, there is a parameter `p : V` with `‖p‖ < r` making
`relativeTranslate f β p` simultaneously transverse to every `j i` while preserving both `f` and
`fderiv ℝ f` on `C`. -/
theorem _root_.IsClosed.exists_forall_isRegularIncidenceParameter_relativeTranslate
    {C : Set E} (hC : IsClosed C) {f : E → V} {j : ∀ i, W i → V} {n : ℕ∞ω} {m : ι → ℕ∞ω}
    (hf : ContDiff ℝ n f) (hj : ∀ i, ContDiff ℝ (m i) (j i))
    (hgood : ∀ i, ∀ x ∈ C, ∀ y, f x = j i y →
      Surjective ((fderiv ℝ f x).coprod (-fderiv ℝ (j i) y)))
    (hn : ∀ i, ((finrank ℝ E + finrank ℝ (W i) - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ min n (m i)) :
    ∃ β : E → ℝ, ContDiff ℝ ∞ β ∧ range β ⊆ Icc 0 1 ∧ (∀ x, β x = 0 ↔ x ∈ C) ∧
      ∀ ⦃r : ℝ⦄, 0 < r → ∃ p : V, ‖p‖ < r ∧
        (∀ i, IsRegularIncidenceParameter
          (fun z : E × V ↦ relativeTranslate f β z.2 z.1) (j i) p) ∧
        EqOn (relativeTranslate f β p) f C ∧
        ∀ x ∈ C, fderiv ℝ (relativeTranslate f β p) x = fderiv ℝ f x := by
  obtain ⟨β, hsupp, hβ, hrange⟩ := hC.isOpen_compl.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  have hnonneg : ∀ x, 0 ≤ β x := fun x ↦ (hrange (mem_range_self x)).1
  have hzero : ∀ x, β x = 0 ↔ x ∈ C := by
    intro x
    rw [← notMem_support, hsupp, notMem_compl_iff]
  have hn' : ∀ i, ((finrank ℝ E + finrank ℝ (W i) - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤
      min (min n ∞) (m i) := fun i ↦
    le_min (le_min ((hn i).trans (min_le_left _ _)) (by simp))
      ((hn i).trans (min_le_right _ _))
  refine ⟨β, hβ, hrange, hzero, fun {r} hr ↦ ?_⟩
  obtain ⟨p, hpr, hpreg, hpEq⟩ :=
    TauCeti.exists_forall_isRegularIncidenceParameter_relativeTranslate
      hf hβ hj hnonneg hzero hgood hn' hr
  exact ⟨p, hpr, hpreg, hpEq, fun x hxC ↦
    fderiv_relativeTranslate_of_eventually_nonneg_of_eq_zero
      (hβ.contDiffAt.differentiableAt (by simp))
      (Eventually.of_forall hnonneg) ((hzero x).2 hxC) p⟩

end CountableAndClosedSet

section SingleMapPerturbation

variable {E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- **Small relative perturbations (`C^n` form).** For a `C^n` map `f`, a nonnegative `C^k` cutoff
`β` with zero set `C`, and a `C^m` map `j : W → V` satisfying the Morse--Sard threshold
`finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 ≤ min (min n k) m`, if `f` is already transverse to `j`
on `C`, then for every `r > 0` there exists `p : V` with `‖p‖ < r` making
`relativeTranslate f β p` transverse to `j` while fixing `f` on `C`. -/
theorem exists_isRegularIncidenceParameter_relativeTranslate
    {f : E → V} {β : E → ℝ} {j : W → V} {C : Set E} {n k m : ℕ∞ω}
    (hf : ContDiff ℝ n f) (hβ : ContDiff ℝ k β) (hj : ContDiff ℝ m j)
    (hnonneg : ∀ x, 0 ≤ β x) (hzero : ∀ x, β x = 0 ↔ x ∈ C)
    (hgood : ∀ x ∈ C, ∀ y, f x = j y →
      Surjective ((fderiv ℝ f x).coprod (-fderiv ℝ j y)))
    (hn : ((finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ min (min n k) m)
    {r : ℝ} (hr : 0 < r) :
    ∃ p : V, ‖p‖ < r ∧
      IsRegularIncidenceParameter (fun z : E × V ↦ relativeTranslate f β z.2 z.1) j p ∧
      EqOn (relativeTranslate f β p) f C := by
  obtain ⟨p, hpr, hpreg, hpEq⟩ :=
    exists_forall_isRegularIncidenceParameter_relativeTranslate
      (ι := Unit) (W := fun _ ↦ W) (j := fun _ ↦ j) (m := fun _ ↦ m)
      hf hβ (fun _ ↦ hj) hnonneg hzero (fun _ ↦ hgood) (fun _ ↦ hn) hr
  exact ⟨p, hpr, hpreg (), hpEq⟩

/-- **Cutoff-free closed-set relative transversality (single-map `C^n` form).** If `C ⊆ E` is
closed and `C^n` / `C^m` maps `f : E → V` and `j : W → V` satisfying the Morse--Sard threshold
`finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 ≤ min n m` are already transverse along `C`, then there
exists a smooth cutoff `β : E → ℝ` with `range β ⊆ Icc 0 1` and `{x | β x = 0} = C` such that for
every `r > 0`, some parameter `p : V` with `‖p‖ < r` makes `relativeTranslate f β p` transverse to
`j` while preserving both `f` and `fderiv ℝ f` on `C`. -/
theorem _root_.IsClosed.exists_isRegularIncidenceParameter_relativeTranslate
    {C : Set E} (hC : IsClosed C) {f : E → V} {j : W → V} {n m : ℕ∞ω}
    (hf : ContDiff ℝ n f) (hj : ContDiff ℝ m j)
    (hgood : ∀ x ∈ C, ∀ y, f x = j y →
      Surjective ((fderiv ℝ f x).coprod (-fderiv ℝ j y)))
    (hn : ((finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ min n m) :
    ∃ β : E → ℝ, ContDiff ℝ ∞ β ∧ range β ⊆ Icc 0 1 ∧ (∀ x, β x = 0 ↔ x ∈ C) ∧
      ∀ ⦃r : ℝ⦄, 0 < r → ∃ p : V, ‖p‖ < r ∧
        IsRegularIncidenceParameter (fun z : E × V ↦ relativeTranslate f β z.2 z.1) j p ∧
        EqOn (relativeTranslate f β p) f C ∧
        ∀ x ∈ C, fderiv ℝ (relativeTranslate f β p) x = fderiv ℝ f x := by
  obtain ⟨β, hβ, hrange, hzero, hp⟩ :=
    hC.exists_forall_isRegularIncidenceParameter_relativeTranslate
      (ι := Unit) (W := fun _ ↦ W) (j := fun _ ↦ j) (n := n) (m := fun _ ↦ m)
      hf (fun _ ↦ hj) (fun _ ↦ hgood) (fun _ ↦ hn)
  refine ⟨β, hβ, hrange, hzero, fun {r} hr ↦ ?_⟩
  obtain ⟨p, hpr, hpreg, hpEq, hpfd⟩ := hp hr
  exact ⟨p, hpr, hpreg (), hpEq, hpfd⟩

end SingleMapPerturbation

section Examples

-- Concrete evaluation check: translating `0` along `β(x) = x ^ 2` by `1` at `x = 2` gives `4`.
example : relativeTranslate (0 : ℝ → ℝ) (fun x : ℝ ↦ x ^ 2) (1 : ℝ) 2 = 4 := by
  norm_num [relativeTranslate]

-- Necessity of transversality along `C`: for `f(x) = x ^ 2`, `β(x) = x ^ 2`, `C = {0}` on `ℝ`,
-- and target `j : Unit → ℝ := 0`, every hypothesis of
-- `TauCeti.exists_isRegularIncidenceParameter_relativeTranslate` holds except transversality of `f`
-- to `j` at `0 ∈ C`, and no parameter `p : ℝ` is regular.
example (p : ℝ) :
    ¬ IsRegularIncidenceParameter
      (fun z : ℝ × ℝ ↦ relativeTranslate (fun x : ℝ ↦ x ^ 2) (fun x : ℝ ↦ x ^ 2) z.2 z.1)
      (fun _ : Unit ↦ (0 : ℝ)) p := by
  rw [isRegularIncidenceParameter_const, isRegularParameter_iff]
  intro hp
  have hd : HasDerivAt (fun x : ℝ ↦ x ^ 2) 0 (0 : ℝ) := by
    simpa using hasDerivAt_pow 2 (0 : ℝ)
  have hsq : DifferentiableAt ℝ (fun x : ℝ ↦ x ^ 2) 0 := hd.differentiableAt
  obtain ⟨u, hu⟩ := hp 0 (by norm_num [relativeTranslate]) 1
  rw [← fderiv_slice_left (differentiableAt_relativeTranslate_snd_fst hsq hsq p),
    fderiv_relativeTranslate_of_eventually_nonneg_of_eq_zero hsq
      (Eventually.of_forall fun x ↦ sq_nonneg x) (by norm_num) p,
    hd.hasFDerivAt.fderiv] at hu
  simp at hu

end Examples

end TauCeti
