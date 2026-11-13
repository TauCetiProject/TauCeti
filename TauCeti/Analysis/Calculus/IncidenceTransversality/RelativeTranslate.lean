/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IncidenceTransversality.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.OpenPos
import TauCeti.Analysis.Calculus.ContDiff.Bounds

/-!
# Relative translation families and small transverse perturbations

Let `f : E → V` be a map into a real normed space and `β : E → ℝ` a scalar cutoff vanishing on a
set `C ⊆ E`. The **relative translation family**

  `TauCeti.relativeTranslate f β p x = f x + β x • p`

leaves `f` unchanged on `C`, varies linearly with `p` in every higher `C^k` norm on compact sets,
and connects `f` to `relativeTranslate f β p` via the straight-line homotopy
`t ↦ relativeTranslate f β (t • p)` fixing `C`.

Suppose now that `β` is nonnegative with zero set `{x | β x = 0} = C`, and that `f`, `β`, and
`j : W → V` are differentiable. Every zero `x` of `β` is a local minimum of `β`, so
`fderiv ℝ β x = 0` by Fermat's theorem. Consequently:
1. Where `β x ≠ 0`, differentiating `relativeTranslate f β p x` in the parameter `p` gives the
   surjective scaling `q ↦ β x • q` onto `V`.
2. Where `β x = 0`, we have `x ∈ C`, `relativeTranslate f β p x = f x`, and the parameter
   derivative vanishes while the spatial derivative agrees with `fderiv ℝ f x`.

Therefore, if `f` is already transverse to `j` along `C`, the incidence equation of
`(x, p) ↦ relativeTranslate f β p x` against `j` has surjective total derivative at every
incidence point `((x, y), p)` with `relativeTranslate f β p x = j y`.
Applying the finite-dimensional parametric transversality theorem from
`TauCeti.Analysis.Calculus.IncidenceTransversality.Basic` (under `C^n` smoothness above the
Morse--Sard threshold) then yields that almost every parameter
`p : V` (for additive Haar measure), and in particular arbitrarily small parameters `‖p‖ < r`,
makes `relativeTranslate f β p` transverse to `j` while agreeing with `f` on `C`. Combining this
with `IsOpen.exists_contDiff_support_eq` on `Cᶜ` eliminates the external cutoff altogether for any
closed set `C` in a finite-dimensional real normed space.

## Main declarations

* `TauCeti.relativeTranslate`: the family `f x + β x • p`, defined with minimal algebraic
  typeclasses so that it applies unchanged to arbitrary source types (including manifolds).
* `TauCeti.fderiv_relativeTranslate_of_eventually_nonneg_of_eq_zero`: at a zero of a locally
  nonnegative cutoff `β`, `fderiv ℝ (relativeTranslate f β p) x = fderiv ℝ f x`.
* `TauCeti.exists_norm_iteratedFDeriv_relativeTranslate_sub_le`: uniform linear `O(‖p‖)` control of
  all derivatives up to order `k` of `relativeTranslate f β p - f` on compact sets.
* `TauCeti.surjective_fderiv_incidenceEquation_relativeTranslate`: surjectivity of the total
  derivative of the incidence equation of `relativeTranslate f β` against `j` at an incidence point
  `((x, y), p)`, assuming differentiability at `x` and `y`, local nonnegativity of `β` near `x`
  with `β x = 0 → x ∈ C`, and transversality of `f` to `j` along `C`.
* `TauCeti.addHaar_setOf_not_isRegularIncidenceParameter_relativeTranslate_eq_zero`,
  `TauCeti.exists_isRegularIncidenceParameter_relativeTranslate`, and
  `TauCeti.exists_forall_isRegularIncidenceParameter_relativeTranslate`: generic and arbitrarily
  small relative transverse perturbations against one map or a countable family of maps.
* `IsClosed.exists_isRegularIncidenceParameter_relativeTranslate` and
  `IsClosed.exists_forall_isRegularIncidenceParameter_relativeTranslate`: cutoff-free closed-set
  relative transversality in finite dimensions.
* Concrete witnesses, including `TauCeti.not_isRegularIncidenceParameter_relativeTranslate_sq`,
  demonstrating that transversality along `C` cannot be omitted even when `β` vanishes there.

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

/-- Pointwise evaluation of `TauCeti.relativeTranslate`. -/
@[simp]
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

/-- The straight-line affine homotopy between `f x` and `relativeTranslate f β p x` at time `t : ℝ`
is `relativeTranslate f β (t • p) x`, which therefore also fixes `f` wherever `β` vanishes. -/
theorem lineMap_relativeTranslate {E V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : E → V) (β : E → ℝ) (p : V) (x : E) (t : ℝ) :
    AffineMap.lineMap (f x) (relativeTranslate f β p x) t = relativeTranslate f β (t • p) x := by
  rw [AffineMap.lineMap_apply_module', relativeTranslate_sub_self, smul_comm, add_comm]
  rfl

end Algebraic

section Calculus

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Joint `C^n` smoothness at `(x, p)` of `(x', p') ↦ relativeTranslate f β p' x'`. -/
theorem contDiffAt_relativeTranslate_uncurry {f : E → V} {β : E → ℝ} {n : ℕ∞ω} {x : E} {p : V}
    (hf : ContDiffAt ℝ n f x) (hβ : ContDiffAt ℝ n β x) :
    ContDiffAt ℝ n (fun z : E × V ↦ relativeTranslate f β z.2 z.1) (x, p) :=
  (hf.comp (x, p) contDiffAt_fst).add ((hβ.comp (x, p) contDiffAt_fst).smul contDiffAt_snd)

/-- Global joint `C^n` smoothness of `(x, p) ↦ relativeTranslate f β p x`. -/
theorem contDiff_relativeTranslate_uncurry {f : E → V} {β : E → ℝ} {n : ℕ∞ω}
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
theorem hasFDerivAt_relativeTranslate_uncurry {f : E → V} {β : E → ℝ}
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

/-- Action of `fderiv ℝ (fun z : E × V ↦ relativeTranslate f β z.2 z.1) (x, p)` on `(u, q)`. -/
theorem fderiv_relativeTranslate_uncurry_apply {f : E → V} {β : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hβ : DifferentiableAt ℝ β x) (p : V) (u : E) (q : V) :
    fderiv ℝ (fun z : E × V ↦ relativeTranslate f β z.2 z.1) (x, p) (u, q) =
      fderiv ℝ f x u + fderiv ℝ β x u • p + β x • q := by
  rw [(hasFDerivAt_relativeTranslate_uncurry hf.hasFDerivAt hβ.hasFDerivAt p).fderiv]
  simp [add_assoc]

/-- Fréchet derivative of the fixed-parameter slice `relativeTranslate f β p` at `x`. -/
theorem hasFDerivAt_relativeTranslate {f : E → V} {β : E → ℝ}
    {Df : E →L[ℝ] V} {Dβ : E →L[ℝ] ℝ} {x : E}
    (hf : HasFDerivAt f Df x) (hβ : HasFDerivAt β Dβ x) (p : V) :
    HasFDerivAt (relativeTranslate f β p) (Df + Dβ.smulRight p) x := by
  refine (hf.add (hβ.smul (hasFDerivAt_const p x))).congr_fderiv ?_
  ext u
  simp

/-- At a zero `x` of a locally nonnegative cutoff `β`, `β` attains a local minimum, so `Dβ = 0` and
`relativeTranslate f β p` has the exact same Fréchet derivative `Df` as `f` at `x`. -/
theorem hasFDerivAt_relativeTranslate_of_eventually_nonneg_of_eq_zero {f : E → V} {β : E → ℝ}
    {Df : E →L[ℝ] V} {x : E} (hf : HasFDerivAt f Df x) (hβ : DifferentiableAt ℝ β x)
    (hnonneg : ∀ᶠ y in 𝓝 x, 0 ≤ β y) (hx : β x = 0) (p : V) :
    HasFDerivAt (relativeTranslate f β p) Df x := by
  have hmin : IsLocalMin β x := hnonneg.mono fun y hy ↦ by rwa [hx]
  have hβ0 : HasFDerivAt β 0 x := hmin.fderiv_eq_zero ▸ hβ.hasFDerivAt
  simpa using hasFDerivAt_relativeTranslate hf hβ0 p

/-- At a zero `x` of a locally nonnegative differentiable cutoff `β`, the Fréchet derivative of
`relativeTranslate f β p` equals `fderiv ℝ f x`. -/
theorem fderiv_relativeTranslate_of_eventually_nonneg_of_eq_zero {f : E → V} {β : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hβ : DifferentiableAt ℝ β x)
    (hnonneg : ∀ᶠ y in 𝓝 x, 0 ≤ β y) (hx : β x = 0) (p : V) :
    fderiv ℝ (relativeTranslate f β p) x = fderiv ℝ f x :=
  (hasFDerivAt_relativeTranslate_of_eventually_nonneg_of_eq_zero
    hf.hasFDerivAt hβ hnonneg hx p).fderiv

/-- At a zero `x` of a locally nonnegative differentiable cutoff `β`, the joint Fréchet derivative
of `(x', p') ↦ relativeTranslate f β p' x'` at `(x, p)` kills the parameter variation and reduces
to `(fderiv ℝ f x).comp fst`. -/
theorem fderiv_relativeTranslate_uncurry_of_eventually_nonneg_of_eq_zero {f : E → V} {β : E → ℝ}
    {x : E} (hf : DifferentiableAt ℝ f x) (hβ : DifferentiableAt ℝ β x)
    (hnonneg : ∀ᶠ y in 𝓝 x, 0 ≤ β y) (hx : β x = 0) (p : V) :
    fderiv ℝ (fun z : E × V ↦ relativeTranslate f β z.2 z.1) (x, p) =
      (fderiv ℝ f x).comp (ContinuousLinearMap.fst ℝ E V) := by
  have hmin : IsLocalMin β x := hnonneg.mono fun y hy ↦ by rwa [hx]
  refine ContinuousLinearMap.ext fun ⟨u, q⟩ ↦ ?_
  rw [fderiv_relativeTranslate_uncurry_apply hf hβ p u q, hmin.fderiv_eq_zero, hx]
  simp

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

section UniversalTransversality

variable {E W V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Universal transversality of `relativeTranslate`.** At any incidence point
`relativeTranslate f β p x = j y`:
* if `β x ≠ 0`, parameter variation `q ↦ β x • q` alone spans `V`;
* if `β x = 0` and `β` is locally nonnegative near `x`, then `x ∈ C`, `f x = j y`,
  `fderiv ℝ β x = 0`, and transversality of `f` to `j` at `(x, y)` spans `V`.

Only pointwise differentiability at `x` and `y`, local nonnegativity of `β` near `x`, and the
implication `β x = 0 → x ∈ C` are needed. -/
theorem surjective_fderiv_incidenceEquation_relativeTranslate
    {f : E → V} {β : E → ℝ} {j : W → V} {C : Set E} {x : E} {y : W} {p : V}
    (hf : DifferentiableAt ℝ f x) (hβ : DifferentiableAt ℝ β x) (hj : DifferentiableAt ℝ j y)
    (hnonneg : ∀ᶠ x' in 𝓝 x, 0 ≤ β x') (hzero : β x = 0 → x ∈ C)
    (hEq : relativeTranslate f β p x = j y)
    (hgood : x ∈ C → f x = j y → Surjective ((fderiv ℝ f x).coprod (-fderiv ℝ j y))) :
    Surjective
      (fderiv ℝ (incidenceEquation (fun z : E × V ↦ relativeTranslate f β z.2 z.1) j)
        ((x, y), p)) := by
  have hFd : DifferentiableAt ℝ (fun z : E × V ↦ relativeTranslate f β z.2 z.1) (x, p) :=
    (hasFDerivAt_relativeTranslate_uncurry hf.hasFDerivAt hβ.hasFDerivAt p).differentiableAt
  by_cases hβx : β x = 0
  · rw [surjective_fderiv_incidenceEquation_iff hFd hj,
      fderiv_relativeTranslate_uncurry_of_eventually_nonneg_of_eq_zero hf hβ hnonneg hβx p]
    have hxC : x ∈ C := hzero hβx
    have hfjy : f x = j y := by
      rwa [relativeTranslate_apply_of_eq_zero p hβx] at hEq
    intro w
    obtain ⟨⟨u, v⟩, huv⟩ := hgood hxC hfjy w
    refine ⟨((u, 0), v), ?_⟩
    simpa using huv
  · refine surjective_fderiv_incidenceEquation_of_surjective_inr hFd hj fun w ↦ ?_
    refine ⟨(β x)⁻¹ • w, ?_⟩
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      fderiv_relativeTranslate_uncurry_apply hf hβ p 0 ((β x)⁻¹ • w), map_zero, zero_smul,
      zero_add, smul_smul, mul_inv_cancel₀ hβx, one_smul]

end UniversalTransversality

section FiniteDimensional

variable {E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- **Generic relative perturbations on a subset `U` (measure form).** For `C^n` data along the
incidence locus inside `U ⊆ (E × W) × V` above the Morse--Sard threshold
`finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 ≤ n`, if `f` is already transverse to `j` at points of
`C`, the parameters `p : V` failing regularity on `U` have additive Haar measure zero. -/
theorem addHaar_setOf_not_isRegularIncidenceParameterOn_relativeTranslate_eq_zero
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [IsAddHaarMeasure μ]
    {f : E → V} {β : E → ℝ} {j : W → V} {C : Set E} {U : Set ((E × W) × V)} {n : ℕ∞ω}
    (hf : ∀ z ∈ U, relativeTranslate f β z.2 z.1.1 = j z.1.2 → ContDiffAt ℝ n f z.1.1)
    (hβ : ∀ z ∈ U, relativeTranslate f β z.2 z.1.1 = j z.1.2 → ContDiffAt ℝ n β z.1.1)
    (hj : ∀ z ∈ U, relativeTranslate f β z.2 z.1.1 = j z.1.2 → ContDiffAt ℝ n j z.1.2)
    (hnonneg : ∀ z ∈ U, relativeTranslate f β z.2 z.1.1 = j z.1.2 → ∀ᶠ x' in 𝓝 z.1.1, 0 ≤ β x')
    (hzero : ∀ z ∈ U, relativeTranslate f β z.2 z.1.1 = j z.1.2 → β z.1.1 = 0 → z.1.1 ∈ C)
    (hgood : ∀ x ∈ C, ∀ y, f x = j y →
      Surjective ((fderiv ℝ f x).coprod (-fderiv ℝ j y)))
    (hn : ((finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) :
    μ {p | ¬ IsRegularIncidenceParameterOn
      (fun z : E × V ↦ relativeTranslate f β z.2 z.1) j U p} = 0 := by
  have hn0 : n ≠ 0 := by
    intro h0
    have h1 : (1 : ℕ∞ω) ≤ 0 := le_trans (by exact_mod_cast Nat.succ_pos _) (h0 ▸ hn)
    exact absurd h1 (by simp)
  refine addHaar_setOf_not_isRegularIncidenceParameterOn_eq_zero μ
    (fun z hzU hz0 ↦ ?_) (fun z hzU hz0 ↦ ?_) (fun ⟨⟨x, y⟩, p⟩ hzU hz0 ↦ ?_) hn
  · rw [incidenceEquation_def, sub_eq_zero] at hz0
    exact contDiffAt_relativeTranslate_uncurry (hf z hzU hz0) (hβ z hzU hz0)
  · rw [incidenceEquation_def, sub_eq_zero] at hz0
    exact hj z hzU hz0
  · have hEq : relativeTranslate f β p x = j y := incidenceEquation_eq_zero_iff.1 hz0
    exact surjective_fderiv_incidenceEquation_relativeTranslate
      ((hf _ hzU hEq).differentiableAt hn0) ((hβ _ hzU hEq).differentiableAt hn0)
      ((hj _ hzU hEq).differentiableAt hn0) (hnonneg _ hzU hEq) (hzero _ hzU hEq) hEq
      (fun hxC ↦ hgood x hxC y)

/-- **Generic relative perturbations (global `C^n` measure form).** -/
theorem addHaar_setOf_not_isRegularIncidenceParameter_relativeTranslate_eq_zero
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [IsAddHaarMeasure μ]
    {f : E → V} {β : E → ℝ} {j : W → V} {C : Set E} {n : ℕ∞ω}
    (hf : ContDiff ℝ n f) (hβ : ContDiff ℝ n β) (hj : ContDiff ℝ n j)
    (hnonneg : ∀ x, 0 ≤ β x) (hzero : ∀ x, β x = 0 → x ∈ C)
    (hgood : ∀ x ∈ C, ∀ y, f x = j y →
      Surjective ((fderiv ℝ f x).coprod (-fderiv ℝ j y)))
    (hn : ((finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) :
    μ {p | ¬ IsRegularIncidenceParameter
      (fun z : E × V ↦ relativeTranslate f β z.2 z.1) j p} = 0 := by
  simpa only [isRegularIncidenceParameterOn_univ] using
    addHaar_setOf_not_isRegularIncidenceParameterOn_relativeTranslate_eq_zero (U := univ) μ
      (fun _ _ _ ↦ hf.contDiffAt) (fun _ _ _ ↦ hβ.contDiffAt) (fun _ _ _ ↦ hj.contDiffAt)
      (fun _ _ _ ↦ Eventually.of_forall hnonneg) (fun z _ _ ↦ hzero z.1.1) hgood hn

/-- Almost every parameter `p : V` for additive Haar measure makes `relativeTranslate f β p`
transverse to `j`. -/
theorem ae_isRegularIncidenceParameter_relativeTranslate
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [IsAddHaarMeasure μ]
    {f : E → V} {β : E → ℝ} {j : W → V} {C : Set E} {n : ℕ∞ω}
    (hf : ContDiff ℝ n f) (hβ : ContDiff ℝ n β) (hj : ContDiff ℝ n j)
    (hnonneg : ∀ x, 0 ≤ β x) (hzero : ∀ x, β x = 0 → x ∈ C)
    (hgood : ∀ x ∈ C, ∀ y, f x = j y →
      Surjective ((fderiv ℝ f x).coprod (-fderiv ℝ j y)))
    (hn : ((finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ∀ᵐ p ∂μ, IsRegularIncidenceParameter
      (fun z : E × V ↦ relativeTranslate f β z.2 z.1) j p :=
  ae_iff.2 <|
    addHaar_setOf_not_isRegularIncidenceParameter_relativeTranslate_eq_zero μ
      hf hβ hj hnonneg hzero hgood hn

/-- The parameters `p : V` making `relativeTranslate f β p` transverse to `j` are dense in `V`
(needing no measurable space on `V`). -/
theorem dense_setOf_isRegularIncidenceParameter_relativeTranslate
    {f : E → V} {β : E → ℝ} {j : W → V} {C : Set E} {n : ℕ∞ω}
    (hf : ContDiff ℝ n f) (hβ : ContDiff ℝ n β) (hj : ContDiff ℝ n j)
    (hnonneg : ∀ x, 0 ≤ β x) (hzero : ∀ x, β x = 0 → x ∈ C)
    (hgood : ∀ x ∈ C, ∀ y, f x = j y →
      Surjective ((fderiv ℝ f x).coprod (-fderiv ℝ j y)))
    (hn : ((finrank ℝ E + finrank ℝ W - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {p | IsRegularIncidenceParameter
      (fun z : E × V ↦ relativeTranslate f β z.2 z.1) j p} := by
  borelize V
  exact Measure.dense_of_ae (μ := (addHaar : Measure V))
    (ae_isRegularIncidenceParameter_relativeTranslate addHaar hf hβ hj hnonneg hzero hgood hn)

/-- **Small relative perturbations.** If `f` is already transverse to `j` on the zero set `C` of a
nonnegative smooth cutoff `β`, arbitrarily small parameters `p : V` make `relativeTranslate f β p`
transverse to `j` while fixing `f` on `C`. -/
theorem exists_isRegularIncidenceParameter_relativeTranslate
    (f : E → V) (β : E → ℝ) (j : W → V) (C : Set E)
    (hf : ContDiff ℝ ∞ f) (hβ : ContDiff ℝ ∞ β) (hj : ContDiff ℝ ∞ j)
    (hnonneg : ∀ x, 0 ≤ β x) (hzero : ∀ x, β x = 0 ↔ x ∈ C)
    (hgood : ∀ x ∈ C, ∀ y, f x = j y →
      Function.Surjective ((fderiv ℝ f x).coprod (-fderiv ℝ j y)))
    {r : ℝ} (hr : 0 < r) :
    ∃ p : V, ‖p‖ < r ∧
      IsRegularIncidenceParameter (fun z : E × V ↦ relativeTranslate f β z.2 z.1) j p ∧
      EqOn (relativeTranslate f β p) f C := by
  have hdense := dense_setOf_isRegularIncidenceParameter_relativeTranslate
    hf hβ hj hnonneg (fun x hx ↦ (hzero x).1 hx) hgood (by simp)
  obtain ⟨p, hp_ball, hp_reg⟩ := Metric.dense_iff.1 hdense 0 r hr
  exact ⟨p, mem_ball_zero_iff.1 hp_ball, hp_reg,
    eqOn_relativeTranslate_of_eq_zero p fun x hx ↦ (hzero x).2 hx⟩

end FiniteDimensional

section CountableAndClosedSet

variable {ι E V : Type*} [Countable ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]
  [∀ i, FiniteDimensional ℝ (W i)]

/-- **Simultaneous small relative perturbation against a countable family of maps (`C^n` form).**
If `f` is transverse on `C` to each map `j i : W i → V` of a countable family, there exist
arbitrarily small parameters `‖p‖ < r` making `relativeTranslate f β p` simultaneously transverse
to every `j i` while fixing `f` on `C`. -/
theorem exists_forall_isRegularIncidenceParameter_relativeTranslate
    {f : E → V} {β : E → ℝ} {j : ∀ i, W i → V} {C : Set E} {n : ℕ∞ω} {m : ι → ℕ∞ω}
    (hf : ContDiff ℝ n f) (hβ : ContDiff ℝ n β) (hj : ∀ i, ContDiff ℝ (m i) (j i))
    (hnonneg : ∀ x, 0 ≤ β x) (hzero : ∀ x, β x = 0 ↔ x ∈ C)
    (hgood : ∀ i, ∀ x ∈ C, ∀ y, f x = j i y →
      Surjective ((fderiv ℝ f x).coprod (-fderiv ℝ (j i) y)))
    (hn : ∀ i, ((finrank ℝ E + finrank ℝ (W i) - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ min n (m i))
    {r : ℝ} (hr : 0 < r) :
    ∃ p : V, ‖p‖ < r ∧
      (∀ i, IsRegularIncidenceParameter
        (fun z : E × V ↦ relativeTranslate f β z.2 z.1) (j i) p) ∧
      EqOn (relativeTranslate f β p) f C := by
  have hdense : Dense {p : V | ∀ i, IsRegularIncidenceParameter
      (fun z : E × V ↦ relativeTranslate f β z.2 z.1) (j i) p} := by
    borelize V
    refine Measure.dense_of_ae (μ := (addHaar : Measure V)) (ae_all_iff.2 fun i ↦ ?_)
    exact ae_isRegularIncidenceParameter_relativeTranslate addHaar (n := min n (m i))
      (hf.of_le (min_le_left _ _)) (hβ.of_le (min_le_left _ _))
      ((hj i).of_le (min_le_right _ _)) hnonneg (fun x hx ↦ (hzero x).1 hx) (hgood i) (hn i)
  obtain ⟨p, hp_ball, hp_reg⟩ := Metric.dense_iff.1 hdense 0 r hr
  exact ⟨p, mem_ball_zero_iff.1 hp_ball, hp_reg,
    eqOn_relativeTranslate_of_eq_zero p fun x hx ↦ (hzero x).2 hx⟩

/-- **Cutoff-free closed-set relative transversality (countable-family `C^n` form).** Given any
closed subset `C ⊆ E` of a finite-dimensional real normed space on which `f : E → V` is already
transverse to each `j i : W i → V`, `IsOpen.exists_contDiff_support_eq` on `Cᶜ` supplies a smooth
cutoff `β : E → ℝ` with `range β ⊆ Icc 0 1` and `{x | β x = 0} = C`, together with an arbitrarily
small parameter `‖p‖ < r` making `relativeTranslate f β p` simultaneously transverse to every `j i`
while preserving both `f` and `fderiv ℝ f` on `C`. -/
theorem _root_.IsClosed.exists_forall_isRegularIncidenceParameter_relativeTranslate
    {C : Set E} (hC : IsClosed C) {f : E → V} {j : ∀ i, W i → V} {n : ℕ∞} {m : ι → ℕ∞ω}
    (hf : ContDiff ℝ n f) (hj : ∀ i, ContDiff ℝ (m i) (j i))
    (hgood : ∀ i, ∀ x ∈ C, ∀ y, f x = j i y →
      Surjective ((fderiv ℝ f x).coprod (-fderiv ℝ (j i) y)))
    (hn : ∀ i, ((finrank ℝ E + finrank ℝ (W i) - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤
      min (n : ℕ∞ω) (m i))
    {r : ℝ} (hr : 0 < r) :
    ∃ (β : E → ℝ) (p : V), ContDiff ℝ ∞ β ∧ range β ⊆ Icc 0 1 ∧ (∀ x, β x = 0 ↔ x ∈ C) ∧
      ‖p‖ < r ∧
      (∀ i, IsRegularIncidenceParameter
        (fun z : E × V ↦ relativeTranslate f β z.2 z.1) (j i) p) ∧
      EqOn (relativeTranslate f β p) f C ∧
      ∀ x ∈ C, fderiv ℝ (relativeTranslate f β p) x = fderiv ℝ f x := by
  obtain ⟨β, hsupp, hβ, hrange⟩ := hC.isOpen_compl.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  have hnonneg : ∀ x, 0 ≤ β x := fun x ↦ (hrange (mem_range_self x)).1
  have hzero : ∀ x, β x = 0 ↔ x ∈ C := by
    intro x
    rw [← notMem_support, hsupp, notMem_compl_iff]
  have hβn : ContDiff ℝ n β := hβ.of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨p, hpr, hpreg, hpEq⟩ :=
    TauCeti.exists_forall_isRegularIncidenceParameter_relativeTranslate
      hf hβn hj hnonneg hzero hgood hn hr
  refine ⟨β, p, hβ, hrange, hzero, hpr, hpreg, hpEq, fun x hxC ↦ ?_⟩
  by_cases hfd : DifferentiableAt ℝ f x
  · exact fderiv_relativeTranslate_of_eventually_nonneg_of_eq_zero hfd
      (hβ.contDiffAt.differentiableAt (by simp))
      (Eventually.of_forall hnonneg) ((hzero x).2 hxC) p
  · have hnot : ¬ DifferentiableAt ℝ (relativeTranslate f β p) x := by
      intro hrd
      have hβp : DifferentiableAt ℝ (fun y ↦ β y • p) x :=
        ((hβ.contDiffAt.differentiableAt (by simp)).smul (differentiableAt_const p))
      have hfx : f = fun y ↦ relativeTranslate f β p y - β y • p := by
        ext y
        simp
      exact hfd (hfx ▸ hrd.sub hβp)
    rw [fderiv_zero_of_not_differentiableAt hnot, fderiv_zero_of_not_differentiableAt hfd]

end CountableAndClosedSet

section SingleClosedSet

variable {E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- **Cutoff-free closed-set relative transversality (single-map smooth form).** -/
theorem _root_.IsClosed.exists_isRegularIncidenceParameter_relativeTranslate
    {C : Set E} (hC : IsClosed C) {f : E → V} {j : W → V}
    (hf : ContDiff ℝ ∞ f) (hj : ContDiff ℝ ∞ j)
    (hgood : ∀ x ∈ C, ∀ y, f x = j y →
      Surjective ((fderiv ℝ f x).coprod (-fderiv ℝ j y)))
    {r : ℝ} (hr : 0 < r) :
    ∃ (β : E → ℝ) (p : V), ContDiff ℝ ∞ β ∧ range β ⊆ Icc 0 1 ∧ (∀ x, β x = 0 ↔ x ∈ C) ∧
      ‖p‖ < r ∧
      IsRegularIncidenceParameter (fun z : E × V ↦ relativeTranslate f β z.2 z.1) j p ∧
      EqOn (relativeTranslate f β p) f C ∧
      ∀ x ∈ C, fderiv ℝ (relativeTranslate f β p) x = fderiv ℝ f x := by
  obtain ⟨β, p, hβ, hrange, hzero, hpr, hpreg, hpEq, hpfd⟩ :=
    hC.exists_forall_isRegularIncidenceParameter_relativeTranslate
      (ι := Unit) (W := fun _ ↦ W) (j := fun _ ↦ j) (n := ⊤) (m := fun _ ↦ ∞)
      hf (fun _ ↦ hj) (fun _ ↦ hgood) (fun _ ↦ by simp) hr
  exact ⟨β, p, hβ, hrange, hzero, hpr, hpreg (), hpEq, hpfd⟩

end SingleClosedSet

section Examples

/-- Concrete evaluation check: translating `0` along `β(x) = x ^ 2` by `1` at `x = 2` gives `4`. -/
theorem relativeTranslate_zero_sq_one_two :
    relativeTranslate (0 : ℝ → ℝ) (fun x : ℝ ↦ x ^ 2) (1 : ℝ) 2 = 4 := by
  norm_num [relativeTranslate]

/-- **Necessity of transversality along `C`.** Let `f(x) = x ^ 2`, `β(x) = x ^ 2`, and `C = {0}` on
`ℝ`, with target point `j : Unit → ℝ := 0`. Every hypothesis of
`TauCeti.exists_isRegularIncidenceParameter_relativeTranslate` holds except transversality of `f` to
`j` at `0 ∈ C`. Here *no* parameter `p : ℝ` at all is regular: for every `p`, `x = 0` remains a
degenerate solution of `x ^ 2 + x ^ 2 * p = 0` with zero derivative. -/
theorem not_isRegularIncidenceParameter_relativeTranslate_sq (p : ℝ) :
    ¬ IsRegularIncidenceParameter
      (fun z : ℝ × ℝ ↦ relativeTranslate (fun x : ℝ ↦ x ^ 2) (fun x : ℝ ↦ x ^ 2) z.2 z.1)
      (fun _ : Unit ↦ (0 : ℝ)) p := by
  have hsq : ContDiff ℝ ∞ (fun x : ℝ ↦ x ^ 2) := contDiff_id.pow 2
  have hF : ContDiff ℝ ∞
      (fun z : ℝ × ℝ ↦ relativeTranslate (fun x : ℝ ↦ x ^ 2) (fun x : ℝ ↦ x ^ 2) z.2 z.1) :=
    contDiff_relativeTranslate_uncurry hsq hsq
  have hj : ContDiff ℝ ∞ (fun _ : Unit ↦ (0 : ℝ)) := contDiff_const
  rw [isRegularIncidenceParameter_iff_coprod
    (fun _ _ _ ↦ hF.contDiffAt.differentiableAt (by simp))
    (fun _ _ _ ↦ hj.contDiffAt.differentiableAt (by simp))]
  intro h
  obtain ⟨⟨u, _⟩, huv⟩ := h 0 () (by norm_num [relativeTranslate]) 1
  have h0 : fderiv ℝ (relativeTranslate (fun x : ℝ ↦ x ^ 2) (fun x : ℝ ↦ x ^ 2) p) 0 = 0 := by
    rw [fderiv_relativeTranslate_of_eventually_nonneg_of_eq_zero
      (hsq.contDiffAt.differentiableAt (by simp))
      (hsq.contDiffAt.differentiableAt (by simp))
      (Eventually.of_forall fun x ↦ sq_nonneg x) (by norm_num) p]
    have hd : HasDerivAt (fun x : ℝ ↦ x ^ 2) 0 (0 : ℝ) := by
      simpa using hasDerivAt_pow 2 (0 : ℝ)
    refine ContinuousLinearMap.ext fun v ↦ ?_
    rw [hd.hasFDerivAt.fderiv]
    simp
  have hj0 : fderiv ℝ (fun _ : Unit ↦ (0 : ℝ)) () = 0 := by simp
  have h_fun_eq :
      (fun x' : ℝ ↦
        (fun z : ℝ × ℝ ↦ relativeTranslate (fun x : ℝ ↦ x ^ 2) (fun x : ℝ ↦ x ^ 2) z.2 z.1)
          (x', p)) =
      relativeTranslate (fun x : ℝ ↦ x ^ 2) (fun x : ℝ ↦ x ^ 2) p := rfl
  rw [h_fun_eq, h0, hj0] at huv
  simp at huv

end Examples

end TauCeti
