/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Order
public import TauCeti.Analysis.CStarAlgebra.Matrix.Trace
public import TauCeti.Analysis.CStarAlgebra.State.TraceKernel
public import TauCeti.Analysis.CStarAlgebra.State.Tracial
import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Matrix

/-!
# Amenable, quasidiagonal and uniform amenable traces

A tracial state `τ` of a C⋆-algebra `A` is approximated by matrix traces when, for every finite
set `F ⊆ A` and every `ε > 0`, there is a completely positive contraction `φ : A → M_k` into a
full matrix algebra `M_k = CStarMatrix (Fin k) (Fin k) ℂ` which is almost multiplicative on `F`
and whose normalized trace `tr_k ∘ φ` almost recovers `τ`. Measuring the two errors in different
ways gives three classes of traces:

* `PositiveContinuousLinearMap.IsAmenableTrace`: `‖φ(ab) - φ(a)φ(b)‖₂ < ε` in the normalized
  2-norm `CStarMatrix.normalizedTwoNorm` and `|tr_k(φ(a)) - τ(a)| < ε` for `a, b ∈ F`;
* `PositiveContinuousLinearMap.IsQuasidiagonalTrace`: the same, with the operator norm of `M_k`
  in place of the 2-norm;
* `PositiveContinuousLinearMap.IsUniformAmenableTrace`: the 2-norm condition on `F`, and
  `|tr_k(φ(a)) - τ(a)| ≤ ε‖a‖` for every `a ∈ A`, that is, `tr_k ∘ φ` is `ε`-close to `τ` in the
  norm of the dual.

The traces are normalized: with the unnormalized trace `Tr_k` the maps `a ↦ τ(a) • 1 / k`
would recover any tracial state exactly with operator-norm defect of order `1 / k`, so every
tracial state would qualify.

The sets `TauCeti.amenableTraces A`, `TauCeti.quasidiagonalTraces A` and
`TauCeti.uniformAmenableTraces A` of tracial states with these properties are subsets of the
tracial state space `TauCeti.tracialStates A` in the weak-* dual.
`TauCeti.AdmitsFaithfulAmenableTrace A` says that some amenable tracial state of `A` is faithful
(`PositiveContinuousLinearMap.IsFaithfulTrace`).

## Main results

* `PositiveContinuousLinearMap.isAmenableTrace_iff` and its siblings unfold the three predicates,
  and `PositiveContinuousLinearMap.isAmenableTrace_iff_exists_superset` and its siblings record
  their monotonicity: a witness for `(F', ε')` is a witness for every `F ⊆ F'` and `ε ≥ ε'`.
* `PositiveContinuousLinearMap.IsQuasidiagonalTrace.isAmenableTrace` and
  `PositiveContinuousLinearMap.IsUniformAmenableTrace.isAmenableTrace`: quasidiagonal and uniform
  amenable traces are amenable, because `‖x‖₂ ≤ ‖x‖` and the recovery error `ε‖a‖` is uniformly
  small on a finite set.
* `PositiveContinuousLinearMap.IsAmenableTrace.comp` and its two siblings: the three properties
  pull back along every star homomorphism `f : A → B`, by composing approximants with `f`, and
  `PositiveContinuousLinearMap.isAmenableTrace_comp_iff` and its siblings: they are invariant
  under star isomorphisms.
* `CStarMatrix.isQuasidiagonalTrace_normalizedTraceMap`,
  `CStarMatrix.isUniformAmenableTrace_normalizedTraceMap` and
  `CStarMatrix.isAmenableTrace_normalizedTraceMap`: the normalized trace of a matrix algebra has
  all three properties, witnessed by the identity map; composing with `IsAmenableTrace.comp`, so
  does `tr_k ∘ π` for every star homomorphism `π : A → M_k`.
* `CStarMatrix.admitsFaithfulAmenableTrace`: a nonempty matrix algebra admits a faithful amenable
  trace, its normalized trace.
* `TauCeti.admitsFaithfulAmenableTrace_congr`: admitting a faithful amenable trace is invariant
  under star isomorphisms, and `TauCeti.not_admitsFaithfulAmenableTrace_of_subsingleton`: the
  zero algebra admits none.
* `TauCeti.convex_amenableTraces`, `TauCeti.convex_quasidiagonalTraces` and
  `TauCeti.convex_uniformAmenableTraces`: the three sets are convex. For `τ = θ τ₁ + (1 - θ) τ₂`,
  approximants `φ₁ : A → M_{k₁}` and `φ₂ : A → M_{k₂}` of `τ₁` and `τ₂` give the block-diagonal
  sum of `p k₂` copies of `φ₁` and `(N - p) k₁` copies of `φ₂`, whose normalized trace is
  `(p / N) tr ∘ φ₁ + (1 - p / N) tr ∘ φ₂`; choosing `p / N` close to `θ` recovers `τ`, and the
  multiplicativity defect of a block-diagonal sum is bounded by the largest defect of its blocks
  (with equality in the operator norm).
* `TauCeti.closure_amenableTraces_inter_tracialStates` and
  `TauCeti.closure_quasidiagonalTraces_inter_tracialStates`: `AT(A)` and `AT_QD(A)` are weak-*
  closed in `T(A)`, hence weak-* closed for unital `A` (`TauCeti.isClosed_amenableTraces`,
  `TauCeti.isClosed_quasidiagonalTraces`), and
  `TauCeti.isClosed_preimage_toWeakDual_uniformAmenableTraces`: `UAT(A)` is closed in the norm
  topology of the continuous dual. It need not be weak-* closed (Brown 2006, Remark 4.1.7).
* `TauCeti.pullbackFunctional_mem_amenableTraces` and its siblings: the restriction of an element
  of each of the three sets along a star homomorphism lies in the corresponding set as soon as it
  is a state. Hence `TauCeti.mapsTo_pullbackFunctional_amenableTraces_of_surjective` and its
  siblings lift the three sets from quotients, and
  `TauCeti.mapsTo_pullbackFunctional_amenableTraces` and its siblings restrict them along unital
  star homomorphisms of unital algebras.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*,
  Mem. Amer. Math. Soc. 184 (2006), no. 865; arXiv:math/0304009v2 (numbering cited),
  Theorem 3.1.6 (2), Definitions 3.2.1 and 3.3.1, Section 3.5 (Proposition 3.5.1 for convexity
  and closure).
* A. Tikuisis, S. White, W. Winter, *Quasidiagonality of nuclear C⋆-algebras*, Ann. of Math.
  185 (2017), Definition 1.2 and Remark 1.5.
* C. Schafhauser, *Subalgebras of simple AF-algebras*, Ann. of Math. 192 (2020), no. 2,
  Theorem A.
-/

public section

open Set WeakDual
open scoped CStarAlgebra ComplexOrder

namespace PositiveContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {τ : A →P[ℂ] ℂ}

/-- `τ` is an **amenable trace**: for every finite `F ⊆ A` and `ε > 0` some completely positive
contraction `φ : A → M_k` satisfies `‖φ(ab) - φ(a)φ(b)‖₂ < ε` in the normalized 2-norm and
`|tr_k(φ(a)) - τ(a)| < ε` for all `a, b ∈ F`. The predicate is applied to tracial states. -/
def IsAmenableTrace (τ : A →P[ℂ] ℂ) : Prop :=
  ∀ (F : Finset A) (ε : ℝ), 0 < ε → ∃ (k : ℕ) (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ),
    (∀ a, ‖φ a‖ ≤ ‖a‖) ∧
    (∀ a ∈ F, ∀ b ∈ F, CStarMatrix.normalizedTwoNorm (φ (a * b) - φ a * φ b) < ε) ∧
    ∀ a ∈ F, ‖CStarMatrix.normalizedTrace (φ a) - τ a‖ < ε

/-- `τ` is a **quasidiagonal trace**: the condition of `IsAmenableTrace` with the
multiplicativity defect `‖φ(ab) - φ(a)φ(b)‖ < ε` measured in the operator norm of `M_k`. -/
def IsQuasidiagonalTrace (τ : A →P[ℂ] ℂ) : Prop :=
  ∀ (F : Finset A) (ε : ℝ), 0 < ε → ∃ (k : ℕ) (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ),
    (∀ a, ‖φ a‖ ≤ ‖a‖) ∧
    (∀ a ∈ F, ∀ b ∈ F, ‖φ (a * b) - φ a * φ b‖ < ε) ∧
    ∀ a ∈ F, ‖CStarMatrix.normalizedTrace (φ a) - τ a‖ < ε

/-- `τ` is a **uniform amenable trace**: the condition of `IsAmenableTrace` with the trace
recovered in the norm of the dual, `|tr_k(φ(a)) - τ(a)| ≤ ε‖a‖` for every `a ∈ A`. -/
def IsUniformAmenableTrace (τ : A →P[ℂ] ℂ) : Prop :=
  ∀ (F : Finset A) (ε : ℝ), 0 < ε → ∃ (k : ℕ) (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ),
    (∀ a, ‖φ a‖ ≤ ‖a‖) ∧
    (∀ a ∈ F, ∀ b ∈ F, CStarMatrix.normalizedTwoNorm (φ (a * b) - φ a * φ b) < ε) ∧
    ∀ a, ‖CStarMatrix.normalizedTrace (φ a) - τ a‖ ≤ ε * ‖a‖

/-- Unfolding lemma for `IsAmenableTrace`. -/
theorem isAmenableTrace_iff : τ.IsAmenableTrace ↔
    ∀ (F : Finset A) (ε : ℝ), 0 < ε → ∃ (k : ℕ) (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ),
      (∀ a, ‖φ a‖ ≤ ‖a‖) ∧
      (∀ a ∈ F, ∀ b ∈ F, CStarMatrix.normalizedTwoNorm (φ (a * b) - φ a * φ b) < ε) ∧
      ∀ a ∈ F, ‖CStarMatrix.normalizedTrace (φ a) - τ a‖ < ε :=
  Iff.rfl

/-- Unfolding lemma for `IsQuasidiagonalTrace`. -/
theorem isQuasidiagonalTrace_iff : τ.IsQuasidiagonalTrace ↔
    ∀ (F : Finset A) (ε : ℝ), 0 < ε → ∃ (k : ℕ) (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ),
      (∀ a, ‖φ a‖ ≤ ‖a‖) ∧
      (∀ a ∈ F, ∀ b ∈ F, ‖φ (a * b) - φ a * φ b‖ < ε) ∧
      ∀ a ∈ F, ‖CStarMatrix.normalizedTrace (φ a) - τ a‖ < ε :=
  Iff.rfl

/-- Unfolding lemma for `IsUniformAmenableTrace`. -/
theorem isUniformAmenableTrace_iff : τ.IsUniformAmenableTrace ↔
    ∀ (F : Finset A) (ε : ℝ), 0 < ε → ∃ (k : ℕ) (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ),
      (∀ a, ‖φ a‖ ≤ ‖a‖) ∧
      (∀ a ∈ F, ∀ b ∈ F, CStarMatrix.normalizedTwoNorm (φ (a * b) - φ a * φ b) < ε) ∧
      ∀ a, ‖CStarMatrix.normalizedTrace (φ a) - τ a‖ ≤ ε * ‖a‖ :=
  Iff.rfl

/-- The approximation property shared by the three trace predicates: completely positive
contractions into `M_k` whose multiplicativity defect, measured by `d`, is `< ε` on `F` and which
satisfy the recovery clause `R F ε`. -/
private def ApproxBy (d : ∀ k : ℕ, CStarMatrix (Fin k) (Fin k) ℂ → ℝ)
    (R : Finset A → ℝ → ∀ k : ℕ, (A →CP CStarMatrix (Fin k) (Fin k) ℂ) → Prop)
    (F : Finset A) (ε : ℝ) : Prop :=
  ∃ (k : ℕ) (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ), (∀ a, ‖φ a‖ ≤ ‖a‖) ∧
    (∀ a ∈ F, ∀ b ∈ F, d k (φ (a * b) - φ a * φ b) < ε) ∧ R F ε k φ

/-- The recovery clause of amenable and quasidiagonal traces: `tr_k ∘ φ` is `ε`-close to `τ` on
`F`. -/
private def RecoverOn (τ : A →P[ℂ] ℂ) (F : Finset A) (ε : ℝ) (k : ℕ)
    (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ) : Prop :=
  ∀ a ∈ F, ‖CStarMatrix.normalizedTrace (φ a) - τ a‖ < ε

/-- The recovery clause of uniform amenable traces: `tr_k ∘ φ` is `ε`-close to `τ` in the norm of
the dual. -/
private def RecoverUniform (τ : A →P[ℂ] ℂ) (_F : Finset A) (ε : ℝ) (k : ℕ)
    (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ) : Prop :=
  ∀ a, ‖CStarMatrix.normalizedTrace (φ a) - τ a‖ ≤ ε * ‖a‖

private theorem isAmenableTrace_iff_approxBy : τ.IsAmenableTrace ↔ ∀ (F : Finset A) (ε : ℝ),
    0 < ε → ApproxBy (fun _ => CStarMatrix.normalizedTwoNorm) (RecoverOn τ) F ε :=
  Iff.rfl

private theorem isQuasidiagonalTrace_iff_approxBy : τ.IsQuasidiagonalTrace ↔
    ∀ (F : Finset A) (ε : ℝ), 0 < ε → ApproxBy (fun _ => norm) (RecoverOn τ) F ε :=
  Iff.rfl

private theorem isUniformAmenableTrace_iff_approxBy : τ.IsUniformAmenableTrace ↔
    ∀ (F : Finset A) (ε : ℝ), 0 < ε →
      ApproxBy (fun _ => CStarMatrix.normalizedTwoNorm) (RecoverUniform τ) F ε :=
  Iff.rfl

/-- An approximant for `(F', ε')` is one for every `F ⊆ F'` and `ε' ≤ ε`, as soon as the recovery
clause is antitone in the finite set and monotone in the error. -/
private theorem ApproxBy.mono {d : ∀ k : ℕ, CStarMatrix (Fin k) (Fin k) ℂ → ℝ}
    {R : Finset A → ℝ → ∀ k : ℕ, (A →CP CStarMatrix (Fin k) (Fin k) ℂ) → Prop}
    (hR : ∀ ⦃F F' : Finset A⦄ ⦃ε ε' : ℝ⦄ ⦃k : ℕ⦄ ⦃φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ⦄,
      F ⊆ F' → ε' ≤ ε → R F' ε' k φ → R F ε k φ)
    {F F' : Finset A} {ε ε' : ℝ} (hF : F ⊆ F') (hε : ε' ≤ ε) (h : ApproxBy d R F' ε') :
    ApproxBy d R F ε := by
  obtain ⟨k, φ, hφ, hmul, hrec⟩ := h
  exact ⟨k, φ, hφ, fun a ha b hb => (hmul a (hF ha) b (hF hb)).trans_le hε, hR hF hε hrec⟩

/-- The monotonicity of `ApproxBy`, in the form of the `_iff_exists_superset` lemmas. -/
private theorem forall_approxBy_iff_exists_superset
    {d : ∀ k : ℕ, CStarMatrix (Fin k) (Fin k) ℂ → ℝ}
    {R : Finset A → ℝ → ∀ k : ℕ, (A →CP CStarMatrix (Fin k) (Fin k) ℂ) → Prop}
    (hR : ∀ ⦃F F' : Finset A⦄ ⦃ε ε' : ℝ⦄ ⦃k : ℕ⦄ ⦃φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ⦄,
      F ⊆ F' → ε' ≤ ε → R F' ε' k φ → R F ε k φ) :
    (∀ (F : Finset A) (ε : ℝ), 0 < ε → ApproxBy d R F ε) ↔
      ∀ (F : Finset A) (ε : ℝ), 0 < ε → ∃ F' : Finset A, F ⊆ F' ∧ ∃ ε' ≤ ε,
        ApproxBy d R F' ε' :=
  ⟨fun h F ε hε => ⟨F, subset_rfl, ε, le_rfl, h F ε hε⟩, fun h F ε hε => by
    obtain ⟨F', hF, ε', hε', h'⟩ := h F ε hε
    exact h'.mono hR hF hε'⟩

/-- **Monotonicity of amenability.** A witness for `(F', ε')` is a witness for every `F ⊆ F'`
and `ε ≥ ε'`, so it suffices to find, for each `(F, ε)`, a witness for some larger finite set
and some smaller error. -/
theorem isAmenableTrace_iff_exists_superset : τ.IsAmenableTrace ↔
    ∀ (F : Finset A) (ε : ℝ), 0 < ε → ∃ F' : Finset A, F ⊆ F' ∧ ∃ ε' ≤ ε,
      ∃ (k : ℕ) (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ), (∀ a, ‖φ a‖ ≤ ‖a‖) ∧
      (∀ a ∈ F', ∀ b ∈ F', CStarMatrix.normalizedTwoNorm (φ (a * b) - φ a * φ b) < ε') ∧
      ∀ a ∈ F', ‖CStarMatrix.normalizedTrace (φ a) - τ a‖ < ε' :=
  forall_approxBy_iff_exists_superset fun _ _ _ _ _ _ hF hε h a ha => (h a (hF ha)).trans_le hε

/-- **Monotonicity of quasidiagonality.** A witness for `(F', ε')` is a witness for every
`F ⊆ F'` and `ε ≥ ε'`. -/
theorem isQuasidiagonalTrace_iff_exists_superset : τ.IsQuasidiagonalTrace ↔
    ∀ (F : Finset A) (ε : ℝ), 0 < ε → ∃ F' : Finset A, F ⊆ F' ∧ ∃ ε' ≤ ε,
      ∃ (k : ℕ) (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ), (∀ a, ‖φ a‖ ≤ ‖a‖) ∧
      (∀ a ∈ F', ∀ b ∈ F', ‖φ (a * b) - φ a * φ b‖ < ε') ∧
      ∀ a ∈ F', ‖CStarMatrix.normalizedTrace (φ a) - τ a‖ < ε' :=
  forall_approxBy_iff_exists_superset fun _ _ _ _ _ _ hF hε h a ha => (h a (hF ha)).trans_le hε

/-- **Monotonicity of uniform amenability.** A witness for `(F', ε')` is a witness for every
`F ⊆ F'` and `ε ≥ ε'`. -/
theorem isUniformAmenableTrace_iff_exists_superset : τ.IsUniformAmenableTrace ↔
    ∀ (F : Finset A) (ε : ℝ), 0 < ε → ∃ F' : Finset A, F ⊆ F' ∧ ∃ ε' ≤ ε,
      ∃ (k : ℕ) (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ), (∀ a, ‖φ a‖ ≤ ‖a‖) ∧
      (∀ a ∈ F', ∀ b ∈ F', CStarMatrix.normalizedTwoNorm (φ (a * b) - φ a * φ b) < ε') ∧
      ∀ a, ‖CStarMatrix.normalizedTrace (φ a) - τ a‖ ≤ ε' * ‖a‖ :=
  forall_approxBy_iff_exists_superset fun _ _ _ _ _ _ _ hε h a =>
    (h a).trans (mul_le_mul_of_nonneg_right hε (norm_nonneg a))

/-- A quasidiagonal trace is amenable, since `‖x‖₂ ≤ ‖x‖` on matrix algebras. -/
theorem IsQuasidiagonalTrace.isAmenableTrace (hτ : τ.IsQuasidiagonalTrace) :
    τ.IsAmenableTrace := by
  intro F ε hε
  obtain ⟨k, φ, hφ, hmul, htr⟩ := hτ F ε hε
  exact ⟨k, φ, hφ, fun a ha b hb => (CStarMatrix.normalizedTwoNorm_le_norm _).trans_lt
    (hmul a ha b hb), htr⟩

/-- A uniform amenable trace is amenable: on a finite set `F` the recovery error `ε‖a‖` is at
most `ε` times the largest norm on `F`. -/
theorem IsUniformAmenableTrace.isAmenableTrace (hτ : τ.IsUniformAmenableTrace) :
    τ.IsAmenableTrace := by
  intro F ε hε
  set M := ∑ a ∈ F, ‖a‖
  have hM : 0 < M + 1 := by positivity
  obtain ⟨k, φ, hφ, hmul, htr⟩ := hτ F (ε / (M + 1)) (div_pos hε hM)
  refine ⟨k, φ, hφ, fun a ha b hb => (hmul a ha b hb).trans_le ?_, fun a ha => ?_⟩
  · exact div_le_self hε.le (by linarith [show 0 ≤ M by positivity])
  · calc ‖CStarMatrix.normalizedTrace (φ a) - τ a‖ ≤ ε / (M + 1) * ‖a‖ := htr a
      _ < ε / (M + 1) * (M + 1) := by
        gcongr
        linarith [Finset.single_le_sum (fun b _ => norm_nonneg b) ha (f := fun b => ‖b‖)]
      _ = ε := div_mul_cancel₀ ε hM.ne'

section Pullback

variable {B F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B] {σ : B →P[ℂ] ℂ}

/-- Composing an approximant `φ` for `(S.image f, ε)` with a star homomorphism `f : A → B` gives an
approximant for `(S, ε)`, for any measure `d` of the multiplicativity defect, as soon as the
recovery clause passes from `φ` on `S.image f` to `φ ∘ f` on `S`. -/
private theorem ApproxBy.comp {d : ∀ k : ℕ, CStarMatrix (Fin k) (Fin k) ℂ → ℝ}
    {RA : Finset A → ℝ → ∀ k : ℕ, (A →CP CStarMatrix (Fin k) (Fin k) ℂ) → Prop}
    {RB : Finset B → ℝ → ∀ k : ℕ, (B →CP CStarMatrix (Fin k) (Fin k) ℂ) → Prop}
    [DecidableEq B] (f : F) {S : Finset A} {ε : ℝ}
    (hR : ∀ ⦃k : ℕ⦄ ⦃φ : B →CP CStarMatrix (Fin k) (Fin k) ℂ⦄,
      RB (S.image f) ε k φ → RA S ε k (φ.comp (f : A →CP B)))
    (h : ApproxBy d RB (S.image f) ε) : ApproxBy d RA S ε := by
  obtain ⟨k, φ, hφ, hmul, hrec⟩ := h
  exact ⟨k, φ.comp (f : A →CP B),
    fun a => by simpa using (hφ (f a)).trans (NonUnitalStarAlgHom.norm_apply_le f a),
    fun a ha b hb => by
      simpa using hmul (f a) (Finset.mem_image_of_mem f ha) (f b) (Finset.mem_image_of_mem f hb),
    hR hrec⟩

/-- **Pullback of amenable traces.** If `σ` is an amenable trace of `B`, then so is its composite
with any star homomorphism `f : A → B`: an approximant `φ` of `σ` gives the approximant
`φ ∘ f` of `σ ∘ f`. The composite is a tracial state only under a norm condition, see
`PositiveContinuousLinearMap.IsTracialState.comp_of_norm_eq_one`. -/
theorem IsAmenableTrace.comp (hσ : σ.IsAmenableTrace) (f : F) :
    (σ.comp (.ofClass f)).IsAmenableTrace := by
  classical
  exact isAmenableTrace_iff_approxBy.2 fun S ε hε =>
    (isAmenableTrace_iff_approxBy.1 hσ (S.image f) ε hε).comp f fun _ _ h a ha => by
      simpa using h (f a) (Finset.mem_image_of_mem f ha)

/-- **Pullback of quasidiagonal traces** along any star homomorphism `f : A → B`. -/
theorem IsQuasidiagonalTrace.comp (hσ : σ.IsQuasidiagonalTrace) (f : F) :
    (σ.comp (.ofClass f)).IsQuasidiagonalTrace := by
  classical
  exact isQuasidiagonalTrace_iff_approxBy.2 fun S ε hε =>
    (isQuasidiagonalTrace_iff_approxBy.1 hσ (S.image f) ε hε).comp f fun _ _ h a ha => by
      simpa using h (f a) (Finset.mem_image_of_mem f ha)

/-- **Pullback of uniform amenable traces** along any star homomorphism `f : A → B`; the
recovery error at `a` is the error of `σ` at `f a`, and `‖f a‖ ≤ ‖a‖`. -/
theorem IsUniformAmenableTrace.comp (hσ : σ.IsUniformAmenableTrace) (f : F) :
    (σ.comp (.ofClass f)).IsUniformAmenableTrace := by
  classical
  exact isUniformAmenableTrace_iff_approxBy.2 fun S ε hε =>
    (isUniformAmenableTrace_iff_approxBy.1 hσ (S.image f) ε hε).comp f fun _ _ h a => by
      simpa using (h (f a)).trans
        (mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le f a) hε.le)

/-- Amenability of traces is invariant under star isomorphisms. -/
theorem isAmenableTrace_comp_iff (e : A ≃⋆ₐ[ℂ] B) :
    (σ.comp (.ofClass e)).IsAmenableTrace ↔ σ.IsAmenableTrace :=
  ⟨fun h => comp_ofClass_comp_ofClass_symm e σ ▸ h.comp e.symm, fun h => h.comp e⟩

/-- Quasidiagonality of traces is invariant under star isomorphisms. -/
theorem isQuasidiagonalTrace_comp_iff (e : A ≃⋆ₐ[ℂ] B) :
    (σ.comp (.ofClass e)).IsQuasidiagonalTrace ↔ σ.IsQuasidiagonalTrace :=
  ⟨fun h => comp_ofClass_comp_ofClass_symm e σ ▸ h.comp e.symm, fun h => h.comp e⟩

/-- Uniform amenability of traces is invariant under star isomorphisms. -/
theorem isUniformAmenableTrace_comp_iff (e : A ≃⋆ₐ[ℂ] B) :
    (σ.comp (.ofClass e)).IsUniformAmenableTrace ↔ σ.IsUniformAmenableTrace :=
  ⟨fun h => comp_ofClass_comp_ofClass_symm e σ ▸ h.comp e.symm, fun h => h.comp e⟩

end Pullback

section Convex

open CompletelyPositiveMap

/-- An approximant may be taken into a nonzero matrix algebra: a map into `M_0` is replaced by the
zero map into `M_1`, which has the same normalized trace `0` and multiplicativity defect `0`. -/
private theorem exists_pos_approximant {k : ℕ} (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ)
    (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) : ∃ (l : ℕ) (ψ : A →CP CStarMatrix (Fin l) (Fin l) ℂ), 0 < l ∧
      (∀ a, ‖ψ a‖ ≤ ‖a‖) ∧
      (∀ a, CStarMatrix.normalizedTrace (ψ a) = CStarMatrix.normalizedTrace (φ a)) ∧
      (∀ a b, CStarMatrix.normalizedTwoNorm (ψ (a * b) - ψ a * ψ b) ≤
        CStarMatrix.normalizedTwoNorm (φ (a * b) - φ a * φ b)) ∧
      ∀ a b, ‖ψ (a * b) - ψ a * ψ b‖ ≤ ‖φ (a * b) - φ a * φ b‖ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨1, 0, one_pos, fun _ => by simp,
      fun _ => by simp [CStarMatrix.normalizedTrace_of_isEmpty], fun _ _ => by simp,
      fun _ _ => by simp⟩
  · exact ⟨k, φ, hk, hφ, fun _ => rfl, fun _ _ => le_rfl, fun _ _ => le_rfl⟩

/-- The normalized trace of the block-diagonal sum of `m₁` copies of `φ₁ : A → M_{k₁}` and `m₂`
copies of `φ₂ : A → M_{k₂}` weights `tr ∘ φ₁` by `m₁ k₁ / (m₁ k₁ + m₂ k₂)` and `tr ∘ φ₂` by
`m₂ k₂ / (m₁ k₁ + m₂ k₂)`. -/
private theorem normalizedTrace_blockDiagonal_sumRec {k₁ k₂ m₁ m₂ : ℕ}
    (φ₁ : A →CP CStarMatrix (Fin k₁) (Fin k₁) ℂ) (φ₂ : A →CP CStarMatrix (Fin k₂) (Fin k₂) ℂ)
    (a : A) :
    CStarMatrix.normalizedTrace (blockDiagonal
      (n := fun i : Fin m₁ ⊕ Fin m₂ => Fin (Sum.elim (fun _ => k₁) (fun _ => k₂) i))
      (Sum.rec (fun _ => φ₁) (fun _ => φ₂)) a) =
      (m₁ * k₁ / (m₁ * k₁ + m₂ * k₂) : ℂ) * CStarMatrix.normalizedTrace (φ₁ a) +
        (m₂ * k₂ / (m₁ * k₁ + m₂ * k₂) : ℂ) * CStarMatrix.normalizedTrace (φ₂ a) := by
  have hc : ∑ i : Fin m₁ ⊕ Fin m₂, Fintype.card (Fin (Sum.elim (fun _ => k₁) (fun _ => k₂) i)) =
      m₁ * k₁ + m₂ * k₂ := by
    simp [Fintype.sum_sum_type]
  -- the block at `inl j` is `φ₁` on `M_{k₁}` and the block at `inr j` is `φ₂` on `M_{k₂}`; the
  -- block family is dependent, so `Sum.elim_inl`/`Sum.elim_inr` cannot be rewritten (the motive is
  -- not type-correct), and each `rfl` instead reduces `Sum.rec`/`Sum.elim` at `inl j`/`inr j`
  rw [normalizedTrace_blockDiagonal_apply, Fintype.card_sigma, hc, Fintype.sum_sum_type,
    Fintype.sum_congr _ (fun _ : Fin m₁ =>
      (k₁ / (m₁ * k₁ + m₂ * k₂ : ℕ) : ℂ) * CStarMatrix.normalizedTrace (φ₁ a))
      fun _ => by rw [Fintype.card_fin]; rfl,
    Fintype.sum_congr _ (fun _ : Fin m₂ =>
      (k₂ / (m₁ * k₁ + m₂ * k₂ : ℕ) : ℂ) * CStarMatrix.normalizedTrace (φ₂ a))
      fun _ => by rw [Fintype.card_fin]; rfl]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- The block-diagonal sum of `p k₂` copies of `φ₁ : A → M_{k₁}` and `(N - p) k₁` copies of
`φ₂ : A → M_{k₂}`, reindexed to `M_{N k₁ k₂}`, is a completely positive contraction with
normalized trace `(p / N) tr(φ₁) + (1 - p / N) tr(φ₂)`, whose multiplicativity defects are bounded
by the larger of those of `φ₁` and `φ₂`, in the normalized 2-norm and in the operator norm. -/
private theorem exists_blockDiagonal_approximant {k₁ k₂ : ℕ}
    (φ₁ : A →CP CStarMatrix (Fin k₁) (Fin k₁) ℂ) (φ₂ : A →CP CStarMatrix (Fin k₂) (Fin k₂) ℂ)
    (h₁ : ∀ a, ‖φ₁ a‖ ≤ ‖a‖) (h₂ : ∀ a, ‖φ₂ a‖ ≤ ‖a‖) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) {N p : ℕ}
    (hN : 0 < N) (hp : p ≤ N) :
    ∃ (K : ℕ) (Φ : A →CP CStarMatrix (Fin K) (Fin K) ℂ), (∀ a, ‖Φ a‖ ≤ ‖a‖) ∧
      (∀ a, CStarMatrix.normalizedTrace (Φ a) = ((p / N : ℝ) : ℂ) *
        CStarMatrix.normalizedTrace (φ₁ a) + ((1 - p / N : ℝ) : ℂ) *
          CStarMatrix.normalizedTrace (φ₂ a)) ∧
      (∀ a b, CStarMatrix.normalizedTwoNorm (Φ (a * b) - Φ a * Φ b) ≤
        max (CStarMatrix.normalizedTwoNorm (φ₁ (a * b) - φ₁ a * φ₁ b))
          (CStarMatrix.normalizedTwoNorm (φ₂ (a * b) - φ₂ a * φ₂ b))) ∧
      ∀ a b, ‖Φ (a * b) - Φ a * Φ b‖ ≤
        max ‖φ₁ (a * b) - φ₁ a * φ₁ b‖ ‖φ₂ (a * b) - φ₂ a * φ₂ b‖ := by
  classical
  -- The blocks: `p k₂` copies of `M_{k₁}` and `(N - p) k₁` copies of `M_{k₂}`.
  let n := fun i : Fin (p * k₂) ⊕ Fin ((N - p) * k₁) => Fin (Sum.elim (fun _ => k₁) (fun _ => k₂) i)
  let φ : ∀ i, A →CP CStarMatrix (n i) (n i) ℂ := Sum.rec (fun _ => φ₁) (fun _ => φ₂)
  let ρ := CStarMatrix.reindexₐ ℂ ℂ (Fintype.equivFin (Σ i, n i))
  have hρ (x : CStarMatrix (Σ i, n i) (Σ i, n i) ℂ) : ‖ρ x‖ = ‖x‖ :=
    NonUnitalStarAlgHom.norm_map ρ ρ.injective x
  have hdef (a b : A) : ρ (blockDiagonal φ (a * b)) - ρ (blockDiagonal φ a) *
      ρ (blockDiagonal φ b) = ρ (CStarMatrix.ofMatrix (Matrix.blockDiagonal' fun i =>
        CStarMatrix.ofMatrix.symm (φ i (a * b) - φ i a * φ i b))) := by
    rw [← map_mul, ← map_sub, blockDiagonal_map_mul_sub]
  refine ⟨_, (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap ρ).comp (blockDiagonal φ),
    ?_, ?_, ?_, ?_⟩ <;>
    simp only [CompletelyPositiveMap.comp_apply,
      CompletelyPositiveMapClass.coe_toCompletelyPositiveLinearMap]
  · intro a
    rw [hρ, norm_blockDiagonal_apply, pi_norm_le_iff_of_nonneg (norm_nonneg a)]
    rintro (_ | _)
    exacts [h₁ a, h₂ a]
  · intro a
    have hden : ((p * k₂ : ℕ) : ℂ) * k₁ + ((N - p) * k₁ : ℕ) * k₂ = N * k₁ * k₂ := by
      push_cast [Nat.cast_sub hp]
      ring
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have hk₁' : (k₁ : ℂ) ≠ 0 := by exact_mod_cast hk₁.ne'
    have hk₂' : (k₂ : ℂ) ≠ 0 := by exact_mod_cast hk₂.ne'
    rw [CStarMatrix.normalizedTrace_reindexₐ, normalizedTrace_blockDiagonal_sumRec, hden]
    push_cast [Nat.cast_sub hp]
    field_simp
  · intro a b
    rw [hdef, CStarMatrix.normalizedTwoNorm_reindexₐ]
    refine CStarMatrix.normalizedTwoNorm_blockDiagonal'_le
      (le_max_of_le_left (CStarMatrix.normalizedTwoNorm_nonneg _)) ?_
    rintro (_ | _)
    exacts [le_max_left _ _, le_max_right _ _]
  · intro a b
    rw [hdef, hρ, CStarMatrix.norm_ofMatrix_blockDiagonal',
      pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))]
    rintro (_ | _)
    exacts [le_max_left _ _, le_max_right _ _]

/-- **Approximants of a convex combination.** If `τ = θ τ₁ + (1 - θ) τ₂` with `θ ∈ [0, 1]`, then
for every `η > 0` completely positive contractions `φ₁` and `φ₂` combine into a completely
positive contraction `Φ` whose multiplicativity defects are bounded by the larger of those of `φ₁`
and `φ₂`, and which recovers `τ` at `a` up to the larger of the recovery errors of `φ₁` and `φ₂`
plus `η (|τ₁ a| + |τ₂ a|)`. The map `Φ` is a block-diagonal sum of copies of `φ₁` and `φ₂` whose
normalized trace has weight `w = p / N` on `φ₁`, with `|w - θ| ≤ η`. -/
private theorem exists_approximant_of_apply_eq {τ₁ τ₂ : A →P[ℂ] ℂ} {θ : ℝ} (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) (hτ : ∀ a, τ a = θ * τ₁ a + (1 - θ) * τ₂ a) {k₁ k₂ : ℕ}
    (φ₁ : A →CP CStarMatrix (Fin k₁) (Fin k₁) ℂ) (φ₂ : A →CP CStarMatrix (Fin k₂) (Fin k₂) ℂ)
    (h₁ : ∀ a, ‖φ₁ a‖ ≤ ‖a‖) (h₂ : ∀ a, ‖φ₂ a‖ ≤ ‖a‖) {η : ℝ} (hη : 0 < η) :
    ∃ (K : ℕ) (Φ : A →CP CStarMatrix (Fin K) (Fin K) ℂ), (∀ a, ‖Φ a‖ ≤ ‖a‖) ∧
      (∀ a b, CStarMatrix.normalizedTwoNorm (Φ (a * b) - Φ a * Φ b) ≤
        max (CStarMatrix.normalizedTwoNorm (φ₁ (a * b) - φ₁ a * φ₁ b))
          (CStarMatrix.normalizedTwoNorm (φ₂ (a * b) - φ₂ a * φ₂ b))) ∧
      (∀ a b, ‖Φ (a * b) - Φ a * Φ b‖ ≤
        max ‖φ₁ (a * b) - φ₁ a * φ₁ b‖ ‖φ₂ (a * b) - φ₂ a * φ₂ b‖) ∧
      ∀ a, ‖CStarMatrix.normalizedTrace (Φ a) - τ a‖ ≤
        max ‖CStarMatrix.normalizedTrace (φ₁ a) - τ₁ a‖
          ‖CStarMatrix.normalizedTrace (φ₂ a) - τ₂ a‖ + η * (‖τ₁ a‖ + ‖τ₂ a‖) := by
  obtain ⟨l₁, ψ₁, hl₁, hψ₁, tr₁, d₁, n₁⟩ := exists_pos_approximant φ₁ h₁
  obtain ⟨l₂, ψ₂, hl₂, hψ₂, tr₂, d₂, n₂⟩ := exists_pos_approximant φ₂ h₂
  -- The weight `w = ⌊θ N⌋ / N` is within `1 / N < η` of `θ`.
  obtain ⟨N, hN⟩ := exists_nat_gt η⁻¹
  have hN0 : (0 : ℝ) < N := (inv_pos.2 hη).trans hN
  have hp : ⌊θ * N⌋₊ ≤ N := Nat.floor_le_of_le (by nlinarith)
  obtain ⟨K, Φ, hΦ, htr, hd, hn⟩ :=
    exists_blockDiagonal_approximant ψ₁ ψ₂ hψ₁ hψ₂ hl₁ hl₂ (by exact_mod_cast hN0) hp
  set w : ℝ := (⌊θ * N⌋₊ / N : ℝ)
  have hw₀ : 0 ≤ w := by positivity
  have hw₁ : w ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hp) hN0.le
  have hwθ : |w - θ| ≤ η := by
    have hlt : θ * N < ⌊θ * N⌋₊ + 1 := Nat.lt_floor_add_one _
    have hle : (⌊θ * N⌋₊ : ℝ) ≤ θ * N := Nat.floor_le (by positivity)
    have hNη : 1 / (N : ℝ) < η := by rwa [one_div, inv_lt_comm₀ hN0 hη]
    rw [abs_sub_comm, abs_of_nonneg (by rw [sub_nonneg, div_le_iff₀ hN0]; exact hle)]
    refine le_of_lt (lt_of_le_of_lt ?_ hNη)
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hN0]
    linarith
  refine ⟨K, Φ, hΦ, fun a b => (hd a b).trans (max_le_max (d₁ a b) (d₂ a b)),
    fun a b => (hn a b).trans (max_le_max (n₁ a b) (n₂ a b)), fun a => ?_⟩
  set t₁ := CStarMatrix.normalizedTrace (φ₁ a)
  set t₂ := CStarMatrix.normalizedTrace (φ₂ a)
  have hsplit : CStarMatrix.normalizedTrace (Φ a) - τ a = (w : ℂ) * (t₁ - τ₁ a) +
      ((1 - w : ℝ) : ℂ) * (t₂ - τ₂ a) + ((w - θ : ℝ) : ℂ) * (τ₁ a - τ₂ a) := by
    rw [htr, tr₁, tr₂, hτ]
    push_cast
    ring
  have hmax₁ : ‖t₁ - τ₁ a‖ ≤ max ‖t₁ - τ₁ a‖ ‖t₂ - τ₂ a‖ := le_max_left _ _
  have hmax₂ : ‖t₂ - τ₂ a‖ ≤ max ‖t₁ - τ₁ a‖ ‖t₂ - τ₂ a‖ := le_max_right _ _
  rw [hsplit]
  refine (norm_add₃_le).trans ?_
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw₀,
    abs_of_nonneg (sub_nonneg.2 hw₁)]
  have h₃ : |w - θ| * ‖τ₁ a - τ₂ a‖ ≤ η * (‖τ₁ a‖ + ‖τ₂ a‖) :=
    mul_le_mul hwθ (norm_sub_le _ _) (norm_nonneg _) hη.le
  nlinarith [mul_le_mul_of_nonneg_left hmax₁ hw₀,
    mul_le_mul_of_nonneg_left hmax₂ (sub_nonneg.2 hw₁)]

/-- Convex combinations preserve the approximation property shared by amenable and quasidiagonal
traces, for a measure `d` of the multiplicativity defect for which approximants combine as in
`exists_approximant_of_apply_eq`. -/
private theorem forall_approxBy_recoverOn_of_apply_eq
    {d : ∀ k : ℕ, CStarMatrix (Fin k) (Fin k) ℂ → ℝ} {τ₁ τ₂ : A →P[ℂ] ℂ}
    (hd : ∀ {k₁ k₂ : ℕ} (φ₁ : A →CP CStarMatrix (Fin k₁) (Fin k₁) ℂ)
      (φ₂ : A →CP CStarMatrix (Fin k₂) (Fin k₂) ℂ), (∀ a, ‖φ₁ a‖ ≤ ‖a‖) → (∀ a, ‖φ₂ a‖ ≤ ‖a‖) →
      ∀ η : ℝ, 0 < η → ∃ (K : ℕ) (Φ : A →CP CStarMatrix (Fin K) (Fin K) ℂ),
        (∀ a, ‖Φ a‖ ≤ ‖a‖) ∧
        (∀ a b, d K (Φ (a * b) - Φ a * Φ b) ≤
          max (d k₁ (φ₁ (a * b) - φ₁ a * φ₁ b)) (d k₂ (φ₂ (a * b) - φ₂ a * φ₂ b))) ∧
        ∀ a, ‖CStarMatrix.normalizedTrace (Φ a) - τ a‖ ≤
          max ‖CStarMatrix.normalizedTrace (φ₁ a) - τ₁ a‖
            ‖CStarMatrix.normalizedTrace (φ₂ a) - τ₂ a‖ + η * (‖τ₁ a‖ + ‖τ₂ a‖))
    (h₁ : ∀ (F : Finset A) (ε : ℝ), 0 < ε → ApproxBy d (RecoverOn τ₁) F ε)
    (h₂ : ∀ (F : Finset A) (ε : ℝ), 0 < ε → ApproxBy d (RecoverOn τ₂) F ε) :
    ∀ (F : Finset A) (ε : ℝ), 0 < ε → ApproxBy d (RecoverOn τ) F ε := by
  intro F ε hε
  set M := ∑ a ∈ F, (‖τ₁ a‖ + ‖τ₂ a‖)
  have hM : 0 ≤ M := by positivity
  obtain ⟨k₁, φ₁, c₁, m₁, r₁⟩ := h₁ F (ε / 2) (half_pos hε)
  obtain ⟨k₂, φ₂, c₂, m₂, r₂⟩ := h₂ F (ε / 2) (half_pos hε)
  obtain ⟨K, Φ, c, m, r⟩ := hd φ₁ φ₂ c₁ c₂ (ε / (2 * (M + 1))) (by positivity)
  refine ⟨K, Φ, c, fun a ha b hb => (m a b).trans_lt
    ((max_lt (m₁ a ha b hb) (m₂ a ha b hb)).trans (half_lt_self hε)), fun a ha => (r a).trans_lt ?_⟩
  have hMa : ‖τ₁ a‖ + ‖τ₂ a‖ ≤ M :=
    Finset.single_le_sum (f := fun b => ‖τ₁ b‖ + ‖τ₂ b‖) (fun _ _ => by positivity) ha
  have hη : ε / (2 * (M + 1)) * (‖τ₁ a‖ + ‖τ₂ a‖) < ε / 2 := by
    calc ε / (2 * (M + 1)) * (‖τ₁ a‖ + ‖τ₂ a‖) ≤ ε / (2 * (M + 1)) * M := by gcongr
      _ < ε / (2 * (M + 1)) * (M + 1) := by gcongr; linarith
      _ = ε / 2 := by field_simp
  linarith [max_lt (r₁ a ha) (r₂ a ha)]

/-- **Convex combinations of amenable traces.** If `τ₁` and `τ₂` are amenable traces and
`τ = θ τ₁ + (1 - θ) τ₂` with `θ ∈ [0, 1]`, then `τ` is amenable. -/
private theorem IsAmenableTrace.of_apply_eq {τ₁ τ₂ : A →P[ℂ] ℂ} (h₁ : τ₁.IsAmenableTrace)
    (h₂ : τ₂.IsAmenableTrace) {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hτ : ∀ a, τ a = θ * τ₁ a + (1 - θ) * τ₂ a) : τ.IsAmenableTrace :=
  forall_approxBy_recoverOn_of_apply_eq (fun φ₁ φ₂ c₁ c₂ _ hη =>
    let ⟨K, Φ, c, m, _, r⟩ := exists_approximant_of_apply_eq hθ₀ hθ₁ hτ φ₁ φ₂ c₁ c₂ hη
    ⟨K, Φ, c, m, r⟩) h₁ h₂

/-- **Convex combinations of quasidiagonal traces.** If `τ₁` and `τ₂` are quasidiagonal traces
and `τ = θ τ₁ + (1 - θ) τ₂` with `θ ∈ [0, 1]`, then `τ` is quasidiagonal. -/
private theorem IsQuasidiagonalTrace.of_apply_eq {τ₁ τ₂ : A →P[ℂ] ℂ}
    (h₁ : τ₁.IsQuasidiagonalTrace) (h₂ : τ₂.IsQuasidiagonalTrace) {θ : ℝ} (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) (hτ : ∀ a, τ a = θ * τ₁ a + (1 - θ) * τ₂ a) : τ.IsQuasidiagonalTrace :=
  forall_approxBy_recoverOn_of_apply_eq (d := fun _ => norm) (fun φ₁ φ₂ c₁ c₂ _ hη =>
    let ⟨K, Φ, c, _, n, r⟩ := exists_approximant_of_apply_eq hθ₀ hθ₁ hτ φ₁ φ₂ c₁ c₂ hη
    ⟨K, Φ, c, n, r⟩) h₁ h₂

/-- **Convex combinations of uniform amenable traces.** If `τ₁` and `τ₂` are uniform amenable
traces and `τ = θ τ₁ + (1 - θ) τ₂` with `θ ∈ [0, 1]`, then `τ` is uniform amenable; the extra
recovery error `η (|τ₁ a| + |τ₂ a|)` is at most `η (‖τ₁‖ + ‖τ₂‖) ‖a‖`. -/
private theorem IsUniformAmenableTrace.of_apply_eq {τ₁ τ₂ : A →P[ℂ] ℂ}
    (h₁ : τ₁.IsUniformAmenableTrace) (h₂ : τ₂.IsUniformAmenableTrace) {θ : ℝ} (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) (hτ : ∀ a, τ a = θ * τ₁ a + (1 - θ) * τ₂ a) : τ.IsUniformAmenableTrace := by
  intro F ε hε
  set C := ‖(τ₁ : A →L[ℂ] ℂ)‖ + ‖(τ₂ : A →L[ℂ] ℂ)‖
  have hC : 0 ≤ C := by positivity
  obtain ⟨k₁, φ₁, c₁, m₁, r₁⟩ := h₁ F (ε / 2) (half_pos hε)
  obtain ⟨k₂, φ₂, c₂, m₂, r₂⟩ := h₂ F (ε / 2) (half_pos hε)
  obtain ⟨K, Φ, c, m, -, r⟩ :=
    exists_approximant_of_apply_eq hθ₀ hθ₁ hτ φ₁ φ₂ c₁ c₂ (η := ε / (2 * (C + 1))) (by positivity)
  refine ⟨K, Φ, c, fun a ha b hb => (m a b).trans_lt
    ((max_lt (m₁ a ha b hb) (m₂ a ha b hb)).trans (half_lt_self hε)), fun a => (r a).trans ?_⟩
  have hτa : ‖τ₁ a‖ + ‖τ₂ a‖ ≤ C * ‖a‖ := by
    rw [add_mul]
    exact add_le_add (by simpa using (τ₁ : A →L[ℂ] ℂ).le_opNorm a)
      (by simpa using (τ₂ : A →L[ℂ] ℂ).le_opNorm a)
  have hη : ε / (2 * (C + 1)) * (‖τ₁ a‖ + ‖τ₂ a‖) ≤ ε / 2 * ‖a‖ := by
    calc ε / (2 * (C + 1)) * (‖τ₁ a‖ + ‖τ₂ a‖) ≤ ε / (2 * (C + 1)) * (C * ‖a‖) := by gcongr
      _ ≤ ε / (2 * (C + 1)) * ((C + 1) * ‖a‖) := by gcongr; linarith
      _ = ε / 2 * ‖a‖ := by field_simp
  linarith [max_le (r₁ a) (r₂ a)]

end Convex

end PositiveContinuousLinearMap

namespace TauCeti

open PositiveContinuousLinearMap

variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `A` **admits a faithful amenable trace**: some tracial state of `A` is both faithful and
amenable. This is the trace hypothesis of Schafhauser's embedding theorem into simple AF
algebras (Schafhauser 2020, Theorem A). -/
def AdmitsFaithfulAmenableTrace : Prop :=
  ∃ τ : A →P[ℂ] ℂ, τ.IsTracialState ∧ τ.IsFaithfulTrace ∧ τ.IsAmenableTrace

variable {A}

/-- Unfolding lemma for `TauCeti.AdmitsFaithfulAmenableTrace`. -/
theorem admitsFaithfulAmenableTrace_iff : AdmitsFaithfulAmenableTrace A ↔
    ∃ τ : A →P[ℂ] ℂ, τ.IsTracialState ∧ τ.IsFaithfulTrace ∧ τ.IsAmenableTrace :=
  Iff.rfl

/-- The zero algebra admits no faithful amenable trace: it has no tracial state, since every
functional on it has norm `0`. -/
theorem not_admitsFaithfulAmenableTrace_of_subsingleton [Subsingleton A] :
    ¬ AdmitsFaithfulAmenableTrace A :=
  fun ⟨τ, hτ, _⟩ => by simpa [Subsingleton.elim (τ : A →L[ℂ] ℂ) 0] using hτ.norm_eq_one

/-- A faithful amenable tracial state of `B` pulls back along a star isomorphism `e : A ≃ B`. -/
private theorem AdmitsFaithfulAmenableTrace.of_starAlgEquiv {B : Type*} [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] (e : A ≃⋆ₐ[ℂ] B) (h : AdmitsFaithfulAmenableTrace B) :
    AdmitsFaithfulAmenableTrace A :=
  let ⟨σ, hs, hf, ha⟩ := h
  ⟨σ.comp (.ofClass e), hs.comp_of_surjective e e.surjective, hf.comp e e.injective, ha.comp e⟩

/-- Admitting a faithful amenable trace is invariant under star isomorphisms. -/
theorem admitsFaithfulAmenableTrace_congr {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] (e : A ≃⋆ₐ[ℂ] B) :
    AdmitsFaithfulAmenableTrace A ↔ AdmitsFaithfulAmenableTrace B :=
  ⟨AdmitsFaithfulAmenableTrace.of_starAlgEquiv e.symm,
    AdmitsFaithfulAmenableTrace.of_starAlgEquiv e⟩

end TauCeti

namespace CStarMatrix

open PositiveContinuousLinearMap

variable {n : Type*} [Fintype n]

/-- The normalized trace of a nonempty matrix algebra is a tracial state. -/
theorem isTracialState_normalizedTraceMap [Nonempty n] :
    (normalizedTraceMap n).IsTracialState :=
  isTracialState_iff.2 ⟨norm_normalizedTraceMap n, normalizedTraceMap_mul_comm⟩

/-- On `M_k` the identity map is an exact approximant: it is a contraction, its multiplicativity
defect is `d k 0`, and it satisfies any recovery clause that holds for it. -/
private theorem approxBy_id {k : ℕ} {d : ∀ k : ℕ, CStarMatrix (Fin k) (Fin k) ℂ → ℝ}
    {R : Finset (CStarMatrix (Fin k) (Fin k) ℂ) → ℝ →
      ∀ l : ℕ, (CStarMatrix (Fin k) (Fin k) ℂ →CP CStarMatrix (Fin l) (Fin l) ℂ) → Prop}
    {F : Finset (CStarMatrix (Fin k) (Fin k) ℂ)} {ε : ℝ} (hd : d k 0 < ε)
    (hR : R F ε k (CompletelyPositiveMap.id _)) : ApproxBy d R F ε :=
  ⟨k, CompletelyPositiveMap.id _, fun _ => by simp, fun _ _ _ _ => by simpa using hd, hR⟩

/-- The normalized trace of a matrix algebra is a quasidiagonal trace: on `M_k` the identity map
is an exact approximant, and a general finite index type is reindexed to `Fin k`. -/
theorem isQuasidiagonalTrace_normalizedTraceMap : (normalizedTraceMap n).IsQuasidiagonalTrace := by
  have hfin (k : ℕ) : (normalizedTraceMap (Fin k)).IsQuasidiagonalTrace :=
    isQuasidiagonalTrace_iff_approxBy.2 fun _ ε hε =>
      approxBy_id (by simpa using hε) fun _ _ => by simpa using hε
  rw [← normalizedTraceMap_comp_reindexₐ (Fintype.equivFin n)]
  exact (hfin _).comp _

/-- The normalized trace of a matrix algebra is a uniform amenable trace, recovered exactly by
the identity map. -/
theorem isUniformAmenableTrace_normalizedTraceMap :
    (normalizedTraceMap n).IsUniformAmenableTrace := by
  have hfin (k : ℕ) : (normalizedTraceMap (Fin k)).IsUniformAmenableTrace :=
    isUniformAmenableTrace_iff_approxBy.2 fun _ ε hε =>
      approxBy_id (by simpa using hε) fun _ => by simpa using mul_nonneg hε.le (norm_nonneg _)
  rw [← normalizedTraceMap_comp_reindexₐ (Fintype.equivFin n)]
  exact (hfin _).comp _

/-- The normalized trace of a matrix algebra is an amenable trace. -/
theorem isAmenableTrace_normalizedTraceMap : (normalizedTraceMap n).IsAmenableTrace :=
  isQuasidiagonalTrace_normalizedTraceMap.isAmenableTrace

/-- The normalized trace of a matrix algebra is faithful. -/
theorem isFaithfulTrace_normalizedTraceMap : (normalizedTraceMap n).IsFaithfulTrace :=
  isFaithfulTrace_iff.2 fun _ h => normalizedTrace_star_mul_self_eq_zero_iff.1 (by simpa using h)

/-- A nonempty matrix algebra admits a faithful amenable trace: its normalized trace. -/
theorem admitsFaithfulAmenableTrace [Nonempty n] :
    TauCeti.AdmitsFaithfulAmenableTrace (CStarMatrix n n ℂ) :=
  ⟨_, isTracialState_normalizedTraceMap, isFaithfulTrace_normalizedTraceMap,
    isAmenableTrace_normalizedTraceMap⟩

end CStarMatrix

namespace TauCeti

open PositiveContinuousLinearMap

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (A) in
/-- The set `AT(A)` of **amenable traces** of `A`: the amenable tracial states, as a subset of the
weak-* dual. -/
noncomputable def amenableTraces : Set (WeakDual ℂ A) :=
  (fun τ : A →P[ℂ] ℂ => StrongDual.toWeakDual (τ : A →L[ℂ] ℂ)) ''
    {τ | τ.IsTracialState ∧ τ.IsAmenableTrace}

variable (A) in
/-- The set `AT_QD(A)` of **quasidiagonal traces** of `A`: the quasidiagonal tracial states, as a
subset of the weak-* dual. -/
noncomputable def quasidiagonalTraces : Set (WeakDual ℂ A) :=
  (fun τ : A →P[ℂ] ℂ => StrongDual.toWeakDual (τ : A →L[ℂ] ℂ)) ''
    {τ | τ.IsTracialState ∧ τ.IsQuasidiagonalTrace}

variable (A) in
/-- The set `UAT(A)` of **uniform amenable traces** of `A`: the uniform amenable tracial states,
as a subset of the weak-* dual. -/
noncomputable def uniformAmenableTraces : Set (WeakDual ℂ A) :=
  (fun τ : A →P[ℂ] ℂ => StrongDual.toWeakDual (τ : A →L[ℂ] ℂ)) ''
    {τ | τ.IsTracialState ∧ τ.IsUniformAmenableTrace}

/-- A positive functional lies in `AT(A)` exactly when it is an amenable tracial state. -/
@[simp]
theorem toWeakDual_mem_amenableTraces_iff {τ : A →P[ℂ] ℂ} :
    StrongDual.toWeakDual (τ : A →L[ℂ] ℂ) ∈ amenableTraces A ↔
      τ.IsTracialState ∧ τ.IsAmenableTrace :=
  (StrongDual.toWeakDual.injective.comp toContinuousLinearMap_injective).mem_set_image

/-- A positive functional lies in `AT_QD(A)` exactly when it is a quasidiagonal tracial state. -/
@[simp]
theorem toWeakDual_mem_quasidiagonalTraces_iff {τ : A →P[ℂ] ℂ} :
    StrongDual.toWeakDual (τ : A →L[ℂ] ℂ) ∈ quasidiagonalTraces A ↔
      τ.IsTracialState ∧ τ.IsQuasidiagonalTrace :=
  (StrongDual.toWeakDual.injective.comp toContinuousLinearMap_injective).mem_set_image

/-- A positive functional lies in `UAT(A)` exactly when it is a uniform amenable tracial
state. -/
@[simp]
theorem toWeakDual_mem_uniformAmenableTraces_iff {τ : A →P[ℂ] ℂ} :
    StrongDual.toWeakDual (τ : A →L[ℂ] ℂ) ∈ uniformAmenableTraces A ↔
      τ.IsTracialState ∧ τ.IsUniformAmenableTrace :=
  (StrongDual.toWeakDual.injective.comp toContinuousLinearMap_injective).mem_set_image

/-- The elements of `AT(A)` are the functionals induced by amenable tracial states. -/
theorem mem_amenableTraces_iff {φ : WeakDual ℂ A} : φ ∈ amenableTraces A ↔
    ∃ τ : A →P[ℂ] ℂ, τ.IsTracialState ∧ τ.IsAmenableTrace ∧
      StrongDual.toWeakDual (τ : A →L[ℂ] ℂ) = φ :=
  exists_congr fun _ => and_assoc

/-- The elements of `AT_QD(A)` are the functionals induced by quasidiagonal tracial states. -/
theorem mem_quasidiagonalTraces_iff {φ : WeakDual ℂ A} : φ ∈ quasidiagonalTraces A ↔
    ∃ τ : A →P[ℂ] ℂ, τ.IsTracialState ∧ τ.IsQuasidiagonalTrace ∧
      StrongDual.toWeakDual (τ : A →L[ℂ] ℂ) = φ :=
  exists_congr fun _ => and_assoc

/-- The elements of `UAT(A)` are the functionals induced by uniform amenable tracial states. -/
theorem mem_uniformAmenableTraces_iff {φ : WeakDual ℂ A} : φ ∈ uniformAmenableTraces A ↔
    ∃ τ : A →P[ℂ] ℂ, τ.IsTracialState ∧ τ.IsUniformAmenableTrace ∧
      StrongDual.toWeakDual (τ : A →L[ℂ] ℂ) = φ :=
  exists_congr fun _ => and_assoc

/-- Amenable traces are tracial states. -/
theorem amenableTraces_subset_tracialStates : amenableTraces A ⊆ tracialStates A := by
  rintro _ ⟨τ, hτ, rfl⟩
  exact toWeakDual_mem_tracialStates_iff.2 hτ.1

/-- Quasidiagonal traces are tracial states. -/
theorem quasidiagonalTraces_subset_tracialStates : quasidiagonalTraces A ⊆ tracialStates A := by
  rintro _ ⟨τ, hτ, rfl⟩
  exact toWeakDual_mem_tracialStates_iff.2 hτ.1

/-- Uniform amenable traces are tracial states. -/
theorem uniformAmenableTraces_subset_tracialStates :
    uniformAmenableTraces A ⊆ tracialStates A := by
  rintro _ ⟨τ, hτ, rfl⟩
  exact toWeakDual_mem_tracialStates_iff.2 hτ.1

/-- `AT_QD(A) ⊆ AT(A)`: quasidiagonal traces are amenable. -/
theorem quasidiagonalTraces_subset_amenableTraces : quasidiagonalTraces A ⊆ amenableTraces A :=
  image_mono fun _ hτ => ⟨hτ.1, hτ.2.isAmenableTrace⟩

/-- `UAT(A) ⊆ AT(A)`: uniform amenable traces are amenable. -/
theorem uniformAmenableTraces_subset_amenableTraces :
    uniformAmenableTraces A ⊆ amenableTraces A :=
  image_mono fun _ hτ => ⟨hτ.1, hτ.2.isAmenableTrace⟩

/-- The set of tracial states with a property `P` is convex as soon as `P` passes to convex
combinations `θ τ₁ + (1 - θ) τ₂` of tracial states, since `T(A)` is convex. -/
private theorem convex_image_toWeakDual {P : (A →P[ℂ] ℂ) → Prop}
    (hP : ∀ ⦃τ₁ τ₂ τ : A →P[ℂ] ℂ⦄, P τ₁ → P τ₂ → ∀ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 →
      (∀ a, τ a = θ * τ₁ a + (1 - θ) * τ₂ a) → P τ) :
    Convex ℝ ((fun τ : A →P[ℂ] ℂ => StrongDual.toWeakDual (τ : A →L[ℂ] ℂ)) ''
      {τ | τ.IsTracialState ∧ P τ}) := by
  rintro _ ⟨τ₁, ⟨hτ₁, h₁⟩, rfl⟩ _ ⟨τ₂, ⟨hτ₂, h₂⟩, rfl⟩ s t hs ht hst
  obtain rfl : t = 1 - s := by linarith
  obtain ⟨τ, hτ, he⟩ := mem_tracialStates_iff_exists_isTracialState.1 <| convex_tracialStates
    (toWeakDual_mem_tracialStates_iff.2 hτ₁) (toWeakDual_mem_tracialStates_iff.2 hτ₂) hs ht hst
  refine ⟨τ, ⟨hτ, hP h₁ h₂ hs (by linarith) fun a => ?_⟩, he⟩
  calc τ a = (s • StrongDual.toWeakDual (τ₁ : A →L[ℂ] ℂ) +
        (1 - s) • StrongDual.toWeakDual (τ₂ : A →L[ℂ] ℂ)) a := congrArg (fun φ => φ a) he
    -- functionals in the weak-* dual are added and scaled pointwise; Mathlib states this for
    -- `WeakDual` only definitionally (it has no `IsAddApply` or `smul_apply` API), hence `rfl`
    _ = s • τ₁ a + (1 - s) • τ₂ a := rfl
    _ = s * τ₁ a + (1 - s) * τ₂ a := by simp [Complex.real_smul]

/-- **Convexity of `AT(A)`.** Convex combinations of amenable traces are amenable: the
approximants are block-diagonal sums of copies of approximants of the two traces. -/
theorem convex_amenableTraces : Convex ℝ (amenableTraces A) :=
  convex_image_toWeakDual fun _ _ _ h₁ h₂ _ hθ₀ hθ₁ hτ =>
    IsAmenableTrace.of_apply_eq h₁ h₂ hθ₀ hθ₁ hτ

/-- **Convexity of `AT_QD(A)`.** Convex combinations of quasidiagonal traces are quasidiagonal. -/
theorem convex_quasidiagonalTraces : Convex ℝ (quasidiagonalTraces A) :=
  convex_image_toWeakDual fun _ _ _ h₁ h₂ _ hθ₀ hθ₁ hτ =>
    IsQuasidiagonalTrace.of_apply_eq h₁ h₂ hθ₀ hθ₁ hτ

/-- **Convexity of `UAT(A)`.** Convex combinations of uniform amenable traces are uniform
amenable. -/
theorem convex_uniformAmenableTraces : Convex ℝ (uniformAmenableTraces A) :=
  convex_image_toWeakDual fun _ _ _ h₁ h₂ _ hθ₀ hθ₁ hτ =>
    IsUniformAmenableTrace.of_apply_eq h₁ h₂ hθ₀ hθ₁ hτ

/-- A tracial state in the weak-* closure of the tracial states with an approximation property of
amenable or quasidiagonal type has that property: near `τ` on a finite set `F` there is such a
state `σ`, and an approximant of `σ` for `F` approximates `τ` on `F`. -/
private theorem of_mem_closure_image_toWeakDual {d : ∀ k : ℕ, CStarMatrix (Fin k) (Fin k) ℂ → ℝ}
    {P : (A →P[ℂ] ℂ) → Prop}
    (hP : ∀ σ, P σ ↔ ∀ (F : Finset A) (ε : ℝ), 0 < ε → ApproxBy d (RecoverOn σ) F ε)
    {τ : A →P[ℂ] ℂ} (hτ : StrongDual.toWeakDual (τ : A →L[ℂ] ℂ) ∈
      closure ((fun σ : A →P[ℂ] ℂ => StrongDual.toWeakDual (σ : A →L[ℂ] ℂ)) ''
        {σ | σ.IsTracialState ∧ P σ})) :
    P τ := by
  refine (hP τ).2 fun F ε hε => ?_
  let U : Set (WeakDual ℂ A) := ⋂ a ∈ F, {y | ‖y a - τ a‖ < ε / 2}
  have hU : IsOpen U := isOpen_biInter_finset fun a _ =>
    isOpen_lt (continuous_norm.comp ((eval_continuous a).sub continuous_const)) continuous_const
  have hτU : StrongDual.toWeakDual (τ : A →L[ℂ] ℂ) ∈ U :=
    mem_iInter₂.2 fun a _ => by simpa using half_pos hε
  obtain ⟨_, hyU, σ, ⟨-, hσ⟩, rfl⟩ := mem_closure_iff.1 hτ U hU hτU
  obtain ⟨k, φ, hφ, hm, hr⟩ := (hP σ).1 hσ F (ε / 2) (half_pos hε)
  refine ⟨k, φ, hφ, fun a ha b hb => (hm a ha b hb).trans (half_lt_self hε), fun a ha => ?_⟩
  have hστ : ‖σ a - τ a‖ < ε / 2 := by simpa using mem_iInter₂.1 hyU a ha
  calc ‖CStarMatrix.normalizedTrace (φ a) - τ a‖
      ≤ ‖CStarMatrix.normalizedTrace (φ a) - σ a‖ + ‖σ a - τ a‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hr a ha) hστ
    _ = ε := add_halves ε

/-- **`AT(A)` is weak-* closed in `T(A)`.** A tracial state in the weak-* closure of the amenable
traces is amenable. -/
theorem closure_amenableTraces_inter_tracialStates :
    closure (amenableTraces A) ∩ tracialStates A = amenableTraces A := by
  refine Subset.antisymm ?_ (subset_inter subset_closure amenableTraces_subset_tracialStates)
  rintro _ ⟨hcl, hT⟩
  obtain ⟨τ, hτ, rfl⟩ := mem_tracialStates_iff_exists_isTracialState.1 hT
  exact toWeakDual_mem_amenableTraces_iff.2
    ⟨hτ, of_mem_closure_image_toWeakDual (fun _ => isAmenableTrace_iff_approxBy) hcl⟩

/-- **`AT_QD(A)` is weak-* closed in `T(A)`.** A tracial state in the weak-* closure of the
quasidiagonal traces is quasidiagonal. -/
theorem closure_quasidiagonalTraces_inter_tracialStates :
    closure (quasidiagonalTraces A) ∩ tracialStates A = quasidiagonalTraces A := by
  refine Subset.antisymm ?_ (subset_inter subset_closure quasidiagonalTraces_subset_tracialStates)
  rintro _ ⟨hcl, hT⟩
  obtain ⟨τ, hτ, rfl⟩ := mem_tracialStates_iff_exists_isTracialState.1 hT
  exact toWeakDual_mem_quasidiagonalTraces_iff.2
    ⟨hτ, of_mem_closure_image_toWeakDual (fun _ => isQuasidiagonalTrace_iff_approxBy) hcl⟩

/-- **`UAT(A)` is norm closed.** In the norm topology of the continuous dual, the uniform amenable
traces form a closed set: if `‖σ - τ‖ ≤ ε / 2`, an approximant of `σ` with recovery error
`(ε / 2)‖a‖` recovers `τ` with error `ε ‖a‖`. -/
theorem isClosed_preimage_toWeakDual_uniformAmenableTraces :
    IsClosed (StrongDual.toWeakDual ⁻¹' uniformAmenableTraces A) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  have hT : StrongDual.toWeakDual x ∈ tracialStates A := mem_preimage.1 <|
    closure_minimal (preimage_mono uniformAmenableTraces_subset_tracialStates)
      isClosed_preimage_toWeakDual_tracialStates hx
  obtain ⟨τ, hτ, he⟩ := mem_tracialStates_iff_exists_isTracialState.1 hT
  have hτx : (τ : A →L[ℂ] ℂ) = x := StrongDual.toWeakDual.injective he
  rw [mem_preimage, ← hτx, toWeakDual_mem_uniformAmenableTraces_iff]
  refine ⟨hτ, fun F ε hε => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx (ε / 2) (half_pos hε)
  obtain ⟨σ, -, hσ, hσy⟩ := mem_uniformAmenableTraces_iff.1 (mem_preimage.1 hy)
  have hσy' : (σ : A →L[ℂ] ℂ) = y := StrongDual.toWeakDual.injective hσy
  obtain ⟨k, φ, hφ, hm, hr⟩ := hσ F (ε / 2) (half_pos hε)
  refine ⟨k, φ, hφ, fun a ha b hb => (hm a ha b hb).trans (half_lt_self hε), fun a => ?_⟩
  have hστ : ‖σ a - τ a‖ ≤ ε / 2 * ‖a‖ := by
    have h : σ a - τ a = (y - x) a := by rw [← hσy', ← hτx]; simp
    rw [h]
    refine ((y - x).le_opNorm a).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg a))
    rw [← dist_eq_norm, dist_comm]
    exact hxy.le
  calc ‖CStarMatrix.normalizedTrace (φ a) - τ a‖
      ≤ ‖CStarMatrix.normalizedTrace (φ a) - σ a‖ + ‖σ a - τ a‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε / 2 * ‖a‖ + ε / 2 * ‖a‖ := add_le_add (hr a) hστ
    _ = ε * ‖a‖ := by ring

variable {B F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B] {φ : WeakDual ℂ B}

/-- The restriction along `f` of the functional of a tracial state of `B` with a property `PB`
is the functional of a tracial state of `A` with a property `PA`, as soon as it is a state and `PB`
passes to `PA` under composition with `f`. -/
private theorem pullbackFunctional_mem_image {PA : (A →P[ℂ] ℂ) → Prop}
    {PB : (B →P[ℂ] ℂ) → Prop} (f : F) (hP : ∀ σ, PB σ → PA (σ.comp (.ofClass f)))
    (hφ : φ ∈ (fun σ : B →P[ℂ] ℂ => StrongDual.toWeakDual (σ : B →L[ℂ] ℂ)) ''
      {σ | σ.IsTracialState ∧ PB σ})
    (hf : pullbackFunctional A f φ ∈ stateSpace A) :
    pullbackFunctional A f φ ∈ (fun τ : A →P[ℂ] ℂ => StrongDual.toWeakDual (τ : A →L[ℂ] ℂ)) ''
      {τ | τ.IsTracialState ∧ PA τ} := by
  obtain ⟨σ, ⟨hσ, hσ'⟩, rfl⟩ := hφ
  rw [pullbackFunctional_toWeakDual, toWeakDual_mem_stateSpace_iff] at hf
  rw [pullbackFunctional_toWeakDual]
  exact ⟨_, ⟨hσ.comp_of_norm_eq_one f hf, hP σ hσ'⟩, rfl⟩

/-- **Pullback of amenable traces.** If `φ ∈ AT(B)` and its restriction along a star
homomorphism `f : A → B` is a state, then that restriction lies in `AT(A)`. -/
theorem pullbackFunctional_mem_amenableTraces (f : F) (hφ : φ ∈ amenableTraces B)
    (hf : pullbackFunctional A f φ ∈ stateSpace A) :
    pullbackFunctional A f φ ∈ amenableTraces A :=
  pullbackFunctional_mem_image f (fun _ h => h.comp f) hφ hf

/-- **Pullback of quasidiagonal traces.** If `φ ∈ AT_QD(B)` and its restriction along a star
homomorphism `f : A → B` is a state, then that restriction lies in `AT_QD(A)`. -/
theorem pullbackFunctional_mem_quasidiagonalTraces (f : F) (hφ : φ ∈ quasidiagonalTraces B)
    (hf : pullbackFunctional A f φ ∈ stateSpace A) :
    pullbackFunctional A f φ ∈ quasidiagonalTraces A :=
  pullbackFunctional_mem_image f (fun _ h => h.comp f) hφ hf

/-- **Pullback of uniform amenable traces.** If `φ ∈ UAT(B)` and its restriction along a star
homomorphism `f : A → B` is a state, then that restriction lies in `UAT(A)`. -/
theorem pullbackFunctional_mem_uniformAmenableTraces (f : F) (hφ : φ ∈ uniformAmenableTraces B)
    (hf : pullbackFunctional A f φ ∈ stateSpace A) :
    pullbackFunctional A f φ ∈ uniformAmenableTraces A :=
  pullbackFunctional_mem_image f (fun _ h => h.comp f) hφ hf

/-- **Lifting amenable traces from quotients.** Precomposition with a surjective star
homomorphism `A → B` maps `AT(B)` to `AT(A)`. -/
theorem mapsTo_pullbackFunctional_amenableTraces_of_surjective (f : F)
    (hf : Function.Surjective f) :
    MapsTo (pullbackFunctional A f) (amenableTraces B) (amenableTraces A) := fun _ hφ =>
  pullbackFunctional_mem_amenableTraces f hφ <| mapsTo_pullbackFunctional_stateSpace_of_surjective
    f hf <| tracialStates_subset_stateSpace <| amenableTraces_subset_tracialStates hφ

/-- **Lifting quasidiagonal traces from quotients.** Precomposition with a surjective star
homomorphism `A → B` maps `AT_QD(B)` to `AT_QD(A)`. -/
theorem mapsTo_pullbackFunctional_quasidiagonalTraces_of_surjective (f : F)
    (hf : Function.Surjective f) :
    MapsTo (pullbackFunctional A f) (quasidiagonalTraces B) (quasidiagonalTraces A) := fun _ hφ =>
  pullbackFunctional_mem_quasidiagonalTraces f hφ <|
    mapsTo_pullbackFunctional_stateSpace_of_surjective f hf <| tracialStates_subset_stateSpace <|
      quasidiagonalTraces_subset_tracialStates hφ

/-- **Lifting uniform amenable traces from quotients.** Precomposition with a surjective star
homomorphism `A → B` maps `UAT(B)` to `UAT(A)`. -/
theorem mapsTo_pullbackFunctional_uniformAmenableTraces_of_surjective (f : F)
    (hf : Function.Surjective f) :
    MapsTo (pullbackFunctional A f) (uniformAmenableTraces B) (uniformAmenableTraces A) :=
  fun _ hφ => pullbackFunctional_mem_uniformAmenableTraces f hφ <|
    mapsTo_pullbackFunctional_stateSpace_of_surjective f hf <| tracialStates_subset_stateSpace <|
      uniformAmenableTraces_subset_tracialStates hφ

end NonUnital

section Unital

variable {A B F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [AlgHomClass F ℂ A B] [StarHomClass F A B]

/-- **Restriction of amenable traces.** Precomposition with a unital star homomorphism `A → B`
maps `AT(B)` to `AT(A)`; in particular amenable traces restrict to unital C⋆-subalgebras. -/
theorem mapsTo_pullbackFunctional_amenableTraces (f : F) :
    MapsTo (pullbackFunctional A f) (amenableTraces B) (amenableTraces A) := fun _ hφ =>
  pullbackFunctional_mem_amenableTraces f hφ <| mapsTo_pullbackFunctional_stateSpace f <|
    tracialStates_subset_stateSpace <| amenableTraces_subset_tracialStates hφ

/-- **Restriction of quasidiagonal traces.** Precomposition with a unital star homomorphism
`A → B` maps `AT_QD(B)` to `AT_QD(A)`. -/
theorem mapsTo_pullbackFunctional_quasidiagonalTraces (f : F) :
    MapsTo (pullbackFunctional A f) (quasidiagonalTraces B) (quasidiagonalTraces A) := fun _ hφ =>
  pullbackFunctional_mem_quasidiagonalTraces f hφ <| mapsTo_pullbackFunctional_stateSpace f <|
    tracialStates_subset_stateSpace <| quasidiagonalTraces_subset_tracialStates hφ

/-- **Restriction of uniform amenable traces.** Precomposition with a unital star homomorphism
`A → B` maps `UAT(B)` to `UAT(A)`. -/
theorem mapsTo_pullbackFunctional_uniformAmenableTraces (f : F) :
    MapsTo (pullbackFunctional A f) (uniformAmenableTraces B) (uniformAmenableTraces A) :=
  fun _ hφ => pullbackFunctional_mem_uniformAmenableTraces f hφ <|
    mapsTo_pullbackFunctional_stateSpace f <| tracialStates_subset_stateSpace <|
      uniformAmenableTraces_subset_tracialStates hφ

/-- For unital `A`, the set `AT(A)` of amenable traces is weak-* closed, as `T(A)` is. -/
theorem isClosed_amenableTraces : IsClosed (amenableTraces A) :=
  isClosed_of_closure_subset fun _ hx => closure_amenableTraces_inter_tracialStates (A := A) ▸
    ⟨hx, closure_minimal amenableTraces_subset_tracialStates isClosed_tracialStates hx⟩

/-- For unital `A`, the set `AT_QD(A)` of quasidiagonal traces is weak-* closed, as `T(A)` is. -/
theorem isClosed_quasidiagonalTraces : IsClosed (quasidiagonalTraces A) :=
  isClosed_of_closure_subset fun _ hx => closure_quasidiagonalTraces_inter_tracialStates (A := A) ▸
    ⟨hx, closure_minimal quasidiagonalTraces_subset_tracialStates isClosed_tracialStates hx⟩

end Unital

end TauCeti
