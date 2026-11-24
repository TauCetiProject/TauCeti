/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Order
public import TauCeti.Analysis.CStarAlgebra.Matrix.Trace
public import TauCeti.Analysis.CStarAlgebra.State.Tracial

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
* `TauCeti.pullbackFunctional_mem_amenableTraces` and its siblings: the restriction of an element
  of each of the three sets along a star homomorphism lies in the corresponding set as soon as it
  is a state. Hence `TauCeti.mapsTo_pullbackFunctional_amenableTraces_of_surjective` and its
  siblings lift the three sets from quotients, and
  `TauCeti.mapsTo_pullbackFunctional_amenableTraces` and its siblings restrict them along unital
  star homomorphisms of unital algebras.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*,
  Mem. Amer. Math. Soc. 184 (2006), no. 865; arXiv:math/0304009v2 (numbering cited),
  Theorem 3.1.6 (2), Definitions 3.2.1 and 3.3.1, Section 3.5.
* A. Tikuisis, S. White, W. Winter, *Quasidiagonality of nuclear C⋆-algebras*, Ann. of Math.
  185 (2017), Definition 1.2 and Remark 1.5.
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

/-- **Monotonicity of amenability.** A witness for `(F', ε')` is a witness for every `F ⊆ F'`
and `ε ≥ ε'`, so it suffices to find, for each `(F, ε)`, a witness for some larger finite set
and some smaller error. -/
theorem isAmenableTrace_iff_exists_superset : τ.IsAmenableTrace ↔
    ∀ (F : Finset A) (ε : ℝ), 0 < ε → ∃ F' : Finset A, F ⊆ F' ∧ ∃ ε' ≤ ε,
      ∃ (k : ℕ) (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ), (∀ a, ‖φ a‖ ≤ ‖a‖) ∧
      (∀ a ∈ F', ∀ b ∈ F', CStarMatrix.normalizedTwoNorm (φ (a * b) - φ a * φ b) < ε') ∧
      ∀ a ∈ F', ‖CStarMatrix.normalizedTrace (φ a) - τ a‖ < ε' :=
  ⟨fun h F ε hε => ⟨F, subset_rfl, ε, le_rfl, h F ε hε⟩, fun h F ε hε => by
    obtain ⟨F', hF, ε', hε', k, φ, hφ, hmul, htr⟩ := h F ε hε
    exact ⟨k, φ, hφ, fun a ha b hb => (hmul a (hF ha) b (hF hb)).trans_le hε',
      fun a ha => (htr a (hF ha)).trans_le hε'⟩⟩

/-- **Monotonicity of quasidiagonality.** A witness for `(F', ε')` is a witness for every
`F ⊆ F'` and `ε ≥ ε'`. -/
theorem isQuasidiagonalTrace_iff_exists_superset : τ.IsQuasidiagonalTrace ↔
    ∀ (F : Finset A) (ε : ℝ), 0 < ε → ∃ F' : Finset A, F ⊆ F' ∧ ∃ ε' ≤ ε,
      ∃ (k : ℕ) (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ), (∀ a, ‖φ a‖ ≤ ‖a‖) ∧
      (∀ a ∈ F', ∀ b ∈ F', ‖φ (a * b) - φ a * φ b‖ < ε') ∧
      ∀ a ∈ F', ‖CStarMatrix.normalizedTrace (φ a) - τ a‖ < ε' :=
  ⟨fun h F ε hε => ⟨F, subset_rfl, ε, le_rfl, h F ε hε⟩, fun h F ε hε => by
    obtain ⟨F', hF, ε', hε', k, φ, hφ, hmul, htr⟩ := h F ε hε
    exact ⟨k, φ, hφ, fun a ha b hb => (hmul a (hF ha) b (hF hb)).trans_le hε',
      fun a ha => (htr a (hF ha)).trans_le hε'⟩⟩

/-- **Monotonicity of uniform amenability.** A witness for `(F', ε')` is a witness for every
`F ⊆ F'` and `ε ≥ ε'`. -/
theorem isUniformAmenableTrace_iff_exists_superset : τ.IsUniformAmenableTrace ↔
    ∀ (F : Finset A) (ε : ℝ), 0 < ε → ∃ F' : Finset A, F ⊆ F' ∧ ∃ ε' ≤ ε,
      ∃ (k : ℕ) (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ), (∀ a, ‖φ a‖ ≤ ‖a‖) ∧
      (∀ a ∈ F', ∀ b ∈ F', CStarMatrix.normalizedTwoNorm (φ (a * b) - φ a * φ b) < ε') ∧
      ∀ a, ‖CStarMatrix.normalizedTrace (φ a) - τ a‖ ≤ ε' * ‖a‖ :=
  ⟨fun h F ε hε => ⟨F, subset_rfl, ε, le_rfl, h F ε hε⟩, fun h F ε hε => by
    obtain ⟨F', hF, ε', hε', k, φ, hφ, hmul, htr⟩ := h F ε hε
    exact ⟨k, φ, hφ, fun a ha b hb => (hmul a (hF ha) b (hF hb)).trans_le hε',
      fun a => (htr a).trans (mul_le_mul_of_nonneg_right hε' (norm_nonneg a))⟩⟩

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

/-- Composing an approximant `φ` of a trace of `B` with a star homomorphism `f : A → B` gives a
contraction which is as multiplicative on `S` as `φ` is on `f '' S`, for any measure `d` of the
multiplicativity defect. -/
private theorem comp_approx (d : ∀ k : ℕ, CStarMatrix (Fin k) (Fin k) ℂ → ℝ) (f : F)
    [DecidableEq B] {S : Finset A} {ε : ℝ} {k : ℕ} {φ : B →CP CStarMatrix (Fin k) (Fin k) ℂ}
    (hφ : ∀ b, ‖φ b‖ ≤ ‖b‖)
    (hmul : ∀ a ∈ S.image f, ∀ b ∈ S.image f, d k (φ (a * b) - φ a * φ b) < ε) :
    (∀ a, ‖φ.comp (f : A →CP B) a‖ ≤ ‖a‖) ∧ ∀ a ∈ S, ∀ b ∈ S,
      d k (φ.comp (f : A →CP B) (a * b) - φ.comp (f : A →CP B) a * φ.comp (f : A →CP B) b) < ε :=
  ⟨fun a => by simpa using (hφ (f a)).trans (NonUnitalStarAlgHom.norm_apply_le f a),
    fun a ha b hb => by
      simpa using hmul (f a) (Finset.mem_image_of_mem f ha) (f b) (Finset.mem_image_of_mem f hb)⟩

/-- **Pullback of amenable traces.** If `σ` is an amenable trace of `B`, then so is its composite
with any star homomorphism `f : A → B`: an approximant `φ` of `σ` gives the approximant
`φ ∘ f` of `σ ∘ f`. The composite is a tracial state only under a norm condition, see
`PositiveContinuousLinearMap.IsTracialState.comp_of_norm_eq_one`. -/
theorem IsAmenableTrace.comp (hσ : σ.IsAmenableTrace) (f : F) :
    (σ.comp (.ofClass f)).IsAmenableTrace := by
  classical
  intro S ε hε
  obtain ⟨k, φ, hφ, hmul, htr⟩ := hσ (S.image f) ε hε
  obtain ⟨hφ', hmul'⟩ := comp_approx (fun _ => CStarMatrix.normalizedTwoNorm) f hφ hmul
  exact ⟨k, _, hφ', hmul', fun a ha => by simpa using htr (f a) (Finset.mem_image_of_mem f ha)⟩

/-- **Pullback of quasidiagonal traces** along any star homomorphism `f : A → B`. -/
theorem IsQuasidiagonalTrace.comp (hσ : σ.IsQuasidiagonalTrace) (f : F) :
    (σ.comp (.ofClass f)).IsQuasidiagonalTrace := by
  classical
  intro S ε hε
  obtain ⟨k, φ, hφ, hmul, htr⟩ := hσ (S.image f) ε hε
  obtain ⟨hφ', hmul'⟩ := comp_approx (fun _ => norm) f hφ hmul
  exact ⟨k, _, hφ', hmul', fun a ha => by simpa using htr (f a) (Finset.mem_image_of_mem f ha)⟩

/-- **Pullback of uniform amenable traces** along any star homomorphism `f : A → B`; the
recovery error at `a` is the error of `σ` at `f a`, and `‖f a‖ ≤ ‖a‖`. -/
theorem IsUniformAmenableTrace.comp (hσ : σ.IsUniformAmenableTrace) (f : F) :
    (σ.comp (.ofClass f)).IsUniformAmenableTrace := by
  classical
  intro S ε hε
  obtain ⟨k, φ, hφ, hmul, htr⟩ := hσ (S.image f) ε hε
  obtain ⟨hφ', hmul'⟩ := comp_approx (fun _ => CStarMatrix.normalizedTwoNorm) f hφ hmul
  refine ⟨k, _, hφ', hmul', fun a => ?_⟩
  simpa using (htr (f a)).trans
    (mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le f a) hε.le)

/-- Amenability of traces is invariant under star isomorphisms. -/
theorem isAmenableTrace_comp_iff (e : A ≃⋆ₐ[ℂ] B) :
    (σ.comp (.ofClass e)).IsAmenableTrace ↔ σ.IsAmenableTrace := by
  refine ⟨fun h => ?_, fun h => h.comp e⟩
  convert h.comp e.symm using 1
  ext b
  simp

/-- Quasidiagonality of traces is invariant under star isomorphisms. -/
theorem isQuasidiagonalTrace_comp_iff (e : A ≃⋆ₐ[ℂ] B) :
    (σ.comp (.ofClass e)).IsQuasidiagonalTrace ↔ σ.IsQuasidiagonalTrace := by
  refine ⟨fun h => ?_, fun h => h.comp e⟩
  convert h.comp e.symm using 1
  ext b
  simp

/-- Uniform amenability of traces is invariant under star isomorphisms. -/
theorem isUniformAmenableTrace_comp_iff (e : A ≃⋆ₐ[ℂ] B) :
    (σ.comp (.ofClass e)).IsUniformAmenableTrace ↔ σ.IsUniformAmenableTrace := by
  refine ⟨fun h => ?_, fun h => h.comp e⟩
  convert h.comp e.symm using 1
  ext b
  simp

end Pullback

end PositiveContinuousLinearMap

namespace CStarMatrix

open PositiveContinuousLinearMap

variable {n : Type*} [Fintype n]

/-- The normalized trace of a nonempty matrix algebra is a tracial state. -/
theorem isTracialState_normalizedTraceMap [Nonempty n] :
    (normalizedTraceMap n).IsTracialState :=
  isTracialState_iff.2 ⟨norm_normalizedTraceMap n, fun x y => by
    simpa using normalizedTrace_mul_comm x y⟩

/-- The normalized trace of a matrix algebra is a quasidiagonal trace: on `M_k` the identity map
is an exact approximant, and a general finite index type is reindexed to `Fin k`. -/
theorem isQuasidiagonalTrace_normalizedTraceMap : (normalizedTraceMap n).IsQuasidiagonalTrace := by
  have hfin (k : ℕ) : (normalizedTraceMap (Fin k)).IsQuasidiagonalTrace := fun F ε hε =>
    ⟨k, CompletelyPositiveMap.id _, fun _ => by simp, fun _ _ _ _ => by simpa using hε,
      fun _ _ => by simpa using hε⟩
  rw [← normalizedTraceMap_comp_reindexₐ (Fintype.equivFin n)]
  exact (hfin _).comp _

/-- The normalized trace of a matrix algebra is a uniform amenable trace, recovered exactly by
the identity map. -/
theorem isUniformAmenableTrace_normalizedTraceMap :
    (normalizedTraceMap n).IsUniformAmenableTrace := by
  have hfin (k : ℕ) : (normalizedTraceMap (Fin k)).IsUniformAmenableTrace := fun F ε hε =>
    ⟨k, CompletelyPositiveMap.id _, fun _ => by simp, fun _ _ _ _ => by simpa using hε,
      fun _ => by simpa using mul_nonneg hε.le (norm_nonneg _)⟩
  rw [← normalizedTraceMap_comp_reindexₐ (Fintype.equivFin n)]
  exact (hfin _).comp _

/-- The normalized trace of a matrix algebra is an amenable trace. -/
theorem isAmenableTrace_normalizedTraceMap : (normalizedTraceMap n).IsAmenableTrace :=
  isQuasidiagonalTrace_normalizedTraceMap.isAmenableTrace

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

variable {B F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B] {φ : WeakDual ℂ B}

/-- Restricting the functional induced by `σ` along `f` gives the functional induced by
`σ ∘ f`. -/
private theorem pullbackFunctional_toWeakDual (f : F) (σ : B →P[ℂ] ℂ) :
    pullbackFunctional A f (StrongDual.toWeakDual (σ : B →L[ℂ] ℂ)) =
      StrongDual.toWeakDual ((σ.comp (.ofClass f) : A →P[ℂ] ℂ) : A →L[ℂ] ℂ) :=
  DFunLike.ext _ _ fun _ => by simp

/-- **Pullback of amenable traces.** If `φ ∈ AT(B)` and its restriction along a star
homomorphism `f : A → B` is a state, then that restriction lies in `AT(A)`. -/
theorem pullbackFunctional_mem_amenableTraces (f : F) (hφ : φ ∈ amenableTraces B)
    (hf : pullbackFunctional A f φ ∈ stateSpace A) :
    pullbackFunctional A f φ ∈ amenableTraces A := by
  obtain ⟨σ, hσ, hσ', rfl⟩ := mem_amenableTraces_iff.1 hφ
  rw [pullbackFunctional_toWeakDual, toWeakDual_mem_stateSpace_iff] at hf
  rw [pullbackFunctional_toWeakDual, toWeakDual_mem_amenableTraces_iff]
  exact ⟨hσ.comp_of_norm_eq_one f hf, hσ'.comp f⟩

/-- **Pullback of quasidiagonal traces.** If `φ ∈ AT_QD(B)` and its restriction along a star
homomorphism `f : A → B` is a state, then that restriction lies in `AT_QD(A)`. -/
theorem pullbackFunctional_mem_quasidiagonalTraces (f : F) (hφ : φ ∈ quasidiagonalTraces B)
    (hf : pullbackFunctional A f φ ∈ stateSpace A) :
    pullbackFunctional A f φ ∈ quasidiagonalTraces A := by
  obtain ⟨σ, hσ, hσ', rfl⟩ := mem_quasidiagonalTraces_iff.1 hφ
  rw [pullbackFunctional_toWeakDual, toWeakDual_mem_stateSpace_iff] at hf
  rw [pullbackFunctional_toWeakDual, toWeakDual_mem_quasidiagonalTraces_iff]
  exact ⟨hσ.comp_of_norm_eq_one f hf, hσ'.comp f⟩

/-- **Pullback of uniform amenable traces.** If `φ ∈ UAT(B)` and its restriction along a star
homomorphism `f : A → B` is a state, then that restriction lies in `UAT(A)`. -/
theorem pullbackFunctional_mem_uniformAmenableTraces (f : F) (hφ : φ ∈ uniformAmenableTraces B)
    (hf : pullbackFunctional A f φ ∈ stateSpace A) :
    pullbackFunctional A f φ ∈ uniformAmenableTraces A := by
  obtain ⟨σ, hσ, hσ', rfl⟩ := mem_uniformAmenableTraces_iff.1 hφ
  rw [pullbackFunctional_toWeakDual, toWeakDual_mem_stateSpace_iff] at hf
  rw [pullbackFunctional_toWeakDual, toWeakDual_mem_uniformAmenableTraces_iff]
  exact ⟨hσ.comp_of_norm_eq_one f hf, hσ'.comp f⟩

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

end Unital

end TauCeti
