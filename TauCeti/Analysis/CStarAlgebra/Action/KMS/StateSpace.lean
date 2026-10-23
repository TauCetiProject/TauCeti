/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.KMS.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import TauCeti.Analysis.CStarAlgebra.Action.KMS.Dense
import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# The weak-* topology and convexity of the set of KMS states

For a real action `α` on a C⋆-algebra `A` and an inverse temperature `β`, `kmsStates α β` is
the set `K_β` of β-KMS states of `α`, viewed in the weak-* dual `WeakDual ℂ A`.

Membership is characterised by the analytic KMS identity on entire analytic elements,
`mem_kmsStates_iff_forall_isEntireAnalytic`. Since this identity is linear in the functional
and is preserved under pointwise limits, it gives the following.

* `IsKMSState.of_tendsto`: a pointwise limit of β-KMS states is a β-KMS state as soon as it
  has norm one. The norm condition cannot be dropped for nonunital `A`, where states may
  converge weak-* to `0`. In set form this is `closure_kmsStates_inter_subset`.
* `convex_kmsStates`: `K_β` is convex. No identity element is needed, because the norm of a
  positive functional is its limit along an approximate unit.
* For unital `A`, `K_β` is weak-* closed, `isClosed_kmsStates`, and weak-* compact,
  `isCompact_kmsStates`, by the Banach--Alaoglu theorem.

## References

Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second edition,
Theorem 5.3.30.
-/

public section

open Complex Set Filter WeakDual
open scoped ComplexOrder Topology

namespace TauCeti.CStarAction

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {α : CStarAction (Multiplicative ℝ) A} {β : ℝ} {ω : A →P[ℂ] ℂ}

/-- **Pointwise limits of KMS states.** If β-KMS states converge pointwise to a positive
functional of norm one, then the limit is a β-KMS state. -/
theorem IsKMSState.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {ω' : ι → A →P[ℂ] ℂ}
    (hω' : ∀ᶠ i in l, α.IsKMSState β (ω' i)) (hlim : ∀ a, Tendsto (fun i => ω' i a) l (𝓝 (ω a)))
    (hnorm : ‖(ω : A →L[ℂ] ℂ)‖ = 1) : α.IsKMSState β ω := by
  refine isKMSState_iff_forall_isEntireAnalytic.mpr ⟨hnorm, fun a _ b hb => ?_⟩
  exact tendsto_nhds_unique ((hlim _).congr' <| hω'.mono fun i hi =>
    hi.apply_mul_entireExtension_mul_I a hb) (hlim _)

variable (α β) in
/-- The set `K_β` of β-KMS states of the real action `α`, as a subset of the weak-* dual of `A`.
-/
noncomputable def kmsStates : Set (WeakDual ℂ A) :=
  (fun ω : A →P[ℂ] ℂ => StrongDual.toWeakDual (ω : A →L[ℂ] ℂ)) '' {ω | α.IsKMSState β ω}

/-- The elements of `K_β` are the images in the weak-* dual of the β-KMS states. -/
theorem mem_kmsStates_iff {φ : WeakDual ℂ A} :
    φ ∈ α.kmsStates β ↔ ∃ ω : A →P[ℂ] ℂ, α.IsKMSState β ω ∧
      StrongDual.toWeakDual (ω : A →L[ℂ] ℂ) = φ :=
  Iff.rfl

/-- A positive functional lies in `K_β` exactly when it is a β-KMS state. -/
@[simp]
theorem toWeakDual_mem_kmsStates_iff :
    StrongDual.toWeakDual (ω : A →L[ℂ] ℂ) ∈ α.kmsStates β ↔ α.IsKMSState β ω := by
  refine ⟨fun ⟨ω', hω', h⟩ => ?_, fun hω => ⟨ω, hω, rfl⟩⟩
  rwa [← PositiveContinuousLinearMap.toContinuousLinearMap_injective
    (StrongDual.toWeakDual.injective h)]

/-- **Analytic description of `K_β`.** A functional lies in `K_β` exactly when it is positive,
has norm one, and satisfies the analytic KMS identity `φ (a α_{iβ}(b)) = φ (b a)` for all
entire analytic `a` and `b`. -/
theorem mem_kmsStates_iff_forall_isEntireAnalytic {φ : WeakDual ℂ A} :
    φ ∈ α.kmsStates β ↔ (∀ a, 0 ≤ a → 0 ≤ φ a) ∧ ‖toStrongDual φ‖ = 1 ∧
      ∀ a, α.IsEntireAnalytic a → ∀ b, α.IsEntireAnalytic b →
        φ (a * α.entireExtension b (β * I)) = φ (b * a) := by
  constructor
  · rintro ⟨ω, hω, rfl⟩
    exact ⟨fun a ha => ω.map_nonneg ha, isKMSState_iff_forall_isEntireAnalytic.mp hω⟩
  · rintro ⟨hpos, hφ⟩
    refine ⟨.mk₀ (toStrongDual φ) fun a ha => (hpos a ha).trans_eq (toStrongDual_apply φ a).symm,
      isKMSState_iff_forall_isEntireAnalytic.mpr ?_, ?_⟩
    · simpa using hφ
    · simp

omit [StarOrderedRing A] in
/-- The positive functionals form a weak-* closed set. -/
private theorem isClosed_setOf_nonneg :
    IsClosed {φ : WeakDual ℂ A | ∀ a, 0 ≤ a → 0 ≤ φ a} := by
  simp only [ofPred_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun _ => isClosed_le continuous_const
    (eval_continuous a)

omit [PartialOrder A] [StarOrderedRing A] in
/-- The functionals satisfying the analytic KMS identity form a weak-* closed set. -/
private theorem isClosed_setOf_apply_mul_entireExtension_eq (α : CStarAction (Multiplicative ℝ) A)
    (β : ℝ) :
    IsClosed {φ : WeakDual ℂ A | ∀ a, α.IsEntireAnalytic a → ∀ b, α.IsEntireAnalytic b →
      φ (a * α.entireExtension b (β * I)) = φ (b * a)} := by
  simp only [ofPred_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun _ => isClosed_iInter fun b =>
    isClosed_iInter fun _ => isClosed_eq (eval_continuous _) (eval_continuous _)

/-- **Weak-* limits of KMS states.** A weak-* limit point of β-KMS states which has norm one
is a β-KMS state. -/
theorem closure_kmsStates_inter_subset :
    closure (α.kmsStates β) ∩ {φ | ‖toStrongDual φ‖ = 1} ⊆ α.kmsStates β := by
  have hsub : α.kmsStates β ⊆ {φ : WeakDual ℂ A | ∀ a, 0 ≤ a → 0 ≤ φ a} ∩
      {φ | ∀ a, α.IsEntireAnalytic a → ∀ b, α.IsEntireAnalytic b →
        φ (a * α.entireExtension b (β * I)) = φ (b * a)} := fun φ hφ =>
    have h := mem_kmsStates_iff_forall_isEntireAnalytic.mp hφ
    ⟨h.1, h.2.2⟩
  rintro φ ⟨hφ, hnorm⟩
  obtain ⟨hpos, hid⟩ := closure_minimal hsub (isClosed_setOf_nonneg.inter
    (isClosed_setOf_apply_mul_entireExtension_eq α β)) hφ
  exact mem_kmsStates_iff_forall_isEntireAnalytic.mpr ⟨hpos, hnorm, hid⟩

/-- A functional that is nonnegative on positive elements is monotone. -/
private theorem monotone_toStrongDual {φ : WeakDual ℂ A} (hpos : ∀ a, 0 ≤ a → 0 ≤ φ a) :
    Monotone (toStrongDual φ) :=
  (monotone_iff_map_nonneg _).mpr fun a ha => (hpos a ha).trans_eq (toStrongDual_apply φ a).symm

/-- Along an approximate unit, a positive functional tends to its norm. -/
private theorem tendsto_apply_approximateUnit {φ : WeakDual ℂ A} (hpos : ∀ a, 0 ≤ a → 0 ≤ φ a) :
    Tendsto (fun e => φ e) (CStarAlgebra.approximateUnit A) (𝓝 (‖toStrongDual φ‖ : ℂ)) := by
  simpa using (ContinuousLinearMap.monotone_iff_tendsto_nhds_opNorm
    (CStarAlgebra.increasingApproximateUnit A)).mp (monotone_toStrongDual hpos)

/-- **Convexity of `K_β`.** Convex combinations of β-KMS states are β-KMS states. -/
theorem convex_kmsStates : Convex ℝ (α.kmsStates β) := by
  intro φ hφ ψ hψ s t hs ht hst
  rw [mem_kmsStates_iff_forall_isEntireAnalytic] at hφ hψ ⊢
  have hpos (a : A) (ha : 0 ≤ a) : 0 ≤ (s • φ + t • ψ) a := by
    simpa using add_nonneg (smul_nonneg hs (hφ.1 a ha)) (smul_nonneg ht (hψ.1 a ha))
  refine ⟨hpos, ?_, fun a ha b hb => by simp [hφ.2.2 a ha b hb, hψ.2.2 a ha b hb]⟩
  -- the norm of a positive functional is its limit along an approximate unit
  have h := ((tendsto_apply_approximateUnit hφ.1).const_smul s).add
    ((tendsto_apply_approximateUnit hψ.1).const_smul t)
  simp only [hφ.2.1, hψ.2.1, ofReal_one, ← add_smul, hst, one_smul] at h
  exact_mod_cast tendsto_nhds_unique (tendsto_apply_approximateUnit hpos)
    (h.congr fun e => by simp)

section Unital

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {α : CStarAction (Multiplicative ℝ) B} {β : ℝ}

/-- For unital `B`, the set `K_β` of β-KMS states is weak-* closed. -/
theorem isClosed_kmsStates : IsClosed (α.kmsStates β) := by
  -- on positive functionals of a unital algebra, the norm is the value at `1`
  have hnorm {φ : WeakDual ℂ B} (hpos : ∀ a, 0 ≤ a → 0 ≤ φ a) :
      (‖toStrongDual φ‖ : ℂ) = φ 1 := by
    simpa using ContinuousLinearMap.monotone_iff_opNorm_eq_map_one.mp (monotone_toStrongDual hpos)
  refine closure_subset_iff_isClosed.mp fun φ hφ => closure_kmsStates_inter_subset ⟨hφ, ?_⟩
  have hsub : α.kmsStates β ⊆ {φ | (∀ a, 0 ≤ a → 0 ≤ φ a) ∧ φ 1 = 1} := fun ψ hψ => by
    obtain ⟨hpos, h1, -⟩ := mem_kmsStates_iff_forall_isEntireAnalytic.mp hψ
    exact ⟨hpos, by rw [← hnorm hpos, h1, ofReal_one]⟩
  obtain ⟨hpos, h1⟩ := closure_minimal hsub (isClosed_setOf_nonneg.inter
    (isClosed_eq (eval_continuous 1) continuous_const)) hφ
  exact_mod_cast (hnorm hpos).trans h1

/-- **Weak-* compactness of `K_β`.** For unital `B`, the set of β-KMS states is weak-* compact. -/
theorem isCompact_kmsStates : IsCompact (α.kmsStates β) := by
  refine (WeakDual.isCompact_closedBall 0 1).of_isClosed_subset isClosed_kmsStates fun φ hφ => ?_
  simp [(mem_kmsStates_iff_forall_isEntireAnalytic.mp hφ).2.1]

end Unital

end TauCeti.CStarAction
