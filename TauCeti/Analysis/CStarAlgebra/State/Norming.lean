/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Space
import Mathlib.Analysis.LocallyConvex.Separation
import TauCeti.Analysis.CStarAlgebra.State.Spectrum
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Norming sets of states

A set `S` of states of a unital C⋆-algebra `A` *norms the self-adjoint part* of `A` when
`‖a‖ = ⨆ σ : S, ‖σ a‖` for every self-adjoint `a`. This file proves that this happens exactly when
the weak-* closed convex hull `closedConvexHull ℝ S` is the whole state space,
`TauCeti.closedConvexHull_eq_stateSpace_iff`.

The substantial direction is Lemma 2.8 of Brown: if `S` norms the self-adjoint part and a state
`φ` lies outside the closed convex hull of `S`, Hahn–Banach separation in the weak-* dual gives an
element of `A` whose real part `b` separates `φ` from `S`. After the shift `c = b + ‖b‖ • 1`, which
is positive, every state `σ ∈ S` has `σ c = ‖σ c‖`, so the norming property bounds `‖c‖` below the
value `φ c`, contradicting the contractivity of `φ`. The converse direction evaluates the closed
convex condition `‖ψ a‖ ≤ ⨆ σ : S, ‖σ a‖` at a state attaining `‖a‖`.

Typical norming sets are the vector states of a faithful representation and the states obtained
from an approximating family of completely positive maps; the density statement is how such
states are shown to reach every state of `A`.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*,
  Mem. Amer. Math. Soc. 184 (2006), no. 865, Lemma 2.8.
-/

public section

open Set WeakDual
open scoped ComplexOrder ComplexStarModule

namespace TauCeti

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- If `S` norms the self-adjoint part of `A`, then no state lies outside the weak-* closed convex
hull of `S`. -/
private theorem mem_closedConvexHull_of_forall_norm_eq_iSup {S : Set (WeakDual ℂ A)}
    (hS : S ⊆ stateSpace A)
    (hnorm : ∀ a : A, IsSelfAdjoint a → ‖a‖ = ⨆ σ : S, ‖(σ : WeakDual ℂ A) a‖)
    {φ : WeakDual ℂ A} (hφ : φ ∈ stateSpace A) : φ ∈ closedConvexHull ℝ S := by
  by_contra hφS
  -- separate `φ` from the closed convex hull by the real part of evaluation at some `x`
  obtain ⟨l, u, hlS, hlφ⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
    convex_closedConvexHull isClosed_closedConvexHull hφS
  obtain ⟨x, hx⟩ := WeakDual.exists_forall_apply_eq_apply l
  set b : A := (ℜ x : A)
  have hb : IsSelfAdjoint b := (ℜ x).property
  -- the positive shift `c = b + ‖b‖ • 1`, on which every state `ψ` takes the value
  -- `ψ c = re (ψ x) + ‖b‖ ≥ 0`
  set c : A := b + algebraMap ℝ A ‖b‖
  have hc : 0 ≤ c := neg_le_iff_add_nonneg.1 (IsSelfAdjoint.neg_algebraMap_norm_le_self b hb)
  have hψc {ψ : WeakDual ℂ A} (hψ : ψ ∈ stateSpace A) :
      ‖ψ c‖ = (ψ x).re + ‖b‖ := by
    have h := congrArg Complex.re (Complex.norm_of_nonneg' (map_nonneg_of_mem_stateSpace hψ hc))
    rw [Complex.ofReal_re] at h
    rw [h, ← re_apply_realPart_of_mem_stateSpace hψ x]
    simp [c, b, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, map_one_of_mem_stateSpace hψ]
  -- `S` is nonempty, since `A` is nonzero and `S` norms `1`
  have := nontrivial_of_mem_stateSpace hφ
  have hSne : Nonempty S := by
    by_contra hS0
    rw [not_nonempty_iff] at hS0
    simpa using hnorm 1 (.one A)
  -- the norming property bounds `‖c‖` by `u + ‖b‖`, below `‖φ c‖`
  have hcle : ‖c‖ ≤ u + ‖b‖ := by
    rw [hnorm c (hb.add (.algebraMap A (.all _)))]
    refine ciSup_le fun σ => ?_
    rw [hψc (hS σ.property)]
    have := hlS σ (subset_closedConvexHull σ.property)
    rw [hx, RCLike.re_to_complex] at this
    linarith
  have hφc := norm_apply_le_of_mem_stateSpace hφ c
  rw [hψc hφ] at hφc
  rw [hx, RCLike.re_to_complex] at hlφ
  linarith

/-- **Norming sets of states.** A set `S` of states of a unital C⋆-algebra has weak-* closed convex
hull equal to the whole state space exactly when it norms the self-adjoint part:
`‖a‖ = ⨆ σ : S, ‖σ a‖` for every self-adjoint `a`. -/
theorem closedConvexHull_eq_stateSpace_iff {S : Set (WeakDual ℂ A)} (hS : S ⊆ stateSpace A) :
    closedConvexHull ℝ S = stateSpace A ↔
      ∀ a : A, IsSelfAdjoint a → ‖a‖ = ⨆ σ : S, ‖(σ : WeakDual ℂ A) a‖ := by
  refine ⟨fun h a ha => ?_, fun h => ?_⟩
  swap
  · exact (closedConvexHull_min hS convex_stateSpace isClosed_stateSpace).antisymm
      fun φ hφ => mem_closedConvexHull_of_forall_norm_eq_iSup hS h hφ
  rcases isEmpty_or_nonempty S with hS0 | hS0
  · -- a C⋆-algebra without states is zero
    have hempty : stateSpace A ⊆ ∅ :=
      h ▸ closedConvexHull_min (eq_empty_of_isEmpty S).subset convex_empty isClosed_empty
    have : Subsingleton A := not_nontrivial_iff_subsingleton.1 fun _ =>
      stateSpace_nonempty.ne_empty (subset_empty_iff.1 hempty)
    simp [Subsingleton.elim a 0]
  have hbdd : BddAbove (range fun σ : S => ‖(σ : WeakDual ℂ A) a‖) :=
    ⟨‖a‖, forall_mem_range.2 fun σ => norm_apply_le_of_mem_stateSpace (hS σ.property) a⟩
  refine le_antisymm ?_ (ciSup_le fun σ => norm_apply_le_of_mem_stateSpace (hS σ.property) a)
  -- the functionals `ψ` with `‖ψ a‖ ≤ ⨆ σ : S, ‖σ a‖` form a closed convex set containing `S`
  set M := ⨆ σ : S, ‖(σ : WeakDual ℂ A) a‖
  set T : Set (WeakDual ℂ A) := (fun ψ : WeakDual ℂ A => ψ a) ⁻¹' Metric.closedBall 0 M
  have hT : stateSpace A ⊆ T :=
    h ▸ closedConvexHull_min
      (fun σ hσ => mem_closedBall_zero_iff.2 (le_ciSup hbdd ⟨σ, hσ⟩))
      ((convex_closedBall (0 : ℂ) M).is_linear_preimage ⟨fun _ _ => rfl, fun _ _ => rfl⟩)
      (Metric.isClosed_closedBall.preimage (eval_continuous a))
  -- a state attaining `‖a‖` lies in `T`
  have := nontrivial_of_mem_stateSpace (hS hS0.some.property)
  have := ha.isStarNormal
  obtain ⟨ω, -, hω, hωa⟩ := CStarAlgebra.exists_positiveContinuousLinearMap_norm_apply_eq_norm a
  simpa [T, hωa] using hT (ω.toWeakDual_mem_stateSpace_iff.2 hω)

end TauCeti
