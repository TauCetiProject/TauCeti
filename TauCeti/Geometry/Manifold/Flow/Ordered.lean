/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow

/-!
# Ordered compositions of flows

Let `v₀, …, v_(k-1)` be vector fields on a manifold `M`, with flows `ψ^(v i)`. For times
`s = (s₀, …, s_(k-1))` the **ordered flow**

`orderedFlowOf v s = ψ^(v 0)_(s 0) ∘ ψ^(v 1)_(s 1) ∘ ⋯ ∘ ψ^(v (k-1))_(s (k-1))`

(`TauCeti.orderedFlowOf`) runs the last field first. When every field is complete and `C^n`,
`1 ≤ n`, it is jointly `C^n` in the times and the point
(`TauCeti.contMDiff_orderedFlowOf_uncurry`), and all times zero give the identity
(`TauCeti.orderedFlowOf_zero`). Running the fields in the reverse order for the negated times,
`ψ^(v (k-1))_(-s (k-1)) ∘ ⋯ ∘ ψ^(v 0)_(-s 0)`, inverts the ordered flow
(`TauCeti.orderedFlowOf_rev_neg_orderedFlowOf`, `TauCeti.orderedFlowOf_orderedFlowOf_rev_neg`), so
the ordered flows of complete smooth fields are diffeomorphisms depending smoothly on the times,
with inverses depending smoothly on the times as well.

## Main definitions

* `TauCeti.orderedFlowOf`: the ordered composite of the flows of finitely many fields.

## Main results

* `TauCeti.orderedFlowOf_zero`: all times zero give the identity.
* `TauCeti.contMDiff_orderedFlowOf_uncurry`: joint smoothness in the times and the point.
* `TauCeti.orderedFlowOf_rev_neg_orderedFlowOf`, `TauCeti.orderedFlowOf_orderedFlowOf_rev_neg`:
  the reversed ordered flow for the negated times is the inverse of the ordered flow.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the proof of Theorem 10.2.5).
* Augustin Banyaga, *The Structure of Classical Diffeomorphism Groups*, Kluwer, 1997,
  Section 3.1.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The **ordered flow** of finitely many vector fields `v 0, …, v (k - 1)` for the times
`s 0, …, s (k - 1)`: the composite `ψ^(v 0)_(s 0) ∘ ψ^(v 1)_(s 1) ∘ ⋯ ∘ ψ^(v (k-1))_(s (k-1))` of
their maximal flows, in which the last field runs first. -/
def orderedFlowOf : {k : ℕ} → (Fin k → (x : M) → TangentSpace I x) → (Fin k → ℝ) → M → M
  | 0, _, _ => id
  | _ + 1, v, s => flowOf (v 0) (s 0) ∘ orderedFlowOf (fun i ↦ v i.succ) (fun i ↦ s i.succ)

/-- The ordered flow of no fields is the identity. -/
@[simp]
theorem orderedFlowOf_of_fin_zero (v : Fin 0 → (x : M) → TangentSpace I x) (s : Fin 0 → ℝ) :
    orderedFlowOf v s = id :=
  (rfl)

/-- The ordered flow of `k + 1` fields runs the last `k` fields first, in order, and then the
first field. -/
theorem orderedFlowOf_succ {k : ℕ} (v : Fin (k + 1) → (x : M) → TangentSpace I x)
    (s : Fin (k + 1) → ℝ) :
    orderedFlowOf v s =
      flowOf (v 0) (s 0) ∘ orderedFlowOf (fun i ↦ v i.succ) (fun i ↦ s i.succ) :=
  (rfl)

/-- The ordered flow of `k + 1` fields runs the last field first, and then the first `k` fields,
in order. -/
theorem orderedFlowOf_eq_comp_flowOf_last {k : ℕ} (v : Fin (k + 1) → (x : M) → TangentSpace I x)
    (s : Fin (k + 1) → ℝ) :
    orderedFlowOf v s = orderedFlowOf (fun i ↦ v i.castSucc) (fun i ↦ s i.castSucc) ∘
      flowOf (v (Fin.last k)) (s (Fin.last k)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [orderedFlowOf_succ, ih (fun i ↦ v i.succ) (fun i ↦ s i.succ),
      orderedFlowOf_succ (fun i ↦ v i.castSucc)]
    simp only [Fin.succ_last, Fin.castSucc_zero, Fin.succ_castSucc, Function.comp_assoc]

/-- The ordered flow for all times zero is the identity. -/
@[simp]
theorem orderedFlowOf_zero {k : ℕ} (v : Fin k → (x : M) → TangentSpace I x) :
    orderedFlowOf v (fun _ ↦ 0) = id := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext x
    rw [orderedFlowOf_succ]
    exact (congrArg (flowOf (v 0) 0) (congrFun (ih fun i ↦ v i.succ) x)).trans (flowOf_zero _ _)

/-- **Ordered flows are jointly smooth.** For complete `C^n` vector fields, `1 ≤ n`, the ordered
flow `(s, x) ↦ ψ^(v 0)_(s 0) ∘ ⋯ ∘ ψ^(v (k-1))_(s (k-1)) x` is jointly `C^n` in the times and the
point. -/
theorem contMDiff_orderedFlowOf_uncurry [CompleteSpace E] [T2Space M] [BoundarylessManifold I M]
    [IsManifold I 1 M] {n : ℕ∞} [IsManifold I n M] (hn : 1 ≤ n) {k : ℕ}
    {v : Fin k → (x : M) → TangentSpace I x}
    (hv : ∀ i, CMDiff n (fun y ↦ (⟨y, v i y⟩ : TangentBundle I M)))
    (hc : ∀ i, IsCompleteVectorField (v i)) :
    ContMDiff (𝓘(ℝ, Fin k → ℝ).prod I) I n fun p : (Fin k → ℝ) × M ↦ orderedFlowOf v p.1 p.2 := by
  induction k with
  | zero => exact contMDiff_snd
  | succ k ih =>
    have h₀ : ContMDiff (𝓘(ℝ, Fin (k + 1) → ℝ).prod I) 𝓘(ℝ) n
        fun p : (Fin (k + 1) → ℝ) × M ↦ p.1 0 :=
      (contDiff_apply ℝ (fun _ ↦ ℝ) 0).contMDiff.comp contMDiff_fst
    have htail : ContMDiff (𝓘(ℝ, Fin (k + 1) → ℝ).prod I) 𝓘(ℝ, Fin k → ℝ) n
        fun p : (Fin (k + 1) → ℝ) × M ↦ fun i : Fin k ↦ p.1 i.succ :=
      (contDiff_pi.2 fun i : Fin k ↦ contDiff_apply ℝ (fun _ ↦ ℝ) i.succ).contMDiff.comp
        contMDiff_fst
    have h := (contMDiff_globalFlow_uncurry (hc 0) hn (hv 0)).comp
      (h₀.prodMk ((ih (v := fun i ↦ v i.succ) (fun i ↦ hv i.succ) fun i ↦ hc i.succ).comp
        (htail.prodMk contMDiff_snd)))
    refine h.congr fun p ↦ ?_
    rw [orderedFlowOf_succ, Function.comp_apply,
      flowOf_eq_globalFlow ((hv 0).of_le (by exact_mod_cast hn)) (hc 0)]
    rfl

section Inverse

variable [T2Space M] [BoundarylessManifold I M] [IsManifold I 1 M] {k : ℕ}
  {v : Fin k → (x : M) → TangentSpace I x}

/-- **The reversed ordered flow undoes the ordered flow.** For complete `C¹` vector fields, running
the fields in the reverse order for the negated times,
`ψ^(v (k-1))_(-s (k-1)) ∘ ⋯ ∘ ψ^(v 0)_(-s 0)`, undoes the ordered flow
`ψ^(v 0)_(s 0) ∘ ⋯ ∘ ψ^(v (k-1))_(s (k-1))`. -/
theorem orderedFlowOf_rev_neg_orderedFlowOf
    (hv : ∀ i, CMDiff 1 (fun y ↦ (⟨y, v i y⟩ : TangentBundle I M)))
    (hc : ∀ i, IsCompleteVectorField (v i)) (s : Fin k → ℝ) (x : M) :
    orderedFlowOf (fun i ↦ v i.rev) (fun i ↦ -s i.rev) (orderedFlowOf v s x) = x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [orderedFlowOf_eq_comp_flowOf_last (fun i ↦ v i.rev), orderedFlowOf_succ v]
    simp only [Function.comp_apply, Fin.rev_last, Fin.rev_castSucc]
    rw [flowOf_neg_flowOf (hv 0) ((hc 0).mem_flowDomain _ _)]
    exact ih (fun i ↦ hv i.succ) (fun i ↦ hc i.succ) (fun i ↦ s i.succ) _

/-- **The ordered flow undoes the reversed ordered flow.** For complete `C¹` vector fields, the
ordered flow `ψ^(v 0)_(s 0) ∘ ⋯ ∘ ψ^(v (k-1))_(s (k-1))` undoes the reversed ordered flow
`ψ^(v (k-1))_(-s (k-1)) ∘ ⋯ ∘ ψ^(v 0)_(-s 0)`. -/
theorem orderedFlowOf_orderedFlowOf_rev_neg
    (hv : ∀ i, CMDiff 1 (fun y ↦ (⟨y, v i y⟩ : TangentBundle I M)))
    (hc : ∀ i, IsCompleteVectorField (v i)) (s : Fin k → ℝ) (x : M) :
    orderedFlowOf v s (orderedFlowOf (fun i ↦ v i.rev) (fun i ↦ -s i.rev) x) = x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [orderedFlowOf_eq_comp_flowOf_last (fun i ↦ v i.rev), orderedFlowOf_succ v]
    simp only [Function.comp_apply, Fin.rev_last, Fin.rev_castSucc]
    rw [ih (fun i ↦ hv i.succ) (fun i ↦ hc i.succ) (fun i ↦ s i.succ)]
    exact flowOf_flowOf_neg (hv 0) (hc 0) (s 0) _

end Inverse

end TauCeti
