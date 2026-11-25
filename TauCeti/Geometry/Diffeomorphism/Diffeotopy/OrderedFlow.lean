/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Flow
public import TauCeti.Geometry.Manifold.Flow.Ordered
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Ordered diffeotopies of complete flows

Let `v₀, …, v_(k-1)` be complete vector fields on a manifold `M`, with flows `ψ^(v i)`, and let
`TauCeti.orderedFlowOf v s = ψ^(v 0)_(s 0) ∘ ⋯ ∘ ψ^(v (k-1))_(s (k-1))` be their ordered flow,
defined in `TauCeti.Geometry.Manifold.Flow.Ordered`.

Given `C^n` time functions `A i : ℝ → ℝ` with `A i 0 = 0`, running each field along its time
function and composing in this order gives the diffeotopy

`ψ_t = ψ^(v 0)_(A 0 t) ∘ ⋯ ∘ ψ^(v (k-1))_(A (k-1) t)`

(`TauCeti.orderedGlobalFlowDiffeotopy`, `TauCeti.Diffeotopy.timeSlice_orderedGlobalFlowDiffeotopy`),
the pointwise composite of the diffeotopies `TauCeti.globalFlowDiffeotopyAlong`. These are
the ordered flows used to correct a symplectic isotopy by finitely many symplectic flows, with
`A i t` the integral up to time `t` of a cohomology coordinate of the isotopy.

When every total time vanishes, `A i 1 = 0`, the diffeotopy is a loop, `ψ₁ = id`
(`TauCeti.Diffeotopy.final_orderedGlobalFlowDiffeotopy_eq_refl`). Scaling all the time functions
by `1 - s` then contracts it to the constant diffeotopy through the ordered flows of the scaled time
functions, which are loops too, with both time ends fixed throughout
(`TauCeti.Diffeotopy.exists_homotopy_orderedGlobalFlowDiffeotopy`).

## Main definitions

* `TauCeti.orderedGlobalFlowDiffeotopy`: the diffeotopy running finitely many complete fields
  along time functions, composed in order.

## Main results

* `TauCeti.Diffeotopy.timeSlice_orderedGlobalFlowDiffeotopy`: the time slices are ordered flows.
* `TauCeti.Diffeotopy.final_orderedGlobalFlowDiffeotopy_eq_refl`: vanishing total times give a
  loop.
* `TauCeti.Diffeotopy.exists_homotopy_orderedGlobalFlowDiffeotopy`: such a loop is homotopic to
  the constant diffeotopy relative to both time ends, through ordered flows.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the proof of Theorem 10.2.5, that symplectic isotopies of
  zero flux are homotopic to Hamiltonian isotopies).
* Augustin Banyaga, *The Structure of Classical Diffeomorphism Groups*, Kluwer, 1997,
  Section 3.1.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [IsManifold I 1 M]
  {n : ℕ∞} [IsManifold I n M]

/-- Run complete `C^n` vector fields `v 0, …, v (k - 1)` along `C^n` time functions
`A 0, …, A (k - 1)` vanishing at `0`, and compose in order: the motion at time `t ∈ [0, 1]` is
`ψ^(v 0)_(A 0 t) ∘ ⋯ ∘ ψ^(v (k-1))_(A (k-1) t)`. It is the pointwise composite of the diffeotopies
`TauCeti.globalFlowDiffeotopyAlong`. -/
def orderedGlobalFlowDiffeotopy (hn : 1 ≤ n) :
    {k : ℕ} → (v : Fin k → (x : M) → TangentSpace I x) →
      (∀ i, CMDiff n (fun y ↦ (⟨y, v i y⟩ : TangentBundle I M))) →
      (∀ i, IsCompleteVectorField (v i)) → (A : Fin k → ℝ → ℝ) → (∀ i, ContDiff ℝ n (A i)) →
      (∀ i, A i 0 = 0) → Diffeotopy I n M
  | 0, _, _, _, _, _, _ => Diffeotopy.refl I n M
  | _ + 1, v, hv, hc, A, hA, hA₀ =>
    (orderedGlobalFlowDiffeotopy hn (fun i ↦ v i.succ) (fun i ↦ hv i.succ) (fun i ↦ hc i.succ)
      (fun i ↦ A i.succ) (fun i ↦ hA i.succ) (fun i ↦ hA₀ i.succ)).trans
      (globalFlowDiffeotopyAlong hn (hv 0) (hc 0) (A 0) (hA 0) (hA₀ 0))

section Ordered

variable (hn : 1 ≤ n) {k : ℕ} (v : Fin k → (x : M) → TangentSpace I x)
  (hv : ∀ i, CMDiff n (fun y ↦ (⟨y, v i y⟩ : TangentBundle I M)))
  (hc : ∀ i, IsCompleteVectorField (v i)) (A : Fin k → ℝ → ℝ) (hA : ∀ i, ContDiff ℝ n (A i))
  (hA₀ : ∀ i, A i 0 = 0)

/-- The ordered diffeotopy of no fields is the constant diffeotopy. -/
theorem orderedGlobalFlowDiffeotopy_of_fin_zero (v : Fin 0 → (x : M) → TangentSpace I x)
    (hv : ∀ i, CMDiff n (fun y ↦ (⟨y, v i y⟩ : TangentBundle I M)))
    (hc : ∀ i, IsCompleteVectorField (v i)) (A : Fin 0 → ℝ → ℝ)
    (hA : ∀ i, ContDiff ℝ n (A i)) (hA₀ : ∀ i, A i 0 = 0) :
    orderedGlobalFlowDiffeotopy hn v hv hc A hA hA₀ = Diffeotopy.refl I n M :=
  (rfl)

/-- The ordered diffeotopy of `k + 1` fields is the ordered diffeotopy of the last `k` fields,
followed pointwise by the first field run along its time function. -/
theorem orderedGlobalFlowDiffeotopy_succ (v : Fin (k + 1) → (x : M) → TangentSpace I x)
    (hv : ∀ i, CMDiff n (fun y ↦ (⟨y, v i y⟩ : TangentBundle I M)))
    (hc : ∀ i, IsCompleteVectorField (v i)) (A : Fin (k + 1) → ℝ → ℝ)
    (hA : ∀ i, ContDiff ℝ n (A i)) (hA₀ : ∀ i, A i 0 = 0) :
    orderedGlobalFlowDiffeotopy hn v hv hc A hA hA₀ =
      (orderedGlobalFlowDiffeotopy hn (fun i ↦ v i.succ) (fun i ↦ hv i.succ) (fun i ↦ hc i.succ)
        (fun i ↦ A i.succ) (fun i ↦ hA i.succ) (fun i ↦ hA₀ i.succ)).trans
        (globalFlowDiffeotopyAlong hn (hv 0) (hc 0) (A 0) (hA 0) (hA₀ 0)) :=
  (rfl)

/-- The ordered diffeotopy at time `t` is the ordered flow for the times `A i t`. -/
@[simp]
theorem orderedGlobalFlowDiffeotopy_apply (p : unitInterval × M) :
    orderedGlobalFlowDiffeotopy hn v hv hc A hA hA₀ p = orderedFlowOf v (fun i ↦ A i p.1) p.2 := by
  induction k with
  | zero =>
    rw [orderedGlobalFlowDiffeotopy_of_fin_zero, Diffeotopy.refl_apply, orderedFlowOf_of_fin_zero,
      id_eq]
  | succ k ih =>
    rw [orderedGlobalFlowDiffeotopy_succ, Diffeotopy.trans_apply, ih,
      globalFlowDiffeotopyAlong_apply, orderedFlowOf_succ, Function.comp_apply, flowOf_apply]

namespace Diffeotopy

/-- The time-`t` map of the ordered diffeotopy is the ordered flow
`ψ^(v 0)_(A 0 t) ∘ ⋯ ∘ ψ^(v (k-1))_(A (k-1) t)`. -/
theorem timeSlice_orderedGlobalFlowDiffeotopy (t : unitInterval) :
    ⇑((orderedGlobalFlowDiffeotopy hn v hv hc A hA hA₀).timeSlice t) =
      orderedFlowOf v fun i ↦ A i t := by
  funext x
  rw [timeSlice_apply, orderedGlobalFlowDiffeotopy_apply]

/-- The motion of the ordered diffeotopy, read on the cylinder: at `(x, t)` it is the ordered flow
of `x` for the times `A i t`. -/
theorem cylinderMap_orderedGlobalFlowDiffeotopy :
    (orderedGlobalFlowDiffeotopy hn v hv hc A hA hA₀).cylinderMap =
      fun p : M × unitInterval ↦ orderedFlowOf v (fun i ↦ A i p.2) p.1 := by
  funext p
  rw [cylinderMap_apply, orderedGlobalFlowDiffeotopy_apply]

/-- **Vanishing total times give a loop.** If every time function vanishes at time one, the
ordered diffeotopy ends at the identity. -/
theorem final_orderedGlobalFlowDiffeotopy_eq_refl (h₁ : ∀ i, A i 1 = 0) :
    (orderedGlobalFlowDiffeotopy hn v hv hc A hA hA₀).final = Diffeomorph.refl I M n := by
  refine Diffeomorph.ext fun x ↦ ?_
  rw [final_def, timeSlice_apply, orderedGlobalFlowDiffeotopy_apply]
  simp [h₁]

/-- **Loops of ordered flows contract.** If every time function vanishes at time one, the ordered
diffeotopy is homotopic to the constant diffeotopy relative to both time ends: the motions
`G ((x, t), s) = ψ^(v 0)_((1 - s) A 0 t) ∘ ⋯ ∘ ψ^(v (k-1))_((1 - s) A (k-1) t) x` form a jointly
`C^n` homotopy, fixing `x` at the times `0` and `1`, from the motion of the ordered diffeotopy at
`s = 0` to the constant motion at `s = 1`. Every map `x ↦ G ((x, t), s)` is an ordered flow. -/
theorem exists_homotopy_orderedGlobalFlowDiffeotopy (h₁ : ∀ i, A i 1 = 0) :
    ∃ G : (M × unitInterval) × unitInterval → M,
      ContMDiff ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) I n G ∧
      (∀ p, G (p, 0) = (orderedGlobalFlowDiffeotopy hn v hv hc A hA hA₀).cylinderMap p) ∧
      (∀ p, G (p, 1) = p.1) ∧ (∀ x s, G ((x, 0), s) = x) ∧ (∀ x s, G ((x, 1), s) = x) ∧
      ∀ t s : unitInterval,
        (fun x ↦ G ((x, t), s)) = orderedFlowOf v fun i ↦ (1 - (s : ℝ)) * A i t := by
  refine ⟨fun q ↦ orderedFlowOf v (fun i ↦ (1 - (q.2 : ℝ)) * A i q.1.2) q.1.1, ?_, fun p ↦ ?_,
    fun p ↦ ?_, fun x s ↦ ?_, fun x s ↦ ?_, fun t s ↦ ?_⟩
  · -- The times `(1 - s) A i t` depend smoothly on `((x, t), s)`.
    have htimes : ContMDiff ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) 𝓘(ℝ, Fin k → ℝ) n
        fun q : (M × unitInterval) × unitInterval ↦ fun i ↦ (1 - (q.2 : ℝ)) * A i q.1.2 :=
      contMDiff_pi_module_iff.2 fun i ↦
        ((contDiff_const.sub contDiff_id).contMDiff.comp
          (contMDiff_subtypeVal_Icc.comp contMDiff_snd)).mul
          ((hA i).contMDiff.comp (contMDiff_subtypeVal_Icc.comp (contMDiff_snd.comp contMDiff_fst)))
    exact (contMDiff_orderedFlowOf_uncurry hn hv hc).comp
      (htimes.prodMk (contMDiff_fst.comp contMDiff_fst))
  · simp
  · simp
  · simp [hA₀]
  · simp [h₁]
  · rfl

end Diffeotopy

end Ordered

end TauCeti
