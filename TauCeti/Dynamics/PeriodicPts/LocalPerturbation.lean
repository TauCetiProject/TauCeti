/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Topology.ContinuousOn

/-!
# Perturbing a map near one point of an orbit

Let `φ` be a self-map, `p` a point and `k > 0`. A perturbation `ψ` which fixes `p` and is the
identity near the later orbit points `φ^[j] p`, `0 < j < k`, changes the `k`-th iterate near `p`
only by precomposition: near `p`,

`(φ ∘ ψ)^[k] = φ^[k] ∘ ψ`

(`Function.iterate_comp_eventuallyEq_of_eventuallyEq_id`). Indeed the orbit of a point near `p`
under `φ ∘ ψ` passes through the neighbourhoods of the points `φ^[j] p`, where `ψ` does nothing.

When `p` is a periodic point of period `k`, the derivative of `φ^[k]` at `p` is the linearized
return map of its orbit. The return map of the perturbed map `φ ∘ ψ` is then the return map of
`φ` composed with the derivative of `ψ` at `p`
(`HasFDerivAt.iterate_comp_of_eventuallyEq_id`). This is how a perturbation supported in a small
neighbourhood of one point of a periodic orbit, for instance a Hamiltonian twist, changes the
linearized return map of that orbit, and only of that orbit.
-/

public section

open Filter Topology

namespace Function

variable {X : Type*} [TopologicalSpace X] {φ ψ : X → X} {p : X} {k : ℕ}

/-- **Iterates of a map perturbed near one point of an orbit.** If `ψ` fixes `p`, is continuous at
`p` and is the identity near `φ^[j] p` for `0 < j < k`, and `φ` is continuous at the orbit points
`φ^[j] p` for `j < k`, then near `p` the `k`-th iterate of `φ ∘ ψ` is `φ^[k] ∘ ψ`. -/
theorem iterate_comp_eventuallyEq_of_eventuallyEq_id (hk : 0 < k) (hψp : ψ p = p)
    (hψ : ContinuousAt ψ p) (hφ : ∀ j < k, ContinuousAt φ (φ^[j] p))
    (hid : ∀ j, 0 < j → j < k → ψ =ᶠ[𝓝 (φ^[j] p)] id) :
    (φ ∘ ψ)^[k] =ᶠ[𝓝 p] φ^[k] ∘ ψ := by
  have hcont : ∀ j ≤ k, ContinuousAt φ^[j] p := by
    intro j hj
    induction j with
    | zero => exact continuousAt_id
    | succ j ih =>
      rw [iterate_succ']
      exact (hφ j (by omega)).comp (ih (by omega))
  obtain ⟨k, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  -- Induction on the number `j + 1 ≤ k + 1` of iterations.
  suffices h : ∀ j ≤ k, (φ ∘ ψ)^[j + 1] =ᶠ[𝓝 p] φ^[j + 1] ∘ ψ from h k le_rfl
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
    have hc : ContinuousAt (φ^[j + 1] ∘ ψ) p :=
      (hcont (j + 1) (by omega)).comp_of_eq hψ hψp
    have hψj : ψ ∘ (φ^[j + 1] ∘ ψ) =ᶠ[𝓝 p] φ^[j + 1] ∘ ψ := by
      rw [ContinuousAt, comp_apply, hψp] at hc
      exact hc.eventually (hid (j + 1) (by omega) (by omega))
    rw [iterate_succ', iterate_succ' φ]
    filter_upwards [ih (by omega), hψj] with x hx hx'
    simp only [comp_apply] at hx hx' ⊢
    rw [hx, hx']

end Function

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {φ ψ : E → E} {p : E} {k : ℕ} {A B : E →L[𝕜] E}

/-- **The linearized return map of a locally perturbed map.** If `ψ` fixes `p` and is the identity
near the orbit points `φ^[j] p`, `0 < j < k`, then the derivative at `p` of the `k`-th iterate
of `φ ∘ ψ` is the derivative of `φ^[k]` at `p` composed with that of `ψ`. -/
theorem HasFDerivAt.iterate_comp_of_eventuallyEq_id (hA : HasFDerivAt φ^[k] A p)
    (hB : HasFDerivAt ψ B p) (hk : 0 < k) (hψp : ψ p = p)
    (hφ : ∀ j < k, ContinuousAt φ (φ^[j] p))
    (hid : ∀ j, 0 < j → j < k → ψ =ᶠ[𝓝 (φ^[j] p)] id) :
    HasFDerivAt (φ ∘ ψ)^[k] (A.comp B) p := by
  rw [← hψp] at hA
  exact (hA.comp p hB).congr_of_eventuallyEq
    (Function.iterate_comp_eventuallyEq_of_eventuallyEq_id hk hψp hB.continuousAt hφ hid)
