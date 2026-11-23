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
The same holds for a perturbation that moves `p`, such as a small translation, provided it is the
identity near the later points `φ^[j] (ψ p)` of the orbit of `ψ p`
(`Function.iterate_comp_eventuallyEq_iterate_comp`); pointwise, it suffices that `ψ` fixes these
points (`Function.iterate_comp_apply_eq_iterate_apply`). In particular, if `ψ` is the translation by
`c` near `p`, then near `p` the `k`-th iterate of `φ ∘ ψ` is `w ↦ φ^[k] (w + c)`
(`Function.iterate_comp_eventuallyEq_comp_add`).

When `p` is a periodic point of period `k`, the derivative of `φ^[k]` at `p` is the linearized
return map of its orbit. The return map of the perturbed map `φ ∘ ψ` is then the return map of
`φ` composed with the derivative of `ψ` at `p`
(`HasFDerivAt.iterate_comp_of_eventuallyEq_id`). This is how a perturbation supported in a small
neighbourhood of one point of a periodic orbit, for instance a Hamiltonian twist, changes the
linearized return map of that orbit.
-/

public section

open Filter Topology

namespace Function

variable {X : Type*} [TopologicalSpace X] {φ ψ : X → X} {p : X} {k : ℕ}

omit [TopologicalSpace X] in
/-- **Iterates of a map perturbed off an orbit, pointwise.** If `ψ` fixes the later points
`φ^[j] (ψ p)`, `0 < j < k`, of the orbit of `ψ p`, then the `k`-th iterate of `φ ∘ ψ` at `p` is
`φ^[k] (ψ p)`. -/
theorem iterate_comp_apply_eq_iterate_apply (hk : 0 < k)
    (hψ : ∀ j, 0 < j → j < k → ψ (φ^[j] (ψ p)) = φ^[j] (ψ p)) : (φ ∘ ψ)^[k] p = φ^[k] (ψ p) := by
  obtain ⟨k, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply', ih (by omega) fun j hj hjk ↦ hψ j hj (by omega), comp_apply,
      hψ (k + 1) (by omega) (by omega), ← iterate_succ_apply' φ]

/-- **Iterates of a map perturbed near the later points of an orbit.** If `ψ` is continuous at
`p` and is the identity near `φ^[j] (ψ p)` for `0 < j < k`, and `φ` is continuous at the orbit
points `φ^[j] (ψ p)` for `j < k`, then near `p` the `k`-th iterate of `φ ∘ ψ` is `φ^[k] ∘ ψ`. The
perturbation need not fix `p`: the orbit that matters is the `φ`-orbit of `ψ p`. -/
theorem iterate_comp_eventuallyEq_iterate_comp (hk : 0 < k) (hψ : ContinuousAt ψ p)
    (hφ : ∀ j < k, ContinuousAt φ (φ^[j] (ψ p)))
    (hid : ∀ j, 0 < j → j < k → ψ =ᶠ[𝓝 (φ^[j] (ψ p))] id) :
    (φ ∘ ψ)^[k] =ᶠ[𝓝 p] φ^[k] ∘ ψ := by
  have hcont : ∀ j ≤ k, ContinuousAt φ^[j] (ψ p) := by
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
    have hc : ContinuousAt (φ^[j + 1] ∘ ψ) p := (hcont (j + 1) (by omega)).comp hψ
    have hψj : ψ ∘ (φ^[j + 1] ∘ ψ) =ᶠ[𝓝 p] φ^[j + 1] ∘ ψ :=
      hc.eventually (hid (j + 1) (by omega) (by omega))
    rw [iterate_succ', iterate_succ' φ]
    filter_upwards [ih (by omega), hψj] with x hx hx'
    simp only [comp_apply] at hx hx' ⊢
    rw [hx, hx']

/-- **Iterates of a map perturbed near one point of an orbit.** If `ψ` fixes `p`, is continuous at
`p` and is the identity near `φ^[j] p` for `0 < j < k`, and `φ` is continuous at the orbit points
`φ^[j] p` for `j < k`, then near `p` the `k`-th iterate of `φ ∘ ψ` is `φ^[k] ∘ ψ`. -/
theorem iterate_comp_eventuallyEq_of_eventuallyEq_id (hk : 0 < k) (hψp : ψ p = p)
    (hψ : ContinuousAt ψ p) (hφ : ∀ j < k, ContinuousAt φ (φ^[j] p))
    (hid : ∀ j, 0 < j → j < k → ψ =ᶠ[𝓝 (φ^[j] p)] id) :
    (φ ∘ ψ)^[k] =ᶠ[𝓝 p] φ^[k] ∘ ψ :=
  iterate_comp_eventuallyEq_iterate_comp hk hψ (by simpa only [hψp] using hφ)
    (by simpa only [hψp] using hid)

/-- **Iterates of a map perturbed by a local translation.** If `ψ` is the translation by `c` near
`p` and the identity near the later points `φ^[j] (p + c)`, `0 < j < k`, of the orbit of `p + c`,
and `φ` is continuous at the orbit points `φ^[j] (p + c)` for `j < k`, then near `p` the `k`-th
iterate of `φ ∘ ψ` is `w ↦ φ^[k] (w + c)`. -/
theorem iterate_comp_eventuallyEq_comp_add [Add X] [ContinuousAdd X] (hk : 0 < k) {c : X}
    (hadd : ψ =ᶠ[𝓝 p] fun w ↦ w + c) (hφ : ∀ j < k, ContinuousAt φ (φ^[j] (p + c)))
    (hid : ∀ j, 0 < j → j < k → ψ =ᶠ[𝓝 (φ^[j] (p + c))] id) :
    (φ ∘ ψ)^[k] =ᶠ[𝓝 p] fun w ↦ φ^[k] (w + c) := by
  rw [← hadd.eq_of_nhds] at hφ hid
  exact (iterate_comp_eventuallyEq_iterate_comp hk
    ((continuous_id.add continuous_const).continuousAt.congr_of_eventuallyEq hadd) hφ hid).trans
    (hadd.fun_comp φ^[k])

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
