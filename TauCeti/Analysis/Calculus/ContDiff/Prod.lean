/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smoothness of slices of a map on a product

If a map `H` on a product is smooth near every point of `s ×ˢ I`, then each of its slices
`H (·, t)` with `t ∈ I` is smooth on `s` (`TauCeti.contDiffOn_comp_prodMk_left`). For instance,
the time slices of a homotopy smooth near `s × [0, 1]` are smooth on `s`.

For a family `F : P × E → X` smooth at `(p, x)`, the spatial differential
`(q, y) ↦ fderiv (F (q, ·)) y` is smooth jointly (`ContDiffAt.fderiv_slice`), smoothness persists
along a graph over the parameter (`ContDiffAt.eventually_contDiffAt_graph`), and the vertical part
of the derivative of a `C¹` map is continuous along a continuous graph
(`ContDiffAt.continuousAt_fderiv_comp_inr`).
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : WithTop ℕ∞} {s : Set E} {I : Set G} {H : E × G → F}

/-- **Slices of a map smooth near `s ×ˢ I` are smooth**: for `t ∈ I`, the slice `H (·, t)` is
smooth on `s`. -/
theorem contDiffOn_comp_prodMk_left (hH : ∀ p ∈ s ×ˢ I, ContDiffAt 𝕜 n H p) {t : G}
    (ht : t ∈ I) : ContDiffOn 𝕜 n (fun x ↦ H (x, t)) s :=
  fun x hx ↦ ((hH (x, t) ⟨hx, ht⟩).comp x (contDiff_prodMk_left t).contDiffAt).contDiffWithinAt

end TauCeti

namespace ContDiffAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] {p : P} {x : E}

/-- The spatial differential of a `C^n` family is `C^m` jointly in the parameter and the spatial
variable, for `m + 1 ≤ n`. -/
theorem fderiv_slice {n m : WithTop ℕ∞} {F : P × E → X}
    (hF : ContDiffAt 𝕜 n F (p, x)) (hmn : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (fun q : P × E ↦ fderiv 𝕜 (fun y ↦ F (q.1, y)) q.2) (p, x) := by
  apply ContDiffAt.fderiv (n := n) (m := m) (x₀ := (p, x))
    (f := fun q : P × E ↦ fun y : E ↦ F (q.1, y)) (g := fun q : P × E ↦ q.2)
  · exact hF.comp ((p, x), x) (by fun_prop)
  · fun_prop
  · exact hmn

/-- A function that is `C^n` at `(p, ψ p)` is `C^n` at `(q, ψ q)` for `q` near `p`, when `ψ` is
continuous at `p`. -/
theorem eventually_contDiffAt_graph {f : P × E → X} {ψ : P → E} {n : ℕ}
    (hf : ContDiffAt 𝕜 n f (p, ψ p)) (hψ : ContinuousAt ψ p) :
    ∀ᶠ q in nhds p, ContDiffAt 𝕜 n f (q, ψ q) :=
  (continuousAt_id.prodMk hψ).eventually (hf.eventually (by norm_num))

/-- The vertical part of the derivative of a `C¹` map is continuous along a continuous graph. -/
theorem continuousAt_fderiv_comp_inr {G : P × E → X} {ψ : P → E}
    (hG : ContDiffAt 𝕜 1 G (p, ψ p)) (hψ : ContinuousAt ψ p) :
    ContinuousAt (fun q ↦ (fderiv 𝕜 G (q, ψ q)).comp (ContinuousLinearMap.inr 𝕜 P E)) p :=
  ((hG.continuousAt_fderiv (by norm_num)).comp_of_eq
    (f := fun q ↦ (q, ψ q)) (continuousAt_id.prodMk hψ) rfl).clm_comp
    continuousAt_const

end ContDiffAt
