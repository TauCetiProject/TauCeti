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

Likewise, a function smooth at the image `g a` of a point under a map `g` continuous at `a` is
differentiable at `g z` for all `z` near `a` (`ContDiffAt.eventually_differentiableAt_comp`).
-/

public section

open scoped ContDiff

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

open Filter in
/-- **Smoothness at `g a` gives differentiability along `g` nearby**: if `f` is `C^n` at `g a` and
`g` is continuous at `a`, with `n ≠ 0` and `n ≠ ∞`, then `f` is differentiable at `g z` for all
`z` near `a`. -/
theorem _root_.ContDiffAt.eventually_differentiableAt_comp {α : Type*} [TopologicalSpace α]
    {f : E → F} {g : α → E} {a : α} (hf : ContDiffAt 𝕜 n f (g a)) (hg : ContinuousAt g a)
    (hn : n ≠ 0) (hn' : n ≠ ∞) : ∀ᶠ z in nhds a, DifferentiableAt 𝕜 f (g z) :=
  (hg.eventually (hf.eventually hn')).mono fun _ h ↦ h.differentiableAt hn

end TauCeti
