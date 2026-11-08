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

The partial derivative in the second variable of a `C^n` function on a product, applied to a fixed
vector, is `C^(n - 1)` jointly (`TauCeti.contDiffAt_fderiv_snd_apply`).
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

/-- The partial derivative in the second variable of a function of `(r.1, z)`, applied to a fixed
vector, is as differentiable in `r` as the function allows. -/
theorem contDiffAt_fderiv_snd_apply {f : E × G → F} {r : E × G} {m : WithTop ℕ∞}
    (hf : ContDiffAt 𝕜 n f r) (hmn : m + 1 ≤ n) (v : G) :
    ContDiffAt 𝕜 m (fun r : E × G ↦ fderiv 𝕜 (fun z ↦ f (r.1, z)) r.2 v) r :=
  (ContDiffAt.fderiv (f := fun (r : E × G) z ↦ f (r.1, z)) (g := Prod.snd)
    (hf.comp _ (by fun_prop)) contDiffAt_snd hmn).clm_apply contDiffAt_const

end TauCeti
