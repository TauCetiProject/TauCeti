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

Likewise, if `S` on `E × G` and `T` on `G × E'` are smooth at the two reindexed copies of a point
of `(E × E') × G`, both are differentiable at the corresponding points near it
(`TauCeti.eventually_differentiableAt_comp_prod_assoc`).
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
/-- **Smoothness at a reindexed point gives differentiability nearby**: if `S` is `C^n` at
`(x.1.1, x.2)` and `T` is `C^n` at `(x.2, x.1.2)`, with `n ≠ 0` and `n ≠ ∞`, then `S` and `T`
are differentiable at the reindexed points `(z.1.1, z.2)` and `(z.2, z.1.2)` for all `z` near
`x`. -/
theorem eventually_differentiableAt_comp_prod_assoc {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    {S : E × G → F} {T : G × E' → F'} {x : (E × E') × G}
    (hn : n ≠ 0) (hn' : n ≠ ∞) (hS : ContDiffAt 𝕜 n S (x.1.1, x.2))
    (hT : ContDiffAt 𝕜 n T (x.2, x.1.2)) :
    ∀ᶠ z in nhds x, DifferentiableAt 𝕜 S (z.1.1, z.2) ∧ DifferentiableAt 𝕜 T (z.2, z.1.2) := by
  have h₁ := ((continuousAt_fst (p := x)).fst.prodMk continuousAt_snd).eventually
    (hS.eventually hn')
  have h₂ := ((continuousAt_snd (p := x)).prodMk continuousAt_fst.snd).eventually
    (hT.eventually hn')
  exact (h₁.mono fun _ h ↦ h.differentiableAt hn).and (h₂.mono fun _ h ↦ h.differentiableAt hn)

end TauCeti
