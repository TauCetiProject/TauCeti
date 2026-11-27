/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Smoothness of within-derivative lifts

If `f : E → F` is `C^n` on a set `s` with unique derivatives and `m + 1 ≤ n`, then its
within-derivative lift `q ↦ (f q.1, (fderivWithin 𝕜 f s q.1).comp q.2)` is `C^m` on
`s ×ˢ Set.univ` (`ContDiffOn.prodMk_fderivWithin_comp`). This is the variational lift used to
propagate higher regularity along first-order equations and flows.
-/

public section

open scoped ContDiff

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- **Smoothness of the first-order within-derivative lift.** If `f : E → F` is `C^n` on a set
`s` with unique derivatives and `m + 1 ≤ n`, then the lifted map
`q ↦ (f q.1, (fderivWithin 𝕜 f s q.1).comp q.2)` on `E × (G →L[𝕜] E)` is `C^m` on
`s ×ˢ Set.univ`. -/
theorem ContDiffOn.prodMk_fderivWithin_comp {m n : ℕ∞ω} {s : Set E} {f : E → F}
    (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (fun q : E × (G →L[𝕜] E) ↦ (f q.1, (fderivWithin 𝕜 f s q.1).comp q.2))
      (s ×ˢ Set.univ) :=
  ((hf.of_le (le_trans le_self_add hmn)).comp contDiffOn_fst Set.mapsTo_fst_prod).prodMk
    (((hf.fderivWithin hs hmn).comp contDiffOn_fst Set.mapsTo_fst_prod).clm_comp contDiffOn_snd)
