/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.WeakSpace
public import TauCeti.Analysis.Variational.BoundedSublevels
import TauCeti.Analysis.Variational.DirectMethod

/-!
# Compact perturbations in the direct method

In infinite dimensions, compact operators and nonlinear lower-order terms `g ∘ J` need not be
globally weakly continuous, and compactly defined constraint sets such as `{u ∈ S | J u ∈ C}` (for
example, Rayleigh normalization spheres `{u | ‖J u‖ = 1}`) need not be weakly closed in general.
Nevertheless, once an energy controls norm sublevels (`TauCeti.HasBoundedSublevelsOn`), every
variational argument localizes to closed norm balls, which are weakly closed over `ℝ` or `ℂ`
(`TauCeti.isClosed_toWeakSpace_closedBall`) and on which a compact operator `J` is weak-to-norm
continuous (`IsCompactOperator.continuousOn_comp_toWeakSpace_symm_of_isBounded`).

This file provides the global weak lower semicontinuity input for compactly perturbed energies
(`IsCompactOperator.lowerSemicontinuousOn_add_comp_toWeakSpace_symm_of_hasBoundedSublevelsOn`): if
`E₀` is weakly lower semicontinuous on `S`, `J : V →L[𝕜] F` is compact, `g : F → β` is lower
semicontinuous on `J '' S`, and `u ↦ E₀ u + g (J u)` has bounded sublevels on `S`, then
`u ↦ E₀ u + g (J u)` is globally weakly lower semicontinuous on `S`.

Together with bounded-ball constraint weak closedness
(`IsCompactOperator.isClosed_toWeakSpace_inter_preimage_inter_closedBall` in
`TauCeti.Analysis.Normed.Operator.Compact.WeakSpace`), this supplies the hypotheses for the general
direct-method theorems in `TauCeti.Analysis.Variational.DirectMethod` (such as
`TauCeti.exists_isMinOn_of_weak_closed`,
`TauCeti.exists_isMinOn_of_isClosed_toWeakSpace_inter_closedBall`, and
`TauCeti.isCompact_toWeakSpace_minimizers_of_isClosed_toWeakSpace_inter_closedBall`).

## References

* M. Struwe, *Variational Methods*, 4th ed., Springer, 2008, Theorem I.1.2 and Section I.2.
* E. Zeidler, *Nonlinear Functional Analysis and its Applications, III: Variational Methods and
  Optimization*, Springer, 1985, §38.3 and §38.7.
-/

public section

open Set

namespace IsCompactOperator

section CompactPerturbation

variable {𝕜 V F β : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [TopologicalSpace F] [AddCommMonoid F] [Module 𝕜 F] [ContinuousConstSMul 𝕜 F]
  [T2Space (WeakSpace 𝕜 F)]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
  [TopologicalSpace β] [OrderTopology β] [ContinuousAdd β]
  {J : V →L[𝕜] F}

/-- **Global weak lower semicontinuity of a compact perturbation under bounded sublevels.** Over
`ℝ` or `ℂ`, if `E₀` is weakly lower semicontinuous on `S`, `J : V →L[𝕜] F` is compact, `g : F → β`
is lower semicontinuous on `J '' S`, and `u ↦ E₀ u + g (J u)` has bounded sublevels on `S`, then
`u ↦ E₀ u + g (J u)` is globally weakly lower semicontinuous on `S`. -/
theorem lowerSemicontinuousOn_add_comp_toWeakSpace_symm_of_hasBoundedSublevelsOn
    (hJ : IsCompactOperator J) {S : Set V} {E₀ : V → β} {g : F → β}
    (hE₀ : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E₀ ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hg : LowerSemicontinuousOn g (J '' S))
    (hb : TauCeti.HasBoundedSublevelsOn (fun u ↦ E₀ u + g (J u)) S) :
    LowerSemicontinuousOn
      (fun w : WeakSpace 𝕜 V ↦
        E₀ ((toWeakSpace 𝕜 V).symm w) + g (J ((toWeakSpace 𝕜 V).symm w)))
      (toWeakSpace 𝕜 V '' S) :=
  TauCeti.lowerSemicontinuousOn_comp_toWeakSpace_symm_of_hasBoundedSublevelsOn hb fun _ hBS hB ↦
    hJ.lowerSemicontinuousOn_add_comp_toWeakSpace_symm hB
      (hE₀.mono (image_mono hBS)) (hg.mono (image_mono hBS))

end CompactPerturbation

end IsCompactOperator
