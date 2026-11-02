/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.OrbitIntegral
public import TauCeti.MeasureTheory.Group.Convolution.UCB

/-!
# Invariant means and convolution of `L∞` with `L¹`

Let `μ` be a regular left Haar measure on a locally compact group `G`. Convolution with a kernel
`h ∈ L¹(G, μ)` smooths `φ ∈ L∞(G, μ)` into the function

```text
(h ⋆ φ) x = ∫ y, h y * φ (y⁻¹ * x) ∂μ
```

in `TauCeti.UCB G` (`MeasureTheory.Lp.convolutionUCB`). This file records how a left-invariant
mean `m` on `UCB G` interacts with this smoothing.

* On the class of a function `ψ` already in `UCB G`, the convolution `h ⋆ ψ` is the orbit
  integral `∫ y, h y • L_y ψ ∂μ`, so invariance of `m` gives `m (h ⋆ ψ) = (∫ h dμ) * m ψ`.
* Left translating the kernel left translates the convolution, `(L_g h) ⋆ φ = L_g (h ⋆ φ)`, so
  `m ((L_g h) ⋆ φ) = m (h ⋆ φ)`.
* Convolution is associative across `L¹` and `L∞`: for kernels `h, k ∈ L¹(G, μ)`, smoothing `φ`
  by the `L¹` convolution `h ⋆ k` (`MeasureTheory.Lp.convolutionL`) is smoothing `φ` by `k` and
  then the class of `k ⋆ φ` in `L∞` by `h` (`MeasureTheory.Lp.convolutionUCB_convolutionL`). Hence
  `m ((h ⋆ k) ⋆ φ) = (∫ h dμ) * m (k ⋆ φ)`.

Together with `h ⋆ (L_g φ) = (R_(g⁻¹) h) ⋆ φ`
(`MeasureTheory.Lp.convolutionUCB_apply_leftTranslation`), whose kernel `R_(g⁻¹) h` is again
nonnegative of integral one when `h` is, these identities are the tools for comparing `m` with
the functional `φ ↦ m (h ⋆ φ)` on `L∞(G, μ)`. That functional is a positive normalized functional
on `L∞` for every nonnegative kernel of integral one; it is left invariant once its value is known
not to depend on the choice of such a kernel.

## Main results

* `MeasureTheory.Lp.convolutionUCB_toLpTop`: `h ⋆ ψ = ∫ y, h y • L_y ψ ∂μ` for `ψ ∈ UCB G`.
* `TauCeti.Mean.IsLeftInvariant.apply_convolutionUCB_toLpTop`: a left-invariant mean satisfies
  `m (h ⋆ ψ) = (∫ h dμ) * m ψ` for `ψ ∈ UCB G`.
* `TauCeti.Mean.IsLeftInvariant.apply_convolutionUCB_leftTranslation`: a left-invariant mean
  satisfies `m ((L_g h) ⋆ φ) = m (h ⋆ φ)`.
* `TauCeti.Mean.IsLeftInvariant.apply_convolutionUCB_convolutionL`: a left-invariant mean
  satisfies `m ((h ⋆ k) ⋆ φ) = (∫ h dμ) * m (k ⋆ φ)`.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G, proof of
  Theorem G.3.1.
-/

public section

open MeasureTheory
open scoped ENNReal BoundedContinuousFunction

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [μ.IsHaarMeasure] [μ.Regular]

namespace MeasureTheory.Lp

open TauCeti

/-- The convolution `h ⋆ ψ` of a kernel `h ∈ L¹(G, μ)` with the class of a function `ψ ∈ UCB G`
is the `UCB G`-valued orbit integral `∫ y, h y • L_y ψ ∂μ`. -/
theorem convolutionUCB_toLpTop (h : Lp ℝ 1 μ) (ψ : UCB G) :
    convolutionUCB h (BoundedContinuousFunction.toLpTop μ ℝ (ψ : G →ᵇ ℝ)) =
      ∫ y, h y • UCB.leftTranslation y ψ ∂μ := by
  refine UCB.ext fun x => ?_
  rw [convolutionUCB_apply_of_ae_eq (ae_eq_refl _)
      (BoundedContinuousFunction.coeFn_toLpTop μ (ψ : G →ᵇ ℝ)) x,
    UCB.integral_smul_leftTranslation_apply (L1.integrable_coeFn h)]

end MeasureTheory.Lp

namespace TauCeti.Mean

/-- A left-invariant mean takes the value `(∫ h dμ) * m ψ` at the convolution `h ⋆ ψ` of a kernel
`h ∈ L¹(G, μ)` with the class of a function `ψ ∈ UCB G`. In particular `m (h ⋆ ψ) = m ψ` when
`h` has integral one. -/
theorem IsLeftInvariant.apply_convolutionUCB_toLpTop {m : Mean G} (hm : m.IsLeftInvariant)
    (h : Lp ℝ 1 μ) (ψ : UCB G) :
    m (Lp.convolutionUCB h (BoundedContinuousFunction.toLpTop μ ℝ (ψ : G →ᵇ ℝ))) =
      (∫ y, h y ∂μ) * m ψ := by
  rw [Lp.convolutionUCB_toLpTop, hm.apply_integral_smul_leftTranslation (L1.integrable_coeFn h)]

/-- A left-invariant mean does not see left translation of the kernel:
`m ((L_g h) ⋆ φ) = m (h ⋆ φ)`. -/
theorem IsLeftInvariant.apply_convolutionUCB_leftTranslation {m : Mean G}
    (hm : m.IsLeftInvariant) (g : G) (h : Lp ℝ 1 μ) (φ : Lp ℝ ∞ μ) :
    m (Lp.convolutionUCB (Lp.leftTranslation μ 1 ℝ g h) φ) = m (Lp.convolutionUCB h φ) := by
  rw [Lp.convolutionUCB_leftTranslation_apply, hm.apply_leftTranslation]

/-- A left-invariant mean takes the value `(∫ h dμ) * m (k ⋆ φ)` at `(h ⋆ k) ⋆ φ`, for kernels
`h, k ∈ L¹(G, μ)` and `φ ∈ L∞(G, μ)`. In particular `m ((h ⋆ k) ⋆ φ) = m (k ⋆ φ)` when `h` has
integral one. -/
theorem IsLeftInvariant.apply_convolutionUCB_convolutionL {m : Mean G} (hm : m.IsLeftInvariant)
    (h k : Lp ℝ 1 μ) (φ : Lp ℝ ∞ μ) :
    m (Lp.convolutionUCB (Lp.convolutionL μ 1 ENNReal.one_ne_top h k) φ) =
      (∫ y, h y ∂μ) * m (Lp.convolutionUCB k φ) := by
  rw [Lp.convolutionUCB_convolutionL, hm.apply_convolutionUCB_toLpTop]

end TauCeti.Mean
