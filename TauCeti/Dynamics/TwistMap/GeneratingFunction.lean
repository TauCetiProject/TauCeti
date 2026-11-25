/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.TwistMap.OpenStrip
public import TauCeti.Geometry.Symplectic.Annulus.TwistBand

/-!
# The generating function of an exact monotone twist map

Let `F` be a monotone twist map of the open strip `ℝ × J` (`TauCeti.IsMonotoneTwistMap`) and
`Q(x, y) = (x, F₁(x, y))` its twist coordinates (`TauCeti.stripTwistCoord`), which record the
first coordinates of the two ends of the step `(x, y) ↦ F(x, y)`. Since `y ↦ F₁(x, y)` is strictly
increasing with `∂_y F₁ > 0`, `Q` is injective on the strip
(`TauCeti.IsMonotoneTwistMap.injOn_stripTwistCoord`) and a local diffeomorphism there, so its image
`D` is open (`TauCeti.IsMonotoneTwistMap.isOpen_image_stripTwistCoord`).

If `F` is exact for the primitive `λ = g dx` with primitive `S`, that is
`dS_p = g(F p) (dF_p)₁ − g(p) dx` on the strip, then `h = S ∘ Q⁻¹ : D → ℝ`, the band generating
function `TauCeti.stripBandGeneratingFunction F J S`, is a generating function of `F`
(`TauCeti.IsMonotoneTwistMap.hasFDerivAt_stripBandGeneratingFunction`):

`dh_{Q(p)} = g(F p) dX − g(p) dx`, that is `g(x, y) = −∂₁h(x, F₁(x, y))` and
`g(F(x, y)) = ∂₂h(x, F₁(x, y))`,

with `h ∘ Q = S` on the strip (`TauCeti.stripBandGeneratingFunction_stripTwistCoord`), and `h`
is invariant under the diagonal deck translation `(x, X) ↦ (x + ℓ, X + ℓ)` when `S` is `ℓ`-periodic
(`TauCeti.IsMonotoneTwistMap.periodic_stripBandGeneratingFunction`).

## References

* M. R. Herman, *Sur les courbes invariantes par les difféomorphismes de l'anneau, Vol. 1*,
  Astérisque 103–104, 1983, Chapitre I, §4.3.
-/

public section

noncomputable section

open Set Filter Topology Function

namespace TauCeti

namespace IsMonotoneTwistMap

variable {ℓ : ℝ} {J : Set ℝ} {F : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}

/-- **The twist coordinates are injective on the strip**, by the twist condition. -/
theorem injOn_stripTwistCoord (hF : IsMonotoneTwistMap ℓ J F) :
    InjOn (stripTwistCoord F) (Prod.snd ⁻¹' J) :=
  TauCeti.injOn_stripTwistCoord hF.ordConnected fun q hq =>
    (hF.fderiv_fst_pos q ⟨mem_univ _, hq⟩).ne'

/-- **The image `D` of the strip under the twist coordinates is open.** -/
theorem isOpen_image_stripTwistCoord (hF : IsMonotoneTwistMap ℓ J F) :
    IsOpen (stripTwistCoord F '' (Prod.snd ⁻¹' J)) :=
  TauCeti.isOpen_image_stripTwistCoord le_rfl hF.isOpen
    (fun _ hq => hF.contDiffOn.contDiffAt (hF.isOpen_strip.mem_nhds ⟨mem_univ _, hq⟩))
    fun q hq => (hF.fderiv_fst_pos q ⟨mem_univ _, hq⟩).ne'

/-- **The generating function of an exact monotone twist map.** If `S` satisfies
`dS_p = g(F p) (dF_p)₁ − g(p) dx` at a point `p` of the strip, as a primitive of `F*λ − λ` for
`λ = g dx` does everywhere on the strip, then `h = S ∘ Q⁻¹` has derivative
`g(F p) dX − g(p) dx` at `Q(p) = (x, F₁(x, y))`: `∂₁h(x, F₁(x, y)) = −g(x, y)` and
`∂₂h(x, F₁(x, y)) = g(F(x, y))`. -/
theorem hasFDerivAt_stripBandGeneratingFunction (hF : IsMonotoneTwistMap ℓ J F)
    {g S : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hp : p ∈ univ ×ˢ J)
    (hS : HasFDerivAt S (g (F p) • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (fderiv ℝ F p) - g p • ContinuousLinearMap.fst ℝ ℝ ℝ) p) :
    HasFDerivAt (stripBandGeneratingFunction F J S)
      (g (F p) • ContinuousLinearMap.snd ℝ ℝ ℝ - g p • ContinuousLinearMap.fst ℝ ℝ ℝ)
      (stripTwistCoord F p) :=
  hasFDerivAt_of_eventuallyEq_comp_stripTwistCoord
    (hF.contDiffOn.contDiffAt (hF.isOpen_strip.mem_nhds hp)) one_ne_zero
    (hF.fderiv_fst_pos p hp).ne' hS <|
    eventually_of_mem (hF.isOpen_strip.mem_nhds hp) fun _ hq =>
      stripBandGeneratingFunction_stripTwistCoord hF.injOn_stripTwistCoord hq.2

/-- **The generating function is invariant under the diagonal deck translation**
`(x, X) ↦ (x + ℓ, X + ℓ)` when the primitive `S` is `ℓ`-periodic in `x`. -/
theorem periodic_stripBandGeneratingFunction (hF : IsMonotoneTwistMap ℓ J F) {S : ℝ × ℝ → ℝ}
    (hper : ∀ x, ∀ y ∈ J, S (x + ℓ, y) = S (x, y)) :
    Periodic (stripBandGeneratingFunction F J S) (ℓ, ℓ) :=
  TauCeti.periodic_stripBandGeneratingFunction hF.injOn_stripTwistCoord
    (fun ⟨x, y⟩ hy => by simpa using hF.apply_add_period x y hy)
    fun ⟨x, y⟩ hy => by simpa using hper x y hy

end IsMonotoneTwistMap

end TauCeti
