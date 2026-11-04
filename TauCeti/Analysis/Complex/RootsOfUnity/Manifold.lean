/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import TauCeti.Analysis.Complex.RootsOfUnity.Quotient

/-!
# The rotated disc as a complex manifold

The open disc `TauCeti.rootsOfUnityBall m r` of radius `r` about `0` in `ℂ` is an open subset of
`ℂ`, so it is a complex manifold modelled on `ℂ`, with the charts of `ℂ` restricted to it. The
group `rootsOfUnity m ℂ` of `m`-th roots of unity acts on it by the rotations `u ↦ ζ u`, which
are restrictions of complex linear maps of `ℂ`, hence holomorphic.

These instances make the disc with its rotations a base to which the manifold and quotient
constructions for actions by `C^n` maps apply, for instance families of complex tori over the disc
on which the rotations lift.

## Main declarations

* `TauCeti.rootsOfUnityBall.opens`: the disc as an open subset of `ℂ`, whose subtype is the
  disc itself.
* `TauCeti.rootsOfUnityBall.instChartedSpace`, `TauCeti.rootsOfUnityBall.instIsManifold`: the disc
  is a `C^n` manifold modelled on `ℂ` for every `n`; for `n = ω` it is a complex manifold.
* `TauCeti.rootsOfUnityBall.contMDiff_val`: the inclusion of the disc into `ℂ` is holomorphic.
* `TauCeti.rootsOfUnityBall.instContMDiffConstSMul`: the rotations act on the disc by `C^n` maps,
  that is, by biholomorphisms.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {m : ℕ} [NeZero m] {r : ℝ} {n : ℕ∞ω}

namespace rootsOfUnityBall

variable (m r) in
/-- The disc of radius `r` as an open subset of `ℂ`. Its carrier is `Metric.ball 0 r`, the carrier
of `rootsOfUnityBall m r`, so its subtype is definitionally the subtype of `rootsOfUnityBall m r`;
the instances below transfer the open-subset manifold structure of `ℂ` along this equality. -/
noncomputable def opens : TopologicalSpace.Opens ℂ :=
  ⟨rootsOfUnityBall m r, isOpen_rootsOfUnityBall⟩

/-- The disc of radius `r` is an open subset of `ℂ`, so it inherits the charts of `ℂ`. -/
noncomputable instance instChartedSpace : ChartedSpace ℂ (rootsOfUnityBall m r) :=
  inferInstanceAs (ChartedSpace ℂ (opens m r))

/-- The disc of radius `r` is a `C^n` manifold modelled on `ℂ`; for `n = ω` it is a complex
manifold. -/
instance instIsManifold : IsManifold 𝓘(ℂ) n (rootsOfUnityBall m r) :=
  inferInstanceAs (IsManifold 𝓘(ℂ) n (opens m r))

/-- The rotations by the `m`-th roots of unity act on the disc of radius `r` by `C^n` maps; for
`n = ω` they are biholomorphisms of the disc. -/
instance instContMDiffConstSMul : ContMDiffConstSMul 𝓘(ℂ) n (rootsOfUnity m ℂ)
    (rootsOfUnityBall m r) where
  contMDiff_const_smul ζ := by
    have h : ContMDiff 𝓘(ℂ) 𝓘(ℂ) n (Subtype.val ∘ fun u : opens m r ↦
        (⟨ζ • (u : ℂ), (rootsOfUnityBall m r).smul_mem ζ u.2⟩ : opens m r)) :=
      (contMDiff_iff_contDiff.2 (contDiff_const_smul ((ζ : ℂˣ) : ℂ))).comp contMDiff_subtype_val
    exact fun u ↦ (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ _ _).1 (h u)

/-- The inclusion of the disc of radius `r` into `ℂ` is `C^n`; it is holomorphic. -/
theorem contMDiff_val : ContMDiff 𝓘(ℂ) 𝓘(ℂ) n ((↑) : rootsOfUnityBall m r → ℂ) :=
  contMDiff_subtype_val (U := opens m r)

end rootsOfUnityBall

end TauCeti
