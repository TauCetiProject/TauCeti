/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import TauCeti.Analysis.Complex.RootsOfUnity.Quotient
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Power

/-!
# The rotated disc as a complex manifold

The open disc `TauCeti.rootsOfUnityBall m r` of radius `r` about `0` in `ℂ` is an open subset of
`ℂ`, so it is a complex manifold modelled on `ℂ`, with the charts of `ℂ` restricted to it. The
group `rootsOfUnity m ℂ` of `m`-th roots of unity acts on it by the rotations `u ↦ ζ u`, which
are restrictions of complex linear maps of `ℂ`, hence holomorphic.

These instances make the disc with its rotations a base to which the manifold and quotient
constructions for actions by `C^n` maps apply, for instance families of complex tori over the disc
on which the rotations lift.

The quotient of the disc by the rotations has the coordinate `u ↦ u ^ m`
(`TauCeti.rootsOfUnityBallQuotientHomeomorph`). Away from the centre this coordinate is a local
biholomorphism (`TauCeti.rootsOfUnityBall.isLocalDiffeomorphAt_pow`): by the inverse function
theorem, since its derivative `m u ^ (m - 1)` does not vanish. At the centre `u ↦ u ^ m` vanishes
to order `m` (Mathlib's `analyticOrderAt_centeredMonomial`), so for `m ≥ 2` it is not a local
biholomorphism there.

## Main declarations

* `TauCeti.rootsOfUnityBall.opens`: the disc as an open subset of `ℂ`, whose subtype is the
  disc itself.
* `TauCeti.rootsOfUnityBall.instChartedSpace`, `TauCeti.rootsOfUnityBall.instIsManifold`: the disc
  is a `C^n` manifold modelled on `ℂ` for every `n`; for `n = ω` it is a complex manifold.
* `TauCeti.rootsOfUnityBall.contMDiff_val`: the inclusion of the disc into `ℂ` is holomorphic.
* `TauCeti.rootsOfUnityBall.instContMDiffConstSMul`: the rotations act on the disc by `C^n` maps,
  that is, by biholomorphisms.
* `TauCeti.rootsOfUnityBall.isLocalDiffeomorph_val`: the inclusion of the disc into `ℂ` is a local
  biholomorphism.
* `TauCeti.rootsOfUnityBall.isLocalDiffeomorphAt_pow`: `u ↦ u ^ m` is a local biholomorphism from
  the disc to `ℂ` away from the centre.

## References

* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Chapter II §4 (the local normal form
  `z ↦ z ^ m` of a holomorphic map, a local biholomorphism exactly where `m = 1`).
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

/-- The inclusion of the disc of radius `r` into `ℂ` is a local biholomorphism. -/
theorem isLocalDiffeomorph_val : IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) n ((↑) : rootsOfUnityBall m r → ℂ) :=
  isLocalDiffeomorph_subtype_val (U := opens m r)

/-- **The quotient coordinate is a local biholomorphism off the centre.** For `1 ≤ n`, the map
`u ↦ u ^ m` from the disc of radius `r` to `ℂ` is a `C^n` local diffeomorphism at every point other
than the centre. -/
theorem isLocalDiffeomorphAt_pow (hn : 1 ≤ n) {u : rootsOfUnityBall m r} (hu : (u : ℂ) ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) n (fun u : rootsOfUnityBall m r ↦ (u : ℂ) ^ m) u :=
  IsLocalDiffeomorphAt.comp (K := 𝓘(ℂ)) (P := ℂ) (isLocalDiffeomorph_val u)
    (TauCeti.isLocalDiffeomorphAt_pow hn (NeZero.ne m) hu)

end rootsOfUnityBall

end TauCeti
