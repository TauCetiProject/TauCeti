/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RootsOfUnity.Quotient
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Power

/-!
# The rotated disc as a Riemann surface, and the power map

The disc `TauCeti.rootsOfUnityBall m r` of radius `r` about `0`, on which the `m`-th roots of unity
act by rotations, is an open subset of `ℂ`. This file gives it the charts of `ℂ` restricted to it,
so that it is a one-dimensional complex manifold, and its inclusion into `ℂ` is a local
biholomorphism (`TauCeti.isLocalDiffeomorph_coe_rootsOfUnityBall`).

The quotient of the disc by the rotations has the coordinate `u ↦ u ^ m`
(`TauCeti.rootsOfUnityBallQuotientHomeomorph`). Away from the centre this coordinate is a local
biholomorphism (`TauCeti.isLocalDiffeomorphAt_coe_pow_rootsOfUnityBall`): by the inverse function
theorem, since its derivative `m u ^ (m - 1)` does not vanish. It is deduced from the general
statement `TauCeti.isLocalDiffeomorphAt_pow` for `w ↦ w ^ k` on any `RCLike` field. At the
centre `u ↦ u ^ m` vanishes to order `m` (Mathlib's `analyticOrderAt_centeredMonomial`), so for
`m ≥ 2` it is not a local biholomorphism there.

These are the local inputs for descending maps through the quotient of a family over the disc by
the rotations, along the coordinate `t = u ^ m` of the quotient disc.

## Main declarations

* `TauCeti.rootsOfUnityBall.instChartedSpace`, `TauCeti.rootsOfUnityBall.instIsManifold`: the disc
  is a complex manifold, with the restricted charts of `ℂ`.
* `TauCeti.isLocalDiffeomorph_coe_rootsOfUnityBall`: the inclusion of the disc into `ℂ` is a local
  biholomorphism.
* `TauCeti.isLocalDiffeomorphAt_coe_pow_rootsOfUnityBall`: `u ↦ u ^ m` is a local biholomorphism
  from the disc to `ℂ` away from the centre.

## References

* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Chapter II §4 (the local normal form
  `z ↦ z ^ m` of a holomorphic map, a local biholomorphism exactly where `m = 1`).
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {m : ℕ} [NeZero m] {r : ℝ}

/-- The rotated disc is an open subset of `ℂ`. -/
theorem isOpen_rootsOfUnityBall (r : ℝ) : IsOpen (rootsOfUnityBall m r : Set ℂ) := by
  rw [coe_rootsOfUnityBall]
  exact Metric.isOpen_ball

/-- The rotated disc is charted by the charts of `ℂ` restricted to it, as an open subset. -/
noncomputable instance rootsOfUnityBall.instChartedSpace (r : ℝ) :
    ChartedSpace ℂ (rootsOfUnityBall m r) :=
  inferInstanceAs (ChartedSpace ℂ (⟨_, isOpen_rootsOfUnityBall r⟩ : TopologicalSpace.Opens ℂ))

/-- The rotated disc is a complex manifold, an open subset of `ℂ`. -/
instance rootsOfUnityBall.instIsManifold (r : ℝ) {n : ℕ∞ω} :
    IsManifold 𝓘(ℂ) n (rootsOfUnityBall m r) :=
  inferInstanceAs (IsManifold 𝓘(ℂ) n (⟨_, isOpen_rootsOfUnityBall r⟩ : TopologicalSpace.Opens ℂ))

/-- The rotated disc is locally compact, being a manifold modelled on `ℂ`. -/
instance rootsOfUnityBall.instLocallyCompactSpace (r : ℝ) :
    LocallyCompactSpace (rootsOfUnityBall m r) :=
  ChartedSpace.locallyCompactSpace ℂ _

/-- The inclusion of the rotated disc into `ℂ` is a local biholomorphism. -/
theorem isLocalDiffeomorph_coe_rootsOfUnityBall {n : ℕ∞ω} :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) n ((↑) : rootsOfUnityBall m r → ℂ) :=
  isLocalDiffeomorph_subtype_val (U := ⟨_, isOpen_rootsOfUnityBall r⟩)

/-- The coordinate `u ↦ u ^ m` of the quotient of the rotated disc is holomorphic. -/
theorem contMDiff_coe_pow_rootsOfUnityBall {n : ℕ∞ω} :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) n fun u : rootsOfUnityBall m r ↦ (u : ℂ) ^ m :=
  (contDiff_id.pow m).contMDiff.comp isLocalDiffeomorph_coe_rootsOfUnityBall.contMDiff

/-- **The quotient coordinate is a local biholomorphism off the centre.** For `1 ≤ n`, the map
`u ↦ u ^ m` from the rotated disc to `ℂ` is a `C^n` local diffeomorphism at every point other
than the centre. -/
theorem isLocalDiffeomorphAt_coe_pow_rootsOfUnityBall {n : ℕ∞ω} (hn : 1 ≤ n)
    {u : rootsOfUnityBall m r} (hu : (u : ℂ) ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) n (fun u : rootsOfUnityBall m r ↦ (u : ℂ) ^ m) u :=
  IsLocalDiffeomorphAt.comp (K := 𝓘(ℂ)) (P := ℂ) (isLocalDiffeomorph_coe_rootsOfUnityBall u)
    (isLocalDiffeomorphAt_pow hn (NeZero.ne m) hu)

end TauCeti
