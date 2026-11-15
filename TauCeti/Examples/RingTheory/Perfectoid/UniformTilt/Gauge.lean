/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.UniformTilt.Gauge
public import TauCeti.RingTheory.Perfectoid.Padic
public import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# Checks for the spectral gauge on a tilt

The tilt of `ℂ_p` contains the shifted compatible roots of any compatible-root parameter. Its
spectral gauge agrees with the original gauge after applying sharp. These checks compute the
gauges of the parameter, its fractional powers and its inverse, and detect that the inverse is
not power-bounded. The final check exercises the comparison on a zero ring.
-/

public section

open TauCeti.Huber TauCeti.Perfectoid

namespace TauCeti.Examples.UniformTiltGauge

variable (p : ℕ) [Fact p.Prime]

local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p])) :=
  ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one (PadicComplex.norm_p_lt_one p)⟩

private noncomputable def parameter : PseudoUniformizerRoots p ℂ_[p] :=
  Classical.choice (nonempty_pseudoUniformizerRoots_of_isAlgClosed (PadicComplex.norm_p_lt_one p))

local instance : IsTateRing (uniformTilt p ℂ_[p]) :=
  uniformTilt.isTateRing_of_sharp (ϖ := (parameter p).toTilt)
    (by simpa using (parameter p).isPseudoUniformizer_root_zero)

local instance : IsPerfectoidTateRing p (uniformTilt p ℂ_[p]) :=
  uniformTilt.isPerfectoidTateRing_of_sharp (ϖ := (parameter p).toTilt)
    (by simpa using (parameter p).isPseudoUniformizer_root_zero)

local instance : IsUniform (uniformTilt p ℂ_[p]) :=
  IsPerfectoidTateRing.isUniform p

example (n m : ℕ) :
    uniformTilt.coeff p ℂ_[p] m ((parameter p).tiltRoots.root n) =
      (parameter p).root (n + m) := by
  simp

example (x : uniformTilt p ℂ_[p]) :
    (parameter p).gauge (uniformTilt.coeff p ℂ_[p] 0 x) =
      (parameter p).tiltRoots.gauge x := by
  simp

example : (parameter p).tiltRoots.gauge (parameter p).toTilt = 1 / 2 := by
  rw [← uniformTilt.gauge_sharp_tiltRoots]
  simp

example (n : ℕ) :
    (parameter p).gauge (uniformTilt.coeff p ℂ_[p] 0 ((parameter p).tiltRoots.root n)) =
      2 ^ (-(1 / (p : ℝ) ^ n)) := by
  simp

example :
    (parameter p).gauge
      (uniformTilt.coeff p ℂ_[p] 0 ((parameter p).tiltRoots.zpow (-1) 0)) = 2 := by
  rw [uniformTilt.gauge_sharp_tiltRoots]
  rw [(parameter p).tiltRoots.gauge_zpow]
  norm_num

example : ((parameter p).tiltRoots.zpow (-1) 0 : uniformTilt p ℂ_[p]) ∉
    powerBoundedSubring (uniformTilt p ℂ_[p]) := by
  rw [← (parameter p).tiltRoots.gauge_le_one_iff]
  rw [(parameter p).tiltRoots.gauge_zpow]
  norm_num

-- No nonzero-ring or characteristic-exactly-p hypothesis is hidden in the comparison.
example {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B] [Subsingleton B]
    [IsUniform B] [Fact (IsTopologicallyNilpotent (p : B))]
    [IsTateRing (uniformTilt p B)] [IsUniform (uniformTilt p B)]
    (ϖ : PseudoUniformizerRoots p B) (x : uniformTilt p B) :
    ϖ.gauge (uniformTilt.coeff p B 0 x) = 0 ∧ ϖ.tiltRoots.gauge x = 0 := by
  have hz : uniformTilt.coeff p B 0 x = 0 := Subsingleton.elim _ _
  constructor
  · rw [hz, map_zero]
  · rw [← uniformTilt.gauge_sharp_tiltRoots, hz, map_zero]

end TauCeti.Examples.UniformTiltGauge
