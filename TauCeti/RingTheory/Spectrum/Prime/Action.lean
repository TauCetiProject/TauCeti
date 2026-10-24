/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Continuity of automorphisms on the prime spectrum

A group acting by semiring automorphisms acts on the prime spectrum by homeomorphisms.
Only continuity for each fixed group element is asserted; no topology on the acting group
is needed. In particular, the action induces an action on connected components.
-/

public section

namespace PrimeSpectrum

variable {G R : Type*} [Group G] [CommSemiring R] [MulSemiringAction G R]

/-- Each semiring automorphism acts continuously on the prime spectrum. -/
instance : ContinuousConstSMul G (PrimeSpectrum R) where
  continuous_const_smul g := by
    have h : (fun p : PrimeSpectrum R ↦ g • p) =
        homeomorphOfRingEquiv (MulSemiringAction.toRingAut G R g) := by
      funext p
      apply PrimeSpectrum.ext
      exact Ideal.pointwise_smul_eq_comap p.asIdeal
    rw [h]
    exact (homeomorphOfRingEquiv (MulSemiringAction.toRingAut G R g)).continuous

end PrimeSpectrum
