/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.FiniteQuotient
public import Mathlib.Analysis.Normed.Operator.Banach
public import TauCeti.RingTheory.Huber.PowerBounded

import TauCeti.Analysis.Normed.Algebra.AutomaticContinuity
import TauCeti.RingTheory.Ideal.KrullIntersection
import TauCeti.RingTheory.Huber.ClosedSubmodule
import TauCeti.RingTheory.Huber.Normed
import TauCeti.RingTheory.Huber.OpenIdeal
import TauCeti.Topology.Algebra.Ring.Ideal

/-!
# Automatic continuity for affinoid algebras

Every algebra homomorphism from a noetherian ultrametric Banach algebra into an affinoid
algebra carrying a complete compatible ultrametric algebra norm is continuous. No continuity
of a Tate presentation is assumed. Finite quotients by powers of all maximal ideals separate
the target, including its nilpotents; continuity into these quotients closes the graph.
Consequently such homomorphisms also preserve power-boundedness.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§3.7.5 and 6.1.3.
-/

public section

namespace TauCeti.IsAffinoidAlgebra

open Filter Topology

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A]
    [CompleteSpace A]

/-- Every homomorphism from a noetherian ultrametric Banach algebra to a completely normed
affinoid algebra is continuous. The affinoid presentation is purely algebraic. -/
theorem continuous_algHom (hA : IsAffinoidAlgebra K A)
    {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B]
    [CompleteSpace B] [IsNoetherianRing B] (f : B →ₐ[K] A) : Continuous f := by
  have := hA.isNoetherianRing
  let : Huber.IsTateRing A := Huber.IsTateRing.of_normedAlgebra K A
  apply f.toLinearMap.continuous_of_seq_closed_graph
  intro u x y hu huy
  suffices y - f x ∈ (⊥ : Ideal A) by
    exact sub_eq_zero.mp this
  rw [← Ideal.iInf_isMaximal_pow_eq_bot]
  simp only [Ideal.mem_iInf]
  intro m hm n hn
  let := hm
  let I := m ^ n
  have : IsClosed (I : Set A) := Huber.isClosed_of_isNoetherian I
  have : Module.Finite K (A ⧸ I) := hA.finite_quotient_pow m n
  let q := Ideal.Quotient.mkₐ K I
  have hq : Continuous q := continuous_quot_mk
  have hqf : Continuous (q.comp f) := continuous_algHom_of_finiteDimensional K (q.comp f)
  have heq : q y = q (f x) := tendsto_nhds_unique
    ((hq.tendsto y).comp huy) ((hqf.tendsto x).comp hu)
  exact Ideal.Quotient.eq_zero_iff_mem.mp (by
    simpa only [q, map_sub, Ideal.Quotient.mkₐ_eq_mk] using sub_eq_zero.mpr heq)

/-- Every homomorphism from a noetherian ultrametric Banach algebra to a completely normed
affinoid algebra maps power-bounded elements to power-bounded elements. -/
theorem isPowerBounded_map (hA : IsAffinoidAlgebra K A)
    {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B]
    [CompleteSpace B] [IsNoetherianRing B] (f : B →ₐ[K] A) {b : B}
    (hb : Huber.IsPowerBounded b) : Huber.IsPowerBounded (f b) :=
  have := Huber.IsTateRing.of_normedAlgebra K B
  have := Huber.IsTateRing.of_normedAlgebra K A
  hb.map_of_isTateRing (f := (f : B →+* A)) (hA.continuous_algHom f).continuousAt

end TauCeti.IsAffinoidAlgebra
