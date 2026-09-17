/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Localization
public import TauCeti.Topology.Algebra.QuadraticForm.Continuity

/-!
# Continuity of localized quadratic forms

Finite, real, and complex localizations of a finite-dimensional quadratic form are continuous
for the module topology on their scalar extensions. The statements accept any topology with
`IsModuleTopology`, so they do not depend on a basis or on a chosen construction of that topology.

At a real place, a neighborhood of a vector with nonzero value preserves the square class of
that value. This is the real-place input for choosing a global vector by weak approximation
while controlling its quadratic value, as in O'Meara, *Introduction to Quadratic Forms*, §66.
-/

public section

namespace TauCeti

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped Topology

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A quadratic form localized at a finite place is continuous for the module topology. -/
@[continuity, fun_prop]
theorem _root_.QuadraticForm.continuous_atFinitePlace [NumberField K]
    (Q : QuadraticForm K V) (v : HeightOneSpectrum (𝓞 K))
    [TopologicalSpace (v.FiniteScalarExtension (V := V))]
    [IsModuleTopology (v.adicCompletion K) (v.FiniteScalarExtension (V := V))] :
    Continuous (Q.atFinitePlace v) := by
  have : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  let : Invertible (2 : v.adicCompletion K) := invertibleOfNonzero two_ne_zero
  exact (Q.atFinitePlace v).continuous

/-- A quadratic form localized at a real place is continuous for the module topology. -/
@[continuity, fun_prop]
theorem _root_.QuadraticForm.continuous_atRealPlace
    (Q : QuadraticForm K V) (w : {w : InfinitePlace K // w.IsReal})
    [TopologicalSpace (RealScalarExtension (V := V) w)]
    [IsModuleTopology ℝ (RealScalarExtension (V := V) w)] :
    Continuous (Q.atRealPlace w) := by
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  let : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  exact (Q.atRealPlace w).continuous

/-- A quadratic form localized through a complex embedding is continuous for the module
topology. -/
@[continuity, fun_prop]
theorem _root_.QuadraticForm.continuous_atComplexEmbedding
    (Q : QuadraticForm K V) (w : InfinitePlace K)
    [TopologicalSpace (w.ComplexScalarExtension (V := V))]
    [IsModuleTopology ℂ (w.ComplexScalarExtension (V := V))] :
    Continuous (Q.atComplexEmbedding w) := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  let : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
  exact (Q.atComplexEmbedding w).continuous

/-- Around a real local vector with nonzero value there is an open neighborhood on which
the quadratic value stays nonzero and in the same square class. -/
theorem _root_.QuadraticForm.exists_isOpen_isSquare_div_atRealPlace
    (Q : QuadraticForm K V) (w : {w : InfinitePlace K // w.IsReal})
    [TopologicalSpace (RealScalarExtension (V := V) w)]
    [IsModuleTopology ℝ (RealScalarExtension (V := V) w)]
    {x : RealScalarExtension (V := V) w} (hx : Q.atRealPlace w x ≠ 0) :
    ∃ U : Set (RealScalarExtension (V := V) w), IsOpen U ∧ x ∈ U ∧
      ∀ z ∈ U, Q.atRealPlace w z ≠ 0 ∧
        IsSquare (Q.atRealPlace w z / Q.atRealPlace w x) := by
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  obtain ⟨U, hU, hUo, hxU⟩ :=
    mem_nhds_iff.mp ((Q.atRealPlace w).eventually_isSquare_div hx)
  exact ⟨U, hUo, hxU, fun z hz ↦ hU hz⟩

end TauCeti
