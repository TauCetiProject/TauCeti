/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Topology
public import TauCeti.RingTheory.Huber.Adic

/-!
# Complete adic rings of finite ideal type

An adic ring of finite ideal type is a commutative topological ring whose topology is defined
by a finitely generated ideal and which is separated and complete for that ideal. The
topology is part of the data. Completeness holds for every ideal of definition, and the ring
is Huber with the whole ring as a ring of definition.

The general continuity criteria in
`TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology` apply using the chosen finitely
generated ideal from `TauCeti.IsAdicRing.ideal_spec`. They test arbitrary ideals of definition
and do not require completeness.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0,
  §§7.1.4, 7.1.7, 7.1.9.
-/

public section

namespace TauCeti

/-- A commutative topological ring is an adic ring of finite ideal type if a finitely
generated ideal defines its topology and makes it adically separated and complete. -/
@[mk_iff isAdicRing_iff]
class IsAdicRing (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] : Prop where
  /-- A finitely generated ideal of definition for which the ring is complete. -/
  exists_isAdic : ∃ I : Ideal A, I.FG ∧ IsAdic I ∧ IsAdicComplete I A

namespace IsAdicRing

variable (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- A chosen finitely generated ideal of definition. -/
noncomputable def ideal [IsAdicRing A] : Ideal A :=
  Classical.choose (exists_isAdic (A := A))

/-- The chosen ideal is finitely generated, defines the topology, and makes the ring
separated and complete. -/
theorem ideal_spec [IsAdicRing A] :
    (ideal A).FG ∧ IsAdic (ideal A) ∧ IsAdicComplete (ideal A) A :=
  Classical.choose_spec (exists_isAdic (A := A))

/-- An adic ring is Huber, with the whole ring as a ring of definition. -/
instance (priority := 100) isHuberRing [IsAdicRing A] : Huber.IsHuberRing A :=
  Huber.isHuberRing_of_isAdic (ideal A) (ideal_spec A).2.1 (ideal_spec A).1

/-- Every discrete commutative ring is adic, using the zero ideal. -/
instance (priority := 100) of_discreteTopology [DiscreteTopology A] : IsAdicRing A :=
  ⟨⊥, Submodule.fg_bot, is_bot_adic_iff.mpr inferInstance, inferInstance⟩

variable {A}

/-- An adic ring is Hausdorff. -/
instance (priority := 100) t2Space [IsAdicRing A] : T2Space A := by
  have := (ideal_spec A).2.2
  exact (ideal_spec A).2.1.isHausdorff_iff.mp inferInstance

/-- In a nonzero adic ring, the chosen ideal of definition is proper. -/
theorem ideal_ne_top [Nontrivial A] [IsAdicRing A] : ideal A ≠ ⊤ := by
  intro h
  have hcomplete : IsAdicComplete (⊤ : Ideal A) A := h ▸ (ideal_spec A).2.2
  exact not_subsingleton A hcomplete.toIsHausdorff.subsingleton

/-- A nonzero complete adic ring is not a Tate ring. -/
theorem not_isTateRing [Nontrivial A] [IsAdicRing A] : ¬ Huber.IsTateRing A := by
  intro h
  exact ideal_ne_top (Huber.IsTateRing.eq_top_of_isAdic (ideal_spec A).2.1)

end IsAdicRing

namespace IsAdicRing

variable (R : Type*) [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]

/-- An adic ring is complete for every compatible additive uniformity supplied by the caller. -/
instance (priority := 100) completeSpace [IsAdicRing R] : CompleteSpace R :=
  ((ideal_spec R).2.1.isAdicComplete_iff.mp (ideal_spec R).2.2).1

end IsAdicRing

end TauCeti

namespace IsAdic

open TauCeti
open TauCeti.IsAdicRing

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Completeness of an adic ring holds for every ideal of definition. -/
theorem isAdicComplete [IsAdicRing A] {I : Ideal A} (hI : IsAdic I) : IsAdicComplete I A :=
  ((ideal_spec A).2.1.isAdicComplete_iff_of_isAdic hI).mp (ideal_spec A).2.2

end IsAdic

namespace TauCeti

/-- A field is an adic ring precisely when its topology is discrete. -/
theorem isAdicRing_iff_discreteTopology (k : Type*) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] : IsAdicRing k ↔ DiscreteTopology k := by
  constructor
  · intro h
    rcases Ideal.eq_bot_or_top (IsAdicRing.ideal k) with hI | hI
    · exact is_bot_adic_iff.mp (hI ▸ (IsAdicRing.ideal_spec k).2.1)
    · exact (IsAdicRing.ideal_ne_top hI).elim
  · intro h
    infer_instance

end TauCeti
