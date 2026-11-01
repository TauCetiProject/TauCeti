/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Completion
public import Mathlib.Topology.Algebra.Algebra

/-!
# The completed rational localisation `A⟨T/s⟩` as a type

For a pair of definition `P` of a topological ring `A`, a finite set of numerators `T` and a
denominator `s` satisfying the standing hypothesis `HasDenominatorPower`, the completed rational
localisation `A⟨T/s⟩` is the separated completion of `A[1/s]` for the localisation topology
(`TauCeti.Huber.PairOfDefinition.completionLocalization`). The uniformity on `A[1/s]` is not an
instance, so every statement about this completion has to name it, together with the uniform group
and topological ring structures it carries.

This file fixes the carrier `A[1/s] = Localization.Away s` and names the completion
`TauCeti.Huber.ratLoc P T s hden`, with its uniform, ring, algebra and Huber structures as global
instances. Statements quantifying over all rational localisations of `A`, such as Kedlaya–Liu's
stably pseudocoherent modules, can then mention `A⟨T/s⟩` and modules over it without local
instances. Since `ratLoc` is reducible, the existing API of `UniformSpace.Completion S` at the
localisation uniformity applies to it unchanged; for instance
`TauCeti.Huber.PairOfDefinition.rationalLocalizationPair` is its Huber pair.

## Main definitions

* `TauCeti.Huber.ratLoc P T s hden`: the completed rational localisation `A⟨T/s⟩`.
* `TauCeti.Huber.ratLocCommRing`: its ring structure, that of the completion.

## Main results

* `TauCeti.Huber.algebraMap_ratLoc`: the structure map `A → A⟨T/s⟩` is
  `TauCeti.Huber.PairOfDefinition.toCompletionLoc`.
* `TauCeti.Huber.continuous_algebraMap_ratLoc`: it is continuous.
* `TauCeti.Huber.isUnit_algebraMap_ratLoc`: the denominator `s` becomes a unit in `A⟨T/s⟩`.
* The instances: `A⟨T/s⟩` is a complete Hausdorff uniform topological ring, a topological
  `A`-algebra and a Huber ring, and it is Tate when `A` is.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory, II: Imperfect period rings*, §2.4.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], §8.1.
-/

public noncomputable section

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (T : Finset A) (s : A)
  (hden : P.HasDenominatorPower T s (Localization.Away s))

/-- The completed rational localisation `A⟨T/s⟩`: the separated completion of `A[1/s]` for the
localisation topology of the pair of definition `P`, with numerators `T` and denominator `s`. -/
abbrev ratLoc : Type _ :=
  @UniformSpace.Completion (Localization.Away s) (P.locUniformSpace T s _ hden)

instance : UniformSpace (ratLoc P T s hden) :=
  @UniformSpace.Completion.uniformSpace _ (P.locUniformSpace T s _ hden)

/-- The ring structure of `A⟨T/s⟩`, that of the completion of `A[1/s]`. -/
abbrev ratLocCommRing : CommRing (ratLoc P T s hden) :=
  letI := P.locUniformSpace T s (Localization.Away s) hden
  haveI := P.isUniformAddGroup_locUniformSpace T s (Localization.Away s) hden
  haveI := P.isTopologicalRing_locUniformSpace T s (Localization.Away s) hden
  UniformSpace.Completion.commRing (Localization.Away s)

instance : CommRing (ratLoc P T s hden) := ratLocCommRing P T s hden

instance : IsUniformAddGroup (ratLoc P T s hden) :=
  letI := P.locUniformSpace T s (Localization.Away s) hden
  haveI := P.isUniformAddGroup_locUniformSpace T s (Localization.Away s) hden
  haveI := P.isTopologicalRing_locUniformSpace T s (Localization.Away s) hden
  inferInstanceAs (IsUniformAddGroup (UniformSpace.Completion (Localization.Away s)))

instance : IsTopologicalRing (ratLoc P T s hden) :=
  letI := P.locUniformSpace T s (Localization.Away s) hden
  haveI := P.isUniformAddGroup_locUniformSpace T s (Localization.Away s) hden
  haveI := P.isTopologicalRing_locUniformSpace T s (Localization.Away s) hden
  inferInstanceAs (IsTopologicalRing (UniformSpace.Completion (Localization.Away s)))

instance : CompleteSpace (ratLoc P T s hden) :=
  @UniformSpace.Completion.completeSpace _ (P.locUniformSpace T s _ hden)

instance : T2Space (ratLoc P T s hden) :=
  letI := P.locUniformSpace T s (Localization.Away s) hden
  inferInstanceAs (T2Space (UniformSpace.Completion (Localization.Away s)))

/-- The `A`-algebra structure of `A⟨T/s⟩`, Mathlib's algebra structure on a completion. Its
structure map is `PairOfDefinition.toCompletionLoc` (`TauCeti.Huber.algebraMap_ratLoc`), and its
scalar action is the one `UniformSpace.Completion` already carries. -/
instance : Algebra A (ratLoc P T s hden) :=
  letI := P.locUniformSpace T s (Localization.Away s) hden
  haveI := P.isUniformAddGroup_locUniformSpace T s (Localization.Away s) hden
  haveI := P.isTopologicalRing_locUniformSpace T s (Localization.Away s) hden
  haveI : UniformContinuousConstSMul A (Localization.Away s) :=
    uniformContinuousConstSMul_of_continuousConstSMul A _
  inferInstanceAs (Algebra A (UniformSpace.Completion (Localization.Away s)))

instance : IsHuberRing (ratLoc P T s hden) :=
  P.isHuberRing_completion_locTopology T s (Localization.Away s) hden

instance [IsTateRing A] : IsTateRing (ratLoc P T s hden) :=
  P.isTateRing_completion_locTopology_of_isTateRing T s (Localization.Away s) hden

/-- The structure map `A → A⟨T/s⟩` is `PairOfDefinition.toCompletionLoc`. -/
theorem algebraMap_ratLoc :
    algebraMap A (ratLoc P T s hden) = P.toCompletionLoc T s (Localization.Away s) hden := by
  let _ := P.locUniformSpace T s (Localization.Away s) hden
  have _ := P.isUniformAddGroup_locUniformSpace T s (Localization.Away s) hden
  have _ := P.isTopologicalRing_locUniformSpace T s (Localization.Away s) hden
  have _ : UniformContinuousConstSMul A (Localization.Away s) :=
    uniformContinuousConstSMul_of_continuousConstSMul A _
  ext a
  exact (UniformSpace.Completion.algebraMap_def (Localization.Away s) A a).trans
    (P.toCompletionLoc_apply T s (Localization.Away s) hden a).symm

/-- The structure map `A → A⟨T/s⟩` is continuous. -/
theorem continuous_algebraMap_ratLoc : Continuous (algebraMap A (ratLoc P T s hden)) := by
  rw [algebraMap_ratLoc]
  exact P.continuous_toCompletionLoc T s (Localization.Away s) hden

instance : ContinuousSMul A (ratLoc P T s hden) :=
  continuousSMul_of_algebraMap A _ (continuous_algebraMap_ratLoc P T s hden)

/-- **The denominator becomes a unit in `A⟨T/s⟩`**: it is already a unit of `A[1/s]`. -/
theorem isUnit_algebraMap_ratLoc : IsUnit (algebraMap A (ratLoc P T s hden) s) := by
  let _ := P.locUniformSpace T s (Localization.Away s) hden
  have _ := P.isUniformAddGroup_locUniformSpace T s (Localization.Away s) hden
  have _ := P.isTopologicalRing_locUniformSpace T s (Localization.Away s) hden
  rw [algebraMap_ratLoc, PairOfDefinition.toCompletionLoc_apply]
  exact (IsLocalization.Away.algebraMap_isUnit s).map UniformSpace.Completion.coeRingHom

end TauCeti.Huber
