/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ClosedSubmodule
public import TauCeti.RingTheory.Huber.ModuleTopology.Complete
public import TauCeti.RingTheory.Huber.NoetherianType.Basic
public import TauCeti.Topology.Algebra.Ring.Ideal

/-!
# Ideals and quotients of Huber rings of noetherian type

Let `A` be a complete Hausdorff Huber ring of noetherian type. This file proves that every ideal
`J` of `A` is closed, so that `A ⧸ J` with the quotient topology is again Hausdorff, and that
`A ⧸ J` is again of noetherian type. Together with the completeness of quotients of complete
first-countable groups (`QuotientAddGroup.completeSpace_right`), this makes `A ⧸ J` a complete
Hausdorff Huber ring of noetherian type. These are the facts used to treat closed subspaces of
locally noetherian adic spaces by ideals of their rings of sections.

Each statement is proved separately for the two alternatives defining noetherian type.

* If `A` has a noetherian ring of definition `A₀`, closedness of ideals is the case `M = A` of
  `TauCeti.Huber.PairOfDefinition.isClosed_of_isNoetherianRing` (Huber, Lemma 2.3(ii)), and the
  image of `A₀` in an open quotient of `A` is a noetherian ring of definition, being a quotient
  ring of `A₀`. This alternative needs neither completeness nor separation for quotients.
* If `A` is a strongly noetherian Tate ring, `A` is a noetherian ring
  (`TauCeti.Huber.isNoetherianRing_of_isStronglyNoetherian`), so its ideals are closed by
  `TauCeti.Huber.isClosed_of_isNoetherian`, and strong noetherianness descends along open
  quotient maps of complete Hausdorff rings (`IsOpenQuotientMap.isStronglyNoetherian`).

The Hausdorff hypothesis cannot be dropped: `ℤ` with the indiscrete topology and pair of
definition `(ℤ, (1))` is complete and of noetherian type, but its zero ideal is not closed.

## Main results

* `TauCeti.Huber.PairOfDefinition.isNoetherianRing_map`: the image of a noetherian ring of
  definition along an open quotient map is noetherian.
* `TauCeti.Huber.IsNoetherianType.of_isOpenQuotientMap`: an open quotient of a complete Hausdorff
  Huber ring of noetherian type is of noetherian type, if it is complete and Hausdorff.
* `TauCeti.Huber.IsNoetherianType.isClosed_ideal`: every ideal of a complete Hausdorff Huber ring
  of noetherian type is closed.
* `TauCeti.Huber.IsNoetherianType.t2Space_quotient`: hence the quotient by any ideal is Hausdorff.
* `TauCeti.Huber.IsNoetherianType.completeSpace_quotient`: the quotient by any ideal is complete
  and Hausdorff.
* `TauCeti.Huber.IsNoetherianType.quotient`: the quotient of a complete Hausdorff Huber ring of
  noetherian type by any ideal is of noetherian type.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, Lemma 2.3(ii).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I*, Chapitre 0, (7.3.6).
* T. Wedhorn, *Adic Spaces*, Proposition 6.17 and Remark 6.37.
-/

public section

open Topology
open scoped Uniformity

namespace TauCeti.Huber

section OpenQuotient

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- **A noetherian ring of definition stays noetherian along an open quotient map**: the image
`f(A₀)` of a noetherian ring of definition `A₀` is a quotient ring of `A₀`. -/
instance PairOfDefinition.isNoetherianRing_map (P : PairOfDefinition A)
    [IsNoetherianRing P.ringOfDefinition] (f : A →+* B) (hf : IsOpenQuotientMap f) :
    IsNoetherianRing (P.map f hf).ringOfDefinition := by
  have h : (f.comp P.ringOfDefinition.subtype).range = (P.map f hf).ringOfDefinition := by
    ext; simp
  exact h ▸ inferInstance

end OpenQuotient

section Complete

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsHuberRing A] [CompleteSpace A] [T0Space A]

/-- **An open quotient of a complete Hausdorff Huber ring of noetherian type is of noetherian
type**, provided it is itself complete and Hausdorff. A noetherian ring of definition maps onto a
noetherian ring of definition, and strong noetherianness of a Tate ring descends along open
quotient maps of complete Hausdorff rings. -/
theorem IsNoetherianType.of_isOpenQuotientMap [IsNoetherianType A] {B : Type*} [CommRing B]
    [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B] [CompleteSpace B]
    [T0Space B] {f : A →+* B} (hf : IsOpenQuotientMap f) : IsNoetherianType B := by
  refine IsNoetherianType.elim ‹_› (fun P _ ↦ .of_pairOfDefinition (P.map f hf) inferInstance)
    fun _ _ ↦ ?_
  have := IsTateRing.of_continuous hf.continuous (φ := f)
  have := hf.isStronglyNoetherian
  infer_instance

/-- **Every ideal of a complete Hausdorff Huber ring of noetherian type is closed** (Huber,
Lemma 2.3(ii); Wedhorn, Proposition 6.17). For a noetherian ring of definition this is the case
of the ring itself among finite modules; a complete Hausdorff strongly noetherian Tate ring is a
noetherian ring, all of whose ideals are closed. -/
theorem IsNoetherianType.isClosed_ideal [IsNoetherianType A] (J : Ideal A) :
    IsClosed (J : Set A) := by
  refine IsNoetherianType.elim ‹_› (fun P _ ↦ P.isClosed_of_isNoetherianRing (M := A) J)
    fun _ _ ↦ ?_
  have : IsNoetherianRing A := isNoetherianRing_of_isStronglyNoetherian <| by
    rwa [IsUniformAddGroup.rightUniformSpace_eq]
  have : (𝓤 A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact isClosed_of_isNoetherian J

/-- **The quotient of a complete Hausdorff Huber ring of noetherian type by any ideal is
Hausdorff**, since the ideal is closed. -/
instance IsNoetherianType.t2Space_quotient [IsNoetherianType A] (J : Ideal A) :
    T2Space (A ⧸ J) :=
  have : T1Space (A ⧸ J) := (Ideal.Quotient.t1Space_iff J).mpr (isClosed_ideal J)
  inferInstance

/-- **The quotient of a complete Hausdorff Huber ring of noetherian type by any ideal is complete
and Hausdorff**, for the uniform structure of the quotient topology. Completeness holds because `A`
is complete and first countable (`QuotientAddGroup.completeSpace_right`), and Hausdorffness
because the ideal is closed (`IsNoetherianType.t2Space_quotient`). -/
theorem IsNoetherianType.completeSpace_quotient [IsNoetherianType A] (J : Ideal A) :
    @CompleteSpace (A ⧸ J) (IsTopologicalAddGroup.rightUniformSpace _) ∧ T2Space (A ⧸ J) :=
  ⟨QuotientAddGroup.completeSpace_right _ J.toAddSubgroup, inferInstance⟩

/-- **The quotient of a complete Hausdorff Huber ring of noetherian type by any ideal is of
noetherian type.** A noetherian ring of definition maps onto one of the quotient, and a strongly
noetherian Tate ring has strongly noetherian quotients by closed ideals
(`IsStronglyNoetherian.quotient`), which applies since every ideal is closed. -/
instance IsNoetherianType.quotient [IsNoetherianType A] (J : Ideal A) :
    IsNoetherianType (A ⧸ J) := by
  refine IsNoetherianType.elim ‹_› (fun P _ ↦ .of_pairOfDefinition
    (P.map _ (QuotientRing.isOpenQuotientMap_mk J)) inferInstance) fun _ _ ↦ ?_
  have := IsTateRing.of_continuous (QuotientRing.isOpenQuotientMap_mk J).continuous
  have := IsStronglyNoetherian.quotient J (isClosed_ideal J)
  infer_instance

end Complete

end TauCeti.Huber
