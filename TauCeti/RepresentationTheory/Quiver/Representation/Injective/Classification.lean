/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.Injective.Envelope
public import TauCeti.RepresentationTheory.Quiver.Representation.Indecomposable

/-!
# Classification of indecomposable injective quiver representations

Over a finite-vertex acyclic quiver, every nonzero representation contains a vertex simple.
Its injective envelope is the corresponding vertex injective `Iᵢ`.
If the representation is itself injective, that envelope splits into it; indecomposability then
makes the splitting an isomorphism. Thus the vertex injectives exhaust the indecomposable
injectives, and the vertex is unique.

This identifies the injective objects excluded from the target of the Auslander–Reiten translate.
The coefficient field is arbitrary; neither algebraic closure nor finiteness of the arrow sets is
needed for the classification. The simple-subrepresentation result keeps the coefficient and
quiver universes independent. The classification uses the universe of the existing embedding
`simpleRepToIndecInjRep`, in which the coefficient field and vertex injectives lie in a common
representation category.

## References

I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
Algebras*, Vol. 1, Chapter III, Section 2.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v w

variable {k : Type (max v w)} {Q : Type v} [Field k] [Quiver.{w} Q]

/-- Every indecomposable injective representation of a finite-vertex acyclic quiver is the
vertex injective at a unique vertex. -/
theorem existsUnique_iso_indecInjRep_of_injective [Finite Q] (hQ : Quiver.IsAcyclic Q)
    {M : QuiverRep k Q} (hM : Indecomposable M) [Injective M] :
    ∃! i : Q, Nonempty (M ≅ indecInjRep k Q i) := by
  obtain ⟨i, f, hf⟩ := exists_mono_simpleRep_of_not_isZero hQ hM.1
  obtain ⟨g, -, hg⟩ :=
    (isEssentialMono_simpleRepToIndecInjRep k (fun p ↦ hQ.eq_nil p)).exists_comp_eq_and_isSplitMono
      hf
  have : IsSplitMono g := hg
  have : IsIso (g ≫ retraction g) := by rw [IsSplitMono.id]; infer_instance
  have : IsIso g := TauCeti.isIso_of_isIso_comp
    (fun hz ↦ not_isZero_indecInjRep i ((IsZero.iff_id_eq_zero _).mpr hz))
    (fun _ he ↦ idempotent_eq_zero_or_id_of_indecomposable hM he) g (retraction g) inferInstance
  refine ⟨i, ⟨(asIso g).symm⟩, ?_⟩
  rintro j ⟨e⟩
  by_contra hji
  exact not_nonempty_indecInjRep_iso_of_isAcyclic hQ hji ⟨e.symm ≪≫ (asIso g).symm⟩

/-- Among indecomposables of a finite-vertex acyclic quiver,
injectivity is equivalent to being isomorphic to a vertex injective. -/
theorem injective_iff_exists_iso_indecInjRep [Finite Q] (hQ : Quiver.IsAcyclic Q)
    {M : QuiverRep k Q} (hM : Indecomposable M) :
    Injective M ↔ ∃ i : Q, Nonempty (M ≅ indecInjRep k Q i) := by
  constructor
  · intro h
    obtain ⟨i, hi, -⟩ := existsUnique_iso_indecInjRep_of_injective hQ hM
    exact ⟨i, hi⟩
  · rintro ⟨i, ⟨e⟩⟩
    exact Injective.of_iso e.symm inferInstance

end TauCeti
