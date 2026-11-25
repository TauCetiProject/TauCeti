/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import TauCeti.NumberTheory.NumberField.AbsoluteGaloisGroup.Decomposition
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Operations
import TauCeti.RepresentationTheory.BaseChange
import TauCeti.RepresentationTheory.Dual
import TauCeti.RepresentationTheory.Quotient
import TauCeti.RepresentationTheory.Stabilizer

/-!
# Ramification of global Galois representations

Let `F` be a field (a number field in the case of interest), `G_F` its absolute Galois group and
`O` the integral closure of `𝓞 F` in `F^alg`. For a finite place `v` of `F`, a height-one prime of
`𝓞 F`, a continuous representation `ρ` of `G_F` is **unramified at `v`** if the inertia group `I_Q`
(`TauCeti.GaloisRep.inertiaGroup`) acts trivially for every maximal ideal `Q` of `O` above `v`.
The **ramification set** of `ρ` is the set of finite places at which `ρ` is ramified.

The ramification set of a product is the union of the ramification sets, and those of a tensor
product, of a contragredient, of an equivariant quotient and of a scalar extension (in particular
of a raw reduction) are contained in the expected sets. The trivial representation is unramified
everywhere, and isomorphic representations have the same ramification set.

The definition quantifies over all maximal ideals above `v`. Since `G_F` permutes them
transitively and `I_{σQ} = σ I_Q σ⁻¹`, one of them suffices; that comparison, and the finiteness of
the ramification set for a representation with open kernel, are not proved here.

## Main definitions

* `TauCeti.ContinuousRep.IsUnramifiedAt ρ v`: `ρ(I_Q) = 1` for every maximal `Q` of `O` above `v`.
* `TauCeti.ContinuousRep.ramificationSet ρ`: the finite places at which `ρ` is ramified.

## Main results

* `TauCeti.ContinuousRep.ramificationSet_trivial`: the trivial representation is unramified
  everywhere.
* `TauCeti.ContinuousRep.ramificationSet_prod`: `Ram(ρ × ρ') = Ram ρ ∪ Ram ρ'`.
* `TauCeti.ContinuousRep.ramificationSet_tprod_subset`: `Ram(ρ ⊗ ρ') ⊆ Ram ρ ∪ Ram ρ'`.
* `TauCeti.ContinuousRep.ramificationSet_dual_subset`: `Ram(ρ^∨) ⊆ Ram ρ`.
* `TauCeti.ContinuousRep.ramificationSet_subset_of_surjective`: an equivariant quotient is
  unramified wherever the representation is.
* `TauCeti.ContinuousRep.ramificationSet_baseChange_subset`: `Ram(B ⊗ ρ) ⊆ Ram ρ`.

-/

public section

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace TauCeti.ContinuousRep

variable {F : Type*} [Field F]

section Predicates

variable {A M N : Type*} [Semiring A] [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  [AddCommMonoid N] [Module A N] [TopologicalSpace N]

/-- A continuous representation of `G_F` is **unramified at the finite place `v`** if the inertia
group `I_Q` acts trivially for every maximal ideal `Q` of the integral closure of `𝓞 F` in `F^alg`
lying over `v`. -/
def IsUnramifiedAt (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M)
    (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F)), Q.IsMaximal →
    Q.under (𝓞 F) = v.asIdeal → GaloisRep.inertiaGroup F Q ≤ ρ.toRepresentation.ker

/-- The **ramification set** of a continuous representation of `G_F`: the finite places at which
it is ramified. -/
def ramificationSet (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M) :
    Set (HeightOneSpectrum (𝓞 F)) :=
  {v | ¬ρ.IsUnramifiedAt v}

variable {ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M}
  {ρ' : ContinuousRep (Field.absoluteGaloisGroup F) A N} {v : HeightOneSpectrum (𝓞 F)}

theorem isUnramifiedAt_iff :
    ρ.IsUnramifiedAt v ↔ ∀ Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F)),
      Q.IsMaximal → Q.under (𝓞 F) = v.asIdeal → ∀ σ ∈ GaloisRep.inertiaGroup F Q, ρ σ = 1 :=
  Iff.rfl

@[simp]
theorem mem_ramificationSet_iff : v ∈ ρ.ramificationSet ↔ ¬ρ.IsUnramifiedAt v :=
  Iff.rfl

/-- A representation is unramified at `v` exactly when `v` is outside its ramification set. -/
theorem notMem_ramificationSet_iff : v ∉ ρ.ramificationSet ↔ ρ.IsUnramifiedAt v :=
  not_not

/-- If every element acting trivially in `ρ` acts trivially in `τ`, possibly over other
coefficients, then `τ` is unramified wherever `ρ` is. -/
theorem IsUnramifiedAt.of_ker_le {B P : Type*} [Semiring B] [AddCommMonoid P] [Module B P]
    [TopologicalSpace P] {τ : ContinuousRep (Field.absoluteGaloisGroup F) B P}
    (h : ρ.IsUnramifiedAt v) (hker : ρ.toRepresentation.ker ≤ τ.toRepresentation.ker) :
    τ.IsUnramifiedAt v :=
  fun Q hQ hv ↦ (h Q hQ hv).trans hker

/-- If every element acting trivially in `ρ` acts trivially in `τ`, possibly over other
coefficients, then `Ram τ ⊆ Ram ρ`. -/
theorem ramificationSet_subset_of_ker_le {B P : Type*} [Semiring B] [AddCommMonoid P]
    [Module B P] [TopologicalSpace P] {τ : ContinuousRep (Field.absoluteGaloisGroup F) B P}
    (hker : ρ.toRepresentation.ker ≤ τ.toRepresentation.ker) :
    τ.ramificationSet ⊆ ρ.ramificationSet :=
  fun _ hv h ↦ hv (h.of_ker_le hker)

variable (F A M) in
/-- The trivial representation is unramified everywhere. -/
@[simp]
theorem ramificationSet_trivial : (trivial (Field.absoluteGaloisGroup F) A M).ramificationSet = ∅ :=
  Set.eq_empty_of_forall_notMem fun v hv ↦ hv fun _ _ _ ↦ by
    rw [toRepresentation_trivial, Representation.ker_trivial]
    exact le_top

/-- A product is unramified at `v` exactly when both factors are. -/
theorem isUnramifiedAt_prod_iff :
    (ρ.prod ρ').IsUnramifiedAt v ↔ ρ.IsUnramifiedAt v ∧ ρ'.IsUnramifiedAt v := by
  simp only [IsUnramifiedAt, toRepresentation_prod, Representation.ker_prod, le_inf_iff]
  exact ⟨fun h ↦ ⟨fun Q hQ hv ↦ (h Q hQ hv).1, fun Q hQ hv ↦ (h Q hQ hv).2⟩,
    fun h Q hQ hv ↦ ⟨h.1 Q hQ hv, h.2 Q hQ hv⟩⟩

/-- **The ramification set of a product** is the union of the ramification sets. -/
theorem ramificationSet_prod :
    (ρ.prod ρ').ramificationSet = ρ.ramificationSet ∪ ρ'.ramificationSet := by
  ext v
  simp only [mem_ramificationSet_iff, Set.mem_union, isUnramifiedAt_prod_iff, not_and_or]

/-- Isomorphic representations have the same ramification set. -/
theorem Iso.ramificationSet_eq (e : Iso ρ ρ') : ρ.ramificationSet = ρ'.ramificationSet :=
  (ramificationSet_subset_of_ker_le e.toRepresentationEquiv.ker_eq.ge).antisymm
    (ramificationSet_subset_of_ker_le e.toRepresentationEquiv.ker_eq.le)

/-- An equivariant quotient is unramified wherever the representation is. -/
theorem ramificationSet_subset_of_surjective (f : Hom ρ ρ') (hf : Function.Surjective f) :
    ρ'.ramificationSet ⊆ ρ.ramificationSet := by
  refine ramificationSet_subset_of_ker_le fun σ hσ ↦ ?_
  rw [MonoidHom.mem_ker] at hσ ⊢
  refine LinearMap.ext fun y ↦ ?_
  obtain ⟨x, rfl⟩ := hf y
  have hx : ρ.toRepresentation σ x = x := LinearMap.congr_fun hσ x
  exact (f.isIntertwining σ x).symm.trans (congrArg f hx)

end Predicates

section Tensor

variable {A M N : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [AddCommGroup M]
  [Module A M] [TopologicalSpace M] [IsModuleTopology A M] [Module.Finite A M] [AddCommGroup N]
  [Module A N] [TopologicalSpace N] [IsModuleTopology A N] [Module.Finite A N]
  [TopologicalSpace (M ⊗[A] N)] [IsModuleTopology A (M ⊗[A] N)]

/-- **The ramification set of a tensor product** is contained in the union of the ramification
sets. -/
theorem ramificationSet_tprod_subset (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M)
    (ρ' : ContinuousRep (Field.absoluteGaloisGroup F) A N) :
    (ρ.tprod ρ').ramificationSet ⊆ ρ.ramificationSet ∪ ρ'.ramificationSet := by
  intro v hv
  by_contra h
  simp only [Set.mem_union, mem_ramificationSet_iff, not_or, not_not] at h
  refine hv fun Q hQ hQv ↦ ?_
  rw [toRepresentation_tprod]
  exact (le_inf (h.1 Q hQ hQv) (h.2 Q hQ hQv)).trans
    (Representation.ker_inf_ker_le_ker_tprod _ _)

end Tensor

section Dual

variable {A M : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [AddCommGroup M]
  [Module A M] [TopologicalSpace M] [IsModuleTopology A M] [Module.Finite A M]
  [Module.Projective A M] [TopologicalSpace (Module.Dual A M)]
  [IsModuleTopology A (Module.Dual A M)]

/-- **The ramification set of the contragredient** is contained in that of the representation. -/
theorem ramificationSet_dual_subset (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M) :
    ρ.dual.ramificationSet ⊆ ρ.ramificationSet := by
  refine ramificationSet_subset_of_ker_le ?_
  rw [toRepresentation_dual]
  exact ρ.toRepresentation.ker_le_ker_dual

end Dual

section BaseChange

variable {A M : Type*} [CommSemiring A] [TopologicalSpace A] [AddCommMonoid M] [Module A M]
  [TopologicalSpace M] [IsModuleTopology A M] [Module.Finite A M] (B : Type*) [Ring B]
  [TopologicalSpace B] [IsTopologicalSemiring B] [Algebra A B] [ContinuousSMul A B]
  [TopologicalSpace (B ⊗[A] M)] [IsModuleTopology B (B ⊗[A] M)]

/-- **Extension of scalars does not create ramification**: `Ram(B ⊗ ρ) ⊆ Ram ρ`. For `B` the
residue field this says that a raw reduction is unramified wherever the representation is; the
converse fails. -/
theorem ramificationSet_baseChange_subset (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M) :
    (ρ.baseChange B).ramificationSet ⊆ ρ.ramificationSet := by
  refine ramificationSet_subset_of_ker_le (ρ := ρ) (τ := ρ.baseChange B) ?_
  rw [toRepresentation_baseChange]
  exact ρ.toRepresentation.ker_le_ker_baseChange B

end BaseChange

end TauCeti.ContinuousRep
