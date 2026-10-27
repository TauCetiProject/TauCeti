/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.NonabelianH1
public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Conjugacy

/-!
# Nonabelian first cohomology of ordinary inertia extensions

Choose a splitting `s` of the canonical Clifford extension of a representation `A`
of a normal subgroup. Ordinary inertia actions on the same vector space, restricting
to exactly `A`, are classified up to isomorphism by nonabelian `H¹` with coefficients
in `CategoryTheory.End A`'s unit group. The quotient acts on these units by conjugation
through `s`. All groups in this cohomology are given the discrete topology, so this
is an algebraic classification.

The reference splitting recovers an ordinary inertia action and determines the base
point. The commutant need not consist of scalars. In particular the result applies to
simple representations over nonsplitting fields, without a finite-group or Maschke
hypothesis. The construction combines `FDRep.cliffordExtensionConjClassesEquiv`
with `GroupExtension.Splitting.nonabelianH1Equiv`.

## References

* J.-P. Serre, *Galois Cohomology*, Springer, 1997, I.5.
* G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker, 1985.
-/

public section

namespace FDRep

open CategoryTheory TauCeti TauCeti.CliffordExtension

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {N : Subgroup G} [N.Normal] (A : FDRep k N)

/-- Isomorphism classes of ordinary extensions of the specified normal-subgroup action
are classified by nonabelian `H¹`, after choosing a reference Clifford splitting.
The coefficient group is the full commutant-unit group with the induced action. -/
noncomputable def cliffordExtensionNonabelianH1Equiv (s : (groupExtension A).Splitting) :
    letI : TopologicalSpace (Quotient A) := ⊥
    letI : TopologicalSpace (End A)ˣ := ⊥
    letI := MulDistribMulAction.compHom (End A)ˣ s.conjAct
    Quotient ((isIsomorphicSetoid (FDRep k (inertia A))).comap
      (fun σ : {σ : Representation k (inertia A) A //
        σ.comp (Subgroup.inclusion (le_inertia A)) = A.ρ} => FDRep.of σ.val)) ≃
      NonabelianH1 (Quotient A) (End A)ˣ := by
  letI : TopologicalSpace (Quotient A) := ⊥
  letI : TopologicalSpace (End A)ˣ := ⊥
  letI : DiscreteTopology (Quotient A) := ⟨rfl⟩
  letI := MulDistribMulAction.compHom (End A)ˣ s.conjAct
  exact (cliffordExtensionConjClassesEquiv A).trans
    (s.nonabelianH1Equiv (fun _ _ => rfl))

/-- An inertia action is sent to the class of its splitting-difference cocycle. -/
@[simp]
theorem cliffordExtensionNonabelianH1Equiv_mk (s : (groupExtension A).Splitting)
    (σ : {σ : Representation k (inertia A) A //
      σ.comp (Subgroup.inclusion (le_inertia A)) = A.ρ}) :
    letI : TopologicalSpace (Quotient A) := ⊥
    letI : TopologicalSpace (End A)ˣ := ⊥
    letI : DiscreteTopology (Quotient A) := ⟨rfl⟩
    letI := MulDistribMulAction.compHom (End A)ˣ s.conjAct
    cliffordExtensionNonabelianH1Equiv A s (Quotient.mk _ σ) =
      NonabelianH1.mk (s.toCocycle (fun _ _ => rfl)
        (splittingOfRepresentation A σ.val σ.prop)) := by
  let : TopologicalSpace (Quotient A) := ⊥
  let : TopologicalSpace (End A)ˣ := ⊥
  let : DiscreteTopology (Quotient A) := ⟨rfl⟩
  let := MulDistribMulAction.compHom (End A)ˣ s.conjAct
  simp only [cliffordExtensionNonabelianH1Equiv, Equiv.trans_apply,
    cliffordExtensionConjClassesEquiv_mk]
  exact s.nonabelianH1Equiv_mk (fun _ _ => rfl) _

/-- The inverse classification recovers the inertia action determined by a cocycle. -/
@[simp]
theorem cliffordExtensionNonabelianH1Equiv_symm_mk (s : (groupExtension A).Splitting) :
    letI : TopologicalSpace (Quotient A) := ⊥
    letI : TopologicalSpace (End A)ˣ := ⊥
    letI : DiscreteTopology (Quotient A) := ⟨rfl⟩
    letI := MulDistribMulAction.compHom (End A)ˣ s.conjAct
    ∀ f : NonabelianH1.Cocycle (Quotient A) (End A)ˣ,
      (cliffordExtensionNonabelianH1Equiv A s).symm (NonabelianH1.mk f) =
        Quotient.mk _
          ⟨representationOfSplitting A (s.ofCocycle (fun _ _ => rfl) f),
            representationOfSplitting_comp A (s.ofCocycle (fun _ _ => rfl) f)⟩ := by
  let : TopologicalSpace (Quotient A) := ⊥
  let : TopologicalSpace (End A)ˣ := ⊥
  let : DiscreteTopology (Quotient A) := ⟨rfl⟩
  let := MulDistribMulAction.compHom (End A)ˣ s.conjAct
  intro f
  simp only [cliffordExtensionNonabelianH1Equiv, Equiv.symm_trans_apply]
  rw [s.nonabelianH1Equiv_symm_mk (fun _ _ => rfl) f]
  exact cliffordExtensionConjClassesEquiv_symm_mk A _

end FDRep
