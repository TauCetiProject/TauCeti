/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ProjectiveRepresentation.RootsOfUnity
import TauCeti.RepresentationTheory.ProjectiveRepresentation.Torsion
import TauCeti.FieldTheory.IsAlgClosed.Units
import TauCeti.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import TauCeti.GroupTheory.GroupExtension.Character.Duality

/-!
# Finite stem extensions with bijective character transgression

For a finite group over an algebraically closed field of arbitrary characteristic, construct a
finite central extension whose kernel lies in the commutator subgroup and whose character
transgression is bijective onto `H²(G, kˣ)`. Thus the character dual of the kernel is exactly
second cohomology, with no surplus kernel characters invisible to projective representations.

Decompose second cohomology into finite cyclic summands. Represent each cyclic generator
by a factor set taking values in roots of unity of its own order, and take their product.
Coordinate characters make transgression surjective; the kernel and second cohomology have
matching cardinalities, so transgression is also injective. The stem criterion then places
the kernel in the commutator subgroup. This supplies the finite extension underlying a
representation group; the universal lifting criterion applies to its surjective transgression.

The cyclic summands have orders nonzero in the field because second cohomology has no
torsion at the characteristic. Thus the kernel also has order prime to the characteristic,
even when the characteristic divides the order of the original group.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985), Chapters 2–3.
* Mathlib's finite abelian structure theorem:
  `AddCommGroup.equiv_directSum_zmod_of_finite'`.
* The torsion representative theorem:
  `TauCeti.FactorSet.nsmul_eq_zero_iff_exists_factorSet_pow_eq_one`.
* The stem criterion:
  `TauCeti.FactorSet.characterTransgression_injective_iff_range_inl_le_commutator_of_rootableBy`.
-/

public section

namespace TauCeti

attribute [local instance] trivialMulDistribMulAction

open scoped BigOperators

variable (k G : Type) [Field k] [IsAlgClosed k] [Group G] [Finite G]

/-- Every finite group over an algebraically closed field has a finite
central stem extension with bijective character transgression. In particular, the character
dual of its kernel is `H²(G, kˣ)`. -/
theorem exists_finite_stem_factorSet_bijective_characterTransgression :
    ∃ (M : Type) (_ : CommGroup M) (_ : Finite M) (α : FactorSet G M),
      (FactorSet.rightHom α).ker ≤ Subgroup.center α.Extension ∧
      (FactorSet.rightHom α).ker ≤ commutator α.Extension ∧
      Function.Bijective (α.characterTransgression (A := kˣ)) := by
  classical
  obtain ⟨ι, hι, n, x, hncast, hx, hgen, hcardH⟩ := exists_cyclic_generators_schurMultiplier k G
  have hnroot (i : ι) : NeZero (n i : k) := ⟨hncast i⟩
  have hne (i : ι) : NeZero (n i) := .of_neZero_natCast k
  have : NeZero (Monoid.exponent (∀ i, rootsOfUnity (n i) k) : k) :=
    ⟨exponent_pi_rootsOfUnity_cast_ne_zero n hncast⟩
  obtain ⟨α, hsurj⟩ := exists_factorSet_surjective_characterTransgression k G n x hx hgen
  have hcard := natCard_additive_equivariantCharacterSubgroup_rootsOfUnity k G n hncast
  have hbij : Function.Bijective (α.characterTransgression (A := kˣ)) :=
    (Nat.bijective_iff_surjective_and_card _).mpr ⟨hsurj, hcard.trans hcardH.symm⟩
  -- Injectivity of transgression forces the central kernel into the commutator subgroup.
  refine ⟨_, inferInstance, inferInstance, α, ?_, ?_, hbij⟩
  · rw [← FactorSet.range_inl_eq_ker_rightHom]
    exact α.inl_range_le_center trivialMulDistribMulAction_smul
  · rw [← FactorSet.range_inl_eq_ker_rightHom]
    exact (α.characterTransgression_injective_iff_range_inl_le_commutator_of_rootableBy
      trivialMulDistribMulAction_smul).mp hbij.injective

end TauCeti
