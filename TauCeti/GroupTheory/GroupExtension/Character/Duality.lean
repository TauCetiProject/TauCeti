/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Character.Basic
public import TauCeti.Algebra.GroupAction.Trivial
public import TauCeti.GroupTheory.Abelianization.Character
import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# Character duality for the commutator part of an extension kernel

For a central factor-set extension `1 → M → E → G → 1`, character transgression has the
same kernel as restriction to the inverse image of `E'` in `M`. If `M` and the abelianization
of `E` are finite and the coefficients have enough roots of unity, this identifies the image
of transgression with the character group of `M ∩ E'`.

In particular, a finite central extension with surjective transgression realizes second
cohomology as the dual of the part of its kernel in the commutator subgroup. This isolates
the kernel detected by projective representations, which a Schur cover must retain.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985), Chapters 2–3.
-/

public section

namespace TauCeti.FactorSet

attribute [local instance] trivialMulDistribMulAction

variable {G M k : Type} [Group G] [CommGroup M] [MulDistribMulAction G M] [CommMonoid k]
  (α : FactorSet G M)

/-- Restrict invariant kernel characters to the part of the kernel lying in the commutator
subgroup of the extension. The additive type tags match character transgression. -/
def commutatorCharacterRestriction :
    Additive (equivariantCharacterSubgroup G M kˣ) →+
      Additive (((commutator α.Extension).comap (inl α)) →* kˣ) :=
  ((MonoidHom.domRestrictHom ((commutator α.Extension).comap (inl α)) kˣ).comp
    (equivariantCharacterSubgroup G M kˣ).subtype).toAdditive

@[simp]
theorem commutatorCharacterRestriction_apply
    (χ : Additive (equivariantCharacterSubgroup G M kˣ)) :
    α.commutatorCharacterRestriction χ =
      Additive.ofMul (χ.toMul.val.domRestrict ((commutator α.Extension).comap (inl α))) :=
  (rfl)

section Restriction

variable [Finite M] [HasEnoughRootsOfUnity k (Monoid.exponent M)]

/-- For a central extension, every character of the commutator part of its kernel is the
restriction of an invariant character of the whole kernel. -/
theorem commutatorCharacterRestriction_surjective
    (hM : ∀ (g : G) (m : M), g • m = m) :
    Function.Surjective (α.commutatorCharacterRestriction (k := k)) := by
  intro χ
  obtain ⟨ψ, hψ⟩ := MonoidHom.domRestrict_surjective (M := k)
    ((commutator α.Extension).comap (inl α)) χ.toMul
  refine ⟨Additive.ofMul ⟨ψ, ?_⟩, ?_⟩
  · apply (mem_equivariantCharacterSubgroup G M kˣ ψ).2
    intro g m
    rw [hM, trivialMulDistribMulAction_smul]
  · rw [commutatorCharacterRestriction_apply]
    exact congrArg Additive.ofMul hψ

end Restriction

variable [Finite (Abelianization α.Extension)]
  [HasEnoughRootsOfUnity k (Monoid.exponent (Abelianization α.Extension))]

/-- Transgression vanishes exactly when the character kills the commutator part of the
extension kernel. The action on the kernel need not be trivial for this criterion. -/
theorem characterTransgression_eq_zero_iff_commutatorCharacterRestriction_eq_zero
    (χ : Additive (equivariantCharacterSubgroup G M kˣ)) :
    α.characterTransgression χ = 0 ↔ α.commutatorCharacterRestriction χ = 0 := by
  rw [α.characterTransgression_eq_zero_iff trivialMulDistribMulAction_smul,
    MonoidHom.exists_comp_eq_iff_comap_commutator_le_ker,
    commutatorCharacterRestriction_apply]
  simp only [ofMul_eq_zero, MonoidHom.domRestrict_eq_one_iff,
    IsConcreteLE.le_iff, MonoidHom.mem_ker]

/-- Transgression and restriction to the commutator part of the kernel have equal kernels. -/
theorem ker_characterTransgression_eq_ker_commutatorCharacterRestriction :
    (α.characterTransgression (A := kˣ)).ker =
      (α.commutatorCharacterRestriction (k := k)).ker := by
  ext χ
  exact α.characterTransgression_eq_zero_iff_commutatorCharacterRestriction_eq_zero χ

variable [Finite M] [HasEnoughRootsOfUnity k (Monoid.exponent M)]

/-- The image of character transgression for a central extension is the character dual of
the intersection of the extension kernel with its commutator subgroup. -/
noncomputable def characterTransgressionRangeEquiv
    (hM : ∀ (g : G) (m : M), g • m = m) :
    (α.characterTransgression (A := kˣ)).range ≃+
      Additive (((commutator α.Extension).comap (inl α)) →* kˣ) :=
  (QuotientAddGroup.quotientKerEquivRange (α.characterTransgression (A := kˣ))).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq
      (α.ker_characterTransgression_eq_ker_commutatorCharacterRestriction (k := k))).trans
        (QuotientAddGroup.quotientKerEquivOfSurjective _
          (α.commutatorCharacterRestriction_surjective hM)))

/-- The image-duality isomorphism sends the class of an invariant kernel character to its
restriction to the commutator part of the kernel. -/
@[simp↓]
theorem characterTransgressionRangeEquiv_apply
    (hM : ∀ (g : G) (m : M), g • m = m)
    (χ : Additive (equivariantCharacterSubgroup G M kˣ)) :
    α.characterTransgressionRangeEquiv hM
      ⟨α.characterTransgression χ, χ, rfl⟩ = α.commutatorCharacterRestriction χ := by
  rw [← TauCeti.QuotientAddGroup.quotientKerEquivRange_apply_mk
    (α.characterTransgression (A := kˣ)) χ]
  simp only [characterTransgressionRangeEquiv, AddEquiv.trans_apply,
    AddEquiv.symm_apply_apply, QuotientAddGroup.quotientAddEquivOfEq_mk,
    TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_apply_mk]

/-- The inverse image-duality isomorphism takes a restricted kernel character back to
its transgression class, regarded as an element of the transgression image. -/
@[simp↓]
theorem characterTransgressionRangeEquiv_symm_commutatorCharacterRestriction
    (hM : ∀ (g : G) (m : M), g • m = m)
    (χ : Additive (equivariantCharacterSubgroup G M kˣ)) :
    (α.characterTransgressionRangeEquiv hM).symm
      (α.commutatorCharacterRestriction χ) = ⟨α.characterTransgression χ, χ, rfl⟩ := by
  rw [← α.characterTransgressionRangeEquiv_apply hM χ]
  exact (α.characterTransgressionRangeEquiv hM).symm_apply_apply _

end TauCeti.FactorSet
