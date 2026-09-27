/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Cohomology
public import TauCeti.GroupTheory.GroupAction.Character
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Characters of factor-set extensions

Pushing a factor set forward along an invariant character of its kernel gives a
second-cohomology class. This is the character transgression, with the convention
that it sends `χ` to the class of `χ ∘ α`. It is bundled as an additive homomorphism
from the additive type tag of the pointwise group of equivariant characters, so its
kernel and range are available as additive subgroups.

The class vanishes exactly when the character extends to the whole extension.
Consequently, if the kernel lies in the commutator subgroup, transgression is
injective. These are the character-theoretic criteria used to identify the kernel
of a representation group with the dual of the factor-set class group.

The coefficient group may be any commutative group with trivial action; the action
on the kernel need not be trivial, provided its characters are equivariant.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985), Chapters 2–3.
-/

public section

namespace TauCeti.FactorSet

open groupCohomology

variable {G M A : Type} [Group G] [CommGroup M] [CommGroup A]
  [MulDistribMulAction G M] [MulDistribMulAction G A]
  (α : FactorSet G M) (hA : ∀ (g : G) (a : A), g • a = a)

/-- Character transgression sends an equivariant kernel character `χ` to the class of
`χ ∘ α`, as an additive homomorphism on the pointwise character group.
For a trivial coefficient action, its kernel consists of the characters
extending to the whole factor-set extension. -/
noncomputable def characterTransgression :
    Additive (equivariantCharacterSubgroup G M A) →+ H2 (Rep.ofMulDistribMulAction G A) where
  toFun χ := (α.map (equivariantCharacterEquiv G M A χ.toMul)).cohomologyClass
  map_zero' := by
    have h : α.map (equivariantCharacterEquiv G M A 1) = trivial G A := by
      ext p
      simp [map_apply]
    rw [toMul_zero, h, cohomologyClass_trivial]
  map_add' χ χ' := by
    simp only [cohomologyClass_def, ← map_add]
    congr 1
    apply cocycles₂_ext
    intro g h
    simp only [coe_toCocycles₂, map_apply]
    -- Mathlib's custom `FunLike` coercion for `cocycles₂` has no addition-application lemma.
    -- Expose pointwise addition in `Additive A`; `Submodule.coe_add` does not match that coercion.
    change Additive.ofMul (equivariantCharacterEquiv G M A (χ + χ').toMul (α (g, h))) =
      (α.map (equivariantCharacterEquiv G M A χ.toMul)).toCocycles₂ (g, h) +
      (α.map (equivariantCharacterEquiv G M A χ'.toMul)).toCocycles₂ (g, h)
    simp only [coe_toCocycles₂, map_apply, equivariantCharacterEquiv_apply, toMul_add,
      Subgroup.coe_mul, MonoidHom.mul_apply, ofMul_mul]
    rfl

@[simp]
theorem characterTransgression_apply (χ : Additive (equivariantCharacterSubgroup G M A)) :
    α.characterTransgression χ =
      (α.map (equivariantCharacterEquiv G M A χ.toMul)).cohomologyClass :=
  (rfl)

include hA

/-- An invariant kernel character has trivial transgression exactly when it extends
to a character of the factor-set extension. -/
theorem characterTransgression_eq_zero_iff (χ : Additive (equivariantCharacterSubgroup G M A)) :
    α.characterTransgression χ = 0 ↔
      ∃ ψ : α.Extension →* A, ψ.comp (inl α) = χ.toMul.val := by
  rw [characterTransgression_apply, cohomologyClass_eq_zero_iff]
  constructor
  · rintro ⟨c, hc⟩
    simp only [map_apply, equivariantCharacterEquiv_apply] at hc
    have hc1 : c 1 = 1 := by simpa [hA] using hc 1 1
    refine ⟨{ toFun x := χ.toMul.val x.left * c x.right
              map_one' := by simp [hc1]
              map_mul' x y := ?_ }, ?_⟩
    · simp only [Extension.mul_left, Extension.mul_right, map_mul,
        (mem_equivariantCharacterSubgroup G M A _).mp χ.toMul.property, hA]
      rw [← hc, hA]
      simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    · ext a
      simp [hc1]
  · rintro ⟨ψ, hψ⟩
    refine ⟨fun g ↦ ψ (α.canonicalSection g), fun g h ↦ ?_⟩
    have heq : ∀ a, ψ (inl α a) = χ.toMul.val a := DFunLike.congr_fun hψ
    have key := congrArg ψ (α.canonicalSection_mul g h)
    simp only [map_mul, heq] at key
    rw [hA, map_apply, equivariantCharacterEquiv_apply]
    rw [div_mul_eq_mul_div, mul_comm, div_eq_iff_eq_mul]
    exact key

/-- Two invariant kernel characters have the same transgression exactly when their
quotient extends to the whole extension. -/
theorem characterTransgression_eq_iff (χ χ' : Additive (equivariantCharacterSubgroup G M A)) :
    α.characterTransgression χ = α.characterTransgression χ' ↔
      ∃ ψ : α.Extension →* A,
        ψ.comp (inl α) = χ.toMul.val / χ'.toMul.val := by
  rw [← sub_eq_zero, ← map_sub, α.characterTransgression_eq_zero_iff hA]
  rw [toMul_sub, Subgroup.coe_div]

/-- For a stem extension, different invariant characters of the kernel give different
second-cohomology classes. No finiteness or divisibility assumption is needed. -/
theorem characterTransgression_injective_of_range_inl_le_commutator
    (hstem : (inl α).range ≤ commutator α.Extension) :
    Function.Injective (α.characterTransgression (A := A)) := by
  intro χ χ' heq
  obtain ⟨ψ, hψ⟩ := (α.characterTransgression_eq_iff hA χ χ').1 heq
  apply Additive.toMul.injective
  apply Subtype.ext
  ext a
  have hmem := Abelianization.commutator_subset_ker ψ (hstem ⟨a, rfl⟩)
  have hval := DFunLike.congr_fun hψ a
  have hdiv : χ.toMul.val a / χ'.toMul.val a = 1 := hval.symm.trans hmem
  exact div_eq_one.mp hdiv

end TauCeti.FactorSet
