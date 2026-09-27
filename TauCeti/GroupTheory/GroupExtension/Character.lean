/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Cohomology
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Characters of factor-set extensions

Pushing a factor set forward along an invariant character of its kernel gives a
second-cohomology class. This is the character transgression, with the convention
that it sends `χ` to the class of `χ ∘ α`.

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

include hA

/-- An invariant kernel character has trivial transgression exactly when it extends
to a character of the factor-set extension. -/
theorem cohomologyClass_map_eq_zero_iff (χ : M →*[G] A) :
    (α.map χ).cohomologyClass = 0 ↔
      ∃ ψ : α.Extension →* A, ψ.comp (inl α) = χ.toMonoidHom := by
  rw [cohomologyClass_eq_zero_iff]
  constructor
  · rintro ⟨c, hc⟩
    have hc1 : c 1 = 1 := by simpa [hA] using hc 1 1
    refine ⟨{ toFun x := χ x.left * c x.right
              map_one' := by simp [hc1]
              map_mul' x y := ?_ }, ?_⟩
    · simp only [Extension.mul_left, Extension.mul_right, map_mul, map_smul, hA]
      rw [← map_apply, ← hc, hA]
      simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    · ext a
      simp [hc1]
  · rintro ⟨ψ, hψ⟩
    refine ⟨fun g ↦ ψ (α.canonicalSection g), fun g h ↦ ?_⟩
    have heq : ∀ a, ψ (inl α a) = χ a := DFunLike.congr_fun hψ
    have key := congrArg ψ (α.canonicalSection_mul g h)
    simp only [map_mul, heq] at key
    rw [hA, map_apply]
    rw [div_mul_eq_mul_div, mul_comm, div_eq_iff_eq_mul]
    exact key

/-- Two invariant kernel characters have the same transgression exactly when their
quotient extends to the whole extension. -/
theorem cohomologyClass_map_eq_iff (χ χ' : M →*[G] A) :
    (α.map χ).cohomologyClass = (α.map χ').cohomologyClass ↔
      ∃ ψ : α.Extension →* A,
        ψ.comp (inl α) = χ.toMonoidHom / χ'.toMonoidHom := by
  let δ : M →*[G] A :=
    { χ.toMonoidHom / χ'.toMonoidHom with
      map_smul' g a := by simp [map_smul, hA] }
  have hδ_apply (a : M) : δ a = χ a / χ' a := rfl
  rw [← α.cohomologyClass_map_eq_zero_iff hA δ, cohomologyClass_eq_zero_iff,
    cohomologyClass_eq_iff]
  simp only [IsMulCoboundary₂, map_apply, hδ_apply]

/-- For a stem extension, different invariant characters of the kernel give different
second-cohomology classes. No finiteness or divisibility assumption is needed. -/
theorem cohomologyClass_map_injective_of_range_inl_le_commutator
    (hstem : (inl α).range ≤ commutator α.Extension) :
    Function.Injective (fun χ : M →*[G] A ↦ (α.map χ).cohomologyClass) := by
  intro χ χ' heq
  obtain ⟨ψ, hψ⟩ := (α.cohomologyClass_map_eq_iff hA χ χ').1 heq
  ext a
  have hmem := Abelianization.commutator_subset_ker ψ (hstem ⟨a, rfl⟩)
  have hval := DFunLike.congr_fun hψ a
  have hdiv : χ a / χ' a = 1 := hval.symm.trans hmem
  exact div_eq_one.mp hdiv

end TauCeti.FactorSet
