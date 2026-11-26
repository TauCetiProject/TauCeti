/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Azumaya.Basic
public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Quaternion
public import TauCeti.RingTheory.LocalProperties.Fiber

/-!
# Azumaya algebras and their fibres

An Azumaya algebra over a commutative ring `R`, in Mathlib's sense `IsAzumaya R A`, is a finite
projective `R`-algebra `A` which is faithful as an `R`-module and for which the map
`AlgHom.mulLeftRight R A : A ⊗[R] Aᵐᵒᵖ → End_R(A)`, `a ⊗ b ↦ (x ↦ a x b)`, is bijective. This file
replaces faithfulness by a fibrewise condition: a finite flat `R`-module `M` is faithful exactly
when every fibre `κ(p) ⊗[R] M` at a prime `p` of `R` is nonzero, that is, has positive dimension
over the residue field `κ(p)` (`Module.faithfulSMul_iff_forall_finrank_residueField_pos`). Hence a
finite projective algebra is Azumaya exactly when its fibres have positive rank and
`AlgHom.mulLeftRight R A` is bijective
(`TauCeti.Brauer.isAzumaya_iff_positive_fibres_mulLeftRight`), the form of Grothendieck's criterion
used for Azumaya algebras over schemes.

The positivity condition cannot be dropped, and global nontriviality of `A` does not replace it:

* the zero matrix algebra over a field has bijective `mulLeftRight` but is not Azumaya
  (`TauCeti.not_isAzumaya_matrix_fin_zero`, `TauCeti.mulLeftRight_matrix_fin_zero_bijective`);
* the algebra `k` over `k × k` through the first projection is nonzero, but not faithful and so
  not Azumaya (`TauCeti.not_isAzumaya_prod_fst`): its fibre over the second point of
  `Spec (k × k)` has rank zero (`TauCeti.finrank_residueField_ker_snd_tensorProduct_prod_fst`);
* the zero ring is Azumaya over itself, as every ring is (Mathlib's `IsAzumaya.id`): this is the
  empty-base case, in which positivity is vacuous.

The dual numbers `k[ε]` over a field are free of rank two with nonzero fibre but not Azumaya
(`TauCeti.not_isAzumaya_dualNumber`): `ε` is central and not a scalar, while Azumaya algebras are
central.
Over `ℤ`, the Lipschitz order `ℍ[ℤ] = ℤ⟨i, j⟩`, `i² = j² = −1`, `ij = −ji`, is free of rank four
and faithful but not Azumaya (`TauCeti.not_isAzumaya_quaternion_int`): modulo `2` it is
commutative, so every map `x ↦ Σ aₙ x bₙ` is congruent modulo `2` to right multiplication by its
value at `1`, and `x ↦ re x` is not.

## Main results

* `TauCeti.Brauer.isAzumaya_iff_positive_fibres_mulLeftRight`: a finite projective algebra is
  Azumaya iff its fibres have positive rank and `AlgHom.mulLeftRight R A` is bijective.

## References

* A. Grothendieck, *Le groupe de Brauer. I. Algèbres d'Azumaya et interprétations diverses*,
  Séminaire Bourbaki, exposé 290 (1964-1966), Théorème 5.1.
-/

public section

open TensorProduct
open scoped Quaternion

universe u v

namespace TauCeti

namespace Brauer

/-- **Azumaya algebras by fibres.** A finite projective algebra `A` over a commutative ring `R` is
Azumaya iff its fibre over every residue field of `R` has positive rank and
`A ⊗[R] Aᵐᵒᵖ → End_R(A)`, `a ⊗ b ↦ (x ↦ a x b)`, is bijective. -/
theorem isAzumaya_iff_positive_fibres_mulLeftRight (R : Type u) (A : Type v) [CommRing R] [Ring A]
    [Algebra R A] [Module.Finite R A] [Module.Projective R A] :
    IsAzumaya R A ↔
      (∀ p : PrimeSpectrum R,
        0 < Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] A)) ∧
      Function.Bijective (AlgHom.mulLeftRight R A) := by
  rw [← Module.faithfulSMul_iff_forall_finrank_residueField_pos (R := R) (M := A)]
  exact ⟨fun h ↦ ⟨h.toFaithfulSMul, h.bij⟩, fun ⟨_, h⟩ ↦ ⟨h⟩⟩

end Brauer

section Checks

variable (k : Type u) [Field k]

/-- The zero matrix algebra over a field is not Azumaya: it is the zero ring, on which the
nonzero field cannot act faithfully. -/
theorem not_isAzumaya_matrix_fin_zero : ¬ IsAzumaya k (Matrix (Fin 0) (Fin 0) k) := fun _ ↦
  zero_ne_one ((FaithfulSMul.algebraMap_injective k (Matrix (Fin 0) (Fin 0) k))
    (Subsingleton.elim _ _))

/-- The map `A ⊗ Aᵐᵒᵖ → End(A)` of the zero matrix algebra over a field is bijective, both sides
being zero. So bijectivity of `mulLeftRight` alone does not make an algebra Azumaya. -/
theorem mulLeftRight_matrix_fin_zero_bijective :
    Function.Bijective (AlgHom.mulLeftRight k (Matrix (Fin 0) (Fin 0) k)) :=
  ⟨Function.injective_of_subsingleton _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- The algebra `k` over `k × k` through the first projection is nonzero but not Azumaya: the
idempotent `(0, 1)` acts on it by zero, so it is not faithful. -/
theorem not_isAzumaya_prod_fst :
    letI := (RingHom.fst k k).toAlgebra
    ¬ IsAzumaya (k × k) k := by
  let := (RingHom.fst k k).toAlgebra
  intro h
  have := (FaithfulSMul.algebraMap_injective (k × k) k) (a₁ := (0, 1)) (a₂ := 0)
    (by simp [RingHom.algebraMap_toAlgebra])
  simpa using congrArg Prod.snd this

/-- The algebra `k` over `k × k` through the first projection has rank zero at the second point of
`Spec (k × k)`, the kernel of the second projection: the idempotent `(1, 0)` acts on `k` by one and
on the residue field by zero, so the fibre vanishes. This is where the positivity condition of
`TauCeti.Brauer.isAzumaya_iff_positive_fibres_mulLeftRight` fails. -/
theorem finrank_residueField_ker_snd_tensorProduct_prod_fst :
    letI := (RingHom.fst k k).toAlgebra
    letI := RingHom.ker_isPrime (RingHom.snd k k)
    Module.finrank (RingHom.ker (RingHom.snd k k)).ResidueField
      ((RingHom.ker (RingHom.snd k k)).ResidueField ⊗[k × k] k) = 0 := by
  let := (RingHom.fst k k).toAlgebra
  let := RingHom.ker_isPrime (RingHom.snd k k)
  let P := RingHom.ker (RingHom.snd k k)
  have hP : algebraMap (k × k) P.ResidueField (1, 0) = 0 :=
    (Ideal.algebraMap_residueField_eq_zero).2 (by simp [P])
  have : Subsingleton (P.ResidueField ⊗[k × k] k) := by
    refine subsingleton_of_forall_eq 0 fun t ↦ ?_
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      have hy : ((1, 0) : k × k) • y = y := by
        simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      rw [← hy, ← TensorProduct.smul_tmul, Algebra.smul_def, hP, zero_mul,
        TensorProduct.zero_tmul]
    | add t t' ht ht' => rw [ht, ht', add_zero]
  exact Module.finrank_zero_of_subsingleton

/-- The dual numbers over a field are not Azumaya: they are commutative, so `ε` is central, but `ε`
is not a scalar, while an Azumaya algebra has centre `k`. -/
theorem not_isAzumaya_dualNumber : ¬ IsAzumaya k (DualNumber k) := by
  intro h
  have hc := (Algebra.IsCentral.out (K := k) (D := DualNumber k))
    (Subalgebra.mem_center_iff.2 fun b ↦ mul_comm b DualNumber.eps)
  obtain ⟨r, hr⟩ := Algebra.mem_bot.1 hc
  simpa [TrivSqZeroExt.algebraMap_eq_inl] using congrArg TrivSqZeroExt.snd hr

/-- In the Lipschitz order `ℍ[ℤ]` every commutator has even coordinates: `a x - x a` is twice
the cross product of the vector parts. -/
private lemma exists_quaternion_int_commutator_eq_two_smul (a x : ℍ[ℤ]) :
    ∃ y : ℍ[ℤ], a * x - x * a = (2 : ℤ) • y :=
  ⟨⟨0, a.imJ * x.imK - a.imK * x.imJ, a.imK * x.imI - a.imI * x.imK,
    a.imI * x.imJ - a.imJ * x.imI⟩, by ext <;> simp <;> ring⟩

/-- Modulo `2`, every endomorphism of `ℍ[ℤ]` in the image of `mulLeftRight` is right multiplication
by its value at `1`, since `ℍ[ℤ]` is commutative modulo `2`. -/
private lemma exists_mulLeftRight_quaternion_int_sub_eq_two_smul (t : ℍ[ℤ] ⊗[ℤ] ℍ[ℤ]ᵐᵒᵖ)
    (x : ℍ[ℤ]) :
    ∃ y : ℍ[ℤ],
      AlgHom.mulLeftRight ℤ ℍ[ℤ] t x - x * AlgHom.mulLeftRight ℤ ℍ[ℤ] t 1 = (2 : ℤ) • y := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    obtain ⟨y, hy⟩ := exists_quaternion_int_commutator_eq_two_smul a x
    refine ⟨y * b.unop, ?_⟩
    rw [AlgHom.mulLeftRight_apply, AlgHom.mulLeftRight_apply, mul_one, ← smul_mul_assoc, ← hy]
    simp only [sub_mul, mul_assoc]
  | add t t' ht ht' =>
    obtain ⟨y, hy⟩ := ht
    obtain ⟨y', hy'⟩ := ht'
    refine ⟨y + y', ?_⟩
    simp only [map_add, LinearMap.add_apply, mul_add, smul_add, ← hy, ← hy']
    abel

/-- The Lipschitz order `ℤ⟨i, j⟩`, `i² = j² = −1`, `ij = −ji`, is free of rank four over `ℤ` but
not Azumaya: the endomorphism `x ↦ re x` is not of the form `x ↦ Σ aₙ x bₙ`, since modulo `2`
the algebra is commutative and such a map is multiplication by its value at `1`. -/
theorem not_isAzumaya_quaternion_int : ¬ IsAzumaya ℤ ℍ[ℤ] := by
  intro h
  let E : Module.End ℤ ℍ[ℤ] := Algebra.linearMap ℤ ℍ[ℤ] ∘ₗ QuaternionAlgebra.reₗ (-1) 0 (-1)
  obtain ⟨t, ht⟩ := h.bij.2 E
  obtain ⟨y, hy⟩ := exists_mulLeftRight_quaternion_int_sub_eq_two_smul t ⟨0, 1, 0, 0⟩
  have := congrArg QuaternionAlgebra.imI hy
  rw [QuaternionAlgebra.imI_smul] at this
  have h2 : (-1 : ℤ) = 2 * y.imI := by simpa [ht, E] using this
  omega

end Checks

end TauCeti
