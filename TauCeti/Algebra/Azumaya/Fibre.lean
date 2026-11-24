/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Azumaya.Basic
public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Quaternion
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.LocalRing.Module

/-!
# Azumaya algebras and their fibres

An Azumaya algebra over a commutative ring `R`, in Mathlib's sense `IsAzumaya R A`, is a finite
projective `R`-algebra `A` which is faithful as an `R`-module and for which the map
`AlgHom.mulLeftRight R A : A ⊗[R] Aᵐᵒᵖ → End_R(A)`, `a ⊗ b ↦ (x ↦ a x b)`, is bijective. This file
replaces faithfulness by a fibrewise condition: a finite flat `R`-module `M` is faithful exactly
when every fibre `κ(p) ⊗[R] M` at a prime `p` of `R` is nonzero, that is, has positive dimension
over the residue field `κ(p)` (`Module.faithfulSMul_iff_forall_finrank_residueField_pos`). Hence a
finite projective algebra is Azumaya exactly when its fibres have positive rank and
`AlgHom.mulLeftRight R A` is bijective (`isAzumaya_iff_positive_fibres_mulLeftRight`), the form of
Grothendieck's criterion used for Azumaya algebras over schemes.

One direction holds for every finite module: the support of a finite module is the zero locus of
its annihilator, so a faithful module has full support, and by Nakayama's lemma its fibres are
nonzero. Conversely, at a maximal ideal `m` the localization `M_m` of a finite flat module is free
over the local ring `R_m`, and nonzero when the fibre at `m` is, so `R_m` acts faithfully on it; an
element of `R` killing `M` therefore vanishes in every `R_m`, hence is zero.

The positivity condition cannot be dropped, and global nontriviality of `A` does not replace it:

* the zero matrix algebra over a field has bijective `mulLeftRight` but is not Azumaya
  (`not_isAzumaya_matrix_fin_zero`, `bijective_mulLeftRight_matrix_fin_zero`);
* the algebra `k` over `k × k` through the first projection is nonzero, but not faithful and so
  not Azumaya (`not_isAzumaya_prod_fst`);
* the zero ring is Azumaya over itself, as every ring is (Mathlib's `IsAzumaya.id`): this is the
  empty-base case, in which positivity is vacuous.

The dual numbers `k[ε]` over a field are free of rank two with nonzero fibre but not Azumaya
(`not_isAzumaya_dualNumber`): `ε` is central and not a scalar, while Azumaya algebras are central.
Over `ℤ`, the Lipschitz order `ℍ[ℤ] = ℤ⟨i, j⟩`, `i² = j² = −1`, `ij = −ji`, is free of rank four
and faithful but not Azumaya (`not_isAzumaya_lipschitz`): modulo `2` it is commutative, so every
map `x ↦ Σ aₙ x bₙ` is congruent modulo `2` to right multiplication by its value at `1`, and
`x ↦ re x` is not.

## Main results

* `Module.faithfulSMul_iff_forall_finrank_residueField_pos`: a finite flat module is faithful iff
  all of its fibres at primes are nonzero.
* `isAzumaya_iff_positive_fibres_mulLeftRight`: a finite projective algebra is Azumaya iff its
  fibres have positive rank and `AlgHom.mulLeftRight R A` is bijective.

## References

* A. Grothendieck, *Le groupe de Brauer. I. Algèbres d'Azumaya et interprétations diverses*,
  Séminaire Bourbaki, exposé 290 (1964-1966), Théorème 5.1.
-/

public section

open TensorProduct
open scoped Quaternion

universe u v

section Fibre

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- A faithful finite module has nonzero fibre at every prime: its support is the zero locus of its
annihilator, which is everything, and by Nakayama's lemma the fibre at a point of the support is
nonzero. -/
theorem Module.finrank_residueField_pos_of_faithfulSMul [Module.Finite R M] [FaithfulSMul R M]
    (p : PrimeSpectrum R) :
    0 < Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) := by
  have hp : p ∈ Module.support R M := Module.mem_support_iff_of_finite.2 <| by
    rw [Module.annihilator_eq_bot.2 inferInstance]
    exact bot_le
  have := (Module.mem_support_iff_nontrivial_residueField_tensorProduct p).1 hp
  exact Module.finrank_pos

/-- A finite flat module whose fibres at all primes are nonzero is faithful: at each maximal ideal
`m` its localization is free over `R_m` and nonzero, so an element of `R` killing the module
vanishes in every `R_m`. -/
theorem Module.faithfulSMul_of_forall_finrank_residueField_pos [Module.Finite R M]
    [Module.Flat R M]
    (h : ∀ p : PrimeSpectrum R,
      0 < Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) :
    FaithfulSMul R M := by
  refine Module.annihilator_eq_bot.1 (eq_bot_iff.2 fun r hr ↦ ?_)
  rw [Module.mem_annihilator] at hr
  refine (Submodule.mem_bot R).2 (eq_zero_of_localization r fun J hJ ↦ ?_)
  let p : PrimeSpectrum R := ⟨J, hJ.isPrime⟩
  have : Nontrivial (LocalizedModule J.primeCompl M) :=
    Module.mem_support_iff.1 ((Module.mem_support_iff_nontrivial_residueField_tensorProduct p).2
      (Module.nontrivial_of_finrank_pos (h p)))
  have : Module.Free (Localization.AtPrime J) (LocalizedModule J.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  refine smul_left_injective' (M := Localization.AtPrime J) (α := LocalizedModule J.primeCompl M)
    (funext fun x ↦ ?_)
  induction x using LocalizedModule.induction_on with
  | h m s =>
    simp [LocalizedModule.smul'_mk, hr]

/-- **Faithfulness is fibrewise.** A finite flat module over a commutative ring is faithful iff
its fibre `κ(p) ⊗[R] M` at every prime `p` is nonzero. -/
theorem Module.faithfulSMul_iff_forall_finrank_residueField_pos [Module.Finite R M]
    [Module.Flat R M] :
    FaithfulSMul R M ↔ ∀ p : PrimeSpectrum R,
      0 < Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) :=
  ⟨fun _ ↦ Module.finrank_residueField_pos_of_faithfulSMul,
    Module.faithfulSMul_of_forall_finrank_residueField_pos⟩

end Fibre

section Azumaya

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

end Azumaya

section Checks

variable (k : Type u) [Field k]

/-- The zero matrix algebra over a field is not Azumaya: it is the zero ring, on which the
nonzero field cannot act faithfully. -/
theorem not_isAzumaya_matrix_fin_zero : ¬ IsAzumaya k (Matrix (Fin 0) (Fin 0) k) := fun _ ↦
  zero_ne_one ((FaithfulSMul.algebraMap_injective k (Matrix (Fin 0) (Fin 0) k))
    (Subsingleton.elim _ _))

/-- The map `A ⊗ Aᵐᵒᵖ → End(A)` of the zero matrix algebra over a field is bijective, both sides
being zero. So bijectivity of `mulLeftRight` alone does not make an algebra Azumaya. -/
theorem bijective_mulLeftRight_matrix_fin_zero :
    Function.Bijective (AlgHom.mulLeftRight k (Matrix (Fin 0) (Fin 0) k)) :=
  ⟨Function.injective_of_subsingleton _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- The algebra `k` over `k × k` through the first projection is nonzero but not Azumaya: the
idempotent `(0, 1)` acts on it by zero, so it is not faithful. -/
theorem not_isAzumaya_prod_fst :
    letI := (RingHom.fst k k).toAlgebra
    ¬ IsAzumaya (k × k) k := by
  let := (RingHom.fst k k).toAlgebra
  intro h
  have := (FaithfulSMul.algebraMap_injective (k × k) k) (a₁ := (0, 1)) (a₂ := 0) rfl
  simpa using congrArg Prod.snd this

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
private lemma exists_lipschitz_commutator_eq_two_smul (a x : ℍ[ℤ]) :
    ∃ y : ℍ[ℤ], a * x - x * a = (2 : ℤ) • y :=
  ⟨⟨0, a.imJ * x.imK - a.imK * x.imJ, a.imK * x.imI - a.imI * x.imK,
    a.imI * x.imJ - a.imJ * x.imI⟩, by ext <;> simp <;> ring⟩

/-- Modulo `2`, every endomorphism of `ℍ[ℤ]` in the image of `mulLeftRight` is right multiplication
by its value at `1`, since `ℍ[ℤ]` is commutative modulo `2`. -/
private lemma exists_mulLeftRight_lipschitz_sub_eq_two_smul (t : ℍ[ℤ] ⊗[ℤ] ℍ[ℤ]ᵐᵒᵖ) (x : ℍ[ℤ]) :
    ∃ y : ℍ[ℤ],
      AlgHom.mulLeftRight ℤ ℍ[ℤ] t x - x * AlgHom.mulLeftRight ℤ ℍ[ℤ] t 1 = (2 : ℤ) • y := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    obtain ⟨y, hy⟩ := exists_lipschitz_commutator_eq_two_smul a x
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
theorem not_isAzumaya_lipschitz : ¬ IsAzumaya ℤ ℍ[ℤ] := by
  intro h
  let E : Module.End ℤ ℍ[ℤ] := Algebra.linearMap ℤ ℍ[ℤ] ∘ₗ QuaternionAlgebra.reₗ (-1) 0 (-1)
  obtain ⟨t, ht⟩ := h.bij.2 E
  obtain ⟨y, hy⟩ := exists_mulLeftRight_lipschitz_sub_eq_two_smul t ⟨0, 1, 0, 0⟩
  have := congrArg QuaternionAlgebra.imI hy
  rw [QuaternionAlgebra.imI_smul] at this
  simp [ht, E] at this
  omega

end Checks
