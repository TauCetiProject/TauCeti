/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.DualNumber.Basic
public import TauCeti.Algebra.Lie.Derivation.Basic
public import TauCeti.RingTheory.Derivation.DualNumber

/-!
# Infinitesimal automorphisms of an algebra are its derivations

Let `A` be an `R`-algebra, not necessarily commutative. An automorphism of `A[ε]` over `R` that
fixes `ε` and reduces to the identity modulo `ε` (an element of
`TauCeti.infinitesimalDualNumberAut R A`) is uniquely of the form `a + b ε ↦ a + (b + D a) ε` for
a derivation `D` of `A` in the sense of `TauCeti.derivationLieAlgebra`, and composition of
automorphisms is addition of derivations.

This generalises the commutative statement: for commutative `A`, Mathlib's `Derivation R A A` is
`TauCeti.derivationLieAlgebra R A` through `TauCeti.derivationEquivDerivationLieAlgebra`, and
`TauCeti.derivationEquivInfinitesimalDualNumberAut` is obtained by composing with it.
The infinitesimal automorphisms of the base change `R[ε] ⊗[R] A` over `R[ε]` correspond to these
by conjugation with `TauCeti.dualNumberAlgebraTensorAlgEquiv`.

## Main definitions

* `TauCeti.derivationLieAlgebra.toDualNumberAut`: the automorphism `a + b ε ↦ a + (b + D a) ε`.
* `TauCeti.derivationLieAlgebra.equivInfinitesimalDualNumberAut`: derivations, with addition
  written multiplicatively, are the infinitesimal automorphisms of `A[ε]`.
* `TauCeti.derivationEquivInfinitesimalDualNumberAut`: the commutative case, for Mathlib's
  `Derivation R A A`.

## References

* R. Hartshorne, *Deformation Theory*, Graduate Texts in Mathematics 257, Springer, 2010,
  Chapter 1, for infinitesimal automorphisms as derivations.
-/

public section

open TrivSqZeroExt DualNumber

namespace TauCeti

namespace derivationLieAlgebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The algebra map `a ↦ a + (D a) ε` attached to a derivation; its multiplicativity is the
Leibniz rule. -/
private def toDualNumberAlgHom (D : derivationLieAlgebra R A) : A →ₐ[R] A[ε] where
  toFun a := inl a + inr ((D : Module.End R A) a)
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp [add_comm]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp [add_add_add_comm]
  commutes' r := by ext <;> simp [algebraMap_eq_inl']

private def dualNumberEnd (D : derivationLieAlgebra R A) : A[ε] →ₐ[R] A[ε] :=
  DualNumber.lift ⟨(toDualNumberAlgHom D, ε), eps_mul_eps, fun a ↦ by
    ext <;> simp [toDualNumberAlgHom]⟩

private theorem dualNumberEnd_fst (D : derivationLieAlgebra R A) (z : A[ε]) :
    (dualNumberEnd D z).fst = z.fst := by
  simp [dualNumberEnd, DualNumber.lift_apply_apply, toDualNumberAlgHom]

private theorem dualNumberEnd_snd (D : derivationLieAlgebra R A) (z : A[ε]) :
    (dualNumberEnd D z).snd = z.snd + (D : Module.End R A) z.fst := by
  simp [dualNumberEnd, DualNumber.lift_apply_apply, toDualNumberAlgHom, add_comm]

/-- The infinitesimal automorphism `a + b ε ↦ a + (b + D a) ε` attached to a derivation `D`.
Its inverse is the automorphism attached to `-D`. -/
def toDualNumberAut (D : derivationLieAlgebra R A) : A[ε] ≃ₐ[R] A[ε] :=
  AlgEquiv.ofAlgHom (dualNumberEnd D) (dualNumberEnd (-D))
    (by ext z <;> simp [dualNumberEnd_fst, dualNumberEnd_snd])
    (by ext z <;> simp [dualNumberEnd_fst, dualNumberEnd_snd])

/-- An infinitesimal automorphism leaves the scalar part unchanged. -/
@[simp]
theorem toDualNumberAut_fst (D : derivationLieAlgebra R A) (z : A[ε]) :
    (toDualNumberAut D z).fst = z.fst :=
  dualNumberEnd_fst D z

/-- The infinitesimal part changes by the derivation of the scalar part. -/
@[simp]
theorem toDualNumberAut_snd (D : derivationLieAlgebra R A) (z : A[ε]) :
    (toDualNumberAut D z).snd = z.snd + (D : Module.End R A) z.fst :=
  dualNumberEnd_snd D z

/-- An infinitesimal automorphism fixes `ε`. -/
@[simp]
theorem toDualNumberAut_eps (D : derivationLieAlgebra R A) : toDualNumberAut D ε = ε := by
  ext <;> simp

/-- Addition of derivations corresponds to composition of infinitesimal automorphisms. -/
@[simp]
theorem toDualNumberAut_add (D E : derivationLieAlgebra R A) :
    toDualNumberAut (D + E) = toDualNumberAut D * toDualNumberAut E := by
  ext z <;> simp [add_left_comm, add_comm]

/-- The derivation `a ↦ (e a).snd` read off an infinitesimal automorphism `e`; multiplicativity
of `e` is its Leibniz rule. -/
private def ofInfinitesimalDualNumberAut (e : infinitesimalDualNumberAut R A) :
    derivationLieAlgebra R A :=
  ⟨{ toFun := fun a ↦ (e.val (inl a)).snd
     map_add' := fun a b ↦ by simp
     map_smul' := fun r a ↦ by simp [inl_smul] }, mem_derivationLieAlgebra.2 fun x y ↦ by
    have hfst (a : A) : (e.val (inl a)).fst = a := ((mem_infinitesimalDualNumberAut _).1 e.prop).1 _
    have h := congrArg snd (map_mul e.val (inl x) (inl y))
    rw [← inl_mul, DualNumber.snd_mul, hfst, hfst] at h
    simpa [add_comm] using h⟩

/-- **Infinitesimal automorphisms are derivations**: derivations of `A`, with addition written
multiplicatively, are the automorphisms of `A[ε]` over `R` that fix `ε` and reduce to the identity
modulo `ε`. The inverse reads off the coefficient of `ε` in the image of a constant. -/
def equivInfinitesimalDualNumberAut :
    Multiplicative (derivationLieAlgebra R A) ≃* infinitesimalDualNumberAut R A where
  toFun D := ⟨toDualNumberAut D.toAdd, by simp⟩
  invFun e := Multiplicative.ofAdd (ofInfinitesimalDualNumberAut e)
  left_inv D := by
    apply Multiplicative.toAdd.injective
    ext a
    simp [ofInfinitesimalDualNumberAut]
  right_inv e := by
    obtain ⟨hfst, heps⟩ := (mem_infinitesimalDualNumberAut _).1 e.prop
    apply Subtype.ext
    ext z
    · simpa only [toDualNumberAut_fst] using (hfst z).symm
    · have h : e.val z = e.val (inl z.fst) + e.val (inl z.snd) * e.val ε :=
        AlgHom.apply_dualNumber e.val.toAlgHom z
      rw [heps] at h
      rw [h, toDualNumberAut_snd]
      simp [ofInfinitesimalDualNumberAut, hfst, add_comm]
  map_mul' D E := Subtype.ext (toDualNumberAut_add D.toAdd E.toAdd)

/-- The automorphism corresponding to a derivation is `toDualNumberAut`. -/
@[simp]
theorem equivInfinitesimalDualNumberAut_apply_coe
    (D : Multiplicative (derivationLieAlgebra R A)) :
    (equivInfinitesimalDualNumberAut D : A[ε] ≃ₐ[R] A[ε]) = toDualNumberAut D.toAdd :=
  (rfl)

/-- Recover a derivation by taking the infinitesimal part of the image of each constant. -/
@[simp]
theorem equivInfinitesimalDualNumberAut_symm_apply (e : infinitesimalDualNumberAut R A) (a : A) :
    ((equivInfinitesimalDualNumberAut.symm e).toAdd : Module.End R A) a = (e.val (inl a)).snd :=
  (rfl)

end derivationLieAlgebra

section Commutative

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- For commutative `A`, the automorphism attached to a Mathlib derivation agrees with the one
attached to the corresponding element of `derivationLieAlgebra R A`. -/
@[simp]
theorem derivationLieAlgebra.toDualNumberAut_derivationEquivDerivationLieAlgebra
    (d : Derivation R A A) :
    derivationLieAlgebra.toDualNumberAut (derivationEquivDerivationLieAlgebra d) =
      d.toDualNumberAut := by
  ext z <;> simp

/-- Derivations, with addition written multiplicatively, are the infinitesimal
automorphisms of the dual numbers: the commutative case of
`TauCeti.derivationLieAlgebra.equivInfinitesimalDualNumberAut`. -/
def derivationEquivInfinitesimalDualNumberAut :
    Multiplicative (Derivation R A A) ≃* infinitesimalDualNumberAut R A :=
  (AddEquiv.toMultiplicative derivationEquivDerivationLieAlgebra.toLinearEquiv.toAddEquiv).trans
    derivationLieAlgebra.equivInfinitesimalDualNumberAut

/-- The automorphism corresponding to a derivation is `Derivation.toDualNumberAut`. -/
@[simp]
theorem derivationEquivInfinitesimalDualNumberAut_apply_coe
    (d : Multiplicative (Derivation R A A)) :
    (derivationEquivInfinitesimalDualNumberAut d : A[ε] ≃ₐ[R] A[ε]) =
      d.toAdd.toDualNumberAut :=
  derivationLieAlgebra.toDualNumberAut_derivationEquivDerivationLieAlgebra d.toAdd

/-- Recover a derivation by taking the infinitesimal part of the image of each constant. -/
@[simp]
theorem derivationEquivInfinitesimalDualNumberAut_symm_apply
    (e : infinitesimalDualNumberAut R A) (a : A) :
    ((derivationEquivInfinitesimalDualNumberAut (R := R) (A := A)).symm e).toAdd a =
      (e.val (inl a)).snd :=
  -- the inverse of the composite is the inverse of `derivationEquivDerivationLieAlgebra`
  -- applied after that of `equivInfinitesimalDualNumberAut`
  (derivationEquivDerivationLieAlgebra_symm_apply _ a).trans
    (derivationLieAlgebra.equivInfinitesimalDualNumberAut_symm_apply e a)

end Commutative

end TauCeti
