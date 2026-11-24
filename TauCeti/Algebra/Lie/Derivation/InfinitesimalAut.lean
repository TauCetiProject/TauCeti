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
a derivation `D` of `A` in the sense of `TauCeti.derivationLieAlgebra` (this is
`TauCeti.derivationLieAlgebra.toDualNumberAut`), and composition of automorphisms is addition of
derivations.

This generalises the commutative statement: for commutative `A`, Mathlib's `Derivation R A A` is
`TauCeti.derivationLieAlgebra R A` through `TauCeti.derivationEquivDerivationLieAlgebra`, and
`TauCeti.derivationEquivInfinitesimalDualNumberAut` is obtained by composing with it.
The infinitesimal automorphisms of the base change `R[ε] ⊗[R] A` over `R[ε]` correspond to these
by conjugation with `TauCeti.dualNumberAlgebraTensorAlgEquiv`.

## Main definitions

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
      d.toAdd.toDualNumberAut := by
  ext z <;> simp [derivationEquivInfinitesimalDualNumberAut]

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
