/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.SymmetricAlgebra.BaseChange

/-!
# Basic invariants under scalar extension

A system of basic invariants consists of homogeneous invariants that freely generate the
invariant algebra. For a representation on `V`, use the contragredient representation to obtain
basic invariant polynomial functions on `V`.

`Representation.IsBasicInvariants.baseChange` extends a system of basic invariants for a finite
group along a flat algebra, keeping the degree of each generator. It uses
`Representation.symmetricAlgebraInvariantsBaseChangeEquiv` and Mathlib's
`MvPolynomial.algebraTensorAlgEquiv` to compare the two polynomial presentations.
-/

public section

open MvPolynomial TauCeti.SymmetricAlgebra
open scoped TensorProduct

namespace Representation

variable {R G M ι : Type*}

section CommSemiring

variable [CommSemiring R] [Monoid G] [AddCommMonoid M] [Module R M]

/-- The family `f` is a system of basic invariants of degrees `d` if each `f i` is homogeneous of
degree `d i` and evaluation at `f` identifies the polynomial algebra with `Sym(M)^G`. -/
structure IsBasicInvariants (ρ : Representation R G M)
    (f : ι → ρ.symmetricAlgebraInvariants) (d : ι → ℕ) : Prop where
  /-- Each generator belongs to the specified homogeneous piece. -/
  homogeneous (i : ι) : (f i : SymmetricAlgebra R M) ∈ homogeneousSubmodule R M (d i)
  /-- Polynomial evaluation at the generators is bijective. -/
  bijective_aeval : Function.Bijective (aeval (R := R) f)

end CommSemiring

section BaseChange

variable {S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G] [Finite G]
  [AddCommGroup M] [Module R M] [Module.Flat R S]
  {ρ : Representation R G M} {f : ι → ρ.symmetricAlgebraInvariants} {d : ι → ℕ}

/-- Over a flat algebra `S`, the scalar extensions of basic invariants of a finite group
are basic invariants of the same degrees. -/
theorem IsBasicInvariants.baseChange (h : ρ.IsBasicInvariants f d) :
    (ρ.baseChange S).IsBasicInvariants
      (fun i ↦ ρ.symmetricAlgebraInvariantsBaseChangeEquiv (1 ⊗ₜ[R] f i)) d := by
  constructor
  · intro i
    rw [coe_symmetricAlgebraInvariantsBaseChangeEquiv, Algebra.TensorProduct.map_tmul]
    exact scalarTensorBialgEquiv_mem_homogeneousSubmodule
      (Submodule.tmul_mem_baseChange_of_mem 1 (h.homogeneous i))
  · let e := (MvPolynomial.algebraTensorAlgEquiv (σ := ι) R S).symm.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
        (AlgEquiv.ofBijective (aeval f) h.bijective_aeval)).trans
        ρ.symmetricAlgebraInvariantsBaseChangeEquiv)
    have he : aeval (fun i ↦ ρ.symmetricAlgebraInvariantsBaseChangeEquiv (1 ⊗ₜ[R] f i)) =
        e.toAlgHom := by
      ext i
      simp [e]
    rw [he]
    exact e.bijective

end BaseChange

end Representation
