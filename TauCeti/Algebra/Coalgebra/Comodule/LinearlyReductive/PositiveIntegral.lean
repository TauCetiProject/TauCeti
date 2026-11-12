/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Unitarization
public import TauCeti.Algebra.Coalgebra.Comodule.Unitary.Subcomodule

/-!
# Complete reducibility from a positive invariant integral

A complex Hopf star algebra with a nonzero positive right invariant integral is linearly
reductive. Its finite-dimensional comodules admit a basis with unitary coefficient matrix by
algebraic Haar averaging; orthogonal complements then split every subcomodule. No topology on
the Hopf algebra or preassigned inner product on the comodule is required.

The conclusion is the native `TauCeti.Coalgebra.IsLinearlyReductive` interface. In particular,
`TauCeti.Coalgebra.IsLinearlyReductive.isCompletelyReducible` applies it to arbitrary comodules,
in every carrier universe, not only finite-dimensional ones. The coefficient-spanning theorem
`TauCeti.Coalgebra.IsLinearlyReductive.iSup_matrixCoefficientSubmodule_eq_top` then says that the
Hopf algebra is spanned by coefficients of its finite-dimensional simple comodules. Each such
comodule is unitarizable by the same averaging theorem. This is the spanning direction of
algebraic Peter–Weyl theory; independence of the simple coefficient spaces is a separate result.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Section 3.2,
  for complete reducibility of unitary comodules and compact-type Hopf star algebras.
-/

public section

open scoped ComplexOrder

namespace LinearMap

universe v w

variable {A : Type v} [Ring A] [StarRing A] [HopfAlgebra ℂ A]
  [StarModule ℂ A] [TauCeti.StarCoalgebra ℂ A] {h : A →ₗ[ℂ] ℂ}

/-- A complex Hopf star algebra with a nonzero positive right invariant integral is linearly
reductive. Normalization of the integral and finite dimension of the algebra are not required. -/
theorem IsRightInvariantIntegral.isLinearlyReductive (hh : h.IsRightInvariantIntegral)
    (h0 : h ≠ 0) (hpos : ∀ a, 0 ≤ h (star a * a)) :
    TauCeti.Coalgebra.IsLinearlyReductive.{0, v, w} ℂ A := by
  apply TauCeti.Coalgebra.IsLinearlyReductive.of_forall_isCompletelyReducible
  intro M _ _ _ _
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨b, hb⟩ := TauCeti.Comodule.exists_basis_coefficientMatrix_mem_unitary hh h0 hpos
    (Module.finBasis ℂ M)
  exact b.isCompletelyReducible_of_coefficientMatrix_mem_unitary hb

end LinearMap
