/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Data.Finsupp.SMul

/-!
# The permutation module of a `G`-set is the permutation representation

A monoid `G` acting on a type `X` acts on the finitely supported functions `X →₀ R` by pushing the
support forward (`Finsupp.comapDistribMulAction`), and that action is `R`-linear
(`TauCeti.comapSMulCommClass`), so `X →₀ R` is a representation of `G` over `R`. It is the
permutation representation `Representation.ofMulAction R G X` on `R[X]`, read through the
coefficient identification `MonoidAlgebra.coeffLinearEquiv`
(`TauCeti.ofDistribMulActionComapEquiv`).

This is the bridge between the two forms a permutation module comes in. The unbundled form — an
additive monoid carrying a `DistribMulAction` — is the form a `G`-module convention asks for, and
the form in which a permutation lattice `ℤ[X] = X →₀ ℤ` is tensored with a ring along its canonical
`ℤ`-module structure; the bundled `Representation.ofMulAction` is the form the representation-theory
API is stated in.

Neither `Finsupp.comapDistribMulAction` nor `TauCeti.comapSMulCommClass` is a global instance: the
first would conflict with the coefficientwise action, and the second is stated for it. A consumer
installs both with `attribute [local instance]`, the way `Mathlib/Data/Finsupp/SMul.lean` states its
own lemmas about the action.

## Main declarations

* `TauCeti.comapSMulCommClass`: pushing the support forward commutes with the coefficientwise
  scalars.
* `TauCeti.ofDistribMulActionComapEquiv`: the permutation module `X →₀ R` is the permutation
  representation `R[X]`.
-/

public section

namespace TauCeti

attribute [local instance] Finsupp.comapSMul Finsupp.comapMulAction Finsupp.comapDistribMulAction

variable {R : Type*} [CommSemiring R] {G : Type*} [Monoid G] {X : Type*} [MulAction G X]

/-- **Pushing the support forward commutes with the coefficientwise scalars.** This is what makes
the permutation module `X →₀ R`, with the action of `Finsupp.comapDistribMulAction`, a
representation of `G` over `R`. Like that action it is not a global instance; a consumer who wants
`Representation.ofDistribMulAction` installs both with `attribute [local instance]`. -/
theorem comapSMulCommClass : SMulCommClass G R (X →₀ R) where
  smul_comm g r f := by
    simp only [Finsupp.comapSMul_def]
    exact Finsupp.mapDomain_smul (f := (g • ·)) r f

attribute [local instance] comapSMulCommClass

variable (R G X)

/-- **The permutation module on a `G`-set is the permutation representation.** The `G`-module
`X →₀ R`, whose action pushes the support forward (`Finsupp.comapDistribMulAction`), is
`Representation.ofMulAction R G X` read through the coefficients: this is the bridge between the
unbundled `DistribMulAction` form of a permutation module and the bundled representation. -/
noncomputable def ofDistribMulActionComapEquiv :
    (_root_.Representation.ofDistribMulAction R G (X →₀ R)).Equiv
      (_root_.Representation.ofMulAction R G X) :=
  _root_.Representation.Equiv.mk (MonoidAlgebra.coeffLinearEquiv R).symm fun g => by
    ext x r
    simp [Finsupp.comapSMul_def]

variable {R X}

/-- `TauCeti.ofDistribMulActionComapEquiv` is the identification of coefficients. -/
@[simp]
theorem ofDistribMulActionComapEquiv_single (x : X) (r : R) :
    ofDistribMulActionComapEquiv R G X (Finsupp.single x r) = MonoidAlgebra.single x r := by
  simp only [ofDistribMulActionComapEquiv, _root_.Representation.Equiv.mk_apply,
    MonoidAlgebra.coeffLinearEquiv_symm_apply, MonoidAlgebra.ofCoeff_single]

/-- `TauCeti.ofDistribMulActionComapEquiv` reads a coefficient back off `R[X]`. -/
@[simp]
theorem ofDistribMulActionComapEquiv_symm_single (x : X) (r : R) :
    (ofDistribMulActionComapEquiv R G X).symm (MonoidAlgebra.single x r) = Finsupp.single x r := by
  rw [← ofDistribMulActionComapEquiv_single (G := G) x r,
    _root_.Representation.Equiv.symm_apply_apply]

end TauCeti

end
