/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.IsometricAction
public import TauCeti.NumberTheory.Padics.AlgebraicClosure.Basic
public import TauCeti.Topology.Algebra.UniformMulAction

/-!
# The Galois action on `ℂ_p`

Let `K` be a field between `ℚ_p` and its algebraic closure `PadicAlgCl p`, for instance a finite
extension of `ℚ_p` inside `PadicAlgCl p`, and let `G_K = Gal(PadicAlgCl p / K)` carry its Krull
topology. Every element of `G_K` fixes `ℚ_p`, so it preserves the spectral norm of
`PadicAlgCl p` (`AlgEquiv.norm_apply`): `G_K` acts on `PadicAlgCl p` by isometries
(`PadicAlgCl.instIsIsometricSMul`, in `TauCeti.NumberTheory.Padics.AlgebraicClosure.Basic`).
This file records the consequences for the completion `ℂ_p = PadicComplex p`, on which
`σ ∈ G_K` acts by the extension `UniformSpace.Completion.map σ` of `σ` by continuity
(`UniformSpace.Completion.algEquiv_smul_def`).

All of the following structure is then inferred from instances.

* `ℂ_p` is a `G_K`-module by ring automorphisms (`MulSemiringAction`) commuting with `ℚ_p`
  (`SMulCommClass`), so `MulSemiringAction.toAlgAut G_K ℚ_[p] ℂ_[p]` is a group homomorphism
  from `G_K` to the `ℚ_p`-algebra automorphisms of `ℂ_p`, and `smul_algebraMap` says that every
  `σ` fixes `ℚ_p`.
* Every `σ` acts by an isometry (`IsIsometricSMul`), so it preserves the norm
  (`IsIsometricSMul.norm_smul`), and the action is faithful (`FaithfulSMul`).
* The action map `G_K × ℂ_p → ℂ_p` is jointly continuous (`ContinuousSMul`), by
  `AlgEquiv.continuousSMul_of_isIsometricSMul` on `PadicAlgCl p` and
  `UniformSpace.Completion.continuousSMul_of_isIsometricSMul` on its completion. Continuity of
  each map `x ↦ σ • x` alone does not give this; it uses the isometries together with the
  openness of the stabilizer of each algebraic element.

The general completion lemmas characterize the action: on `PadicAlgCl p` it is `σ` itself
(`UniformSpace.Completion.algEquiv_smul_coe`), and `x ↦ σ • x` is the unique continuous extension
of `σ` to `ℂ_p` (`UniformSpace.Completion.eq_smul_of_continuous`). This file states nothing
further; importing it makes the whole structure above available on `ℂ_p`.

## Main results

* `UniformSpace.Completion.algEquiv_smul_def`: `σ` acts on `ℂ_p` by
  `UniformSpace.Completion.map σ`.
* `UniformSpace.Completion.algEquiv_smul_coe`: the action on `ℂ_p` extends the action on
  `PadicAlgCl p`.
* `UniformSpace.Completion.eq_smul_of_continuous`: the action of `σ` on `ℂ_p` is the unique
  continuous extension of `σ`.

## References

* O. Brinon and B. Conrad, *CMI summer school notes on p-adic Hodge theory* (2009), §2.1.
* J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois representations*, §4.1.2.
-/
