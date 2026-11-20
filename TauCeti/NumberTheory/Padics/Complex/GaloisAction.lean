/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.IsometricAction
public import TauCeti.NumberTheory.Padics.AlgebraicClosure
public import TauCeti.Topology.Algebra.UniformMulAction

/-!
# The Galois action on `ℂ_p`

Let `K` be a field between `ℚ_p` and its algebraic closure `PadicAlgCl p`, for instance a finite
extension of `ℚ_p` inside `PadicAlgCl p`, and let `G_K = Gal(PadicAlgCl p / K)` carry its Krull
topology. Every element of `G_K` fixes `ℚ_p`, so it preserves the spectral norm of
`PadicAlgCl p` (`AlgEquiv.norm_apply`): `G_K` acts on `PadicAlgCl p` by isometries
(`PadicAlgCl.instIsIsometricSMul`). This file records the consequences for the completion
`ℂ_p = PadicComplex p`, on which `σ ∈ G_K` acts by the extension `UniformSpace.Completion.map σ`
of `σ` by continuity.

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

The theorems below characterize the action: on `PadicAlgCl p` it is `σ` itself
(`PadicComplex.smul_coe`), and `x ↦ σ • x` is the unique continuous extension of `σ` to `ℂ_p`
(`PadicComplex.eq_smul_of_continuous`).

## Main results

* `PadicAlgCl.instIsIsometricSMul`: `G_K` acts on `PadicAlgCl p` by isometries.
* `PadicComplex.smul_coe`: the action on `ℂ_p` extends the action on `PadicAlgCl p`.
* `PadicComplex.eq_smul_of_continuous`: the action of `σ` on `ℂ_p` is the unique continuous
  extension of `σ`.

## References

* O. Brinon and B. Conrad, *CMI summer school notes on p-adic Hodge theory* (2009), §2.1.
* J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois representations*, §4.1.2.
-/

public section

open UniformSpace

variable {p : ℕ} [Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ_[p] K]
  [Algebra K (PadicAlgCl p)] [IsScalarTower ℚ_[p] K (PadicAlgCl p)]

namespace PadicAlgCl

/-- `PadicAlgCl p` is algebraic over every field between `ℚ_p` and `PadicAlgCl p`. -/
instance instIsIntegral : Algebra.IsIntegral K (PadicAlgCl p) :=
  Algebra.IsIntegral.tower_top ℚ_[p]

/-- The `K`-automorphisms of `PadicAlgCl p` are isometries for its spectral norm. -/
instance instIsIsometricSMul : IsIsometricSMul (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (PadicAlgCl p) :=
  ⟨fun σ ↦ AddMonoidHomClass.isometry_of_norm (σ : PadicAlgCl p →+* PadicAlgCl p)
    (AlgEquiv.norm_apply (σ.restrictScalars ℚ_[p]))⟩

end PadicAlgCl

namespace PadicComplex

variable {K}

/-- On the image of `PadicAlgCl p`, the action of `σ` on `ℂ_p` is `σ`. -/
@[simp]
theorem smul_coe (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (x : PadicAlgCl p) :
    σ • (x : ℂ_[p]) = ((σ x : PadicAlgCl p) : ℂ_[p]) := by
  rw [← Completion.coe_smul, AlgEquiv.smul_def]

/-- **Uniqueness of the extended action.** A continuous map `ℂ_p → ℂ_p` that agrees with `σ` on
`PadicAlgCl p` is the action of `σ`. -/
theorem eq_smul_of_continuous (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) {f : ℂ_[p] → ℂ_[p]}
    (hf : Continuous f) (h : ∀ x : PadicAlgCl p, f x = ((σ x : PadicAlgCl p) : ℂ_[p])) :
    f = (σ • ·) :=
  Completion.ext hf (continuous_const_smul σ) fun a ↦ by rw [h, smul_coe]

end PadicComplex
