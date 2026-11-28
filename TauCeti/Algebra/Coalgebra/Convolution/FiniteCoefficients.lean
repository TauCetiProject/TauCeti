/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.FiniteDual.Characters
public import Mathlib.LinearAlgebra.Contraction
public import TauCeti.Algebra.WithConv
import TauCeti.Algebra.Coalgebra.Convolution

/-!
# Characters of a convolution algebra after extending coefficients

For a finite projective coalgebra, extending the values of base-valued functionals spans
the entire coefficient-valued convolution algebra. Consequently its characters are determined
by restriction. If the base is integrally closed in the coefficients, every character is
evaluation at a group-like element over the base.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 11.c and Aside 11.17,
  https://www.jmilne.org/math/Books/iAG2017.pdf.
-/

public noncomputable section

open TensorProduct WithConv

namespace TauCeti.ConvolutionDual

variable {R A S : Type*} [CommRing R] [AddCommGroup A] [Module R A] [Coalgebra R A]
  [Module.Finite R A] [Module.Projective R A] [CommRing S] [Algebra R S]

/-- The coefficient extensions of base-valued functionals span the coefficient-valued
convolution algebra. -/
theorem span_range_convPostcomp :
    Submodule.span S (Set.range ((Algebra.ofId R S).convPostcomp (C := A))) = ⊤ := by
  apply top_unique
  intro f _
  obtain ⟨t, ht⟩ := (dualTensorHomEquiv R A S).surjective f.ofConv
  suffices h : toConv (dualTensorHomEquiv R A S t) ∈
      Submodule.span S (Set.range ((Algebra.ofId R S).convPostcomp (C := A))) by
    simpa only [ht, toConv_ofConv] using h
  clear ht
  induction t using TensorProduct.inductionOn with
  | add t u ht hu => simpa using Submodule.add_mem _ ht hu
  | tmul φ s =>
    have h : toConv (dualTensorHomEquiv R A S (φ ⊗ₜ[R] s)) =
        s • (Algebra.ofId R S).convPostcomp (toConv φ) := by
      ext a
      simp only [ofConv_smul, LinearMap.smul_apply, smul_eq_mul]
      simp [Algebra.smul_def, mul_comm]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨toConv φ, rfl⟩)

/-- Characters of a finite-projective convolution algebra are determined by restriction to
base-valued functionals. -/
theorem algHom_ext_convPostcomp {f g : WithConv (A →ₗ[R] S) →ₐ[S] S}
    (h : ∀ φ : ConvolutionDual R A,
      f ((Algebra.ofId R S).convPostcomp φ) = g ((Algebra.ofId R S).convPostcomp φ)) : f = g :=
  AlgHom.toLinearMap_injective <|
    LinearMap.ext_on_range span_range_convPostcomp h

/-- Every coefficient-valued character is evaluation at a unique group-like element of the
base coalgebra if the base is integrally closed in the coefficients. -/
theorem existsUnique_groupLike_algHom_coefficients [IsIntegrallyClosedIn R S]
    (χ : WithConv (A →ₗ[R] S) →ₐ[S] S) :
    ∃! u : GroupLike R A, ∀ f : WithConv (A →ₗ[R] S), χ f = f.ofConv u.val := by
  obtain ⟨u, hu, huniq⟩ := existsUnique_groupLike_algHom R A S
    ((χ.restrictScalars R).comp (Algebra.ofId R S).convPostcomp)
  have heq : χ = evalGroupLike R A u :=
    algHom_ext_convPostcomp fun φ ↦ by simpa using hu φ
  refine ⟨u, fun f ↦ by rw [heq, evalGroupLike_apply], ?_⟩
  intro v hv
  apply huniq v
  intro φ
  simpa using hv ((Algebra.ofId R S).convPostcomp φ)

end TauCeti.ConvolutionDual
