/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.StableLocus.Basic
public import TauCeti.AlgebraicGeometry.Grassmannian.Projective
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver.Coproduct

/-!
# Projectivity of finite coproducts of stable Grassmannians

For a finite module over a commutative ring, the closed locus of submodules preserved by an
endomorphism is projective over the coefficient ring. So is the scheme coproduct for any finite
family of quotient ranks. In particular this applies to all ranks from zero to the rank of a
finite free ambient module, as needed for finite charts parametrizing stable projective
quotients whose rank may vary between connected components of the test scheme.

The schemes here are the native stable loci, retaining their possible nilpotents. Their
embeddings are the stable-locus inclusions followed by the Plücker embeddings and the
identification of the rank-one Grassmannian with the projective spectrum of a symmetric algebra.

## References

* X. Zhu, *An introduction to affine Grassmannians and the geometric Satake equivalence*,
  §1.1, for stable Grassmannians in finite lattice charts.
-/

public section

universe u v

open CategoryTheory Limits AlgebraicGeometry TauCeti.SymmetricAlgebra

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

/-- The stable locus in the quotient Grassmannian is projective over the coefficient ring
when its Plücker coordinate module is finite. Finiteness of the ambient module suffices. -/
theorem isProjectiveOver_schemeStableLocus (r : ℕ) (t : Module.End R M)
    [Module.Finite R (⋀[R]^r M)] :
    (schemeStableLocus r t).subscheme.IsProjectiveOver R :=
  Scheme.IsProjectiveOver.of_isClosedImmersion R (schemeStableLocus r t).subschemeι

/-- A finite scheme coproduct of stable Grassmannians is projective over `Spec R`, for any
finite family of quotient ranks with finite Plücker coordinate modules. Its structure map
is induced by the native structure maps. Repeated ranks retain separate summands. -/
theorem isProjectiveOver_sigma_schemeStableLocus {ι : Type v} [Finite ι]
    (r : ι → ℕ) (t : Module.End R M) [∀ i, Module.Finite R (⋀[R]^(r i) M)] :
    (∐ fun i ↦ (schemeStableLocus (r i) t).subscheme).IsProjectiveOver R := by
  have : ∀ i, (schemeStableLocus (r i) t).subscheme.IsProjectiveOver R :=
    fun i ↦ isProjectiveOver_schemeStableLocus (r i) t
  exact Scheme.IsProjectiveOver.sigma R _

end Module.Grassmannian
