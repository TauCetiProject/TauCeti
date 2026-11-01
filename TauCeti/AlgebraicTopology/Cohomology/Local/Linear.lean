/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Local.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Linear

/-!
# Linear coordinate changes on local cohomology

An invertible real linear map acts on `Hⁿ(E, E ∖ {0}; R, N)` by the sign of its
determinant. Here the chain coefficient module `R` is projective, while the cochain
coefficient module `N` is arbitrary. The formula holds in every degree, including
for a zero-dimensional space.

In particular, orientation-preserving linear changes of coordinates fix every local
cohomology class, whereas orientation-reversing ones negate it. This is the transition
formula needed to compare the local fibre generators of an oriented Thom class.

The proof uses the determinant action on local homology in
`TauCeti.singularHomologyMap_continuousLinearMap_compl_zero` and the relative
Kronecker equivalence in `TauCeti.singularCohomologyComplSingletonKroneckerEquiv`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Section 10 (oriented fibre
  generators of Thom classes).
* A. Hatcher, *Algebraic Topology*, Sections 3.1 and 3.3 (universal coefficients and
  local orientations).
-/

public noncomputable section

open CategoryTheory Module

universe w

namespace TauCeti

variable {k : Type*} [CommRing k] (R N : ModuleCat.{w} k) [Module.Projective k R]
  {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- An invertible real linear map acts on local cohomology at zero by the sign of its
determinant, with arbitrary cochain coefficients and projective chain coefficients. -/
theorem singularCohomologyMap_continuousLinearMap_compl_zero (f : E →L[ℝ] E)
    (hf : Set.MapsTo f ({0}ᶜ : Set E) {0}ᶜ) (n : ℕ) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := N)
        (TopPair.ofSubsetMap (TopCat.ofHom (f : C(E, E))) hf) n =
      (SignType.sign f.det : ℤ) • 𝟙 _ := by
  have hx : (0 : E) ∈ (OpenPartialHomeomorph.refl E).source := by simp
  apply ModuleCat.hom_ext
  ext α
  simp only [ModuleCat.hom_zsmul, LinearMap.smul_apply, ModuleCat.hom_id,
    LinearMap.id_apply]
  apply (singularCohomologyComplSingletonKroneckerEquiv R N
    (OpenPartialHomeomorph.refl E) hx n).injective
  rw [singularCohomologyComplSingletonKroneckerEquiv_apply,
    singularCohomologyComplSingletonKroneckerEquiv_apply]
  rw [TopPair.singularKronecker_naturality,
    singularHomologyMap_continuousLinearMap_compl_zero]
  simp

end TauCeti
