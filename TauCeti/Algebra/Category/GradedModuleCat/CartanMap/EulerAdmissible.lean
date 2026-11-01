/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ProjectiveDimension
public import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.MinimalResolution
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.FiniteLength

/-!
# Graded Euler-admissibility and the graded Cartan isomorphism

Let `A` be a finite-dimensional algebra over a field `k`, nonnegatively graded with semisimple
degree-zero part, and let `S` be an exhaustive family of graded simples up to internal shift,
indexed by a finite type. If every pair `(Sᵢ, Sⱼ)` is graded Euler-admissible, then every finite
graded module has finite projective dimension, so it has a finite resolution by finite graded
projectives. Admissibility of `(M, Sⱼ)` gives a cohomological bound on `Extⁿ(M, Sⱼ{d})` that is
uniform in the internal degree `d`, and every finite simple graded module is some `Sⱼ{d}`; hence
`Extⁿ(M, -)` vanishes on all finite simples from some degree on, and this bounds the projective
dimension of `M`
(`TauCeti.GradedProjectiveResolution.hasProjectiveDimensionLT_of_subsingleton_ext_simple`).

Consequently the graded Cartan map is an isomorphism of `ℤ[q,q⁻¹]`-modules, and the graded Cartan
matrix in any projective and module bases indexed by the same finite type has unit determinant.
Nothing is assumed about the field splitting the simple modules, so this applies to the bases
`TauCeti.gradedIdempotentProjectiveBasisOfPrimitive` and
`TauCeti.gradedIdempotentHeadBasisOfPrimitive` of a family of primitive idempotents
(`TauCeti.isUnit_det_gradedCartanMatrix_gradedIdempotentProjectiveBasisOfPrimitive`).

Admissibility of the simples is a genuine hypothesis: for the dual numbers `k[ε]/(ε²)` with `ε` in
degree two, the graded Cartan matrix is `[1 + q²]`, whose determinant is not a unit of
`ℤ[q,q⁻¹]`.

## Main results

* `TauCeti.gradedFiniteModules_le_admitsFiniteResolution_of_isGradedEulerAdmissible`: every
  finite graded module has a finite resolution by finite graded projectives.
* `TauCeti.gradedCartanMap_bijective_of_isGradedEulerAdmissible`: the graded Cartan map is
  bijective.
* `TauCeti.isUnit_det_gradedCartanMatrix_of_isGradedEulerAdmissible`: graded Cartan
  unimodularity in any two bases indexed by the same finite type.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 4.1, for projective
  dimension, and *The K-book*, Chapter II, Theorem 7.6, for the resolution theorem.
* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Section 1.2, for minimal resolutions over a positively graded ring with semisimple degree-zero
  part.
* Z. Dancso and A. Licata, "Koszul algebras and flow lattices", Section 2.2, for the graded
  Cartan matrix over `ℤ[q,q⁻¹]`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian

universe w uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [IsSemisimpleRing (𝒜 0)]
  [HasExt.{w} (GradedModuleCat.{uA} 𝒜)] (hneg : ∀ p < 0, 𝒜 p = ⊥)
  {I : Type uI} [Finite I] {S : I → (gradedFiniteModules 𝒜).FullSubcategory}
  (hS : IsExhaustiveGradedSimpleFamily S)
  (h : ∀ i j, IsGradedEulerAdmissible.{w} k (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj)

include hneg hS h in
/-- **Euler-admissible simples force finite resolutions.** Over a finite-dimensional
nonnegatively graded algebra with semisimple degree-zero part, if every pair of members of an
exhaustive family of graded simples is graded Euler-admissible, then every finite graded module
has a finite resolution by finite graded projectives. -/
theorem gradedFiniteModules_le_admitsFiniteResolution_of_isGradedEulerAdmissible :
    gradedFiniteModules 𝒜 ≤ (gradedModuleCanonicalExactStructure 𝒜).admitsFiniteResolution
      (gradedFiniteProjectiveModules 𝒜) := by
  have : IsNoetherianRing A := isNoetherian_of_tower k inferInstance
  refine gradedFiniteModules_le_admitsFiniteResolution_of_finite_projectiveDimension
    fun M hMA ↦ ?_
  have : Module.Finite k M := Module.Finite.trans A M
  have hM : gradedFiniteModules 𝒜 M := gradedFiniteModules_iff.2 hMA
  -- One cohomological bound for `M` against the finitely many `Sⱼ`, uniform in the shift.
  obtain ⟨d, hd⟩ := exists_forall_isGradedExtBoundedBy fun j ↦
    (((isGradedEulerAdmissibleOn_gradedFiniteModules_iff hS).2 h).isGradedEulerAdmissible
      hM (S j).property).bounded
  have : HasProjectiveDimensionLT (GradedModuleCat.toModuleCat.obj M) d :=
    GradedProjectiveResolution.hasProjectiveDimensionLT_of_subsingleton_ext_simple hneg M d
      fun n hn N _ hN ↦ by
        -- A finite simple `N` is a shift `Sⱼ{e}`, against which `Extⁿ(M, -)` vanishes.
        obtain ⟨j, e, ⟨φ⟩⟩ := (isExhaustiveGradedSimpleFamily_iff S).1 hS
          ⟨N, gradedFiniteModules_iff.2 (Module.Finite.of_restrictScalars_finite k A N)⟩ hN
        have := (hd j).subsingleton hn e
        exact (extAddEquivOfIso (Iso.refl M)
          (φ ≪≫ ((GradedModuleCat.shiftPowIso 𝒜 e).app (S j).obj).symm) n).toEquiv.subsingleton
  exact ⟨d, hasProjectiveDimensionLT_of_ge _ d (d + 1) d.le_succ⟩

include hneg hS h in
/-- **The graded Cartan map is an isomorphism when the simples are Euler-admissible.** Over a
finite-dimensional nonnegatively graded algebra with semisimple degree-zero part, if every pair of
members of an exhaustive family of graded simples is graded Euler-admissible, then the graded
Cartan map `K₀^gr(proj A) ⟶ G₀^gr(mod A)` is bijective. -/
theorem gradedCartanMap_bijective_of_isGradedEulerAdmissible :
    Function.Bijective (gradedCartanMap 𝒜) :=
  gradedCartanMap_bijective 𝒜
    (gradedFiniteModules_le_admitsFiniteResolution_of_isGradedEulerAdmissible hneg hS h)

include hneg hS h in
/-- **Graded Cartan unimodularity from Euler-admissible simples.** Over a finite-dimensional
nonnegatively graded algebra with semisimple degree-zero part, if every pair of members of an
exhaustive family of graded simples is graded Euler-admissible, then the graded Cartan matrix in a
projective basis and a module basis indexed by the same finite type has determinant a unit of
`ℤ[q,q⁻¹]`. No splitting hypothesis on the field is needed. -/
theorem isUnit_det_gradedCartanMatrix_of_isGradedEulerAdmissible {J : Type*} [Fintype J]
    [DecidableEq J]
    (bP : Module.Basis J (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (bM : Module.Basis J (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜))) :
    IsUnit (gradedCartanMatrix 𝒜 bP bM).det :=
  isUnit_det_gradedCartanMatrix_of_le_admitsFiniteResolution 𝒜
    (gradedFiniteModules_le_admitsFiniteResolution_of_isGradedEulerAdmissible hneg hS h) bP bM

end TauCeti
