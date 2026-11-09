/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Kunneth
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
public import TauCeti.AlgebraicTopology.Singular.Sphere

/-!
# Positive-degree singular cohomology of spheres

For every commutative ring `k` and every `k`-module `M`, evaluation on the native standard
homology generator identifies `Hⁿ⁺¹(Sⁿ⁺¹; M)` with `M`. Positive-degree cohomology vanishes
outside the sphere dimension, including for the zero-sphere. No hereditary-ring or
injectivity assumption is needed: the singular homology of a sphere with coefficients in
`k` is free, so the Kronecker map is an isomorphism over any commutative ring.

The equivalence is natural in the coefficient module. Its evaluation formula uses exactly
`TauCeti.reducedSingularHomologyTopCatSphereIso` and the canonical reduced-to-ordinary
inclusion; it does not choose another orientation or generator. In particular its inverse
applied to a nonzero coefficient gives a nonzero top cohomology class.

Since the homology of a sphere is free of finite rank, the Künneth theorem for cohomology applies
to a product with a sphere over every commutative ring and with no hypothesis on the other factor
(`TopCat.singularCohomologyKunneth_sphere_bijective`).

## References

* A. Hatcher, *Algebraic Topology*, Section 3.1 (universal coefficients) and Section 3.2
  (the cohomology of spheres).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology

universe w

namespace TauCeti

variable (k : Type w) [CommRing k] (M : ModuleCat.{w} k)

/-- Evaluation on the standard homology generator identifies the top cohomology of a
positive-dimensional sphere with its coefficient module, over any commutative ring. -/
def singularCohomologyTopCatSphereEquiv (n : ℕ) :
    (TopCat.sphere.{w} (n + 1)).singularCohomology (ModuleCat.of k k) k M (n + 1) ≃ₗ[k] M :=
  ((TopCat.sphere (n + 1)).singularKroneckerEquivOfProjectiveHomology
      (ModuleCat.of k k) M (n + 1)).trans
    ((Linear.homCongr k
      (((reducedSingularHomologySuccIso (ModuleCat.of k k) n).app
        (TopCat.sphere (n + 1))).symm ≪≫
        reducedSingularHomologyTopCatSphereIso (ModuleCat.of k k) (n + 1))
      (Iso.refl M)).trans
        (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf k k M)))

/-- The sphere cohomology equivalence evaluates on the native reduced generator, included
in ordinary homology. -/
@[simp]
lemma singularCohomologyTopCatSphereEquiv_apply (n : ℕ)
    (α : (TopCat.sphere.{w} (n + 1)).singularCohomology (ModuleCat.of k k) k M (n + 1)) :
    singularCohomologyTopCatSphereEquiv k M n α =
      ((TopCat.sphere (n + 1)).singularKronecker k (n + 1) α)
        (((reducedSingularHomologyι (ModuleCat.of k k) (n + 1)).app
          (TopCat.sphere (n + 1)))
          ((reducedSingularHomologyTopCatSphereIso (ModuleCat.of k k) (n + 1)).inv 1)) := by
  simp only [singularCohomologyTopCatSphereEquiv, LinearEquiv.trans_apply,
    TopCat.singularKroneckerEquivOfProjectiveHomology_apply, Linear.homCongr_apply,
    Iso.refl_hom, Category.comp_id, Iso.trans_inv, Iso.symm_inv]
  rw [← reducedSingularHomologySuccIso_hom]
  rw [ModuleCat.homLinearEquiv_apply, LinearMap.ringLmapEquivSelf_apply]
  -- The additive hom equivalence is the underlying linear map; it has no apply lemma.
  rfl

/-- The inverse sphere cohomology equivalence has prescribed evaluation on the native
standard generator. -/
-- Not a simp lemma: the reduced-to-ordinary inclusion simplifies inside the left-hand side.
lemma singularKronecker_singularCohomologyTopCatSphereEquiv_symm (n : ℕ) (m : M) :
    ((TopCat.sphere (n + 1)).singularKronecker k (n + 1)
      ((singularCohomologyTopCatSphereEquiv k M n).symm m))
        (((reducedSingularHomologyι (ModuleCat.of k k) (n + 1)).app
          (TopCat.sphere (n + 1)))
          ((reducedSingularHomologyTopCatSphereIso (ModuleCat.of k k) (n + 1)).inv 1)) = m := by
  rw [← singularCohomologyTopCatSphereEquiv_apply]
  exact (singularCohomologyTopCatSphereEquiv k M n).apply_symm_apply m

/-- Positive-degree singular cohomology of a sphere vanishes away from its dimension,
with arbitrary module coefficients over any commutative ring. -/
theorem isZero_singularCohomology_topCatSphere_of_ne (d q : ℕ) (h : q + 1 ≠ d) :
    IsZero ((TopCat.sphere.{w} d).singularCohomology (ModuleCat.of k k) k M (q + 1)) := by
  have hz := (isZero_reducedSingularHomologyFunctor_topCatSphere_of_ne
    (ModuleCat.of k k) h).of_iso
      ((reducedSingularHomologySuccIso (ModuleCat.of k k) q).app (TopCat.sphere d)).symm
  have : Subsingleton (_ ⟶ M) := ⟨hz.eq_of_src⟩
  have := ((TopCat.sphere d).singularKronecker_bijective_of_projective_homology
    (ModuleCat.of k k) M (q + 1)).1.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- Evaluation on the sphere generator commutes with every coefficient-module map.
The map on cohomology is induced by postcomposition on the actual singular cochains. -/
lemma singularCohomologyTopCatSphereEquiv_naturality {N : ModuleCat.{w} k}
    (g : M ⟶ N) (n : ℕ)
    (α : (TopCat.sphere.{w} (n + 1)).singularCohomology (ModuleCat.of k k) k M (n + 1)) :
    singularCohomologyTopCatSphereEquiv k N n
      (HomologicalComplex.homologyMap
        (((TopCat.toSSet.obj (TopCat.sphere (n + 1))).chainComplex
          (ModuleCat.of k k)).linearYonedaObjMap k g) (n + 1) α) =
      g (singularCohomologyTopCatSphereEquiv k M n α) := by
  rw [singularCohomologyTopCatSphereEquiv_apply,
    singularCohomologyTopCatSphereEquiv_apply,
    TopCat.singularKronecker_coefficient_naturality, ModuleCat.comp_apply]

end TauCeti

namespace TopCat

variable {k : Type w} [CommRing k] (Y : TopCat.{w})

/-- **The cohomology of a product with a sphere**: over every commutative ring `k`, the cohomology
cross product induces an isomorphism `⨁_{p + q = n} Hᵖ(Sᵈ; k) ⊗ H^q(Y; k) ≅ Hⁿ(Sᵈ × Y; k)` for
every space `Y`, since the homology of the sphere is free of finite rank. For `d = 1` and
`k = ℤ` this splits `Hⁿ(S¹ × Y; ℤ)` into the cross products of `H⁰(S¹; ℤ) ≅ ℤ` with `Hⁿ(Y; ℤ)` and
of `H¹(S¹; ℤ) ≅ ℤ` with `Hⁿ⁻¹(Y; ℤ)`, torsion included. -/
theorem singularCohomologyKunneth_sphere_bijective (d n : ℕ) :
    Function.Bijective (singularCohomologyKunneth (TopCat.sphere.{w} d) Y (𝟙_ (ModuleCat.{w} k))
      (𝟙_ (ModuleCat.{w} k)) k (λ_ (𝟙_ (ModuleCat.{w} k))).hom n) :=
  singularCohomologyKunneth_bijective _ Y n fun _ _ ↦ inferInstance

end TopCat
