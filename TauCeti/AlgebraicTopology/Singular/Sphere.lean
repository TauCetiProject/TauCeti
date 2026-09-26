/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Reduced
public import TauCeti.AlgebraicTopology.Sphere.Equator
public import TauCeti.AlgebraicTopology.Sphere.Puncture

/-!
# The Mayer–Vietoris sequence of a sphere

For a point `p` of the unit sphere `S` of a real normed space, the complements of `p` and of `-p`
form an open cover of `S` by two contractible sets whose intersection is `S ∖ {p, -p}`. The
reduced Mayer–Vietoris connecting morphism of this cover is therefore an isomorphism
`Hₖ₊₁(S) ≅ H_redₖ(S ∖ {p, -p})` in every degree. In a real inner product space, `S ∖ {p, -p}` is
homotopy equivalent to the unit sphere of the orthogonal complement `(ℝ ∙ p)ᗮ`, and composing
gives the isomorphism `H_redₖ₊₁(S) ≅ H_redₖ(S ∩ (ℝ ∙ p)ᗮ)`, lowering both the sphere's dimension
and the degree.

Coefficients are an object `R` of an abelian category with coproducts.

## Main definitions and results

* `TauCeti.isIso_reducedMayerVietorisδ_sphere`: the reduced Mayer–Vietoris connecting morphism
  `Hₖ₊₁(S) ⟶ H_redₖ(S ∖ {p, -p})` of the cover of `S` by the complements of `p` and `-p` is an
  isomorphism.
* `TauCeti.reducedSingularHomologySphereSuccIso`: the isomorphism
  `H_redₖ₊₁(S) ≅ H_redₖ(S ∩ (ℝ ∙ p)ᗮ)`, given by that connecting morphism followed by the homotopy
  equivalence of `S ∖ {p, -p}` with the equator.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2: the reduced Mayer–Vietoris sequence of a cover of
  `Sⁿ` by two neighbourhoods of its hemispheres, here the complements of two antipodal points.
-/

public section

noncomputable section

open CategoryTheory Limits Metric

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

section Normed

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] (p : sphere (0 : E) 1)

/-- **The Mayer–Vietoris isomorphism of a sphere.** The reduced Mayer–Vietoris connecting
morphism `Hₖ₊₁(S) ⟶ H_redₖ(S ∖ {p, -p})` of the cover of the unit sphere `S` by the complements of
`p` and `-p` is an isomorphism in every degree, since both complements are contractible. -/
theorem isIso_reducedMayerVietorisδ_sphere (k : ℕ) :
    IsIso (TopCat.reducedMayerVietorisδ R (X := TopCat.of (sphere (0 : E) 1))
      isOpen_compl_singleton isOpen_compl_singleton
      (compl_singleton_union_compl_singleton_neg p) k) :=
  have := contractibleSpace_sphere_compl_singleton p
  have := contractibleSpace_sphere_compl_singleton (-p)
  inferInstance

end Normed

variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : sphere (0 : E) 1)

-- `reducedSingularHomologySuccIso` targets `singularHomologyFunctor`, while the
-- Mayer–Vietoris connecting morphism starts at `TopCat.toSSet` homology. Ordinary
-- singular homology is defined using `TopCat.toSSet`, so these objects are definitionally equal.
private abbrev singularHomologyFunctor_obj_eq_toSSetHomology (n : ℕ) (X : TopCat.{w}) :
    ((AlgebraicTopology.singularHomologyFunctor C n).obj R).obj X =
      (TopCat.toSSet.obj X).homology R n := rfl

private lemma singularHomologyFunctor_obj_eq_toSSetHomology_hom_comp
    (n : ℕ) (X : TopCat.{w}) {Y : C}
    (f : (TopCat.toSSet.obj X).homology R n ⟶ Y) :
    (eqToIso (singularHomologyFunctor_obj_eq_toSSetHomology R n X)).hom ≫ f = f := by
  -- The equality above is `rfl`, so its `eqToIso` is the identity after reduction.
  change 𝟙 _ ≫ f = f
  exact Category.id_comp f

/-- **The suspension isomorphism for the homology of spheres.** For a point `p` of the unit
sphere `S` of a real inner product space `E`, the reduced homology of `S` in degree `k + 1` is
isomorphic to the reduced homology in degree `k` of the equator, the unit sphere of
`(ℝ ∙ p)ᗮ`. It is the Mayer–Vietoris connecting morphism of the cover of `S` by the complements of
`p` and `-p`, followed by the homotopy equivalence `TauCeti.equatorHomotopyEquiv` of
`S ∖ {p, -p}` with the equator. -/
def reducedSingularHomologySphereSuccIso (k : ℕ) :
    (reducedSingularHomologyFunctor R (k + 1)).obj (TopCat.of (sphere (0 : E) 1)) ≅
      (reducedSingularHomologyFunctor R k).obj (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)) :=
  -- `TauCeti.isIso_reducedMayerVietorisδ_sphere` is a theorem rather than an instance, so it is
  -- supplied to `asIso` explicitly.
  (reducedSingularHomologySuccIso R k).app _ ≪≫
    eqToIso (singularHomologyFunctor_obj_eq_toSSetHomology R (k + 1) _) ≪≫
    @asIso _ _ _ _ (TopCat.reducedMayerVietorisδ R (X := TopCat.of (sphere (0 : E) 1))
      isOpen_compl_singleton isOpen_compl_singleton
      (compl_singleton_union_compl_singleton_neg p) k)
      (isIso_reducedMayerVietorisδ_sphere R p k) ≪≫
    (equatorHomotopyEquiv p).reducedSingularHomologyIso R k

/-- The suspension isomorphism is the identification of reduced with ordinary homology in positive
degrees, followed by the reduced Mayer–Vietoris connecting morphism of the cover by the complements
of `p` and `-p`, and by the map induced by radial projection of the orthogonal projection onto
`(ℝ ∙ p)ᗮ`. -/
@[simp]
lemma reducedSingularHomologySphereSuccIso_hom (k : ℕ) :
    (reducedSingularHomologySphereSuccIso R p k).hom =
      (reducedSingularHomologyι R (k + 1)).app _ ≫
        TopCat.reducedMayerVietorisδ R (X := TopCat.of (sphere (0 : E) 1))
          isOpen_compl_singleton isOpen_compl_singleton
          (compl_singleton_union_compl_singleton_neg p) k ≫
        (reducedSingularHomologyFunctor R k).map (TopCat.ofHom (equatorHomotopyEquiv p).toFun) := by
  simp only [reducedSingularHomologySphereSuccIso, Iso.trans_hom, Iso.app_hom,
    reducedSingularHomologySuccIso_hom, ContinuousMap.HomotopyEquiv.reducedSingularHomologyIso_hom]
  simp only [singularHomologyFunctor_obj_eq_toSSetHomology_hom_comp, asIso_hom]
  -- Both remaining compositions use the same `toSSet` homology object definitionally.
  rfl

end TauCeti
