/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Reduced
public import TauCeti.AlgebraicTopology.Sphere.Equator
public import TauCeti.AlgebraicTopology.Sphere.Puncture
public import TauCeti.AlgebraicTopology.Sphere.Zero
public import Mathlib.Analysis.InnerProductSpace.Orientation
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.Analysis.InnerProductSpace.LinearIsometry
public import TauCeti.Analysis.InnerProductSpace.OrthogonalLast
public import TauCeti.Geometry.Sphere.LinearIsometry

/-!
# The homology of spheres

For a point `p` of the unit sphere `S` of a real normed space, the complements of `p` and of `-p`
form an open cover of `S` by two contractible sets whose intersection is `S ∖ {p, -p}`. The
reduced Mayer–Vietoris connecting morphism of this cover is therefore an isomorphism
`Hₖ₊₁(S) ≅ H_redₖ(S ∖ {p, -p})` in every degree. In a real inner product space, `S ∖ {p, -p}` is
homotopy equivalent to the unit sphere of the orthogonal complement `(ℝ ∙ p)ᗮ`, and composing
gives the isomorphism `H_redₖ₊₁(S) ≅ H_redₖ(S ∩ (ℝ ∙ p)ᗮ)`, lowering both the sphere's dimension
and the degree.

Iterating this suspension isomorphism down to the zero-sphere, whose reduced homology is one copy
of the coefficient object in degree zero and vanishes above, computes the reduced homology of the
unit sphere of an `(n + 1)`-dimensional real inner product space: it is one copy of the
coefficient object in degree `n` and vanishes in every other degree.

The identification with the coefficient object, that is, the generator of `H_redₙ(Sⁿ)`, is
determined by an orthonormal basis `b` indexed by `Fin (n + 1)`: the suspension isomorphisms are
taken at the last basis vector, then at the last remaining one on the equator, and so on, down to
the zero-sphere `{b 0, -b 0}` with generator `[-b 0] - [b 0]`.  The suspension isomorphism is
natural under linear isometries carrying one pole to the other, so a linear isometry carrying the
basis `b` to a basis `c` carries the generator determined by `b` to the generator determined by
`c`.

The generator depends on `b` only through its orientation.  A linear isometry negating `b 0` and
fixing the other basis vectors fixes the last one, so it commutes with the suspension isomorphisms
and acts by `-1`, as it swaps the two points of the zero-sphere `{b 0, -b 0}`.  Every reflection
has this form for a suitable basis, so it acts by `-1` on `H_redₙ(S)`; by the Cartan–Dieudonné
theorem every linear isometry is a product of reflections, so it acts by the sign of its
determinant.  Applied to the isometry carrying one orthonormal basis to another, this shows that
bases of the same orientation determine the same generator and bases of opposite orientations
determine opposite generators.  In particular the antipodal map acts by `(-1) ^ (n + 1)`.

Mathlib's `TopCat.sphere n` is the universe lift of the unit sphere of
`EuclideanSpace ℝ (Fin (n + 1))`; through `TauCeti.diskBoundaryHomeomorph` it is homeomorphic to
the unit sphere of a Euclidean space of the same dimension in the lifted universe, so the same
computation applies to it, and the standard basis of that space gives its standard generator.

For the unit circle `S` of a two-dimensional real inner product space, the explicit form of the
Mayer–Vietoris sequence is recorded directly: the cover is by the two open arcs `S ∖ {p}` and
`S ∖ {-p}`, whose intersection `S ∖ {p, -p}` consists of two open arcs, the path components of any
of its points `x` and of `-x`.  The connecting morphism `H₁(S) ⟶ H₀(S ∖ {p, -p})` identifies
`H₁(S)` with one copy of the coefficient object and sends the resulting generator to `[-x] - [x]`.

Coefficients are an object `R` of an abelian category with coproducts.

## Main definitions and results

* `TauCeti.isZero_reducedSingularHomologyFunctor_sphere_compl_singleton`: the unit sphere minus a
  point is acyclic.
* `TauCeti.isIso_reducedMayerVietorisδ_sphere`: the reduced Mayer–Vietoris connecting morphism
  `Hₖ₊₁(S) ⟶ H_redₖ(S ∖ {p, -p})` of the cover of `S` by the complements of `p` and `-p` is an
  isomorphism.
* `TauCeti.reducedSingularHomologySphereSuccIso`: the isomorphism
  `H_redₖ₊₁(S) ≅ H_redₖ(S ∩ (ℝ ∙ p)ᗮ)`, given by that connecting morphism followed by the homotopy
  equivalence of `S ∖ {p, -p}` with the equator, and
  `TauCeti.reducedSingularHomologySphereSuccIso_hom_naturality`: its naturality under linear
  isometries.
* `TauCeti.reducedSingularHomologySphereIsoOfFinrankEq`: the unit spheres of two
  finite-dimensional real normed spaces of the same dimension have isomorphic reduced homology,
  which transports the computations below from inner product spaces to normed spaces.
* `TauCeti.reducedSingularHomologySphereZeroIso`: `H_red₀(S) ≅ R` for the zero-sphere, with
  generator `[-p] - [p]`.
* `TauCeti.singularHomologySphereOneIso` and
  `TauCeti.singularHomologySphereOneIso_inv_mayerVietorisδ`: `H₁(S) ≅ R` for the circle, whose
  generator the Mayer–Vietoris connecting morphism of the cover by `S ∖ {p}` and `S ∖ {-p}` sends
  to `[-x] - [x]` in the zeroth homology of `S ∖ {p, -p}`.
* `TauCeti.isZero_reducedSingularHomologyFunctor_sphere_of_ne`: for `finrank ℝ E = n + 1`, the
  reduced homology of the unit sphere of `E` vanishes in degrees `k ≠ n`.
* `TauCeti.reducedSingularHomologySphereIso`: the isomorphism `H_redₙ(S) ≅ R` determined by an
  orthonormal basis of `E` indexed by `Fin (n + 1)`, with the recursion
  `TauCeti.reducedSingularHomologySphereIso_succ` and the degree-zero generator
  `TauCeti.reducedSingularHomologySphereIso_inv_ι`.
* `TauCeti.reducedSingularHomologySphereIso_hom_naturality`: a linear isometry matching two
  orthonormal bases carries the generator determined by one to the generator determined by the
  other.
* `TauCeti.reducedSingularHomologyFunctor_map_reflection_unitSphereMap` and
  `TauCeti.reducedSingularHomologyFunctor_map_unitSphereMap`: a reflection acts on `H_redₙ(S)` by
  `-1`, and a linear isometry by the sign of its determinant.
* `TauCeti.reducedSingularHomologySphereIso_hom_eq_sign_det_smul`,
  `TauCeti.reducedSingularHomologySphereIso_eq_of_orientation_eq` and
  `TauCeti.reducedSingularHomologySphereIso_hom_eq_neg_of_orientation_ne`: the generator determined
  by an orthonormal basis depends only on its orientation, and reversing the orientation negates
  it.
* `TauCeti.reducedSingularHomologyFunctor_map_sphere_neg`: the antipodal map acts on `H_redₙ(S)`
  by `(-1) ^ (n + 1)`.
* `TauCeti.isZero_reducedSingularHomologyFunctor_topCatSphere_of_ne` and
  `TauCeti.reducedSingularHomologyTopCatSphereIso`: the same for Mathlib's `TopCat.sphere n`, with
  the standard generator determined by the standard basis.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, Example 2.46: the reduced Mayer–Vietoris sequence
  of a cover of `Sⁿ` by two contractible open sets meeting in a space homotopy equivalent to
  `Sⁿ⁻¹`, there neighbourhoods of the two hemispheres and here the complements of two antipodal
  points, and the resulting induction on dimension.  The computed groups are those of Section 2.1,
  Corollary 2.14.
* A. Hatcher, *Algebraic Topology*, Section 2.2, properties (e) and (f) of degree: a reflection of
  `Sⁿ` has degree `-1`, and the antipodal map has degree `(-1) ^ (n + 1)`.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Module

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

/-- **The unit sphere minus a point is acyclic.** For a point `p` of the unit sphere of a real
normed space, the reduced homology of the complement of `p` vanishes in every degree, since that
complement is contractible. -/
theorem isZero_reducedSingularHomologyFunctor_sphere_compl_singleton (k : ℕ) :
    IsZero ((reducedSingularHomologyFunctor R k).obj
      (TopCat.of ↥({p}ᶜ : Set (sphere (0 : E) 1)))) :=
  have := contractibleSpace_sphere_compl_singleton p
  isZero_reducedSingularHomologyFunctor_of_contractibleSpace R _ k

/-- **Reduced homology of the zero-sphere.**  For a point `p` of the unit sphere of a
one-dimensional real normed space, the reduced homology of the sphere in degree zero is one copy
of the coefficient object, generated by the class `[-p] - [p]`
(`TauCeti.reducedSingularHomologySphereZeroIso_inv_ι`). -/
def reducedSingularHomologySphereZeroIso (h : finrank ℝ E = 1) (p : sphere (0 : E) 1) :
    (reducedSingularHomologyFunctor R 0).obj (TopCat.of (sphere (0 : E) 1)) ≅ R :=
  haveI := zerothHomotopySphereUnique h p
  reducedSingularHomology₀Iso R (X := TopCat.of (sphere (0 : E) 1)) p ≪≫ coproductUniqueIso _

/-- The generator of the reduced homology of the zero-sphere `{p, -p}` is the class
`[-p] - [p]`. -/
-- Not a simp lemma: `reducedSingularHomologyι_zero_app` rewrites the degree-zero inclusion
-- inside the left-hand side first, so this would fail the `simpNF` linter.
@[reassoc]
lemma reducedSingularHomologySphereZeroIso_inv_ι (h : finrank ℝ E = 1) (p : sphere (0 : E) 1) :
    (reducedSingularHomologySphereZeroIso R h p).inv ≫
        (reducedSingularHomologyι R 0).app (TopCat.of (sphere (0 : E) 1)) =
      singularHomology₀Section R (X := TopCat.of (sphere (0 : E) 1)) (-p) -
        singularHomology₀Section R (X := TopCat.of (sphere (0 : E) 1)) p := by
  have := zerothHomotopySphereUnique h p
  simp only [reducedSingularHomologySphereZeroIso, Iso.trans_inv, Category.assoc,
    coproductUniqueIso_inv, zerothHomotopySphereUnique_default]
  exact ι_reducedSingularHomology₀Iso_inv_ι R (X := TopCat.of (sphere (0 : E) 1)) p (-p) _

/-- The unit spheres of two finite-dimensional real normed spaces of the same dimension have
isomorphic reduced homology, through the homeomorphism `TauCeti.sphereHomeomorphOfFinrankEq`.
This transports the computations of this file from inner product spaces to normed spaces. -/
def reducedSingularHomologySphereIsoOfFinrankEq [FiniteDimensional ℝ E] {F : Type w}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hEF : finrank ℝ E = finrank ℝ F) (k : ℕ) :
    (reducedSingularHomologyFunctor R k).obj (TopCat.of (sphere (0 : E) 1)) ≅
      (reducedSingularHomologyFunctor R k).obj (TopCat.of (sphere (0 : F) 1)) :=
  (reducedSingularHomologyFunctor R k).mapIso (TopCat.isoOfHomeo (sphereHomeomorphOfFinrankEq hEF))

/-- `TauCeti.reducedSingularHomologySphereIsoOfFinrankEq` is the map induced by
`TauCeti.sphereHomeomorphOfFinrankEq`. -/
@[simp]
lemma reducedSingularHomologySphereIsoOfFinrankEq_hom [FiniteDimensional ℝ E] {F : Type w}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hEF : finrank ℝ E = finrank ℝ F) (k : ℕ) :
    (reducedSingularHomologySphereIsoOfFinrankEq R hEF k).hom =
      (reducedSingularHomologyFunctor R k).map
        (TopCat.ofHom (sphereHomeomorphOfFinrankEq hEF : C(sphere (0 : E) 1, sphere (0 : F) 1))) :=
  (rfl)

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

/-- **Naturality of the suspension isomorphism under linear isometries.** A linear isometry
`f : E →ₗᵢ[ℝ] F` sending the pole `p` to the pole `q` intertwines the suspension isomorphisms at
`p` and at `q`, where the equators are related by the restriction
`f.orthogonalComplementSingletonMap` of `f` to the orthogonal complements of the poles. -/
@[reassoc]
lemma reducedSingularHomologySphereSuccIso_hom_naturality {F : Type w} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (f : E →ₗᵢ[ℝ] F) (q : sphere (0 : F) 1) (hpq : f p = q) (k : ℕ) :
    (reducedSingularHomologyFunctor R (k + 1)).map
          (TopCat.ofHom ⟨f.unitSphereMap, f.continuous_unitSphereMap⟩) ≫
        (reducedSingularHomologySphereSuccIso R q k).hom =
      (reducedSingularHomologySphereSuccIso R p k).hom ≫
        (reducedSingularHomologyFunctor R k).map
          (TopCat.ofHom ⟨(f.orthogonalComplementSingletonMap hpq).unitSphereMap,
            (f.orthogonalComplementSingletonMap hpq).continuous_unitSphereMap⟩) := by
  let g : TopCat.of (sphere (0 : E) 1) ⟶ TopCat.of (sphere (0 : F) 1) :=
    TopCat.ofHom ⟨f.unitSphereMap, f.continuous_unitSphereMap⟩
  have hg : Function.Injective g := fun x y h ↦
    Subtype.ext (f.injective (by simpa [g] using congrArg Subtype.val h))
  have hU : Set.MapsTo g ({p}ᶜ : Set (sphere (0 : E) 1)) {q}ᶜ :=
    fun x hx hgx ↦ hx (hg (hgx.trans (Subtype.ext (by simp [g, hpq])).symm))
  have hV : Set.MapsTo g ({-p}ᶜ : Set (sphere (0 : E) 1)) {-q}ᶜ :=
    fun x hx hgx ↦ hx (hg (hgx.trans (Subtype.ext (by simp [g, hpq]))))
  simp only [reducedSingularHomologySphereSuccIso_hom, Category.assoc]
  -- The inclusion of reduced homology, the Mayer–Vietoris connecting morphism and the radial
  -- projection onto the equator are each natural for `g`.  The first two squares are stated with
  -- ordinary homology in its `toSSet` form, the source of the connecting morphism.
  have hι : (reducedSingularHomologyFunctor R (k + 1)).map g ≫
      (reducedSingularHomologyι R (k + 1)).app (TopCat.of (sphere (0 : F) 1)) =
      (reducedSingularHomologyι R (k + 1)).app (TopCat.of (sphere (0 : E) 1)) ≫
        SSet.homologyMap (TopCat.toSSet.map g) R (k + 1) :=
    (reducedSingularHomologyι R (k + 1)).naturality g
  have hδ := TopCat.reducedMayerVietorisδ_naturality R (X := TopCat.of (sphere (0 : E) 1))
    isOpen_compl_singleton isOpen_compl_singleton (compl_singleton_union_compl_singleton_neg p)
    isOpen_compl_singleton isOpen_compl_singleton (compl_singleton_union_compl_singleton_neg q)
    g hU hV k
  have hE : (reducedSingularHomologyFunctor R k).map (TopCat.ofHom ⟨(hU.inter_inter hV).restrict,
        g.hom.continuous.restrict (hU.inter_inter hV)⟩) ≫
        (reducedSingularHomologyFunctor R k).map (TopCat.ofHom (equatorHomotopyEquiv q).toFun) =
      (reducedSingularHomologyFunctor R k).map (TopCat.ofHom (equatorHomotopyEquiv p).toFun) ≫
        (reducedSingularHomologyFunctor R k).map
          (TopCat.ofHom ⟨(f.orthogonalComplementSingletonMap hpq).unitSphereMap,
            (f.orthogonalComplementSingletonMap hpq).continuous_unitSphereMap⟩) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext x
    -- The orthogonal projection away from a unit vector, and normalization, commute with `f`.
    simp only [TopCat.hom_ofHom, ContinuousMap.coe_mk, TopCat.hom_comp, ConcreteCategory.hom_ofHom,
      ContinuousMap.comp_apply, coe_equatorHomotopyEquiv_apply, NormedSpace.normalize, ← hpq,
      Set.MapsTo.val_restrict_apply, LinearIsometry.coe_unitSphereMap_apply,
      Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton,
      LinearIsometry.inner_map_map, LinearIsometry.norm_map, norm_eq_of_mem_sphere, one_pow,
      RCLike.ofReal_real_eq_id, id_eq, div_one,
      LinearIsometry.coe_orthogonalComplementSingletonMap_apply, map_smul, map_sub, g]
    rw [← f.map_smul, ← f.map_sub, f.norm_map]
  -- The composites are chained as terms: rewriting would have to match ordinary homology in its
  -- two definitionally equal forms, `singularHomologyFunctor` and `toSSet` homology.
  refine ((Category.assoc _ _ _).symm.trans ((hι =≫ _).trans (Category.assoc _ _ _))).trans ?_
  refine (congrArg (fun t ↦ _ ≫ t) ((reassoc_of% hδ) _).symm).trans ?_
  rw [hE]
  exact congrArg (fun t ↦ _ ≫ t) (Category.assoc _ _ _).symm

section Circle

variable {p} (hE : finrank ℝ E = 2) {x : sphere (0 : E) 1}
  (hx : x ∈ ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)))

/-- On the unit circle minus `p` and `-p`, the path component of `-x` is the unique path
component other than that of `x`. -/
@[instance_reducible]
private def zerothHomotopyComplUnique :
    Unique {c : ZerothHomotopy ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)) //
      c ≠ ZerothHomotopy.mk ⟨x, hx⟩} where
  default := ⟨_, zerothHomotopy_mk_neg_ne_of_finrank_eq_two hE hx⟩
  uniq := by
    rintro ⟨c, hc⟩
    obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective c
    exact Subtype.ext ((zerothHomotopy_mk_eq_or_eq_neg_of_finrank_eq_two hE hx y).resolve_left hc)

/-- **The first homology of a circle through its Mayer–Vietoris sequence.** For a point `p` of
the unit circle `S` of a two-dimensional real inner product space, the Mayer–Vietoris connecting
morphism of the cover of `S` by the two open arcs `S ∖ {p}` and `S ∖ {-p}` identifies `H₁(S)`
with the reduced zeroth homology of their intersection, which consists of two open arcs.  For a
point `x` of that intersection, the arcs are the path components of `x` and of `-x`, so this
reduced homology is one copy of the coefficient object, generated by `[-x] - [x]`.  The
connecting morphism therefore sends the generator of `H₁(S)` determined by this isomorphism to
`[-x] - [x]` (`TauCeti.singularHomologySphereOneIso_inv_mayerVietorisδ`). -/
def singularHomologySphereOneIso :
    (TopCat.toSSet.obj (TopCat.of (sphere (0 : E) 1))).homology R 1 ≅ R :=
  haveI := zerothHomotopyComplUnique hE hx
  -- `TauCeti.isIso_reducedMayerVietorisδ_sphere` is a theorem rather than an instance, so it is
  -- supplied to `asIso` explicitly.
  @asIso _ _ _ _ (TopCat.reducedMayerVietorisδ R (X := TopCat.of (sphere (0 : E) 1))
      isOpen_compl_singleton isOpen_compl_singleton
      (compl_singleton_union_compl_singleton_neg p) 0)
      (isIso_reducedMayerVietorisδ_sphere R p 0) ≪≫
    reducedSingularHomology₀Iso R (X := TopCat.of ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)))
      ⟨x, hx⟩ ≪≫ coproductUniqueIso _

/-- **The Mayer–Vietoris sequence of a circle covered by two arcs.**  The generator of `H₁(S)`
given by `TauCeti.singularHomologySphereOneIso` is sent by the Mayer–Vietoris connecting morphism
of the cover of `S` by `S ∖ {p}` and `S ∖ {-p}` to the class `[-x] - [x]` in the zeroth homology
of `S ∖ {p, -p}`, the difference of points on its two arcs. -/
@[reassoc]
lemma singularHomologySphereOneIso_inv_mayerVietorisδ :
    (singularHomologySphereOneIso R hE hx).inv ≫
        TopCat.mayerVietorisδ R (X := TopCat.of (sphere (0 : E) 1))
          isOpen_compl_singleton isOpen_compl_singleton
          (compl_singleton_union_compl_singleton_neg p) 1 0 =
      singularHomology₀Section R
          (X := TopCat.of ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)))
          ⟨-x, neg_mem_compl_singleton_inter_compl_singleton_neg hx⟩ -
        singularHomology₀Section R
          (X := TopCat.of ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) ⟨x, hx⟩ := by
  have := isIso_reducedMayerVietorisδ_sphere R p 0
  let := zerothHomotopyComplUnique hE hx
  -- The inverse of the reduced connecting morphism, followed by the connecting morphism, is the
  -- inclusion of reduced homology.
  have key : inv (TopCat.reducedMayerVietorisδ R (X := TopCat.of (sphere (0 : E) 1))
        isOpen_compl_singleton isOpen_compl_singleton
        (compl_singleton_union_compl_singleton_neg p) 0) ≫
      TopCat.mayerVietorisδ R (X := TopCat.of (sphere (0 : E) 1))
        isOpen_compl_singleton isOpen_compl_singleton
        (compl_singleton_union_compl_singleton_neg p) 1 0 =
      (reducedSingularHomologyι R 0).app _ :=
    (IsIso.inv_comp_eq _).2 (TopCat.reducedMayerVietorisδ_comp_ι R _ _ _ 0).symm
  simp only [singularHomologySphereOneIso, Iso.trans_inv, asIso_inv, coproductUniqueIso_inv,
    Category.assoc, key]
  exact ι_reducedSingularHomology₀Iso_inv_ι R (X := TopCat.of ({p}ᶜ ∩ {-p}ᶜ : Set _)) ⟨x, hx⟩
    ⟨-x, neg_mem_compl_singleton_inter_compl_singleton_neg hx⟩
    (zerothHomotopy_mk_neg_ne_of_finrank_eq_two hE hx)

end Circle

section Dimension

/-- **The reduced homology of a sphere vanishes outside its dimension.**  For a real inner product
space `E` of dimension `n + 1`, the reduced singular homology of its unit sphere vanishes in every
degree `k ≠ n`. -/
theorem isZero_reducedSingularHomologyFunctor_sphere_of_ne {n k : ℕ} (h : finrank ℝ E = n + 1)
    (hk : k ≠ n) :
    IsZero ((reducedSingularHomologyFunctor R k).obj (TopCat.of (sphere (0 : E) 1))) := by
  induction n generalizing E k with
  | zero =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ h
    obtain ⟨p⟩ := (NormedSpace.sphere_nonempty (E := E) (x := 0).mpr zero_le_one).coe_sort
    have : Fact (finrank ℝ E = 0 + 1) := ⟨h⟩
    have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ 0
    have hE : finrank ℝ (ℝ ∙ (p : E))ᗮ = 0 :=
      Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p)
    have : Subsingleton (ℝ ∙ (p : E))ᗮ := Module.finrank_zero_iff.mp hE
    have : IsEmpty (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :=
      Set.isEmpty_coe_sort.mpr (sphere_eq_empty_of_subsingleton one_ne_zero)
    exact (isZero_reducedSingularHomologyFunctor_of_isEmpty R
      (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)) k).of_iso
      (reducedSingularHomologySphereSuccIso R p k)
  | succ n ih =>
    have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ h
    obtain ⟨p⟩ := (NormedSpace.sphere_nonempty (E := E) (x := 0).mpr zero_le_one).coe_sort
    have : Fact (finrank ℝ E = (n + 1) + 1) := ⟨h⟩
    have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ (n + 1)
    cases k with
    | zero =>
      have : PathConnectedSpace (sphere (0 : E) 1) :=
        isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere (by
          rw [← Module.finrank_eq_rank, h]
          exact_mod_cast (by omega : 1 < n + 1 + 1)) 0 zero_le_one)
      exact isZero_reducedSingularHomologyFunctor_zero R (TopCat.of (sphere (0 : E) 1))
    | succ k =>
      exact (ih (Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p))
        (fun hkn ↦ hk (by omega))).of_iso (reducedSingularHomologySphereSuccIso R p k)

/-- The recursion behind `TauCeti.reducedSingularHomologySphereIso`, with the space as an explicit
argument so that it can vary along the induction on the dimension. -/
private def reducedSingularHomologySphereIsoAux :
    (n : ℕ) → (E : Type w) → [NormedAddCommGroup E] → [InnerProductSpace ℝ E] →
      OrthonormalBasis (Fin (n + 1)) ℝ E →
      ((reducedSingularHomologyFunctor R n).obj (TopCat.of (sphere (0 : E) 1)) ≅ R)
  | 0, _, _, _, b =>
    reducedSingularHomologySphereZeroIso R (by simp [finrank_eq_card_basis b.toBasis])
      ⟨b 0, by simp⟩
  | n + 1, _, _, _, b =>
    reducedSingularHomologySphereSuccIso R ⟨b (Fin.last _), by simp⟩ n ≪≫
      reducedSingularHomologySphereIsoAux n _ b.orthogonalLast

/-- **The reduced homology of a sphere in its dimension.**  An orthonormal basis `b` of a real
inner product space `E`, indexed by `Fin (n + 1)`, determines an isomorphism between the reduced
singular homology of the unit sphere of `E` in degree `n` and one copy of the coefficient object,
that is, a generator of `H_redₙ(Sⁿ)`.

In degree zero the sphere is `{b 0, -b 0}` and the generator is the class `[-b 0] - [b 0]`
(`TauCeti.reducedSingularHomologySphereIso_inv_ι`).  In positive degree the isomorphism is the
suspension isomorphism `TauCeti.reducedSingularHomologySphereSuccIso` at the last basis vector,
followed by the isomorphism for the equator determined by the remaining basis vectors
`b.orthogonalLast` (`TauCeti.reducedSingularHomologySphereIso_succ`).  Linear isometries matching
two bases carry one generator to the other
(`TauCeti.reducedSingularHomologySphereIso_hom_naturality`). -/
def reducedSingularHomologySphereIso {n : ℕ} (b : OrthonormalBasis (Fin (n + 1)) ℝ E) :
    (reducedSingularHomologyFunctor R n).obj (TopCat.of (sphere (0 : E) 1)) ≅ R :=
  reducedSingularHomologySphereIsoAux R n E b

/-- In degree zero, `TauCeti.reducedSingularHomologySphereIso` is the zero-sphere isomorphism
`TauCeti.reducedSingularHomologySphereZeroIso` at the basis vector `b 0`. -/
@[simp]
lemma reducedSingularHomologySphereIso_zero (b : OrthonormalBasis (Fin 1) ℝ E) :
    reducedSingularHomologySphereIso R b =
      reducedSingularHomologySphereZeroIso R (by simp [finrank_eq_card_basis b.toBasis])
        ⟨b 0, by simp⟩ :=
  (rfl)

/-- In degree `n + 1`, `TauCeti.reducedSingularHomologySphereIso` is the suspension isomorphism at
the last basis vector, followed by the isomorphism for the equator determined by the remaining
basis vectors. -/
@[simp]
lemma reducedSingularHomologySphereIso_succ {n : ℕ} (b : OrthonormalBasis (Fin (n + 2)) ℝ E) :
    reducedSingularHomologySphereIso R b =
      reducedSingularHomologySphereSuccIso R ⟨b (Fin.last _), by simp⟩ n ≪≫
        reducedSingularHomologySphereIso R b.orthogonalLast :=
  (rfl)

/-- **The generator of the reduced homology of the zero-sphere** determined by an orthonormal basis
`b` of a one-dimensional space is the class `[-b 0] - [b 0]`. -/
-- Not a simp lemma: `reducedSingularHomologyι_zero_app` rewrites the degree-zero inclusion
-- inside the left-hand side first, so this would fail the `simpNF` linter.
@[reassoc]
lemma reducedSingularHomologySphereIso_inv_ι (b : OrthonormalBasis (Fin 1) ℝ E) :
    (reducedSingularHomologySphereIso R b).inv ≫
        (reducedSingularHomologyι R 0).app (TopCat.of (sphere (0 : E) 1)) =
      singularHomology₀Section R (X := TopCat.of (sphere (0 : E) 1)) (-⟨b 0, by simp⟩) -
        singularHomology₀Section R (X := TopCat.of (sphere (0 : E) 1)) ⟨b 0, by simp⟩ :=
  reducedSingularHomologySphereZeroIso_inv_ι R _ _

/-- The degree-zero case of `TauCeti.reducedSingularHomologySphereIso_hom_naturality`, stated
for the inverses: on the zero-sphere, `f` carries the class `[-b 0] - [b 0]` to `[-c 0] - [c 0]`. -/
private lemma reducedSingularHomologySphereIso_inv_naturality_zero {F : Type w}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (b : OrthonormalBasis (Fin 1) ℝ E)
    (c : OrthonormalBasis (Fin 1) ℝ F) (f : E →ₗᵢ[ℝ] F) (hf : ∀ i, f (b i) = c i) :
    (reducedSingularHomologySphereIso R b).inv ≫
        (reducedSingularHomologyFunctor R 0).map
          (TopCat.ofHom ⟨f.unitSphereMap, f.continuous_unitSphereMap⟩) =
      (reducedSingularHomologySphereIso R c).inv := by
  rw [← cancel_mono ((reducedSingularHomologyι R 0).app _), Category.assoc,
    (reducedSingularHomologyι R 0).naturality, reducedSingularHomologySphereIso_inv_ι_assoc,
    reducedSingularHomologySphereIso_inv_ι, Preadditive.sub_comp]
  simp only [singularHomology₀Section_naturality]
  congr 2 <;> ext <;> simp [hf]

/-- **Naturality of the generators of the homology of spheres.**  Let `b` and `c` be orthonormal
bases of real inner product spaces `E` and `F`, indexed by `Fin (n + 1)`, and let
`f : E →ₗᵢ[ℝ] F` be a linear isometry with `f (b i) = c i` for every `i`.  Then the map induced on
`H_redₙ` by the restriction of `f` to the unit spheres carries the generator determined by `b` to
the generator determined by `c`. -/
@[reassoc]
theorem reducedSingularHomologySphereIso_hom_naturality {F : Type w} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {n : ℕ} (b : OrthonormalBasis (Fin (n + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (n + 1)) ℝ F) (f : E →ₗᵢ[ℝ] F) (hf : ∀ i, f (b i) = c i) :
    (reducedSingularHomologyFunctor R n).map
          (TopCat.ofHom ⟨f.unitSphereMap, f.continuous_unitSphereMap⟩) ≫
        (reducedSingularHomologySphereIso R c).hom =
      (reducedSingularHomologySphereIso R b).hom := by
  induction n generalizing E F with
  | zero =>
    rw [← Iso.eq_comp_inv, ← Iso.inv_comp_eq]
    exact reducedSingularHomologySphereIso_inv_naturality_zero R b c f hf
  | succ n ih =>
    -- The suspension isomorphisms at the last basis vectors are natural, and the restriction of
    -- `f` to the equators matches the remaining basis vectors.
    rw [reducedSingularHomologySphereIso_succ, reducedSingularHomologySphereIso_succ,
      Iso.trans_hom, Iso.trans_hom,
      reducedSingularHomologySphereSuccIso_hom_naturality_assoc R ⟨b (Fin.last _), by simp⟩ f
        ⟨c (Fin.last _), by simp⟩ (hf (Fin.last _))]
    congr 1
    exact ih _ _ _ fun i ↦ Subtype.ext (by simp [hf])

end Dimension

section Orientation

/-- A linear isometry negating the first vector of an orthonormal basis `b` and fixing the others
acts by `-1` on the generator determined by `b`. -/
private lemma reducedSingularHomologySphereIso_hom_neg_zero {F : Type w} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {n : ℕ} (b : OrthonormalBasis (Fin (n + 1)) ℝ F) (f : F →ₗᵢ[ℝ] F)
    (h₀ : f (b 0) = -b 0) (h : ∀ i ≠ 0, f (b i) = b i) :
    (reducedSingularHomologyFunctor R n).map
          (TopCat.ofHom ⟨f.unitSphereMap, f.continuous_unitSphereMap⟩) ≫
        (reducedSingularHomologySphereIso R b).hom =
      -(reducedSingularHomologySphereIso R b).hom := by
  induction n generalizing F with
  | zero =>
    suffices (reducedSingularHomologySphereIso R b).inv ≫
        (reducedSingularHomologyFunctor R 0).map
          (TopCat.ofHom ⟨f.unitSphereMap, f.continuous_unitSphereMap⟩) =
        -(reducedSingularHomologySphereIso R b).inv by
      rw [← cancel_epi (reducedSingularHomologySphereIso R b).inv, reassoc_of% this]
      simp
    -- `f` carries the class `[-b 0] - [b 0]` to `[b 0] - [-b 0]`.
    rw [← cancel_mono ((reducedSingularHomologyι R 0).app _), Category.assoc,
      (reducedSingularHomologyι R 0).naturality, reducedSingularHomologySphereIso_inv_ι_assoc,
      Preadditive.neg_comp, reducedSingularHomologySphereIso_inv_ι, Preadditive.sub_comp, neg_sub]
    simp only [singularHomology₀Section_naturality]
    congr 2 <;> ext <;> simp [h₀]
  | succ n ih =>
    -- `f` fixes the last basis vector, so it commutes with the suspension isomorphism there, and
    -- its restriction to the equator negates the first vector of `b.orthogonalLast`.
    have hlast : f (b (Fin.last _)) = b (Fin.last _) := h _ Fin.last_pos.ne'
    rw [reducedSingularHomologySphereIso_succ, Iso.trans_hom,
      reducedSingularHomologySphereSuccIso_hom_naturality_assoc R ⟨b (Fin.last _), by simp⟩ f
        ⟨b (Fin.last _), by simp⟩ hlast,
      ih _ _ ?_ ?_, Preadditive.comp_neg]
    · apply Subtype.ext
      rw [LinearIsometry.coe_orthogonalComplementSingletonMap_apply, Submodule.coe_neg,
        OrthonormalBasis.coe_orthogonalLast_apply, Fin.castSucc_zero, h₀]
    · intro i hi
      apply Subtype.ext
      rw [LinearIsometry.coe_orthogonalComplementSingletonMap_apply,
        OrthonormalBasis.coe_orthogonalLast_apply]
      exact h _ (by rwa [ne_eq, Fin.castSucc_eq_zero_iff])

/-- **A reflection acts by `-1` on the homology of a sphere.**  For a real inner product space `E`
of dimension `n + 1` and a nonzero vector `v`, the reflection of `E` in the hyperplane `(ℝ ∙ v)ᗮ`
induces `-1` on the reduced homology `H_redₙ(S)` of the unit sphere `S` of `E`. -/
theorem reducedSingularHomologyFunctor_map_reflection_unitSphereMap {n : ℕ}
    (hE : finrank ℝ E = n + 1) {v : E} (hv : v ≠ 0) :
    (reducedSingularHomologyFunctor R n).map (TopCat.ofHom
        ⟨(ℝ ∙ v)ᗮ.reflection.toLinearIsometry.unitSphereMap,
          (ℝ ∙ v)ᗮ.reflection.toLinearIsometry.continuous_unitSphereMap⟩) = -𝟙 _ := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  -- Extend the unit vector `‖v‖⁻¹ • v` to an orthonormal basis `b` with `b 0 = ‖v‖⁻¹ • v`.
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
    (ι := Fin (n + 1)) (by simpa using hE) (v := fun _ ↦ ‖v‖⁻¹ • v) (s := {0})
    (orthonormal_iff_ite.2 fun i j ↦ by
      rw [Subsingleton.elim i j]
      simp [hv])
  have hb₀ : b 0 = ‖v‖⁻¹ • v := hb 0 rfl
  rw [← cancel_mono (reducedSingularHomologySphereIso R b).hom, Preadditive.neg_comp,
    Category.id_comp]
  refine reducedSingularHomologySphereIso_hom_neg_zero R b _ ?_ fun i hi ↦ ?_
  · simp [hb₀, Submodule.reflection_orthogonalComplement_singleton_eq_neg]
  · refine Submodule.reflection_mem_subspace_eq_self
      (Submodule.mem_orthogonal_singleton_iff_inner_right.2 ?_)
    have : inner ℝ (b 0) (b i) = 0 := b.orthonormal.2 hi.symm
    rw [hb₀, real_inner_smul_left] at this
    simpa [hv] using this

/-- The case of `TauCeti.reducedSingularHomologyFunctor_map_unitSphereMap` for a product of
reflections, by induction on the number of factors. -/
private lemma reducedSingularHomologyFunctor_map_list_prod_reflection {n : ℕ}
    (hE : finrank ℝ E = n + 1) (l : List E) :
    (reducedSingularHomologyFunctor R n).map (TopCat.ofHom
        ⟨(l.map fun v ↦ (ℝ ∙ v)ᗮ.reflection).prod.toLinearIsometry.unitSphereMap,
          (l.map fun v ↦ (ℝ ∙ v)ᗮ.reflection).prod.toLinearIsometry.continuous_unitSphereMap⟩) =
      (SignType.sign (LinearMap.det
        (l.map fun v ↦ (ℝ ∙ v)ᗮ.reflection).prod.toLinearIsometry.toLinearMap) : ℤ) • 𝟙 _ := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  induction l with
  | nil =>
    -- The empty product is the identity, of determinant one.
    have h₁ : TopCat.ofHom ⟨(1 : E ≃ₗᵢ[ℝ] E).toLinearIsometry.unitSphereMap,
        (1 : E ≃ₗᵢ[ℝ] E).toLinearIsometry.continuous_unitSphereMap⟩ =
        𝟙 (TopCat.of (sphere (0 : E) 1)) := by
      ext; simp
    have h₂ : (1 : E ≃ₗᵢ[ℝ] E).toLinearIsometry.toLinearMap = LinearMap.id := by
      ext; simp
    simp [h₁, h₂]
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons]
    set φ := (l.map fun v ↦ (ℝ ∙ v)ᗮ.reflection).prod
    rcases eq_or_ne v 0 with rfl | hv
    · -- The reflection in `(ℝ ∙ 0)ᗮ = ⊤` is the identity.
      have h₁ : (ℝ ∙ (0 : E))ᗮ.reflection = 1 := LinearIsometryEquiv.ext fun x ↦
        Submodule.reflection_mem_subspace_eq_self (by simp)
      rw [h₁, one_mul]
      exact ih
    -- Otherwise the reflection acts by `-1` and has determinant `(-1) ^ finrank (ℝ ∙ v) = -1`.
    have hcomp : TopCat.ofHom ⟨((ℝ ∙ v)ᗮ.reflection * φ).toLinearIsometry.unitSphereMap,
        ((ℝ ∙ v)ᗮ.reflection * φ).toLinearIsometry.continuous_unitSphereMap⟩ =
        TopCat.ofHom ⟨φ.toLinearIsometry.unitSphereMap,
            φ.toLinearIsometry.continuous_unitSphereMap⟩ ≫
          TopCat.ofHom ⟨(ℝ ∙ v)ᗮ.reflection.toLinearIsometry.unitSphereMap,
            (ℝ ∙ v)ᗮ.reflection.toLinearIsometry.continuous_unitSphereMap⟩ := by
      ext; simp
    have hdet : ((ℝ ∙ v)ᗮ.reflection * φ).toLinearIsometry.toLinearMap =
        (ℝ ∙ v)ᗮ.reflection.toLinearMap ∘ₗ φ.toLinearIsometry.toLinearMap := by
      ext; simp
    rw [hcomp, Functor.map_comp, ih,
      reducedSingularHomologyFunctor_map_reflection_unitSphereMap R hE hv, hdet,
      LinearMap.det_comp, sign_mul, Submodule.det_reflection, Submodule.orthogonal_orthogonal,
      finrank_span_singleton hv]
    simp

/-- **A linear isometry acts on the homology of a sphere by the sign of its determinant.**  For a
real inner product space `E` of dimension `n + 1` and a linear isometry `f : E →ₗᵢ[ℝ] E`, the
restriction of `f` to the unit sphere `S` induces multiplication by `sign (det f) = ±1` on
`H_redₙ(S)`. -/
theorem reducedSingularHomologyFunctor_map_unitSphereMap {n : ℕ} (hE : finrank ℝ E = n + 1)
    (f : E →ₗᵢ[ℝ] E) :
    (reducedSingularHomologyFunctor R n).map
        (TopCat.ofHom ⟨f.unitSphereMap, f.continuous_unitSphereMap⟩) =
      (SignType.sign (LinearMap.det f.toLinearMap) : ℤ) • 𝟙 _ := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  -- By the Cartan–Dieudonné theorem, `f` is a product of reflections.
  obtain ⟨l, -, hl⟩ := (f.toLinearIsometryEquiv rfl).reflections_generate_dim
  obtain rfl : f = (l.map fun v ↦ (ℝ ∙ v)ᗮ.reflection).prod.toLinearIsometry :=
    LinearIsometry.ext fun x ↦ by simp [← hl]
  exact reducedSingularHomologyFunctor_map_list_prod_reflection R hE l

/-- **Change of basis for the generators of the homology of spheres.**  For two orthonormal bases
`b` and `c` of a real inner product space, indexed by `Fin (n + 1)`, the generator of `H_redₙ(S)`
determined by `c` is `sign (det_b c) = ±1` times the generator determined by `b`. -/
theorem reducedSingularHomologySphereIso_hom_eq_sign_det_smul {n : ℕ}
    (b c : OrthonormalBasis (Fin (n + 1)) ℝ E) :
    (reducedSingularHomologySphereIso R c).hom =
      (SignType.sign (b.toBasis.det c) : ℤ) • (reducedSingularHomologySphereIso R b).hom := by
  -- The linear isometry `f` carrying `b` to `c` has determinant `det_b c`.
  let f := b.equiv c (Equiv.refl _)
  have hf : ∀ i, f (b i) = c i := by simp [f]
  have hdet : LinearMap.det f.toLinearIsometry.toLinearMap = b.toBasis.det c := by
    have := b.toBasis.det_comp f.toLinearIsometry.toLinearMap b.toBasis
    rwa [Basis.det_self, mul_one, show (f.toLinearIsometry.toLinearMap ∘ b.toBasis) = c from
      funext fun i ↦ by simp [hf], eq_comm] at this
  have hsq : (SignType.sign (b.toBasis.det c) : ℤ) * SignType.sign (b.toBasis.det c) = 1 := by
    rcases b.det_to_matrix_orthonormalBasis_real c with h | h <;> simp [h]
  have := reducedSingularHomologySphereIso_hom_naturality R b c f.toLinearIsometry hf
  rw [reducedSingularHomologyFunctor_map_unitSphereMap R
      (by simp [finrank_eq_card_basis b.toBasis]),
    hdet, Preadditive.zsmul_comp, Category.id_comp] at this
  rw [← this, smul_smul, hsq, one_smul]

/-- **The generator of the homology of a sphere depends only on the orientation.**  Two
orthonormal bases of a real inner product space with the same orientation determine the same
isomorphism `H_redₙ(S) ≅ R`. -/
theorem reducedSingularHomologySphereIso_eq_of_orientation_eq {n : ℕ}
    {b c : OrthonormalBasis (Fin (n + 1)) ℝ E}
    (h : b.toBasis.orientation = c.toBasis.orientation) :
    reducedSingularHomologySphereIso R b = reducedSingularHomologySphereIso R c := by
  ext
  simp [reducedSingularHomologySphereIso_hom_eq_sign_det_smul R b c,
    b.det_to_matrix_orthonormalBasis_of_same_orientation c h]

/-- **Reversing the orientation negates the generator of the homology of a sphere.**  Two
orthonormal bases of a real inner product space with opposite orientations determine
isomorphisms `H_redₙ(S) ≅ R` differing by a sign. -/
theorem reducedSingularHomologySphereIso_hom_eq_neg_of_orientation_ne {n : ℕ}
    {b c : OrthonormalBasis (Fin (n + 1)) ℝ E}
    (h : b.toBasis.orientation ≠ c.toBasis.orientation) :
    (reducedSingularHomologySphereIso R c).hom = -(reducedSingularHomologySphereIso R b).hom := by
  simp [reducedSingularHomologySphereIso_hom_eq_sign_det_smul R b c,
    b.det_to_matrix_orthonormalBasis_of_opposite_orientation c h]

/-- **The antipodal map acts by `(-1) ^ (n + 1)` on the homology of a sphere.**  For a real inner
product space `E` of dimension `n + 1`, the antipodal map `x ↦ -x` of the unit sphere `S` of `E`
induces multiplication by `(-1) ^ (n + 1)` on `H_redₙ(S)`, the determinant of `-1` on `E`. -/
theorem reducedSingularHomologyFunctor_map_sphere_neg {n : ℕ} (hE : finrank ℝ E = n + 1) :
    (reducedSingularHomologyFunctor R n).map
        (TopCat.ofHom ⟨Neg.neg, continuous_neg⟩ : TopCat.of (sphere (0 : E) 1) ⟶ _) =
      (-1 : ℤ) ^ (n + 1) • 𝟙 _ := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  have h : (TopCat.ofHom ⟨Neg.neg, continuous_neg⟩ : TopCat.of (sphere (0 : E) 1) ⟶ _) =
      TopCat.ofHom ⟨(LinearIsometryEquiv.neg ℝ).toLinearIsometry.unitSphereMap,
        (LinearIsometryEquiv.neg ℝ).toLinearIsometry.continuous_unitSphereMap⟩ := by
    ext; simp
  have hdet : (LinearIsometryEquiv.neg ℝ (E := E)).toLinearIsometry.toLinearMap =
      (-1 : ℝ) • LinearMap.id := by
    ext; simp
  rw [h, reducedSingularHomologyFunctor_map_unitSphereMap R hE, hdet, LinearMap.det_smul,
    LinearMap.det_id, mul_one, hE, sign_pow]
  simp

end Orientation

section TopCatSphere

/-- **The reduced homology of `TopCat.sphere n` vanishes outside degree `n`.** -/
theorem isZero_reducedSingularHomologyFunctor_topCatSphere_of_ne {n k : ℕ} (hk : k ≠ n) :
    IsZero ((reducedSingularHomologyFunctor R k).obj (TopCat.sphere.{w} n)) :=
  (isZero_reducedSingularHomologyFunctor_sphere_of_ne R (finrank_euclideanSpace_ulift_fin (n + 1))
    hk).of_iso ((diskBoundaryHomeomorph (n + 1)).toHomotopyEquiv.reducedSingularHomologyIso R k)

/-- **The standard generator of the reduced homology of `TopCat.sphere n`.**  The reduced
homology of `TopCat.sphere n` in degree `n` is one copy of the coefficient object, through the
homeomorphism `TauCeti.diskBoundaryHomeomorph` with the unit sphere of
`EuclideanSpace ℝ (ULift (Fin (n + 1)))` and the generator
`TauCeti.reducedSingularHomologySphereIso` determined by the standard basis of that space, in its
order.  The generator involves no choices: by `TauCeti.reducedSingularHomologySphereIso_succ` it
is obtained from the class `[-e₀] - [e₀]` of the zero-sphere by suspending successively at the
last standard basis vector. -/
def reducedSingularHomologyTopCatSphereIso (n : ℕ) :
    (reducedSingularHomologyFunctor R n).obj (TopCat.sphere.{w} n) ≅ R :=
  (diskBoundaryHomeomorph (n + 1)).toHomotopyEquiv.reducedSingularHomologyIso R n ≪≫
    reducedSingularHomologySphereIso R
      ((EuclideanSpace.basisFun (ULift.{w} (Fin (n + 1))) ℝ).reindex Equiv.ulift)

/-- The standard generator of `H_redₙ(TopCat.sphere n)` is the map induced by the homeomorphism
`TauCeti.diskBoundaryHomeomorph` with the unit sphere of `EuclideanSpace ℝ (ULift (Fin (n + 1)))`,
followed by the generator `TauCeti.reducedSingularHomologySphereIso` of that sphere determined by
its standard basis. -/
@[simp]
lemma reducedSingularHomologyTopCatSphereIso_hom (n : ℕ) :
    (reducedSingularHomologyTopCatSphereIso R n).hom =
      (reducedSingularHomologyFunctor R n).map
          (TopCat.ofHom (diskBoundaryHomeomorph (n + 1)).toHomotopyEquiv.toFun) ≫
        (reducedSingularHomologySphereIso R
          ((EuclideanSpace.basisFun (ULift.{w} (Fin (n + 1))) ℝ).reindex Equiv.ulift)).hom :=
  -- The source object of the composite is `TopCat.sphere n` only up to unfolding, so `simp` and
  -- `rw` cannot apply `Iso.trans_hom` here; the equations are chained as terms instead.
  (Iso.trans_hom _ _).trans
    (congrArg (· ≫ _) (ContinuousMap.HomotopyEquiv.reducedSingularHomologyIso_hom R _ n))

end TopCatSphere

end TauCeti
