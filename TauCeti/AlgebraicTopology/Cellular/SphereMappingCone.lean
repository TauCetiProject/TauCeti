/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.LocalDegree
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Sphere
public import TauCeti.Topology.CWComplex.Classical.Sphere.MappingCone

/-!
# The cellular differential of `Sⁿ ∪_f Dⁿ⁺¹`

The CW complex `TauCeti.sphereMappingConeCWComplex h f` attaches an `(n + 1)`-cell to the sphere
`Sⁿ` along `f : Sⁿ → Sⁿ`, and its `n`-skeleton is `Sⁿ`
(`TauCeti.sphereMappingConeSkeletonHomeomorph`). This file shows that, read through that
identification, the attaching map `TauCeti.cellAttachingMap` of the `(n + 1)`-cell is `f`
(`TauCeti.cellAttachingMap_sphereMappingConeTopCell_apply`), and computes the cellular differential
of the complex from it: for a sphere of positive dimension `n + 1`, the differential from the
`(n + 2)`-cell to the `(n + 1)`-cell is multiplication by the degree of `f`, up to a unit fixed by
the orientation of the `(n + 1)`-cell and independent of `f`.

The degree is read in reduced singular homology with coefficients in a ring `R`: `f` has degree
`m` when it sends the standard generator of `H_redₙ₊₁(Sⁿ⁺¹; R)`
(`TauCeti.reducedSingularHomologyTopCatSphereIso`) to `m` times the generator determined by an
orthonormal basis `b` of the target (`TauCeti.reducedSingularHomologySphereIso`).

## Main results

* `TauCeti.exists_cellularIncidence_sphereMappingCone_eq_mul`: there is a unit `u` of `R` such
  that for every `f` of degree `m`, the incidence coefficient of the `(n + 1)`-cell in the
  boundary of the `(n + 2)`-cell of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` is `m * u`. Over `ℤ`, `u = ±1`.
* `TauCeti.exists_cellularDifferential_sphereMappingCone_eq_smul`: the same statement for the
  cellular differential on the basis vector of the `(n + 2)`-cell.

## Implementation notes

By `TauCeti.singularHomologyπ_cellAttachingMap_eq_cellularIncidence_smul`, the incidence
coefficient is the coordinate, with respect to the local class of the `(n + 1)`-cell at a point
`(x, 0)` of its open cell, of the image of the sphere generator under the attaching map in the
local homology of the `(n + 1)`-skeleton at `(x, 0)`. The `(n + 1)`-skeleton of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` is
`Sⁿ⁺¹ × {0}`, and the characteristic map of its `(n + 1)`-cell is that of `Sⁿ⁺¹` followed by
`a ↦ (a, 0)`. So the local class at `(x, 0)` is the image of the local class of the CW structure
`TauCeti.sphereCWComplex h` on `Sⁿ⁺¹` at `x`, and the image of the sphere generator is `m` times the
image of the generator determined by `b`. The coordinate `u` of that generator with respect to the
local class of `Sⁿ⁺¹` at `x` involves only `Sⁿ⁺¹`, not `f`, and it is a unit because
`Sⁿ⁺¹ ∖ {x}` is contractible, so that the generator also generates the local homology at `x`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Chapter 0
  (attaching cells), and Section 2.2 (the cellular boundary formula, and the Moore spaces
  `Sⁿ ∪_f eⁿ⁺¹` with `f` of degree `m`).
-/

public section

noncomputable section

open CategoryTheory Limits Metric Topology Topology.RelCWComplex

universe u

namespace TauCeti

section AttachingMap

variable {ι : Type u} [Fintype ι] {n : ℕ} (h : Fintype.card ι = n + 1)
  (f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, sphere (0 : EuclideanSpace ℝ ι) 1))

/-- The attaching map of the `(n + 1)`-cell of `Sⁿ ∪_f Dⁿ⁺¹` is `f`, read through the
identification `TauCeti.sphereMappingConeSkeletonHomeomorph` of the `n`-skeleton with `Sⁿ`. -/
@[simp]
theorem cellAttachingMap_sphereMappingConeTopCell_apply (x : TopCat.diskBoundary.{u} (n + 1)) :
    letI := sphereMappingConeCWComplex h f
    ConcreteCategory.hom (Y := TopCat.of (skeletonLT (sphereMappingCone f) ((n + 1 : ℕ) : ℕ∞)))
        (cellAttachingMap (sphereMappingConeTopCell h f)) x =
      sphereMappingConeSkeletonHomeomorph h f (f x.down) := by
  let _ := sphereMappingConeCWComplex h f
  apply Subtype.ext
  rw [coe_cellAttachingMap_apply, coe_diskHomeomorphClosedBall_apply]
  exact (map_sphereMappingConeTopCell_unitBallHomeomorph_coe_sphere h f x.down).trans
    (coe_sphereMappingConeSkeletonHomeomorph_apply h f _).symm

end AttachingMap

section Incidence

variable {ι : Type u} [Fintype ι] {n : ℕ} (h : Fintype.card ι = n + 1 + 1)

/-- The `(n + 1)`-skeleton of the CW structure on `Sⁿ⁺¹` is all of `Sⁿ⁺¹`. -/
private lemma coe_skeletonLT_sphere :
    letI := sphereCWComplex h
    (skeletonLT (sphere (0 : EuclideanSpace ℝ ι) 1) ((n + 1 + 1 : ℕ) : ℕ∞) :
      Set (EuclideanSpace ℝ ι)) = sphere 0 1 := by
  let _ := sphereCWComplex h
  exact skeletonLT_eq_complex_of_isEmpty_cell _ (n + 1 + 1) fun _ hm ↦
    isEmpty_cell_sphereCWComplex h hm

/-- `Sⁿ⁺¹` as its own `(n + 1)`-skeleton. -/
private def sphereToSkeleton :
    letI := sphereCWComplex h
    TopCat.of (sphere (0 : EuclideanSpace ℝ ι) 1) ⟶
      skeletonObj (sphere (0 : EuclideanSpace ℝ ι) 1) (n + 1 + 1) :=
  letI := sphereCWComplex h
  (TopCat.isoOfHomeo (Homeomorph.setCongr (coe_skeletonLT_sphere h)).symm).hom

private lemma isIso_sphereToSkeleton :
    letI := sphereCWComplex h
    IsIso (sphereToSkeleton h) := by
  rw [sphereToSkeleton]
  infer_instance

section Generator

variable {A : Type*} [Category A] [HasCoproducts.{u} A] [Abelian A] (R : A)
  (b : OrthonormalBasis (Fin (n + 1 + 1)) ℝ (EuclideanSpace ℝ ι))

/-- The generator of `H_redₙ₊₁(Sⁿ⁺¹)` determined by the orthonormal basis `b`, read in the local
homology `Hₙ₊₁(Sⁿ⁺¹, Sⁿ⁺¹ ∖ {x})` of `Sⁿ⁺¹`, viewed as its own `(n + 1)`-skeleton. -/
private def sphereLocalGenerator
    (x : letI := sphereCWComplex h; skeletonObj (sphere (0 : EuclideanSpace ℝ ι) 1) (n + 1 + 1)) :
    R ⟶ (TopPair.ofSubset ({x}ᶜ : Set _)).singularHomology R (n + 1) :=
  (reducedSingularHomologySphereIso R b).inv ≫
    (reducedSingularHomologyι R (n + 1)).app _ ≫
      SSet.homologyMap (TopCat.toSSet.map (sphereToSkeleton h)) R (n + 1) ≫
        (TopPair.ofSubset ({x}ᶜ : Set _)).singularHomologyπ R (n + 1)

/-- The generator of `H_redₙ₊₁(Sⁿ⁺¹)` generates the local homology of `Sⁿ⁺¹` at every point. -/
private lemma isIso_sphereLocalGenerator
    (x : letI := sphereCWComplex h; skeletonObj (sphere (0 : EuclideanSpace ℝ ι) 1) (n + 1 + 1)) :
    IsIso (sphereLocalGenerator h R b x) := by
  -- The four factors are isomorphisms: the generator; the comparison of reduced and unreduced
  -- homology in positive degree; the map induced by the homeomorphism of `Sⁿ⁺¹` with its
  -- `(n + 1)`-skeleton; and the map to the local homology at `x`, as `Sⁿ⁺¹ ∖ {x}` is
  -- contractible.
  let _ := sphereCWComplex h
  have : IsIso ((reducedSingularHomologyι R (n + 1)).app
      (TopCat.of (sphere (0 : EuclideanSpace ℝ ι) 1))) := by
    rw [reducedSingularHomologyι_succ_app]
    infer_instance
  have : IsIso (SSet.homologyMap (TopCat.toSSet.map (sphereToSkeleton h)) R (n + 1)) := by
    rw [← singularHomologyFunctor_obj_map]
    have := isIso_sphereToSkeleton h
    exact Functor.map_isIso _ _
  let e := Homeomorph.setCongr (coe_skeletonLT_sphere h)
  have : ContractibleSpace (TopPair.ofSubset ({x}ᶜ : Set (skeletonObj
      (sphere (0 : EuclideanSpace ℝ ι) 1) (n + 1 + 1)))).snd :=
    (e.subtype (q := (· ∈ ({e x}ᶜ : Set _))) fun _ ↦
      e.injective.ne_iff.symm).contractibleSpace_iff.2 (contractibleSpace_sphere_compl_singleton _)
  have : IsIso ((TopPair.ofSubset ({x}ᶜ : Set (skeletonObj
      (sphere (0 : EuclideanSpace ℝ ι) 1) (n + 1 + 1)))).singularHomologyπ R (n + 1)) :=
    TopPair.isIso_singularHomologyπ_of_contractibleSpace _ _ n
  -- The factors are invertible by the instances above, which match them only up to the
  -- presentation of the ambient spaces, so they are supplied by `‹_›`.
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' ‹_› (IsIso.comp_isIso' ‹_› ‹_›))

end Generator

variable (f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 1 + 1))) 1,
  sphere (0 : EuclideanSpace ℝ ι) 1))

/-- The map `f`, with its source written as Mathlib's sphere `TopCat.diskBoundary (n + 2)`. -/
private def diskBoundaryMap :
    TopCat.diskBoundary.{u} (n + 1 + 1) ⟶ TopCat.of (sphere (0 : EuclideanSpace ℝ ι) 1) :=
  TopCat.ofHom (f.comp ⟨ULift.down, continuous_uliftDown⟩)

/-- A point `(a, 0)` with `a` in the `(n + 1)`-skeleton of `Sⁿ⁺¹` lies in the `(n + 1)`-skeleton
of `Sⁿ⁺¹ ∪_f Dⁿ⁺²`. -/
private lemma mem_skeletonLT_sphereMappingCone
    (p : letI := sphereCWComplex h; skeletonObj (sphere (0 : EuclideanSpace ℝ ι) 1) (n + 1 + 1)) :
    letI := sphereMappingConeCWComplex h f
    ((p : EuclideanSpace ℝ ι), (0 : EuclideanSpace ℝ (Fin (n + 1 + 1)))) ∈
      (skeletonLT (sphereMappingCone f) ((n + 1 + 1 : ℕ) : ℕ∞) : Set _) := by
  let _ := sphereCWComplex h
  rw [coe_skeletonLT_sphereMappingCone]
  exact ⟨p, (skeletonLT _ _).subset_complex p.2, rfl⟩

/-- The `(n + 1)`-skeleton of `Sⁿ⁺¹` included in the `(n + 1)`-skeleton of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` by
`a ↦ (a, 0)`. -/
private def skeletonToMappingCone :
    letI := sphereCWComplex h
    letI := sphereMappingConeCWComplex h f
    skeletonObj (sphere (0 : EuclideanSpace ℝ ι) 1) (n + 1 + 1) ⟶
      skeletonObj (sphereMappingCone f) (n + 1 + 1) :=
  letI := sphereCWComplex h
  letI := sphereMappingConeCWComplex h f
  TopCat.ofHom ⟨fun p ↦ ⟨((p : EuclideanSpace ℝ ι), 0), mem_skeletonLT_sphereMappingCone h f p⟩,
    (continuous_subtype_val.prodMk continuous_const).subtype_mk _⟩

private lemma coe_skeletonToMappingCone_apply
    (p : letI := sphereCWComplex h; skeletonObj (sphere (0 : EuclideanSpace ℝ ι) 1) (n + 1 + 1)) :
    (skeletonToMappingCone h f p : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin (n + 1 + 1))) =
      ((p : EuclideanSpace ℝ ι), 0) :=
  (rfl)

private lemma injective_skeletonToMappingCone :
    letI := sphereCWComplex h
    letI := sphereMappingConeCWComplex h f
    Function.Injective (skeletonToMappingCone h f) := fun p q hpq ↦ by
  have := congrArg (fun z ↦ (z.1 : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin (n + 1 + 1))).1) hpq
  rw [coe_skeletonToMappingCone_apply, coe_skeletonToMappingCone_apply] at this
  exact Subtype.ext this

private lemma mapsTo_skeletonToMappingCone_compl
    (x : letI := sphereCWComplex h; skeletonObj (sphere (0 : EuclideanSpace ℝ ι) 1) (n + 1 + 1)) :
    Set.MapsTo (skeletonToMappingCone h f) ({x}ᶜ : Set _) {skeletonToMappingCone h f x}ᶜ :=
  fun _ hp hq ↦ hp (injective_skeletonToMappingCone h f hq)

/-- The attaching map of the `(n + 2)`-cell of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` is `f`, followed by the inclusion
of `Sⁿ⁺¹` as the `(n + 1)`-skeleton. -/
private lemma cellAttachingMap_sphereMappingConeTopCell_eq :
    letI := sphereMappingConeCWComplex h f
    cellAttachingMap (sphereMappingConeTopCell h f) =
      diskBoundaryMap f ≫ sphereToSkeleton h ≫ skeletonToMappingCone h f := by
  ext x : 1
  rw [cellAttachingMap_sphereMappingConeTopCell_apply]
  exact Subtype.ext (coe_sphereMappingConeSkeletonHomeomorph_apply h f _)

/-- `a ↦ (a, 0)` maps the open `(n + 1)`-cell of `Sⁿ⁺¹` into the corresponding open cell of
`Sⁿ⁺¹ ∪_f Dⁿ⁺²`. -/
private lemma mem_openCell_skeletonToMappingCone
    {i : letI := sphereCWComplex h; cell (sphere (0 : EuclideanSpace ℝ ι) 1) (n + 1)}
    {x : letI := sphereCWComplex h; skeletonObj (sphere (0 : EuclideanSpace ℝ ι) 1) (n + 1 + 1)}
    (hx : letI := sphereCWComplex h; (x : EuclideanSpace ℝ ι) ∈ openCell (n + 1) i) :
    letI := sphereMappingConeCWComplex h f
    (skeletonToMappingCone h f x : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin (n + 1 + 1))) ∈
      openCell (n + 1) (sphereMappingConeSphereCell h f i) := by
  let _ := sphereCWComplex h
  obtain ⟨y, hy, hyx⟩ := hx
  refine ⟨y, hy, ?_⟩
  rw [map_sphereMappingConeSphereCell_apply, hyx, coe_skeletonToMappingCone_apply]

variable {A : Type*} [Category A] [HasCoproducts.{u} A] [Abelian A] (R : A)

/-- The local class of the `(n + 1)`-cell of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` at `(a, 0)` is the image of the
local class of the `(n + 1)`-cell of `Sⁿ⁺¹` at `a`. -/
private lemma cellLocalClass_skeletonToMappingCone
    {i : letI := sphereCWComplex h; cell (sphere (0 : EuclideanSpace ℝ ι) 1) (n + 1)}
    {x : letI := sphereCWComplex h; skeletonObj (sphere (0 : EuclideanSpace ℝ ι) 1) (n + 1 + 1)}
    (hx : letI := sphereCWComplex h; (x : EuclideanSpace ℝ ι) ∈ openCell (n + 1) i) :
    letI := sphereCWComplex h
    letI := sphereMappingConeCWComplex h f
    cellLocalClass (sphereMappingCone f) R (skeletonToMappingCone h f x)
        (mem_openCell_skeletonToMappingCone h f hx) =
      cellLocalClass (sphere (0 : EuclideanSpace ℝ ι) 1) R x hx ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap (skeletonToMappingCone h f)
          (mapsTo_skeletonToMappingCone_compl h f x)) R (n + 1) := by
  let _ := sphereCWComplex h
  let _ := sphereMappingConeCWComplex h f
  rw [cellLocalClass_def, cellLocalClass_def, Category.assoc, ← TopPair.singularHomologyMap_comp]
  congr 2
  apply TopPair.hom_ext_of_fst
  ext z : 1
  apply Subtype.ext
  rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, TopPair.Hom.fst_comp,
    skeletonPairToComplSingleton_fst, skeletonPairToComplSingleton_fst, TopPair.ofSubsetMap_fst]
  -- The characteristic maps land in the skeletal pair, whose ambient space is the skeleton only
  -- up to unfolding `TopPair.ofSubset`, so the evaluation lemmas are applied with `erw`.
  erw [Category.comp_id, Category.comp_id, ConcreteCategory.comp_apply,
    coe_skeletonToMappingCone_apply, coe_characteristicCellPairMap_fst_apply,
    coe_characteristicCellPairMap_fst_apply, map_sphereMappingConeSphereCell_apply]

/-- If `f` has degree `m` with respect to the generator determined by `b`, then the attaching map
of the `(n + 2)`-cell of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` sends the standard generator of `H_redₙ₊₁(Sⁿ⁺¹)` to `m`
times the image of `sphereLocalGenerator h R b x` in the local homology at `(x, 0)`. -/
private lemma sphereGenerator_comp_cellAttachingMap_comp_singularHomologyπ
    (b : OrthonormalBasis (Fin (n + 1 + 1)) ℝ (EuclideanSpace ℝ ι)) (m : ℤ)
    (hf : (reducedSingularHomologyTopCatSphereIso R (n + 1)).inv ≫
        (reducedSingularHomologyFunctor R (n + 1)).map (diskBoundaryMap f) =
      m • (reducedSingularHomologySphereIso R b).inv)
    (x : letI := sphereCWComplex h; skeletonObj (sphere (0 : EuclideanSpace ℝ ι) 1) (n + 1 + 1)) :
    letI := sphereMappingConeCWComplex h f
    (reducedSingularHomologyTopCatSphereIso R (n + 1)).inv ≫
        (reducedSingularHomologyι R (n + 1)).app (TopCat.diskBoundary.{u} (n + 1 + 1)) ≫
          SSet.homologyMap (TopCat.toSSet.map (cellAttachingMap (sphereMappingConeTopCell h f)))
            R (n + 1) ≫
            (TopPair.ofSubset ({skeletonToMappingCone h f x}ᶜ : Set _)).singularHomologyπ R
              (n + 1) =
      m • (sphereLocalGenerator h R b x ≫ TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (skeletonToMappingCone h f)
          (mapsTo_skeletonToMappingCone_compl h f x)) R (n + 1)) := by
  let _ := sphereMappingConeCWComplex h f
  have hπ := TopPair.singularHomologyπ_naturality
    (TopPair.ofSubsetMap (skeletonToMappingCone h f) (mapsTo_skeletonToMappingCone_compl h f x))
    R (n + 1)
  rw [TopPair.ofSubsetMap_fst] at hπ
  have hι := (reducedSingularHomologyι R (n + 1)).naturality (diskBoundaryMap f)
  rw [← singularHomologyFunctor_obj_map, cellAttachingMap_sphereMappingConeTopCell_eq,
    Functor.map_comp, Functor.map_comp]
  -- Singular homology of a space appears both as the target of `reducedSingularHomologyι` and
  -- as the source of `singularHomologyπ`, as `TopCat.diskBoundary (n + 2)` and as
  -- `TopCat.sphere (n + 1)`, and the presentations agree only up to unfolding; so associativity,
  -- the naturality squares and `hf` are rewritten with `erw`, and the two sides of the final
  -- equation are the same composite up to these presentations.
  erw [Category.assoc, Category.assoc, ← reassoc_of% hι, reassoc_of% hf, hπ]
  rw [Preadditive.zsmul_comp, singularHomologyFunctor_obj_map]
  simp only [sphereLocalGenerator, Category.assoc]
  erw [Category.assoc]
  rfl

/-- **The cellular differential of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` is multiplication by the degree of `f`.**
Let `b` be an orthonormal basis of `EuclideanSpace ℝ ι` and `i` the `(n + 1)`-cell of the sphere
`Sⁿ⁺¹` of positive dimension `n + 1`. There is a unit `u` of `R` such that for every
`f : Sⁿ⁺¹ → Sⁿ⁺¹` of degree `m`, in the sense that `f` sends the standard generator of
`H_redₙ₊₁(Sⁿ⁺¹; R)` to `m` times the generator determined by `b`, the incidence coefficient of `i`
in the cellular boundary of the `(n + 2)`-cell of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` is `m * u`. The unit `u` does
not depend on `f`: it compares the orientation of the characteristic map of `i` with the
generator determined by `b`. Over `ℤ` it is `1` or `-1`. -/
theorem exists_cellularIncidence_sphereMappingCone_eq_mul (R : Type u) [Ring R]
    (b : OrthonormalBasis (Fin (n + 1 + 1)) ℝ (EuclideanSpace ℝ ι))
    (i : letI := sphereCWComplex h; cell (sphere (0 : EuclideanSpace ℝ ι) 1) (n + 1)) :
    ∃ u : Rˣ, ∀ (f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 1 + 1))) 1,
        sphere (0 : EuclideanSpace ℝ ι) 1)) (m : ℤ),
      (reducedSingularHomologyTopCatSphereIso (ModuleCat.of R R) (n + 1)).inv ≫
          (reducedSingularHomologyFunctor (ModuleCat.of R R) (n + 1)).map
            (TopCat.ofHom (f.comp ⟨ULift.down, continuous_uliftDown⟩)) =
        m • (reducedSingularHomologySphereIso (ModuleCat.of R R) b).inv →
      letI := sphereMappingConeCWComplex h f
      cellularIncidence (sphereMappingCone f) R (n + 1) (sphereMappingConeSphereCell h f i)
        (sphereMappingConeTopCell h f) = m * u := by
  let _ := sphereCWComplex h
  -- A point `x` of the open `(n + 1)`-cell of `Sⁿ⁺¹`, and the coordinate `u` of the generator
  -- determined by `b` with respect to the local class of `i` at `x`.
  let x : skeletonObj (sphere (0 : EuclideanSpace ℝ ι) 1) (n + 1 + 1) :=
    ⟨map (n + 1) i 0, map_mem_skeletonLT_succ i (by simp)⟩
  have hx : (x : EuclideanSpace ℝ ι) ∈ openCell (n + 1) i := ⟨0, by simp, rfl⟩
  set g := sphereLocalGenerator h (ModuleCat.of R R) b x
  have := isIso_sphereLocalGenerator h (ModuleCat.of R R) b x
  have hu : IsUnit (inv (cellLocalClass _ (ModuleCat.of R R) x hx) (g 1)) := by
    -- An automorphism of `R` as a module over itself is right multiplication by a unit.
    have hbij := ConcreteCategory.bijective_of_isIso
      (g ≫ inv (cellLocalClass _ (ModuleCat.of R R) x hx))
    exact (((Module.End.isUnit_iff _).2 hbij).map (RingEquiv.moduleEndSelf R).symm).unop
  set u := inv (cellLocalClass _ (ModuleCat.of R R) x hx) (g 1)
  refine ⟨hu.unit, fun f m hf ↦ ?_⟩
  let _ := sphereMappingConeCWComplex h f
  -- The local class of the `(n + 1)`-cell of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` at `(x, 0)`.
  set c := cellLocalClass (sphereMappingCone f) (ModuleCat.of R R) (skeletonToMappingCone h f x)
    (mem_openCell_skeletonToMappingCone h f hx)
  -- Read in the local homology at `(x, 0)`, the image of the sphere generator under the attaching
  -- map is the incidence coefficient times `c 1`, and also `m * u` times `c 1`.
  have hsmul : cellularIncidence (sphereMappingCone f) R (n + 1)
      (sphereMappingConeSphereCell h f i) (sphereMappingConeTopCell h f) • c 1 =
        ((m : R) * u) • c 1 := by
    rw [← singularHomologyπ_cellAttachingMap_eq_cellularIncidence_smul]
    -- `diskBoundaryMap f` is the map of the hypothesis `hf`, with its source written as
    -- `TopCat.diskBoundary (n + 2)`.
    refine (ConcreteCategory.congr_hom
      (sphereGenerator_comp_cellAttachingMap_comp_singularHomologyπ h f _ b m hf x) 1).trans ?_
    have hg : g 1 = cellLocalClass _ (ModuleCat.of R R) x hx (u • 1) := by
      rw [smul_eq_mul, mul_one, IsIso.inv_hom_id_apply]
    have hm (y : ModuleCat.of R R) {M : ModuleCat R} (φ : ModuleCat.of R R ⟶ M) :
        (m • φ) y = m • φ y := by
      simp
    rw [hm, ModuleCat.comp_apply, hg, map_smul, map_smul, ← ModuleCat.comp_apply,
      ← cellLocalClass_skeletonToMappingCone, mul_smul, Int.cast_smul_eq_zsmul]
  have := congrArg (inv c) hsmul
  rw [map_smul, map_smul, IsIso.hom_inv_id_apply, smul_eq_mul, smul_eq_mul, mul_one,
    mul_one] at this
  rw [this, IsUnit.unit_spec]

/-- **The cellular differential of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` is multiplication by the degree of `f`**, as a
formula for the differential: with `u` as in
`TauCeti.exists_cellularIncidence_sphereMappingCone_eq_mul`, for every `f` of degree `m` the
cellular differential sends the basis vector of the `(n + 2)`-cell to `m * u` times the basis
vector of the `(n + 1)`-cell `i`. -/
theorem exists_cellularDifferential_sphereMappingCone_eq_smul (R : Type u) [Ring R]
    (b : OrthonormalBasis (Fin (n + 1 + 1)) ℝ (EuclideanSpace ℝ ι))
    (i : letI := sphereCWComplex h; cell (sphere (0 : EuclideanSpace ℝ ι) 1) (n + 1)) :
    ∃ u : Rˣ, ∀ (f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 1 + 1))) 1,
        sphere (0 : EuclideanSpace ℝ ι) 1)) (m : ℤ),
      (reducedSingularHomologyTopCatSphereIso (ModuleCat.of R R) (n + 1)).inv ≫
          (reducedSingularHomologyFunctor (ModuleCat.of R R) (n + 1)).map
            (TopCat.ofHom (f.comp ⟨ULift.down, continuous_uliftDown⟩)) =
        m • (reducedSingularHomologySphereIso (ModuleCat.of R R) b).inv →
      letI := sphereMappingConeCWComplex h f
      cellularDifferential (sphereMappingCone f) (ModuleCat.of R R) (n + 1)
          (cellularChainBasis (sphereMappingCone f) R (n + 1 + 1)
            (sphereMappingConeTopCell h f)) =
        ((m : R) * u) • cellularChainBasis (sphereMappingCone f) R (n + 1)
          (sphereMappingConeSphereCell h f i) := by
  obtain ⟨u, hu⟩ := exists_cellularIncidence_sphereMappingCone_eq_mul h R b i
  refine ⟨u, fun f m hf ↦ ?_⟩
  let _ := sphereCWComplex h
  let _ := sphereMappingConeCWComplex h f
  -- The cell `i` is the only cell of `Sⁿ⁺¹ ∪_f Dⁿ⁺²` in dimension `n + 1`.
  have hi (j : cell (sphereMappingCone f) (n + 1)) : j = sphereMappingConeSphereCell h f i := by
    have hcard := nat_card_cell_sphereCWComplex h (n + 1)
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, zero_add] at hcard
    have := (Nat.card_eq_one_iff_unique.1 hcard).1
    obtain ⟨j', rfl⟩ := exists_sphereMappingConeSphereCell_eq h f (by omega) j
    rw [Subsingleton.elim j' i]
  have hcol : cellularBoundaryColumn (sphereMappingCone f) R (n + 1)
      (sphereMappingConeTopCell h f) =
        Finsupp.single (sphereMappingConeSphereCell h f i) ((m : R) * u) := by
    ext j
    rw [hi j, Finsupp.single_eq_same, cellularBoundaryColumn_apply, hu f m hf]
  rw [cellularDifferential_basis, hcol, Finsupp.sum_single_index]
  exact zero_smul R _

end Incidence

end TauCeti
