/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.ProjectiveSpace.Charts
public import TauCeti.Geometry.Toric.Analytic.Fan.GlueData

/-!
# Homogeneous-ratio transitions for toric projective space

The maximal charts of the projective-space fan cover its analytic realization. A point in
the chart normalized by `X_k = 1` lies in the chart of `l` precisely when `X_l` is nonzero.
On this overlap, its coordinates normalized by `X_l = 1` are `X_j / X_l`, including at
coordinate hyperplanes. Equality in the actual fan gluing is characterized by these equations.

The computations use the existing face-localization maps and the intersection-cone gluing
relation. They identify the standard affine projective transition functions without introducing
a second quotient or assuming that every homogeneous coordinate is nonzero.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.4.
-/

public section

open CategoryTheory Multiplicative Set

namespace TauCeti.Toric

universe u

variable {N V : Type u} {ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [Fintype ι] (b : Module.Basis ι ℤ N) {i : N →+ V} (hi : IsIntegralLattice i)

/-- Every point of toric projective space is represented in a maximal cone chart. This
includes dimension zero, when there is a single chart and no nonconstant affine coordinate. -/
theorem exists_projectiveSpaceMaximalCone_chart (p :
    (Fan.projectiveSpace b hi).analyticRealization (Fan.isRegular_projectiveSpace b hi)) :
    ∃ (k : Option ι)
      (x : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ))),
      (Fan.projectiveSpace b hi).analyticAffineChartι (Fan.isRegular_projectiveSpace b hi)
        (Fan.projectiveSpaceMaximalCone b hi k) x = p := by
  let Φ := Fan.projectiveSpace b hi
  obtain ⟨σ, x, rfl⟩ := Φ.exists_analyticAffineChartι_apply_eq
    (Fan.isRegular_projectiveSpace b hi) p
  obtain ⟨k, hk⟩ := Fan.exists_le_projectiveSpaceCone_compl b hi σ.2
  have hle : σ ≤ Fan.projectiveSpaceMaximalCone b hi k := Subtype.coe_le_coe.mp hk
  exact ⟨k, faceAffinePointMap hi (Φ.isFaceOf_of_le
    (Fan.projectiveSpaceMaximalCone b hi k).2 σ.2 hle) x,
    Φ.analyticAffineChartι_faceAffinePointMap (Fan.isRegular_projectiveSpace b hi) hle x⟩

private theorem overlap_coordinates (k l : Option ι)
    (z : AffineSemigroupComplexPoint (dualSemigroup hi
      (projectiveSpaceCone b i {k}ᶜ ⊓ projectiveSpaceCone b i {l}ᶜ))) :
    let x := (Fan.projectiveSpace b hi).analyticOverlapLeft
      (Fan.projectiveSpaceMaximalCone b hi k) (Fan.projectiveSpaceMaximalCone b hi l) z
    let y := (Fan.projectiveSpace b hi).analyticOverlapRight
      (Fan.projectiveSpaceMaximalCone b hi k) (Fan.projectiveSpaceMaximalCone b hi l) z
    projectiveSpaceHomogeneousCoordinate b hi k x l ≠ 0 ∧
      ∀ j, projectiveSpaceHomogeneousCoordinate b hi l y j =
        projectiveSpaceHomogeneousCoordinate b hi k x j /
          projectiveSpaceHomogeneousCoordinate b hi k x l := by
  let Φ := Fan.projectiveSpace b hi
  let σ := Fan.projectiveSpaceMaximalCone b hi k
  let τ := Fan.projectiveSpaceMaximalCone b hi l
  let a (j : Option ι) : dualSemigroup hi (σ ⊓ τ).1 :=
    ⟨projectiveSpaceRatioCharacter b j k, dualSemigroup_anti hi inf_le_left
      (projectiveSpaceRatioCharacter_mem_dualSemigroup b hi j k (by simp))⟩
  let c (j : Option ι) : dualSemigroup hi (σ ⊓ τ).1 :=
    ⟨projectiveSpaceRatioCharacter b j l, dualSemigroup_anti hi inf_le_right
      (projectiveSpaceRatioCharacter_mem_dualSemigroup b hi j l (by simp))⟩
  have hleft (j) : projectiveSpaceHomogeneousCoordinate b hi k
      (Φ.analyticOverlapLeft σ τ z) j = z (MonoidAlgebra.single (ofAdd (a j)) 1) := by
    erw [projectiveSpaceHomogeneousCoordinate_def, Fan.analyticOverlapLeft_def,
      Fan.analyticAffineChartDiagram_map_apply]
    -- The diagram uses bundled chart objects, while the monomial equation uses affine points.
    erw [AffineSemigroupComplexPoint.comap_apply_single]
    rfl
  have hright (j) : projectiveSpaceHomogeneousCoordinate b hi l
      (Φ.analyticOverlapRight σ τ z) j = z (MonoidAlgebra.single (ofAdd (c j)) 1) := by
    erw [projectiveSpaceHomogeneousCoordinate_def, Fan.analyticOverlapRight_def,
      Fan.analyticAffineChartDiagram_map_apply]
    -- The diagram uses bundled chart objects, while the monomial equation uses affine points.
    erw [AffineSemigroupComplexPoint.comap_apply_single]
    rfl
  have hac (j) : c j + a l = a j :=
    Subtype.ext (projectiveSpaceRatioCharacter_add b j l k)
  have hinv : a l + c k = 0 :=
    Subtype.ext ((projectiveSpaceRatioCharacter_add b l k l).trans
      (projectiveSpaceRatioCharacter_self b l))
  have hprod : z (MonoidAlgebra.single (ofAdd (a l)) 1) *
      z (MonoidAlgebra.single (ofAdd (c k)) 1) = 1 := by
    rw [← z.apply_single_add, hinv, ofAdd_zero, ← MonoidAlgebra.one_def, map_one]
  have hn := left_ne_zero_of_mul_eq_one hprod
  dsimp only
  refine ⟨?_, fun j ↦ ?_⟩
  · rw [hleft]
    exact hn
  · rw [hleft, hleft, hright, eq_div_iff hn, ← z.apply_single_add, hac]

/-- Equal representatives in two maximal charts have the standard ratio coordinates. Only
the denominator must be nonzero; every other homogeneous coordinate may vanish. -/
private theorem coordinates_of_chart_eq (k l : Option ι)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)))
    (y : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {l}ᶜ)))
    (h : (Fan.projectiveSpace b hi).analyticAffineChartι (Fan.isRegular_projectiveSpace b hi)
        (Fan.projectiveSpaceMaximalCone b hi k) x =
      (Fan.projectiveSpace b hi).analyticAffineChartι (Fan.isRegular_projectiveSpace b hi)
        (Fan.projectiveSpaceMaximalCone b hi l) y) :
    projectiveSpaceHomogeneousCoordinate b hi k x l ≠ 0 ∧
      ∀ j, projectiveSpaceHomogeneousCoordinate b hi l y j =
        projectiveSpaceHomogeneousCoordinate b hi k x j /
          projectiveSpaceHomogeneousCoordinate b hi k x l := by
  obtain ⟨z, rfl, rfl⟩ :=
    (Fan.analyticAffineChartι_eq_analyticAffineChartι_iff (Fan.projectiveSpace b hi)
      (Fan.isRegular_projectiveSpace b hi)
      (σ := Fan.projectiveSpaceMaximalCone b hi k)
      (τ := Fan.projectiveSpaceMaximalCone b hi l) x y).1 h
  exact overlap_coordinates b hi k l z

/-- The overlap of two maximal projective charts is exactly the nonvanishing locus of the
new normalizing coordinate. The statement also covers the self-overlap. -/
theorem projectiveSpace_chart_mem_range_iff (k l : Option ι)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ))) :
    (Fan.projectiveSpace b hi).analyticAffineChartι (Fan.isRegular_projectiveSpace b hi)
        (Fan.projectiveSpaceMaximalCone b hi k) x ∈
      Set.range ((Fan.projectiveSpace b hi).analyticAffineChartι
        (Fan.isRegular_projectiveSpace b hi) (Fan.projectiveSpaceMaximalCone b hi l)) ↔
      projectiveSpaceHomogeneousCoordinate b hi k x l ≠ 0 := by
  let Φ := Fan.projectiveSpace b hi
  let σ := Fan.projectiveSpaceMaximalCone b hi k
  let τ := Fan.projectiveSpaceMaximalCone b hi l
  constructor
  · rintro ⟨y, hy⟩
    exact (coordinates_of_chart_eq b hi k l x y hy.symm).1
  · intro hx
    let m : dualSemigroup hi σ.1 := ⟨projectiveSpaceRatioCharacter b l k,
      projectiveSpaceRatioCharacter_mem_dualSemigroup b hi l k (by simp)⟩
    have hker : σ.1 ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)) =
        (σ ⊓ τ).1 := projectiveSpaceCone_inf_ker_ratioCharacter b hi k l
    have hrange : x ∈ Set.range (faceAffinePointMap hi
        (Φ.isFaceOf_of_le σ.2 (σ ⊓ τ).2 inf_le_left)) := by
      rw [range_faceAffinePointMap_of_inf_ker_eq hi
        (isRegularCone_projectiveSpaceCone b hi (by simp)).fg _ m hker]
      simpa only [Set.mem_ofPred_eq, projectiveSpaceHomogeneousCoordinate_def, m] using hx
    obtain ⟨z, hz⟩ := hrange
    refine ⟨faceAffinePointMap hi (Φ.isFaceOf_of_le τ.2 (σ ⊓ τ).2 inf_le_right) z, ?_⟩
    exact (Φ.analyticAffineChartι_faceAffinePointMap_eq
      (Fan.isRegular_projectiveSpace b hi) (υ := σ ⊓ τ) inf_le_right inf_le_left z).trans
        (congrArg (Φ.analyticAffineChartι (Fan.isRegular_projectiveSpace b hi) σ) hz)

/-- Two affine representatives determine the same point of toric projective space exactly
when the new denominator is nonzero and all normalized coordinates satisfy the ratio formula.
This is equality in the fan realization, including points on coordinate hyperplanes. -/
theorem projectiveSpace_chart_eq_iff (k l : Option ι)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)))
    (y : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {l}ᶜ))) :
    (Fan.projectiveSpace b hi).analyticAffineChartι (Fan.isRegular_projectiveSpace b hi)
        (Fan.projectiveSpaceMaximalCone b hi k) x =
      (Fan.projectiveSpace b hi).analyticAffineChartι (Fan.isRegular_projectiveSpace b hi)
        (Fan.projectiveSpaceMaximalCone b hi l) y ↔
      projectiveSpaceHomogeneousCoordinate b hi k x l ≠ 0 ∧
        ∀ j, projectiveSpaceHomogeneousCoordinate b hi l y j =
          projectiveSpaceHomogeneousCoordinate b hi k x j /
            projectiveSpaceHomogeneousCoordinate b hi k x l := by
  constructor
  · exact coordinates_of_chart_eq b hi k l x y
  · rintro ⟨hn, hcoords⟩
    obtain ⟨y', hy'⟩ := (projectiveSpace_chart_mem_range_iff b hi k l x).2 hn
    have hcoords' := (coordinates_of_chart_eq
      b hi k l x y' hy'.symm).2
    have heq : y' = y := projectiveSpaceHomogeneousCoordinate_injective b hi l
      (funext fun j ↦ (hcoords' j).trans (hcoords j).symm)
    exact hy'.symm.trans (congrArg ((Fan.projectiveSpace b hi).analyticAffineChartι
      (Fan.isRegular_projectiveSpace b hi) (Fan.projectiveSpaceMaximalCone b hi l)) heq)

end TauCeti.Toric
