/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.ProjectiveSpace.Transition
public import TauCeti.Topology.ComplexProjectiveSpace.Charts
import TauCeti.Geometry.Toric.Analytic.Fan.Topology
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Toric projective space and the sphere quotient

The analytic realization of the standard projective-space fan is homeomorphic to complex
projective space, modelled by the circle quotient of the unit sphere. The comparison sends
the chart normalized at `k` to its homogeneous-coordinate vector. Conversely, a unit vector
whose `k`th coordinate is nonzero gives the affine ratios `X_j / X_k`. These formulas hold
also on coordinate hyperplanes and in dimension zero.

The comparison uses the affine homogeneous-coordinate charts and their ratio transitions.
The sphere quotient is `TauCeti.ComplexProjectiveSpace`, and normalization uses Mathlib's
`NormedSpace.normalize`.

The comparison matches the toric charts with the standard affine opens of the sphere quotient:
the maximal cone omitting the ray `k` corresponds to the affine open where `X_k` is nonzero, and
on it the homogeneous ratios `X_j / X_k` are the toric homogeneous coordinates
(`TauCeti.Toric.preimage_projectiveSpaceHomeomorph_affineOpen`,
`TauCeti.Toric.ratio_projectiveSpaceHomeomorph_analyticAffineChartι`,
`TauCeti.Toric.affineChart_projectiveSpaceHomeomorph_analyticAffineChartι`, and
`TauCeti.Toric.projectiveSpaceHomeomorph_symm_eq_of_mem_affineOpen`).

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.4.
-/

public section

open CategoryTheory Metric Set Topology

namespace TauCeti.Toric

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {n : ℕ} (b : Module.Basis (Fin n) ℤ N) {i : N →+ V} (hi : IsIntegralLattice i)

private noncomputable abbrev maximalChart (k : Option (Fin n)) :=
  Fan.projectiveSpaceMaximalCone b hi k

@[instance_reducible]
private noncomputable def chartTopology (k : Option (Fin n)) :
    TopologicalSpace (AffineSemigroupComplexPoint
      (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ))) :=
  affinePointTopology ((Fan.projectiveSpace b hi).analyticChartGenerators
    (maximalChart b hi k)).2

attribute [local instance] chartTopology

private noncomputable abbrev chartCoordinates (k : Option (Fin n)) :=
  projectiveSpacePointHomeomorph b hi k
    ((Fan.projectiveSpace b hi).analyticChartGenerators (maximalChart b hi k)).2

private noncomputable def vectorChart (k : Option (Fin n))
    (v : EuclideanSpace ℂ (Fin (n + 1))) :
    AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)) :=
  (chartCoordinates b hi k).symm
    (fun j ↦ v ((finSuccEquiv n).symm j) / v ((finSuccEquiv n).symm k))

private theorem vectorChart_coordinate (k : Option (Fin n))
    (v : EuclideanSpace ℂ (Fin (n + 1))) (hk : v ((finSuccEquiv n).symm k) ≠ 0)
    (j : Option (Fin n)) :
    projectiveSpaceHomogeneousCoordinate b hi k (vectorChart b hi k v) j =
      v ((finSuccEquiv n).symm j) / v ((finSuccEquiv n).symm k) := by
  by_cases hj : j = k
  · subst j
    simp [hk]
  · exact (projectiveSpacePointHomeomorph_eq_homogeneousCoordinate b hi k
      ((Fan.projectiveSpace b hi).analyticChartGenerators (maximalChart b hi k)).2
      (vectorChart b hi k v) ⟨j, hj⟩).symm.trans
        (congrFun ((chartCoordinates b hi k).apply_symm_apply _) ⟨j, hj⟩)

private noncomputable def vectorChartPoint (k : Option (Fin n))
    (v : EuclideanSpace ℂ (Fin (n + 1))) :
    (Fan.projectiveSpace b hi).analyticRealization (Fan.isRegular_projectiveSpace b hi) :=
  (Fan.projectiveSpace b hi).analyticAffineChartι (Fan.isRegular_projectiveSpace b hi)
    (maximalChart b hi k) (vectorChart b hi k v)

private theorem vectorChartPoint_eq (k l : Option (Fin n))
    (v : EuclideanSpace ℂ (Fin (n + 1)))
    (hk : v ((finSuccEquiv n).symm k) ≠ 0)
    (hl : v ((finSuccEquiv n).symm l) ≠ 0) :
    vectorChartPoint b hi k v = vectorChartPoint b hi l v := by
  apply (projectiveSpace_chart_eq_iff b hi k l _ _).2
  simp only [vectorChart_coordinate b hi _ _ hk, vectorChart_coordinate b hi _ _ hl]
  exact ⟨div_ne_zero hl hk, fun j ↦ by field_simp⟩

private theorem exists_nonzero_coordinate
    (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    ∃ k : Option (Fin n), v.1 ((finSuccEquiv n).symm k) ≠ 0 := by
  by_contra! h
  have hv : v.1 = 0 := by
    ext j
    simpa using h ((finSuccEquiv n) j)
  simpa [hv] using v.2

private noncomputable def spherePoint
    (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    (Fan.projectiveSpace b hi).analyticRealization (Fan.isRegular_projectiveSpace b hi) :=
  vectorChartPoint b hi (Classical.choose (exists_nonzero_coordinate v)) v.1

private theorem spherePoint_eq
    (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) (k : Option (Fin n))
    (hk : v.1 ((finSuccEquiv n).symm k) ≠ 0) :
    spherePoint b hi v = vectorChartPoint b hi k v.1 :=
  vectorChartPoint_eq b hi _ k v.1 (Classical.choose_spec (exists_nonzero_coordinate v)) hk

private theorem spherePoint_smul (c : sphere (0 : ℂ) 1)
    (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    spherePoint b hi (c • v) = spherePoint b hi v := by
  obtain ⟨k, hk⟩ := exists_nonzero_coordinate v
  have hc : (c : ℂ) ≠ 0 := by
    intro h
    simpa [h] using c.2
  have hck : (c • v).1 ((finSuccEquiv n).symm k) ≠ 0 := mul_ne_zero hc hk
  rw [spherePoint_eq b hi (c • v) k hck, spherePoint_eq b hi v k hk]
  apply congrArg ((Fan.projectiveSpace b hi).analyticAffineChartι
    (Fan.isRegular_projectiveSpace b hi) (maximalChart b hi k))
  apply congrArg (chartCoordinates b hi k).symm
  funext j
  exact mul_div_mul_left _ _ hc

private theorem continuous_spherePoint : Continuous (spherePoint b hi) := by
  apply continuous_iff_continuousAt.2
  intro v
  obtain ⟨k, hk⟩ := exists_nonzero_coordinate v
  have heval (j : Option (Fin n)) :
      Continuous (fun w : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 ↦
        w.1 ((finSuccEquiv n).symm j)) :=
    (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) ↦ ℂ)
      ((finSuccEquiv n).symm j)).comp continuous_subtype_val
  have hcoord : ContinuousAt (fun w : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 ↦
      fun j : {j : Option (Fin n) // j ≠ k} ↦
        w.1 ((finSuccEquiv n).symm j) / w.1 ((finSuccEquiv n).symm k)) v :=
    continuousAt_pi.2 fun j ↦ (heval j).continuousAt.div (heval k).continuousAt hk
  have hcont : ContinuousAt (fun w : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 ↦
      vectorChartPoint b hi k w.1) v :=
    ((Fan.projectiveSpace b hi).analyticAffineChartι
      (Fan.isRegular_projectiveSpace b hi) (maximalChart b hi k)).hom.continuous.continuousAt.comp
        ((chartCoordinates b hi k).symm.continuous.continuousAt.comp hcoord)
  exact hcont.congr_of_eventuallyEq (((heval k).continuousAt.eventually_ne hk).mono
    fun w hw ↦ spherePoint_eq b hi w k hw)

private theorem mk_eq_of_spherePoint_eq
    (v w : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)
    (h : spherePoint b hi v = spherePoint b hi w) :
    ComplexProjectiveSpace.mk n v = ComplexProjectiveSpace.mk n w := by
  obtain ⟨k, hk⟩ := exists_nonzero_coordinate v
  obtain ⟨l, hl⟩ := exists_nonzero_coordinate w
  have heq : vectorChartPoint b hi l w.1 = vectorChartPoint b hi k v.1 :=
    (spherePoint_eq b hi w l hl).symm.trans (h.symm.trans (spherePoint_eq b hi v k hk))
  have hwk : w.1 ((finSuccEquiv n).symm k) ≠ 0 := by
    have hh := ((projectiveSpace_chart_eq_iff b hi l k _ _).1 heq).1
    rw [vectorChart_coordinate b hi l w.1 hl] at hh
    exact (div_ne_zero_iff.1 hh).1
  have hcharts : vectorChart b hi k v.1 = vectorChart b hi k w.1 :=
    ((Fan.projectiveSpace b hi).isOpenEmbedding_analyticAffineChartι
      (Fan.isRegular_projectiveSpace b hi) (maximalChart b hi k)).injective
        ((spherePoint_eq b hi v k hk).symm.trans
          (h.trans (spherePoint_eq b hi w k hwk)))
  have hratio (j : Option (Fin n)) :
      v.1 ((finSuccEquiv n).symm j) / v.1 ((finSuccEquiv n).symm k) =
        w.1 ((finSuccEquiv n).symm j) / w.1 ((finSuccEquiv n).symm k) := by
    rw [← vectorChart_coordinate b hi k v.1 hk,
      ← vectorChart_coordinate b hi k w.1 hwk, hcharts]
  let c := v.1 ((finSuccEquiv n).symm k) / w.1 ((finSuccEquiv n).symm k)
  have hsmul : c • w.1 = v.1 := by
    ext j
    have hj := hratio ((finSuccEquiv n) j)
    simp only [Equiv.symm_apply_apply] at hj
    have he := (div_eq_div_iff hk hwk).1 hj
    dsimp [c]
    simp only [div_mul_eq_mul_div]
    exact (div_eq_iff hwk).2 ((mul_comm _ _).trans he.symm)
  have hc : ‖c‖ = 1 := by
    have hn := congrArg norm hsmul
    simpa only [norm_smul, mem_sphere_zero_iff_norm.1 w.2,
      mem_sphere_zero_iff_norm.1 v.2, mul_one] using hn
  exact (ComplexProjectiveSpace.mk_eq_mk_iff n v w).2
    ⟨⟨c, mem_sphere_zero_iff_norm.2 hc⟩, Subtype.ext hsmul⟩

private noncomputable def projectivePoint : ComplexProjectiveSpace n →
    (Fan.projectiveSpace b hi).analyticRealization (Fan.isRegular_projectiveSpace b hi) :=
  ComplexProjectiveSpace.lift n (spherePoint b hi) (spherePoint_smul b hi)

private theorem projectivePoint_mk
    (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    projectivePoint b hi (ComplexProjectiveSpace.mk n v) = spherePoint b hi v :=
  ComplexProjectiveSpace.lift_mk n _ _ v

private theorem continuous_projectivePoint : Continuous (projectivePoint b hi) :=
  (ComplexProjectiveSpace.isOpenQuotientMap_mk n).continuous_comp_iff.1
    ((continuous_spherePoint b hi).congr fun v ↦ (projectivePoint_mk b hi v).symm)

private theorem projectivePoint_injective : Function.Injective (projectivePoint b hi) := by
  intro p q h
  obtain ⟨v, rfl⟩ := ComplexProjectiveSpace.mk_surjective n p
  obtain ⟨w, rfl⟩ := ComplexProjectiveSpace.mk_surjective n q
  exact mk_eq_of_spherePoint_eq b hi v w (by simpa only [projectivePoint_mk] using h)

/-- The homogeneous coordinates of an affine toric projective chart, arranged as a vector
in `ℂⁿ⁺¹`. The normalizing coordinate is one, so this vector never vanishes. -/
noncomputable def projectiveSpaceHomogeneousVector (k : Option (Fin n))
    (x : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ))) :
    EuclideanSpace ℂ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun j ↦ projectiveSpaceHomogeneousCoordinate b hi k x ((finSuccEquiv n) j))

/-- The vector coordinates are the normalized homogeneous coordinates of the affine point. -/
@[simp]
theorem projectiveSpaceHomogeneousVector_apply (k : Option (Fin n))
    (x : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)))
    (j : Fin (n + 1)) :
    projectiveSpaceHomogeneousVector b hi k x j =
      projectiveSpaceHomogeneousCoordinate b hi k x ((finSuccEquiv n) j) := (rfl)

/-- A normalized homogeneous-coordinate vector is nonzero. -/
theorem projectiveSpaceHomogeneousVector_ne_zero (k : Option (Fin n))
    (x : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ))) :
    projectiveSpaceHomogeneousVector b hi k x ≠ 0 := by
  intro h
  have hh := congrArg (fun v : EuclideanSpace ℂ (Fin (n + 1)) ↦
    v ((finSuccEquiv n).symm k)) h
  simp at hh

private noncomputable def homogeneousSphere (k : Option (Fin n))
    (x : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ))) :
    sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 :=
  ⟨NormedSpace.normalize (projectiveSpaceHomogeneousVector b hi k x),
    mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize
      (projectiveSpaceHomogeneousVector_ne_zero b hi k x))⟩

private theorem homogeneousSphere_ratio (k : Option (Fin n))
    (x : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)))
    (j : Option (Fin n)) :
    (homogeneousSphere b hi k x).1 ((finSuccEquiv n).symm j) /
        (homogeneousSphere b hi k x).1 ((finSuccEquiv n).symm k) =
      projectiveSpaceHomogeneousCoordinate b hi k x j := by
  have hn := norm_ne_zero_iff.2 (projectiveSpaceHomogeneousVector_ne_zero b hi k x)
  simp [homogeneousSphere, NormedSpace.normalize, PiLp.smul_apply]
  field_simp [Complex.ofReal_ne_zero.mpr hn]

private theorem homogeneousSphere_normalizing_ne_zero (k : Option (Fin n))
    (x : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ))) :
    (homogeneousSphere b hi k x).1 ((finSuccEquiv n).symm k) ≠ 0 := by
  have hh := homogeneousSphere_ratio b hi k x k
  rw [projectiveSpaceHomogeneousCoordinate_self] at hh
  exact (div_ne_zero_iff.1 (hh ▸ one_ne_zero)).1

private theorem spherePoint_homogeneousSphere (k : Option (Fin n))
    (x : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ))) :
    spherePoint b hi (homogeneousSphere b hi k x) =
      (Fan.projectiveSpace b hi).analyticAffineChartι (Fan.isRegular_projectiveSpace b hi)
        (maximalChart b hi k) x := by
  rw [spherePoint_eq b hi _ k (homogeneousSphere_normalizing_ne_zero b hi k x)]
  apply congrArg ((Fan.projectiveSpace b hi).analyticAffineChartι
    (Fan.isRegular_projectiveSpace b hi) (maximalChart b hi k))
  apply projectiveSpaceHomogeneousCoordinate_injective b hi k
  funext j
  rw [vectorChart_coordinate b hi _ _ (homogeneousSphere_normalizing_ne_zero b hi k x),
    homogeneousSphere_ratio]

private theorem projectivePoint_surjective : Function.Surjective (projectivePoint b hi) := by
  intro p
  obtain ⟨k, x, rfl⟩ := exists_projectiveSpaceMaximalCone_chart b hi p
  exact ⟨ComplexProjectiveSpace.mk n (homogeneousSphere b hi k x),
    (projectivePoint_mk b hi _).trans (spherePoint_homogeneousSphere b hi k x)⟩

/-- Homogeneous coordinates identify the analytic realization of the standard projective-space
fan with complex projective space as the circle quotient of the unit sphere. -/
noncomputable def projectiveSpaceHomeomorph :
    (Fan.projectiveSpace b hi).analyticRealization (Fan.isRegular_projectiveSpace b hi) ≃ₜ
      ComplexProjectiveSpace n :=
  let e := Equiv.ofBijective (projectivePoint b hi)
    ⟨projectivePoint_injective b hi, projectivePoint_surjective b hi⟩
  (e.toHomeomorphOfContinuousClosed (continuous_projectivePoint b hi)
    (continuous_projectivePoint b hi).isClosedMap).symm

private theorem projectiveSpaceHomeomorph_symm_apply (p : ComplexProjectiveSpace n) :
    (projectiveSpaceHomeomorph b hi).symm p = projectivePoint b hi p := (rfl)

/-- A unit homogeneous vector whose normalizing coordinate is nonzero represents the affine
point with the usual homogeneous ratios. The other coordinates are allowed to vanish. -/
theorem projectiveSpaceHomeomorph_symm_mk
    (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) (k : Option (Fin n))
    (hk : v.1 ((finSuccEquiv n).symm k) ≠ 0) :
    let _ := affinePointTopology ((Fan.projectiveSpace b hi).analyticChartGenerators
      (Fan.projectiveSpaceMaximalCone b hi k)).2
    (projectiveSpaceHomeomorph b hi).symm (ComplexProjectiveSpace.mk n v) =
      (Fan.projectiveSpace b hi).analyticAffineChartι (Fan.isRegular_projectiveSpace b hi)
        (Fan.projectiveSpaceMaximalCone b hi k)
        ((projectiveSpacePointHomeomorph b hi k
          ((Fan.projectiveSpace b hi).analyticChartGenerators
            (Fan.projectiveSpaceMaximalCone b hi k)).2).symm
          (fun j ↦ v.1 ((finSuccEquiv n).symm j) / v.1 ((finSuccEquiv n).symm k))) := by
  rw [projectiveSpaceHomeomorph_symm_apply, projectivePoint_mk, spherePoint_eq b hi v k hk]
  rfl

/-- On an affine chart, the comparison takes the class of the normalized homogeneous vector.
In particular, normalization does not discard points on coordinate hyperplanes. -/
theorem projectiveSpaceHomeomorph_apply_chart (k : Option (Fin n))
    (x : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ))) :
    projectiveSpaceHomeomorph b hi
      ((Fan.projectiveSpace b hi).analyticAffineChartι (Fan.isRegular_projectiveSpace b hi)
        (Fan.projectiveSpaceMaximalCone b hi k) x) =
      ComplexProjectiveSpace.mk n
        ⟨NormedSpace.normalize (projectiveSpaceHomogeneousVector b hi k x),
          mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize
            (projectiveSpaceHomogeneousVector_ne_zero b hi k x))⟩ := by
  apply (projectiveSpaceHomeomorph b hi).symm.injective
  rw [Homeomorph.symm_apply_apply, projectiveSpaceHomeomorph_symm_apply, projectivePoint_mk]
  exact (spherePoint_homogeneousSphere b hi k x).symm

/-- On the toric chart of the maximal cone omitting `k`, the homogeneous ratios `X_j / X_k` of the
comparison with the sphere quotient are the normalized toric homogeneous coordinates. -/
@[simp]
theorem ratio_projectiveSpaceHomeomorph_analyticAffineChartι (k : Option (Fin n))
    (x : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)))
    (j : Fin (n + 1)) :
    ComplexProjectiveSpace.ratio ((finSuccEquiv n).symm k) j
        (projectiveSpaceHomeomorph b hi
          ((Fan.projectiveSpace b hi).analyticAffineChartι (Fan.isRegular_projectiveSpace b hi)
            (Fan.projectiveSpaceMaximalCone b hi k) x)) =
      projectiveSpaceHomogeneousCoordinate b hi k x (finSuccEquiv n j) := by
  have hn := norm_ne_zero_iff.2 (projectiveSpaceHomogeneousVector_ne_zero b hi k x)
  rw [projectiveSpaceHomeomorph_apply_chart, ComplexProjectiveSpace.ratio_mk]
  simp only [NormedSpace.normalize, PiLp.smul_apply, projectiveSpaceHomogeneousVector_apply,
    Equiv.apply_symm_apply, projectiveSpaceHomogeneousCoordinate_self, Complex.real_smul,
    mul_one]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (inv_ne_zero hn))

/-- On the toric chart of the maximal cone omitting `k`, the standard affine chart of the sphere
quotient where `X_k` is nonzero reads the comparison as the toric homogeneous coordinates. -/
theorem affineChart_projectiveSpaceHomeomorph_analyticAffineChartι (k : Option (Fin n))
    (x : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ))) :
    ComplexProjectiveSpace.affineChart ((finSuccEquiv n).symm k)
        (projectiveSpaceHomeomorph b hi
          ((Fan.projectiveSpace b hi).analyticAffineChartι (Fan.isRegular_projectiveSpace b hi)
            (Fan.projectiveSpaceMaximalCone b hi k) x)) =
      fun j ↦ projectiveSpaceHomogeneousCoordinate b hi k x
        (finSuccEquiv n (((finSuccEquiv n).symm k).succAbove j)) := by
  funext j
  rw [ComplexProjectiveSpace.affineChart_apply]
  exact ratio_projectiveSpaceHomeomorph_analyticAffineChartι b hi k x _

/-- The standard affine open of complex projective space where the homogeneous coordinate `k` is
nonzero corresponds to the toric chart of the maximal cone omitting the ray `k`. -/
theorem preimage_projectiveSpaceHomeomorph_affineOpen (k : Option (Fin n)) :
    projectiveSpaceHomeomorph b hi ⁻¹'
        ComplexProjectiveSpace.affineOpen ((finSuccEquiv n).symm k) =
      range ((Fan.projectiveSpace b hi).analyticAffineChartι (Fan.isRegular_projectiveSpace b hi)
        (Fan.projectiveSpaceMaximalCone b hi k)) := by
  ext p
  constructor
  · intro hp
    obtain ⟨v, hv⟩ := ComplexProjectiveSpace.mk_surjective n (projectiveSpaceHomeomorph b hi p)
    have hk : v.1 ((finSuccEquiv n).symm k) ≠ 0 := by simpa [← hv] using hp
    refine ⟨_, (projectiveSpaceHomeomorph_symm_mk b hi v k hk).symm.trans ?_⟩
    rw [hv, Homeomorph.symm_apply_apply]
  · rintro ⟨x : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)),
      rfl⟩
    have h := ratio_projectiveSpaceHomeomorph_analyticAffineChartι b hi k x
      ((finSuccEquiv n).symm k)
    rw [Equiv.apply_symm_apply, projectiveSpaceHomogeneousCoordinate_self] at h
    exact (ComplexProjectiveSpace.mem_affineOpen_iff _ _).2 (ne_of_eq_of_ne h one_ne_zero)

/-- On the standard affine open where `X_k` is nonzero, the inverse comparison is the point of
the toric chart of the maximal cone omitting `k` with toric coordinates the homogeneous ratios
`X_j / X_k`. -/
theorem projectiveSpaceHomeomorph_symm_eq_of_mem_affineOpen (k : Option (Fin n))
    {p : ComplexProjectiveSpace n}
    (hp : p ∈ ComplexProjectiveSpace.affineOpen ((finSuccEquiv n).symm k)) :
    let _ := affinePointTopology ((Fan.projectiveSpace b hi).analyticChartGenerators
      (Fan.projectiveSpaceMaximalCone b hi k)).2
    (projectiveSpaceHomeomorph b hi).symm p =
      (Fan.projectiveSpace b hi).analyticAffineChartι (Fan.isRegular_projectiveSpace b hi)
        (Fan.projectiveSpaceMaximalCone b hi k)
        ((projectiveSpacePointHomeomorph b hi k
          ((Fan.projectiveSpace b hi).analyticChartGenerators
            (Fan.projectiveSpaceMaximalCone b hi k)).2).symm
          (fun j ↦ ComplexProjectiveSpace.ratio ((finSuccEquiv n).symm k)
            ((finSuccEquiv n).symm j) p)) := by
  obtain ⟨v, rfl⟩ := ComplexProjectiveSpace.mk_surjective n p
  have hk : v.1 ((finSuccEquiv n).symm k) ≠ 0 := by simpa using hp
  simp only [ComplexProjectiveSpace.ratio_mk]
  exact projectiveSpaceHomeomorph_symm_mk b hi v k hk

end TauCeti.Toric
