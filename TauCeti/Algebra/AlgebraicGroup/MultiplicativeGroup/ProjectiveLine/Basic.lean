/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.HomogeneousIdeal
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.FromMatrix
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.LinearAction
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Semilinear
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ClosedPoints
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ChartEquality
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.CoordinateMap
import TauCeti.RingTheory.Spectrum.Prime.Polynomial

/-!
# Orbits of the multiplicative group on the projective line

Let `𝔾ₘ = Spec R[T, T⁻¹]` act on `R²` by `t • (u, v) = (t u, v)`, and hence on the projective
line `ℙ¹ = ℙ(R²)` by `t • [u : v] = [t u : v]`. This file computes the orbits of this action, as
the full images of the projective orbit morphisms `𝔾ₘ ⟶ ℙ¹`, nonclosed points included. Over a
field `k`:

* the lines `[1 : 0]` and `[0 : 1]` through the two standard basis vectors are fixed by the whole
  group scheme, so their orbits are single closed points;
* the orbit of `[1 : 1]` is dense in `ℙ¹` (over any domain) and consists of all points except the
  two fixed points, so it is not closed;
* hence the boundary of that orbit, its closure minus the orbit, is exactly the two fixed points.

This is the standard example of the closed-orbit lemma: the open orbit has a boundary made of
orbits of smaller dimension, and these are closed. Over `ℂ` the open orbit is `ℂ*`, embedded as
`t ↦ [t : 1]`, and its boundary is the two closed fixed points `0` and `∞`.

The fixed points are lines spanned by weight vectors. The orbit of `[1 : 1]` is dense because its
orbit coordinates satisfy no homogeneous relation: after identifying the forms on `R²` with
`R[X₀, X₁]`, they are the dehomogenization `f ↦ f(T, 1)`, which is injective on forms of each
degree. The orbit itself is computed by identifying `ℙ(k²)` with the standard projective line
`Proj k[X₀, X₁]` through the dual basis: the orbit morphism becomes the localization
`Spec k[T, T⁻¹] ⟶ Spec k[X]` followed by the standard chart `D₊(X₁)`, so the orbit is the overlap
`D₊(X₀) ∩ D₊(X₁)` of the two standard charts. Its complement is the two fixed points, over any
field and including nonclosed points.

## Main declarations

* `TauCeti.MultiplicativeGroup.scalingComodule`: the representation `t • (u, v) = (t u, v)` of
  `𝔾ₘ` on `R²`, over any commutative ring.
* `TauCeti.MultiplicativeGroup.range_projectiveOrbitMap_single`: the orbits of `[1 : 0]` and
  `[0 : 1]` are single points.
* `TauCeti.MultiplicativeGroup.isClosed_range_projectiveOrbitMap_single`: these orbits are closed.
* `TauCeti.MultiplicativeGroup.dense_range_projectiveOrbitMap_one`: the orbit of `[1 : 1]` is
  dense.
* `TauCeti.MultiplicativeGroup.projectiveOrbitMap_one_comp_symmetricAlgebraMapIso_hom`: on the
  standard projective line, the orbit morphism of `[1 : 1]` is the chart `D₊(X₁)` on `D(X)`.
* `TauCeti.MultiplicativeGroup.range_projectiveOrbitMap_one`: the orbit of `[1 : 1]` is the
  complement of the two fixed points.
* `TauCeti.MultiplicativeGroup.projectiveOrbitMap_single_notMem_range_one` and
  `TauCeti.MultiplicativeGroup.not_isClosed_range_projectiveOrbitMap_one`: it misses both fixed
  points, so it is not closed.
* `TauCeti.MultiplicativeGroup.closure_diff_range_projectiveOrbitMap_one`: its boundary consists
  of the two fixed points.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f, orbits and homogeneous spaces.
* A. Borel, *Linear Algebraic Groups*, 2nd ed., GTM 126, Springer (1991), §1.8.
-/

public section

open CategoryTheory AlgebraicGeometry LaurentPolynomial TauCeti.Comodule

namespace TauCeti.MultiplicativeGroup

universe u

section Ring

variable (R : Type u) [CommRing R]

/-- The weights `T` and `1` of the two standard basis vectors of `R²`. -/
noncomputable def scalingWeight : Fin 2 → GroupLike R R[T;T⁻¹] :=
  ![groupLikeT R, 1]

@[simp]
theorem scalingWeight_zero : scalingWeight R 0 = groupLikeT R :=
  (rfl)

@[simp]
theorem scalingWeight_one : scalingWeight R 1 = 1 :=
  (rfl)

/-- The coefficient matrix `diag(T, 1)` of the representation `t • (u, v) = (t u, v)`. -/
private noncomputable def scalingMatrix : Matrix (Fin 2) (Fin 2) R[T;T⁻¹] :=
  Matrix.diagonal fun i ↦ (scalingWeight R i).val

/-- The diagonal matrix of group-like elements `diag(T, 1)` is multiplicative. -/
private theorem map_comul_scalingMatrix :
    (scalingMatrix R).map (Bialgebra.comulAlgHom R R[T;T⁻¹]) =
      (scalingMatrix R).map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        (scalingMatrix R).map (Algebra.TensorProduct.includeRight (R := R)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalingMatrix, scalingWeight, Matrix.mul_apply, Fin.sum_univ_two, comul_T,
      Algebra.TensorProduct.one_def]

/-- The counit sends `diag(T, 1)` to the identity matrix. -/
private theorem counit_scalingMatrix (i j : Fin 2) :
    Coalgebra.counit (R := R) (scalingMatrix R i j) =
      (Pi.basisFun R (Fin 2)).repr ((Pi.basisFun R (Fin 2)) j) i := by
  fin_cases i <;> fin_cases j <;> simp [scalingMatrix, scalingWeight, counit_T]

/-- The representation of `𝔾ₘ` on `R²` in which a point `t` acts by `(u, v) ↦ (t u, v)`: the
first standard basis vector has weight `T` and the second has weight `1`. Install it with
`attribute [local instance] TauCeti.MultiplicativeGroup.scalingComodule`. -/
@[instance_reducible]
noncomputable def scalingComodule : Comodule R R[T;T⁻¹] (Fin 2 → R) :=
  matrixComodule R (scalingMatrix R) (map_comul_scalingMatrix R) (counit_scalingMatrix R)

attribute [local instance] scalingComodule

/-- The `i`-th standard basis vector of `R²` has weight `scalingWeight R i`. -/
theorem single_mem_weightSpace (i : Fin 2) :
    (Pi.single i 1 : Fin 2 → R) ∈ GroupLike.weightSpace (M := Fin 2 → R) (scalingWeight R i) := by
  rw [GroupLike.mem_weightSpace, scalingComodule, matrixComodule_coact, ← Pi.basisFun_apply,
    matrixCoact_apply_basisFun, Fin.sum_univ_two]
  fin_cases i <;> simp [scalingMatrix]

/-- A rational point `t` of `𝔾ₘ` acts on `R²` by `(u, v) ↦ (t u, v)`. -/
theorem basePointsRepresentation_pointsMulEquiv_symm (t : Rˣ) (v : Fin 2 → R) :
    basePointsRepresentation (H := R[T;T⁻¹]) (Fin 2 → R) (pointsMulEquiv.symm t) v =
      ![t * v 0, v 1] := by
  have hv : v = v 0 • (Pi.single 0 1 : Fin 2 → R) + v 1 • Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp
  rw [hv, map_add, map_smul, map_smul,
    basePointsRepresentation_apply_of_mem_weightSpace _ (single_mem_weightSpace R 0),
    basePointsRepresentation_apply_of_mem_weightSpace _ (single_mem_weightSpace R 1)]
  ext i
  fin_cases i <;> simp [scalingWeight, mul_comm]

/-- The standard basis vectors are unimodular. -/
theorem isUnimodular_single (i : Fin 2) : Module.IsUnimodular R (Pi.single i 1 : Fin 2 → R) :=
  Module.isUnimodular_of_apply_eq_one (f := LinearMap.proj i) (by simp)

/-- The vector `(1, 1)` is unimodular. -/
theorem isUnimodular_one : Module.IsUnimodular R (1 : Fin 2 → R) :=
  Module.isUnimodular_of_apply_eq_one (f := LinearMap.proj 0) (by simp)

/-- The matrix coefficients of `(1, 1)`: `φ ↦ φ(1, 0) T + φ(0, 1)`. These are the orbit
coordinates of `[1 : 1]` on linear forms. -/
theorem matrixCoefficient_one (φ : Module.Dual R (Fin 2 → R)) :
    matrixCoefficient (C := R[T;T⁻¹]) φ (1 : Fin 2 → R) =
      φ (Pi.single 0 1) • T 1 + φ (Pi.single 1 1) • 1 := by
  have h1 : (1 : Fin 2 → R) = Pi.single 0 1 + Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp
  rw [h1, matrixCoefficient_add,
    GroupLike.matrixCoefficient_of_mem_weightSpace (single_mem_weightSpace R 0),
    GroupLike.matrixCoefficient_of_mem_weightSpace (single_mem_weightSpace R 1)]
  simp

/-- After identifying the forms on `R²` with `R[X₀, X₁]` through the dual basis, the orbit
coordinates of `(1, 1)` are the dehomogenization `f ↦ f(T, 1)`. -/
theorem orbitCoordinates_one_comp_map_toDual :
    (orbitCoordinates (H := R[T;T⁻¹]) (1 : Fin 2 → R)).comp
        (SymmetricAlgebra.map R (Pi.basisFun R (Fin 2)).toDual) =
      Polynomial.toLaurentAlg.comp (AlgebraicGeometry.projectiveLine.dehomogenize R 1) := by
  refine SymmetricAlgebra.algHom_ext ((Pi.basisFun R (Fin 2)).ext fun i ↦ ?_)
  have hX := AlgebraicGeometry.projectiveLine.dehomogenize_coord_rev R 1
  rw [show (1 : Fin 2).rev = 0 by simp] at hX
  have hdual (i' j : Fin 2) : (Pi.basisFun R (Fin 2)).toDual (Pi.single i' 1) (Pi.single j 1) =
      if i' = j then 1 else 0 := by
    simpa using (Pi.basisFun R (Fin 2)).toDual_apply i' j
  simp only [LinearMap.coe_comp, LinearMap.coe_ofClass, AlgHom.coe_comp, Function.comp_apply,
    SymmetricAlgebra.map_apply_ι, orbitCoordinates_ι, Polynomial.coe_toLaurentAlg]
  rw [matrixCoefficient_one, Pi.basisFun_apply,
    AlgebraicGeometry.projectiveLine.ι_eq_smul_coord_add_smul_coord R 1 (Pi.single i 1)]
  fin_cases i <;> simp [hX, hdual]

/-- No nonzero form vanishes on the orbit coordinates of `(1, 1)`. -/
theorem eq_zero_of_orbitCoordinates_one_eq_zero {n : ℕ}
    {s : SymmetricAlgebra R (Module.Dual R (Fin 2 → R))}
    (hs : s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Module.Dual R (Fin 2 → R)) n)
    (h : orbitCoordinates (H := R[T;T⁻¹]) (1 : Fin 2 → R) s = 0) : s = 0 := by
  let e := (Pi.basisFun R (Fin 2)).toDualEquiv
  set s' := SymmetricAlgebra.map R e.symm.toLinearMap s
  have hs' : s' ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R) n :=
    TauCeti.SymmetricAlgebra.map_mem_homogeneousSubmodule _ hs
  have hss' : SymmetricAlgebra.map R e.toLinearMap s' = s :=
    SymmetricAlgebra.map_rightInverse R (f := e.toLinearMap) (g := e.symm.toLinearMap)
      e.apply_symm_apply s
  have hcomp := AlgHom.congr_fun (orbitCoordinates_one_comp_map_toDual R) s'
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at hcomp
  -- `toDualEquiv` and `toDual` have the same underlying linear map.
  change orbitCoordinates (H := R[T;T⁻¹]) (1 : Fin 2 → R)
    (SymmetricAlgebra.map R e.toLinearMap s') = _ at hcomp
  rw [hss', h, eq_comm, Polynomial.toLaurentAlg_apply,
    map_eq_zero_iff _ Polynomial.toLaurent_injective,
    AlgebraicGeometry.projectiveLine.dehomogenize_eq_zero_iff R 1 hs'] at hcomp
  rw [← hss', hcomp, map_zero]

variable [IsDomain R]

/-- The orbit of `[1 : 1]` is dense in the projective line. -/
theorem dense_range_projectiveOrbitMap_one :
    Dense (Set.range (projectiveOrbitMap (H := R[T;T⁻¹]) (1 : Fin 2 → R) (isUnimodular_one R))) :=
  dense_range_projectiveOrbitMap _ _ fun _ _ _ hs ↦ eq_zero_of_orbitCoordinates_one_eq_zero R hs

end Ring

section Field

variable (k : Type u) [Field k]

attribute [local instance] scalingComodule

/-- The orbits of the two lines `[1 : 0]` and `[0 : 1]` spanned by the standard basis vectors are
single points: these lines are fixed by the whole group scheme. -/
theorem range_projectiveOrbitMap_single (i : Fin 2) :
    Set.range (projectiveOrbitMap (H := k[T;T⁻¹]) (Pi.single i 1) (isUnimodular_single k i)) =
      {projectiveOrbitMap (H := k[T;T⁻¹]) (Pi.single i 1) (isUnimodular_single k i)
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k k[T;T⁻¹]))} :=
  range_projectiveOrbitMap_of_mem_weightSpace (single_mem_weightSpace k i) _

/-- The orbits of `[1 : 0]` and `[0 : 1]` are closed. -/
theorem isClosed_range_projectiveOrbitMap_single (i : Fin 2) :
    IsClosed (Set.range
      (projectiveOrbitMap (H := k[T;T⁻¹]) (Pi.single i 1) (isUnimodular_single k i))) := by
  rw [range_projectiveOrbitMap_single, ← mem_closedPoints_iff]
  exact projectiveOrbitMap_kernelPoint_mem_closedPoints _ _ _

/-- The fixed points `[1 : 0]` and `[0 : 1]` are not on the orbit of `[1 : 1]`. -/
theorem projectiveOrbitMap_single_notMem_range_one (i : Fin 2) :
    projectiveOrbitMap (H := k[T;T⁻¹]) (Pi.single i 1) (isUnimodular_single k i)
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k k[T;T⁻¹])) ∉
      Set.range (projectiveOrbitMap (H := k[T;T⁻¹]) (1 : Fin 2 → k) (isUnimodular_one k)) := by
  -- The coordinate of the other basis vector vanishes at `[eᵢ]`, and its orbit coordinate
  -- along `(1, 1)` is the unit `T` or `1`.
  set φ : Module.Dual k (Fin 2 → k) := LinearMap.proj i.rev
  have hφ := SymmetricAlgebra.ι_mem_homogeneousSubmodule k (Module.Dual k (Fin 2 → k)) φ
  refine notMem_range_projectiveOrbitMap_of_isUnit _ _ one_pos hφ ?_ ?_
  · rw [orbitCoordinates_ι, matrixCoefficient_one]
    fin_cases i
    · simp [φ]
    · simpa [φ] using isUnit_T 1
  · rw [mem_projectiveOrbitMap_iff _ _ _ one_pos hφ, orbitCoordinates_ι,
      GroupLike.matrixCoefficient_of_mem_weightSpace (single_mem_weightSpace k i)]
    fin_cases i <;> simp [φ]

/-- The orbit of `[1 : 1]` is not closed. -/
theorem not_isClosed_range_projectiveOrbitMap_one :
    ¬ IsClosed
      (Set.range (projectiveOrbitMap (H := k[T;T⁻¹]) (1 : Fin 2 → k) (isUnimodular_one k))) := by
  intro h
  apply projectiveOrbitMap_single_notMem_range_one k 0
  rw [← h.closure_eq, (dense_range_projectiveOrbitMap_one k).closure_eq]
  trivial

/-- After identifying the projective line of lines in `k²` with the standard projective line
`Proj k[X₀, X₁]` through the dual basis, the orbit morphism of `[1 : 1]` is the localization
`Spec k[T, T⁻¹] ⟶ Spec k[X]` followed by the standard chart `D₊(X₁)`. -/
theorem projectiveOrbitMap_one_comp_symmetricAlgebraMapIso_hom :
    projectiveOrbitMap (H := k[T;T⁻¹]) (1 : Fin 2 → k) (isUnimodular_one k) ≫
        (Proj.symmetricAlgebraMapIso k (Pi.basisFun k (Fin 2)).toDualEquiv).hom =
      Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial k →+* k[T;T⁻¹])) ≫
        AlgebraicGeometry.projectiveLine.polynomialChartι k 1 := by
  have hcongr {X : Scheme.{u}} (f g : SymmetricAlgebra k (Fin 2 → k) →+* Γ(X, ⊤))
      (hf : (HomogeneousIdeal.irrelevant
        (SymmetricAlgebra.homogeneousSubmodule k (Fin 2 → k))).toIdeal.map f = ⊤)
      (hg : (HomogeneousIdeal.irrelevant
        (SymmetricAlgebra.homogeneousSubmodule k (Fin 2 → k))).toIdeal.map g = ⊤)
      (h : f = g) :
      Proj.fromOfGlobalSections _ f hf = Proj.fromOfGlobalSections _ g hg := by
    subst h
    rfl
  set f := (Polynomial.toLaurent : Polynomial k →+* k[T;T⁻¹]).comp
    (AlgebraicGeometry.projectiveLine.dehomogenize k 1).toRingHom
  have hθ : (orbitCoordinates (H := k[T;T⁻¹]) (1 : Fin 2 → k)).toRingHom.comp
      (SymmetricAlgebra.gradedMap k (Pi.basisFun k (Fin 2)).toDualEquiv.toLinearMap).toRingHom =
      f := by
    refine RingHom.ext fun s ↦ ?_
    rw [RingHom.comp_apply, GradedRingHom.coe_toRingHom, SymmetricAlgebra.gradedMap_apply]
    exact AlgHom.congr_fun (orbitCoordinates_one_comp_map_toDual k) s
  have hu : IsUnit (f (AlgebraicGeometry.projectiveLine.coord k 1)) := by
    simp [f, AlgebraicGeometry.projectiveLine.dehomogenize_coord_self]
  have hirr : (HomogeneousIdeal.irrelevant
      (SymmetricAlgebra.homogeneousSubmodule k (Fin 2 → k))).toIdeal.map f = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _
      (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos
        (AlgebraicGeometry.projectiveLine.coord_mem k 1))) hu
  rw [Proj.symmetricAlgebraMapIso_hom, projectiveOrbitMap_def, Proj.fromOfGlobalSections_map,
    hcongr _ ((Scheme.ΓSpecIso (.of k[T;T⁻¹])).inv.hom.comp f) _
      (by rw [← Ideal.map_map, hirr, Ideal.map_top]) (by rw [RingHom.comp_assoc, ← hθ]),
    Proj.fromOfGlobalSections_Spec_eq_awayLift f hirr one_pos
      (AlgebraicGeometry.projectiveLine.coord_mem k 1) hu,
    AlgebraicGeometry.projectiveLine.polynomialChartι_def, ← Spec.map_comp_assoc]
  congr 2
  ext z
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _
    (AlgebraicGeometry.projectiveLine.coord_mem k 1) z
  simp [f, HomogeneousLocalization.Away.lift_mk,
    AlgebraicGeometry.projectiveLine.awayEquivPolynomial_mk,
    AlgebraicGeometry.projectiveLine.dehomogenize_coord_self]

/-- On the standard projective line, the fixed point `[eᵢ]` lies off the chart `D₊(X_{1-i})`. -/
private theorem symmetricAlgebraMapIso_hom_single_notMem_range (i : Fin 2) :
    (Proj.symmetricAlgebraMapIso k (Pi.basisFun k (Fin 2)).toDualEquiv).hom
        (projectiveOrbitMap (H := k[T;T⁻¹]) (Pi.single i 1) (isUnimodular_single k i)
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k k[T;T⁻¹]))) ∉
      Set.range (AlgebraicGeometry.projectiveLine.polynomialChartι k i.rev) := by
  rw [← Scheme.Hom.coe_opensRange, AlgebraicGeometry.projectiveLine.opensRange_polynomialChartι,
    SetLike.mem_coe, ← Scheme.Hom.mem_preimage, Proj.symmetricAlgebraMapIso_hom,
    Proj.map_preimage_basicOpen, Proj.mem_basicOpen, not_not, SymmetricAlgebra.gradedMap_apply]
  refine (mem_projectiveOrbitMap_iff (H := k[T;T⁻¹]) _ _ _
    (s := SymmetricAlgebra.map k (Pi.basisFun k (Fin 2)).toDualEquiv.toLinearMap
      (AlgebraicGeometry.projectiveLine.coord k i.rev)) one_pos
    (SymmetricAlgebra.map_mem_homogeneousSubmodule _
      (AlgebraicGeometry.projectiveLine.coord_mem k i.rev))).mpr ?_
  have hcoord : AlgebraicGeometry.projectiveLine.coord k i.rev =
      SymmetricAlgebra.ι k (Fin 2 → k) (Pi.single i.rev 1) := by
    fin_cases i <;> simp [AlgebraicGeometry.projectiveLine.ι_eq_smul_coord_add_smul_coord k 0]
  rw [hcoord, SymmetricAlgebra.map_apply_ι, orbitCoordinates_ι,
    GroupLike.matrixCoefficient_of_mem_weightSpace (single_mem_weightSpace k i)]
  fin_cases i
  · simpa using (Pi.basisFun k (Fin 2)).toDual_apply 1 0
  · simpa using (Pi.basisFun k (Fin 2)).toDual_apply 0 1

/-- The orbit of `[1 : 1]` consists of all points of the projective line except the two fixed
points `[1 : 0]` and `[0 : 1]`, nonclosed points included. -/
theorem range_projectiveOrbitMap_one :
    Set.range (projectiveOrbitMap (H := k[T;T⁻¹]) (1 : Fin 2 → k) (isUnimodular_one k)) =
      {projectiveOrbitMap (H := k[T;T⁻¹]) (Pi.single 0 1) (isUnimodular_single k 0)
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k k[T;T⁻¹])),
        projectiveOrbitMap (H := k[T;T⁻¹]) (Pi.single 1 1) (isUnimodular_single k 1)
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k k[T;T⁻¹]))}ᶜ := by
  set e := Proj.symmetricAlgebraMapIso k (Pi.basisFun k (Fin 2)).toDualEquiv
  have he : Function.Injective e.hom := (Scheme.homeoOfIso e).injective
  refine subset_antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨y, rfl⟩ (h | h)
    · exact projectiveOrbitMap_single_notMem_range_one k 0 ⟨y, h⟩
    · exact projectiveOrbitMap_single_notMem_range_one k 1 ⟨y, h⟩
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
  have hcover :=
    AlgebraicGeometry.projectiveLine.range_polynomialChartι_union_range_polynomialChartι k
  by_cases h0 : e.hom x ∈ Set.range (AlgebraicGeometry.projectiveLine.polynomialChartι k 0)
  swap
  · -- Off the chart `D₊(X₀)` there is only the point at infinity, which is `[e₁]`.
    have h1 := symmetricAlgebraMapIso_hom_single_notMem_range k 1
    rw [show (1 : Fin 2).rev = 0 by simp] at h1
    rw [← Set.mem_compl_iff, AlgebraicGeometry.projectiveLine.compl_range_polynomialChartι] at h0 h1
    exact (hx.2 (he (h0.trans h1.symm))).elim
  by_cases h1 : e.hom x ∈ Set.range (AlgebraicGeometry.projectiveLine.polynomialChartι k 1)
  swap
  · -- Off the chart `D₊(X₁)` there is only the origin of `D₊(X₀)`, which is `[e₀]`.
    have hV {y : AlgebraicGeometry.projectiveLine k}
        (hy : y ∉ Set.range (AlgebraicGeometry.projectiveLine.polynomialChartι k 1)) :
        ∃ r : PrimeSpectrum k, AlgebraicGeometry.projectiveLine.polynomialChartι k 0
          (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : k)) r) = y := by
      have hy' : y ∈ Set.range (AlgebraicGeometry.projectiveLine.polynomialChartι k 0) ∪
          Set.range (AlgebraicGeometry.projectiveLine.polynomialChartι k 1) := by
        rw [hcover]
        trivial
      obtain ⟨q, rfl⟩ := hy'.resolve_right hy
      have hq : Polynomial.X ∈ q.asIdeal := not_not.mp fun h ↦ hy <| by
        simpa using (AlgebraicGeometry.projectiveLine.polynomialChartι_mem_range_iff k 0 q).mpr h
      obtain ⟨r, hr⟩ := (Set.ext_iff.mp (Polynomial.range_comap_evalRingHom_zero k) q).mpr hq
      exact ⟨r, congrArg _ hr⟩
    obtain ⟨r, hr⟩ := hV h1
    obtain ⟨r', hr'⟩ := hV (symmetricAlgebraMapIso_hom_single_notMem_range k 0)
    rw [Subsingleton.elim r r'] at hr
    exact (hx.1 (he (hr.symm.trans hr'))).elim
  obtain ⟨q, hq⟩ := h1
  rw [← hq] at h0
  have hX : Polynomial.X ∉ q.asIdeal :=
    (AlgebraicGeometry.projectiveLine.polynomialChartι_mem_range_iff k 1 q).mp (by simpa using h0)
  obtain ⟨p, hp⟩ : q ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (Polynomial k) k[T;T⁻¹])) := by
    rw [PrimeSpectrum.localization_away_comap_range k[T;T⁻¹] Polynomial.X]
    exact hX
  exact ⟨p, he ((congrArg (fun f ↦ f p)
    (projectiveOrbitMap_one_comp_symmetricAlgebraMapIso_hom k)).trans
      ((congrArg _ hp).trans hq))⟩

/-- The boundary of the orbit of `[1 : 1]` consists exactly of the two fixed points `[1 : 0]`
and `[0 : 1]`. -/
theorem closure_diff_range_projectiveOrbitMap_one :
    closure (Set.range (projectiveOrbitMap (H := k[T;T⁻¹]) (1 : Fin 2 → k) (isUnimodular_one k))) \
        Set.range (projectiveOrbitMap (H := k[T;T⁻¹]) (1 : Fin 2 → k) (isUnimodular_one k)) =
      {projectiveOrbitMap (H := k[T;T⁻¹]) (Pi.single 0 1) (isUnimodular_single k 0)
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k k[T;T⁻¹])),
        projectiveOrbitMap (H := k[T;T⁻¹]) (Pi.single 1 1) (isUnimodular_single k 1)
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k k[T;T⁻¹]))} := by
  rw [(dense_range_projectiveOrbitMap_one k).closure_eq, range_projectiveOrbitMap_one,
    ← Set.compl_eq_univ_sdiff, compl_compl]

end Field

end TauCeti.MultiplicativeGroup
