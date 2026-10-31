/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.HomogeneousIdeal
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.LocallyClosed
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.FromMatrix
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Semilinear

/-!
# Orbits of the multiplicative group on the projective line

Let `𝔾ₘ = Spec R[T, T⁻¹]` act on `R²` by `t • (u, v) = (t u, v)`, and hence on the projective
line `ℙ¹ = ℙ(R²)` by `t • [u : v] = [t u : v]`. This file computes the orbits of this action, as
the full images of the projective orbit morphisms `𝔾ₘ ⟶ ℙ¹`, nonclosed points included. Over a
field `k`:

* the lines `[1 : 0]` and `[0 : 1]` through the two standard basis vectors are fixed by the whole
  group scheme, so their orbits are single points, which are closed when `k` is algebraically
  closed;
* the orbit of `[1 : 1]` is dense in `ℙ¹` (over any domain) but misses both fixed points, so it is
  not closed;
* when `k` is algebraically closed, the boundary of that orbit, its closure minus the orbit, is
  exactly the two fixed points.

This is the standard example of the closed-orbit lemma: the open orbit has a boundary made of
orbits of smaller dimension, and these are closed. Over `ℂ` the open orbit is `ℂ*`, embedded as
`t ↦ [t : 1]`, and its boundary is the two closed fixed points `0` and `∞`.

The fixed points are lines spanned by weight vectors. The orbit of `[1 : 1]` is dense because its
orbit coordinates satisfy no homogeneous relation: after identifying the forms on `R²` with
`R[X₀, X₁]`, they are the dehomogenization `f ↦ f(T, 1)`, which is injective on forms of each
degree. The boundary is computed from its closed points, using that it is closed and that the
projective line over a field is a Jacobson space.

## Main declarations

* `TauCeti.MultiplicativeGroup.scalingComodule`: the representation `t • (u, v) = (t u, v)` of
  `𝔾ₘ` on `R²`, over any commutative ring.
* `TauCeti.MultiplicativeGroup.range_projectiveOrbitMap_single`: the orbits of `[1 : 0]` and
  `[0 : 1]` are single points.
* `TauCeti.MultiplicativeGroup.isClosed_range_projectiveOrbitMap_single`: these orbits are closed.
* `TauCeti.MultiplicativeGroup.dense_range_projectiveOrbitMap_one`: the orbit of `[1 : 1]` is
  dense.
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

/-- The coordinate `T` of `𝔾ₘ`, as a group-like element of `R[T, T⁻¹]`. -/
noncomputable def groupLikeT : GroupLike R R[T;T⁻¹] :=
  ⟨T 1, ⟨by simp [counit_T], comul_T 1⟩⟩

@[simp]
theorem groupLikeT_val : (groupLikeT R).val = T 1 :=
  (rfl)

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
noncomputable def scalingMatrix : Matrix (Fin 2) (Fin 2) R[T;T⁻¹] :=
  Matrix.diagonal fun i ↦ (scalingWeight R i).val

/-- The diagonal matrix of group-like elements `diag(T, 1)` is multiplicative. -/
theorem map_comul_scalingMatrix :
    (scalingMatrix R).map (Bialgebra.comulAlgHom R R[T;T⁻¹]) =
      (scalingMatrix R).map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        (scalingMatrix R).map (Algebra.TensorProduct.includeRight (R := R)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalingMatrix, scalingWeight, Matrix.mul_apply, Fin.sum_univ_two, comul_T,
      Algebra.TensorProduct.one_def]

/-- The counit sends `diag(T, 1)` to the identity matrix. -/
theorem counit_scalingMatrix (i j : Fin 2) :
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
  rw [show (1 : Fin 2).rev = 0 from rfl] at hX
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

variable [IsAlgClosed k]

/-- Over an algebraically closed field the orbits of `[1 : 0]` and `[0 : 1]` are closed. -/
theorem isClosed_range_projectiveOrbitMap_single (i : Fin 2) :
    IsClosed (Set.range
      (projectiveOrbitMap (H := k[T;T⁻¹]) (Pi.single i 1) (isUnimodular_single k i))) := by
  rw [range_projectiveOrbitMap_single, ← mem_closedPoints_iff,
    ProjectiveSpectrum.mem_closedPoints_iff_exists_projectiveOrbitMap_eq (H := k[T;T⁻¹])]
  exact ⟨_, _, rfl⟩

/-- Over an algebraically closed field, a closed point of the projective line off the orbit of
`[1 : 1]` is one of the fixed points `[1 : 0]` and `[0 : 1]`: every other closed point is the line
through some `(t, 1)` with `t ≠ 0`, the image of the rational point `t`. -/
theorem eq_or_eq_of_mem_closedPoints_of_notMem_range_one
    {x : Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (Fin 2 → k)))}
    (hx : x ∈ closedPoints _)
    (hxR : x ∉ Set.range
      (projectiveOrbitMap (H := k[T;T⁻¹]) (1 : Fin 2 → k) (isUnimodular_one k))) :
    x = projectiveOrbitMap (H := k[T;T⁻¹]) (Pi.single 0 1) (isUnimodular_single k 0)
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k k[T;T⁻¹])) ∨
      x = projectiveOrbitMap (H := k[T;T⁻¹]) (Pi.single 1 1) (isUnimodular_single k 1)
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k k[T;T⁻¹])) := by
  have hone : (1 : WithConv (k[T;T⁻¹] →ₐ[k] k)).ofConv = Bialgebra.counitAlgHom k k[T;T⁻¹] := by
    rw [AlgHom.convOne_def, Algebra.ofId_self, AlgHom.id_comp]
  -- Lines that coincide have the same image under the identity point.
  have hline {v w : Fin 2 → k} (hv : Module.IsUnimodular k v) (hw : Module.IsUnimodular k w)
      (h : k ∙ v = k ∙ w) :
      projectiveOrbitMap (H := k[T;T⁻¹]) v hv
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k k[T;T⁻¹])) =
        projectiveOrbitMap (H := k[T;T⁻¹]) w hw
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k k[T;T⁻¹])) := by
    rw [← hone, projectiveOrbitMap_kernelPoint_eq_iff_span_eq]
    simpa using h
  obtain ⟨v, hv, rfl⟩ :=
    (ProjectiveSpectrum.mem_closedPoints_iff_exists_projectiveOrbitMap_eq (H := k[T;T⁻¹]) x).mp hx
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨f, hf⟩ := Module.isUnimodular_iff.mp hv
    simp at hf
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := fun h1 ↦ hv0 (funext fun i ↦ by fin_cases i <;> simp [h0, h1])
    refine Or.inr (hline _ _ ?_)
    have hv' : v = v 1 • Pi.single 1 1 := funext fun i ↦ by fin_cases i <;> simp [h0]
    rw [hv', Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr h1)]
  by_cases h1 : v 1 = 0
  · refine Or.inl (hline _ _ ?_)
    have hv' : v = v 0 • Pi.single 0 1 := funext fun i ↦ by fin_cases i <;> simp [h1]
    rw [hv', Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr h0)]
  refine (hxR ⟨AlgHom.kernelPoint
    ((pointsMulEquiv (R := k) (A := k)).symm (Units.mk0 (v 0 / v 1) (by simp [h0, h1]))).ofConv,
    ?_⟩).elim
  rw [← hone, projectiveOrbitMap_kernelPoint_eq_iff_span_eq,
    basePointsRepresentation_pointsMulEquiv_symm, map_one, Module.End.one_apply,
    ← Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero h1)) v]
  congr 2
  funext i
  fin_cases i <;> simp [div_eq_inv_mul, h1]

/-- Over an algebraically closed field, the boundary of the orbit of `[1 : 1]` consists exactly
of the two fixed points `[1 : 0]` and `[0 : 1]`. -/
theorem closure_diff_range_projectiveOrbitMap_one :
    closure (Set.range (projectiveOrbitMap (H := k[T;T⁻¹]) (1 : Fin 2 → k) (isUnimodular_one k))) \
        Set.range (projectiveOrbitMap (H := k[T;T⁻¹]) (1 : Fin 2 → k) (isUnimodular_one k)) =
      {projectiveOrbitMap (H := k[T;T⁻¹]) (Pi.single 0 1) (isUnimodular_single k 0)
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k k[T;T⁻¹])),
        projectiveOrbitMap (H := k[T;T⁻¹]) (Pi.single 1 1) (isUnimodular_single k 1)
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k k[T;T⁻¹]))} := by
  have : JacobsonSpace (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k
      (Module.Dual k (Fin 2 → k)))) :=
    LocallyOfFiniteType.jacobsonSpace (TauCeti.SymmetricAlgebra.projToSpec k _)
  refine subset_antisymm ?_ ?_
  · -- The boundary is closed, hence the closure of its closed points, which are the two fixed
    -- points; and these form a closed set.
    rw [← JacobsonSpace.closure_inter_closedPoints
      (isClosed_closure_diff_range_projectiveOrbitMap _ (isUnimodular_one k))]
    refine closure_minimal (fun x ⟨⟨_, hxR⟩, hx⟩ ↦
      eq_or_eq_of_mem_closedPoints_of_notMem_range_one k hx hxR) ?_
    rw [Set.insert_eq, ← range_projectiveOrbitMap_single, ← range_projectiveOrbitMap_single]
    exact (isClosed_range_projectiveOrbitMap_single k 0).union
      (isClosed_range_projectiveOrbitMap_single k 1)
  · rintro _ (rfl | rfl)
    · exact ⟨(dense_range_projectiveOrbitMap_one k).closure_eq ▸ trivial,
        projectiveOrbitMap_single_notMem_range_one k 0⟩
    · exact ⟨(dense_range_projectiveOrbitMap_one k).closure_eq ▸ trivial,
        projectiveOrbitMap_single_notMem_range_one k 1⟩

end Field

end TauCeti.MultiplicativeGroup
