/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Basic
public import TauCeti.Analysis.Complex.Fuchsian.TriangleOrder.Group
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation
import TauCeti.Analysis.Complex.UpperHalfPlane.Rho

/-!
# The level-one modular group as the triangle group `Δ(3, 2, ∞)`

Let `ρ = e^{2πi/3}`. The hyperbolic triangle `ModularGroup.triangle` with vertices `ρ`, `i` and
the ideal vertex `∞`, listed counterclockwise, is the left half of the standard fundamental
domain of the modular group. Its angles are `π / 3` at `ρ`, `π / 2` at `i` and `0` at `∞`.

Its sides lie on the unit circle, the imaginary axis and the vertical line `Re z = -1/2`. The
products of the reflections in consecutive sides are the vertex transformations
`S T : z ↦ -1 / (z + 1)` at `ρ`, `S : z ↦ -1 / z` at `i`, and `T⁻¹ : z ↦ z - 1` at `∞`. Since
`S` and `T` generate `SL(2, ℤ)`, the triangle group of this triangle is the image of `PSL(2, ℤ)`
in `PSL(2, ℝ)`.

Poincaré's polygon theorem for triangle groups then gives the classical presentation of the
modular group from its fundamental polygon:

`PSL(2, ℤ) ≅ Δ(3, 2, ∞) = ⟨x, y, z | x ^ 3, y ^ 2, z * y * x⟩`,

with `x ↦ S T`, `y ↦ S` and `z ↦ T⁻¹`; the cusp entry `∞` is encoded by the exponent `0`, which
imposes no relation. The typed angle triple `(3, 2, ∞)` also counts the elliptic orbits of the
level-one group from the polygon: there are exactly two, the orbits of `ρ` and `i`.

## Main declarations

* `TauCeti.ModularGroup.triangle`: the triangle with vertices `ρ`, `i`, `∞`.
* `TauCeti.ModularGroup.interiorAngle_triangle_zero`, `interiorAngle_triangle_one` and
  `interiorAngle_triangle_two`: its angles `π / 3`, `π / 2` and `0`.
* `TauCeti.ModularGroup.vertexReflectionComp_triangle_zero`,
  `vertexReflectionComp_triangle_one` and `vertexReflectionComp_triangle_two`: its vertex
  transformations are the images of `S T`, `S` and `T⁻¹`.
* `TauCeti.ModularGroup.triangleGroup_triangle`: its triangle group is the effective level-one
  group `psl2zToPSL2R.range`.
* `TauCeti.ModularGroup.triangleGroupEquiv`: the presentation `Δ(3, 2, ∞) ≃* PSL(2, ℤ)`.
* `TauCeti.ModularGroup.natCard_ellipticOrbits_psl2zToPSL2RRange`: the effective level-one group
  has two elliptic orbits.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91, Springer,
  1983, §10.6 (triangle groups).
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §4.3 (Poincaré's theorem and the signature).
* Jean-Pierre Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer,
  1973, Chapter VII, §1 (the generators `S`, `T` and the fundamental domain).
-/

public section

noncomputable section

open MulAction UpperHalfPlane
open Matrix.ProjectiveSpecialLinearGroup (upperRightHom)
open TauCeti.UpperHalfPlane
open scoped MatrixGroups OnePoint Real

namespace TauCeti.ModularGroup

/-! ### The triangle with vertices `ρ`, `i`, `∞` -/

private theorem ρ_ne_infty : (.inl ρ : ℍ ⊕ OnePoint ℝ) ≠ .inr ∞ := Sum.inl_ne_inr

private theorem I_ne_infty : (.inl I : ℍ ⊕ OnePoint ℝ) ≠ .inr ∞ := Sum.inl_ne_inr

private theorem ρ_ne_I : (.inl ρ : ℍ ⊕ OnePoint ℝ) ≠ .inl I :=
  fun h ↦ I_ne_ρ (Sum.inl_injective h).symm

private theorem re_ρ_lt_re_I : (toComplex (.inl ρ)).re < (toComplex (.inl I)).re := by
  norm_num [UpperHalfPlane.ρ, UpperHalfPlane.I]

private theorem normSq_ρ : Complex.normSq (toComplex (.inl ρ) - ((0 : ℝ) : ℂ)) = 1 ^ 2 := by
  rw [toComplex_inl, Complex.ofReal_zero, sub_zero, Complex.normSq_eq_norm_sq, norm_ρ]

private theorem normSq_I : Complex.normSq (toComplex (.inl I) - ((0 : ℝ) : ℂ)) = 1 ^ 2 := by
  simp [UpperHalfPlane.I]

/-- **The modular triangle**: the hyperbolic triangle with vertices `ρ = e^{2πi/3}`, `i` and the
ideal vertex `∞`, listed counterclockwise. It is the left half of the standard fundamental domain
of the modular group, and its triangle group is the level-one modular group
(`TauCeti.ModularGroup.triangleGroup_triangle`). -/
def triangle : ConvexPolygon 3 :=
  ConvexPolygon.triangleInfty ρ_ne_infty I_ne_infty re_ρ_lt_re_I

/-- The vertices of the modular triangle are `ρ`, `i` and `∞`. -/
@[simp]
theorem vertex_triangle : triangle.vertex = ![.inl ρ, .inl I, .inr ∞] :=
  ConvexPolygon.vertex_triangleInfty ..

/-- The angle of the modular triangle at `ρ` is `π / 3`. -/
@[simp]
theorem interiorAngle_triangle_zero : triangle.interiorAngle 0 = π / 3 := by
  have hsub : (0 : Fin 3) - 1 = 2 := by decide
  rw [ConvexPolygon.interiorAngle_def, hsub, zero_add, vertex_triangle]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  rw [vertexAngle_infty_of_re_lt one_pos ρ_ne_infty I_ne_infty normSq_ρ normSq_I re_ρ_lt_re_I]
  have hre : (toComplex (.inl ρ : ℍ ⊕ OnePoint ℝ)).re = -Real.cos (π / 3) := by
    norm_num [UpperHalfPlane.ρ, Real.cos_pi_div_three]
  rw [hre, sub_zero, div_one, ← Real.cos_pi_sub, Real.arccos_cos (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])]
  ring

/-- The angle of the modular triangle at `i` is `π / 2`. -/
@[simp]
theorem interiorAngle_triangle_one : triangle.interiorAngle 1 = π / 2 := by
  have hadd : (1 : Fin 3) + 1 = 2 := by decide
  rw [ConvexPolygon.interiorAngle_def, sub_self, hadd, vertex_triangle]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  rw [vertexAngle_infty_of_lt_re one_pos ρ_ne_infty I_ne_infty normSq_ρ normSq_I re_ρ_lt_re_I]
  simp [UpperHalfPlane.I]

/-- The angle of the modular triangle at the ideal vertex `∞` is `0`. -/
@[simp]
theorem interiorAngle_triangle_two : triangle.interiorAngle 2 = 0 :=
  triangle.interiorAngle_eq_zero_of_vertex_eq_inr (ξ := ∞) (by simp)

/-! ### The vertex transformations -/

/-- The element `z ↦ (z - 1/2) / (z + 1/2)` of `SL(2, ℝ)`, whose geodesic line is the unit
semicircle. -/
private def unitCircleMatrix : SL(2, ℝ) :=
  ⟨!![1, -1 / 2; 1, 1 / 2], by norm_num [Matrix.det_fin_two]⟩

private theorem coe_unitCircleMatrix :
    (unitCircleMatrix : Matrix (Fin 2) (Fin 2) ℝ) = !![1, -1 / 2; 1, 1 / 2] :=
  (rfl)

/-- Conjugating `unitCircleMatrix` by `J` and dividing by it gives `-S`. -/
private theorem conjJ_unitCircleMatrix_mul_inv :
    Matrix.SpecialLinearGroup.conjJ unitCircleMatrix * unitCircleMatrix⁻¹ =
      -Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) _root_.ModularGroup.S := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      coe_unitCircleMatrix, _root_.ModularGroup.coe_S]

/-- In `PSL(2, ℝ)`, conjugating `unitCircleMatrix` by `J` and dividing by it gives `S`. -/
private theorem pslConjJ_unitCircleMatrix_mul_inv :
    pslConjJ (unitCircleMatrix : PSL(2, ℝ)) * (unitCircleMatrix : PSL(2, ℝ))⁻¹ =
      psl2zToPSL2R (_root_.ModularGroup.S : PSL(2, ℤ)) := by
  rw [pslConjJ_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, conjJ_unitCircleMatrix_mul_inv]
  simp

/-- The unit semicircle is the geodesic line of `unitCircleMatrix`. -/
private theorem mem_range_geodesicLine_unitCircleMatrix {z : ℍ} (hz : Complex.normSq z = 1) :
    z ∈ Set.range (geodesicLine (unitCircleMatrix : PSL(2, ℝ))) := by
  rw [mem_range_geodesicLine_iff_sideForm_eq_zero, sideForm_mk, hz]
  simp [unitCircleMatrix]
  ring

/-- The side of the modular triangle from `ρ` to `i` lies on the unit semicircle. -/
private theorem range_geodesicLine_sideGeodesic_zero :
    Set.range (geodesicLine (unitCircleMatrix : PSL(2, ℝ))) =
      Set.range (geodesicLine (triangle.sideGeodesic 0)) := by
  have h : IsGeodesicFromTo (triangle.sideGeodesic 0) (.inl ρ) (.inl I) := by
    simpa using triangle.isGeodesicFromTo_sideGeodesic 0
  have hρ : Complex.normSq (ρ : ℂ) = 1 := by simpa using normSq_ρ
  have hI : Complex.normSq (I : ℂ) = 1 := by simp
  exact range_geodesicLine_eq_of_mem (fun h ↦ ρ_ne_I (congrArg _ h))
    (mem_range_geodesicLine_unitCircleMatrix hρ) (mem_range_geodesicLine_unitCircleMatrix hI)
    h.left_mem_range h.right_mem_range

/-- The side of the modular triangle from `i` to `∞` lies on the imaginary axis. -/
private theorem exists_sideGeodesic_one :
    ∃ s : ℝ, triangle.sideGeodesic 1 = 1 * ↑(Matrix.SpecialLinearGroup.dilation s) := by
  have h : IsGeodesicFromTo (triangle.sideGeodesic 1) (.inl I) (.inr ∞) := by
    simpa using triangle.isGeodesicFromTo_sideGeodesic 1
  exact IsGeodesicFromTo.exists_eq_mul_dilation
    (isGeodesicFromTo_inl_inr.2 ⟨⟨0, by rw [geodesicLine_zero, one_smul]⟩, one_smul _ _⟩) h

/-- The side of the modular triangle from `∞` to `ρ` lies on the vertical line `Re z = -1/2`. -/
private theorem exists_sideGeodesic_two :
    ∃ s : ℝ, triangle.sideGeodesic 2 =
      upperRightHom (-1 / 2 : ℝ) * pslS * ↑(Matrix.SpecialLinearGroup.dilation s) := by
  have h : IsGeodesicFromTo (triangle.sideGeodesic 2) (.inr ∞) (.inl ρ) := by
    simpa using triangle.isGeodesicFromTo_sideGeodesic 2
  refine IsGeodesicFromTo.exists_eq_mul_dilation
    (isGeodesicFromTo_mul_pslS_iff.2 (isGeodesicFromTo_inl_inr.2 ⟨?_, ?_⟩)) h
  · rw [mem_range_geodesicLine_iff, ← AddChar.map_neg_eq_inv, upperRightHom_smul, vadd_re]
    norm_num [UpperHalfPlane.ρ]
  · exact Matrix.ProjectiveSpecialLinearGroup.upperRightHom_smul_infty _

/-- The transformation of the modular triangle at `i` is `S : z ↦ -1 / z`. -/
@[simp]
theorem vertexReflectionComp_triangle_one :
    triangle.vertexReflectionComp 1 = psl2zToPSL2R (_root_.ModularGroup.S : PSL(2, ℤ)) := by
  obtain ⟨s, hs⟩ := exists_sideGeodesic_one
  rw [ConvexPolygon.vertexReflectionComp_one, hs, geodesicReflectionComp_mul_dilation_left]
  rcases exists_eq_mul_dilation_or_eq_mul_pslS_mul_dilation_of_range_eq
    range_geodesicLine_sideGeodesic_zero with ⟨t, ht⟩ | ⟨t, ht⟩ <;>
  · simp only [ht, geodesicReflectionComp_mul_dilation_right, geodesicReflectionComp_mul_pslS_right]
    simpa [geodesicReflectionComp_def] using pslConjJ_unitCircleMatrix_mul_inv

/-- The transformation of the modular triangle at `∞` is `T⁻¹ : z ↦ z - 1`. -/
@[simp]
theorem vertexReflectionComp_triangle_two :
    triangle.vertexReflectionComp 2 = psl2zToPSL2R (_root_.ModularGroup.T : PSL(2, ℤ))⁻¹ := by
  obtain ⟨s, hs⟩ := exists_sideGeodesic_one
  obtain ⟨t, ht⟩ := exists_sideGeodesic_two
  rw [ConvexPolygon.vertexReflectionComp_two, hs, ht, geodesicReflectionComp_mul_dilation_left,
    geodesicReflectionComp_mul_dilation_right, geodesicReflectionComp_mul_pslS_left,
    ← AddChar.map_zero_eq_one upperRightHom, geodesicReflectionComp_upperRightHom, map_inv,
    psl2zToPSL2R_T]
  norm_num [← AddChar.map_neg_eq_inv]

/-- The transformation of the modular triangle at `ρ` is `S T : z ↦ -1 / (z + 1)`. -/
@[simp]
theorem vertexReflectionComp_triangle_zero :
    triangle.vertexReflectionComp 0 =
      psl2zToPSL2R ((_root_.ModularGroup.S : PSL(2, ℤ)) * _root_.ModularGroup.T) := by
  have h := triangle.vertexReflectionComp_two_mul_one_mul_zero
  rw [vertexReflectionComp_triangle_two, vertexReflectionComp_triangle_one, ← map_mul,
    mul_eq_one_iff_eq_inv] at h
  rw [← inv_inv (triangle.vertexReflectionComp 0), ← h, ← map_inv, mul_inv_rev, inv_inv,
    ModularGroup.S_inv_PSL2Z]

/-! ### The modular group as a triangle group -/

/-- **The level-one modular group is a triangle group.** The triangle group of the modular
triangle, generated by the products of the reflections in its sides, is the image of `PSL(2, ℤ)`
in `PSL(2, ℝ)`. -/
theorem triangleGroup_triangle : triangle.triangleGroup = psl2zToPSL2R.range := by
  refine le_antisymm ?_ ?_
  · rw [ConvexPolygon.triangleGroup_eq_closure_range_vertexReflectionComp, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨_, vertexReflectionComp_triangle_zero.symm⟩
    · exact ⟨_, vertexReflectionComp_triangle_one.symm⟩
    · exact ⟨_, vertexReflectionComp_triangle_two.symm⟩
  · rw [← range_sl2zToPSL2R_eq_range_psl2zToPSL2R, MonoidHom.range_eq_map,
      ← _root_.SpecialLinearGroup.SL2Z_generators, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, rfl | rfl, rfl⟩
    · rw [← psl2zToPSL2R_mk, ← vertexReflectionComp_triangle_one]
      exact triangle.vertexReflectionComp_mem_triangleGroup 1
    · rw [← psl2zToPSL2R_mk, ← inv_inv (_root_.ModularGroup.T : PSL(2, ℤ)), map_inv,
        ← vertexReflectionComp_triangle_two]
      exact inv_mem (triangle.vertexReflectionComp_mem_triangleGroup 2)

private theorem interiorAngle_triangle_zero_eq_angle :
    triangle.interiorAngle 0 = (TriangleOrder.elliptic 3 (by norm_num)).angle := by
  rw [interiorAngle_triangle_zero, TriangleOrder.angle_elliptic, Nat.cast_ofNat]

private theorem interiorAngle_triangle_one_eq_angle :
    triangle.interiorAngle 1 = (TriangleOrder.elliptic 2 le_rfl).angle := by
  rw [interiorAngle_triangle_one, TriangleOrder.angle_elliptic, Nat.cast_ofNat]

private theorem interiorAngle_triangle_two_eq_angle :
    triangle.interiorAngle 2 = TriangleOrder.cusp.angle := by
  rw [interiorAngle_triangle_two, TriangleOrder.angle_cusp]

/-- `S T` has order dividing `3` in `PSL(2, ℤ)`: it is the transformation at the vertex `ρ` of the
modular triangle, whose angle is `π / 3`. -/
private theorem S_mul_T_pow_three :
    ((_root_.ModularGroup.S : PSL(2, ℤ)) * _root_.ModularGroup.T) ^ 3 = 1 := by
  apply psl2zToPSL2R_injective
  have h := triangle.orderOf_vertexReflectionComp_of_interiorAngle_eq (i := 0) (m := 3)
    (by rw [interiorAngle_triangle_zero, Nat.cast_ofNat])
  rw [map_pow, map_one, ← vertexReflectionComp_triangle_zero]
  exact orderOf_dvd_iff_pow_eq_one.1 h.dvd

/-- The homomorphism `Δ(3, 2, ∞) →* PSL(2, ℤ)` sending `x`, `y`, `z` to `S T`, `S` and `T⁻¹`. -/
private def triangleGroupHom : TriangleGroup 3 2 0 →* PSL(2, ℤ) :=
  TriangleGroup.lift ((_root_.ModularGroup.S : PSL(2, ℤ)) * _root_.ModularGroup.T)
    _root_.ModularGroup.S (_root_.ModularGroup.T : PSL(2, ℤ))⁻¹ S_mul_T_pow_three
    (by rw [pow_two, ModularGroup.S_mul_S_PSL2Z]) (pow_zero _)
    (by rw [← mul_assoc, mul_assoc _ _ (_root_.ModularGroup.S : PSL(2, ℤ)),
      ModularGroup.S_mul_S_PSL2Z, mul_one, inv_mul_cancel])

/-- Poincaré's theorem for the modular triangle: `triangleGroupHom` is an isomorphism. -/
private theorem bijective_triangleGroupHom : Function.Bijective triangleGroupHom := by
  -- the triangle group of the modular triangle is presented by `Δ(p.order, q.order, r.order)`;
  -- identify these orders with `3`, `2`, `0` before comparing with `triangleGroupHom`
  suffices h : ∀ {a b c : ℕ} (_ : a = 3) (_ : b = 2) (_ : c = 0)
      (e : TriangleGroup a b c ≃* triangle.triangleGroup),
      (e (TriangleGroup.x a b c) : PSL(2, ℝ)) = triangle.vertexReflectionComp 0 →
      (e (TriangleGroup.y a b c) : PSL(2, ℝ)) = triangle.vertexReflectionComp 1 →
      Function.Bijective triangleGroupHom from
    h (TriangleOrder.order_elliptic 3 _) (TriangleOrder.order_elliptic 2 _)
      TriangleOrder.order_cusp _ (ConvexPolygon.coe_triangleGroupEquiv_x
        interiorAngle_triangle_zero_eq_angle interiorAngle_triangle_one_eq_angle
        interiorAngle_triangle_two_eq_angle)
      (ConvexPolygon.coe_triangleGroupEquiv_y interiorAngle_triangle_zero_eq_angle
        interiorAngle_triangle_one_eq_angle interiorAngle_triangle_two_eq_angle)
  intro a b c ha hb hc e hx hy
  subst ha hb hc
  have hcomp (u : TriangleGroup 3 2 0) :
      psl2zToPSL2R (triangleGroupHom u) = (e u : PSL(2, ℝ)) := by
    have : psl2zToPSL2R.comp triangleGroupHom = triangle.triangleGroup.subtype.comp e :=
      TriangleGroup.hom_ext _ _ _
        (by simp [triangleGroupHom, hx, vertexReflectionComp_triangle_zero])
        (by simp [triangleGroupHom, hy, vertexReflectionComp_triangle_one])
    exact DFunLike.congr_fun this u
  refine ⟨fun u v huv ↦ e.injective (Subtype.ext ?_), fun g ↦ ?_⟩
  · rw [← hcomp, ← hcomp, huv]
  · obtain ⟨u, hu⟩ := e.surjective ⟨psl2zToPSL2R g, triangleGroup_triangle ▸ ⟨g, rfl⟩⟩
    exact ⟨u, psl2zToPSL2R_injective (by rw [hcomp, hu])⟩

/-- **The presentation of the modular group.** `PSL(2, ℤ)` is the triangle group
`Δ(3, 2, ∞) = ⟨x, y, z | x ^ 3, y ^ 2, z * y * x⟩`, in which the cusp imposes no power relation on
`z`. The isomorphism sends `x`, `y`, `z` to `S T`, `S` and `T⁻¹`. It comes from Poincaré's polygon
theorem for the modular triangle. -/
def triangleGroupEquiv : TriangleGroup 3 2 0 ≃* PSL(2, ℤ) :=
  MulEquiv.ofBijective triangleGroupHom bijective_triangleGroupHom

/-- The presentation `Δ(3, 2, ∞) ≃* PSL(2, ℤ)` sends `x` to `S T`. -/
@[simp]
theorem triangleGroupEquiv_x :
    triangleGroupEquiv (TriangleGroup.x 3 2 0) =
      (_root_.ModularGroup.S : PSL(2, ℤ)) * _root_.ModularGroup.T :=
  TriangleGroup.lift_x ..

/-- The presentation `Δ(3, 2, ∞) ≃* PSL(2, ℤ)` sends `y` to `S`. -/
@[simp]
theorem triangleGroupEquiv_y :
    triangleGroupEquiv (TriangleGroup.y 3 2 0) = (_root_.ModularGroup.S : PSL(2, ℤ)) :=
  TriangleGroup.lift_y ..

/-- The presentation `Δ(3, 2, ∞) ≃* PSL(2, ℤ)` sends `z` to `T⁻¹`. -/
@[simp]
theorem triangleGroupEquiv_z :
    triangleGroupEquiv (TriangleGroup.z 3 2 0) = (_root_.ModularGroup.T : PSL(2, ℤ))⁻¹ :=
  TriangleGroup.lift_z ..

/-- **The elliptic orbits of the modular group**, from its triangle: the effective level-one group
has exactly two elliptic orbits, one for each finite vertex `ρ` and `i` of the modular
triangle. -/
theorem natCard_ellipticOrbits_psl2zToPSL2RRange :
    Nat.card psl2zToPSL2R.range.ellipticOrbits = 2 := by
  rw [← triangleGroup_triangle, ConvexPolygon.natCard_ellipticOrbits_triangleGroup
    interiorAngle_triangle_zero_eq_angle interiorAngle_triangle_one_eq_angle
    interiorAngle_triangle_two_eq_angle, Finset.card_filter, Fin.sum_univ_three]
  simp

end TauCeti.ModularGroup
