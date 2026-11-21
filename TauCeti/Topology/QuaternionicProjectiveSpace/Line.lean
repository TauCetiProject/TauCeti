/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.QuaternionicProjectiveSpace.Sphere4
public import TauCeti.Topology.Sphere.Suspension
public import TauCeti.Topology.MappingSpace.Evaluation

/-!
# Quaternionic projective lines and their great two-spheres

A **quaternionic two-frame** of `ℍⁿ⁺¹` (`TauCeti.QuaternionicProjectiveSpace.twoFrame`) is a pair
`(x, y)` of unit vectors with `y` orthogonal to the quaternionic line `x ℍ`. Such a frame spans a
quaternionic plane, and `(a, b) ↦ x a + y b` is a real-linear isometry from `ℍ²` onto it
(`TauCeti.QuaternionicProjectiveSpace.lineIsometry`), compatible with right multiplication by
quaternions. On projective spaces it gives the **quaternionic projective line** of the frame,

`HP¹ → HPⁿ`, `[a : b] ↦ [x a + y b]`

(`TauCeti.QuaternionicProjectiveSpace.lineMap`), jointly continuous in the frame and the point.
For each frame it is a closed embedding sending `[e₀]` to `[x]` and `[e₁]` to `[y]`.

Through `HP¹ ≃ₜ S⁴` (`TauCeti.QuaternionicProjectiveSpace.homeomorphSphere4`), the line is a
four-sphere with poles `[x]` and `[y]`. A unit imaginary quaternion `q` spans with `1` a real
plane of `ℍ`, and the great two-sphere `(s₀, s₁, s₂) ↦ (s₀, s₁ + s₂ q)` of `S⁴ ⊆ ℝ × ℍ`
(`TauCeti.QuaternionicProjectiveSpace.greatSphere4`) runs through both poles. Composing gives the
family of two-spheres

`σ : V₂(ℍⁿ⁺¹) × S(Im ℍ) → Map(S², HPⁿ)`

(`TauCeti.QuaternionicProjectiveSpace.lineSphereFamily`): `σ (x, y, q)` is the great two-sphere of
the quaternionic line through `[x]` and `[y]` consisting of `[y]` and the points `[x + y z]` with
`z` in the real plane spanned by `1` and `q`. Every such sphere is injective, sends the north pole
of `S²` to `[x]` and the south pole to `[y]`, so the family lies over `HPⁿ` through evaluation at
the north pole. Replacing `(x, y, q)` by `(x c, y c, c* q c)` for a unit quaternion `c`, with
conjugate `c* = star c`, does not change the sphere
(`TauCeti.QuaternionicProjectiveSpace.lineSphereFamily_eq_of_op_smul`), so the family descends to
the space of orthonormal tangent two-frames `(u, v)` at points of `HPⁿ` with `v` tangent to the
quaternionic line of `u`, of dimension `8n + 1`. This is the family of two-spheres of `HPⁿ` used by
Barraud–Damian–Humilière–Oancea to show that quaternionic projective spaces are abundant with
two-spheres.

## Main declarations

* `TauCeti.QuaternionicProjectiveSpace.twoFrame`: quaternionic orthonormal two-frames of `ℍⁿ⁺¹`;
  for `n ≥ 1` every unit vector starts one
  (`TauCeti.QuaternionicProjectiveSpace.exists_mem_twoFrame`).
* `TauCeti.QuaternionicProjectiveSpace.lineIsometry`: the isometry `(a, b) ↦ x a + y b`.
* `TauCeti.QuaternionicProjectiveSpace.lineMap`: the projective line `[a : b] ↦ [x a + y b]`.
* `TauCeti.QuaternionicProjectiveSpace.isClosedEmbedding_lineMap_right`: the line of a fixed
  two-frame is a closed embedding.
* `TauCeti.QuaternionicProjectiveSpace.greatSphere4`: the great two-sphere of `S⁴` through the poles
  in the direction of a unit imaginary quaternion.
* `TauCeti.QuaternionicProjectiveSpace.lineSphereFamily`: the family of great two-spheres of the
  quaternionic projective lines of `HPⁿ`, with
  `TauCeti.QuaternionicProjectiveSpace.mappingSpaceEval_comp_lineSphereFamily` (it lies over `HPⁿ`)
  and `TauCeti.QuaternionicProjectiveSpace.lineSphereFamily_eq_of_op_smul` (it descends to tangent
  frames).

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.5, proof of Proposition 6.39.
* A. L. Besse, *Manifolds all of whose geodesics are closed*, Springer, 1978, Theorem 3.25
  (the quaternionic lines of `HPⁿ` are totally geodesic round four-spheres).
-/

public section

noncomputable section

open Metric MulOpposite Quaternion
open scoped RightActions RealInnerProductSpace

namespace TauCeti.QuaternionicProjectiveSpace

variable {n : ℕ}

/-! ### Quaternionic two-frames and their lines -/

section Line

variable (n) in
/-- The **quaternionic two-frames** of `ℍⁿ⁺¹`: pairs `(x, y)` of unit vectors with `y` orthogonal
to the quaternionic line `x ℍ`, that is `⟪x a, y⟫ = 0` for every quaternion `a`. -/
def twoFrame : Set (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1 ×
    sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) :=
  {f | ∀ a : ℍ, ⟪(f.1 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) <• a,
    (f.2 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ)⟫ = 0}

@[simp]
theorem mem_twoFrame_iff {f : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1 ×
    sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1} :
    f ∈ twoFrame n ↔ ∀ a : ℍ, ⟪(f.1 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) <• a,
      (f.2 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ)⟫ = 0 :=
  Iff.rfl

/-- For `n ≥ 1`, every unit vector `x` of `ℍⁿ⁺¹` is the first vector of a quaternionic two-frame:
the real dimension `4n + 4` of `ℍⁿ⁺¹` exceeds that of the quaternionic line `x ℍ`. -/
theorem exists_mem_twoFrame (hn : n ≠ 0) (x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) :
    ∃ y, (x, y) ∈ twoFrame n := by
  obtain ⟨w, hw, hxw⟩ :=
    exists_norm_eq_one_forall_inner_op_smul_eq_zero (F := PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) (by
      rw [← Module.finrank_eq_rank, finrank_piLp_quaternion, Fintype.card_fin]
      exact_mod_cast (by omega : 4 < 4 * (n + 1))) x
  exact ⟨⟨w, mem_sphere_zero_iff_norm.2 hw⟩, hxw⟩

/-- The vector `x a + y b` has the norm of `(a, b)` when `(x, y)` is a quaternionic two-frame:
`x a` and `y b` are orthogonal, of norms `‖a‖` and `‖b‖`. -/
private theorem norm_op_smul_add_op_smul (f : twoFrame n) (v : PiLp 2 fun _ : Fin 2 ↦ ℍ) :
    ‖(f.1.1 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) <• v 0 +
      (f.1.2 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) <• v 1‖ = ‖v‖ := by
  have hx : ‖(f.1.1 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ)‖ = 1 := norm_eq_of_mem_sphere _
  have hy : ‖(f.1.2 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ)‖ = 1 := norm_eq_of_mem_sphere _
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_add_sq_real, inner_op_smul_op_smul_eq_zero f.2, PiLp.norm_sq_eq_of_L2 _ v,
    Fin.sum_univ_two, norm_smul, norm_smul, norm_op, norm_op, hx, hy]
  ring

/-- The real-linear isometry `(a, b) ↦ x a + y b` from `ℍ²` onto the quaternionic plane spanned
by a quaternionic two-frame `(x, y)`. -/
def lineIsometry (f : twoFrame n) :
    (PiLp 2 fun _ : Fin 2 ↦ ℍ) →ₗᵢ[ℝ] PiLp 2 fun _ : Fin (n + 1) ↦ ℍ where
  toFun v := (f.1.1 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) <• v 0 +
    (f.1.2 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) <• v 1
  map_add' v w := by
    simp only [WithLp.ofLp_add, Pi.add_apply, op_add, add_smul]
    abel
  map_smul' c v := by
    simp only [WithLp.ofLp_smul, Pi.smul_apply, op_smul, smul_assoc, smul_add, RingHom.id_apply]
  norm_map' := norm_op_smul_add_op_smul f

@[simp]
theorem lineIsometry_apply (f : twoFrame n) (v : PiLp 2 fun _ : Fin 2 ↦ ℍ) :
    lineIsometry f v = (f.1.1 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) <• v 0 +
      (f.1.2 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) <• v 1 :=
  (rfl)

/-- The isometry of a two-frame commutes with right multiplication by quaternions. -/
theorem lineIsometry_op_smul (f : twoFrame n) (v : PiLp 2 fun _ : Fin 2 ↦ ℍ) (q : ℍ) :
    lineIsometry f (v <• q) = lineIsometry f v <• q := by
  simp only [lineIsometry_apply, PiLp.smul_apply, op_smul_eq_mul, smul_add, op_mul, mul_smul]

/-- The unit vector `x a + y b` of `ℍⁿ⁺¹`, for a quaternionic two-frame `(x, y)` and a unit vector
`(a, b)` of `ℍ²`, jointly continuous in the frame and the vector. -/
def lineSphere : C(twoFrame n × sphere (0 : PiLp 2 fun _ : Fin 2 ↦ ℍ) 1,
    sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) where
  toFun p := ⟨lineIsometry p.1 p.2, by
    rw [mem_sphere_zero_iff_norm, LinearIsometry.norm_map]
    exact norm_eq_of_mem_sphere p.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    simp only [lineIsometry_apply]
    fun_prop

@[simp]
theorem coe_lineSphere_apply (p : twoFrame n × sphere (0 : PiLp 2 fun _ : Fin 2 ↦ ℍ) 1) :
    (lineSphere p : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) = lineIsometry p.1 p.2 :=
  (rfl)

/-- The unit vector `x a + y b` is compatible with right multiplication by unit quaternions. -/
theorem lineSphere_op_smul (f : twoFrame n) (q : sphere (0 : ℍ) 1)
    (v : sphere (0 : PiLp 2 fun _ : Fin 2 ↦ ℍ) 1) :
    lineSphere (f, v <• q) = lineSphere (f, v) <• q :=
  Subtype.ext (lineIsometry_op_smul f _ _)

/-- **The quaternionic projective line of a two-frame**: `((x, y), [a : b]) ↦ [x a + y b]`, a
continuous map from the product of the space of quaternionic two-frames of `ℍⁿ⁺¹` with `HP¹` to
`HPⁿ`. -/
def lineMap : C(twoFrame n × QuaternionicProjectiveSpace 1, QuaternionicProjectiveSpace n) where
  toFun p := QuaternionicProjectiveSpace.lift 1 (fun v ↦ mk n (lineSphere (p.1, v)))
    (fun q v ↦ by rw [lineSphere_op_smul, mk_op_smul]) p.2
  continuous_toFun := by
    -- `id × mk` is a quotient map, through which the line is the projection of `lineSphere`.
    have hq := ((IsOpenQuotientMap.id (X := twoFrame n)).prodMap
      (isOpenQuotientMap_mk 1)).isQuotientMap
    rw [hq.continuous_iff]
    exact ((continuous_mk n).comp lineSphere.continuous).congr fun p ↦
      (QuaternionicProjectiveSpace.lift_mk 1 (fun v ↦ mk n (lineSphere (p.1, v))) _ p.2).symm

/-- The line of a two-frame `(x, y)` sends `[v]` to the class of `x v₀ + y v₁`. -/
@[simp]
theorem lineMap_mk (f : twoFrame n) (v : sphere (0 : PiLp 2 fun _ : Fin 2 ↦ ℍ) 1) :
    lineMap (f, mk 1 v) = mk n (lineSphere (f, v)) :=
  QuaternionicProjectiveSpace.lift_mk 1 _ _ v

/-- The line of a two-frame `(x, y)` sends the base point `[e₀]` of `HP¹` to `[x]`. -/
@[simp]
theorem lineMap_basePoint (f : twoFrame n) : lineMap (f, basePoint 1) = mk n f.1.1 := by
  rw [basePoint_def, lineMap_mk]
  congr 1
  ext : 1
  simp

/-- The line of a two-frame `(x, y)` sends `[e₁]` to `[y]`. -/
theorem lineMap_mk_single_one (f : twoFrame n) :
    lineMap (f, mk 1 ⟨PiLp.single 2 1 1, by simp⟩) = mk n f.1.2 := by
  rw [lineMap_mk]
  congr 1
  ext : 1
  simp

/-- **The line of a two-frame is injective**: `x a + y b` determines `(a, b)` since the line
isometry is injective, so `[x a + y b]` determines `[a : b]`. -/
theorem lineMap_right_injective (f : twoFrame n) : Function.Injective fun p ↦ lineMap (f, p) := by
  intro p p' h
  induction p using QuaternionicProjectiveSpace.inductionOn with | h v => ?_
  induction p' using QuaternionicProjectiveSpace.inductionOn with | h w => ?_
  simp only [lineMap_mk, mk_eq_mk_iff] at h
  obtain ⟨q, hq⟩ := h
  refine (mk_eq_mk_iff 1 v w).2 ⟨q, Subtype.ext ((lineIsometry f).injective ?_)⟩
  rw [← lineSphere_op_smul] at hq
  exact congrArg Subtype.val hq

/-- **The line of a two-frame is a closed embedding** of the four-sphere `HP¹` into `HPⁿ`. -/
theorem isClosedEmbedding_lineMap_right (f : twoFrame n) :
    Topology.IsClosedEmbedding fun p ↦ lineMap (f, p) :=
  (lineMap.continuous.comp (Continuous.prodMk_right f)).isClosedEmbedding
    (lineMap_right_injective f)

end Line

/-! ### Great two-spheres of the quaternionic lines -/

section Sphere

/-- The point `(s₀, s₁ + s₂ q)` of `ℝ × ℍ` for `s ∈ ℝ³` and a quaternion `q`. -/
private def greatSphereVector (q : ℍ) (s : EuclideanSpace ℝ (Fin 3)) : WithLp 2 (ℝ × ℍ) :=
  WithLp.toLp 2 (s 0, (s 1 : ℍ) + s 2 • q)

private theorem norm_greatSphereVector {q : ℍ} (hq : ‖q‖ = 1) (hq0 : q.re = 0) (s : Sphere2) :
    ‖greatSphereVector q s‖ = 1 := by
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 ?_
  have hs := EuclideanSpace.norm_sq_eq (s : EuclideanSpace ℝ (Fin 3))
  rw [norm_eq_of_mem_sphere s, Fin.sum_univ_three] at hs
  have hinner : ⟪((s : EuclideanSpace ℝ (Fin 3)) 1 : ℍ), (s : EuclideanSpace ℝ (Fin 3)) 2 • q⟫ =
      0 := by
    rw [real_inner_smul_right, inner_def]
    simp [hq0]
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [greatSphereVector, WithLp.toLp_fst, WithLp.toLp_snd]
  rw [norm_add_sq_real, hinner, norm_smul, norm_coe, hq]
  simp only [Real.norm_eq_abs, sq_abs, mul_one, mul_zero, add_zero] at hs ⊢
  linarith

/-- **The great two-sphere of `S⁴` in the direction of a unit imaginary quaternion `q`**: the map
`(s₀, s₁, s₂) ↦ (s₀, s₁ + s₂ q)` from `S² ⊆ ℝ³` to `S⁴ ⊆ ℝ × ℍ`, continuous in `q`. It is the
intersection of `S⁴` with the real three-space spanned by `(1, 0)`, `(0, 1)` and `(0, q)`, and runs
through the poles `(±1, 0)`. -/
def greatSphere4 :
    C({q : sphere (0 : ℍ) 1 // (q : ℍ).re = 0} × Sphere2, sphere (0 : WithLp 2 (ℝ × ℍ)) 1) where
  toFun p := ⟨greatSphereVector p.1.1 p.2, mem_sphere_zero_iff_norm.2
    (norm_greatSphereVector (norm_eq_of_mem_sphere p.1.1) p.1.2 p.2)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have := Quaternion.continuous_coe
    unfold greatSphereVector
    fun_prop

@[simp]
theorem coe_greatSphere4_apply (p : {q : sphere (0 : ℍ) 1 // (q : ℍ).re = 0} × Sphere2) :
    (greatSphere4 p : WithLp 2 (ℝ × ℍ)) =
      WithLp.toLp 2 ((p.2 : EuclideanSpace ℝ (Fin 3)) 0,
        ((p.2 : EuclideanSpace ℝ (Fin 3)) 1 : ℍ) + (p.2 : EuclideanSpace ℝ (Fin 3)) 2 •
          (p.1 : ℍ)) :=
  (rfl)

/-- Each great two-sphere is injective: `1` and `q` are linearly independent over `ℝ`. -/
theorem greatSphere4_right_injective (q : {q : sphere (0 : ℍ) 1 // (q : ℍ).re = 0}) :
    Function.Injective fun s ↦ greatSphere4 (q, s) := by
  intro s s' h
  have h' := congrArg (fun x : sphere (0 : WithLp 2 (ℝ × ℍ)) 1 ↦
    WithLp.ofLp (x : WithLp 2 (ℝ × ℍ))) h
  simp only [coe_greatSphere4_apply, WithLp.ofLp_toLp, Prod.mk.injEq] at h'
  obtain ⟨h0, h12⟩ := h'
  have hre := congrArg (fun z : ℍ ↦ z.re) h12
  simp only [re_add, re_coe, re_smul, q.2, smul_zero, add_zero] at hre
  rw [hre, add_right_inj] at h12
  have hq : ((q : sphere (0 : ℍ) 1) : ℍ) ≠ 0 := ne_zero_of_mem_unit_sphere _
  have h2 := smul_left_injective ℝ hq h12
  refine Subtype.ext (PiLp.ext fun i ↦ ?_)
  fin_cases i
  exacts [h0, hre, h2]

/-- The great two-sphere sends the north pole of `S²` to the north pole `(1, 0)` of `S⁴`. -/
theorem coe_greatSphere4_north (q : {q : sphere (0 : ℍ) 1 // (q : ℍ).re = 0}) :
    (greatSphere4 (q, Sphere2.north) : WithLp 2 (ℝ × ℍ)) = WithLp.toLp 2 (1, 0) := by
  simp [Sphere2.coe_north]

/-- The great two-sphere sends the south pole of `S²` to the south pole `(-1, 0)` of `S⁴`. -/
theorem coe_greatSphere4_south (q : {q : sphere (0 : ℍ) 1 // (q : ℍ).re = 0}) :
    (greatSphere4 (q, Sphere2.south) : WithLp 2 (ℝ × ℍ)) = WithLp.toLp 2 (-1, 0) := by
  simp [Sphere2.coe_south]

/-- **The family of great two-spheres of the quaternionic projective lines of `HPⁿ`**:
`σ (x, y, q)` is the great two-sphere in the direction `q` of the quaternionic line of the
two-frame `(x, y)`, read through `HP¹ ≃ₜ S⁴`. It is a continuous family of maps `S² → HPⁿ`
parametrized by the quaternionic two-frames of `ℍⁿ⁺¹` and the unit imaginary quaternions. -/
def lineSphereFamily :
    C(twoFrame n × {q : sphere (0 : ℍ) 1 // (q : ℍ).re = 0},
      C(Sphere2, QuaternionicProjectiveSpace n)) :=
  ContinuousMap.curry
    ⟨fun p ↦ lineMap (p.1.1, homeomorphSphere4.symm (greatSphere4 (p.1.2, p.2))), by fun_prop⟩

/-- The sphere `σ (x, y, q)` is the line of `(x, y)` composed with the great two-sphere in the
direction `q`. -/
theorem lineSphereFamily_apply (p : twoFrame n × {q : sphere (0 : ℍ) 1 // (q : ℍ).re = 0})
    (s : Sphere2) :
    lineSphereFamily p s = lineMap (p.1, homeomorphSphere4.symm (greatSphere4 (p.2, s))) :=
  (rfl)

/-- The sphere `σ (x, y, q)` sends the north pole of `S²` to `[x]`. -/
@[simp]
theorem lineSphereFamily_apply_north (p : twoFrame n × {q : sphere (0 : ℍ) 1 // (q : ℍ).re = 0}) :
    lineSphereFamily p Sphere2.north = mk n p.1.1.1 := by
  have h : greatSphere4 (p.2, Sphere2.north) = homeomorphSphere4 (basePoint 1) :=
    Subtype.ext (by rw [coe_greatSphere4_north, coe_homeomorphSphere4_basePoint])
  rw [lineSphereFamily_apply, h, Homeomorph.symm_apply_apply, lineMap_basePoint]

/-- The sphere `σ (x, y, q)` sends the south pole of `S²` to `[y]`. -/
@[simp]
theorem lineSphereFamily_apply_south (p : twoFrame n × {q : sphere (0 : ℍ) 1 // (q : ℍ).re = 0}) :
    lineSphereFamily p Sphere2.south = mk n p.1.1.2 := by
  have h : greatSphere4 (p.2, Sphere2.south) =
      hopfSphere4 ⟨PiLp.single 2 1 1, by simp⟩ :=
    Subtype.ext (by rw [coe_greatSphere4_south, coe_hopfSphere4_single_one])
  rw [lineSphereFamily_apply, h, homeomorphSphere4_symm_hopfSphere4, lineMap_mk_single_one]

/-- **The family lies over `HPⁿ`**: evaluating `σ (x, y, q)` at the north pole of `S²` gives the
point `[x]`. -/
theorem mappingSpaceEval_comp_lineSphereFamily :
    (mappingSpaceEval Sphere2.north).comp (lineSphereFamily (n := n)) =
      ⟨fun p ↦ mk n p.1.1.1, by fun_prop⟩ := by
  ext p
  simp

/-- **Each sphere of the family is injective**: `σ (x, y, q)` is a one-to-one map
`S² → HPⁿ`. -/
theorem lineSphereFamily_apply_injective
    (p : twoFrame n × {q : sphere (0 : ℍ) 1 // (q : ℍ).re = 0}) :
    Function.Injective (lineSphereFamily p) :=
  (lineMap_right_injective p.1).comp
    (homeomorphSphere4.symm.injective.comp (greatSphere4_right_injective p.2))

/-- **The family descends to tangent frames**: replacing a two-frame `(x, y)` by `(x c, y c)` and
the imaginary unit `q` by `c* q c`, for a unit quaternion `c`, does not change the sphere. The
tangent directions `y` and `y q` at `[x]` of the sphere become `y c` and `y c (c* q c) = y q c`,
and `[x a + y b] = [x c (c* a c) + y c (c* b c)]`. -/
theorem lineSphereFamily_eq_of_op_smul {f f' : twoFrame n}
    {q q' : {q : sphere (0 : ℍ) 1 // (q : ℍ).re = 0}} (c : sphere (0 : ℍ) 1)
    (hx : (f'.1.1 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) = f.1.1 <• (c : ℍ))
    (hy : (f'.1.2 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) = f.1.2 <• (c : ℍ))
    (hq : ((q' : sphere (0 : ℍ) 1) : ℍ) = star (c : ℍ) * q * c) :
    lineSphereFamily (f', q') = lineSphereFamily (f, q) := by
  have hc : ‖(c : ℍ)‖ = 1 := norm_eq_of_mem_sphere c
  have hcc : (c : ℍ) * star (c : ℍ) = 1 :=
    Unitary.mul_star_self_of_mem ((mem_unitary_iff_mem_sphere_zero_one _).2 c.2)
  have hcc' : star (c : ℍ) * c = 1 :=
    Unitary.star_mul_self_of_mem ((mem_unitary_iff_mem_sphere_zero_one _).2 c.2)
  ext s : 1
  obtain ⟨v, hv⟩ := hopfSphere4_surjective (greatSphere4 (q, s))
  -- The conjugate `w = (c* a c, c* b c)` of a Hopf preimage `v = (a, b)` of the sphere point.
  let w : sphere (0 : PiLp 2 fun _ : Fin 2 ↦ ℍ) 1 :=
    ⟨WithLp.toLp 2 fun i ↦ star (c : ℍ) * (v : PiLp 2 fun _ : Fin 2 ↦ ℍ) i * c, by
      rw [mem_sphere_zero_iff_norm]
      refine Eq.trans ?_ (norm_eq_of_mem_sphere v)
      refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
      rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2 _ (v : PiLp 2 fun _ : Fin 2 ↦ ℍ)]
      simp [norm_mul, hc]⟩
  have hw : greatSphere4 (q', s) = hopfSphere4 w := by
    refine Subtype.ext ?_
    rw [coe_hopfSphere4_conj c v w (fun _ ↦ rfl), hv, coe_greatSphere4_apply,
      coe_greatSphere4_apply, hq]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, mul_add, add_mul, mul_smul_comm,
      smul_mul_assoc, ← coe_commutes, mul_assoc, hcc', mul_one]
  have hline : lineSphere (f', w) = lineSphere (f, v) <• c := by
    refine Subtype.ext ?_
    simp only [coe_lineSphere_apply, Sphere.coe_op_sphere_smul, unop_op, lineIsometry_apply, hx,
      hy, smul_add, ← mul_smul, ← op_mul]
    simp only [w, ← mul_assoc, hcc, one_mul]
  rw [lineSphereFamily_apply, lineSphereFamily_apply]
  dsimp only
  rw [hw, ← hv, homeomorphSphere4_symm_hopfSphere4,
    homeomorphSphere4_symm_hopfSphere4, lineMap_mk, lineMap_mk, hline, mk_op_smul]

end Sphere

end TauCeti.QuaternionicProjectiveSpace
