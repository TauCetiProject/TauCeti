/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Reflection
public import TauCeti.Analysis.Normed.Lp.ProdLp
public import TauCeti.Geometry.Euclidean.Inversion
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Ext

/-!
# The isometry group of the upper half-space model

For `R ≠ 0` and a point `(a, 0)` of the boundary hyperplane `E × {0}`, the Euclidean inversion
`x ↦ (a, 0) + (R / ‖x - (a, 0)‖) ^ 2 • (x - (a, 0))` preserves the open upper half-space of
`E × ℝ`. It scales tangent vectors and the height `t` by the same factor
`(R / ‖x - (a, 0)‖) ^ 2`, so it is an isometry of the hyperbolic metric `(‖dx‖² + dt²) / t²`.

Together with the similarities `(x, t) ↦ (c • A x + b, c • t)` of
`TauCeti.UpperHalfSpace.similarity`, these inversions exhaust the isometry group of the upper
half-space model when `E` is finite-dimensional: every isometry is a similarity, or a similarity
followed by one inversion. This is the classical description of the isometries of hyperbolic space
in the upper half-space model as the Möbius transformations preserving the upper half-space,
written in an explicit normal form.
With `E = EuclideanSpace ℝ (Fin 2)` it describes the full isometry group of the hyperbolic model
geometry `ℍ³`.

The classification uses that an isometry of a connected Riemannian manifold is determined by its
value and differential at one point (`TauCeti.RiemannianIsometry.ext_of_mfderiv_eq`). After a
similarity, an isometry fixes `(0, 1)`, where the hyperbolic metric is the Euclidean one, so its
differential there is a linear isometry of `E × ℝ`. If that differential fixes the vertical unit
vector, it is the differential of a linear similarity; otherwise it is the differential of a
linear similarity followed by the inversion in the sphere through `(0, 1)` whose differential
exchanges the vertical vector with its image.

## Main definitions

* `TauCeti.UpperHalfSpace.inversion`: the inversion in the sphere of radius `|R|` centred at the
  boundary point `(a, 0)`, as an isometry of the upper half-space model.

## Main results

* `TauCeti.UpperHalfSpace.tangentSpaceCastModel_mfderiv_inversion`: the differential of an
  inversion is a positive multiple of a reflection.
* `TauCeti.UpperHalfSpace.inversion_mul_self`: inversions are involutions.
* `TauCeti.UpperHalfSpace.exists_eq_similarity_or_exists_eq_inversion_mul_similarity`: every
  isometry of the upper half-space model with finite-dimensional `E` is a similarity or an
  inversion composed with a similarity.

## References

* J. G. Ratcliffe, *Foundations of Hyperbolic Manifolds*, 3rd ed., Springer GTM 149 (2019),
  §4.6 (the upper half-space model, whose isometries are the Möbius transformations preserving
  it).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 3 (the isometries of the upper half-space model) and Proposition 5.22 (an isometry is
  determined by its value and differential at one point).
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.UpperHalfSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- A point of the upper half-space is not a point `(a, 0)` of its boundary hyperplane. -/
private theorem coe_ne_toLp (x : UpperHalfSpace E) (a : E) :
    (x : WithLp 2 (E × ℝ)) ≠ WithLp.toLp 2 (a, 0) := fun h ↦
  (height_pos x).ne' (by simpa [← snd_coe] using congrArg WithLp.snd h)

omit [InnerProductSpace ℝ E] in
/-- The scale factor `(R / ‖x - (a, 0)‖) ^ 2` of the inversion in the sphere of radius `|R|` about
`(a, 0)` at the point `x` is positive. -/
private theorem inversion_factor_pos (a : E) {R : ℝ} (hR : R ≠ 0) (x : UpperHalfSpace E) :
    0 < (R / dist (x : WithLp 2 (E × ℝ)) (WithLp.toLp 2 (a, 0))) ^ 2 := by
  have hd : dist (x : WithLp 2 (E × ℝ)) (WithLp.toLp 2 (a, 0)) ≠ 0 :=
    dist_ne_zero.2 (coe_ne_toLp x a)
  positivity

/-- The underlying map of `inversion a R hR`. -/
private def inversionMap (a : E) (R : ℝ) (hR : R ≠ 0) (x : UpperHalfSpace E) :
    UpperHalfSpace E :=
  mk (EuclideanGeometry.inversion (WithLp.toLp 2 (a, 0)) R x) (by
    rw [snd_inversion, snd_coe]
    exact mul_pos (inversion_factor_pos a hR x) (height_pos x))

private theorem coe_inversionMap (a : E) (R : ℝ) (hR : R ≠ 0) (x : UpperHalfSpace E) :
    (inversionMap a R hR x : WithLp 2 (E × ℝ)) =
      EuclideanGeometry.inversion (WithLp.toLp 2 (a, 0)) R x :=
  coe_mk _ _

private theorem coe_comp_inversionMap (a : E) (R : ℝ) (hR : R ≠ 0) :
    coe ∘ inversionMap a R hR = EuclideanGeometry.inversion (WithLp.toLp 2 (a, 0)) R ∘ coe :=
  funext (coe_inversionMap a R hR)

private theorem height_inversionMap (a : E) (R : ℝ) (hR : R ≠ 0) (x : UpperHalfSpace E) :
    height (inversionMap a R hR x) =
      (R / dist (x : WithLp 2 (E × ℝ)) (WithLp.toLp 2 (a, 0))) ^ 2 * height x := by
  rw [← snd_coe, coe_inversionMap, snd_inversion, snd_coe]

private theorem inversionMap_inversionMap (a : E) (R : ℝ) (hR : R ≠ 0) (x : UpperHalfSpace E) :
    inversionMap a R hR (inversionMap a R hR x) = x :=
  ext (by rw [coe_inversionMap, coe_inversionMap, EuclideanGeometry.inversion_inversion _ hR])

private theorem contMDiff_inversionMap {n : ℕ∞ω} (a : E) (R : ℝ) (hR : R ≠ 0) :
    ContMDiff 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) n (inversionMap a R hR) := by
  refine contMDiff_coe_comp_iff.1 fun x ↦ ?_
  rw [coe_comp_inversionMap]
  exact (EuclideanGeometry.contDiffAt_inversion (coe_ne_toLp x a)).contMDiffAt.comp x
    (contMDiff_coe.of_le le_top x)

private theorem tangentSpaceCastModel_mfderiv_inversionMap (a : E) (R : ℝ) (hR : R ≠ 0)
    (x : UpperHalfSpace E) (v : TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :
    tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) (inversionMap a R hR x)
        (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) (inversionMap a R hR) x v) =
      (R / dist (x : WithLp 2 (E × ℝ)) (WithLp.toLp 2 (a, 0))) ^ 2 •
        (ℝ ∙ ((x : WithLp 2 (E × ℝ)) - WithLp.toLp 2 (a, 0)))ᗮ.reflection
          (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x v) :=
  tangentSpaceCastModel_mfderiv_apply
    ((contMDiff_inversionMap (n := 1) a R hR x).mdifferentiableAt one_ne_zero)
    (EuclideanGeometry.hasFDerivAt_inversion (coe_ne_toLp x a))
    (coe_comp_inversionMap a R hR) v

/-- The inversion `x ↦ (a, 0) + (R / ‖x - (a, 0)‖) ^ 2 • (x - (a, 0))` in the sphere of radius
`|R|` centred at the boundary point `(a, 0)`, as an isometry of the upper half-space model: it
scales tangent vectors and the height by the same factor `(R / ‖x - (a, 0)‖) ^ 2`.
Geometrically, it is the hyperbolic reflection in the hemisphere `‖x - (a, 0)‖ = |R|`. -/
def inversion (a : E) (R : ℝ) (hR : R ≠ 0) : Isom 𝓘(ℝ, WithLp 2 (E × ℝ)) (UpperHalfSpace E) where
  toFun := inversionMap a R hR
  invFun := inversionMap a R hR
  left_inv := inversionMap_inversionMap a R hR
  right_inv := inversionMap_inversionMap a R hR
  contMDiff_toFun := contMDiff_inversionMap a R hR
  contMDiff_invFun := contMDiff_inversionMap a R hR
  inner_mfderiv' x v w := by
    -- The diffeomorphism under construction is `inversionMap a R hR` by definition; `change`
    -- states the goal in terms of that function, so that its differential lemma applies.
    change inner ℝ
        (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) (inversionMap a R hR) x v)
        (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) (inversionMap a R hR) x w) =
      inner ℝ v w
    rw [inner_def, inner_def, tangentSpaceCastModel_mfderiv_inversionMap,
      tangentSpaceCastModel_mfderiv_inversionMap, height_inversionMap, real_inner_smul_left,
      real_inner_smul_right, LinearIsometryEquiv.inner_map_map]
    have := (inversion_factor_pos a hR x).ne'
    have := (height_pos x).ne'
    have : dist (x : WithLp 2 (E × ℝ)) (WithLp.toLp 2 (a, 0)) ≠ 0 :=
      dist_ne_zero.2 (coe_ne_toLp x a)
    field_simp

/-- The coercion of `inversion a R hR` to a function is `inversionMap a R hR`: the coercion of an
isometry is the `toFun` field of its underlying equivalence. -/
private theorem coe_inversion (a : E) (R : ℝ) (hR : R ≠ 0) :
    ⇑(inversion a R hR) = inversionMap a R hR :=
  (rfl)

/-- The isometry `inversion a R hR` is the Euclidean inversion in the sphere of radius `|R|` about
`(a, 0)`. -/
@[simp]
theorem coe_inversion_apply (a : E) (R : ℝ) (hR : R ≠ 0) (x : UpperHalfSpace E) :
    (inversion a R hR x : WithLp 2 (E × ℝ)) =
      EuclideanGeometry.inversion (WithLp.toLp 2 (a, 0)) R x := by
  rw [coe_inversion, coe_inversionMap]

/-- The inversion `inversion a R hR` multiplies the height of `x` by
`(R / ‖x - (a, 0)‖) ^ 2`. -/
@[simp]
theorem height_inversion_apply (a : E) (R : ℝ) (hR : R ≠ 0) (x : UpperHalfSpace E) :
    height (inversion a R hR x) =
      (R / dist (x : WithLp 2 (E × ℝ)) (WithLp.toLp 2 (a, 0))) ^ 2 * height x := by
  rw [coe_inversion, height_inversionMap]

/-- The differential of `inversion a R hR` at `x` is `(R / ‖x - (a, 0)‖) ^ 2` times the
reflection in the hyperplane orthogonal to `x - (a, 0)`. -/
theorem tangentSpaceCastModel_mfderiv_inversion (a : E) (R : ℝ) (hR : R ≠ 0)
    (x : UpperHalfSpace E) (v : TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :
    tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) (inversion a R hR x)
        (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) (inversion a R hR) x v) =
      (R / dist (x : WithLp 2 (E × ℝ)) (WithLp.toLp 2 (a, 0))) ^ 2 •
        (ℝ ∙ ((x : WithLp 2 (E × ℝ)) - WithLp.toLp 2 (a, 0)))ᗮ.reflection
          (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x v) := by
  rw [coe_inversion]
  exact tangentSpaceCastModel_mfderiv_inversionMap a R hR x v

/-- Applying an inversion twice returns the original point. -/
@[simp]
theorem inversion_apply_inversion_apply (a : E) (R : ℝ) (hR : R ≠ 0) (x : UpperHalfSpace E) :
    inversion a R hR (inversion a R hR x) = x := by
  rw [coe_inversion, inversionMap_inversionMap]

/-- An inversion is an involution. -/
@[simp]
theorem inversion_mul_self (a : E) (R : ℝ) (hR : R ≠ 0) :
    inversion a R hR * inversion a R hR = 1 := by
  ext x
  rw [RiemannianIsometry.mul_apply, inversion_apply_inversion_apply, RiemannianIsometry.one_apply]

/-- An inversion is its own inverse. -/
@[simp]
theorem inversion_inv (a : E) (R : ℝ) (hR : R ≠ 0) : (inversion a R hR)⁻¹ = inversion a R hR :=
  inv_eq_of_mul_eq_one_left (inversion_mul_self a R hR)

section Classification

/-- The point `(0, 1)`, at which an isometry is normalized by its value and differential. -/
private def basePoint : UpperHalfSpace E :=
  mk (WithLp.toLp 2 (0, 1)) (by simp)

omit [InnerProductSpace ℝ E] in
private theorem coe_basePoint :
    (basePoint : UpperHalfSpace E) = WithLp.toLp 2 ((0 : E), (1 : ℝ)) :=
  coe_mk _ _

omit [InnerProductSpace ℝ E] in
private theorem height_basePoint : height (basePoint : UpperHalfSpace E) = 1 := by
  simp [← snd_coe, coe_basePoint]

/-- The differential of an isometry at `(0, 1)`, read in the model `E × ℝ`. -/
private def mfderivBase (Φ : Isom 𝓘(ℝ, WithLp 2 (E × ℝ)) (UpperHalfSpace E)) :
    WithLp 2 (E × ℝ) →L[ℝ] WithLp 2 (E × ℝ) :=
  (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) (Φ basePoint) :
      TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) (Φ basePoint) →L[ℝ] WithLp 2 (E × ℝ)).comp
    ((mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) Φ basePoint).comp
      (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) basePoint).symm.toContinuousLinearMap)

/-- Evaluate the model differential by transporting the input and output tangent vectors. -/
private theorem mfderivBase_apply
    (Φ : Isom 𝓘(ℝ, WithLp 2 (E × ℝ)) (UpperHalfSpace E)) (p : WithLp 2 (E × ℝ)) :
    mfderivBase Φ p = tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) (Φ basePoint)
      (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) Φ basePoint
        ((tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) basePoint).symm p)) := by
  simp only [mfderivBase, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]

/-- An isometry fixing `(0, 1)` has a Euclidean linear isometry as differential there, since the
hyperbolic metric at height `1` is the Euclidean one. -/
private theorem inner_mfderivBase {Φ : Isom 𝓘(ℝ, WithLp 2 (E × ℝ)) (UpperHalfSpace E)}
    (he : Φ basePoint = basePoint) (p q : WithLp 2 (E × ℝ)) :
    inner ℝ (mfderivBase Φ p) (mfderivBase Φ q) = inner ℝ p q := by
  have h := Φ.inner_mfderiv basePoint
    ((tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) basePoint).symm p)
    ((tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) basePoint).symm q)
  have hΦ : height (Φ basePoint) = 1 := by rw [he, height_basePoint]
  rw [inner_def, inner_def, hΦ, height_basePoint] at h
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply,
    one_pow, div_one, div_one] at h
  rw [mfderivBase_apply, mfderivBase_apply]
  exact h

variable [FiniteDimensional ℝ E]

/-- An isometry fixing `(0, 1)` whose differential there fixes the vertical unit vector is a
linear isometry of `E` acting on the first coordinate. -/
private theorem exists_eq_similarity_of_mfderivBase
    {Φ : Isom 𝓘(ℝ, WithLp 2 (E × ℝ)) (UpperHalfSpace E)} (he : Φ basePoint = basePoint)
    (hv : mfderivBase Φ (WithLp.toLp 2 (0, 1)) = WithLp.toLp 2 (0, 1)) :
    ∃ A : E ≃ₗᵢ[ℝ] E, Φ = similarity 1 one_pos A 0 := by
  -- The differential maps the horizontal hyperplane `E × {0}`, orthogonal to the vertical
  -- vector, to itself.
  have hsnd (x : E) : (mfderivBase Φ (WithLp.toLp 2 (x, 0))).snd = 0 := by
    have h := inner_mfderivBase he (WithLp.toLp 2 (x, 0)) (WithLp.toLp 2 (0, 1))
    rw [hv] at h
    simpa using h
  let B₀ : E →ₗ[ℝ] E :=
    { toFun x := (mfderivBase Φ (WithLp.toLp 2 (x, 0))).fst
      map_add' x y := by
        rw [← WithLp.add_fst, ← map_add, ← WithLp.toLp_add, Prod.mk_add_mk, add_zero]
      map_smul' c x := by
        rw [RingHom.id_apply, ← WithLp.smul_fst, ← map_smul, ← WithLp.toLp_smul, Prod.smul_mk,
          smul_zero] }
  have hB₀ (x y : E) : inner ℝ (B₀ x) (B₀ y) = inner ℝ x y := by
    have h := inner_mfderivBase he (WithLp.toLp 2 (x, 0)) (WithLp.toLp 2 (y, 0))
    simpa [hsnd, B₀] using h
  let B : E ≃ₗᵢ[ℝ] E := (B₀.isometryOfInner hB₀).toLinearIsometryEquiv rfl
  have hL (p : WithLp 2 (E × ℝ)) :
      mfderivBase Φ p = LinearIsometryEquiv.withLpProdCongr 2 B (.refl ℝ ℝ) p := by
    have hp : p = WithLp.toLp 2 (p.fst, 0) + p.snd • WithLp.toLp 2 (0, 1) :=
      (WithLp.ext_iff 2).2 (Prod.ext (by simp) (by simp))
    rw [hp, map_add, map_smul, hv]
    exact (WithLp.ext_iff 2).2 (Prod.ext (by simp [B, B₀]) (by simp [hsnd]))
  refine ⟨B, RiemannianIsometry.ext_of_mfderiv_eq Φ _ (p := basePoint) ?_ ?_⟩
  · rw [he]
    exact ext_fst_height (by simp [coe_basePoint]) (by simp [height_basePoint])
  · ext v
    have h := tangentSpaceCastModel_mfderiv_similarity 1 one_pos B 0 basePoint v
    rw [one_smul] at h
    -- `tangentSpaceCastModel` is the identity of the model on every tangent space, so the goal
    -- is `hL v` and `h` up to these identity maps; `change` exposes them.
    change mfderivBase Φ v = tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ))
      (similarity 1 one_pos B 0 basePoint)
      (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) (similarity 1 one_pos B 0)
        basePoint v)
    exact (hL v).trans h.symm

/-- An isometry fixing `(0, 1)` is a linear isometry of `E` acting on the first coordinate,
possibly followed by an inversion in a sphere through `(0, 1)` centred on the boundary. -/
private theorem eq_similarity_or_eq_inversion_mul_similarity_of_apply_basePoint
    {Φ : Isom 𝓘(ℝ, WithLp 2 (E × ℝ)) (UpperHalfSpace E)} (he : Φ basePoint = basePoint) :
    (∃ A : E ≃ₗᵢ[ℝ] E, Φ = similarity 1 one_pos A 0) ∨
      ∃ (a : E) (R : ℝ) (hR : R ≠ 0) (A : E ≃ₗᵢ[ℝ] E),
        Φ = inversion a R hR * similarity 1 one_pos A 0 := by
  set u := mfderivBase Φ (WithLp.toLp 2 (0, 1)) with hu_def
  by_cases hu : u = WithLp.toLp 2 (0, 1)
  · exact .inl (exists_eq_similarity_of_mfderivBase he hu)
  right
  -- The differential sends the vertical unit vector to a unit vector `u` of height less than `1`.
  have hnorm : ‖u‖ = 1 := by
    have h := inner_mfderivBase he (WithLp.toLp 2 (0, 1)) (WithLp.toLp 2 (0, 1))
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ← hu_def] at h
    exact (pow_left_inj₀ (norm_nonneg u) zero_le_one two_ne_zero).1 (by simpa using h)
  have hs := snd_lt_one hnorm hu
  -- Invert in the sphere through `(0, 1)` centred at the boundary point `(a, 0)` on the line
  -- through the vertical vector and `u`; its differential at `(0, 1)` exchanges them.
  set a : E := (1 - u.snd)⁻¹ • u.fst
  have hR :
      dist ((basePoint : UpperHalfSpace E) : WithLp 2 (E × ℝ)) (WithLp.toLp 2 (a, 0)) ≠ 0 :=
    dist_ne_zero.2 (coe_ne_toLp basePoint a)
  set ι := inversion a _ hR
  have hιe : ι basePoint = basePoint :=
    ext (by rw [coe_inversion_apply]; exact EuclideanGeometry.inversion_dist_center _ _)
  have hfix : (ι * Φ) basePoint = basePoint := by rw [RiemannianIsometry.mul_apply, he, hιe]
  have hcomp : mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) (ι * Φ) basePoint =
      (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) ι (Φ basePoint)).comp
        (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) Φ basePoint) := by
    rw [RiemannianIsometry.coe_mul]
    exact mfderiv_comp basePoint (ι.mdifferentiableAt _) (Φ.mdifferentiableAt _)
  have hv : mfderivBase (ι * Φ) (WithLp.toLp 2 (0, 1)) = WithLp.toLp 2 (0, 1) := by
    have h := tangentSpaceCastModel_mfderiv_inversion a _ hR (Φ basePoint)
      (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) Φ basePoint
        ((tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) basePoint).symm (WithLp.toLp 2 (0, 1))))
    rw [congrArg coe he, div_self hR, one_pow, one_smul] at h
    rw [mfderivBase, hcomp]
    -- `tangentSpaceCastModel` is the identity of the model on every tangent space, so the goal
    -- is `h` read at the points `(ι * Φ) (0, 1)` and `ι (Φ (0, 1))`, with `u` as argument.
    change tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) (ι (Φ basePoint))
      (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) ι (Φ basePoint)
        (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) Φ basePoint
          ((tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) basePoint).symm
            (WithLp.toLp 2 (0, 1))))) = _
    rw [h, coe_basePoint]
    exact reflection_apply_eq_toLp_zero_one hnorm hs
  obtain ⟨A, hA⟩ := exists_eq_similarity_of_mfderivBase hfix hv
  exact ⟨a, _, hR, A, by rw [← hA, ← mul_assoc, inversion_mul_self, one_mul]⟩

/-- **Isometries of the upper half-space model.** When `E` is finite-dimensional, every isometry
of the upper half-space model of hyperbolic space is either a similarity
`(x, t) ↦ (c • A x + b, c • t)` or such a similarity followed by the inversion in a sphere centred
on the boundary hyperplane `t = 0`. -/
theorem exists_eq_similarity_or_exists_eq_inversion_mul_similarity
    (Φ : Isom 𝓘(ℝ, WithLp 2 (E × ℝ)) (UpperHalfSpace E)) :
    (∃ (c : ℝ) (hc : 0 < c) (A : E ≃ₗᵢ[ℝ] E) (b : E), Φ = similarity c hc A b) ∨
      ∃ (a : E) (R : ℝ) (hR : R ≠ 0) (c : ℝ) (hc : 0 < c) (A : E ≃ₗᵢ[ℝ] E) (b : E),
        Φ = inversion a R hR * similarity c hc A b := by
  -- Precompose with a similarity `T` sending `(0, 1)` to `Φ⁻¹ (0, 1)`, so that `Φ * T` fixes
  -- `(0, 1)`, and absorb `T⁻¹` into the similarity factor.
  obtain ⟨q, hq⟩ : ∃ q, q = Φ⁻¹ basePoint := ⟨_, rfl⟩
  set T := similarity (height q) (height_pos q) (.refl ℝ E) (q : WithLp 2 (E × ℝ)).fst
  have hT : T basePoint = q := ext_fst_height (by simp [T, coe_basePoint])
    (by simp [T, height_basePoint])
  have hfix : (Φ * T) basePoint = basePoint := by
    rw [RiemannianIsometry.mul_apply, hT, hq, ← RiemannianIsometry.mul_apply, mul_inv_cancel,
      RiemannianIsometry.one_apply]
  have hΦ : Φ = Φ * T * T⁻¹ := (mul_inv_cancel_right Φ T).symm
  rcases eq_similarity_or_eq_inversion_mul_similarity_of_apply_basePoint hfix with
    ⟨A, hA⟩ | ⟨a, R, hR, A, hA⟩
  · rw [hA, similarity_inv, similarity_mul_similarity] at hΦ
    exact .inl ⟨_, _, _, _, hΦ⟩
  · rw [hA, similarity_inv, mul_assoc, similarity_mul_similarity] at hΦ
    exact .inr ⟨a, R, hR, _, _, _, _, hΦ⟩

end Classification

end TauCeti.UpperHalfSpace
