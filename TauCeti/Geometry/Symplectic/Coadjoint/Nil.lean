/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Heisenberg.Orbit
public import TauCeti.Geometry.Manifold.Riemannian.Nil.Basic
public import TauCeti.Geometry.Symplectic.Coadjoint.Orbit
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Symplectic.StandardCompatible

/-!
# Adjoint and coadjoint orbits of the Lie group Nil

`Nil` is the real Heisenberg group, a real-analytic Lie group in the global coordinates
`(x, y, z)` with product `(a, b, c) * (x, y, z) = (a + x, b + y, c + z + a y)`
(`TauCeti.Geometry.Manifold.Riemannian.Nil.Basic`). This file computes its adjoint and coadjoint
actions on its tangent Lie algebra `𝔫 = GroupLieAlgebra 𝓘(ℝ, ℝ × ℝ × ℝ) Nil` and the
Kirillov–Kostant–Souriau forms of its coadjoint orbits, the basic noncompact example of the
orbit method. Tangent vectors at the identity are read in the model space `ℝ³` through
`tangentSpaceCastModel`.

Conjugation by `p` is the linear map `(x, y, z) ↦ (x, y, z + p.x y - p.y x)`, so the adjoint action
is `Ad_p (a, b, c) = (a, b, c + p.x b - p.y a)`
(`TauCeti.Nil.tangentSpaceCastModel_adjointContinuousLinearMap`), and the bracket of `𝔫` is
`⁅(a, b, c), (a', b', c')⁆ = (0, 0, a b' - b a')` (`TauCeti.Nil.tangentSpaceCastModel_lie`).
Hence `(a, b, c) ↦ a X + b Y + c Z` is an isomorphism of Lie algebras from `𝔫` onto the
Heisenberg Lie algebra of strictly upper triangular `3 × 3` matrices
(`TauCeti.Nil.lieAlgebraEquiv`), and it carries `Ad_p` to conjugation by the unipotent matrix of
`p` (`TauCeti.Nil.lieAlgebraEquiv_adjointRepresentation`). The orbit computations of
`TauCeti.Algebra.Lie.Heisenberg.Orbit` then transfer to the Lie group `Nil`.

Write `X = ∂_x`, `Y = ∂_y`, `Z = ∂_z` for the coordinate generators and
`(p, q, r) = (ν X, ν Y, ν Z)` for a functional `ν ∈ 𝔫*`. The coadjoint action of `g = (x, y, z)` is
`Ad*_g (p, q, r) = (p + r y, q - r x, r)`
(`TauCeti.Nil.coadjointRepresentation_apply_lieAlgebraEquiv_symm_heisenbergX`,
`TauCeti.Nil.coadjointRepresentation_apply_lieAlgebraEquiv_symm_heisenbergY`); in particular `r` is
constant on coadjoint orbits.

* The adjoint orbit of `(a, b, c)` is the affine line `{(a, b, c') | c' ∈ ℝ}` when
  `(a, b) ≠ (0, 0)` (`TauCeti.Nil.range_adjointRepresentation_apply_of_ne_zero`) and a point
  otherwise. The nontrivial adjoint orbits are odd-dimensional.
* The coadjoint orbit of `ν` is the plane `{μ | μ Z = r}` when `r ≠ 0`
  (`TauCeti.Nil.range_coadjointRepresentation_apply_of_ne_zero`) and the point `{ν}` when `r = 0`
  (`TauCeti.Nil.range_coadjointRepresentation_apply_of_eq_zero`), fixed by all of `Nil`
  (`TauCeti.Nil.stabilizer_coadjointRepresentation_of_eq_zero`). For `r ≠ 0` the coadjoint
  stabilizer is the centre of `Nil` (`TauCeti.Nil.stabilizer_coadjointRepresentation_of_ne_zero`),
  and the orbit manifold `Nil ⧸ Nil_ν` is two-dimensional
  (`TauCeti.Nil.finrank_quotientModelSpace_stabilizer_coadjointRepresentation_of_ne_zero`).
* On the orbit manifold, the generator of `ξ = (s, t, u)` is `(t r, -s r, 0)` in the coordinates
  `(μ X, μ Y, μ Z)` of the orbit map
  (`TauCeti.Nil.mvfderiv_orbitMap_coadjointRepresentation_apply_fundamentalVectorField`), and the
  KKS form pairs the generators of `ξ` and `ξ' = (s', t', u')` to `r (s t' - t s')`
  (`TauCeti.Nil.eval₂_coadjointOrbitForm_fundamentalVectorField`). On the plane `r = r₀ ≠ 0` the
  KKS form is therefore `dp ∧ dq / r₀` in the coordinates `p = μ X`, `q = μ Y`.

**The orbit as a symplectic plane.** For `r = ν Z ≠ 0` the coordinates `(p, q) = (μ X, μ Y)` of
the orbit map are a diffeomorphism `Nil ⧸ Nil_ν ≃ ℝ × ℝ`
(`TauCeti.Nil.coadjointOrbitPlaneDiffeomorph`), sending the coset of `g = (x, y, z)` to
`(ν X + r y, ν Y - r x)` (`TauCeti.Nil.coadjointOrbitPlaneDiffeomorph_mk`), with inverse
`(p, q) ↦ [((ν Y - q) / r, (p - ν X) / r, 0)]`. So the coset space, with its homogeneous smooth
structure, is identified with the plane `r = r₀` of `𝔫*`, and not only as a set. In these
coordinates the KKS form is the constant form `dp ∧ dq / r₀`: the diffeomorphism pulls
`r⁻¹ (dp ∧ dq)` back to the KKS form
(`TauCeti.Nil.mpullback_coadjointOrbitPlaneDiffeomorph_stdSymplecticForm`), and its inverse pulls
the KKS form back to `r⁻¹ (dp ∧ dq)`
(`TauCeti.Nil.mpullback_coadjointOrbitPlaneDiffeomorph_symm_coadjointOrbitForm`). Here `dp ∧ dq` is
the standard symplectic form `TauCeti.stdSymplecticForm` of `ℝ × ℝ`, as a constant two-form. Since
the generators span every tangent space of the orbit, both forms are determined by their values on
generators, which the formula `(t r, -s r)` for the generators compares.

## Main definitions

* `TauCeti.Nil.lieAlgebraEquiv`: the Lie algebra of `Nil` is the Heisenberg Lie algebra.
* `TauCeti.Nil.coadjointOrbitPlaneDiffeomorph`: for `ν Z ≠ 0`, the coordinates `(μ X, μ Y)` as a
  diffeomorphism of the coadjoint orbit `Nil ⧸ Nil_ν` onto the plane.

## Main results

* `TauCeti.Nil.tangentSpaceCastModel_adjointContinuousLinearMap`,
  `TauCeti.Nil.tangentSpaceCastModel_lie`: the adjoint action and the bracket in coordinates.
* `TauCeti.Nil.coadjointRepresentation_comp_lieAlgebraEquiv`: the coadjoint action of `Nil` is that
  of the Heisenberg group.
* `TauCeti.Nil.range_coadjointRepresentation_apply_of_ne_zero`,
  `TauCeti.Nil.range_coadjointRepresentation_apply_of_eq_zero`: the coadjoint orbits.
* `TauCeti.Nil.eval₂_coadjointOrbitForm_fundamentalVectorField`: the KKS form on generators.
* `TauCeti.Nil.mpullback_coadjointOrbitPlaneDiffeomorph_stdSymplecticForm`,
  `TauCeti.Nil.mpullback_coadjointOrbitPlaneDiffeomorph_symm_coadjointOrbitForm`: in the coordinates
  `(p, q)` the KKS form of the orbit through `ν` with `ν Z = r₀ ≠ 0` is `dp ∧ dq / r₀`.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Chapter 2 (representations and orbits of the Heisenberg group).
-/

public section

open Module
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Nil

local notation "R3" => ℝ × ℝ × ℝ

/-! ### The adjoint action -/

/-- Conjugation by `p`, `(x, y, z) ↦ (x, y, z + p.x y - p.y x)`, read in the model space. -/
private def conjL (p : Nil) : R3 →L[ℝ] R3 :=
  .id ℝ R3 + (p.x • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (.snd ℝ ℝ (ℝ × ℝ)) -
    p.y • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).smulRight ((0, 0, 1) : R3)

/-- Conjugation by `p` is the linear map `conjL p` in the global coordinates. -/
private theorem toProd_comp_conjDiffeomorph_comp_toProd_symm (p : Nil) :
    toProd ∘ (Lie.conjDiffeomorph (I := 𝓘(ℝ, R3)) (n := 1) p) ∘ toProd.symm = conjL p := by
  funext r
  ext <;> simp [conjL]
  ring

/-- Reading a tangent vector of `Nil` in the model space does not depend on the base point. -/
private theorem tangentSpaceCastModel_congr {p q : Nil} (h : p = q) (w : TangentSpace 𝓘(ℝ, R3) p) :
    tangentSpaceCastModel 𝓘(ℝ, R3) q w = tangentSpaceCastModel 𝓘(ℝ, R3) p w := by
  subst h
  rfl

/-- **The adjoint action of Nil.** Read in the model space `ℝ³`, the differential
`Ad_p = d(conj_p)_1` of conjugation by `p` is `(a, b, c) ↦ (a, b, c + p.x b - p.y a)`. -/
theorem tangentSpaceCastModel_adjointContinuousLinearMap (p : Nil)
    (v : GroupLieAlgebra 𝓘(ℝ, R3) Nil) :
    let u := tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) v
    tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) (Lie.adjointContinuousLinearMap (I := 𝓘(ℝ, R3)) p v) =
      (u.1, u.2.1, u.2.2 + p.x * u.2.1 - p.y * u.1) := by
  intro u
  have h1 : Lie.conjDiffeomorph (I := 𝓘(ℝ, R3)) (n := 1) p 1 = 1 := by simp
  rw [Lie.adjointContinuousLinearMap_apply, tangentSpaceCastModel_congr h1,
    ← fderiv_toProd_conj_apply, toProd_comp_conjDiffeomorph_comp_toProd_symm, (conjL p).fderiv]
  ext <;> simp [conjL, u, add_sub_assoc]

/-- `Ad_(g⁻¹)` adds a multiple of the central generator `∂_z`. -/
private theorem adjointContinuousLinearMap_inv_apply (g : Nil)
    (v : GroupLieAlgebra 𝓘(ℝ, R3) Nil) :
    Lie.adjointContinuousLinearMap (I := 𝓘(ℝ, R3)) g⁻¹ v =
      v + (g.y * (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) v).1 -
          g.x * (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) v).2.1) •
        (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil)).symm (0, 0, 1) := by
  apply (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil)).injective
  rw [tangentSpaceCastModel_adjointContinuousLinearMap, map_add, map_smul,
    ContinuousLinearEquiv.apply_symm_apply]
  ext <;> simp
  ring

/-! ### The Lie bracket -/

section Bracket

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **The Lie bracket of Nil.** Read in the model space `ℝ³`, the bracket of the Lie algebra of
`Nil` is `⁅(a, b, c), (a', b', c')⁆ = (0, 0, a b' - b a')`: the only nonzero bracket of the
coordinate vectors is `⁅∂_x, ∂_y⁆ = ∂_z`. -/
@[simp]
theorem tangentSpaceCastModel_lie (v w : GroupLieAlgebra 𝓘(ℝ, R3) Nil) :
    let u := tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) v
    let u' := tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) w
    tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ⁅v, w⁆ = (0, 0, u.1 * u'.2.1 - u.2.1 * u'.1) := by
  intro u u'
  set Z := (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil)).symm (0, 0, 1)
  suffices h : ⁅v, w⁆ = (u.1 * u'.2.1 - u.2.1 * u'.1) • Z by
    rw [h, map_smul, ContinuousLinearEquiv.apply_symm_apply]
    simp
  rw [← sub_eq_zero, ← forall_dual_apply_eq_zero_iff ℝ]
  intro ν
  rw [map_sub, ← Lie.mvfderiv_coadjointRepresentation_apply_one, sub_eq_zero]
  -- In the global coordinates, `g ↦ (Ad*_g ν) v = ν (Ad_(g⁻¹) v)` is affine.
  set L : R3 →L[ℝ] ℝ := (ν Z * u.1) • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (.snd ℝ ℝ (ℝ × ℝ)) -
    (ν Z * u.2.1) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
  have hfun : (fun g : Nil ↦ Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil g ν v) =
      (fun r : R3 ↦ ν v + L r) ∘ toProd := by
    funext g
    rw [Lie.coadjointRepresentation_apply, adjointContinuousLinearMap_inv_apply]
    simp [L, u]
    ring
  rw [hfun, mvfderiv_comp_apply_of_differentiableAt (by fun_prop)
      (contMDiff_toProd.mdifferentiableAt one_ne_zero), mvfderiv_apply_eq_mfderiv_apply,
    mfderiv_toProd_apply, fderiv_const_add, L.fderiv]
  simp [L, u']
  ring

end Bracket

/-! ### The Lie algebra is the Heisenberg Lie algebra -/

/-- **The Lie algebra of Nil is the Heisenberg Lie algebra.** The tangent vector `(a, b, c)` of
`Nil` at the identity, read in the model space `ℝ³`, corresponds to `a X + b Y + c Z`, where
`X = E₀₁`, `Y = E₁₂` and `Z = E₀₂` are the matrix units of the strictly upper triangular
`3 × 3` matrices. -/
def lieAlgebraEquiv : GroupLieAlgebra 𝓘(ℝ, R3) Nil ≃ₗ⁅ℝ⁆ heisenberg ℝ where
  toFun v :=
    (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) v).1 • heisenbergX ℝ +
      (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) v).2.1 • heisenbergY ℝ +
      (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) v).2.2 • heisenbergZ ℝ
  map_add' v w := by
    simp only [map_add, Prod.fst_add, Prod.snd_add, add_smul]
    abel
  map_smul' c v := by
    simp only [map_smul, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul, RingHom.id_apply,
      smul_add]
  map_lie' {v w} := by
    rw [lie_eq_smul_heisenbergZ, tangentSpaceCastModel_lie]
    simp [mul_comm]
  invFun A := (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil)).symm
    ((A : Matrix (Fin 3) (Fin 3) ℝ) 0 1, (A : Matrix (Fin 3) (Fin 3) ℝ) 1 2,
      (A : Matrix (Fin 3) (Fin 3) ℝ) 0 2)
  left_inv v := by
    apply (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil)).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    simp
  right_inv A := by
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    exact (eq_smul_heisenbergX_add_smul_heisenbergY_add_smul_heisenbergZ A).symm

theorem lieAlgebraEquiv_apply (v : GroupLieAlgebra 𝓘(ℝ, R3) Nil) :
    lieAlgebraEquiv v =
      (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) v).1 • heisenbergX ℝ +
        (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) v).2.1 • heisenbergY ℝ +
        (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) v).2.2 • heisenbergZ ℝ :=
  (rfl)

@[simp]
theorem tangentSpaceCastModel_lieAlgebraEquiv_symm (A : heisenberg ℝ) :
    tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) (lieAlgebraEquiv.symm A) =
      ((A : Matrix (Fin 3) (Fin 3) ℝ) 0 1, (A : Matrix (Fin 3) (Fin 3) ℝ) 1 2,
        (A : Matrix (Fin 3) (Fin 3) ℝ) 0 2) :=
  ContinuousLinearEquiv.apply_symm_apply _ _

@[simp]
theorem lieAlgebraEquiv_apply_zero_one (v : GroupLieAlgebra 𝓘(ℝ, R3) Nil) :
    (lieAlgebraEquiv v : Matrix (Fin 3) (Fin 3) ℝ) 0 1 =
      (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) v).1 := by
  simp [lieAlgebraEquiv_apply]

@[simp]
theorem lieAlgebraEquiv_apply_one_two (v : GroupLieAlgebra 𝓘(ℝ, R3) Nil) :
    (lieAlgebraEquiv v : Matrix (Fin 3) (Fin 3) ℝ) 1 2 =
      (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) v).2.1 := by
  simp [lieAlgebraEquiv_apply]

@[simp]
theorem lieAlgebraEquiv_apply_zero_two (v : GroupLieAlgebra 𝓘(ℝ, R3) Nil) :
    (lieAlgebraEquiv v : Matrix (Fin 3) (Fin 3) ℝ) 0 2 =
      (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) v).2.2 := by
  simp [lieAlgebraEquiv_apply]

/-- **Every bracket in the Lie algebra of Nil is central**: `⁅(a, b, c), (a', b', c')⁆` is
`a b' - b a'` times the central generator `Z = lieAlgebraEquiv.symm (heisenbergZ ℝ)`. -/
theorem lie_eq_smul_lieAlgebraEquiv_symm_heisenbergZ (ξ ξ' : GroupLieAlgebra 𝓘(ℝ, R3) Nil) :
    ⁅ξ, ξ'⁆ = ((tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).1 *
          (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ').2.1 -
        (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).2.1 *
          (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ').1) •
      lieAlgebraEquiv.symm (heisenbergZ ℝ) := by
  rw [← lieAlgebraEquiv.symm_apply_apply ⁅ξ, ξ'⁆, LieEquiv.map_lie, lie_eq_smul_heisenbergZ,
    map_smul]
  simp [lieAlgebraEquiv_apply, mul_comm]

/-! ### Adjoint and coadjoint actions through the Heisenberg Lie algebra -/

/-- **The adjoint action of Nil is conjugation of strictly upper triangular matrices.** Under
`lieAlgebraEquiv`, `Ad_p` is the adjoint action `A ↦ g A g⁻¹` of the unipotent matrix `g` of
`toHeisenberg p`. -/
theorem lieAlgebraEquiv_adjointRepresentation (p : Nil) (v : GroupLieAlgebra 𝓘(ℝ, R3) Nil) :
    lieAlgebraEquiv (Lie.adjointRepresentation ℝ 𝓘(ℝ, R3) Nil p v) =
      HeisenbergGroup.adjointRepresentation ℝ (toHeisenberg p) (lieAlgebraEquiv v) := by
  rw [HeisenbergGroup.adjointRepresentation_apply, lie_eq_smul_heisenbergZ]
  simp only [Lie.adjointRepresentation_apply, lieAlgebraEquiv_apply,
    tangentSpaceCastModel_adjointContinuousLinearMap]
  simp
  module

/-! ### Adjoint orbits -/

/-- Adjoint orbits of Nil are adjoint orbits of the Heisenberg group, carried back along
`lieAlgebraEquiv`. -/
private theorem range_adjointRepresentation_apply_eq_image (v : GroupLieAlgebra 𝓘(ℝ, R3) Nil) :
    Set.range (fun p : Nil ↦ Lie.adjointRepresentation ℝ 𝓘(ℝ, R3) Nil p v) =
      lieAlgebraEquiv.symm ''
        Set.range (fun a ↦ HeisenbergGroup.adjointRepresentation ℝ a (lieAlgebraEquiv v)) := by
  have h : (fun p : Nil ↦ Lie.adjointRepresentation ℝ 𝓘(ℝ, R3) Nil p v) =
      (fun a ↦ lieAlgebraEquiv.symm (HeisenbergGroup.adjointRepresentation ℝ a
        (lieAlgebraEquiv v))) ∘ toHeisenberg := by
    funext p
    rw [Function.comp_apply, ← lieAlgebraEquiv_adjointRepresentation, LieEquiv.symm_apply_apply]
  rw [h, toHeisenberg.surjective.range_comp]
  exact Set.range_comp lieAlgebraEquiv.symm _

/-- **The adjoint orbit of a noncentral element of the Lie algebra of Nil is an affine line**: for
`(a, b) ≠ (0, 0)`, the orbit of `(a, b, c)` is the line `{(a, b, c') | c' ∈ ℝ}`, the image of
`a X + b Y + ℝ Z`. Adjoint orbits are thus one-dimensional, unlike the coadjoint orbits. -/
theorem range_adjointRepresentation_apply_of_ne_zero {v : GroupLieAlgebra 𝓘(ℝ, R3) Nil}
    (hv : ((tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) v).1,
      (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) v).2.1) ≠ (0, 0)) :
    Set.range (fun p : Nil ↦ Lie.adjointRepresentation ℝ 𝓘(ℝ, R3) Nil p v) =
      {w | (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) w).1 =
          (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) v).1 ∧
        (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) w).2.1 =
          (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) v).2.1} := by
  rw [range_adjointRepresentation_apply_eq_image,
    HeisenbergGroup.range_adjointRepresentation_apply_of_ne_zero
      (by simpa [lieAlgebraEquiv_apply, or_iff_not_imp_left] using hv)]
  ext w
  refine ⟨?_, fun hw ↦ ⟨lieAlgebraEquiv w, ?_, lieAlgebraEquiv.symm_apply_apply w⟩⟩
  · rintro ⟨B, hB, rfl⟩
    simpa [lieAlgebraEquiv_apply] using hB
  · simpa [lieAlgebraEquiv_apply] using hw

/-- **The adjoint orbit of a central element of the Lie algebra of Nil is a point.** -/
theorem range_adjointRepresentation_apply_of_eq_zero {v : GroupLieAlgebra 𝓘(ℝ, R3) Nil}
    (h₁ : (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) v).1 = 0)
    (h₂ : (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) v).2.1 = 0) :
    Set.range (fun p : Nil ↦ Lie.adjointRepresentation ℝ 𝓘(ℝ, R3) Nil p v) = {v} := by
  rw [range_adjointRepresentation_apply_eq_image,
    HeisenbergGroup.range_adjointRepresentation_apply_of_eq_zero
      (by simp [lieAlgebraEquiv_apply, h₁]) (by simp [lieAlgebraEquiv_apply, h₂]),
    Set.image_singleton, LieEquiv.symm_apply_apply]

/-- **The coadjoint action of Nil is the coadjoint action of the Heisenberg group**: pulling
functionals back along `lieAlgebraEquiv` intertwines the two. -/
theorem coadjointRepresentation_comp_lieAlgebraEquiv (p : Nil) (ν : Dual ℝ (heisenberg ℝ)) :
    Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil p
        (ν ∘ₗ (lieAlgebraEquiv : GroupLieAlgebra 𝓘(ℝ, R3) Nil →ₗ[ℝ] heisenberg ℝ)) =
      HeisenbergGroup.coadjointRepresentation ℝ (toHeisenberg p) ν ∘ₗ
        (lieAlgebraEquiv : GroupLieAlgebra 𝓘(ℝ, R3) Nil →ₗ[ℝ] heisenberg ℝ) := by
  refine LinearMap.ext fun v ↦ ?_
  simp only [Lie.coadjointRepresentation_apply, LinearMap.comp_apply,
    HeisenbergGroup.coadjointRepresentation_apply_apply, ← map_inv]
  rw [← Lie.adjointRepresentation_apply, LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv,
    lieAlgebraEquiv_adjointRepresentation]

/-! ### Coadjoint orbits -/

/-- Every functional on the Lie algebra of Nil is pulled back from the Heisenberg Lie algebra. -/
private theorem comp_lieAlgebraEquiv_symm_comp (ν : Dual ℝ (GroupLieAlgebra 𝓘(ℝ, R3) Nil)) :
    (ν ∘ₗ (lieAlgebraEquiv.symm : heisenberg ℝ →ₗ[ℝ] GroupLieAlgebra 𝓘(ℝ, R3) Nil)) ∘ₗ
        (lieAlgebraEquiv : GroupLieAlgebra 𝓘(ℝ, R3) Nil →ₗ[ℝ] heisenberg ℝ) = ν :=
  LinearMap.ext fun v ↦ by simp

/-- **Coadjoint orbits of Nil are coadjoint orbits of the Heisenberg group**, pulled back along
`lieAlgebraEquiv`. -/
theorem range_coadjointRepresentation_comp (ν : Dual ℝ (heisenberg ℝ)) :
    Set.range (fun p : Nil ↦ Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil p
        (ν ∘ₗ (lieAlgebraEquiv : GroupLieAlgebra 𝓘(ℝ, R3) Nil →ₗ[ℝ] heisenberg ℝ))) =
      (fun μ : Dual ℝ (heisenberg ℝ) ↦
          μ ∘ₗ (lieAlgebraEquiv : GroupLieAlgebra 𝓘(ℝ, R3) Nil →ₗ[ℝ] heisenberg ℝ)) ''
        Set.range (fun a ↦ HeisenbergGroup.coadjointRepresentation ℝ a ν) := by
  rw [← Set.range_comp]
  simp_rw [coadjointRepresentation_comp_lieAlgebraEquiv]
  exact toHeisenberg.surjective.range_comp
    (fun a ↦ HeisenbergGroup.coadjointRepresentation ℝ a ν ∘ₗ
      (lieAlgebraEquiv : GroupLieAlgebra 𝓘(ℝ, R3) Nil →ₗ[ℝ] heisenberg ℝ))

/-- The value `r = ν Z` of a functional on the central generator is invariant under the coadjoint
action of Nil. -/
theorem coadjointRepresentation_apply_lieAlgebraEquiv_symm_heisenbergZ (p : Nil)
    (ν : Dual ℝ (GroupLieAlgebra 𝓘(ℝ, R3) Nil)) :
    Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil p ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)) =
      ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)) := by
  conv_lhs =>
    rw [← comp_lieAlgebraEquiv_symm_comp ν, coadjointRepresentation_comp_lieAlgebraEquiv]
  simp

/-- The first coordinate `p = ν X` of a functional transforms under the coadjoint action of Nil as
`p ↦ p + r y`, where `r = ν Z`. -/
theorem coadjointRepresentation_apply_lieAlgebraEquiv_symm_heisenbergX (p : Nil)
    (ν : Dual ℝ (GroupLieAlgebra 𝓘(ℝ, R3) Nil)) :
    Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil p ν (lieAlgebraEquiv.symm (heisenbergX ℝ)) =
      ν (lieAlgebraEquiv.symm (heisenbergX ℝ)) +
        p.y * ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)) := by
  conv_lhs =>
    rw [← comp_lieAlgebraEquiv_symm_comp ν, coadjointRepresentation_comp_lieAlgebraEquiv]
  simp [HeisenbergGroup.coadjointRepresentation_apply_heisenbergX]

/-- The second coordinate `q = ν Y` of a functional transforms under the coadjoint action of Nil
as `q ↦ q - r x`, where `r = ν Z`. -/
theorem coadjointRepresentation_apply_lieAlgebraEquiv_symm_heisenbergY (p : Nil)
    (ν : Dual ℝ (GroupLieAlgebra 𝓘(ℝ, R3) Nil)) :
    Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil p ν (lieAlgebraEquiv.symm (heisenbergY ℝ)) =
      ν (lieAlgebraEquiv.symm (heisenbergY ℝ)) -
        p.x * ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)) := by
  conv_lhs =>
    rw [← comp_lieAlgebraEquiv_symm_comp ν, coadjointRepresentation_comp_lieAlgebraEquiv]
  simp [HeisenbergGroup.coadjointRepresentation_apply_heisenbergY]

/-- **The coadjoint orbit of Nil through a functional `ν` with `ν Z ≠ 0` is the plane
`{μ | μ Z = ν Z}`**, where `Z = ∂_z` is the central generator. -/
theorem range_coadjointRepresentation_apply_of_ne_zero
    {ν : Dual ℝ (GroupLieAlgebra 𝓘(ℝ, R3) Nil)}
    (hν : ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)) ≠ 0) :
    Set.range (fun p : Nil ↦ Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil p ν) =
      {μ | μ (lieAlgebraEquiv.symm (heisenbergZ ℝ)) =
        ν (lieAlgebraEquiv.symm (heisenbergZ ℝ))} := by
  conv_lhs => rw [← comp_lieAlgebraEquiv_symm_comp ν]
  rw [range_coadjointRepresentation_comp,
    HeisenbergGroup.range_coadjointRepresentation_apply_of_isUnit (by simpa using hν)]
  ext μ
  refine ⟨?_, fun hμ ↦ ⟨_, ?_, comp_lieAlgebraEquiv_symm_comp μ⟩⟩
  · rintro ⟨μ', hμ', rfl⟩
    simpa using hμ'
  · simpa using hμ

/-- **The coadjoint orbit of Nil through a functional vanishing on the central generator is a
point.** -/
theorem range_coadjointRepresentation_apply_of_eq_zero
    {ν : Dual ℝ (GroupLieAlgebra 𝓘(ℝ, R3) Nil)}
    (hν : ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)) = 0) :
    Set.range (fun p : Nil ↦ Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil p ν) = {ν} := by
  conv_lhs => rw [← comp_lieAlgebraEquiv_symm_comp ν]
  rw [range_coadjointRepresentation_comp,
    HeisenbergGroup.range_coadjointRepresentation_apply_of_eq_zero (by simpa using hν),
    Set.image_singleton, comp_lieAlgebraEquiv_symm_comp]

/-- **The coadjoint stabilizer of a functional `ν` with `ν Z ≠ 0` is the centre of Nil.** -/
theorem stabilizer_coadjointRepresentation_of_ne_zero
    {ν : Dual ℝ (GroupLieAlgebra 𝓘(ℝ, R3) Nil)}
    (hν : ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)) ≠ 0) :
    (Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).stabilizer ν = Subgroup.center Nil := by
  ext p
  rw [Representation.mem_stabilizer, mem_center_iff]
  conv_lhs =>
    rw [← comp_lieAlgebraEquiv_symm_comp ν, coadjointRepresentation_comp_lieAlgebraEquiv]
  rw [LinearMap.cancel_right lieAlgebraEquiv.toLinearEquiv.surjective,
    ← Representation.mem_stabilizer,
    HeisenbergGroup.stabilizer_coadjointRepresentation_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero (by simpa using hν)), HeisenbergGroup.mem_zAxis_iff]
  simp

/-- **A functional vanishing on the central generator is fixed by all of Nil.** -/
theorem stabilizer_coadjointRepresentation_of_eq_zero
    {ν : Dual ℝ (GroupLieAlgebra 𝓘(ℝ, R3) Nil)}
    (hν : ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)) = 0) :
    (Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).stabilizer ν = ⊤ := by
  refine eq_top_iff.mpr fun g _ ↦ Representation.mem_stabilizer.mpr ?_
  have h := range_coadjointRepresentation_apply_of_eq_zero hν
  exact Set.mem_singleton_iff.mp (h ▸ Set.mem_range_self g)

/-- **The coadjoint orbits of Nil through functionals with `ν Z ≠ 0` are two-dimensional**: the
model space of the orbit manifold `Nil ⧸ Nil_ν` has dimension `2`. -/
theorem finrank_quotientModelSpace_stabilizer_coadjointRepresentation_of_ne_zero
    {ν : Dual ℝ (GroupLieAlgebra 𝓘(ℝ, R3) Nil)}
    (hν : ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)) ≠ 0) :
    finrank ℝ (Subgroup.QuotientModelSpace 𝓘(ℝ, R3)
      ((Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).stabilizer ν)) = 2 := by
  rw [Dual.finrank_quotientModelSpace_eq_finrank_quotient_lieAnnihilator,
    (Dual.quotientLieAnnihilatorEquiv _ (f := lieAlgebraEquiv.toLieHom)
      lieAlgebraEquiv.surjective (comp_lieAlgebraEquiv_symm_comp ν)).finrank_eq]
  exact finrank_quotient_lieAnnihilator_heisenberg (by simpa using hν)

/-! ### The Kirillov–Kostant–Souriau form -/

/-- **Points of a coadjoint orbit of Nil on brackets.** At every point `μ` of the orbit
`Nil ⧸ Nil_ν`, `μ ⁅ξ, ξ'⁆ = r (s t' - t s')` for `ξ = (s, t, u)` and `ξ' = (s', t', u')`, where
`r = ν Z` is the constant value of the orbit on the central generator. -/
theorem orbitMap_coadjointRepresentation_apply_lie (ν : Dual ℝ (GroupLieAlgebra 𝓘(ℝ, R3) Nil))
    (x : Nil ⧸ (Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).stabilizer ν)
    (ξ ξ' : GroupLieAlgebra 𝓘(ℝ, R3) Nil) :
    (Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).orbitMap ν x ⁅ξ, ξ'⁆ =
      ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)) *
        ((tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).1 *
            (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ').2.1 -
          (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).2.1 *
            (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ').1) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [Representation.orbitMap_mk, lie_eq_smul_lieAlgebraEquiv_symm_heisenbergZ, map_smul,
    coadjointRepresentation_apply_lieAlgebraEquiv_symm_heisenbergZ, smul_eq_mul, mul_comm]

/-- **The Kirillov–Kostant–Souriau form of a coadjoint orbit of Nil.** At every point of the
orbit `Nil ⧸ Nil_ν`, the KKS form pairs the generators of `ξ = (s, t, u)` and `ξ' = (s', t', u')`
to `r (s t' - t s')`, where `r = ν Z` is the constant value of the orbit on the central generator.
So on the plane `r = r₀ ≠ 0` it is `dp ∧ dq / r₀` in the coordinates `p = μ X`, `q = μ Y`
(`TauCeti.Nil.mpullback_coadjointOrbitPlaneDiffeomorph_stdSymplecticForm`). -/
theorem eval₂_coadjointOrbitForm_fundamentalVectorField
    (ν : Dual ℝ (GroupLieAlgebra 𝓘(ℝ, R3) Nil))
    (x : Nil ⧸ (Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).stabilizer ν)
    (ξ ξ' : GroupLieAlgebra 𝓘(ℝ, R3) Nil) :
    SmoothBundleForm.eval₂ ν.coadjointOrbitForm x
        (fundamentalVectorField 𝓘(ℝ, Subgroup.QuotientModelSpace 𝓘(ℝ, R3)
          ((Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).stabilizer ν)) ξ x)
        (fundamentalVectorField 𝓘(ℝ, Subgroup.QuotientModelSpace 𝓘(ℝ, R3)
          ((Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).stabilizer ν)) ξ' x) =
      ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)) *
        ((tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).1 *
            (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ').2.1 -
          (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).2.1 *
            (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ').1) := by
  rw [Dual.eval₂_coadjointOrbitForm_fundamentalVectorField,
    orbitMap_coadjointRepresentation_apply_lie]

/-- **The generators of a coadjoint orbit of Nil.** Along the generator of `ξ = (s, t, u)` at a
point `μ` of the orbit, with `r = μ Z`, the coordinate `⟨μ, ζ⟩` of the orbit map changes at the
rate `r (a t - b s)` for `ζ = (a, b, c)`. So in the coordinates `(p, q, r) = (μ X, μ Y, μ Z)` the
generator is `(t r, -s r, 0)`. -/
theorem mvfderiv_orbitMap_coadjointRepresentation_apply_fundamentalVectorField
    (ν : Dual ℝ (GroupLieAlgebra 𝓘(ℝ, R3) Nil))
    (x : Nil ⧸ (Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).stabilizer ν)
    (ξ ζ : GroupLieAlgebra 𝓘(ℝ, R3) Nil) :
    mvfderiv 𝓘(ℝ, Subgroup.QuotientModelSpace 𝓘(ℝ, R3)
          ((Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).stabilizer ν))
        (fun y ↦ (Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).orbitMap ν y ζ) x
        (fundamentalVectorField 𝓘(ℝ, Subgroup.QuotientModelSpace 𝓘(ℝ, R3)
          ((Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).stabilizer ν)) ξ x) =
      ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)) *
        ((tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ζ).1 *
            (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).2.1 -
          (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ζ).2.1 *
            (tangentSpaceCastModel 𝓘(ℝ, R3) (1 : Nil) ξ).1) := by
  rw [Dual.mvfderiv_orbitMap_coadjointRepresentation_apply_fundamentalVectorField,
    orbitMap_coadjointRepresentation_apply_lie]

/-! ### The coadjoint orbit as a symplectic plane -/

variable {ν : Dual ℝ (GroupLieAlgebra 𝓘(ℝ, R3) Nil)}

/-- When `ν Z ≠ 0`, the coset of `g` in the coadjoint orbit `Nil ⧸ Nil_ν` is the coset of the
point `(g.x, g.y, 0)`, since the stabilizer is the centre, the `z`-axis. -/
private theorem coe_toProd_symm_x_y_zero (hν : ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)) ≠ 0)
    (g : Nil) :
    (toProd.symm (g.x, g.y, 0) : Nil ⧸ (Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).stabilizer ν) =
      (g : Nil ⧸ (Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).stabilizer ν) := by
  rw [QuotientGroup.eq, stabilizer_coadjointRepresentation_of_ne_zero hν, mem_center_iff]
  simp

/-- **The coadjoint orbit of Nil is a plane.** For a functional `ν` with `r = ν Z ≠ 0`, the
coordinates `(p, q) = (μ X, μ Y)` of the orbit map `[g] ↦ μ = Ad*_g ν` are a diffeomorphism of the
coadjoint orbit `Nil ⧸ Nil_ν`, with its homogeneous smooth structure, onto `ℝ × ℝ`. Its inverse
sends `(p, q)` to the coset of `((ν Y - q) / r, (p - ν X) / r, 0)`. -/
def coadjointOrbitPlaneDiffeomorph (hν : ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)) ≠ 0) :
    (Nil ⧸ (Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).stabilizer ν) ≃ₘ⟮𝓘(ℝ,
      Subgroup.QuotientModelSpace 𝓘(ℝ, R3)
        ((Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).stabilizer ν)), 𝓘(ℝ, ℝ × ℝ)⟯ ℝ × ℝ where
  toFun x := ((Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).orbitMap ν x
      (lieAlgebraEquiv.symm (heisenbergX ℝ)),
    (Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).orbitMap ν x
      (lieAlgebraEquiv.symm (heisenbergY ℝ)))
  invFun c := (toProd.symm ((ν (lieAlgebraEquiv.symm (heisenbergY ℝ)) - c.2) /
      ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)),
    (c.1 - ν (lieAlgebraEquiv.symm (heisenbergX ℝ))) /
      ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)), 0) : Nil)
  left_inv x := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [Representation.orbitMap_mk,
      coadjointRepresentation_apply_lieAlgebraEquiv_symm_heisenbergX,
      coadjointRepresentation_apply_lieAlgebraEquiv_symm_heisenbergY]
    rw [← coe_toProd_symm_x_y_zero hν g]
    congr 2
    simp [hν]
  right_inv c := by
    simp only [Representation.orbitMap_mk,
      coadjointRepresentation_apply_lieAlgebraEquiv_symm_heisenbergX,
      coadjointRepresentation_apply_lieAlgebraEquiv_symm_heisenbergY, x_toProd_symm,
      y_toProd_symm]
    ext <;> field_simp <;> ring
  contMDiff_toFun := (ν.contMDiff_orbitMap_coadjointRepresentation_apply _).prodMk_space
    (ν.contMDiff_orbitMap_coadjointRepresentation_apply _)
  contMDiff_invFun := ν.isSubmersion_quotientMk_stabilizer_coadjointRepresentation.contMDiff.comp
    (contMDiff_toProd_symm.comp (ContDiff.contMDiff (f := fun c : ℝ × ℝ ↦
      ((ν (lieAlgebraEquiv.symm (heisenbergY ℝ)) - c.2) / ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)),
        (c.1 - ν (lieAlgebraEquiv.symm (heisenbergX ℝ))) /
          ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)), (0 : ℝ))) (by fun_prop)))

/-- The diffeomorphism of the coadjoint orbit onto the plane reads the coordinates
`(μ X, μ Y)` of the orbit map. -/
@[simp]
theorem coadjointOrbitPlaneDiffeomorph_apply (hν : ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)) ≠ 0)
    (x : Nil ⧸ (Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).stabilizer ν) :
    coadjointOrbitPlaneDiffeomorph hν x =
      ((Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).orbitMap ν x
          (lieAlgebraEquiv.symm (heisenbergX ℝ)),
        (Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).orbitMap ν x
          (lieAlgebraEquiv.symm (heisenbergY ℝ))) :=
  (rfl)

/-- The inverse of the diffeomorphism of the coadjoint orbit onto the plane sends `(p, q)` to the
coset of `((ν Y - q) / r, (p - ν X) / r, 0)`, where `r = ν Z`. -/
@[simp]
theorem coadjointOrbitPlaneDiffeomorph_symm_apply
    (hν : ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)) ≠ 0) (c : ℝ × ℝ) :
    (coadjointOrbitPlaneDiffeomorph hν).symm c =
      ((toProd.symm ((ν (lieAlgebraEquiv.symm (heisenbergY ℝ)) - c.2) /
          ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)),
        (c.1 - ν (lieAlgebraEquiv.symm (heisenbergX ℝ))) /
          ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)), 0) : Nil) :
        Nil ⧸ (Lie.coadjointRepresentation ℝ 𝓘(ℝ, R3) Nil).stabilizer ν) :=
  (rfl)

/-- The diffeomorphism of the coadjoint orbit onto the plane sends the coset of `g = (x, y, z)` to
`(ν X + r y, ν Y - r x)`, where `r = ν Z`. -/
theorem coadjointOrbitPlaneDiffeomorph_mk (hν : ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)) ≠ 0)
    (g : Nil) :
    coadjointOrbitPlaneDiffeomorph hν g =
      (ν (lieAlgebraEquiv.symm (heisenbergX ℝ)) + g.y * ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)),
        ν (lieAlgebraEquiv.symm (heisenbergY ℝ)) -
          g.x * ν (lieAlgebraEquiv.symm (heisenbergZ ℝ))) := by
  simp only [coadjointOrbitPlaneDiffeomorph_apply, Representation.orbitMap_mk,
    coadjointRepresentation_apply_lieAlgebraEquiv_symm_heisenbergX,
    coadjointRepresentation_apply_lieAlgebraEquiv_symm_heisenbergY]

/-- **The KKS form of a coadjoint orbit of Nil is `dp ∧ dq / r`.** For a functional `ν` with
`r = ν Z ≠ 0`, the diffeomorphism `[g] ↦ (μ X, μ Y)` of the coadjoint orbit `Nil ⧸ Nil_ν` onto the
plane pulls the constant form `r⁻¹ (dp ∧ dq)` back to the Kirillov–Kostant–Souriau form, where
`dp ∧ dq` is the standard symplectic form of `ℝ × ℝ`. -/
theorem mpullback_coadjointOrbitPlaneDiffeomorph_stdSymplecticForm
    (hν : ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)) ≠ 0) :
    SmoothForm.mpullback (coadjointOrbitPlaneDiffeomorph hν)
        (coadjointOrbitPlaneDiffeomorph hν).contMDiff
        ((ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)))⁻¹ •
          (stdSymplecticForm (V := ℝ)).constSmooth) =
      ν.coadjointOrbitForm := by
  -- Both forms are determined by their values on generators, which span the tangent spaces.
  refine SmoothBundleForm.ext_eval₂ fun x v w ↦ ?_
  obtain ⟨ξ, rfl⟩ := Subgroup.surjective_fundamentalVectorField
    (Lie.isClosed_stabilizer_coadjointRepresentation 𝓘(ℝ, R3) ν) x v
  obtain ⟨η, rfl⟩ := Subgroup.surjective_fundamentalVectorField
    (Lie.isClosed_stabilizer_coadjointRepresentation 𝓘(ℝ, R3) ν) x w
  have hX := (ν.contMDiff_orbitMap_coadjointRepresentation_apply
    (lieAlgebraEquiv.symm (heisenbergX ℝ))).mdifferentiableAt (x := x) (by simp)
  have hY := (ν.contMDiff_orbitMap_coadjointRepresentation_apply
    (lieAlgebraEquiv.symm (heisenbergY ℝ))).mdifferentiableAt (x := x) (by simp)
  -- In the coordinates `(p, q)` the generator of `(s, t, u)` is `(t r, -s r)`.
  rw [map_smul, SmoothBundleForm.eval₂_apply, Submodule.coe_smul, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply, ← SmoothBundleForm.eval₂_apply,
    SmoothForm.eval₂_mpullback, SymplecticForm.eval₂_constSmooth_mfderiv_eq,
    funext (coadjointOrbitPlaneDiffeomorph_apply hν), hX.mvfderiv_prodMk_apply hY,
    hX.mvfderiv_prodMk_apply hY,
    mvfderiv_orbitMap_coadjointRepresentation_apply_fundamentalVectorField,
    mvfderiv_orbitMap_coadjointRepresentation_apply_fundamentalVectorField,
    mvfderiv_orbitMap_coadjointRepresentation_apply_fundamentalVectorField,
    mvfderiv_orbitMap_coadjointRepresentation_apply_fundamentalVectorField,
    eval₂_coadjointOrbitForm_fundamentalVectorField, stdSymplecticForm_apply]
  simp [tangentSpaceCastModel_lieAlgebraEquiv_symm]
  field_simp
  ring

/-- **The KKS form of a coadjoint orbit of Nil in the coordinates `(p, q)`.** For a functional `ν`
with `r = ν Z ≠ 0`, the inverse of the diffeomorphism `[g] ↦ (μ X, μ Y)` pulls the
Kirillov–Kostant–Souriau form back to the constant form `r⁻¹ (dp ∧ dq)` on the plane. -/
theorem mpullback_coadjointOrbitPlaneDiffeomorph_symm_coadjointOrbitForm
    (hν : ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)) ≠ 0) :
    SmoothForm.mpullback (coadjointOrbitPlaneDiffeomorph hν).symm
        (coadjointOrbitPlaneDiffeomorph hν).symm.contMDiff ν.coadjointOrbitForm =
      (ν (lieAlgebraEquiv.symm (heisenbergZ ℝ)))⁻¹ •
        (stdSymplecticForm (V := ℝ)).constSmooth := by
  rw [← mpullback_coadjointOrbitPlaneDiffeomorph_stdSymplecticForm hν,
    SmoothForm.mpullback_mpullback_of_comp_eq (coadjointOrbitPlaneDiffeomorph hν).symm.contMDiff
      (coadjointOrbitPlaneDiffeomorph hν).contMDiff contMDiff_id contMDiff_id
      (funext (coadjointOrbitPlaneDiffeomorph hν).apply_symm_apply), SmoothForm.mpullback_id,
    LinearMap.id_apply, LinearMap.id_apply]

end TauCeti.Nil
