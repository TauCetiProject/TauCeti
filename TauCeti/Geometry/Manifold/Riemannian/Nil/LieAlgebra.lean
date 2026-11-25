/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Heisenberg.Orbit
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Nil.Basic
import TauCeti.Geometry.Lie.Adjoint.Infinitesimal
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The Lie algebra, adjoint orbits and coadjoint orbits of Nil

`Nil` is the real Heisenberg group, the analytic Lie group `ℝ³` with the product
`(a, b, c) * (x, y, z) = (a + x, b + y, c + z + a y)`. Its Lie algebra `𝔫` is the tangent space at
the identity, the model space `ℝ³`, with the bracket of left-invariant vector fields, and its
adjoint and coadjoint representations `Lie.adjointRepresentation` and
`Lie.coadjointRepresentation` are defined by differentiating conjugation. This file computes all
three in the global coordinates and identifies them with the algebraic Heisenberg group of
`TauCeti.Algebra.Lie.Heisenberg.Orbit`, whose orbits are computed there.

* **The adjoint action.** Conjugation by `p = (x, y, z)` is linear in the coordinates, so its
  differential is `Ad_p (a, b, c) = (a, b, c + x b - y a)`
  (`TauCeti.Nil.tangentSpaceCastModel_adjointRepresentation`).
* **The bracket.** Differentiating `p ↦ Ad_p v` at the identity gives
  `⁅(a, b, c), (a', b', c')⁆ = (0, 0, a b' - b a')` (`TauCeti.Nil.tangentSpaceCastModel_lie`): the
  only nonzero bracket of the coordinate basis is `⁅∂_x, ∂_y⁆ = ∂_z`.
* **The Heisenberg Lie algebra.** Hence `(a, b, c) ↦ a X + b Y + c Z` is a Lie algebra isomorphism
  from `𝔫` onto the strictly upper triangular `3 × 3` matrices `TauCeti.heisenberg ℝ`
  (`TauCeti.Nil.lieAlgebraLieEquiv`). Together with the group isomorphism `TauCeti.Nil.toHeisenberg`
  it intertwines the adjoint and coadjoint representations of `Nil` with those of
  `TauCeti.HeisenbergGroup ℝ` (`TauCeti.Nil.lieAlgebraLieEquiv_adjointRepresentation`,
  `TauCeti.Nil.coadjointRepresentation_dualMap_lieAlgebraLieEquiv`).

Transporting the algebraic orbit computations, with `r = μ(∂_z)` the value of a functional on the
central generator:

* the coadjoint action moves `(p, q, r) = (μ(∂_x), μ(∂_y), μ(∂_z))` to `(p + r y, q - r x, r)`;
* the coadjoint orbit of `μ` is the plane `{μ' | μ'(∂_z) = r}` when `r ≠ 0`, and the point `{μ}`
  when `r = 0` (`TauCeti.Nil.range_coadjointRepresentation_apply_of_ne_zero`,
  `TauCeti.Nil.range_coadjointRepresentation_apply_of_eq_zero`);
* the coadjoint stabilizer of `μ` is the centre `{(0, 0, z)}` when `r ≠ 0`, and all of `Nil` when
  `r = 0` (`TauCeti.Nil.mem_stabilizer_coadjointRepresentation_iff`,
  `TauCeti.Nil.stabilizer_coadjointRepresentation_of_eq_zero`);
* the adjoint orbit of `(a, b, c)` is the affine line `{(a, b, c') | c' ∈ ℝ}` when
  `(a, b) ≠ (0, 0)`, and a point otherwise
  (`TauCeti.Nil.range_adjointRepresentation_apply_of_ne_zero`,
  `TauCeti.Nil.range_adjointRepresentation_apply_of_eq_zero`).

So the nontrivial adjoint orbits are lines, of odd dimension, whereas the nontrivial coadjoint
orbits are planes, of even dimension, as the symplectic form on a coadjoint orbit requires.

Coordinates on `𝔫` are read through the canonical identification `tangentSpaceCastModel` of the
tangent space at the identity with the model space `ℝ³`, as for the left-invariant vector fields of
`TauCeti.Geometry.Manifold.Riemannian.Nil.Connection`.

## Main definitions

* `TauCeti.Nil.lieAlgebraLieEquiv`: the Lie algebra of `Nil` is the Heisenberg Lie algebra.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Chapter 2 (the Heisenberg group, its adjoint and coadjoint orbits).
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

namespace TauCeti.Nil

local notation "R3" => ℝ × ℝ × ℝ

local notation "J" => 𝓘(ℝ, ℝ × ℝ × ℝ)

local notation "𝔫" => GroupLieAlgebra J Nil

/-- The coordinates of an element of the Lie algebra of `Nil`. -/
local notation "𝔠" => tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) (1 : Nil)

/-- The linear map `(a, b, c) ↦ (a, b, c + x b - y a)` of conjugation by a point `p = (x, y, z)`
in the global coordinates. -/
private def conjLinear (p : Nil) : R3 →L[ℝ] R3 :=
  ContinuousLinearMap.id ℝ R3 +
    (p.x • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) -
      p.y • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).smulRight ((0, 0, 1) : R3)

private theorem conjLinear_apply (p : Nil) (a : R3) :
    conjLinear p a = (a.1, a.2.1, a.2.2 + p.x * a.2.1 - p.y * a.1) := by
  ext <;> simp [conjLinear]
  ring

/-- **The adjoint action of `Nil`** on its Lie algebra, in the global coordinates:
`Ad_p (a, b, c) = (a, b, c + x b - y a)` for `p = (x, y, z)`. -/
private theorem tangentSpaceCastModel_adjointRepresentation_eq_conjLinear (p : Nil) (u : 𝔫) :
    𝔠 (Lie.adjointRepresentation ℝ J Nil p u) = conjLinear p (𝔠 u) := by
  have hconj : toProd ∘ (fun q : Nil ↦ p * q * p⁻¹) ∘ toProd.symm = conjLinear p := by
    funext r
    rw [conjLinear_apply]
    ext <;> simp
    ring
  have h := fderiv_toProd_conj_apply (fun q : Nil ↦ p * q * p⁻¹) 1 u
  rw [hconj, (conjLinear p).fderiv] at h
  have hc : ⇑(Lie.conjDiffeomorph (I := J) (n := 1) p) = fun q : Nil ↦ p * q * p⁻¹ :=
    funext (Lie.conjDiffeomorph_apply p)
  rw [Lie.adjointRepresentation_apply, Lie.adjointContinuousLinearMap_apply, hc]
  -- `h` reads the differential at `p * 1 * p⁻¹` rather than `1`; both tangent-space casts are the
  -- identity of the model space `ℝ³`.
  exact h.symm

/-- The linear map `(x, y, z) ↦ (0, 0, x b - y a)`, the linear part of the affine map
`p ↦ Ad_p v` in the global coordinates for `v = (a, b, c)`. -/
private def bracketLinear (b : R3) : R3 →L[ℝ] R3 :=
  (b.2.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) -
    b.1 • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).smulRight
      ((0, 0, 1) : R3)

/-- The bracket `⁅u, v⁆` is the derivative of `p ↦ Ad_p v` at the identity in the direction
`u`. -/
private theorem tangentSpaceCastModel_lie_eq_bracketLinear (u v : 𝔫) :
    𝔠 ⁅u, v⁆ = bracketLinear (𝔠 v) (𝔠 u) := by
  set b := 𝔠 v
  -- The tangent space at `1` is the model space, so `h` is the same statement as
  -- `Lie.mvfderiv_tangentAd_apply_one` read through the identity `tangentSpaceCastModel`.
  have h : mvfderiv J (fun g : Nil ↦ 𝔠 (Lie.tangentAd g v)) 1 u = 𝔠 ⁅u, v⁆ := by
    have h := Lie.mvfderiv_tangentAd_apply_one (I := J) (G := Nil) u v
    rw [LieAlgebra.ad_apply] at h
    exact h
  have hF : (fun g : Nil ↦ 𝔠 (Lie.tangentAd g v)) =
      (fun r ↦ b + bracketLinear b r) ∘ toProd := by
    funext g
    rw [Lie.tangentAd_apply, ← Lie.adjointRepresentation_apply,
      tangentSpaceCastModel_adjointRepresentation_eq_conjLinear, conjLinear_apply]
    ext <;> simp [bracketLinear, b]
    ring
  rw [← h, hF, mvfderiv_comp_apply_of_differentiableAt
      ((bracketLinear b).differentiableAt.const_add b)
      (contMDiff_toProd.mdifferentiableAt one_ne_zero),
    fderiv_const_add, (bracketLinear b).fderiv, mvfderiv_apply_eq_mfderiv_apply,
    mfderiv_toProd_apply]

/-! ### The Lie algebra of `Nil` is the Heisenberg Lie algebra -/

variable (u v : 𝔫)

/-- **The Lie algebra of `Nil` is the Heisenberg Lie algebra.** The tangent vector at the identity
with coordinates `(a, b, c)` corresponds to `a X + b Y + c Z`, where `X = E₀₁`, `Y = E₁₂` and
`Z = E₀₂` are the matrix units of the strictly upper triangular `3 × 3` matrices. -/
def lieAlgebraLieEquiv : 𝔫 ≃ₗ⁅ℝ⁆ heisenberg ℝ where
  toFun u := (𝔠 u).1 • heisenbergX ℝ + (𝔠 u).2.1 • heisenbergY ℝ + (𝔠 u).2.2 • heisenbergZ ℝ
  map_add' u v := by
    simp only [map_add, Prod.fst_add, Prod.snd_add, add_smul]
    abel
  map_smul' c u := by
    simp only [map_smul, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul, smul_add,
      RingHom.id_apply]
  map_lie' {u v} := by
    rw [tangentSpaceCastModel_lie_eq_bracketLinear, lie_eq_smul_heisenbergZ]
    simp [bracketLinear]
    ring_nf
  invFun A := (𝔠).symm
    ((A : Matrix (Fin 3) (Fin 3) ℝ) 0 1, (A : Matrix (Fin 3) (Fin 3) ℝ) 1 2,
      (A : Matrix (Fin 3) (Fin 3) ℝ) 0 2)
  left_inv u := by
    apply (𝔠).injective
    simp
  right_inv A := by
    simpa using (eq_smul_heisenbergX_add_smul_heisenbergY_add_smul_heisenbergZ A).symm

/-- The central generator `∂_z` of the Lie algebra of `Nil`. -/
local notation "ζ" => lieAlgebraLieEquiv.symm (heisenbergZ ℝ)

/-- The element `(a, b, c)` of the Lie algebra of `Nil` is `a X + b Y + c Z`. -/
theorem lieAlgebraLieEquiv_apply :
    lieAlgebraLieEquiv u =
      (𝔠 u).1 • heisenbergX ℝ + (𝔠 u).2.1 • heisenbergY ℝ + (𝔠 u).2.2 • heisenbergZ ℝ :=
  (rfl)

/-- The entry `(0, 1)` of the matrix of `(a, b, c)` is `a`. -/
@[simp]
theorem lieAlgebraLieEquiv_apply_zero_one :
    (lieAlgebraLieEquiv u : Matrix (Fin 3) (Fin 3) ℝ) 0 1 = (𝔠 u).1 := by
  simp [lieAlgebraLieEquiv_apply]

/-- The entry `(1, 2)` of the matrix of `(a, b, c)` is `b`. -/
@[simp]
theorem lieAlgebraLieEquiv_apply_one_two :
    (lieAlgebraLieEquiv u : Matrix (Fin 3) (Fin 3) ℝ) 1 2 = (𝔠 u).2.1 := by
  simp [lieAlgebraLieEquiv_apply]

/-- The entry `(0, 2)` of the matrix of `(a, b, c)` is `c`. -/
@[simp]
theorem lieAlgebraLieEquiv_apply_zero_two :
    (lieAlgebraLieEquiv u : Matrix (Fin 3) (Fin 3) ℝ) 0 2 = (𝔠 u).2.2 := by
  simp [lieAlgebraLieEquiv_apply]

/-- The strictly upper triangular matrix `A` corresponds to the element of the Lie algebra of `Nil`
with coordinates `(A₀₁, A₁₂, A₀₂)`. -/
@[simp]
theorem tangentSpaceCastModel_lieAlgebraLieEquiv_symm_apply (A : heisenberg ℝ) :
    𝔠 (lieAlgebraLieEquiv.symm A) =
      ((A : Matrix (Fin 3) (Fin 3) ℝ) 0 1, (A : Matrix (Fin 3) (Fin 3) ℝ) 1 2,
        (A : Matrix (Fin 3) (Fin 3) ℝ) 0 2) := by
  simp [lieAlgebraLieEquiv]

/-- **The Lie bracket of `Nil`**: `⁅(a, b, c), (a', b', c')⁆ = (0, 0, a b' - b a')`. In particular
`⁅∂_x, ∂_y⁆ = ∂_z` at the identity, and `∂_z` spans the centre. -/
@[simp]
theorem tangentSpaceCastModel_lie :
    𝔠 ⁅u, v⁆ = (0, 0, (𝔠 u).1 * (𝔠 v).2.1 - (𝔠 u).2.1 * (𝔠 v).1) := by
  rw [tangentSpaceCastModel_lie_eq_bracketLinear]
  ext <;> simp [bracketLinear]
  ring

/-- **The adjoint action of `Nil`** in the coordinates of its Lie algebra:
`Ad_p (a, b, c) = (a, b, c + x b - y a)` for `p = (x, y, z)`. -/
theorem tangentSpaceCastModel_adjointRepresentation (p : Nil) :
    𝔠 (Lie.adjointRepresentation ℝ J Nil p u) =
      ((𝔠 u).1, (𝔠 u).2.1, (𝔠 u).2.2 + p.x * (𝔠 u).2.1 - p.y * (𝔠 u).1) := by
  rw [tangentSpaceCastModel_adjointRepresentation_eq_conjLinear, conjLinear_apply]

/-- **The adjoint representation of `Nil` is that of the Heisenberg group**: along
`lieAlgebraLieEquiv` and `toHeisenberg`, the differential of conjugation is conjugation of strictly
upper triangular matrices by unipotent ones. -/
theorem lieAlgebraLieEquiv_adjointRepresentation (p : Nil) :
    lieAlgebraLieEquiv (Lie.adjointRepresentation ℝ J Nil p u) =
      HeisenbergGroup.adjointRepresentation ℝ (toHeisenberg p) (lieAlgebraLieEquiv u) := by
  rw [lieAlgebraLieEquiv_apply, tangentSpaceCastModel_adjointRepresentation,
    HeisenbergGroup.adjointRepresentation_apply, lie_eq_smul_heisenbergZ]
  simp only [HeisenbergGroup.nilpotentPart_apply_zero_one,
    HeisenbergGroup.nilpotentPart_apply_one_two,
    x_toHeisenberg, y_toHeisenberg, lieAlgebraLieEquiv_apply_zero_one,
    lieAlgebraLieEquiv_apply_one_two]
  rw [lieAlgebraLieEquiv_apply u]
  module

/-- **The coadjoint representation of `Nil` is that of the Heisenberg group**: along the dual of
`lieAlgebraLieEquiv` and `toHeisenberg`, the coadjoint actions agree. -/
theorem coadjointRepresentation_dualMap_lieAlgebraLieEquiv (p : Nil)
    (ν : Dual ℝ (heisenberg ℝ)) :
    Lie.coadjointRepresentation ℝ J Nil p (lieAlgebraLieEquiv.toLinearEquiv.dualMap ν) =
      lieAlgebraLieEquiv.toLinearEquiv.dualMap
        (HeisenbergGroup.coadjointRepresentation ℝ (toHeisenberg p) ν) := by
  ext u
  rw [Lie.coadjointRepresentation_apply, ← Lie.adjointRepresentation_apply,
    LinearEquiv.dualMap_apply, LinearEquiv.dualMap_apply,
    HeisenbergGroup.coadjointRepresentation_apply_apply, LieEquiv.coe_toLinearEquiv,
    lieAlgebraLieEquiv_adjointRepresentation, map_inv]

/-- The coadjoint action of `Nil` on a functional `μ`, through the Heisenberg group. -/
private theorem coadjointRepresentation_eq (p : Nil) (μ : Dual ℝ 𝔫) :
    Lie.coadjointRepresentation ℝ J Nil p μ =
      lieAlgebraLieEquiv.toLinearEquiv.dualMap (HeisenbergGroup.coadjointRepresentation ℝ
        (toHeisenberg p) (lieAlgebraLieEquiv.symm.toLinearEquiv.dualMap μ)) := by
  rw [← coadjointRepresentation_dualMap_lieAlgebraLieEquiv]
  congr 1
  ext u
  simp

/-- The coadjoint orbit of `μ` under `Nil` is the image of the corresponding Heisenberg orbit. -/
private theorem range_coadjointRepresentation_apply_eq_image (μ : Dual ℝ 𝔫) :
    Set.range (fun p : Nil ↦ Lie.coadjointRepresentation ℝ J Nil p μ) =
      lieAlgebraLieEquiv.toLinearEquiv.dualMap '' Set.range (fun a ↦
        HeisenbergGroup.coadjointRepresentation ℝ a
          (lieAlgebraLieEquiv.symm.toLinearEquiv.dualMap μ)) := by
  simp_rw [coadjointRepresentation_eq, ← Set.range_comp]
  exact toHeisenberg.surjective.range_comp (lieAlgebraLieEquiv.toLinearEquiv.dualMap ∘ fun a ↦
    HeisenbergGroup.coadjointRepresentation ℝ a (lieAlgebraLieEquiv.symm.toLinearEquiv.dualMap μ))

/-- **The bracket of `Nil` is a multiple of its central generator** `∂_z`, with coefficient the
`2 × 2` determinant `a b' - b a'` of the horizontal coordinates. -/
theorem lie_eq_smul_lieAlgebraLieEquiv_symm_heisenbergZ :
    ⁅u, v⁆ = ((𝔠 u).1 * (𝔠 v).2.1 - (𝔠 u).2.1 * (𝔠 v).1) • ζ := by
  rw [← lieAlgebraLieEquiv.symm_apply_apply ⁅u, v⁆, LieEquiv.map_lie, lie_eq_smul_heisenbergZ,
    map_smul]
  simp only [lieAlgebraLieEquiv_apply_zero_one, lieAlgebraLieEquiv_apply_one_two]
  ring_nf

/-- The first coordinate of the coadjoint action of `Nil`: `p ↦ p + r y`. -/
theorem coadjointRepresentation_apply_lieAlgebraLieEquiv_symm_heisenbergX (p : Nil)
    (μ : Dual ℝ 𝔫) :
    Lie.coadjointRepresentation ℝ J Nil p μ (lieAlgebraLieEquiv.symm (heisenbergX ℝ)) =
      μ (lieAlgebraLieEquiv.symm (heisenbergX ℝ)) + p.y * μ ζ := by
  simp [coadjointRepresentation_eq]

/-- The second coordinate of the coadjoint action of `Nil`: `q ↦ q - r x`. -/
theorem coadjointRepresentation_apply_lieAlgebraLieEquiv_symm_heisenbergY (p : Nil)
    (μ : Dual ℝ 𝔫) :
    Lie.coadjointRepresentation ℝ J Nil p μ (lieAlgebraLieEquiv.symm (heisenbergY ℝ)) =
      μ (lieAlgebraLieEquiv.symm (heisenbergY ℝ)) - p.x * μ ζ := by
  simp [coadjointRepresentation_eq]

/-- The third coordinate `r = μ(∂_z)` is invariant under the coadjoint action of `Nil`. -/
theorem coadjointRepresentation_apply_lieAlgebraLieEquiv_symm_heisenbergZ (p : Nil)
    (μ : Dual ℝ 𝔫) :
    Lie.coadjointRepresentation ℝ J Nil p μ ζ = μ ζ := by
  simp [coadjointRepresentation_eq]

/-- **The coadjoint orbits of `Nil` through functionals nonzero on the centre are planes.** If
`r = μ(∂_z) ≠ 0`, the coadjoint orbit of `μ` is the plane `{μ' | μ'(∂_z) = r}`. -/
theorem range_coadjointRepresentation_apply_of_ne_zero {μ : Dual ℝ 𝔫}
    (hμ : μ ζ ≠ 0) :
    Set.range (fun p : Nil ↦ Lie.coadjointRepresentation ℝ J Nil p μ) = {μ' | μ' ζ = μ ζ} := by
  rw [range_coadjointRepresentation_apply_eq_image,
    HeisenbergGroup.range_coadjointRepresentation_apply_of_isUnit (by simpa using hμ.isUnit)]
  ext μ'
  refine ⟨?_, fun h ↦ ⟨lieAlgebraLieEquiv.symm.toLinearEquiv.dualMap μ', by simpa using h, ?_⟩⟩
  · rintro ⟨ν, hν, rfl⟩
    simpa using hν
  · ext u
    simp

/-- **The coadjoint orbit of `Nil` through a functional vanishing on the centre is a point.** -/
theorem range_coadjointRepresentation_apply_of_eq_zero {μ : Dual ℝ 𝔫} (hμ : μ ζ = 0) :
    Set.range (fun p : Nil ↦ Lie.coadjointRepresentation ℝ J Nil p μ) = {μ} := by
  rw [range_coadjointRepresentation_apply_eq_image,
    HeisenbergGroup.range_coadjointRepresentation_apply_of_eq_zero (by simpa using hμ),
    Set.image_singleton]
  congr 1
  ext u
  simp

/-- **The coadjoint stabilizer of a functional nonzero on the centre is the centre** `{(0, 0, z)}`
of `Nil`. -/
theorem mem_stabilizer_coadjointRepresentation_iff {μ : Dual ℝ 𝔫} (hμ : μ ζ ≠ 0) {p : Nil} :
    p ∈ (Lie.coadjointRepresentation ℝ J Nil).stabilizer μ ↔ p.x = 0 ∧ p.y = 0 := by
  have hμ' : μ = lieAlgebraLieEquiv.toLinearEquiv.dualMap
      (lieAlgebraLieEquiv.symm.toLinearEquiv.dualMap μ) := by
    ext u
    simp
  rw [Representation.mem_stabilizer, coadjointRepresentation_eq]
  nth_rw 2 [hμ']
  rw [(LinearEquiv.injective _).eq_iff, ← Representation.mem_stabilizer,
    HeisenbergGroup.stabilizer_coadjointRepresentation_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero (by simpa using hμ)),
    HeisenbergGroup.mem_zAxis_iff, x_toHeisenberg, y_toHeisenberg]

/-- **A functional vanishing on the centre is fixed by the whole coadjoint action of `Nil`.** -/
theorem stabilizer_coadjointRepresentation_of_eq_zero {μ : Dual ℝ 𝔫} (hμ : μ ζ = 0) :
    (Lie.coadjointRepresentation ℝ J Nil).stabilizer μ = ⊤ := by
  refine eq_top_iff.mpr fun p _ ↦ Representation.mem_stabilizer.mpr ?_
  have h := range_coadjointRepresentation_apply_of_eq_zero hμ
  exact Set.mem_singleton_iff.mp (h ▸ Set.mem_range_self p)

/-- The adjoint orbit of `u` under `Nil` is the image of the corresponding Heisenberg orbit. -/
private theorem range_adjointRepresentation_apply_eq_image :
    Set.range (fun p : Nil ↦ Lie.adjointRepresentation ℝ J Nil p u) =
      lieAlgebraLieEquiv.symm '' Set.range (fun a ↦
        HeisenbergGroup.adjointRepresentation ℝ a (lieAlgebraLieEquiv u)) := by
  have h : (fun p : Nil ↦ Lie.adjointRepresentation ℝ J Nil p u) =
      (lieAlgebraLieEquiv.symm ∘ fun a ↦
        HeisenbergGroup.adjointRepresentation ℝ a (lieAlgebraLieEquiv u)) ∘ toHeisenberg := by
    funext p
    rw [Function.comp_apply, Function.comp_apply, ← lieAlgebraLieEquiv_adjointRepresentation,
      LieEquiv.symm_apply_apply]
  rw [h, toHeisenberg.surjective.range_comp, Set.range_comp]

/-- **The adjoint orbits of `Nil` through noncentral elements are lines**: if `(a, b) ≠ (0, 0)`,
the adjoint orbit of `(a, b, c)` is the line `{(a, b, c') | c' ∈ ℝ}`. -/
theorem range_adjointRepresentation_apply_of_ne_zero
    (hu : (𝔠 u).1 ≠ 0 ∨ (𝔠 u).2.1 ≠ 0) :
    Set.range (fun p : Nil ↦ Lie.adjointRepresentation ℝ J Nil p u) =
      {v | (𝔠 v).1 = (𝔠 u).1 ∧ (𝔠 v).2.1 = (𝔠 u).2.1} := by
  rw [range_adjointRepresentation_apply_eq_image,
    HeisenbergGroup.range_adjointRepresentation_apply_of_ne_zero (by simpa using hu)]
  ext v
  refine ⟨?_, fun h ↦ ⟨lieAlgebraLieEquiv v, by simpa using h, by simp⟩⟩
  rintro ⟨A, hA, rfl⟩
  simpa using hA

/-- **The adjoint orbit of a central element of the Lie algebra of `Nil` is a point.** -/
theorem range_adjointRepresentation_apply_of_eq_zero (h₁ : (𝔠 u).1 = 0) (h₂ : (𝔠 u).2.1 = 0) :
    Set.range (fun p : Nil ↦ Lie.adjointRepresentation ℝ J Nil p u) = {u} := by
  rw [range_adjointRepresentation_apply_eq_image,
    HeisenbergGroup.range_adjointRepresentation_apply_of_eq_zero (by simpa using h₁)
      (by simpa using h₂), Set.image_singleton, LieEquiv.symm_apply_apply]

end TauCeti.Nil
