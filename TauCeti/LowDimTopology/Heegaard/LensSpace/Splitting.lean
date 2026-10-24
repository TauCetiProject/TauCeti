/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.LensSpace.FundamentalGroup
public import TauCeti.Geometry.Manifold.Instances.LensSpace
public import TauCeti.LowDimTopology.Heegaard.Clifford
public import TauCeti.LowDimTopology.Heegaard.FundamentalGroup
public import TauCeti.Topology.Homeomorph.CompactQuotient
import Mathlib.FieldTheory.IsAlgClosed.Basic
import TauCeti.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The genus-one Heegaard splitting of a lens space

The three-dimensional lens space `L(m; ℓ₀, ℓ₁)` is the orbit space of the unit sphere
`S³ = {(z, w) | ‖z‖ ^ 2 + ‖w‖ ^ 2 = 1}` of `ℂ²` under the rotations
`(z, w) ↦ (ζ ^ ℓ₀ z, ζ ^ ℓ₁ w)`, `ζ ^ m = 1`. The rotations preserve the two solid tori
`‖z‖ ≤ ‖w‖` and `‖w‖ ≤ ‖z‖` of the genus-one Heegaard splitting of `S³`
(`TauCeti.cliffordHeegaardSplitting`), so their images are two pieces covering the lens space and
meeting along the image of the Clifford torus. Each image is again a solid torus. On
`‖z‖ ≤ ‖w‖` the rotation acts on the coordinates `(u, v) = (z / ‖w‖, w / ‖w‖) ∈ D² × S¹`
(`TauCeti.sphereProdFstLeHomeomorph`) by
`(u, v) ↦ (ζ ^ ℓ₀ u, ζ ^ ℓ₁ v)`, freely on the core circle; choosing `c` with `c ℓ₁ = ℓ₀` modulo
`m`, the map `(u, v) ↦ (u conj(v) ^ c, v ^ m)` is invariant, and its fibres are exactly the orbits,
so it identifies the quotient with `D² × S¹`. This gives the genus-one Heegaard splitting
`TauCeti.LensSpace.heegaardSplitting` of `L(m; ℓ₀, ℓ₁)`.

The splitting is obtained by descending the splitting of the sphere along the projection, an open
quotient map for which both solid tori are saturated
(`TauCeti.HeegaardSplitting.ofIsOpenQuotientMap`).

Since the fundamental group `ℤ/m` of a lens space with `m ≠ 1` is nontrivial, and its rank is at
most the Heegaard genus (`TauCeti.rank_fundamentalGroup_le_heegaardGenus`), such a lens space has
Heegaard genus exactly one, and its Heegaard genus equals the rank of its fundamental group, as in
Waldhausen's rank-versus-genus conjecture (`TauCeti.RankGenusConjecture`).

## Main definitions

* `TauCeti.LensSpace.heegaardSplitting`: the genus-one Heegaard splitting of `L(m; ℓ₀, ℓ₁)` into
  the images of the solid tori `‖z‖ ≤ ‖w‖` and `‖w‖ ≤ ‖z‖`.

## Main results

* `TauCeti.LensSpace.rank_fundamentalGroup_eq_one`: for `m ≠ 1`, the fundamental group of
  `L(m; ℓ₀, ℓ₁)` has rank one.
* `TauCeti.LensSpace.heegaardGenus_eq_one`: a lens space `L(m; ℓ₀, ℓ₁)` with `m ≠ 1` has Heegaard
  genus one.
* `TauCeti.LensSpace.heegaardGenus_eq_rank`: its Heegaard genus is the rank of its fundamental
  group.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 9 (lens spaces as unions of two
  solid tori).
* M. Scharlemann, *Heegaard splittings of compact 3-manifolds*, in *Handbook of Geometric
  Topology*, North-Holland (2002), Section 2.
-/

public section

noncomputable section

open Metric Set Module Function

namespace TauCeti

namespace LensSpace

variable (m : ℕ) [NeZero m] (ℓ : Fin 2 → (ZMod m)ˣ)

/-- A complex number `z` of norm one satisfies `z ^ n * conj(z) ^ n = 1`. -/
private theorem pow_mul_conj_pow_eq_one {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) :
    z ^ n * starRingEnd ℂ z ^ n = 1 := by
  rw [← mul_pow, Complex.mul_conj', hz]
  norm_num

/-- If `‖ω‖ = 1` and `v ≠ 0`, then `u conj(ω v) ^ c = u' conj(v) ^ c` exactly when
`u = ω ^ c u'`. -/
private theorem mul_conj_pow_eq_iff {u u' v ω : ℂ} (hv : v ≠ 0) (hω : ‖ω‖ = 1) (c : ℕ) :
    u * starRingEnd ℂ (ω * v) ^ c = u' * starRingEnd ℂ v ^ c ↔ u = ω ^ c * u' := by
  have e := pow_mul_conj_pow_eq_one hω c
  rw [map_mul, mul_pow, ← mul_assoc, mul_left_inj' (pow_ne_zero _ ((map_ne_zero _).2 hv))]
  constructor
  · intro h
    linear_combination ω ^ c * h - u * e
  · rintro rfl
    linear_combination u' * e

/-- Every `m`-th root of unity in `ℂ` is a rotation `ZMod.toCircle b`. -/
private theorem exists_toCircle_eq_of_pow_eq_one {ω : ℂ} (hω : ω ^ m = 1) :
    ∃ b : ZMod m, (ZMod.toCircle b : ℂ) = ω := by
  have h0 : ω ≠ 0 := by
    rintro rfl
    simp [NeZero.ne m] at hω
  obtain ⟨b, hb⟩ := surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar m
    ⟨Units.mk0 ω h0, (mem_rootsOfUnity' m _).2 hω⟩
  exact ⟨b, by simpa using congrArg (fun u : rootsOfUnity m ℂ ↦ ((u : ℂˣ) : ℂ)) hb⟩

/-- The exponent `c = ℓᵢ ℓⱼ⁻¹` of the invariant `u conj(v) ^ c` on the solid torus
`‖x i‖ ≤ ‖x j‖`. -/
private def twist (i j : Fin 2) : ℕ := ((ℓ i * (ℓ j)⁻¹ : (ZMod m)ˣ) : ZMod m).val

/-- The twist exponent satisfies `c ℓⱼ = ℓᵢ` modulo `m`, so the `c`-th power of the rotation of the
core coordinate is the rotation of the disc coordinate. -/
private theorem toCircle_pow_twist (i j : Fin 2) (t : ZMod m) :
    ZMod.toCircle ((ℓ j : ZMod m) * t) ^ twist m ℓ i j = ZMod.toCircle ((ℓ i : ZMod m) * t) := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, twist, ZMod.natCast_zmod_val, ← mul_assoc,
    Units.val_mul, Units.inv_mul_cancel_right]

/-! ### The quotient of the model solid torus -/

/-- The quotient map `(u, v) ↦ (u conj(v) ^ c, v ^ m)` of `D² × S¹` by the rotations
`(u, v) ↦ (ζ ^ ℓᵢ u, ζ ^ ℓⱼ v)`, `ζ ^ m = 1`, where `c` is the twist exponent. -/
private def modelQuotient (i j : Fin 2) (p : closedBall (0 : ℂ) 1 × sphere (0 : ℂ) 1) :
    SolidTorus :=
  (⟨p.1 * starRingEnd ℂ p.2 ^ twist m ℓ i j, by
      rw [mem_closedBall_zero_iff, norm_mul, norm_pow, Complex.norm_conj,
        norm_eq_of_mem_sphere p.2, one_pow, mul_one]
      exact mem_closedBall_zero_iff.1 p.1.2⟩,
    ⟨p.2 ^ m, mem_sphere_zero_iff_norm.2 (by rw [norm_pow, norm_eq_of_mem_sphere p.2, one_pow])⟩)

omit [NeZero m] in
private theorem continuous_modelQuotient (i j : Fin 2) : Continuous (modelQuotient m ℓ i j) := by
  refine .prodMk (.subtype_mk ?_ _) (.subtype_mk ?_ _)
  · exact (continuous_subtype_val.comp continuous_fst).mul
      ((Complex.continuous_conj.comp (continuous_subtype_val.comp continuous_snd)).pow _)
  · exact (continuous_subtype_val.comp continuous_snd).pow _

omit [NeZero m] in
private theorem coe_modelQuotient_fst (i j : Fin 2) (p : closedBall (0 : ℂ) 1 × sphere (0 : ℂ) 1) :
    ((modelQuotient m ℓ i j p).1 : ℂ) = p.1 * starRingEnd ℂ p.2 ^ twist m ℓ i j :=
  (rfl)

omit [NeZero m] in
private theorem coe_modelQuotient_snd (i j : Fin 2) (p : closedBall (0 : ℂ) 1 × sphere (0 : ℂ) 1) :
    ((modelQuotient m ℓ i j p).2 : ℂ) = (p.2 : ℂ) ^ m :=
  (rfl)

/-- The quotient map of `D² × S¹` is surjective: `(u, v)` is the image of `(u w ^ c, w)` for any
`m`-th root `w` of `v`. -/
private theorem modelQuotient_surjective (i j : Fin 2) : Surjective (modelQuotient m ℓ i j) := by
  rintro ⟨⟨u, hu⟩, v⟩
  rw [mem_closedBall_zero_iff] at hu
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (v : ℂ) (Nat.pos_of_ne_zero (NeZero.ne m))
  have hw1 : ‖w‖ = 1 := by
    rw [← pow_left_inj₀ (norm_nonneg w) zero_le_one (NeZero.ne m), ← norm_pow, hw,
      Circle.norm_coe, one_pow]
  refine ⟨(⟨u * w ^ twist m ℓ i j, by
      rwa [mem_closedBall_zero_iff, norm_mul, norm_pow, hw1, one_pow, mul_one]⟩,
    ⟨w, mem_sphere_zero_iff_norm.2 hw1⟩), Prod.ext (Subtype.ext ?_) (Circle.ext ?_)⟩
  · rw [coe_modelQuotient_fst, mul_assoc, pow_mul_conj_pow_eq_one hw1, mul_one]
  · rw [coe_modelQuotient_snd, hw]

/-- The fibres of the quotient map of `D² × S¹` are the orbits of the rotations
`(u, v) ↦ (ζ ^ ℓᵢ u, ζ ^ ℓⱼ v)`. -/
private theorem modelQuotient_eq_iff (i j : Fin 2) (p q : closedBall (0 : ℂ) 1 × sphere (0 : ℂ) 1) :
    modelQuotient m ℓ i j p = modelQuotient m ℓ i j q ↔
      ∃ b : ZMod m, (p.1 : ℂ) = ZMod.toCircle ((ℓ i : ZMod m) * b) * q.1 ∧
        (p.2 : ℂ) = ZMod.toCircle ((ℓ j : ZMod m) * b) * q.2 := by
  have hq : (q.2 : ℂ) ≠ 0 := ne_zero_of_mem_unit_sphere q.2
  constructor
  · intro h
    have h1 := congrArg (fun r : SolidTorus ↦ ((r.1 : closedBall (0 : ℂ) 1) : ℂ)) h
    have h2 := congrArg (fun r : SolidTorus ↦ ((r.2 : Circle) : ℂ)) h
    simp only [coe_modelQuotient_fst, coe_modelQuotient_snd] at h1 h2
    -- The ratio of the core coordinates is an `m`-th root of unity, hence a rotation.
    obtain ⟨b, hb⟩ := exists_toCircle_eq_of_pow_eq_one m (ω := p.2 / q.2)
      (by rw [div_pow, h2, div_self (pow_ne_zero _ hq)])
    have hω : ‖(p.2 / q.2 : ℂ)‖ = 1 := by
      rw [norm_div, norm_eq_of_mem_sphere p.2, norm_eq_of_mem_sphere q.2, div_one]
    have hp : (p.2 : ℂ) = p.2 / q.2 * q.2 := (div_mul_cancel₀ _ hq).symm
    refine ⟨((ℓ j)⁻¹ : (ZMod m)ˣ) * b, ?_, ?_⟩
    · rw [← toCircle_pow_twist, Units.mul_inv_cancel_left, Circle.coe_pow, hb]
      rw [hp] at h1
      exact (mul_conj_pow_eq_iff hq hω _).1 h1
    · rw [Units.mul_inv_cancel_left, hb, ← hp]
  · rintro ⟨b, h1, h2⟩
    refine Prod.ext (Subtype.ext ?_) (Circle.ext ?_)
    · rw [coe_modelQuotient_fst, coe_modelQuotient_fst, h2,
        mul_conj_pow_eq_iff hq (Circle.norm_coe _), h1, ← Circle.coe_pow, toCircle_pow_twist]
    · rw [coe_modelQuotient_snd, coe_modelQuotient_snd, h2, mul_pow, ← Circle.coe_pow,
        ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
        AddChar.map_zero_eq_one, Circle.coe_one, one_mul]

/-! ### The two solid tori of a lens space -/

/-- The solid torus `‖x i‖ ≤ ‖x j‖` of the unit sphere of `ℂ²`. -/
private def piece (i j : Fin 2) : Set (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :=
  {x | ‖(x : EuclideanSpace ℂ (Fin 2)) i‖ ≤ ‖(x : EuclideanSpace ℂ (Fin 2)) j‖}

/-- The solid tori are saturated for the projection to the lens space. -/
private theorem preimage_image_piece (i j : Fin 2) :
    mk m ℓ ⁻¹' (mk m ℓ '' piece i j) = piece i j := by
  refine (subset_preimage_image _ _).antisymm' ?_
  rintro x ⟨y, hy, hxy⟩
  obtain ⟨a, ha⟩ := (mk_eq_mk_iff m ℓ y x).1 hxy
  simpa [piece, ← ha] using hy

/-- The solid torus `‖x i‖ ≤ ‖x j‖` is compact. -/
private theorem isCompact_piece (i j : Fin 2) : IsCompact (piece i j) :=
  (isClosed_le (by fun_prop) (by fun_prop)).isCompact

/-- The coordinates `x ↦ (x i, x j)` of `ℂ²`, for `j ≠ i`, as a linear isometry equivalence onto
`WithLp 2 (ℂ × ℂ)`. -/
private def coordEquiv (i : Fin 2) : EuclideanSpace ℂ (Fin 2) ≃ₗᵢ[ℂ] WithLp 2 (ℂ × ℂ) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.swap 0 i)).trans
    (EuclideanSpace.finTwoEquivProd ℂ)

private theorem coordEquiv_apply_fst (i : Fin 2) (x : EuclideanSpace ℂ (Fin 2)) :
    (coordEquiv i x).fst = x i := by
  simp [coordEquiv, Equiv.piCongrLeft']

private theorem coordEquiv_apply_snd {i j : Fin 2} (hij : i ≠ j) (x : EuclideanSpace ℂ (Fin 2)) :
    (coordEquiv i x).snd = x j := by
  fin_cases i <;> fin_cases j <;> simp_all [coordEquiv, Equiv.piCongrLeft']

/-- The solid torus `‖x i‖ ≤ ‖x j‖` is a copy of `D² × S¹` through the disc and core coordinates
`x ↦ (x i / ‖x j‖, x j / ‖x j‖)`: in the coordinates `(z, w) = (x i, x j)` it is the solid torus
`‖z‖ ≤ ‖w‖` of `TauCeti.sphereProdFstLeHomeomorph`. -/
private def pieceHomeomorph {i j : Fin 2} (hij : i ≠ j) :
    piece i j ≃ₜ closedBall (0 : ℂ) 1 × sphere (0 : ℂ) 1 :=
  ((coordEquiv i).unitSphereIsometryEquiv.toHomeomorph.sets
      (t := {x : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 |
        ‖(x : WithLp 2 (ℂ × ℂ)).fst‖ ≤ ‖(x : WithLp 2 (ℂ × ℂ)).snd‖}) (by
        ext x
        simp [piece, coordEquiv_apply_fst, coordEquiv_apply_snd hij])).trans
    (sphereProdFstLeHomeomorph ℂ ℂ)

private theorem coe_pieceHomeomorph_fst {i j : Fin 2} (hij : i ≠ j) (x : piece i j) :
    ((pieceHomeomorph hij x).1 : ℂ) =
      ‖(x : EuclideanSpace ℂ (Fin 2)) j‖⁻¹ • (x : EuclideanSpace ℂ (Fin 2)) i := by
  simp [pieceHomeomorph, coordEquiv_apply_fst, coordEquiv_apply_snd hij]

private theorem coe_pieceHomeomorph_snd {i j : Fin 2} (hij : i ≠ j) (x : piece i j) :
    ((pieceHomeomorph hij x).2 : ℂ) =
      ‖(x : EuclideanSpace ℂ (Fin 2)) j‖⁻¹ • (x : EuclideanSpace ℂ (Fin 2)) j := by
  simp [pieceHomeomorph, coordEquiv_apply_snd hij]

/-- The rotation by a residue `a` of a point of the solid torus `‖x i‖ ≤ ‖x j‖`. -/
private def rotatePiece {i j : Fin 2} (a : Multiplicative (ZMod m)) (x : piece i j) : piece i j :=
  ⟨⟨lensRotation m ℓ a x, by
      rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map, norm_eq_of_mem_sphere]⟩, by
    simpa [piece, norm_lensRotation_apply] using x.2⟩

private theorem coe_rotatePiece {i j : Fin 2} (a : Multiplicative (ZMod m)) (x : piece i j) :
    (rotatePiece m ℓ a x : EuclideanSpace ℂ (Fin 2)) = lensRotation m ℓ a x :=
  (rfl)

/-- The rotation by `a` multiplies each normalised coordinate `x k / ‖x j‖` of a point of the solid
torus `‖x i‖ ≤ ‖x j‖` by `ζ ^ ℓₖ`. -/
private theorem norm_inv_smul_rotatePiece {i j : Fin 2} (a : Multiplicative (ZMod m))
    (x : piece i j) (k : Fin 2) :
    ‖(rotatePiece m ℓ a x : EuclideanSpace ℂ (Fin 2)) j‖⁻¹ •
        (rotatePiece m ℓ a x : EuclideanSpace ℂ (Fin 2)) k =
      ZMod.toCircle ((ℓ k : ZMod m) * a.toAdd) *
        (‖(x : EuclideanSpace ℂ (Fin 2)) j‖⁻¹ • (x : EuclideanSpace ℂ (Fin 2)) k) := by
  rw [coe_rotatePiece, norm_lensRotation_apply, lensRotation_apply, mul_smul_comm]

/-- The fibres of the quotient map `x ↦ (u conj(v) ^ c, v ^ m)` of the solid torus `‖x i‖ ≤ ‖x j‖`
onto `D² × S¹`, for the disc and core coordinates `u = x i / ‖x j‖`, `v = x j / ‖x j‖`, are the
orbits of the lens group. -/
private theorem pieceQuotient_eq_iff {i j : Fin 2} (hij : i ≠ j) (x y : piece i j) :
    modelQuotient m ℓ i j (pieceHomeomorph hij x) = modelQuotient m ℓ i j (pieceHomeomorph hij y) ↔
      mk m ℓ x = mk m ℓ y := by
  rw [modelQuotient_eq_iff, mk_eq_mk_iff, coe_pieceHomeomorph_fst, coe_pieceHomeomorph_fst,
    coe_pieceHomeomorph_snd, coe_pieceHomeomorph_snd]
  constructor
  · rintro ⟨b, h1, h2⟩
    have : rotatePiece m ℓ (.ofAdd b) y = x := by
      refine (pieceHomeomorph hij).injective (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
      · rw [coe_pieceHomeomorph_fst, coe_pieceHomeomorph_fst, h1, norm_inv_smul_rotatePiece,
          toAdd_ofAdd]
      · rw [coe_pieceHomeomorph_snd, coe_pieceHomeomorph_snd, h2, norm_inv_smul_rotatePiece,
          toAdd_ofAdd]
    exact ⟨.ofAdd b, congrArg (fun z : piece i j ↦ (z : EuclideanSpace ℂ (Fin 2))) this⟩
  · rintro ⟨a, ha⟩
    obtain rfl : x = rotatePiece m ℓ a y := Subtype.ext (Subtype.ext ha.symm)
    exact ⟨a.toAdd, norm_inv_smul_rotatePiece m ℓ a y i, norm_inv_smul_rotatePiece m ℓ a y j⟩

/-- **The image of each solid torus in a lens space is a solid torus.** -/
private theorem nonempty_homeomorph_image_piece {i j : Fin 2} (hij : i ≠ j) :
    Nonempty (mk m ℓ '' piece i j ≃ₜ handlebody 1) :=
  (nonempty_homeomorph_image_of_forall_eq_iff (continuous_mk m ℓ) (isCompact_piece i j)
    (modelQuotient m ℓ i j ∘ pieceHomeomorph hij)
    ((continuous_modelQuotient m ℓ i j).comp (pieceHomeomorph hij).continuous)
    ((modelQuotient_surjective m ℓ i j).comp (pieceHomeomorph hij).surjective)
    (pieceQuotient_eq_iff m ℓ hij)).map fun e ↦ e.trans nonempty_homeomorph_handlebody_one.some.symm

/-! ### The genus-one splitting -/

/-- The genus-one Heegaard splitting of the unit sphere of `ℂ²` into the solid tori `‖x 0‖ ≤ ‖x 1‖`
and `‖x 1‖ ≤ ‖x 0‖`, transported from `TauCeti.cliffordHeegaardSplitting`. -/
private def sphereHeegaardSplitting : HeegaardSplitting (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :=
  cliffordHeegaardSplitting.transHomeomorph
    ((EuclideanSpace.finTwoEquivProd ℂ).unitSphereIsometryEquiv.toHomeomorph.symm)

private theorem sphereHeegaardSplitting_left : sphereHeegaardSplitting.left = piece 0 1 := by
  rw [sphereHeegaardSplitting, HeegaardSplitting.transHomeomorph_left, Homeomorph.image_symm]
  ext x
  simp [piece]

private theorem sphereHeegaardSplitting_right : sphereHeegaardSplitting.right = piece 1 0 := by
  rw [sphereHeegaardSplitting, HeegaardSplitting.transHomeomorph_right, Homeomorph.image_symm]
  ext x
  simp [piece]

/-- **The genus-one Heegaard splitting of a lens space.** The lens space `L(m; ℓ₀, ℓ₁)` is the
union of the images of the solid tori `‖z‖ ≤ ‖w‖` and `‖w‖ ≤ ‖z‖` of the unit sphere of `ℂ²`,
which are solid tori meeting along the image of the Clifford torus `‖z‖ = ‖w‖`. -/
def heegaardSplitting : HeegaardSplitting (LensSpace m ℓ) :=
  sphereHeegaardSplitting.ofIsOpenQuotientMap (isOpenQuotientMap_mk m ℓ)
    (by rw [sphereHeegaardSplitting_left]; exact preimage_image_piece m ℓ 0 1)
    (by rw [sphereHeegaardSplitting_right]; exact preimage_image_piece m ℓ 1 0) 1
    (by rw [sphereHeegaardSplitting_left]; exact nonempty_homeomorph_image_piece m ℓ (by decide))
    (by rw [sphereHeegaardSplitting_right]; exact nonempty_homeomorph_image_piece m ℓ (by decide))

@[simp] theorem heegaardSplitting_genus : (heegaardSplitting m ℓ).genus = 1 :=
  HeegaardSplitting.ofIsOpenQuotientMap_genus _ _ _ _ _ _ _

@[simp]
theorem heegaardSplitting_left :
    (heegaardSplitting m ℓ).left =
      mk m ℓ '' {x | ‖(x : EuclideanSpace ℂ (Fin 2)) 0‖ ≤ ‖(x : EuclideanSpace ℂ (Fin 2)) 1‖} := by
  rw [heegaardSplitting, HeegaardSplitting.ofIsOpenQuotientMap_left, sphereHeegaardSplitting_left,
    piece]

@[simp]
theorem heegaardSplitting_right :
    (heegaardSplitting m ℓ).right =
      mk m ℓ '' {x | ‖(x : EuclideanSpace ℂ (Fin 2)) 1‖ ≤ ‖(x : EuclideanSpace ℂ (Fin 2)) 0‖} := by
  rw [heegaardSplitting, HeegaardSplitting.ofIsOpenQuotientMap_right,
    sphereHeegaardSplitting_right, piece]

instance : Nonempty (HeegaardSplitting (LensSpace m ℓ)) := ⟨heegaardSplitting m ℓ⟩

/-- A lens space `L(m; ℓ₀, ℓ₁)` has Heegaard genus at most one. -/
theorem heegaardGenus_le_one : heegaardGenus (LensSpace m ℓ) ≤ 1 :=
  (heegaardGenus_le (heegaardSplitting m ℓ)).trans_eq (heegaardSplitting_genus m ℓ)

/-- The fundamental group of a lens space `L(m; ℓ₀, ℓ₁)` is finitely generated. -/
instance fg_fundamentalGroup (x : LensSpace m ℓ) : Group.FG (FundamentalGroup (LensSpace m ℓ) x) :=
  (heegaardSplitting m ℓ).fg_fundamentalGroup (E := EuclideanSpace ℝ (Fin 3)) (by simp) x

/-- For `m ≠ 1`, the fundamental group `ℤ/m` of a lens space `L(m; ℓ₀, ℓ₁)` has rank one: it is
nontrivial, while its rank is at most the Heegaard genus, which is at most one. -/
theorem rank_fundamentalGroup_eq_one (hm : m ≠ 1) (x : LensSpace m ℓ) :
    Group.rank (FundamentalGroup (LensSpace m ℓ) x) = 1 := by
  have := nontrivial_fundamentalGroup m ℓ le_rfl hm x
  have h := rank_fundamentalGroup_le_heegaardGenus (E := EuclideanSpace ℝ (Fin 3)) (by simp) x
  have h0 : Group.rank (FundamentalGroup (LensSpace m ℓ) x) ≠ 0 := by
    rw [Ne, Group.rank_eq_zero_iff]
    exact not_subsingleton _
  have := heegaardGenus_le_one m ℓ
  omega

/-- **A lens space `L(m; ℓ₀, ℓ₁)` with `m ≠ 1` has Heegaard genus one.** It has a splitting of
genus one, and none of genus zero, since its fundamental group `ℤ/m` has rank one while its rank is
at most the Heegaard genus. -/
theorem heegaardGenus_eq_one (hm : m ≠ 1) : heegaardGenus (LensSpace m ℓ) = 1 := by
  let x : LensSpace m ℓ := Classical.arbitrary _
  refine le_antisymm (heegaardGenus_le_one m ℓ) ?_
  exact (rank_fundamentalGroup_eq_one m ℓ hm x).ge.trans
    (rank_fundamentalGroup_le_heegaardGenus (E := EuclideanSpace ℝ (Fin 3)) (by simp) x)

/-- **A lens space satisfies Waldhausen's equation**: for `m ≠ 1`, the Heegaard genus of
`L(m; ℓ₀, ℓ₁)` equals the rank of its fundamental group, both being one. -/
theorem heegaardGenus_eq_rank (hm : m ≠ 1) (x : LensSpace m ℓ) :
    heegaardGenus (LensSpace m ℓ) = Group.rank (FundamentalGroup (LensSpace m ℓ) x) := by
  rw [heegaardGenus_eq_one m ℓ hm, rank_fundamentalGroup_eq_one m ℓ hm x]

end LensSpace

end TauCeti
