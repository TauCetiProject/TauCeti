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
`‖z‖ ≤ ‖w‖` the rotation acts on the coordinates `(u, v) = (z / ‖w‖, w / ‖w‖) ∈ D² × S¹` by
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

/-! ### The two solid tori of a lens space -/

namespace LensSpace

variable (m : ℕ) [NeZero m] (ℓ : Fin 2 → (ZMod m)ˣ)

/-- The coordinates of a point of the unit sphere of `ℂ²` have squared norms summing to one. -/
private theorem norm_sq_add_norm_sq {i j : Fin 2} (hij : i ≠ j)
    (x : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    ‖(x : EuclideanSpace ℂ (Fin 2)) i‖ ^ 2 + ‖(x : EuclideanSpace ℂ (Fin 2)) j‖ ^ 2 = 1 := by
  have h := EuclideanSpace.norm_sq_eq (x : EuclideanSpace ℂ (Fin 2))
  rw [Fin.sum_univ_two, norm_eq_of_mem_sphere x, one_pow] at h
  fin_cases i <;> fin_cases j <;> simp_all [add_comm]

/-- On the solid torus `‖x i‖ ≤ ‖x j‖`, the core coordinate `x j` does not vanish. -/
private theorem norm_pos_of_le {i j : Fin 2} (hij : i ≠ j)
    {x : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1}
    (hx : ‖(x : EuclideanSpace ℂ (Fin 2)) i‖ ≤ ‖(x : EuclideanSpace ℂ (Fin 2)) j‖) :
    0 < ‖(x : EuclideanSpace ℂ (Fin 2)) j‖ := by
  have h := norm_sq_add_norm_sq hij x
  have := norm_nonneg ((x : EuclideanSpace ℂ (Fin 2)) i)
  by_contra! h0
  nlinarith

/-- The exponent `c = ℓᵢ ℓⱼ⁻¹` of the invariant `u conj(v) ^ c` on the solid torus
`‖x i‖ ≤ ‖x j‖`. -/
private def twist (i j : Fin 2) : ℕ := ((ℓ i * (ℓ j)⁻¹ : (ZMod m)ˣ) : ZMod m).val

/-- The twist exponent satisfies `c ℓⱼ = ℓᵢ` modulo `m`, so the `c`-th power of the rotation of the
core coordinate is the rotation of the disc coordinate. -/
private theorem toCircle_pow_twist (i j : Fin 2) (t : ZMod m) :
    ZMod.toCircle ((ℓ j : ZMod m) * t) ^ twist m ℓ i j = ZMod.toCircle ((ℓ i : ZMod m) * t) := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, twist, ZMod.natCast_zmod_val, ← mul_assoc,
    Units.val_mul, Units.inv_mul_cancel_right]

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

/-- The disc coordinate `x i / ‖x j‖` of a point of the solid torus `‖x i‖ ≤ ‖x j‖`. -/
private def discCoord (i j : Fin 2) (x : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) : ℂ :=
  (x : EuclideanSpace ℂ (Fin 2)) i / (‖(x : EuclideanSpace ℂ (Fin 2)) j‖ : ℂ)

/-- The core coordinate `x j / ‖x j‖` of a point of the solid torus `‖x i‖ ≤ ‖x j‖`. -/
private def coreCoord (j : Fin 2) (x : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) : ℂ :=
  (x : EuclideanSpace ℂ (Fin 2)) j / (‖(x : EuclideanSpace ℂ (Fin 2)) j‖ : ℂ)

private theorem norm_coreCoord {i j : Fin 2} (hij : i ≠ j) (x : piece i j) :
    ‖coreCoord j x‖ = 1 := by
  have h := norm_pos_of_le hij x.2
  rw [coreCoord, norm_div, Complex.norm_real, Real.norm_of_nonneg h.le, div_self h.ne']

private theorem norm_discCoord {i j : Fin 2} (hij : i ≠ j) (x : piece i j) :
    ‖discCoord i j x‖ ≤ 1 := by
  have h := norm_pos_of_le hij x.2
  rw [discCoord, norm_div, Complex.norm_real, Real.norm_of_nonneg h.le, div_le_one h]
  exact x.2

/-- The quotient map of the solid torus `‖x i‖ ≤ ‖x j‖` onto `D² × S¹`:
`x ↦ (u conj(v) ^ c, v ^ m)` for the disc and core coordinates `u = x i / ‖x j‖`,
`v = x j / ‖x j‖`. -/
private def pieceQuotient {i j : Fin 2} (hij : i ≠ j) (x : piece i j) : SolidTorus :=
  (⟨discCoord i j x * (starRingEnd ℂ (coreCoord j x)) ^ twist m ℓ i j, by
      rw [mem_closedBall_zero_iff, norm_mul, norm_pow, Complex.norm_conj, norm_coreCoord hij,
        one_pow, mul_one]
      exact norm_discCoord hij x⟩,
    ⟨coreCoord j x ^ m, mem_sphere_zero_iff_norm.2 (by rw [norm_pow, norm_coreCoord hij, one_pow])⟩)

omit [NeZero m] in
private theorem continuous_pieceQuotient {i j : Fin 2} (hij : i ≠ j) :
    Continuous (pieceQuotient m ℓ hij) := by
  have hne (x : piece i j) : (‖(x : EuclideanSpace ℂ (Fin 2)) j‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (norm_pos_of_le hij x.2).ne'
  have hc : Continuous fun x : piece i j ↦ coreCoord j x :=
    .div (by fun_prop) (by fun_prop) hne
  have hd : Continuous fun x : piece i j ↦ discCoord i j x :=
    .div (by fun_prop) (by fun_prop) hne
  refine .prodMk (.subtype_mk ?_ _) (.subtype_mk ?_ _)
  · exact hd.mul ((Complex.continuous_conj.comp hc).pow _)
  · exact hc.pow _

omit [NeZero m] in
private theorem coe_pieceQuotient_fst {i j : Fin 2} (hij : i ≠ j) (x : piece i j) :
    ((pieceQuotient m ℓ hij x).1 : ℂ) =
      discCoord i j x * (starRingEnd ℂ (coreCoord j x)) ^ twist m ℓ i j :=
  (rfl)

omit [NeZero m] in
private theorem coe_pieceQuotient_snd {i j : Fin 2} (hij : i ≠ j) (x : piece i j) :
    ((pieceQuotient m ℓ hij x).2 : ℂ) = coreCoord j x ^ m :=
  (rfl)

/-- Points of the solid torus `‖x i‖ ≤ ‖x j‖` whose disc coordinates have the same norm have core
coordinates of the same norm, since the squared norms of the two coordinates sum to one. -/
private theorem norm_eq_of_norm_discCoord_eq {i j : Fin 2} (hij : i ≠ j) {x y : piece i j}
    (h : ‖discCoord i j x‖ = ‖discCoord i j y‖) :
    ‖(x : EuclideanSpace ℂ (Fin 2)) j‖ = ‖(y : EuclideanSpace ℂ (Fin 2)) j‖ := by
  have hxj := norm_pos_of_le hij x.2
  have hyj := norm_pos_of_le hij y.2
  simp only [discCoord, norm_div, Complex.norm_real, Real.norm_of_nonneg hxj.le,
    Real.norm_of_nonneg hyj.le] at h
  rw [div_eq_div_iff hxj.ne' hyj.ne'] at h
  have hx2 := norm_sq_add_norm_sq hij x
  have hy2 := norm_sq_add_norm_sq hij y
  refine (pow_left_inj₀ hxj.le hyj.le two_ne_zero).1 ?_
  linear_combination (‖(y : EuclideanSpace ℂ (Fin 2)) j‖ ^ 2) * hx2 -
    (‖(x : EuclideanSpace ℂ (Fin 2)) j‖ ^ 2) * hy2 -
    (‖(x : EuclideanSpace ℂ (Fin 2)) i‖ * ‖(y : EuclideanSpace ℂ (Fin 2)) j‖ +
      ‖(y : EuclideanSpace ℂ (Fin 2)) i‖ * ‖(x : EuclideanSpace ℂ (Fin 2)) j‖) * h

/-- For points of the solid torus `‖x i‖ ≤ ‖x j‖` with core coordinates of the same norm, a
relation between the normalised coordinates `x k / ‖x j‖` is a relation between the coordinates. -/
private theorem div_norm_eq_mul_div_norm_iff {i j : Fin 2} (hij : i ≠ j) {x y : piece i j}
    (hρ : ‖(x : EuclideanSpace ℂ (Fin 2)) j‖ = ‖(y : EuclideanSpace ℂ (Fin 2)) j‖) (k : Fin 2)
    (ω : ℂ) :
    (x : EuclideanSpace ℂ (Fin 2)) k / (‖(x : EuclideanSpace ℂ (Fin 2)) j‖ : ℂ) =
        ω * ((y : EuclideanSpace ℂ (Fin 2)) k / (‖(y : EuclideanSpace ℂ (Fin 2)) j‖ : ℂ)) ↔
      (x : EuclideanSpace ℂ (Fin 2)) k = ω * (y : EuclideanSpace ℂ (Fin 2)) k := by
  rw [hρ, ← mul_div_assoc,
    div_left_inj' (Complex.ofReal_ne_zero.2 (norm_pos_of_le hij y.2).ne')]

/-- The fibres of the quotient map of a solid torus onto `D² × S¹` are the orbits of the lens
group. -/
private theorem pieceQuotient_eq_iff {i j : Fin 2} (hij : i ≠ j) (x y : piece i j) :
    pieceQuotient m ℓ hij x = pieceQuotient m ℓ hij y ↔ mk m ℓ x = mk m ℓ y := by
  have hk (k : Fin 2) : k = i ∨ k = j := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  have hcy : coreCoord j y ≠ 0 := norm_ne_zero_iff.1 (by rw [norm_coreCoord hij y]; norm_num)
  set c := twist m ℓ i j
  constructor
  · intro h
    have h1 := congrArg (fun p : SolidTorus ↦ ((p.1 : closedBall (0 : ℂ) 1) : ℂ)) h
    have h2 := congrArg (fun p : SolidTorus ↦ ((p.2 : Circle) : ℂ)) h
    simp only [coe_pieceQuotient_fst, coe_pieceQuotient_snd] at h1 h2
    have hρ := norm_eq_of_norm_discCoord_eq hij (by
      simpa [norm_mul, norm_pow, Complex.norm_conj, norm_coreCoord hij] using congrArg norm h1)
    -- The ratio of the core coordinates is an `m`-th root of unity `ω`.
    set ω := coreCoord j x / coreCoord j y
    have hω1 : ‖ω‖ = 1 := by rw [norm_div, norm_coreCoord hij, norm_coreCoord hij, div_one]
    have hωm : ω ^ m = 1 := by rw [div_pow, h2, div_self (pow_ne_zero _ hcy)]
    have hcore : coreCoord j x = ω * coreCoord j y := by rw [div_mul_cancel₀ _ hcy]
    have hdisc : discCoord i j x = ω ^ c * discCoord i j y := by
      rw [hcore, map_mul, mul_pow] at h1
      have hc : (starRingEnd ℂ (coreCoord j y)) ^ c ≠ 0 :=
        pow_ne_zero _ ((map_ne_zero _).2 hcy)
      have h1' : discCoord i j x * (starRingEnd ℂ ω) ^ c = discCoord i j y :=
        mul_right_cancel₀ hc (by rw [← h1]; ring)
      have hωc : ω ^ c * (starRingEnd ℂ ω) ^ c = 1 := by
        rw [← mul_pow, Complex.mul_conj', hω1]
        norm_num
      rw [← h1']
      linear_combination (-discCoord i j x) * hωc
    -- Every `m`-th root of unity is a rotation `ZMod.toCircle b`.
    obtain ⟨b, hb⟩ := surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar m
      ⟨Units.mk0 ω (norm_ne_zero_iff.1 (by rw [hω1]; norm_num)), (mem_rootsOfUnity' m _).2 hωm⟩
    replace hb : (ZMod.toCircle b : ℂ) = ω := by
      simpa using congrArg (fun u : rootsOfUnity m ℂ ↦ ((u : ℂˣ) : ℂ)) hb
    refine (mk_eq_mk_iff m ℓ x y).2 ⟨Multiplicative.ofAdd (((ℓ j)⁻¹ : (ZMod m)ˣ) * b), ?_⟩
    ext k
    rw [lensRotation_apply, toAdd_ofAdd]
    rcases hk k with rfl | rfl
    · rw [← toCircle_pow_twist, Units.mul_inv_cancel_left, Circle.coe_pow, hb]
      rw [discCoord, discCoord, div_norm_eq_mul_div_norm_iff hij hρ] at hdisc
      exact hdisc.symm
    · rw [Units.mul_inv_cancel_left, hb]
      rw [coreCoord, coreCoord, div_norm_eq_mul_div_norm_iff hij hρ] at hcore
      exact hcore.symm
  · intro h
    obtain ⟨a, ha⟩ := (mk_eq_mk_iff m ℓ x y).1 h
    have hxk (k : Fin 2) : (x : EuclideanSpace ℂ (Fin 2)) k =
        (ZMod.toCircle ((ℓ k : ZMod m) * a.toAdd) : ℂ) * (y : EuclideanSpace ℂ (Fin 2)) k := by
      rw [← ha, lensRotation_apply]
    have hρ : ‖(x : EuclideanSpace ℂ (Fin 2)) j‖ = ‖(y : EuclideanSpace ℂ (Fin 2)) j‖ := by
      rw [← ha, norm_lensRotation_apply]
    set z : ℂ := (ZMod.toCircle ((ℓ j : ZMod m) * a.toAdd) : ℂ)
    have hz : z ^ c * (starRingEnd ℂ z) ^ c = 1 := by
      rw [← mul_pow, Complex.mul_conj', Circle.norm_coe]
      norm_num
    have hzm : z ^ m = 1 := by
      rw [← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
        AddChar.map_zero_eq_one, Circle.coe_one]
    have hcore : coreCoord j x = z * coreCoord j y := by
      rw [coreCoord, coreCoord, div_norm_eq_mul_div_norm_iff hij hρ]
      exact hxk j
    have hdisc : discCoord i j x = z ^ c * discCoord i j y := by
      rw [discCoord, discCoord, div_norm_eq_mul_div_norm_iff hij hρ, hxk i, ← toCircle_pow_twist,
        Circle.coe_pow]
    refine Prod.ext (Subtype.ext ?_) (Circle.ext ?_)
    · rw [coe_pieceQuotient_fst, coe_pieceQuotient_fst, hdisc, hcore, map_mul, mul_pow]
      linear_combination (discCoord i j y * (starRingEnd ℂ (coreCoord j y)) ^ c) * hz
    · rw [coe_pieceQuotient_snd, coe_pieceQuotient_snd, hcore, mul_pow, hzm, one_mul]

/-- Every disc value `u` and core value `w` of norm one are the coordinates of a point of the solid
torus `‖x i‖ ≤ ‖x j‖`, namely of the unit vector in the direction of `(u, w)`. -/
private theorem exists_discCoord_coreCoord {i j : Fin 2} (hij : i ≠ j) {u w : ℂ} (hu : ‖u‖ ≤ 1)
    (hw : ‖w‖ = 1) : ∃ x : piece i j, discCoord i j x = u ∧ coreCoord j x = w := by
  set ρ : ℝ := (√(1 + ‖u‖ ^ 2))⁻¹
  have hρ : 0 < ρ := inv_pos.2 (Real.sqrt_pos.2 (by positivity))
  have hρ2 : ρ ^ 2 * (1 + ‖u‖ ^ 2) = 1 := by
    rw [inv_pow, Real.sq_sqrt (by positivity), inv_mul_cancel₀ (by positivity)]
  let z : EuclideanSpace ℂ (Fin 2) :=
    WithLp.toLp 2 fun k ↦ if k = i then (ρ : ℂ) * u else (ρ : ℂ) * w
  have hzi : z i = (ρ : ℂ) * u := by simp [z]
  have hzj : z j = (ρ : ℂ) * w := by simp [z, hij.symm]
  have hnzi : ‖z i‖ = ρ * ‖u‖ := by
    rw [hzi, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  have hnzj : ‖z j‖ = ρ := by
    rw [hzj, norm_mul, hw, mul_one, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  have hz : z ∈ sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 := by
    rw [mem_sphere_zero_iff_norm, ← pow_left_inj₀ (norm_nonneg z) zero_le_one two_ne_zero,
      EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, one_pow]
    have : ‖z i‖ ^ 2 + ‖z j‖ ^ 2 = 1 := by
      rw [hnzi, hnzj]
      linear_combination hρ2
    fin_cases i <;> fin_cases j <;> simp_all [add_comm]
  have hzp : (⟨z, hz⟩ : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) ∈ piece i j := by
    rw [piece, mem_ofPred_eq, hnzi, hnzj]
    exact mul_le_of_le_one_right hρ.le hu
  have hρ' : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ.ne'
  refine ⟨⟨⟨z, hz⟩, hzp⟩, ?_, ?_⟩
  · rw [discCoord, hzi, hnzj, mul_div_cancel_left₀ _ hρ']
  · rw [coreCoord, hnzj, hzj, mul_div_cancel_left₀ _ hρ']

/-- The quotient map of a solid torus onto `D² × S¹` is surjective. -/
private theorem pieceQuotient_surjective {i j : Fin 2} (hij : i ≠ j) :
    Surjective (pieceQuotient m ℓ hij) := by
  rintro ⟨⟨u, hu⟩, v⟩
  rw [mem_closedBall_zero_iff] at hu
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (v : ℂ) (Nat.pos_of_ne_zero (NeZero.ne m))
  have hw1 : ‖w‖ = 1 := by
    rw [← pow_left_inj₀ (norm_nonneg w) zero_le_one (NeZero.ne m), ← norm_pow, hw,
      Circle.norm_coe, one_pow]
  have hwc : w * starRingEnd ℂ w = 1 := by
    rw [Complex.mul_conj', hw1]
    norm_num
  set c := twist m ℓ i j
  obtain ⟨x, hxd, hxc⟩ := exists_discCoord_coreCoord hij (u := u * w ^ c)
    (by rwa [norm_mul, norm_pow, hw1, one_pow, mul_one]) hw1
  refine ⟨x, Prod.ext (Subtype.ext ?_) (Circle.ext ?_)⟩
  · rw [coe_pieceQuotient_fst, hxd, hxc, mul_assoc, ← mul_pow, hwc, one_pow, mul_one]
  · rw [coe_pieceQuotient_snd, hxc, hw]

/-- The solid torus `‖x i‖ ≤ ‖x j‖` is compact. -/
private theorem isCompact_piece (i j : Fin 2) : IsCompact (piece i j) :=
  (isClosed_le (by fun_prop) (by fun_prop)).isCompact

/-- **The image of each solid torus in a lens space is a solid torus.** -/
private theorem nonempty_homeomorph_image_piece {i j : Fin 2} (hij : i ≠ j) :
    Nonempty (mk m ℓ '' piece i j ≃ₜ handlebody 1) :=
  (nonempty_homeomorph_image_of_forall_eq_iff (continuous_mk m ℓ) (isCompact_piece i j)
    (pieceQuotient m ℓ hij) (continuous_pieceQuotient m ℓ hij) (pieceQuotient_surjective m ℓ hij)
    (pieceQuotient_eq_iff m ℓ hij)).map fun e ↦ e.trans nonempty_homeomorph_handlebody_one.some.symm

/-! ### The genus-one splitting -/

/-- The genus-one Heegaard splitting of the unit sphere of `ℂ²` into the solid tori `‖x 0‖ ≤ ‖x 1‖`
and `‖x 1‖ ≤ ‖x 0‖`, transported from `TauCeti.cliffordHeegaardSplitting`. -/
private def sphereHeegaardSplitting : HeegaardSplitting (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :=
  cliffordHeegaardSplitting.transHomeomorph
    ((EuclideanSpace.finTwoEquivProd ℂ).unitSphereIsometryEquiv.toHomeomorph.symm)

private theorem sphereHeegaardSplitting_left : sphereHeegaardSplitting.left = piece 0 1 := by
  ext x
  rw [sphereHeegaardSplitting, HeegaardSplitting.transHomeomorph_left, Homeomorph.image_symm,
    mem_preimage, IsometryEquiv.coe_toHomeomorph, cliffordHeegaardSplitting_left, mem_ofPred_eq,
    LinearIsometryEquiv.coe_unitSphereIsometryEquiv_apply, EuclideanSpace.finTwoEquivProd_apply_fst,
    EuclideanSpace.finTwoEquivProd_apply_snd, piece, mem_ofPred_eq]

private theorem sphereHeegaardSplitting_right : sphereHeegaardSplitting.right = piece 1 0 := by
  ext x
  rw [sphereHeegaardSplitting, HeegaardSplitting.transHomeomorph_right, Homeomorph.image_symm,
    mem_preimage, IsometryEquiv.coe_toHomeomorph, cliffordHeegaardSplitting_right, mem_ofPred_eq,
    LinearIsometryEquiv.coe_unitSphereIsometryEquiv_apply, EuclideanSpace.finTwoEquivProd_apply_fst,
    EuclideanSpace.finTwoEquivProd_apply_snd, piece, mem_ofPred_eq]

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
