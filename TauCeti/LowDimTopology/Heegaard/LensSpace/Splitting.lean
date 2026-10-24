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
public import TauCeti.Topology.Maps.OpenQuotient
import Mathlib.FieldTheory.IsAlgClosed.Basic
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

The splitting is obtained from a general descent principle: a Heegaard splitting whose two pieces
are saturated for an open quotient map descends to the quotient, as soon as the images of the
pieces are handlebodies (`TauCeti.HeegaardSplitting.ofIsOpenQuotientMap`).

Since the fundamental group `ℤ/m` of a lens space with `m ≠ 1` is nontrivial, and its rank is at
most the Heegaard genus (`TauCeti.rank_fundamentalGroup_le_heegaardGenus`), such a lens space has
Heegaard genus exactly one, and its Heegaard genus equals the rank of its fundamental group, as in
Waldhausen's rank-versus-genus conjecture (`TauCeti.RankGenusConjecture`).

## Main definitions

* `TauCeti.HeegaardSplitting.ofIsOpenQuotientMap`: the image of a Heegaard splitting with
  saturated pieces under an open quotient map.
* `TauCeti.LensSpace.heegaardSplitting`: the genus-one Heegaard splitting of `L(m; ℓ₀, ℓ₁)` into
  the images of the solid tori `‖z‖ ≤ ‖w‖` and `‖w‖ ≤ ‖z‖`.

## Main results

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

/-! ### Descending Heegaard splittings -/

namespace HeegaardSplitting

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {π : X → Y}

/-- **Heegaard splittings descend along open quotient maps.** If both pieces of a Heegaard
splitting of `X` are saturated for an open quotient map `π : X → Y`, and their images are
handlebodies of genus `g`, then the images form a Heegaard splitting of `Y` of genus `g`. -/
def ofIsOpenQuotientMap (s : HeegaardSplitting X) (hπ : IsOpenQuotientMap π)
    (hl : π ⁻¹' (π '' s.left) = s.left) (hr : π ⁻¹' (π '' s.right) = s.right) (g : ℕ)
    (el : Nonempty (π '' s.left ≃ₜ handlebody g)) (er : Nonempty (π '' s.right ≃ₜ handlebody g)) :
    HeegaardSplitting Y where
  genus := g
  left := π '' s.left
  right := π '' s.right
  union_eq_univ := by rw [← image_union, s.union_eq_univ, image_univ, hπ.surjective.range_eq]
  inter_eq_frontier_left := by
    rw [← image_inter_preimage, hr, hπ.frontier_image_of_preimage_image_eq hl,
      s.inter_eq_frontier_left]
  inter_eq_frontier_right := by
    rw [← image_inter_preimage, hr, hπ.frontier_image_of_preimage_image_eq hr,
      s.inter_eq_frontier_right]
  nonempty_homeomorph_left := el
  nonempty_homeomorph_right := er

@[simp]
theorem ofIsOpenQuotientMap_genus (s : HeegaardSplitting X) (hπ : IsOpenQuotientMap π) (hl hr)
    (g : ℕ) (el er) : (s.ofIsOpenQuotientMap hπ hl hr g el er).genus = g :=
  (rfl)

@[simp]
theorem ofIsOpenQuotientMap_left (s : HeegaardSplitting X) (hπ : IsOpenQuotientMap π) (hl hr)
    (g : ℕ) (el er) : (s.ofIsOpenQuotientMap hπ hl hr g el er).left = π '' s.left :=
  (rfl)

@[simp]
theorem ofIsOpenQuotientMap_right (s : HeegaardSplitting X) (hπ : IsOpenQuotientMap π) (hl hr)
    (g : ℕ) (el er) : (s.ofIsOpenQuotientMap hπ hl hr g el er).right = π '' s.right :=
  (rfl)

end HeegaardSplitting

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

/-- A rotation of the lens group preserves the norm of each coordinate. -/
private theorem norm_lensRotation_apply (a : Multiplicative (ZMod m))
    (x : EuclideanSpace ℂ (Fin 2)) (k : Fin 2) : ‖lensRotation m ℓ a x k‖ = ‖x k‖ := by
  simp [lensRotation_apply]

/-- The exponent `c = ℓᵢ ℓⱼ⁻¹` of the invariant `u conj(v) ^ c` on the solid torus
`‖x i‖ ≤ ‖x j‖`. -/
private def twist (i j : Fin 2) : ℕ := ((ℓ i * (ℓ j)⁻¹ : (ZMod m)ˣ) : ZMod m).val

/-- The twist exponent satisfies `c ℓⱼ = ℓᵢ` modulo `m`, so the `c`-th power of the rotation of the
core coordinate is the rotation of the disc coordinate. -/
private theorem toCircle_pow_twist (i j : Fin 2) (t : ZMod m) :
    ZMod.toCircle ((ℓ j : ZMod m) * t) ^ twist m ℓ i j = ZMod.toCircle ((ℓ i : ZMod m) * t) := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, twist, ZMod.natCast_zmod_val, ← mul_assoc,
    Units.val_mul, Units.inv_mul_cancel_right]

/-- An `m`-th root of unity in `ℂ` is the image of a residue modulo `m` under `ZMod.toCircle`. -/
private theorem exists_toCircle_eq {ω : ℂ} (hω : ω ^ m = 1) :
    ∃ b : ZMod m, (ZMod.toCircle b : ℂ) = ω := by
  obtain ⟨i, -, hi⟩ :=
    (Complex.isPrimitiveRoot_exp m (NeZero.ne m)).eq_pow_of_pow_eq_one hω
  refine ⟨i, ?_⟩
  rw [ZMod.toCircle_natCast, ← hi, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- The `m`-th power of a rotation of the lens group by a residue modulo `m` is one. -/
private theorem toCircle_pow_self (t : ZMod m) : ZMod.toCircle t ^ m = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
    AddChar.map_zero_eq_one]

/-- The solid torus `‖x i‖ ≤ ‖x j‖` of the unit sphere of `ℂ²`. -/
private def piece (i j : Fin 2) : Set (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :=
  {x | ‖(x : EuclideanSpace ℂ (Fin 2)) i‖ ≤ ‖(x : EuclideanSpace ℂ (Fin 2)) j‖}

/-- The solid tori are saturated for the projection to the lens space. -/
private theorem preimage_image_piece (i j : Fin 2) :
    mk m ℓ ⁻¹' (mk m ℓ '' piece i j) = piece i j := by
  refine (subset_preimage_image _ _).antisymm' ?_
  rintro x ⟨y, hy, hxy⟩
  obtain ⟨a, ha⟩ := (mk_eq_mk_iff m ℓ y x).1 hxy
  simpa [piece, ← ha, norm_lensRotation_apply] using hy

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

/-- A complex number of norm one times its conjugate is one. -/
private theorem mul_conj_eq_one {z : ℂ} (hz : ‖z‖ = 1) : z * starRingEnd ℂ z = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  norm_num

/-- The fibres of the quotient map of a solid torus onto `D² × S¹` are the orbits of the lens
group. -/
private theorem pieceQuotient_eq_iff {i j : Fin 2} (hij : i ≠ j) (x y : piece i j) :
    pieceQuotient m ℓ hij x = pieceQuotient m ℓ hij y ↔ mk m ℓ x = mk m ℓ y := by
  have hk (k : Fin 2) : k = i ∨ k = j := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  have hxj := norm_pos_of_le hij x.2
  have hyj := norm_pos_of_le hij y.2
  have hyj' : (‖(y : EuclideanSpace ℂ (Fin 2)) j‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hyj.ne'
  have hcy : coreCoord j y ≠ 0 := norm_ne_zero_iff.1 (by rw [norm_coreCoord hij y]; norm_num)
  set c := twist m ℓ i j
  constructor
  · intro h
    have h1 := congrArg (fun p : SolidTorus ↦ ((p.1 : closedBall (0 : ℂ) 1) : ℂ)) h
    have h2 := congrArg (fun p : SolidTorus ↦ ((p.2 : Circle) : ℂ)) h
    simp only [coe_pieceQuotient_fst, coe_pieceQuotient_snd] at h1 h2
    -- The two points have the same coordinate norms.
    have hd : ‖discCoord i j x‖ = ‖discCoord i j y‖ := by
      simpa [norm_mul, norm_pow, Complex.norm_conj, norm_coreCoord hij] using congrArg norm h1
    simp only [discCoord, norm_div, Complex.norm_real, Real.norm_of_nonneg hxj.le,
      Real.norm_of_nonneg hyj.le] at hd
    rw [div_eq_div_iff hxj.ne' hyj.ne'] at hd
    have hx2 := norm_sq_add_norm_sq hij x
    have hy2 := norm_sq_add_norm_sq hij y
    have hsq : ‖(x : EuclideanSpace ℂ (Fin 2)) j‖ ^ 2 = ‖(y : EuclideanSpace ℂ (Fin 2)) j‖ ^ 2 := by
      linear_combination (‖(y : EuclideanSpace ℂ (Fin 2)) j‖ ^ 2) * hx2 -
        (‖(x : EuclideanSpace ℂ (Fin 2)) j‖ ^ 2) * hy2 -
        (‖(x : EuclideanSpace ℂ (Fin 2)) i‖ * ‖(y : EuclideanSpace ℂ (Fin 2)) j‖ +
          ‖(y : EuclideanSpace ℂ (Fin 2)) i‖ * ‖(x : EuclideanSpace ℂ (Fin 2)) j‖) * hd
    have hρ : ‖(x : EuclideanSpace ℂ (Fin 2)) j‖ = ‖(y : EuclideanSpace ℂ (Fin 2)) j‖ :=
      (pow_left_inj₀ hxj.le hyj.le two_ne_zero).1 hsq
    -- The ratio of the core coordinates is an `m`-th root of unity `ω`.
    set ω := coreCoord j x / coreCoord j y with hωdef
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
        rw [← mul_pow, mul_conj_eq_one hω1, one_pow]
      rw [← h1']
      linear_combination (-discCoord i j x) * hωc
    obtain ⟨b, hb⟩ := exists_toCircle_eq m hωm
    refine (mk_eq_mk_iff m ℓ x y).2 ⟨Multiplicative.ofAdd (((ℓ j)⁻¹ : (ZMod m)ˣ) * b), ?_⟩
    ext k
    rw [lensRotation_apply, toAdd_ofAdd]
    rcases hk k with rfl | rfl
    · rw [← toCircle_pow_twist, Units.mul_inv_cancel_left, Circle.coe_pow, hb]
      rw [discCoord, discCoord, hρ, ← mul_div_assoc] at hdisc
      exact ((div_left_inj' hyj').1 hdisc).symm
    · rw [Units.mul_inv_cancel_left, hb]
      rw [coreCoord, coreCoord, hρ, ← mul_div_assoc] at hcore
      exact ((div_left_inj' hyj').1 hcore).symm
  · intro h
    obtain ⟨a, ha⟩ := (mk_eq_mk_iff m ℓ x y).1 h
    have hxk (k : Fin 2) : (x : EuclideanSpace ℂ (Fin 2)) k =
        (ZMod.toCircle ((ℓ k : ZMod m) * a.toAdd) : ℂ) * (y : EuclideanSpace ℂ (Fin 2)) k := by
      rw [← ha, lensRotation_apply]
    have hρ : ‖(x : EuclideanSpace ℂ (Fin 2)) j‖ = ‖(y : EuclideanSpace ℂ (Fin 2)) j‖ := by
      rw [← ha, norm_lensRotation_apply]
    set z : ℂ := (ZMod.toCircle ((ℓ j : ZMod m) * a.toAdd) : ℂ)
    have hz : z ^ c * (starRingEnd ℂ z) ^ c = 1 := by
      rw [← mul_pow, mul_conj_eq_one (Circle.norm_coe _), one_pow]
    have hzm : z ^ m = 1 := by rw [← Circle.coe_pow, toCircle_pow_self, Circle.coe_one]
    have hcore : coreCoord j x = z * coreCoord j y := by
      rw [coreCoord, coreCoord, hρ, hxk j, mul_div_assoc]
    have hdisc : discCoord i j x = z ^ c * discCoord i j y := by
      rw [discCoord, discCoord, hρ, hxk i, ← toCircle_pow_twist, Circle.coe_pow, mul_div_assoc]
    refine Prod.ext (Subtype.ext ?_) (Circle.ext ?_)
    · rw [coe_pieceQuotient_fst, coe_pieceQuotient_fst, hdisc, hcore, map_mul, mul_pow]
      linear_combination (discCoord i j y * (starRingEnd ℂ (coreCoord j y)) ^ c) * hz
    · rw [coe_pieceQuotient_snd, coe_pieceQuotient_snd, hcore, mul_pow, hzm, one_mul]

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
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw1]
    norm_num
  set c := twist m ℓ i j
  set ρ : ℝ := (√(1 + ‖u‖ ^ 2))⁻¹
  have hρ : 0 < ρ := inv_pos.2 (Real.sqrt_pos.2 (by positivity))
  have hρ2 : ρ ^ 2 * (1 + ‖u‖ ^ 2) = 1 := by
    rw [inv_pow, Real.sq_sqrt (by positivity), inv_mul_cancel₀ (by positivity)]
  let z : EuclideanSpace ℂ (Fin 2) :=
    WithLp.toLp 2 fun k ↦ if k = i then (ρ : ℂ) * (u * w ^ c) else (ρ : ℂ) * w
  have hzi : z i = (ρ : ℂ) * (u * w ^ c) := by simp [z]
  have hzj : z j = (ρ : ℂ) * w := by simp [z, hij.symm]
  have hnzi : ‖z i‖ = ρ * ‖u‖ := by
    rw [hzi, norm_mul, norm_mul, norm_pow, hw1, one_pow, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hρ.le]
  have hnzj : ‖z j‖ = ρ := by
    rw [hzj, norm_mul, hw1, mul_one, Complex.norm_real, Real.norm_of_nonneg hρ.le]
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
  have hcore : coreCoord j ⟨z, hz⟩ = w := by
    rw [coreCoord, hnzj, hzj, mul_div_cancel_left₀ _ hρ']
  refine ⟨⟨⟨z, hz⟩, hzp⟩, Prod.ext (Subtype.ext ?_) (Circle.ext ?_)⟩
  · rw [coe_pieceQuotient_fst]
    dsimp only
    rw [hcore, discCoord, hzi, hnzj, mul_div_cancel_left₀ _ hρ', mul_assoc, ← mul_pow, hwc,
      one_pow, mul_one]
  · rw [coe_pieceQuotient_snd]
    dsimp only
    rw [hcore, hw]

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

/-- The real linear isometry `ℂ² ≃ WithLp 2 (ℂ × ℂ)` reading off the two coordinates. -/
private def finTwoEquivProd : EuclideanSpace ℂ (Fin 2) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℂ) where
  toFun x := WithLp.toLp 2 (x 0, x 1)
  invFun p := WithLp.toLp 2 ![p.fst, p.snd]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    ext k
    fin_cases k <;> rfl
  right_inv _ := rfl
  norm_map' x := by
    rw [WithLp.prod_norm_eq_of_L2, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    rfl

/-- The genus-one Heegaard splitting of the unit sphere of `ℂ²` into the solid tori `‖x 0‖ ≤ ‖x 1‖`
and `‖x 1‖ ≤ ‖x 0‖`, transported from `TauCeti.cliffordHeegaardSplitting`. -/
private def sphereHeegaardSplitting : HeegaardSplitting (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :=
  cliffordHeegaardSplitting.transHomeomorph
    (finTwoEquivProd.unitSphereIsometryEquiv.toHomeomorph.symm)

private theorem sphereHeegaardSplitting_left : sphereHeegaardSplitting.left = piece 0 1 := by
  ext x
  rw [sphereHeegaardSplitting, HeegaardSplitting.transHomeomorph_left, Homeomorph.image_symm,
    mem_preimage, IsometryEquiv.coe_toHomeomorph, cliffordHeegaardSplitting_left, mem_ofPred_eq,
    LinearIsometryEquiv.coe_unitSphereIsometryEquiv_apply]
  rfl

private theorem sphereHeegaardSplitting_right : sphereHeegaardSplitting.right = piece 1 0 := by
  ext x
  rw [sphereHeegaardSplitting, HeegaardSplitting.transHomeomorph_right, Homeomorph.image_symm,
    mem_preimage, IsometryEquiv.coe_toHomeomorph, cliffordHeegaardSplitting_right, mem_ofPred_eq,
    LinearIsometryEquiv.coe_unitSphereIsometryEquiv_apply]
  rfl

/-- The projection from the sphere to a lens space is an open quotient map. -/
theorem isOpenQuotientMap_mk {k : ℕ} (ℓ : Fin (k + 1) → (ZMod m)ˣ) :
    IsOpenQuotientMap (mk m ℓ) := by
  rw [mk_def]
  exact MulAction.isOpenQuotientMap_quotientMk

/-- **The genus-one Heegaard splitting of a lens space.** The lens space `L(m; ℓ₀, ℓ₁)` is the
union of the images of the solid tori `‖z‖ ≤ ‖w‖` and `‖w‖ ≤ ‖z‖` of the unit sphere of `ℂ²`,
which are solid tori meeting along the image of the Clifford torus `‖z‖ = ‖w‖`. -/
def heegaardSplitting : HeegaardSplitting (LensSpace m ℓ) :=
  sphereHeegaardSplitting.ofIsOpenQuotientMap (isOpenQuotientMap_mk m ℓ)
    (by rw [sphereHeegaardSplitting_left]; exact preimage_image_piece m ℓ 0 1)
    (by rw [sphereHeegaardSplitting_right]; exact preimage_image_piece m ℓ 1 0) 1
    (by rw [sphereHeegaardSplitting_left]; exact nonempty_homeomorph_image_piece m ℓ (by decide))
    (by rw [sphereHeegaardSplitting_right]; exact nonempty_homeomorph_image_piece m ℓ (by decide))

@[simp] theorem heegaardSplitting_genus : (heegaardSplitting m ℓ).genus = 1 := (rfl)

theorem heegaardSplitting_left :
    (heegaardSplitting m ℓ).left =
      mk m ℓ '' {x | ‖(x : EuclideanSpace ℂ (Fin 2)) 0‖ ≤ ‖(x : EuclideanSpace ℂ (Fin 2)) 1‖} := by
  rw [heegaardSplitting, HeegaardSplitting.ofIsOpenQuotientMap_left, sphereHeegaardSplitting_left]
  rfl

theorem heegaardSplitting_right :
    (heegaardSplitting m ℓ).right =
      mk m ℓ '' {x | ‖(x : EuclideanSpace ℂ (Fin 2)) 1‖ ≤ ‖(x : EuclideanSpace ℂ (Fin 2)) 0‖} := by
  rw [heegaardSplitting, HeegaardSplitting.ofIsOpenQuotientMap_right,
    sphereHeegaardSplitting_right]
  rfl

instance : Nonempty (HeegaardSplitting (LensSpace m ℓ)) := ⟨heegaardSplitting m ℓ⟩

/-- A lens space `L(m; ℓ₀, ℓ₁)` has Heegaard genus at most one. -/
theorem heegaardGenus_le_one : heegaardGenus (LensSpace m ℓ) ≤ 1 :=
  heegaardGenus_le (heegaardSplitting m ℓ)

/-- The fundamental group of a lens space `L(m; ℓ₀, ℓ₁)` is finitely generated. -/
instance fg_fundamentalGroup (x : LensSpace m ℓ) : Group.FG (FundamentalGroup (LensSpace m ℓ) x) :=
  (heegaardSplitting m ℓ).fg_fundamentalGroup (E := EuclideanSpace ℝ (Fin 3)) (by simp) x

/-- **A lens space `L(m; ℓ₀, ℓ₁)` with `m ≠ 1` has Heegaard genus one.** It has a splitting of
genus one, and none of genus zero, since its fundamental group `ℤ/m` is nontrivial while its rank is
at most the Heegaard genus. -/
theorem heegaardGenus_eq_one (hm : m ≠ 1) : heegaardGenus (LensSpace m ℓ) = 1 := by
  refine le_antisymm (heegaardGenus_le_one m ℓ) ?_
  let x : LensSpace m ℓ := Classical.arbitrary _
  have := nontrivial_fundamentalGroup m ℓ le_rfl hm x
  have h := rank_fundamentalGroup_le_heegaardGenus (E := EuclideanSpace ℝ (Fin 3)) (by simp) x
  have h0 : Group.rank (FundamentalGroup (LensSpace m ℓ) x) ≠ 0 := by
    rw [Ne, Group.rank_eq_zero_iff]
    exact not_subsingleton _
  omega

/-- **A lens space satisfies Waldhausen's equation**: for `m ≠ 1`, the Heegaard genus of
`L(m; ℓ₀, ℓ₁)` equals the rank of its fundamental group, both being one. -/
theorem heegaardGenus_eq_rank (hm : m ≠ 1) (x : LensSpace m ℓ) :
    heegaardGenus (LensSpace m ℓ) = Group.rank (FundamentalGroup (LensSpace m ℓ) x) := by
  have := nontrivial_fundamentalGroup m ℓ le_rfl hm x
  have h := rank_fundamentalGroup_le_heegaardGenus (E := EuclideanSpace ℝ (Fin 3)) (by simp) x
  have h0 : Group.rank (FundamentalGroup (LensSpace m ℓ) x) ≠ 0 := by
    rw [Ne, Group.rank_eq_zero_iff]
    exact not_subsingleton _
  rw [heegaardGenus_eq_one m ℓ hm] at h ⊢
  omega

end LensSpace

end TauCeti
