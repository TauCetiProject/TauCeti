/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.ApproxProd
public import TauCeti.NumberTheory.Height.Primitive

/-!
# The affine product of a system of linear forms

Let `K` be a number field, `F` a field extension of `K`, and `S` a finite set of finite places of
`K`, carried as a `Finset` of height one primes of `𝓞 K`, with every infinite place implicitly
present. Fix at each of these places `v` an absolute value `w v` of `F` and linear forms `L v i` on
`F^ι`. The **affine product** of a point `x : ι → K` is

`(∏ v | ∞, (∏ i, w v (L v i x)) ^ mult v) * ∏ v ∈ S, ∏ i, w v (L v i x)`,

`TauCeti.NumberField.affineProd`. It is the approximation product `NumberField.approxProd` with the
local denominators `⨆ j, v (x j)` left out. The `S`-integral form of the Subspace Theorem concerns
the nonzero `x` with coordinates in `S.integer K` and `affineProd S w L x ≤ mulHeight x ^ (-ε)`;
this is the form in which `S`-unit equations, Thue–Mahler equations and decomposable form
equations use it (Bombieri–Gubler, Corollary 7.2.5 and Theorem 7.2.6).

The passage between the two forms is one identity,
`TauCeti.NumberField.affineProd_eq_approxProd_mul`: dropping the local denominators multiplies the
approximation product, taken over all the infinite places and `S`, by the product `P(x)` of the
local sup norms of `x` over these places, once per form. For a nonzero `S`-integral point, `P(x)`
is at least the height (`NumberField.mulHeight_le_prod`), with equality for an `S`-primitive point
(`NumberField.mulHeight_eq_prod_of_isPrimitive`). At `x = 0` with `ι` nonempty, `P(x)` is `0` while
the height is `1`, but there the approximation product vanishes too. Hence every `S`-integral
solution of the affine inequality, zero included, solves the projective inequality
`approxProd … x ≤ mulHeight x ^ (-card ι - ε)` of the Subspace Theorem with the same `ε`, and for
`S`-primitive points the two inequalities are equivalent. Scaling by an `S`-unit changes neither
the affine product nor `S`-primitivity (`Set.IsPrimitive.unit_smul`).

## Main definitions

* `TauCeti.NumberField.affineProd`: the affine product of a point with respect to linear forms at
  the infinite places and the places of `S`.

## Main results

* `TauCeti.NumberField.affineProd_eq_approxProd_mul`: the affine product is the approximation
  product over all the infinite places and `S` times the `card ι`-th power of the product of the
  local sup norms over these places.
* `TauCeti.NumberField.affineProd_eq_approxProd_mul_mulHeight_pow`: for an `S`-primitive point the
  last factor is `mulHeight x ^ card ι`.
* `TauCeti.NumberField.approxProd_mul_mulHeight_pow_le_affineProd` and
  `TauCeti.NumberField.approxProd_le_of_affineProd_le`: for a nonzero point with `S`-integral
  coordinates this factor is at least `mulHeight x ^ card ι`, so the affine inequality implies the
  projective one; both results also hold at `x = 0`, where the approximation product is `0` when
  `ι` is nonempty.
* `TauCeti.NumberField.affineProd_le_iff_approxProd_le`: for an `S`-primitive point the two
  inequalities are equivalent.
* `TauCeti.NumberField.affineProd_smul` and `TauCeti.NumberField.affineProd_units_smul`: scaling
  the point by `c` multiplies the affine product by the `card ι`-th power of the product of the
  absolute values of `c` over the infinite places and `S`, when each `w v` lies over `v`; this
  factor is `1` for an `S`-unit.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Corollary 7.2.5 and Theorem 7.2.6.
-/

public section

open Finset Height IsDedekindDomain Module

namespace TauCeti.NumberField

open _root_.NumberField

variable {K F ι : Type*} [Field K] [Field F] [Algebra K F] [Fintype ι]

section Local

/-- A local factor of the affine product is the corresponding local factor of the approximation
product times the `card ι`-th power of the local sup norm. When the sup norm vanishes the point is
`0`, and both sides are `0` (or `1`, for an empty index type). -/
private theorem prod_apply_eq_prod_div_iSup_mul_pow {G : Type*} [FunLike G K ℝ]
    [MonoidWithZeroHomClass G K ℝ] [NonnegHomClass G K ℝ] (v : G) (w : AbsoluteValue F ℝ)
    (l : ι → Dual F (ι → F)) (x : ι → K) :
    ∏ i, w (l i fun j ↦ algebraMap K F (x j)) =
      (∏ i, w (l i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) *
        (⨆ j, v (x j)) ^ Fintype.card ι := by
  rw [prod_div_distrib, prod_const, card_univ]
  refine (div_mul_cancel_of_imp fun h ↦ ?_).symm
  obtain ⟨hs, hn⟩ := pow_eq_zero_iff'.mp h
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn)
  have hx : x = 0 := funext fun j ↦ (map_eq_zero v).mp <|
    le_antisymm (hs ▸ le_ciSup (Finite.bddAbove_range fun j ↦ v (x j)) j) (apply_nonneg v _)
  have h0 : (fun j ↦ algebraMap K F (x j)) = 0 := funext fun j ↦ by simp [hx]
  exact prod_eq_zero (mem_univ i) (by simp [h0])

/-- Scaling the point by `c` multiplies a local factor of the affine product by `v c ^ card ι`,
when `w` lies over `v`. -/
private theorem prod_apply_smul {v : AbsoluteValue K ℝ} {w : AbsoluteValue F ℝ} [w.LiesOver v]
    (l : ι → Dual F (ι → F)) (c : K) (x : ι → K) :
    ∏ i, w (l i fun j ↦ algebraMap K F ((c • x) j)) =
      (∏ i, w (l i fun j ↦ algebraMap K F (x j))) * v c ^ Fintype.card ι := by
  have h : (fun j ↦ algebraMap K F ((c • x) j)) = algebraMap K F c • fun j ↦ algebraMap K F (x j) :=
    funext fun j ↦ by simp
  simp only [h, map_smul, smul_eq_mul, map_mul, AbsoluteValue.LiesOver.apply_algebraMap v,
    prod_mul_distrib, prod_const, card_univ, mul_comm]

end Local

variable [NumberField K]

/-- The **affine product** of a point `x : ι → K` with respect to linear forms `L v i` with
coefficients in `F`, at all the infinite places of `K` and at the finite places of `S`, each
measured by an absolute value `w v` of `F`: the product over the infinite places `v` of
`(∏ i, w v (L v i x)) ^ mult v`, times the product over `v ∈ S` of `∏ i, w v (L v i x)`, where `x`
is mapped into `F`.

This is the approximation product `NumberField.approxProd` without the local denominators
`⨆ j, v (x j)`. The data `w` and `L` are indexed by the underlying absolute value of a place, and
their values at the other places play no role. -/
noncomputable def affineProd (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (x : ι → K) : ℝ :=
  (∏ v : InfinitePlace K, (∏ i, w v.val (L v.val i fun j ↦ algebraMap K F (x j))) ^ v.mult) *
    ∏ v ∈ S, ∏ i, w (FinitePlace.mk v).val (L (FinitePlace.mk v).val i fun j ↦ algebraMap K F (x j))

theorem affineProd_def (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (x : ι → K) :
    affineProd S w L x =
      (∏ v : InfinitePlace K, (∏ i, w v.val (L v.val i fun j ↦ algebraMap K F (x j))) ^ v.mult) *
        ∏ v ∈ S, ∏ i, w (FinitePlace.mk v).val
          (L (FinitePlace.mk v).val i fun j ↦ algebraMap K F (x j)) := by
  rw [affineProd]

variable {S : Finset (HeightOneSpectrum (𝓞 K))} {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ}
  {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)} {x : ι → K}

/-- The affine product is nonnegative. -/
theorem affineProd_nonneg (x : ι → K) : 0 ≤ affineProd S w L x := by
  rw [affineProd_def]
  exact mul_nonneg (prod_nonneg fun v _ ↦ pow_nonneg (prod_nonneg fun _ _ ↦ apply_nonneg _ _) _)
    (prod_nonneg fun v _ ↦ prod_nonneg fun _ _ ↦ apply_nonneg _ _)

/-- The affine product depends on the forms only at the infinite places and the places of `S`. -/
theorem affineProd_congr {L' : AbsoluteValue K ℝ → ι → Dual F (ι → F)}
    (hInf : ∀ v : InfinitePlace K, L v.val = L' v.val)
    (hFin : ∀ v ∈ S, L (FinitePlace.mk v).val = L' (FinitePlace.mk v).val) (x : ι → K) :
    affineProd S w L x = affineProd S w L' x := by
  simp only [affineProd_def, hInf]
  congr 1
  exact prod_congr rfl fun v hv ↦ by rw [hFin v hv]

/-- **Scaling the point.** When each `w v` lies over `v`, replacing `x` by `c • x` multiplies the
affine product by the `card ι`-th power of `(∏ v | ∞, v c ^ mult v) * ∏ v ∈ S, v c`. This factor
is `1` when `c` is an `S`-unit, by the product formula. -/
theorem affineProd_smul (hwInf : ∀ v : InfinitePlace K, (w v.val).LiesOver v.val)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).val).LiesOver (FinitePlace.mk v).val) (c : K)
    (x : ι → K) :
    affineProd S w L (c • x) =
      ((∏ v : InfinitePlace K, v c ^ v.mult) * ∏ v ∈ S, FinitePlace.mk v c) ^ Fintype.card ι *
        affineProd S w L x := by
  simp only [affineProd_def, InfinitePlace.coe_apply, FinitePlace.coe_apply]
  have hI (v : InfinitePlace K) :=
    have := hwInf v
    prod_apply_smul (v := v.val) (w := w v.val) (L v.val) c x
  have hF (v) (hv : v ∈ S) :=
    have := hwFin v hv
    prod_apply_smul (v := (FinitePlace.mk v).val) (w := w (FinitePlace.mk v).val)
      (L (FinitePlace.mk v).val) c x
  simp only [hI]
  rw [prod_congr rfl hF]
  simp only [mul_pow, prod_mul_distrib, pow_right_comm _ (Fintype.card ι), prod_pow]
  ring

/-- **Invariance under `S`-units.** When each `w v` lies over `v`, the affine product does not
change when the point is scaled by an `S`-unit, by the product formula for `S`-units. -/
theorem affineProd_units_smul (hwInf : ∀ v : InfinitePlace K, (w v.val).LiesOver v.val)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).val).LiesOver (FinitePlace.mk v).val) {u : Kˣ}
    (hu : u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (x : ι → K) :
    affineProd S w L ((u : K) • x) = affineProd S w L x := by
  rw [affineProd_smul hwInf hwFin, prod_abs_eq_one_of_mem_unit S hu, one_pow, one_mul]

variable [DecidableEq (FinitePlace K)]

/-- **The affine product and the approximation product.** The affine product is the approximation
product over all the infinite places and the places of `S`, times the `card ι`-th power of the
product of the local sup norms of `x` over these places: dropping the local denominators
multiplies by this product once per form. No hypothesis on `x` is needed; at `x = 0` with `ι`
nonempty both sides are `0`. -/
theorem affineProd_eq_approxProd_mul (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (x : ι → K) :
    affineProd S w L x = approxProd univ (S.image FinitePlace.mk) w L x *
      ((∏ v : InfinitePlace K, (⨆ j, v (x j)) ^ v.mult) *
        ∏ v ∈ S, ⨆ j, FinitePlace.mk v (x j)) ^ Fintype.card ι := by
  rw [affineProd_def, approxProd_def, prod_image fun _ _ _ _ h ↦ FinitePlace.mk_injective h]
  simp only [fun v : InfinitePlace K ↦ prod_apply_eq_prod_div_iSup_mul_pow v (w v.val) (L v.val) x,
    fun v : HeightOneSpectrum (𝓞 K) ↦ prod_apply_eq_prod_div_iSup_mul_pow (FinitePlace.mk v)
      (w (FinitePlace.mk v).val) (L (FinitePlace.mk v).val) x]
  simp only [mul_pow, prod_mul_distrib, pow_right_comm _ (Fintype.card ι), prod_pow]
  ring

/-- **The affine product of an `S`-primitive point.** For a point whose coordinates are
`S`-integers generating the unit ideal of `S.integer K`, the affine product is the approximation
product over all the infinite places and the places of `S`, times `mulHeight x ^ card ι`. -/
theorem affineProd_eq_approxProd_mul_mulHeight_pow (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hx : (S : Set (HeightOneSpectrum (𝓞 K))).IsPrimitive x) :
    affineProd S w L x =
      approxProd univ (S.image FinitePlace.mk) w L x * mulHeight x ^ Fintype.card ι := by
  rw [affineProd_eq_approxProd_mul, mulHeight_eq_prod_of_isPrimitive S hx]

/-- **The `S`-integral inequality implies the projective one, multiplicatively.** For a point with
coordinates in `S.integer K`, the approximation product over all the infinite places and the places
of `S`, times `mulHeight x ^ card ι`, is at most the affine product. -/
theorem approxProd_mul_mulHeight_pow_le_affineProd (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hxS : ∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) :
    approxProd univ (S.image FinitePlace.mk) w L x * mulHeight x ^ Fintype.card ι ≤
      affineProd S w L x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases isEmpty_or_nonempty ι with hι | hι
    · simp [affineProd_eq_approxProd_mul]
    -- at `0` every form vanishes, so the factor at any infinite place is `0`
    have h : approxProd univ (S.image FinitePlace.mk) w L 0 = 0 := by
      rw [approxProd_def]
      refine mul_eq_zero_of_left (prod_eq_zero (mem_univ (Classical.arbitrary _)) ?_) _
      simp [InfinitePlace.mult_ne_zero]
    rw [h, zero_mul]
    exact affineProd_nonneg 0
  rw [affineProd_eq_approxProd_mul]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (mulHeight_pos x).le (mulHeight_le_prod S hx hxS) _) (approxProd_nonneg x)

/-- **The `S`-integral form of the inequality of the Subspace Theorem implies the projective form.**
If `x` has coordinates in `S.integer K` and `affineProd S w L x ≤ mulHeight x ^ (-ε)`, then the
approximation product over all the infinite places and the places of `S` is at most
`mulHeight x ^ (-card ι - ε)`. -/
theorem approxProd_le_of_affineProd_le (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    {ε : ℝ} (hxS : ∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K)
    (h : affineProd S w L x ≤ mulHeight x ^ (-ε)) :
    approxProd univ (S.image FinitePlace.mk) w L x ≤
      mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) := by
  have hH := mulHeight_pos x
  rw [sub_eq_add_neg, Real.rpow_add hH, Real.rpow_neg hH.le (Fintype.card ι : ℝ),
    Real.rpow_natCast, ← div_eq_inv_mul, le_div_iff₀ (pow_pos hH _)]
  exact (approxProd_mul_mulHeight_pow_le_affineProd S w L hxS).trans h

/-- **For an `S`-primitive point the two forms of the inequality of the Subspace Theorem agree.**
If the coordinates of `x` are `S`-integers generating the unit ideal of `S.integer K`, then
`affineProd S w L x ≤ mulHeight x ^ (-ε)` exactly when the approximation product over all the
infinite places and the places of `S` is at most `mulHeight x ^ (-card ι - ε)`. -/
theorem affineProd_le_iff_approxProd_le (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    {ε : ℝ} (hx : (S : Set (HeightOneSpectrum (𝓞 K))).IsPrimitive x) :
    affineProd S w L x ≤ mulHeight x ^ (-ε) ↔
      approxProd univ (S.image FinitePlace.mk) w L x ≤
        mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) := by
  have hH := mulHeight_pos x
  rw [sub_eq_add_neg, Real.rpow_add hH, Real.rpow_neg hH.le (Fintype.card ι : ℝ),
    Real.rpow_natCast, ← div_eq_inv_mul, le_div_iff₀ (pow_pos hH _),
    affineProd_eq_approxProd_mul_mulHeight_pow S w L hx]

end TauCeti.NumberField
