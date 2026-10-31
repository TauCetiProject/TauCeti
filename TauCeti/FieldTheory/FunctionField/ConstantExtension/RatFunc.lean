/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.LinearFactor
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basic
public import TauCeti.FieldTheory.FunctionField.Divisor.Conorm
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# Constant field extensions of the rational function field

For a field extension `k' / k`, the rational function field `k'(X)` is the constant field
extension `k(X) · k'` of `k(X)`, for any `k(X)`-algebra structure on `k'(X)` sending `X` to `X`.
Such a structure maps a polynomial to the polynomial with the same coefficients read in `k'`.
When `k' / k` is finite, the place at infinity of `k'(X)` is the only place over the place at
infinity of `k(X)`.

The finite places are described by factorization. If `q ∈ k[X]` is irreducible, the places of
`k'(X)` over the finite place of `q` are the finite places of the irreducible factors `q'` of `q`
in `k'[X]`, and the ramification index of the place of `q'` is the multiplicity of `q'` in `q`.
Neither separability of `k' / k` nor of `q` is assumed. When `q` is inseparable this
multiplicity can exceed one: over a field of characteristic `p`, `X ^ p - a` becomes
`(X - a ^ (1 / p)) ^ p` once a `p`-th root of `a` is adjoined. At a rational finite place, the
place of `X - c` for `c ∈ k`, it cannot: the place of `X - c` in `k'(X)` is the only place above,
with ramification index one, and the conorm of the place is that single place.

## Main results

* `TauCeti.constantCompositum_ratFunc_eq_top`: `k'(X)` is the compositum of `k(X)` and `k'`.
* `TauCeti.algebraMap_ratFunc_algebraMap_polynomial`: the image in `k'(X)` of a polynomial over
  `k` is the polynomial with its coefficients mapped to `k'`.
* `TauCeti.Place.restrict_ratFunc_eq_infty_iff`: a place of `k'(X)` lies over the place at
  infinity of `k(X)` exactly when it is the place at infinity of `k'(X)`.
* `TauCeti.Place.restrict_adicOfIrreducible_eq_iff`: the finite place of `q'` lies over the
  finite place of `q` exactly when `q'` divides `q` in `k'[X]`.
* `TauCeti.Place.restrict_eq_adicOfIrreducible_iff`: the places over the finite place of `q` are
  the finite places of the irreducible factors of `q` in `k'[X]`.
* `TauCeti.Place.ramificationIdx_adicOfIrreducible_eq_multiplicity`: the ramification index of
  the place of such a factor is its multiplicity in `q`.
* `TauCeti.Place.restrict_eq_adicOfIrreducible_X_sub_C_iff`,
  `TauCeti.Place.ramificationIdx_adicOfIrreducible_X_sub_C_algebraMap` and
  `TauCeti.Place.conorm_ofPoint_adicOfIrreducible_X_sub_C`: for `c ∈ k`, the place of `X - c` in
  `k'(X)` is the only place over the place of `X - c` in `k(X)`, with `e = 1` and `Con P = Q`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section 3.6.
-/

public section

open Polynomial

namespace TauCeti

variable {k k' : Type*} [Field k] [Field k']

section Polynomial

variable [Algebra k k'] [Algebra (RatFunc k) (RatFunc k')]
variable [IsScalarTower k (RatFunc k) (RatFunc k')]

/-- A `k`-algebra map `k(X) → k'(X)` sending `X` to `X` maps a polynomial over `k` to the same
polynomial with its coefficients read in `k'`. -/
theorem algebraMap_ratFunc_algebraMap_polynomial
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) (f : k[X]) :
    algebraMap (RatFunc k) (RatFunc k') (algebraMap k[X] (RatFunc k) f) =
      algebraMap k'[X] (RatFunc k') (f.map (algebraMap k k')) := by
  rw [← RatFunc.aeval_X_left_eq_algebraMap, ← Polynomial.aeval_algebraMap_apply, hX,
    ← RatFunc.aeval_X_left_eq_algebraMap, Polynomial.aeval_map_algebraMap]

end Polynomial

/-- **`k'(X)` is the compositum of `k(X)` with the constants `k'`**, for any `k(X)`-algebra
structure on `k'(X)` sending `X` to `X`. -/
theorem constantCompositum_ratFunc_eq_top [Algebra (RatFunc k) (RatFunc k')]
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) :
    constantCompositum (RatFunc k) k' (RatFunc k') = ⊤ := by
  set K := constantCompositum (RatFunc k) k' (RatFunc k')
  -- `K` contains the constants `k'`, so it is an intermediate field of `k'(X) / k'`; it contains
  -- `X`, which generates `k'(X)` over `k'`.
  let E : IntermediateField k' (RatFunc k') :=
    { K.toSubfield with
      algebraMap_mem' := algebraMap_mem_constantCompositum (RatFunc k) k' (RatFunc k') }
  have hXE : (RatFunc.X : RatFunc k') ∈ E := hX ▸ K.algebraMap_mem RatFunc.X
  have hE : E = ⊤ := eq_top_iff.mpr <|
    RatFunc.adjoin_X.symm.le.trans (IntermediateField.adjoin_simple_le_iff.mpr hXE)
  exact eq_top_iff.mpr fun f _ ↦ (hE ▸ IntermediateField.mem_top : f ∈ E)

namespace Place

variable [Algebra k k'] [FiniteDimensional k k']
variable [Algebra (RatFunc k) (RatFunc k')] [IsScalarTower k (RatFunc k) (RatFunc k')]

/-- **The place at infinity of `k'(X)` is the only place over the place at infinity of `k(X)`**,
for a finite extension `k' / k` and any `k(X)`-algebra structure on `k'(X)` sending `X` to `X`. -/
@[simp]
theorem restrict_ratFunc_eq_infty_iff
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X)
    (P' : Place k' (RatFunc k')) :
    letI := finiteDimensional_of_constantCompositum_eq_top (k := k)
      (constantCompositum_ratFunc_eq_top hX)
    P'.restrict k (RatFunc k) = infty k ↔ P' = infty k' := by
  let := finiteDimensional_of_constantCompositum_eq_top (k := k)
    (constantCompositum_ratFunc_eq_top hX)
  rw [← X_notMem_integers_iff_eq_infty, ← X_notMem_integers_iff_eq_infty,
    mem_integers_restrict_iff, hX]

end Place

/-! ### The places over a finite place -/

namespace Place

variable [Algebra k k'] [Algebra (RatFunc k) (RatFunc k')]
variable [IsScalarTower k (RatFunc k) (RatFunc k')] [Algebra.IsIntegral (RatFunc k) (RatFunc k')]

/-- At the finite place of `q'`, the order of a nonzero polynomial `q` over `k` is the
multiplicity of `q'` in `q`, and it is also `e` times the order of `q` at the place below. -/
private theorem multiplicity_map_eq_ramificationIdx_mul_ord
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) {q' : k'[X]}
    (hq' : Irreducible q') {q : k[X]} (hq : q ≠ 0) :
    (multiplicity q' (q.map (algebraMap k k')) : ℤ) =
      ramificationIdx (RatFunc k) (adicOfIrreducible hq') *
        ((adicOfIrreducible hq').restrict k (RatFunc k)).ord (algebraMap k[X] (RatFunc k) q) := by
  rw [← ord_algebraMap_restrict, algebraMap_ratFunc_algebraMap_polynomial hX,
    ord_adicOfIrreducible_algebraMap hq' ((Polynomial.map_ne_zero_iff
      (algebraMap k k').injective).mpr hq)]

/-- **A finite place of `k'(X)` lies over a finite place of `k(X)`**: `X` is regular at it. -/
theorem restrict_adicOfIrreducible_ne_infty
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) {q' : k'[X]}
    (hq' : Irreducible q') :
    (adicOfIrreducible hq').restrict k (RatFunc k) ≠ infty k := by
  rw [Ne, ← X_notMem_integers_iff_eq_infty, not_not, mem_integers_restrict_iff, hX]
  exact X_mem_integers_adicOfIrreducible hq'

/-- **The finite place of `q'` lies over the finite place of `q` exactly when `q'` divides `q` in
`k'[X]`**, for irreducible `q ∈ k[X]` and `q' ∈ k'[X]`. -/
theorem restrict_adicOfIrreducible_eq_iff
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) {q' : k'[X]}
    (hq' : Irreducible q') {q : k[X]} (hq : Irreducible q) :
    (adicOfIrreducible hq').restrict k (RatFunc k) = adicOfIrreducible hq ↔
      q' ∣ q.map (algebraMap k k') := by
  classical
  have hfin : FiniteMultiplicity q' (q.map (algebraMap k k')) :=
    .of_not_isUnit hq'.not_isUnit ((Polynomial.map_ne_zero_iff
      (algebraMap k k').injective).mpr hq.ne_zero)
  have h := multiplicity_map_eq_ramificationIdx_mul_ord hX hq' hq.ne_zero
  have he := ramificationIdx_pos (RatFunc k) (adicOfIrreducible hq')
  rw [← multiplicity_ne_zero hfin]
  constructor
  · intro hP
    rw [hP, ord_adicOfIrreducible_algebraMap_irreducible hq hq,
      ite_eq_left (Associated.refl _)] at h
    omega
  · -- The place below is the finite place of some irreducible `r`, at which `q` has positive
    -- order, so `r` and `q` are associated.
    intro hm
    obtain ⟨r, hr, hP⟩ := (eq_infty_or_exists_eq_adicOfIrreducible _).resolve_left
      (restrict_adicOfIrreducible_ne_infty hX hq')
    rw [hP, ord_adicOfIrreducible_algebraMap_irreducible hr hq] at h
    rw [hP, adicOfIrreducible_eq_adicOfIrreducible_iff]
    by_contra hrq
    rw [ite_eq_right hrq] at h
    omega

/-- **The places over the finite place of `q`** are the finite places of the irreducible factors
of `q` in `k'[X]`. -/
theorem restrict_eq_adicOfIrreducible_iff
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) {q : k[X]}
    (hq : Irreducible q) (Q : Place k' (RatFunc k')) :
    Q.restrict k (RatFunc k) = adicOfIrreducible hq ↔
      ∃ (q' : k'[X]) (hq' : Irreducible q'), q' ∣ q.map (algebraMap k k') ∧
        Q = adicOfIrreducible hq' := by
  constructor
  · intro hQ
    obtain ⟨q', hq', rfl⟩ := (eq_infty_or_exists_eq_adicOfIrreducible Q).resolve_left fun h ↦ by
      have hXQ := X_mem_integers_adicOfIrreducible hq
      rw [← hQ, mem_integers_restrict_iff, hX, h] at hXQ
      exact X_notMem_integers_iff_eq_infty.mpr rfl hXQ
    exact ⟨q', hq', (restrict_adicOfIrreducible_eq_iff hX hq' hq).mp hQ, rfl⟩
  · rintro ⟨q', hq', hdvd, rfl⟩
    exact (restrict_adicOfIrreducible_eq_iff hX hq' hq).mpr hdvd

/-- **The ramification index at an irreducible factor is its multiplicity**: if the irreducible
`q' ∈ k'[X]` divides the irreducible `q ∈ k[X]`, then `e` at the finite place of `q'` over the
finite place of `q` is the multiplicity of `q'` in `q`. -/
theorem ramificationIdx_adicOfIrreducible_eq_multiplicity
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) {q' : k'[X]}
    (hq' : Irreducible q') {q : k[X]} (hq : Irreducible q) (hdvd : q' ∣ q.map (algebraMap k k')) :
    ramificationIdx (RatFunc k) (adicOfIrreducible hq') =
      multiplicity q' (q.map (algebraMap k k')) := by
  classical
  have h := multiplicity_map_eq_ramificationIdx_mul_ord hX hq' hq.ne_zero
  rw [(restrict_adicOfIrreducible_eq_iff hX hq' hq).mpr hdvd,
    ord_adicOfIrreducible_algebraMap_irreducible hq hq, ite_eq_left (Associated.refl _)] at h
  omega

/-! ### Rational finite places -/

/-- The place of `X - c` in `k'(X)`, for `c ∈ k`, lies over the place of `X - c` in `k(X)`. -/
theorem restrict_adicOfIrreducible_X_sub_C_algebraMap
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) (c : k) :
    (adicOfIrreducible (irreducible_X_sub_C (algebraMap k k' c))).restrict k (RatFunc k) =
      adicOfIrreducible (irreducible_X_sub_C c) :=
  (restrict_adicOfIrreducible_eq_iff hX _ _).mpr (map_X_sub_C _ c).symm.dvd

/-- **Over a rational finite place there is only one place**: for `c ∈ k`, the place of `X - c`
in `k'(X)` is the only place over the place of `X - c` in `k(X)`. -/
theorem restrict_eq_adicOfIrreducible_X_sub_C_iff
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) (c : k)
    (Q : Place k' (RatFunc k')) :
    Q.restrict k (RatFunc k) = adicOfIrreducible (irreducible_X_sub_C c) ↔
      Q = adicOfIrreducible (irreducible_X_sub_C (algebraMap k k' c)) := by
  rw [restrict_eq_adicOfIrreducible_iff hX]
  constructor
  · rintro ⟨q', hq', hdvd, rfl⟩
    rw [map_X_sub_C] at hdvd
    exact (adicOfIrreducible_eq_adicOfIrreducible_iff hq' (irreducible_X_sub_C _)).mpr
      (hq'.associated_of_dvd (irreducible_X_sub_C _) hdvd)
  · rintro rfl
    exact ⟨_, irreducible_X_sub_C _, (map_X_sub_C _ c).symm.dvd, rfl⟩

/-- **A rational finite place has ramification index one in `k'(X) / k(X)`**: for `c ∈ k`,
`e = 1` at the place of `X - c` in `k'(X)`. -/
theorem ramificationIdx_adicOfIrreducible_X_sub_C_algebraMap
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) (c : k) :
    ramificationIdx (RatFunc k) (adicOfIrreducible (irreducible_X_sub_C (algebraMap k k' c))) =
      1 := by
  rw [ramificationIdx_adicOfIrreducible_eq_multiplicity hX (irreducible_X_sub_C _)
    (irreducible_X_sub_C c) (map_X_sub_C _ c).symm.dvd, map_X_sub_C,
    multiplicity_self (.of_not_isUnit (not_isUnit_X_sub_C _) (X_sub_C_ne_zero _))]

/-- **The conorm of a rational finite place is a single place**: for `c ∈ k`, the conorm of the
place of `X - c` in `k(X)` is the place of `X - c` in `k'(X)`. -/
theorem conorm_ofPoint_adicOfIrreducible_X_sub_C
    [∀ P : Place k (RatFunc k),
      Finite {Q : Place k' (RatFunc k') // Q.restrict k (RatFunc k) = P}]
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) (c : k) :
    Divisor.conorm k' (RatFunc k') (AlgebraicGeometry.WeilDivisor.ofPoint
        (adicOfIrreducible (irreducible_X_sub_C c))) =
      AlgebraicGeometry.WeilDivisor.ofPoint
        (adicOfIrreducible (irreducible_X_sub_C (algebraMap k k' c))) := by
  refine AlgebraicGeometry.WeilDivisor.ext fun Q ↦ ?_
  rw [Divisor.coeff_conorm]
  by_cases hQ : Q = adicOfIrreducible (irreducible_X_sub_C (algebraMap k k' c))
  · rw [hQ, restrict_adicOfIrreducible_X_sub_C_algebraMap hX,
      ramificationIdx_adicOfIrreducible_X_sub_C_algebraMap hX,
      AlgebraicGeometry.WeilDivisor.coeff_ofPoint_self,
      AlgebraicGeometry.WeilDivisor.coeff_ofPoint_self, Nat.cast_one, one_mul]
  · rw [AlgebraicGeometry.WeilDivisor.coeff_ofPoint_of_ne
      (mt (restrict_eq_adicOfIrreducible_X_sub_C_iff hX c Q).mp hQ),
      AlgebraicGeometry.WeilDivisor.coeff_ofPoint_of_ne hQ, mul_zero]

end Place

end TauCeti
