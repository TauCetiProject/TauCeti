/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basic
public import TauCeti.FieldTheory.FunctionField.Divisor.Conorm
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Unramified
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
public import TauCeti.FieldTheory.RatFunc.Map
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
with ramification index one and relative degree `[k' : k]`, and the conorm of the place is that
single place.

## Main results

* `TauCeti.constantCompositum_eq_top_of_X_mem`: a compositum `F · k'` inside `k'(X)` containing
  `X` is all of `k'(X)`.
* `TauCeti.constantCompositum_ratFunc_eq_top`: `k'(X)` is the compositum of `k(X)` and `k'`.
* `TauCeti.constantCompositum_adjoin_simple_ratFunc_eq_top`: if `z` generates `E` over `k'(X)`,
  then `E` is the compositum of `k(X)(z)` and `k'`.
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
* `TauCeti.Place.relativeDegree_adicOfIrreducible_X_sub_C_algebraMap`: at that place
  `f = [k' : k]`, since the residue extension is `k' / k`.
* `TauCeti.Place.isUnramified_adicOfIrreducible_X_sub_C_iff`: the place of `X - c` in `k(X)` is
  unramified in `k'(X)` exactly when `k' / k` is separable.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section 3.6.
-/

public section

open Polynomial

namespace TauCeti

variable {k k' : Type*} [Field k] [Field k']

/-- **A compositum with `k'` containing `X` is all of `k'(X)`**: for any field `F` inside `k'(X)`,
if `X` lies in `F · k'`, then `F · k' = k'(X)`. -/
theorem constantCompositum_eq_top_of_X_mem {F : Type*} [Field F] [Algebra F (RatFunc k')]
    (hX : (RatFunc.X : RatFunc k') ∈ constantCompositum F k' (RatFunc k')) :
    constantCompositum F k' (RatFunc k') = ⊤ := by
  set K := constantCompositum F k' (RatFunc k')
  -- `K` contains the constants `k'`, so it is an intermediate field of `k'(X) / k'`; it contains
  -- `X`, which generates `k'(X)` over `k'`.
  let E : IntermediateField k' (RatFunc k') :=
    { K.toSubfield with
      algebraMap_mem' := algebraMap_mem_constantCompositum F k' (RatFunc k') }
  have hE : E = ⊤ := eq_top_iff.mpr <|
    RatFunc.adjoin_X.symm.le.trans (IntermediateField.adjoin_simple_le_iff.mpr hX)
  exact eq_top_iff.mpr fun f _ ↦ (hE ▸ IntermediateField.mem_top : f ∈ E)

/-- **`k'(X)` is the compositum of `k(X)` with the constants `k'`**, for any `k(X)`-algebra
structure on `k'(X)` sending `X` to `X`. -/
theorem constantCompositum_ratFunc_eq_top [Algebra (RatFunc k) (RatFunc k')]
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) :
    constantCompositum (RatFunc k) k' (RatFunc k') = ⊤ :=
  constantCompositum_eq_top_of_X_mem (hX ▸ IntermediateField.algebraMap_mem _ RatFunc.X)

section AdjoinSimple

open _root_.IntermediateField

variable {E : Type*} [Field E] [Algebra (RatFunc k) (RatFunc k')] [Algebra (RatFunc k') E]
  [Algebra (RatFunc k) E] [IsScalarTower (RatFunc k) (RatFunc k') E] [Algebra k' E]
  [IsScalarTower k' (RatFunc k') E]

/-- **A simple extension descended to `k(X)` is a model.** If `z` generates `E` over `k'(X)`, then
the compositum of `k(X)(z)` with the constants `k'` is all of `E`, for any `k(X)`-algebra
structure on `k'(X)` sending `X` to `X`. -/
theorem constantCompositum_adjoin_simple_ratFunc_eq_top
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) {z : E}
    (hgen : (RatFunc k')⟮z⟯ = ⊤) :
    constantCompositum (RatFunc k)⟮z⟯ k' E = ⊤ := by
  set L := constantCompositum (RatFunc k)⟮z⟯ k' E
  have hsub : ∀ x ∈ (RatFunc k)⟮z⟯, (x : E) ∈ L.toSubfield := fun x hx ↦ by
    simpa using L.algebraMap_mem ⟨x, hx⟩
  -- The rational functions over `k'` whose images lie in `L` form an intermediate field of
  -- `k'(X) / k'`. It contains `X`, so it is all of `k'(X)`.
  let M := (L.toSubfield.comap (algebraMap (RatFunc k') E)).toIntermediateField (K := k')
    fun c ↦ by
      rw [Subfield.mem_comap, ← IsScalarTower.algebraMap_apply]
      exact algebraMap_mem_constantCompositum _ k' E c
  have hXM : (RatFunc.X : RatFunc k') ∈ M.toSubfield := by
    rw [Subfield.toIntermediateField_toSubfield, Subfield.mem_comap, ← hX,
      ← IsScalarTower.algebraMap_apply]
    exact hsub _ (IntermediateField.algebraMap_mem _ _)
  have hM : M = ⊤ :=
    eq_top_iff.mpr <| _root_.RatFunc.adjoin_X.symm.le.trans (adjoin_simple_le_iff.mpr hXM)
  have hkt (f : RatFunc k') : algebraMap (RatFunc k') E f ∈ L.toSubfield := by
    have hf : f ∈ M.toSubfield := (mem_toSubfield M f).mpr (hM ▸ mem_top)
    rwa [Subfield.toIntermediateField_toSubfield, Subfield.mem_comap] at hf
  -- So `L` is an intermediate field of `E / k'(X)`, and it contains the generator `z`.
  let N := L.toSubfield.toIntermediateField hkt
  have hzN : z ∈ N.toSubfield := by
    rw [Subfield.toIntermediateField_toSubfield]
    exact hsub _ (mem_adjoin_simple_self _ z)
  have hN : N = ⊤ := eq_top_iff.mpr <| hgen.symm.le.trans (adjoin_simple_le_iff.mpr hzN)
  refine eq_top_iff.mpr fun x _ ↦ ?_
  have hx : x ∈ N.toSubfield := (mem_toSubfield N x).mpr (hN ▸ mem_top)
  rwa [Subfield.toIntermediateField_toSubfield, mem_toSubfield] at hx

end AdjoinSimple

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

/-- At the finite place of `q'`, the order of a polynomial `q` over `k` is the
multiplicity of `q'` in `q`, and it is also `e` times the order of `q` at the place below. -/
private theorem multiplicity_map_eq_ramificationIdx_mul_ord
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) {q' : k'[X]}
    (hq' : Irreducible q') {q : k[X]} :
    (multiplicity q' (q.map (algebraMap k k')) : ℤ) =
      ramificationIdx (RatFunc k) (adicOfIrreducible hq') *
        ((adicOfIrreducible hq').restrict k (RatFunc k)).ord (algebraMap k[X] (RatFunc k) q) := by
  rw [← ord_algebraMap_restrict, algebraMap_ratFunc_algebraMap_polynomial hX,
    ord_adicOfIrreducible_algebraMap hq']

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
  have h := multiplicity_map_eq_ramificationIdx_mul_ord hX hq' (q := q)
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
  have h := multiplicity_map_eq_ramificationIdx_mul_ord hX hq' (q := q)
  rw [(restrict_adicOfIrreducible_eq_iff hX hq' hq).mpr hdvd,
    ord_adicOfIrreducible_algebraMap_irreducible hq hq, ite_eq_left (Associated.refl _)] at h
  omega

/-! ### Rational finite places -/

/-- The place of `X - c` in `k'(X)`, for `c ∈ k`, lies over the place of `X - c` in `k(X)`. -/
@[simp]
theorem restrict_adicOfIrreducible_X_sub_C_algebraMap
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) (c : k) :
    (adicOfIrreducible (irreducible_X_sub_C (algebraMap k k' c))).restrict k (RatFunc k) =
      adicOfIrreducible (irreducible_X_sub_C c) :=
  (restrict_adicOfIrreducible_eq_iff hX _ _).mpr (by simp)

/-- **Over a rational finite place there is only one place**: for `c ∈ k`, the place of `X - c`
in `k'(X)` is the only place over the place of `X - c` in `k(X)`. -/
@[simp]
theorem restrict_eq_adicOfIrreducible_X_sub_C_iff
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) (c : k)
    (Q : Place k' (RatFunc k')) :
    Q.restrict k (RatFunc k) = adicOfIrreducible (irreducible_X_sub_C c) ↔
      Q = adicOfIrreducible (irreducible_X_sub_C (algebraMap k k' c)) := by
  rw [restrict_eq_adicOfIrreducible_iff hX]
  constructor
  · rintro ⟨q', hq', hdvd, rfl⟩
    rw [Polynomial.map_sub, map_X, map_C] at hdvd
    exact (adicOfIrreducible_eq_adicOfIrreducible_iff hq' (irreducible_X_sub_C _)).mpr
      (hq'.associated_of_dvd (irreducible_X_sub_C _) hdvd)
  · rintro rfl
    exact ⟨_, irreducible_X_sub_C _, by simp, rfl⟩

/-- **A rational finite place has ramification index one in `k'(X) / k(X)`**: for `c ∈ k`,
`e = 1` at the place of `X - c` in `k'(X)`. -/
@[simp]
theorem ramificationIdx_adicOfIrreducible_X_sub_C_algebraMap
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) (c : k) :
    ramificationIdx (RatFunc k) (adicOfIrreducible (irreducible_X_sub_C (algebraMap k k' c))) =
      1 := by
  rw [ramificationIdx_adicOfIrreducible_eq_multiplicity hX (irreducible_X_sub_C _)
    (irreducible_X_sub_C c) (by simp), Polynomial.map_sub, map_X, map_C,
    multiplicity_self (.of_not_isUnit (not_isUnit_X_sub_C _) (X_sub_C_ne_zero _))]

/-- **A rational finite place has relative degree `[k' : k]` in `k'(X) / k(X)`**: for `c ∈ k`,
the place of `X - c` in `k'(X)` and the place below it are both rational, so the residue extension
is `k' / k`. -/
@[simp]
theorem relativeDegree_adicOfIrreducible_X_sub_C_algebraMap
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) (c : k) :
    relativeDegree k (RatFunc k) (adicOfIrreducible (irreducible_X_sub_C (algebraMap k k' c))) =
      Module.finrank k k' := by
  have h := finrank_mul_degree_eq_relativeDegree_mul_degree_restrict k (RatFunc k)
    (adicOfIrreducible (irreducible_X_sub_C (algebraMap k k' c)))
  rwa [restrict_adicOfIrreducible_X_sub_C_algebraMap hX, degree_adicOfIrreducible_X_sub_C,
    degree_adicOfIrreducible_X_sub_C, mul_one, mul_one, eq_comm] at h

/-- **A rational finite place of `k(X)` is unramified in `k'(X)` exactly when `k' / k` is
separable**, when `k(X)` is embedded in `k'(X)` by `X ↦ X`. For `c ∈ k`, the only place above the
place of `X - c` is the place of `X - c` in `k'(X)`, with ramification index one; both places are
rational, so the residue extension is `k' / k`. -/
@[simp]
theorem isUnramified_adicOfIrreducible_X_sub_C_iff
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) (c : k) :
    (adicOfIrreducible (irreducible_X_sub_C c)).IsUnramified (k' := k') (F' := RatFunc k') ↔
      Algebra.IsSeparable k k' := by
  set Q := adicOfIrreducible (irreducible_X_sub_C (algebraMap k k' c))
  have hQ := restrict_adicOfIrreducible_X_sub_C_algebraMap hX c
  have hsep := isSeparable_residueField_iff_of_degree_eq_one Q
    (degree_adicOfIrreducible_X_sub_C _) (hQ ▸ degree_adicOfIrreducible_X_sub_C c)
  refine ⟨fun h ↦ hsep.mp (h.isSeparable hQ), fun h ↦
    (isUnramified_iff _).mpr ⟨⟨Q, hQ⟩, fun Q' hQ' ↦ ?_⟩⟩
  obtain rfl := (restrict_eq_adicOfIrreducible_X_sub_C_iff hX c Q').mp hQ'
  exact ⟨ramificationIdx_adicOfIrreducible_X_sub_C_algebraMap hX c, hsep.mpr h⟩

/-- **The conorm of a rational finite place is a single place**: for `c ∈ k`, the conorm of the
place of `X - c` in `k(X)` is the place of `X - c` in `k'(X)`. -/
@[simp]
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
