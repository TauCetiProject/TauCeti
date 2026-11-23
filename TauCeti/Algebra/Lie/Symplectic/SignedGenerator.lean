/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Matrix.Single
public import TauCeti.Algebra.Lie.Symplectic.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Molev's signed generators of the symplectic Lie algebra

Molev's construction of Gelfand-Tsetlin bases for `sp₂ᵣ` indexes the coordinates of the
standard module by the signed integers `-r, …, -1, 1, …, r` and works with the generators
`F_ij = E_ij - sgn(i) sgn(j) E_(-j,-i)`. This file translates that convention into the native
coordinates of `LieAlgebra.Symplectic.sp`, on `(l ⊕ l) → R` with form `Matrix.J`, and proves the
facts about the generators that the construction relies on.

On native coordinates, `Sum.swap` plays the role of `i ↦ -i`, and the sign of a coordinate is
`-1` on the `e`-coordinates `inl i` and `1` on the `f`-coordinates `inr i`
(`TauCeti.Symplectic.coordSign`). With these, `F_ab = E_ab - sgn(a) sgn(b) E_(b', a')`
makes sense for any index type `l` and is `TauCeti.LieAlgebra.Symplectic.spGenerator R a b`. It lies
in `sp l R`, satisfies `F_(b', a') = -sgn(a) sgn(b) F_ab`, and the generators satisfy Molev's
commutation relations

`⁅F_ab, F_cd⁆ = δ_bc F_ad - δ_ad F_cb - θ_ab δ_(c, a') F_(b', d) + θ_ab δ_(d, b') F_(c, a')`,

with `θ_ab = sgn(a) sgn(b)`. The proof writes `F_ab = E_ab + J E_abᵀ J` as the symmetrization of a
matrix unit under the involution `X ↦ J Xᵀ J`, whose fixed points form `sp l R`. In particular the
diagonal generators `F_aa = E_aa - E_(a', a')` are diagonal matrices and `ad F_aa` multiplies each
`F_cd` by the scalar `δ_ca - δ_da - δ_(c, a') + δ_(d, a')`. The form itself reads `J a b = sgn(a)`
when `b = a'` and `0` otherwise (`Matrix.J_apply_eq_ite`).

For `l = Fin r`, the signed label `TauCeti.LieAlgebra.Symplectic.signedIndex` identifies the
signed index `-i` with `e_(r + 1 - i)` and `+i` with `f_(r + 1 - i)`, that is `inl k ↦ k - r`
and `inr k ↦ r - k`. It is a bijection onto the nonzero integers of absolute value at most `r`,
sends `Sum.swap` to negation and `coordSign` to the sign, and lists the native coordinates in the
order `e₁, …, e_r, f_r, …, f₁`. The signed indices `∓r` are the first hyperbolic plane `e₁, f₁`,
and on the remaining coordinates the rank `r` labels are the rank `r - 1` labels moved past that
plane by `Fin.succ`. In this order Molev's raising generators `F_ij` with `i < j` are strictly
upper triangular, and the diagonal generator at the signed index `i > 0` is
`E_(f_(r+1-i), f_(r+1-i)) - E_(e_(r+1-i), e_(r+1-i))`.

## Main definitions

* `TauCeti.LieAlgebra.Symplectic.spGenerator`: the generator `F_ab` in native coordinates.
* `TauCeti.LieAlgebra.Symplectic.signedIndex`: Molev's signed label of a native coordinate.

## Main results

* `TauCeti.LieAlgebra.Symplectic.spGenerator_mem_sp`: the generators lie in `sp l R`.
* `TauCeti.LieAlgebra.Symplectic.spGenerator_swap_swap`: `F_(b', a') = -θ_ab F_ab`.
* `TauCeti.LieAlgebra.Symplectic.spGenerator_eq_add_J_mul_transpose_mul_J`:
  `F_ab = E_ab + J E_abᵀ J`.
* `TauCeti.LieAlgebra.Symplectic.lie_spGenerator_spGenerator`: Molev's commutation relations.
* `TauCeti.LieAlgebra.Symplectic.lie_spGenerator_self`: the weight of `F_cd` under `F_aa`.
* `TauCeti.LieAlgebra.Symplectic.submatrix_spGenerator_map`: the generators are compatible with
  injections of the index types.
* `TauCeti.LieAlgebra.Symplectic.range_signedIndex`: the signed labels are exactly the nonzero
  integers of absolute value at most `r`.
* `TauCeti.LieAlgebra.Symplectic.spGenerator_eq_single_sub_single`: in signed indices,
  `F_ij = E_ij - sgn(i) sgn(j) E_(-j, -i)`.
* `TauCeti.LieAlgebra.Symplectic.signedIndex_map_succ`: the signed labels are compatible with the
  inclusion of the last `r` hyperbolic planes in the first `r + 1`.
* `TauCeti.LieAlgebra.Symplectic.spGenerator_apply_eq_zero_of_signedIndex_le`: generators `F_ij`
  with `i < j` are strictly upper triangular in the signed order.

## References

* A. I. Molev, *Gelfand-Tsetlin bases for classical Lie algebras*, in *Handbook of Algebra*,
  Vol. 4, Elsevier (2006); arXiv:math/0211289, §3.1.
-/

public section

open Matrix LieAlgebra.Symplectic TauCeti.Symplectic

namespace TauCeti.LieAlgebra.Symplectic

/-! ### The generators `F_ab` -/

section Generator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {l : Type*} [DecidableEq l] {R : Type*} [CommRing R]

/-- **Molev's generator `F_ab = E_ab - sgn(a) sgn(b) E_(b', a')`** of the symplectic Lie algebra,
in native coordinates: `b'` and `a'` are the coordinates paired with `b` and `a`, and the signs are
those of `TauCeti.Symplectic.coordSign`. -/
def spGenerator (R : Type*) [CommRing R] (a b : l ⊕ l) : Matrix (l ⊕ l) (l ⊕ l) R :=
  single a b 1 - single b.swap a.swap ((coordSign a * coordSign b : ℤ) : R)

theorem spGenerator_def (a b : l ⊕ l) :
    spGenerator R a b =
      single a b (1 : R) - single b.swap a.swap ((coordSign a * coordSign b : ℤ) : R) :=
  (rfl)

/-- **The generators are symplectic**: `F_ab ∈ sp l R`. -/
theorem spGenerator_mem_sp [Fintype l] (a b : l ⊕ l) :
    spGenerator R a b ∈ sp l R := by
  rw [mem_symplecticLieAlgebra_iff]
  rcases a with i | i <;> rcases b with j | j <;>
    refine ⟨fun x y => ?_, fun x y => ?_, fun x y => ?_⟩ <;>
    simp only [spGenerator, Matrix.sub_apply, single_apply, Sum.swap_inl, Sum.swap_inr,
      coordSign_inl, coordSign_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and,
      and_false] <;>
    grind

/-- **The relation `F_(b', a') = -θ_ab F_ab`** between the generators at two pairs of indices
exchanged by `i ↦ -i`, with `θ_ab = sgn(a) sgn(b)`. -/
theorem spGenerator_swap_swap (a b : l ⊕ l) :
    spGenerator R b.swap a.swap =
      -(((coordSign a * coordSign b : ℤ) : R) • spGenerator R a b) := by
  rcases a with i | i <;> rcases b with j | j <;>
    simp [spGenerator, sub_eq_add_neg, ← single_neg]

/-- A diagonal generator is the difference of the diagonal matrix units at a pair of paired
coordinates: `F_aa = E_aa - E_(a', a')`. -/
theorem spGenerator_self (a : l ⊕ l) :
    spGenerator R a a = single a a (1 : R) - single a.swap a.swap 1 := by
  simp [spGenerator, coordSign_mul_self]

/-- On a pair of paired coordinates, the generator is twice a long root vector:
`F_(a, a') = 2 E_(a, a')`. In characteristic two it vanishes, although `E_(a, a')` is
symplectic. -/
theorem spGenerator_swap_right (a : l ⊕ l) :
    spGenerator R a a.swap = single a a.swap (2 : R) := by
  rcases a with i | i <;>
    simp [spGenerator, sub_eq_add_neg, ← single_neg, ← single_add, one_add_one_eq_two]

/-- **A generator is a symmetrization**: `F_ab = E_ab + J E_abᵀ J`. -/
theorem spGenerator_eq_add_J_mul_transpose_mul_J [Fintype l] (a b : l ⊕ l) :
    spGenerator R a b = single a b 1 + J l R * (single a b (1 : R))ᵀ * J l R := by
  rw [J_mul_transpose_single_mul_J, smul_single, smul_eq_mul, mul_one, spGenerator,
    sub_eq_add_neg]

/-- The symmetrization `LieAlgebra.Symplectic.symmetrize` followed by the inclusion of `sp l R`,
as a linear map of matrices; it sends the matrix unit `E_ab` to the generator `F_ab`. -/
private noncomputable def symmetrizeJ [Fintype l] :
    Matrix (l ⊕ l) (l ⊕ l) R →ₗ[R] Matrix (l ⊕ l) (l ⊕ l) R :=
  (sp l R).incl.toLinearMap ∘ₗ symmetrize

private theorem symmetrizeJ_apply [Fintype l] (X : Matrix (l ⊕ l) (l ⊕ l) R) :
    symmetrizeJ X = X + J l R * Xᵀ * J l R := by
  simp [symmetrizeJ, jConj_apply]

private theorem symmetrizeJ_single [Fintype l] (a b : l ⊕ l) :
    symmetrizeJ (single a b (1 : R)) = spGenerator R a b := by
  rw [symmetrizeJ_apply, spGenerator_eq_add_J_mul_transpose_mul_J]

private theorem lie_symmetrizeJ_symmetrizeJ [Fintype l] (X Y : Matrix (l ⊕ l) (l ⊕ l) R) :
    ⁅symmetrizeJ X, symmetrizeJ Y⁆ = symmetrizeJ (⁅X, Y⁆ + ⁅X, J l R * Yᵀ * J l R⁆) := by
  simp only [symmetrizeJ, LinearMap.comp_apply, LieHom.coe_toLinearMap, ← LieHom.map_lie,
    lie_symmetrize_symmetrize, jConj_apply]

/-- **Molev's commutation relations** for the generators of the symplectic Lie algebra:

`⁅F_ab, F_cd⁆ = δ_bc F_ad - δ_ad F_cb - θ_ab δ_(c, a') F_(b', d) + θ_ab δ_(d, b') F_(c, a')`,

with `θ_ab = sgn(a) sgn(b)`. -/
theorem lie_spGenerator_spGenerator [Fintype l] (a b c d : l ⊕ l) :
    ⁅spGenerator R a b, spGenerator R c d⁆ =
      (if b = c then spGenerator R a d else 0) - (if d = a then spGenerator R c b else 0) -
        (if c = a.swap then ((coordSign a * coordSign b : ℤ) : R) • spGenerator R b.swap d
          else 0) +
        if d = b.swap then ((coordSign a * coordSign b : ℤ) : R) • spGenerator R c a.swap
          else 0 := by
  have hinv : Function.Involutive (@Sum.swap l l) := Sum.swap_swap
  -- Both generators are symmetrizations of matrix units, so their bracket is the symmetrization
  -- of `⁅E_ab, E_cd⁆ - θ_cd ⁅E_ab, E_(d', c')⁆`, which is computed by the matrix-unit rule.
  rw [← symmetrizeJ_single, ← symmetrizeJ_single, lie_symmetrizeJ_symmetrizeJ,
    J_mul_transpose_single_mul_J, lie_neg, lie_smul, lie_single_single, lie_single_single]
  simp only [mul_one, map_add, map_sub, map_neg, map_smul, apply_ite symmetrizeJ, map_zero,
    symmetrizeJ_single, eq_comm (a := b) (b := d.swap), hinv.eq_iff]
  -- It remains to rewrite the last two terms by `F_(y', x') = -θ_xy F_xy`, which costs a square
  -- of a sign.
  have hd : (if d = b.swap then ((coordSign c * coordSign d : ℤ) : R) • spGenerator R a c.swap
      else 0) = -if d = b.swap then ((coordSign a * coordSign b : ℤ) : R) • spGenerator R c a.swap
      else 0 := by
    split_ifs with h
    · subst h
      have hθ : coordSign c * coordSign b.swap * (coordSign c * coordSign a.swap) =
          coordSign a * coordSign b := by
        simp only [coordSign_swap]
        linear_combination (coordSign a * coordSign b) * coordSign_mul_self c
      rw [← hinv a, spGenerator_swap_swap, hinv, smul_neg, smul_smul, ← Int.cast_mul, hθ]
    · rw [neg_zero]
  have hc : (if c = a.swap then ((coordSign c * coordSign d : ℤ) : R) • spGenerator R d.swap b
      else 0) = -if c = a.swap then ((coordSign a * coordSign b : ℤ) : R) •
        spGenerator R b.swap d else 0 := by
    split_ifs with h
    · subst h
      have hθ : coordSign a.swap * coordSign d * (coordSign b.swap * coordSign d) =
          coordSign a * coordSign b := by
        simp only [coordSign_swap]
        linear_combination (coordSign a * coordSign b) * coordSign_mul_self d
      rw [← hinv b, spGenerator_swap_swap, hinv, smul_neg, smul_smul, ← Int.cast_mul, hθ]
    · rw [neg_zero]
  simp only [smul_sub, smul_ite, smul_zero]
  rw [hd, hc]
  abel

/-- **The diagonal generators act on each generator by a weight**: `ad F_aa` multiplies `F_cd` by
the scalar `δ_ca - δ_da - δ_(c, a') + δ_(d, a')`. -/
theorem lie_spGenerator_self [Fintype l] (a c d : l ⊕ l) :
    ⁅spGenerator R a a, spGenerator R c d⁆ =
      ((if c = a then 1 else 0) - (if d = a then 1 else 0) - (if c = a.swap then 1 else 0) +
        if d = a.swap then 1 else 0 : R) • spGenerator R c d := by
  have ha : a.swap ≠ a := by cases a <;> simp
  rw [lie_spGenerator_spGenerator, coordSign_mul_self, Int.cast_one, one_smul, one_smul]
  simp only [eq_comm (a := a) (b := c)]
  -- Of the sixteen cases, those with `c = c'` or `d = d'` are contradictory; in the others both
  -- sides are the same multiple of `F_cd`.
  split_ifs <;> subst_vars <;> first
    | exact absurd ‹_ = Sum.swap _›.symm ha
    | module

/-- Restricting a generator for a larger index type to the coordinates of a smaller one recovers
the generator of the smaller type: the generators are compatible with the inclusions of
standard symplectic spaces given by injections of the index types. -/
theorem submatrix_spGenerator_map {l' : Type*} [DecidableEq l'] {f : l → l'}
    (hf : Function.Injective f) (a b : l ⊕ l) :
    (spGenerator R (Sum.map f f a) (Sum.map f f b)).submatrix
        (Sum.map f f) (Sum.map f f) =
      spGenerator R a b := by
  have hinj : Function.Injective (Sum.map f f) := Sum.map_injective.mpr ⟨hf, hf⟩
  have hcomm (x : l ⊕ l) : (Sum.map f f x).swap = Sum.map f f x.swap := by cases x <;> rfl
  have hsign (x : l ⊕ l) : coordSign (Sum.map f f x) = coordSign x := by cases x <;> simp
  ext x y
  simp only [spGenerator, submatrix_apply, Matrix.sub_apply, single_apply, hcomm, hsign,
    hinj.eq_iff]

end Generator

/-! ### Molev's signed indices -/

section SignedIndex

variable {r : ℕ}

/-- **Molev's signed label of a native coordinate** of the standard symplectic space of rank `r`:
the `e`-coordinate `e_(k + 1) = inl k` has label `k - r` and the `f`-coordinate
`f_(k + 1) = inr k` has label `r - k`. Equivalently, the signed index `-i` is `e_(r + 1 - i)` and
`+i` is `f_(r + 1 - i)`. -/
def signedIndex : Fin r ⊕ Fin r → ℤ :=
  Sum.elim (fun k => (k : ℤ) - r) fun k => r - k

@[simp]
theorem signedIndex_inl (k : Fin r) : signedIndex (Sum.inl k) = (k : ℤ) - r :=
  (rfl)

@[simp]
theorem signedIndex_inr (k : Fin r) : signedIndex (Sum.inr k) = r - (k : ℤ) :=
  (rfl)

theorem signedIndex_injective : Function.Injective (signedIndex (r := r)) := by
  rintro (i | i) (j | j) h <;> simp only [signedIndex_inl, signedIndex_inr] at h
  · exact congrArg Sum.inl (Fin.ext (by omega))
  · omega
  · omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

/-- **The signed labels are the signed indices** `-r, …, -1, 1, …, r`. -/
theorem range_signedIndex :
    Set.range (signedIndex (r := r)) = {i : ℤ | i ≠ 0 ∧ |i| ≤ r} := by
  ext i
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a | a, rfl⟩ <;> simp only [signedIndex_inl, signedIndex_inr] <;>
      constructor <;> [omega; (rw [abs_le]; omega); omega; (rw [abs_le]; omega)]
  · rintro ⟨h0, hi⟩
    rw [abs_le] at hi
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · exact ⟨Sum.inl ⟨(i + r).toNat, by omega⟩, by simp; omega⟩
    · exact ⟨Sum.inr ⟨(r - i).toNat, by omega⟩, by simp; omega⟩

/-- Pairing coordinates is negation of signed indices. -/
@[simp]
theorem signedIndex_swap (a : Fin r ⊕ Fin r) : signedIndex a.swap = -signedIndex a := by
  cases a <;> simp

/-- The sign of a coordinate is the sign of its signed index. -/
@[simp]
theorem sign_signedIndex (a : Fin r ⊕ Fin r) : (signedIndex a).sign = coordSign a := by
  rcases a with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [coordSign_inl]
    exact Int.sign_eq_neg_one_of_neg (by simp; omega)
  · rw [coordSign_inr]
    exact Int.sign_eq_one_of_pos (by simp; omega)

/-- In Molev's signed indices, the generator `F_ij` is `E_ij - sgn(i) sgn(j) E_(-j, -i)`. -/
theorem spGenerator_eq_single_sub_single {R : Type*} [CommRing R] (a b : Fin r ⊕ Fin r) :
    spGenerator R a b =
      single a b (1 : R) -
        single b.swap a.swap (((signedIndex a).sign * (signedIndex b).sign : ℤ) : R) := by
  simp [spGenerator_def]

/-- The signed indices `-(r + 1)` and `r + 1` of rank `r + 1` are the coordinates `e₁` and `f₁`
of the first hyperbolic plane. -/
theorem signedIndex_inl_zero : signedIndex (Sum.inl 0 : Fin (r + 1) ⊕ Fin (r + 1)) = -(r + 1) := by
  simp

/-- See `TauCeti.LieAlgebra.Symplectic.signedIndex_inl_zero`. -/
theorem signedIndex_inr_zero : signedIndex (Sum.inr 0 : Fin (r + 1) ⊕ Fin (r + 1)) = r + 1 := by
  simp

/-- **Removing the signed indices `±(r + 1)`**: the rank `r` signed labels, moved past the first
hyperbolic plane by `Fin.succ`, are the rank `r + 1` signed labels. -/
@[simp]
theorem signedIndex_map_succ (a : Fin r ⊕ Fin r) :
    signedIndex (Sum.map Fin.succ Fin.succ a) = signedIndex a := by
  cases a <;> simp

/-- **The generators `F_ij` with `i < j` are strictly upper triangular** in the signed order: their
entry at `(c, d)` vanishes unless the signed index of `c` is smaller than that of `d`. -/
theorem spGenerator_apply_eq_zero_of_signedIndex_le {R : Type*} [CommRing R]
    {a b : Fin r ⊕ Fin r} (hab : signedIndex a < signedIndex b) {c d : Fin r ⊕ Fin r}
    (hdc : signedIndex d ≤ signedIndex c) :
    spGenerator R a b c d = 0 := by
  have h₁ : ¬(a = c ∧ b = d) := by
    rintro ⟨rfl, rfl⟩
    omega
  have h₂ : ¬(b.swap = c ∧ a.swap = d) := by
    rintro ⟨rfl, rfl⟩
    simp only [signedIndex_swap] at hdc
    omega
  rw [spGenerator, Matrix.sub_apply, single_apply_of_ne (h := h₁), single_apply_of_ne (h := h₂),
    sub_zero]

end SignedIndex

end TauCeti.LieAlgebra.Symplectic
