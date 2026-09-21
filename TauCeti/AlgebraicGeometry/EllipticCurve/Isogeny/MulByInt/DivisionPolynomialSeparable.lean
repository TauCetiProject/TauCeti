/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Torsion.Roots
-- Proof-only: `[n]` is `n ²`-to-one over an algebraically closed field, the input to the count.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Fiber
-- Proof-only: a polynomial with as many distinct roots as its degree is separable, which is what
-- each of the three counts below ends in.
import TauCeti.FieldTheory.Separable.OfRootCount
-- Proof-only: an even index with nonzero cast keeps `2` nonzero.
import TauCeti.Data.Int.CastNeZero
-- Proof-only: `ΨSqₙ` is nonzero on a nonsingular curve, and vanishes only at torsion. This also
-- carries the degree, evaluation-bridge and algebraic-closure material the count uses.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Coprimality

/-!
# Division polynomials are separable when `n` is invertible

`preΨₙ` has degree `(n ² - 1) / 2` for odd `n` and `(n ² - 4) / 2` for even `n`, and its roots are
the abscissae of the nonzero `n`-torsion points that are not `2`-torsion. Over an algebraically
closed field there are `n ² - 1` of the former and at most three of the latter, and the abscissa map
is two-to-one, so the roots are as numerous as the degree allows: `preΨₙ` has no repeated root.
The same count against `deg ΨSq₂ = 3` separates `Ψ₂Sq`, whose three roots are the abscissae of the
`2`-torsion and are distinct because those points are their own negatives.

Separability is insensitive to base change, so both statements descend from the algebraic closure to
an arbitrary field in which `n` is invertible.

The consequence the torsion theory wants is the last one: the minimal polynomial of the abscissa of
an `n`-torsion point is separable. `ΨSqₙ` itself need not be — it carries the factor `preΨₙ ²`,
which is repeated as soon as `preΨₙ` is not a unit — but a minimal polynomial is irreducible, so it
divides one of the two factors and inherits that factor's separability.

## Main results

* `WeierstrassCurve.separable_preΨ`: `preΨₙ` is separable when `n` is invertible.
* `WeierstrassCurve.separable_Ψ₂Sq`: `Ψ₂Sq` is separable when `2` is invertible.
* `WeierstrassCurve.separable_minpoly_of_aeval_ΨSq_eq_zero`: the minimal polynomial of a root of
  `ΨSqₙ` is separable when `n` is invertible.
* `WeierstrassCurve.separable_minpoly_of_zsmul_eq_zero`: hence so is that of the `x`-coordinate of
  an `n`-torsion point.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4(b) and exercise 3.7.
-/

public section

open Finset Polynomial WeierstrassCurve.Affine TauCeti.Isogeny

namespace WeierstrassCurve

variable {F : Type*} [Field F]

section Torsion

variable [DecidableEq F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

omit [W.IsElliptic] in
/-- A nonzero point killed by an odd `n` has `preΨₙ` vanishing at its abscissa: at odd `n` the
factor `Ψ₂Sq` is absent from `ΨSqₙ`, so `preΨₙ` carries the whole vanishing. -/
private theorem eval_preΨ_eq_zero_of_odd {n : ℤ} (hodd : ¬ Even n) {x y : F}
    (hns : (W⁄F).toAffine.Nonsingular x y) (h : n • (Affine.Point.some x y hns) = 0) :
    ((W⁄F).preΨ n).eval x = 0 := by
  have hsq := (eval_ΨSq_eq_zero_iff_zsmul_eq_zero (W⁄F) hns n).mpr
    (zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero.mpr h)
  simp only [WeierstrassCurve.ΨSq, hodd, ite_false, mul_one, eval_pow] at hsq
  exact pow_eq_zero_iff two_ne_zero |>.mp hsq

omit [W.IsElliptic] in
/-- A point killed by an even `n` but not by `2` has `preΨₙ` vanishing at its abscissa: the other
factor of `ΨSqₙ` is `Ψ₂Sq`, which vanishes only on the `2`-torsion. -/
private theorem eval_preΨ_eq_zero_of_even {n : ℤ} (heven : Even n) {x y : F}
    (hns : (W⁄F).toAffine.Nonsingular x y) (h : n • (Affine.Point.some x y hns) = 0)
    (h2 : (2 : ℤ) • (Affine.Point.some x y hns) ≠ 0) :
    ((W⁄F).preΨ n).eval x = 0 := by
  have hsq := (eval_ΨSq_eq_zero_iff_zsmul_eq_zero (W⁄F) hns n).mpr
    (zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero.mpr h)
  simp only [WeierstrassCurve.ΨSq, heven, ite_true, eval_mul, eval_pow, mul_eq_zero,
    pow_eq_zero_iff (two_ne_zero)] at hsq
  exact hsq.resolve_right fun hΨ₂ ↦ eval_ΨSq_ne_zero_of_zsmul_ne_zero (W⁄F) hns h2
    (by simpa [WeierstrassCurve.ΨSq_two] using hΨ₂)

end Torsion

section IsAlgClosed

variable [IsAlgClosed F]

omit [IsAlgClosed F] in
/-- **At most two points share an abscissa**: a point is determined by its abscissa up to sign. -/
private theorem card_filter_xRep_le_two [DecidableEq F] {V : WeierstrassCurve.Affine F}
    (s : Finset V.Point) (b : Fin 2 → F) : #{P ∈ s | P.xRep = b} ≤ 2 := by
  rcases Finset.eq_empty_or_nonempty {P ∈ s | P.xRep = b} with h | ⟨Q, hQ⟩
  · simp [h]
  · have hsub : {P ∈ s | P.xRep = b} ⊆ {Q, -Q} := by
      intro P hP
      have hb : P.xRep = Q.xRep := by
        rw [(Finset.mem_filter.mp hP).2, (Finset.mem_filter.mp hQ).2]
      rcases Point.eq_or_eq_neg_of_xRep_eq_xRep hb with h | h <;> simp [h]
    exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by simp))

variable (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- **The `n`-torsion as a `Finset` of `n ²` points.** Over an algebraically closed field in which
`n` is invertible `[n]` is `n ²`-to-one wherever it hits, and the torsion is its fiber above `0`;
the counting arguments want that fiber as a `Finset` with membership spelled out. -/
private theorem exists_finset_zsmul_eq_zero [DecidableEq F] {n : ℤ} (hchar : (n : F) ≠ 0) :
    ∃ T : Finset (W⁄F).toAffine.Point,
      #T = n.natAbs ^ 2 ∧ ∀ P, P ∈ T ↔ n • P = 0 := by
  have hcard : Nat.card ↥{P : (W⁄F).toAffine.Point | n • P = 0} = n.natAbs ^ 2 :=
    card_zsmul_fiber W hchar (P₀ := 0) (smul_zero n)
  have hfin : {P : (W⁄F).toAffine.Point | n • P = 0}.Finite := by
    refine Set.finite_coe_iff.mp (Nat.card_ne_zero.mp ?_).2
    rw [hcard]
    exact pow_ne_zero 2 (Int.natAbs_ne_zero.mpr (by rintro rfl; exact hchar (by simp)))
  exact ⟨hfin.toFinset,
    by rw [← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq, hcard],
    fun _ ↦ hfin.mem_toFinset⟩

omit [IsAlgClosed F] [W.IsElliptic] in
/-- The abscissae of a set of points, as a `Finset` of the roots of `p`. -/
private theorem mem_image_xRep [DecidableEq F] {p : F[X]} {T : Finset (W⁄F).toAffine.Point}
    (h : ∀ P ∈ T, ∃ x y, ∃ hns : (W⁄F).toAffine.Nonsingular x y,
      P = Affine.Point.some x y hns ∧ p.eval x = 0) (hp : p ≠ 0) :
    ∀ P ∈ T, P.xRep ∈ p.roots.toFinset.image (fun x : F ↦ ![x, 1]) := by
  intro P hP
  obtain ⟨x, y, hns, rfl, hx⟩ := h P hP
  exact Finset.mem_image.mpr
    ⟨x, Multiset.mem_toFinset.mpr (mem_roots'.mpr ⟨hp, hx⟩), (Point.xRep_some hns).symm⟩

/-- **`preΨₙ` is separable at odd `n`** over an algebraically closed field in which `n` is
invertible: the `n ² - 1` nonzero points of `ker [n]` map two-to-one onto its roots, so it has at
least `(n ² - 1) / 2` of them, which is its degree. -/
private theorem separable_preΨ_of_odd_of_isAlgClosed {n : ℤ} (hodd : ¬ Even n)
    (hchar : (n : F) ≠ 0) : ((W⁄F).preΨ n).Separable := by
  classical
  obtain ⟨T, hTcard, hTmem⟩ := exists_finset_zsmul_eq_zero W hchar
  set S : Finset F := ((W⁄F).preΨ n).roots.toFinset with hS
  have hmaps : ∀ P ∈ T.erase 0, P.xRep ∈ S.image (fun x : F ↦ ![x, 1]) := by
    refine mem_image_xRep W (fun P hP ↦ ?_) (preΨ_ne_zero _ hchar)
    obtain ⟨hP0, hPT⟩ := Finset.mem_erase.mp hP
    rcases hQ : P with _ | ⟨x, y, hns⟩
    · exact absurd hQ hP0
    · exact ⟨x, y, hns, rfl, eval_preΨ_eq_zero_of_odd W hodd hns (hQ ▸ (hTmem P).mp hPT)⟩
  have hcount : #(T.erase 0) ≤ 2 * #(S.image (fun x : F ↦ ![x, 1])) :=
    Finset.card_le_mul_card_image_of_maps_to hmaps 2 fun b _ ↦ card_filter_xRep_le_two _ b
  have hEr : #(T.erase 0) = n.natAbs ^ 2 - 1 := by
    rw [Finset.card_erase_of_mem ((hTmem 0).mpr (by simp)), hTcard]
  have himg : #(S.image (fun x : F ↦ ![x, 1])) ≤ #S := Finset.card_image_le
  have hdeg : ((W⁄F).preΨ n).natDegree = (n.natAbs ^ 2 - 1) / 2 := by
    rw [natDegree_preΨ _ hchar]; simp [hodd]
  have hdvd : 2 ∣ n.natAbs ^ 2 - 1 :=
    (Nat.Odd.sub_odd (((Int.natAbs_odd).mpr (Int.not_even_iff_odd.mp hodd)).pow) odd_one).two_dvd
  exact separable_of_natDegree_le_card_roots (preΨ_ne_zero _ hchar) (by rw [hdeg, ← hS]; omega)

/-- **At most four points of a `Finset` are `2`-torsion**, over an algebraically closed field in
which `2` is invertible: they all lie in `ker [2]`, which has four points. -/
private theorem card_filter_two_zsmul_eq_zero_le [DecidableEq F] (hchar : ((2 : ℤ) : F) ≠ 0)
    (T : Finset (W⁄F).toAffine.Point) : #{P ∈ T | (2 : ℤ) • P = 0} ≤ 4 := by
  obtain ⟨T₂, hT₂card, hT₂mem⟩ := exists_finset_zsmul_eq_zero W hchar
  refine (Finset.card_le_card fun P hP ↦ (hT₂mem P).mpr (Finset.mem_filter.mp hP).2).trans ?_
  rw [hT₂card]
  norm_num

/-- **`preΨₙ` is separable at even `n`** over an algebraically closed field in which `n` is
invertible: the points of `ker [n]` that are not `2`-torsion — at least `n ² - 4` of them — map
two-to-one onto its roots, and `(n ² - 4) / 2` is its degree. -/
private theorem separable_preΨ_of_even_of_isAlgClosed {n : ℤ} (heven : Even n)
    (hchar : (n : F) ≠ 0) : ((W⁄F).preΨ n).Separable := by
  classical
  have h2F : ((2 : ℤ) : F) ≠ 0 := Int.two_ne_zero_of_even_of_cast_ne_zero heven hchar
  obtain ⟨T, hTcard, hTmem⟩ := exists_finset_zsmul_eq_zero W hchar
  set s : Finset (W⁄F).toAffine.Point := {P ∈ T | ¬ ((2 : ℤ) • P = 0)} with hs
  have hscard : n.natAbs ^ 2 - 4 ≤ #s := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := T) (p := fun P : (W⁄F).toAffine.Point ↦ (2 : ℤ) • P = 0)
    have htor := card_filter_two_zsmul_eq_zero_le W h2F T
    rw [hTcard, ← hs] at hsplit
    omega
  set S : Finset F := ((W⁄F).preΨ n).roots.toFinset with hS
  have hmaps : ∀ P ∈ s, P.xRep ∈ S.image (fun x : F ↦ ![x, 1]) := by
    refine mem_image_xRep W (fun P hP ↦ ?_) (preΨ_ne_zero _ hchar)
    obtain ⟨hPT, hP2⟩ := Finset.mem_filter.mp hP
    rcases hQ : P with _ | ⟨x, y, hns⟩
    · exact absurd (hQ ▸ (by simp : (2 : ℤ) • (0 : (W⁄F).toAffine.Point) = 0)) hP2
    · exact ⟨x, y, hns, rfl, eval_preΨ_eq_zero_of_even W heven hns (hQ ▸ (hTmem P).mp hPT)
        (hQ ▸ hP2)⟩
  have hcount : #s ≤ 2 * #(S.image (fun x : F ↦ ![x, 1])) :=
    Finset.card_le_mul_card_image_of_maps_to hmaps 2 fun b _ ↦ card_filter_xRep_le_two _ b
  have himg : #(S.image (fun x : F ↦ ![x, 1])) ≤ #S := Finset.card_image_le
  have hdeg : ((W⁄F).preΨ n).natDegree = (n.natAbs ^ 2 - 4) / 2 := by
    rw [natDegree_preΨ _ hchar]; simp [heven]
  -- `n ² - 4` is even at even `n`, so the degree is exactly half the count
  have hdvd : 2 ∣ n.natAbs ^ 2 - 4 := by
    obtain ⟨m, rfl⟩ := heven
    have hsq : (m + m).natAbs ^ 2 = 4 * m.natAbs ^ 2 := by
      rw [← two_mul, Int.natAbs_mul]
      ring
    omega
  exact separable_of_natDegree_le_card_roots (preΨ_ne_zero _ hchar) (by rw [hdeg, ← hS]; omega)

/-- **`ΨSq₂` is separable** over an algebraically closed field in which `2` is invertible: the three
nonzero `2`-torsion points are their own negatives, so their abscissae are distinct, and there are
as many of them as the degree. -/
private theorem separable_ΨSq_two_of_isAlgClosed (hchar : ((2 : ℤ) : F) ≠ 0) :
    ((W⁄F).ΨSq 2).Separable := by
  classical
  have hne : ((W⁄F).ΨSq 2) ≠ 0 := ΨSq_ne_zero_of_Δ_ne_zero _ W.isUnit_Δ.ne_zero two_ne_zero
  obtain ⟨T, hTcard, hTmem⟩ := exists_finset_zsmul_eq_zero W hchar
  set S : Finset F := ((W⁄F).ΨSq 2).roots.toFinset with hS
  have hmaps : ∀ P ∈ T.erase 0, P.xRep ∈ S.image (fun x : F ↦ ![x, 1]) := by
    refine mem_image_xRep W (fun P hP ↦ ?_) hne
    obtain ⟨hP0, hPT⟩ := Finset.mem_erase.mp hP
    rcases hQ : P with _ | ⟨x, y, hns⟩
    · exact absurd hQ hP0
    · exact ⟨x, y, hns, rfl, (eval_ΨSq_eq_zero_iff_zsmul_eq_zero (W⁄F) hns 2).mpr
        (zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero.mpr (hQ ▸ (hTmem P).mp hPT))⟩
  -- a `2`-torsion point is its own negative, so distinct ones have distinct abscissae
  have hinj : Set.InjOn (fun P : (W⁄F).toAffine.Point ↦ P.xRep) (T.erase 0) := by
    intro P hP Q hQ hPQ
    obtain ⟨-, hQT⟩ := Finset.mem_erase.mp hQ
    rcases Point.eq_or_eq_neg_of_xRep_eq_xRep hPQ with h | h
    · exact h
    · rw [h, neg_eq_iff_add_eq_zero, ← two_zsmul, (hTmem Q).mp hQT]
  have hEr : #(T.erase 0) = 3 := by
    rw [Finset.card_erase_of_mem ((hTmem 0).mpr (by simp)), hTcard]
    norm_num
  have hle : #(T.erase 0) ≤ #(S.image (fun x : F ↦ ![x, 1])) :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  have himg : #(S.image (fun x : F ↦ ![x, 1])) ≤ #S := Finset.card_image_le
  have hdeg : ((W⁄F).ΨSq 2).natDegree = 3 := by rw [natDegree_ΨSq _ hchar]; norm_num
  exact separable_of_natDegree_le_card_roots hne (by rw [hdeg, ← hS]; omega)

end IsAlgClosed

variable (W : WeierstrassCurve F) [W.IsElliptic]

/-- **`preΨₙ` is separable** over any field in which `n` is invertible. Separability is insensitive
to base change, so it descends from the algebraic closure, where the roots can be counted against
the points of `ker [n]`. -/
theorem separable_preΨ {n : ℤ} (hchar : (n : F) ≠ 0) : (W.preΨ n).Separable := by
  have hchar' : ((n : ℤ) : AlgebraicClosure F) ≠ 0 := by
    simpa only [map_intCast, map_zero] using
      (FaithfulSMul.algebraMap_injective F (AlgebraicClosure F)).ne hchar
  rw [← Polynomial.separable_map (algebraMap F (AlgebraicClosure F)), ← map_preΨ]
  by_cases heven : Even n
  · exact separable_preΨ_of_even_of_isAlgClosed (W⁄(AlgebraicClosure F)).toAffine heven hchar'
  · exact separable_preΨ_of_odd_of_isAlgClosed (W⁄(AlgebraicClosure F)).toAffine heven hchar'

/-- **`Ψ₂Sq` is separable** over any field in which `2` is invertible: its roots are the abscissae
of the three nonzero `2`-torsion points, which are distinct. -/
theorem separable_Ψ₂Sq (hchar : ((2 : ℤ) : F) ≠ 0) : W.Ψ₂Sq.Separable := by
  have hchar' : ((2 : ℤ) : AlgebraicClosure F) ≠ 0 := by
    simpa only [map_intCast, map_zero] using
      (FaithfulSMul.algebraMap_injective F (AlgebraicClosure F)).ne hchar
  rw [← Polynomial.separable_map (algebraMap F (AlgebraicClosure F)), ← ΨSq_two, ← map_ΨSq]
  exact separable_ΨSq_two_of_isAlgClosed (W⁄(AlgebraicClosure F)).toAffine hchar'

/-- **The minimal polynomial of a root of `ΨSqₙ` is separable** when `n` is invertible. `ΨSqₙ`
itself need not be separable — it is
`preΨₙ ²` times `Ψ₂Sq` at even `n`, so it carries a repeated factor once `preΨₙ` is not a unit —
but a minimal polynomial is irreducible, so it divides one of those two factors and inherits
that factor's separability. -/
theorem separable_minpoly_of_aeval_ΨSq_eq_zero {Ω : Type*} [Ring Ω] [IsDomain Ω] [Algebra F Ω]
    {n : ℤ}
    (hchar : (n : F) ≠ 0) {x : Ω} (hroot : aeval x (W.ΨSq n) = 0) :
    (minpoly F x).Separable := by
  have hn : n ≠ 0 := by rintro rfl; exact hchar (by simp)
  have hne : W.ΨSq n ≠ 0 := ΨSq_ne_zero_of_Δ_ne_zero W W.isUnit_Δ.ne_zero hn
  have halg : IsAlgebraic F x := ⟨W.ΨSq n, hne, hroot⟩
  have hprime : Prime (minpoly F x) := (minpoly.irreducible halg.isIntegral).prime
  have hdvd : minpoly F x ∣ W.ΨSq n := minpoly.dvd F x hroot
  rw [WeierstrassCurve.ΨSq] at hdvd
  rcases hprime.dvd_mul.mp hdvd with hd | hd
  · exact (separable_preΨ W hchar).of_dvd (hprime.dvd_of_dvd_pow hd)
  · by_cases he : Even n
    · exact (separable_Ψ₂Sq W (Int.two_ne_zero_of_even_of_cast_ne_zero he hchar)).of_dvd
        (by simpa [he] using hd)
    · exact Polynomial.separable_one.of_dvd (by simpa [he] using hd)

/-- **The minimal polynomial of the abscissa of an `n`-torsion point is separable** when `n` is
invertible: such an abscissa is a root of `ΨSqₙ`. -/
theorem separable_minpoly_of_zsmul_eq_zero {Ω : Type*} [Field Ω] [Algebra F Ω] {n : ℤ}
    (hchar : (n : F) ≠ 0) {x y : Ω} (hns : (W.baseChange Ω).toAffine.Nonsingular x y)
    (htors : n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0) :
    (minpoly F x).Separable :=
  separable_minpoly_of_aeval_ΨSq_eq_zero W hchar <| by
    have hΨSq := (eval_ΨSq_eq_zero_iff_zsmul_eq_zero (W.baseChange Ω) hns n).mpr htors
    rwa [baseChange, map_ΨSq, eval_map, ← aeval_def] at hΨSq

end WeierstrassCurve

end
