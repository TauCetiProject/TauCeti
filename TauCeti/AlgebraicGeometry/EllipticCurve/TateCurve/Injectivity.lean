/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.XCoordinate
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# Injectivity of the Tate uniformisation

Let `K` be a complete non-archimedean normed field and `q ∈ Kˣ` with `‖q‖ < 1`. The Tate
uniformisation `Kˣ / q^ℤ → E_q(K)` is injective (`TauCeti.tateUniformization_injective`).

Two parameters with the same image are equal or mutually inverse, and in the second case their
common image `P` satisfies `-P = P`
(`TauCeti.tateUniformization_eq_tateUniformization_iff`). It remains to see that a nonidentity
parameter `x` whose image has order two satisfies `x² = 1`. Suppose first that `q = r²` in `K`.
The first Tate coordinate of a nonidentity parameter whose image has order two is a root of the
`2`-torsion polynomial `4x³ + b₂x² + 2b₄x + b₆`, and two nonidentity parameters with the same first
coordinate are equal or mutually inverse
(`TauCeti.tateUniformizationX_eq_tateUniformizationX_iff`). When `2 ≠ 0`, the classes of `-1`, `r`
and `-r` are distinct nonidentity classes that are their own inverses, so their images have order
two and their first coordinates are three distinct roots; if `x² ≠ 1` the first coordinate of `x`
would be a fourth root of a cubic. When `2 = 0` we have `-1 = 1` and `-r = r`, and only the class
of `r` is used: the `2`-torsion polynomial of the Tate curve is `x²`, so the first coordinate of
`x` is `0`, as is that of `r`, and `x` is the class of `r`.

In general `q` has a square root in a finite extension `L` of `K`, which is complete for the
spectral norm, and the uniformisation over `L` restricts to the one over `K`
(`TauCeti.mapAlong_tateUniformization`). The norm need not be discrete, and the characteristic is
unrestricted.

As a consequence, the image of a parameter has order dividing two exactly when the parameter does
(`TauCeti.two_nsmul_tateUniformization_eq_zero_iff`).

## Main results

* `TauCeti.tateUniformization_injective`: the Tate uniformisation is injective.
* `TauCeti.tateUniformizationBaseChange_injective`: the same over a complete extension.
* `TauCeti.two_nsmul_tateUniformization_eq_zero_iff`: the image of `x` is killed by two exactly
  when `x² = 1`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3.
* J. Tate, *A review of non-Archimedean elliptic functions* (1995).
-/

public section

namespace TauCeti

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-! ### Parameters whose image has order two -/

section TwoTorsion

/-- The first Tate coordinate of a nonidentity parameter whose image has order two is a root of
the `2`-torsion polynomial. -/
private theorem isRoot_twoTorsionPolynomial_of_neg_eq (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    {x : Kˣ ⧸ Subgroup.zpowers q} (hx : x ≠ 1)
    (h : -tateUniformization q hq x = tateUniformization q hq x) :
    (tateCurveAt q hq).twoTorsionPolynomial.toPoly.IsRoot (tateQuotientCoordinates q x).1 := by
  classical
  rw [tateUniformization_of_ne_one q hq hx, Point.mk] at h
  exact Point.isRoot_twoTorsionPolynomial_of_add_self _ (neg_eq_iff_add_eq_zero.mp h)

/-- A nonidentity parameter with the same first Tate coordinate as a nonidentity self-inverse
class `c` is `c`. -/
private theorem eq_of_tateQuotientCoordinates_fst_eq (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    {c z : Kˣ ⧸ Subgroup.zpowers q} (hc : c ≠ 1) (hcc : c⁻¹ = c) (hz : z ≠ 1)
    (h : (tateQuotientCoordinates q z).1 = (tateQuotientCoordinates q c).1) : z = c := by
  rcases (tateQuotientCoordinates_fst_eq_iff q hq hz hc).mp h with h | h
  · exact h
  · rw [h, hcc]

/-- In characteristic two, the `2`-torsion polynomial of the Tate curve is `x²`, so its only root
is `0`. -/
private theorem eq_zero_of_isRoot_twoTorsionPolynomial (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (h2 : (2 : K) = 0) {t : K} (ht : (tateCurveAt q hq).twoTorsionPolynomial.toPoly.IsRoot t) :
    t = 0 := by
  rw [IsRoot.def, eval_toPoly_twoTorsionPolynomial, b₂, b₄, b₆, tateCurveAt_a₁, tateCurveAt_a₂,
    tateCurveAt_a₃] at ht
  refine pow_eq_zero_iff (n := 2) two_ne_zero |>.mp ?_
  linear_combination ht - (2 * t ^ 3 + 2 * (tateCurveAt q hq).a₄ * t +
    2 * (tateCurveAt q hq).a₆) * h2

/-- **Parameters whose image has order two, in characteristic two.** If `2 = 0` in `K` and
`q = r²`, a nonidentity parameter `x` whose image `P` satisfies `-P = P` is its own inverse. -/
private theorem inv_eq_self_of_two_eq_zero (q : Kˣ) (hq : ‖(q : K)‖ < 1) (h2 : (2 : K) = 0)
    {r : Kˣ} (hr : r ^ 2 = q) {x : Kˣ ⧸ Subgroup.zpowers q} (hx : x ≠ 1)
    (h : -tateUniformization q hq x = tateUniformization q hq x) : x⁻¹ = x := by
  have hc : (r : Kˣ ⧸ Subgroup.zpowers q) ≠ 1 :=
    mt (QuotientGroup.eq_one_iff r).mp (notMem_zpowers_of_sq_eq hq hr)
  have hcc : (r : Kˣ ⧸ Subgroup.zpowers q)⁻¹ = r := inv_eq_of_mul_eq_one_right <| by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, ← sq, hr]
    exact Subgroup.mem_zpowers q
  -- both first coordinates are roots of the `2`-torsion polynomial, hence `0`
  have hxr := (eq_zero_of_isRoot_twoTorsionPolynomial q hq h2
    (isRoot_twoTorsionPolynomial_of_neg_eq q hq hx h)).trans
    (eq_zero_of_isRoot_twoTorsionPolynomial q hq h2 (isRoot_twoTorsionPolynomial_of_neg_eq q hq hc
      (by rw [← tateUniformization_inv, hcc]))).symm
  rw [eq_of_tateQuotientCoordinates_fst_eq q hq hc hcc hx hxr, hcc]

/-- **Parameters whose image has order two, away from characteristic two.** If `2 ≠ 0` in `K` and
`q = r²`, a nonidentity parameter `x` whose image `P` satisfies `-P = P` is its own inverse: the
classes of `-1`, `r` and `-r` already give three distinct roots of the `2`-torsion polynomial. -/
private theorem inv_eq_self_of_two_ne_zero (q : Kˣ) (hq : ‖(q : K)‖ < 1) (h2 : (2 : K) ≠ 0)
    {r : Kˣ} (hr : r ^ 2 = q) {x : Kˣ ⧸ Subgroup.zpowers q} (hx : x ≠ 1)
    (h : -tateUniformization q hq x = tateUniformization q hq x) : x⁻¹ = x := by
  classical
  by_contra hxx
  set ψ := (tateCurveAt q hq).twoTorsionPolynomial
  set X : Kˣ ⧸ Subgroup.zpowers q → K := fun z ↦ (tateQuotientCoordinates q z).1
  have hneg : (-1 : Kˣ) ∉ Subgroup.zpowers q := by
    refine notMem_zpowers_of_norm_eq_one hq (by simp) fun h ↦ h2 ?_
    have h' := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at h'
    linear_combination -h'
  have hr' : (-r) ^ 2 = q := by rw [neg_sq, hr]
  -- the classes of `-1`, `r` and `-r` are nonidentity classes and their own inverses
  have hc {s : Kˣ} (hs : s ∉ Subgroup.zpowers q) : (s : Kˣ ⧸ Subgroup.zpowers q) ≠ 1 :=
    mt (QuotientGroup.eq_one_iff s).mp hs
  have hcc {s : Kˣ} (hs : s ^ 2 ∈ Subgroup.zpowers q) :
      (s : Kˣ ⧸ Subgroup.zpowers q)⁻¹ = s := inv_eq_of_mul_eq_one_right <| by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, ← sq]
    exact hs
  have hc₁ := hc hneg
  have hcc₁ := hcc (s := -1) (by rw [neg_one_sq]; exact one_mem _)
  have hc₂ := hc (notMem_zpowers_of_sq_eq hq hr)
  have hcc₂ := hcc (s := r) (by rw [hr]; exact Subgroup.mem_zpowers q)
  have hc₃ := hc (notMem_zpowers_of_sq_eq hq hr')
  have hcc₃ := hcc (s := -r) (by rw [hr']; exact Subgroup.mem_zpowers q)
  have hne {a b : Kˣ} (hab : a⁻¹ * b ∉ Subgroup.zpowers q) :
      (a : Kˣ ⧸ Subgroup.zpowers q) ≠ b := fun h ↦ hab (QuotientGroup.eq.mp h)
  -- the first coordinates of `x` and of distinct self-inverse classes are distinct
  have hXne {c d : Kˣ ⧸ Subgroup.zpowers q} (hc : c ≠ 1) (hd : d ≠ 1) (hdd : d⁻¹ = d)
      (hcd : c ≠ d) : X c ≠ X d :=
    fun h ↦ hcd (eq_of_tateQuotientCoordinates_fst_eq q hq hd hdd hc h)
  have hXx {c : Kˣ ⧸ Subgroup.zpowers q} (hc : c ≠ 1) (hcc : c⁻¹ = c) : X x ≠ X c :=
    fun h ↦ hxx (by rw [eq_of_tateQuotientCoordinates_fst_eq q hq hc hcc hx h, hcc])
  -- and they are all roots of the `2`-torsion polynomial, a cubic
  have hroot {c : Kˣ ⧸ Subgroup.zpowers q} (hc : c ≠ 1) (hcc : c⁻¹ = c) :
      ψ.toPoly.IsRoot (X c) :=
    isRoot_twoTorsionPolynomial_of_neg_eq q hq hc (by rw [← tateUniformization_inv, hcc])
  have hψ : ψ.toPoly ≠ 0 := Cubic.ne_zero_of_a_ne_zero <| by
    simp only [ψ, twoTorsionPolynomial]
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  set S : Finset K := {X x, X ((-1 : Kˣ) : Kˣ ⧸ Subgroup.zpowers q), X r,
    X ((-r : Kˣ) : Kˣ ⧸ Subgroup.zpowers q)}
  have hcard : S.card = 4 := by
    rw [Finset.card_eq_four]
    refine ⟨_, _, _, _, hXx hc₁ hcc₁, hXx hc₂ hcc₂, hXx hc₃ hcc₃, hXne hc₁ hc₂ hcc₂ (hne ?_),
      hXne hc₁ hc₃ hcc₃ (hne ?_), hXne hc₂ hc₃ hcc₃ (hne ?_), rfl⟩
    · rw [inv_neg_one, neg_one_mul]
      exact notMem_zpowers_of_sq_eq hq hr'
    · rw [inv_neg_one, neg_one_mul, neg_neg]
      exact notMem_zpowers_of_sq_eq hq hr
    · rw [mul_neg, inv_mul_cancel]
      exact hneg
  have hsub : S ⊆ ψ.roots.toFinset := by
    intro t ht
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at ht
    rw [Multiset.mem_toFinset]
    refine (mem_roots hψ).mpr ?_
    rcases ht with rfl | rfl | rfl | rfl
    · exact isRoot_twoTorsionPolynomial_of_neg_eq q hq hx h
    · exact hroot hc₁ hcc₁
    · exact hroot hc₂ hcc₂
    · exact hroot hc₃ hcc₃
  have := (Finset.card_le_card hsub).trans ψ.card_roots_le
  omega

/-- The Tate uniformisation is injective when `q` is a square. -/
private theorem tateUniformization_injective_of_sq_eq (q : Kˣ) (hq : ‖(q : K)‖ < 1) {r : Kˣ}
    (hr : r ^ 2 = q) : Function.Injective (tateUniformization q hq) := by
  intro x y hxy
  rcases (tateUniformization_eq_tateUniformization_iff q hq x y).mp hxy with h | ⟨rfl, h⟩
  · exact h
  · by_cases hy : y = 1
    · simp [hy]
    · by_cases h2 : (2 : K) = 0
      · exact inv_eq_self_of_two_eq_zero q hq h2 hr hy h
      · exact inv_eq_self_of_two_ne_zero q hq h2 hr hy h

end TwoTorsion

/-! ### Injectivity -/

/-- **The Tate uniformisation is injective.** For a complete non-archimedean normed field `K` and
`q ∈ Kˣ` with `‖q‖ < 1`, distinct classes of `Kˣ / q^ℤ` have distinct images on the Tate curve
`E_q(K)`. -/
theorem tateUniformization_injective (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    Function.Injective (tateUniformization q hq) := by
  intro x y hxy
  -- adjoin a square root of `q`, with the spectral norm
  let := NontriviallyNormedField.ofNormNeOne ⟨(q : K), q.ne_zero, hq.ne⟩
  let L := (X ^ 2 - C (q : K)).SplittingField
  let : NormedField L := spectralNorm.normedField K L
  let : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  have : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun a b ↦
      isNonarchimedean_spectralNorm (K := K) (L := L) a b
  have : CompleteSpace L := FiniteDimensional.complete K L
  have : RingHomIsometric (algebraMap K L) := ⟨norm_algebraMap' L _⟩
  obtain ⟨r, hr⟩ : ∃ r : L, ((X ^ 2 - C (q : K)).map (algebraMap K L)).eval r = 0 :=
    (SplittingField.splits _).exists_eval_eq_zero (by
      rw [degree_map, degree_X_pow_sub_C two_pos]
      exact two_ne_zero)
  have hr : r ^ 2 = algebraMap K L q := by
    simpa [sub_eq_zero] using hr
  have hr₀ : r ≠ 0 := by
    rintro rfl
    exact q.ne_zero ((algebraMap K L).injective (by simpa using hr.symm))
  refine tateParameterBaseChange_injective (algebraMap K L) (algebraMap K L).injective q
    (tateUniformization_injective_of_sq_eq (Units.map (algebraMap K L : K →* L) q)
      (by simpa using hq) (r := Units.mk0 r hr₀) (Units.ext (by simpa using hr)) ?_)
  rw [← mapAlong_tateUniformization, ← mapAlong_tateUniformization, hxy]

/-- The Tate uniformisation is injective, as an equality criterion. -/
@[simp]
theorem tateUniformization_inj (q : Kˣ) (hq : ‖(q : K)‖ < 1) {x y : Kˣ ⧸ Subgroup.zpowers q} :
    tateUniformization q hq x = tateUniformization q hq y ↔ x = y :=
  (tateUniformization_injective q hq).eq_iff

/-- **The `2`-torsion of the Tate uniformisation.** The image of a parameter `x` is killed by two
exactly when `x² = 1`. -/
@[simp]
theorem two_nsmul_tateUniformization_eq_zero_iff [DecidableEq K] (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Kˣ ⧸ Subgroup.zpowers q) :
    2 • tateUniformization q hq x = 0 ↔ x ^ 2 = 1 := by
  rw [two_nsmul, ← neg_eq_iff_add_eq_zero, ← tateUniformization_inv, tateUniformization_inj,
    inv_eq_iff_mul_eq_one, sq]

/-- **The Tate uniformisation over a complete extension is injective.** -/
theorem tateUniformizationBaseChange_injective (L : Type*) [NormedField L] [NormedAlgebra K L]
    [CompleteSpace L] [IsUltrametricDist L] (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    Function.Injective (tateUniformizationBaseChange L q hq) := by
  intro x y hxy
  have hq' : ‖((Units.map (algebraMap K L : K →* L) q : Lˣ) : L)‖ < 1 := by simpa using hq
  refine tateUniformization_injective _ hq' ?_
  -- both images are determined by the common image over `L`
  rcases hP : tateUniformizationBaseChange L q hq x with _ | ⟨a, b, h⟩
  · rw [(tateUniformizationBaseChange_eq_zero_iff L q hq x).mp hP,
      (tateUniformizationBaseChange_eq_zero_iff L q hq y).mp (hxy.symm.trans hP)]
  · obtain ⟨hx, hax, hbx⟩ := (tateUniformizationBaseChange_eq_some_iff L q hq x h).mp hP
    obtain ⟨hy, hay, hby⟩ :=
      (tateUniformizationBaseChange_eq_some_iff L q hq y h).mp (hxy.symm.trans hP)
    have h' : (tateCurveAt _ hq').toAffine.Nonsingular a b := by
      exact baseChange_tateCurveAt L q hq ▸ h
    rw [(tateUniformization_eq_some_iff _ hq' x h').mpr ⟨hx, hax, hbx⟩,
      (tateUniformization_eq_some_iff _ hq' y h').mpr ⟨hy, hay, hby⟩]

end TauCeti

end
