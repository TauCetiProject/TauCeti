/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Legendre.Equation
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.TwoTorsion
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TwoTorsion
import TauCeti.RingTheory.Polynomial.Vieta

/-!
# Normalization to a scaled Legendre equation

Let `W : y² = f(x)` be a Weierstrass equation in the normal form `a₁ = a₃ = 0` whose cubic splits
as `f = (X - e₀) (X - e₁) (X - e₂)`. The translation `x ↦ x + e₀` moves the root `e₀` to the
origin, and the translated equation is the scaled Legendre equation

  `y² = x (x - d) (x - d l)`,  `d = e₁ - e₀`,  `d l = e₂ - e₀`.

This is a coefficient identity over every commutative ring
(`WeierstrassCurve.smul_eq_scaledLegendre`). Over a field with distinct roots one takes
`l = (e₂ - e₀) / (e₁ - e₀)`, so `d ≠ 0`, `l ≠ 0` and `l ≠ 1`.

Over a field `K`, an elliptic curve `E` whose group `E(K)` has exactly four points killed by `2`
lives in characteristic `≠ 2` (`WeierstrassCurve.Affine.Point.two_ne_zero_of_two_lt_card`), and
once the square is completed its cubic has three roots in `K`
(`WeierstrassCurve.Affine.card_ker_nsmul_two`). The translation above then normalizes it:
some change of coordinates carries `E` to a scaled Legendre equation with `d ≠ 0`, `l ≠ 0` and
`l ≠ 1` (`WeierstrassCurve.exists_scaledLegendre_of_full_two_torsion`). Since the scaled equation
is the quadratic twist of `y² = x (x - 1) (x - l)` with twisting discriminant `d`
(`TauCeti.scaledLegendre_eq_quadraticTwistOf`), the curve is `K`-isomorphic to a quadratic twist
of a Legendre curve, though in general not to a Legendre curve itself. The argument uses no
classification of automorphisms and covers `j = 0` and `j = 1728`, characteristic `3` included.

## Main results

* `WeierstrassCurve.smul_eq_scaledLegendre`: translating a root of a split cubic to the origin
  gives a scaled Legendre equation.
* `WeierstrassCurve.exists_scaledLegendre_of_full_two_torsion`: an elliptic curve with full
  rational `2`-torsion is a change of coordinates away from a scaled Legendre equation.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1 and III.2.
* M. A. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short character
  sums*, Ann. of Math. 191 (2020), 355–392, §6, the Legendre discussion before Lemma 6.2 and its
  proof.
-/

public section

open Polynomial TauCeti

namespace WeierstrassCurve

/-- **Translating a root of a split cubic to the origin gives a scaled Legendre equation.** If `W`
is in the normal form `a₁ = a₃ = 0` and its cubic is `(X - e₀) (X - e₁) (X - e₂)`, the change of
coordinates `x ↦ x + e₀` carries `W` to `y² = x (x - d) (x - d l)` with `d = e₁ - e₀`, for any
`l` with `d l = e₂ - e₀`. Over a field with `e₀ ≠ e₁` the parameter is
`l = (e₂ - e₀) / (e₁ - e₀)`. -/
theorem smul_eq_scaledLegendre {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    [W.IsCharNeTwoNF] {e₀ e₁ e₂ l : R}
    (hf : W.toAffine.f = (X - C e₀) * (X - C e₁) * (X - C e₂)) (hl : (e₁ - e₀) * l = e₂ - e₀) :
    (⟨1, e₀, 0, 0⟩ : VariableChange R) • W = scaledLegendre (e₁ - e₀) l := by
  rw [Affine.f, Cubic.prod_X_sub_C_eq,
    show X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ = Cubic.toPoly ⟨1, W.a₂, W.a₄, W.a₆⟩ by
      simp [Cubic.toPoly],
    Cubic.toPoly_injective] at hf
  simp only [Cubic.mk.injEq, true_and] at hf
  obtain ⟨h₂, h₄, h₆⟩ := hf
  ext <;> simp [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, h₂, h₄, h₆]
  · linear_combination hl
  · linear_combination -(e₁ - e₀) * hl
  · ring

/-- **An elliptic curve with full rational `2`-torsion is a change of coordinates away from a
scaled Legendre equation.** Let `E` be an elliptic curve over a field `K` whose group of
`K`-points has exactly four elements killed by `2`. Then some change of coordinates carries `E` to
`y² = x (x - d) (x - d l)` with `d ≠ 0`, `l ≠ 0` and `l ≠ 1`. No hypothesis on the characteristic
is needed: in characteristic `2` at most two points are killed by `2`.

The coordinate change is in general not one to `y² = x (x - 1) (x - l)` itself: the scaled
equation is a quadratic twist of that one, with twisting discriminant `d`. -/
theorem exists_scaledLegendre_of_full_two_torsion {K : Type*} [Field K] [DecidableEq K]
    (E : WeierstrassCurve K) [E.IsElliptic]
    (hE : Nat.card (nsmulAddMonoidHom (α := E.toAffine.Point) 2).ker = 4) :
    ∃ (C : VariableChange K) (d l : K), d ≠ 0 ∧ l ≠ 0 ∧ l ≠ 1 ∧
      C • E = scaledLegendre d l := by
  -- four points `T` with `-T = T` exclude characteristic `2`
  have : Finite (nsmulAddMonoidHom (α := E.toAffine.Point) 2).ker :=
    Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  have hfin :=
    Set.toFinite ((nsmulAddMonoidHom (α := E.toAffine.Point) 2).ker : Set E.toAffine.Point)
  have h2 : (2 : K) ≠ 0 := by
    refine Affine.Point.two_ne_zero_of_two_lt_card (S := hfin.toFinset) (fun T hT ↦ ?_) ?_
    · rw [Set.Finite.mem_toFinset, SetLike.mem_coe, AddMonoidHom.mem_ker,
        nsmulAddMonoidHom_apply, two_nsmul] at hT
      exact neg_eq_of_add_eq_zero_right hT
    · rw [← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hE]
      norm_num
  have : Invertible (2 : K) := invertibleOfNonzero h2
  set W := E.toCharNeTwoNF • E
  -- completing the square does not change the number of points killed by `2`
  have hW : Nat.card {x : K // W.toAffine.f.eval x = 0} = 3 := by
    have hker : Nat.card (nsmulAddMonoidHom (α := W.toAffine.Point) 2).ker = 4 := by
      let φ := Affine.Point.addEquivVariableChange E E.toCharNeTwoNF
      refine (Nat.card_congr (φ.toEquiv.subtypeEquiv fun P ↦ ?_)).trans hE
      simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, AddEquiv.toEquiv_eq_coe,
        AddEquiv.coe_toEquiv, ← map_nsmul, AddEquivClass.map_eq_zero_iff]
    have := Affine.card_ker_nsmul_two W.toAffine
    lia
  -- three distinct roots of the monic cubic `f`, which is therefore their product
  have : Finite {x : K // W.toAffine.f.eval x = 0} := Nat.finite_of_card_ne_zero (by lia)
  let e := (Finite.equivFinOfCardEq hW).symm
  have hinj : Function.Injective fun i ↦ (e i).val := Subtype.val_injective.comp e.injective
  have hf : W.toAffine.f = ∏ i, (X - C (e i).val) := by
    refine eq_prod_X_sub_C_of_monic_of_roots_eq W.toAffine.monic_f
      (by simp [W.toAffine.natDegree_f]) (Multiset.eq_of_le_of_card_le ?_ ?_).symm
    · refine (Multiset.le_iff_subset (Finset.univ.nodup.map hinj)).mpr fun x hx ↦ ?_
      obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hx
      exact (mem_roots W.toAffine.f_ne_zero).mpr (e i).property
    · simpa [W.toAffine.natDegree_f] using card_roots' W.toAffine.f
  rw [Fin.prod_univ_three] at hf
  have h01 : (e 1).val - (e 0).val ≠ 0 := sub_ne_zero.mpr (hinj.ne (by decide))
  refine ⟨⟨1, (e 0).val, 0, 0⟩ * E.toCharNeTwoNF, (e 1).val - (e 0).val,
    ((e 2).val - (e 0).val) / ((e 1).val - (e 0).val), h01, ?_, ?_, ?_⟩
  · exact div_ne_zero (sub_ne_zero.mpr (hinj.ne (by decide))) h01
  · rw [Ne, div_eq_one_iff_eq h01, sub_left_inj]
    exact hinj.ne (by decide)
  · rw [mul_smul]
    exact W.smul_eq_scaledLegendre hf (mul_div_cancel₀ _ h01)

end WeierstrassCurve
