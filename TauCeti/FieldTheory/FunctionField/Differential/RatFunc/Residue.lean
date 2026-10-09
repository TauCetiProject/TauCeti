/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.RatFunc.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Expansion.Laurent.Basic
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order

/-!
# The local components of `dx` on `k(x)` are residues

Let `η` be the canonical Weil differential of the rational function field `k(x)`, the
differential classically written `dx` (`TauCeti.ratFuncWeilDifferential`).  At every rational
place its local component is a residue of a Laurent expansion:

* at the place `P_a` of `x - a`, with the uniformizer `x - a`, `η_{P_a} (z) = res_{P_a, x - a} (z)`;
* at the place at infinity, with the uniformizer `x⁻¹`, `η_{P_∞} (z) = -res_{P_∞, x⁻¹} (x² z)`.

These are the two faces of `η_P (z) = res_P (z dx)`: `dx = d(x - a)`, while `dx = -x² d(x⁻¹)`.
This is the rational-function-field case of Stichtenoth's identification of local components
with residues, and the base case from which it is transported to a separable extension of
`k(x)` along the cotrace.

Both sides of each identity are `k`-linear in `z`, vanish once `z` vanishes to high enough
order at the place, and agree on the powers of the uniformizer, so they are equal by
`TauCeti.Place.linearMap_ext_zpow`.  On the powers of `x - a` the local component is computed
from the abstract residue theorem `∑_P η_P (z) = 0`: only `P_a` and `P_∞` contribute.

Feeding the identification back into the abstract residue theorem gives the **residue theorem
for `k(x)`**: if every pole of `z` is a rational place, then
`∑_{a ∈ k} res_{P_a, x - a} (z) = res_{P_∞, x⁻¹} (x² z)`, the classical statement that the
residues of `z dx` over `ℙ¹(k)` sum to zero.  Over an algebraically closed field every place is
rational, and the hypothesis disappears.

## Main results

* `TauCeti.repartitionDualComponent_ratFuncWeilDifferential_infty`:
  `η_{P_∞} (z) = -res_{P_∞, x⁻¹} (x² z)`.
* `TauCeti.repartitionDualComponent_ratFuncWeilDifferential_adicOfIrreducible_X_sub_C`:
  `η_{P_a} (z) = res_{P_a, x - a} (z)`.
* `TauCeti.finsum_residue_adicOfIrreducible_X_sub_C`: the residue theorem for a rational
  function whose poles are rational places.
* `TauCeti.finsum_residue_adicOfIrreducible_X_sub_C_of_isAlgClosed`: the residue theorem for
  `k(x)` over an algebraically closed field.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 1.7.4, Theorem 4.3.2(d) and Corollary 4.3.3.
-/

public section

open Polynomial

namespace TauCeti

open Place

variable {k : Type*} [Field k]

/-! ### The local component at infinity -/

/-- **The local component of `dx` at infinity is a residue** (Stichtenoth, Theorem 4.3.2(d), for
`k(x)`): `η_{P_∞} (z) = -res_{P_∞, x⁻¹} (x² z)`, which is `res_{P_∞} (z dx)` since
`dx = -x² d(x⁻¹)`. -/
theorem repartitionDualComponent_ratFuncWeilDifferential_infty (z : RatFunc k) :
    repartitionDualComponent (ratFuncWeilDifferential k) (infty k) z =
      -(infty k).residue (degree_infty k) ord_infty_inv_X (RatFunc.X ^ 2 * z) := by
  have hX0 : (RatFunc.X : RatFunc k) ≠ 0 := RatFunc.X_ne_zero
  -- `x²` lies in `𝔪_∞^(-2)`, so it carries `𝔪_∞^2` into the valuation ring.
  have hX2 : (RatFunc.X : RatFunc k) ^ 2 ∈ (infty k).filtration (-2) := by
    rw [mem_filtration_iff_le_ord _ (pow_ne_zero 2 hX0), ord_pow, ord_infty, RatFunc.intDegree_X]
    norm_num
  let g : RatFunc k →ₗ[k] k :=
    -((infty k).residue (degree_infty k) ord_infty_inv_X ∘ₗ
      LinearMap.mulLeft k (RatFunc.X ^ 2))
  refine LinearMap.congr_fun
    (?_ : repartitionDualComponent (ratFuncWeilDifferential k) (infty k) = g) z
  refine (infty k).linearMap_ext_zpow (degree_infty k) ord_infty_inv_X (m := 2)
    (fun w hw ↦ ?_) (fun j _ ↦ ?_)
  · -- Both sides vanish on `𝔪_∞^2`: the divisor of `η` is `-2 · P_∞`, and `x² w` is integral.
    have hint : RatFunc.X ^ 2 * w ∈ (infty k).integers := by
      simpa using (infty k).mul_mem_filtration hX2 hw
    rw [repartitionDualComponent_apply_eq_zero_of_le (isGreatest_ratFuncWeilDifferential k).1
      (infty k) (by simpa using hw)]
    simp [g, residue_eq_zero_of_mem_integers _ _ _ hint]
  · -- On `x⁻ʲ` both sides are `-1` for `j = 1` and `0` otherwise.
    have hpow : (RatFunc.X : RatFunc k) ^ 2 * (RatFunc.X⁻¹) ^ j = (RatFunc.X⁻¹) ^ (j - 2) := by
      rw [inv_zpow', inv_zpow', ← zpow_natCast, ← zpow_add₀ hX0]
      congr 1
      omega
    rw [inv_zpow', repartitionDualComponent_ratFuncWeilDifferential_zpow]
    simp only [g, LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, ← inv_zpow',
      hpow, residue_zpow_uniformizer]
    split_ifs <;> first | omega | simp

/-! ### The local components at the finite rational places -/

/-- `x - a` is a unit at every place other than `P_a` and `P_∞`, so all its integer powers are
integral there. -/
private theorem zpow_X_sub_C_mem_integers {a : k} {P : Place k (RatFunc k)}
    (ha : P ≠ adicOfIrreducible (irreducible_X_sub_C a)) (hinf : P ≠ infty k) (n : ℤ) :
    (RatFunc.X - RatFunc.C a) ^ n ∈ P.integers := by
  obtain ⟨q, hq, rfl⟩ := (eq_infty_or_exists_eq_adicOfIrreducible P).resolve_left hinf
  have hassoc : ¬Associated q (X - C a) := fun h ↦
    ha ((adicOfIrreducible_eq_adicOfIrreducible_iff hq (irreducible_X_sub_C a)).mpr h)
  rw [mem_integers_iff_ord_nonneg, ord_zpow, ord_adicOfIrreducible_X_sub_C_of_not_associated hq
    hassoc, mul_zero]

/-- The residue at infinity of `x² (x - a)ⁿ` for `n < 0`: it is `1` for `n = -1`, where
`x² / (x - a) = x + a + a² / (x - a)`, and `0` for `n ≤ -2`, where `x² (x - a)ⁿ` is integral. -/
private theorem residue_infty_X_sq_mul_X_sub_C_zpow (a : k) {n : ℤ} (hn : n < 0) :
    (infty k).residue (degree_infty k) ord_infty_inv_X
        (RatFunc.X ^ 2 * (RatFunc.X - RatFunc.C a) ^ n) =
      if n = -1 then 1 else 0 := by
  set t : RatFunc k := RatFunc.X - RatFunc.C a
  have htinf : (infty k).ord t = -1 := by
    simp only [t]
    rw [ord_infty, ← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub,
      RatFunc.intDegree_polynomial, natDegree_X_sub_C, Nat.cast_one]
  have ht0 : t ≠ 0 := by
    rintro h
    simp [h] at htinf
  split_ifs with h1
  · -- `x² / (x - a) - x = a x / (x - a)` is integral at infinity, and `x = (x⁻¹)⁻¹`.
    subst h1
    have heq : RatFunc.X ^ 2 * t ^ (-1 : ℤ) - (RatFunc.X⁻¹)⁻¹ =
        RatFunc.C a * RatFunc.X * t⁻¹ := by
      field_simp
      simp [t]
    have hint : RatFunc.X ^ 2 * t ^ (-1 : ℤ) - (RatFunc.X⁻¹)⁻¹ ∈ (infty k).integers := by
      rw [heq, mem_integers_iff_ord_nonneg]
      rcases eq_or_ne a 0 with rfl | ha0
      · simp
      have hC : RatFunc.C a ≠ 0 := by simpa using ha0
      rw [(infty k).ord_mul (mul_ne_zero hC RatFunc.X_ne_zero) (inv_ne_zero ht0),
        (infty k).ord_mul hC RatFunc.X_ne_zero, ord_inv, htinf, ord_infty, ord_infty,
        RatFunc.intDegree_C, RatFunc.intDegree_X]
      norm_num
    rw [residue_eq_of_sub_mem_integers _ _ _ hint, residue_inv_uniformizer]
  · -- For `n ≤ -2`, `x² tⁿ` is integral at infinity.
    refine residue_eq_zero_of_mem_integers _ _ _ ?_
    rw [mem_integers_iff_ord_nonneg, (infty k).ord_mul (pow_ne_zero _ RatFunc.X_ne_zero)
      (zpow_ne_zero _ ht0), ord_pow, ord_zpow, htinf, ord_infty, RatFunc.intDegree_X]
    omega

/-- The local component of `dx` at `P_a` on the powers of `x - a`: `1` on `(x - a)⁻¹` and `0`
on every other power. -/
private theorem repartitionDualComponent_ratFuncWeilDifferential_X_sub_C_zpow (a : k) (n : ℤ) :
    repartitionDualComponent (ratFuncWeilDifferential k)
        (adicOfIrreducible (irreducible_X_sub_C a)) ((RatFunc.X - RatFunc.C a) ^ n) =
      if n = -1 then 1 else 0 := by
  classical
  set Pa := adicOfIrreducible (irreducible_X_sub_C a)
  have hPa : Pa ≠ infty k := adicOfIrreducible_ne_infty _
  rcases le_or_gt 0 n with hn | hn
  · -- A nonnegative power is integral at `P_a`.
    rw [ite_eq_right (by omega)]
    refine repartitionDualComponent_ratFuncWeilDifferential_of_ne_infty hPa ?_
    rw [mem_integers_iff_ord_nonneg, ord_zpow, ord_adicOfIrreducible_X_sub_C_self]
    simpa using hn
  -- A negative power: by the abstract residue theorem only `P_a` and `P_∞` contribute, so
  -- `η_{P_a} (tⁿ) = -η_{P_∞} (tⁿ) = res_{P_∞, x⁻¹} (x² tⁿ)`.
  have hsum := finsum_repartitionDualComponent_eq_zero (IsFunctionField.ratFunc k)
    (ratFuncWeilDifferential_mem k) ((RatFunc.X - RatFunc.C a) ^ n)
  rw [finsum_eq_sum_of_support_subset _ (s := {Pa, infty k}) (fun P hP ↦ by
    by_contra hmem
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hmem
    exact hP (repartitionDualComponent_ratFuncWeilDifferential_of_ne_infty hmem.2
      (zpow_X_sub_C_mem_integers hmem.1 hmem.2 n))),
    Finset.sum_pair hPa, repartitionDualComponent_ratFuncWeilDifferential_infty,
    add_neg_eq_zero] at hsum
  rw [hsum, residue_infty_X_sq_mul_X_sub_C_zpow a hn]

/-- **The local component of `dx` at the place of `x - a` is a residue** (Stichtenoth,
Theorem 4.3.2(d), for `k(x)`): `η_{P_a} (z) = res_{P_a, x - a} (z)`, which is
`res_{P_a} (z dx)` since `dx = d(x - a)`. -/
theorem repartitionDualComponent_ratFuncWeilDifferential_adicOfIrreducible_X_sub_C (a : k)
    (z : RatFunc k) :
    repartitionDualComponent (ratFuncWeilDifferential k)
        (adicOfIrreducible (irreducible_X_sub_C a)) z =
      (adicOfIrreducible (irreducible_X_sub_C a)).residue (degree_adicOfIrreducible_X_sub_C a)
        (ord_adicOfIrreducible_X_sub_C_self a) z := by
  refine LinearMap.congr_fun ?_ z
  refine (adicOfIrreducible (irreducible_X_sub_C a)).linearMap_ext_zpow
    (degree_adicOfIrreducible_X_sub_C a) (ord_adicOfIrreducible_X_sub_C_self a) (m := 0)
    (fun w hw ↦ ?_) (fun j _ ↦ ?_)
  · -- Both sides vanish on the functions integral at `P_a`.
    rw [mem_filtration_zero_iff] at hw
    rw [repartitionDualComponent_ratFuncWeilDifferential_of_ne_infty
      (adicOfIrreducible_ne_infty _) hw, residue_eq_zero_of_mem_integers _ _ _ hw]
  · rw [repartitionDualComponent_ratFuncWeilDifferential_X_sub_C_zpow, residue_zpow_uniformizer]

/-! ### The residue theorem -/

/-- **The residue theorem for `k(x)`** (Stichtenoth, Corollary 4.3.3, for `k(x)`): if every pole
of `z` is a rational place, then the residues of `z dx` over `ℙ¹(k)` sum to zero, in the form
`∑_{a ∈ k} res_{P_a, x - a} (z) = res_{P_∞, x⁻¹} (x² z)`.

The hypothesis is needed: over `ℚ`, `z = 2x / (x² - 2)` is integral at every place `P_a`, so the
left side vanishes, while `res_{P_∞, x⁻¹} (x² z) = 2`; the missing residue sits at the place of
`x² - 2`, which has degree two. -/
theorem finsum_residue_adicOfIrreducible_X_sub_C {z : RatFunc k}
    (hz : ∀ P : Place k (RatFunc k), P.degree ≠ 1 → z ∈ P.integers) :
    ∑ᶠ a : k, (adicOfIrreducible (irreducible_X_sub_C a)).residue
        (degree_adicOfIrreducible_X_sub_C a) (ord_adicOfIrreducible_X_sub_C_self a) z =
      (infty k).residue (degree_infty k) ord_infty_inv_X (RatFunc.X ^ 2 * z) := by
  set f : Place k (RatFunc k) → k :=
    fun P ↦ repartitionDualComponent (ratFuncWeilDifferential k) P z
  set g : k → Place k (RatFunc k) := fun a ↦ adicOfIrreducible (irreducible_X_sub_C a)
  have hfin : (Function.support f).Finite := by
    simpa [f] using finite_support_repartitionDualComponent_apply (ratFuncWeilDifferential_mem k)
      ⟨_, const_mem_repartitionSpace (IsFunctionField.ratFunc k) z⟩
  -- Off the rational places, `z` is integral, so its local component vanishes.
  have hsupp : ∀ P ∈ Function.support f, P ∈ insert (infty k) (Set.range g) := by
    intro P hP
    by_contra hmem
    simp only [Set.mem_insert_iff, Set.mem_range, not_or, not_exists] at hmem
    refine hP (repartitionDualComponent_ratFuncWeilDifferential_of_ne_infty hmem.1 (hz P ?_))
    intro hdeg
    rcases eq_infty_or_exists_eq_adicOfIrreducible_X_sub_C hdeg with h | ⟨a, h⟩
    exacts [hmem.1 h, hmem.2 a h.symm]
  have hinf : infty k ∉ Set.range g := by
    rintro ⟨a, h⟩
    exact adicOfIrreducible_ne_infty _ h
  have hsum := finsum_repartitionDualComponent_eq_zero (IsFunctionField.ratFunc k)
    (ratFuncWeilDifferential_mem k) z
  rw [← finsum_mem_univ, finsum_mem_inter_support_eq' f _ _ fun P hP ↦
      iff_of_true (Set.mem_univ P) (hsupp P hP),
    finsum_mem_insert' f hinf (hfin.subset Set.inter_subset_right),
    finsum_mem_range (adicOfIrreducible_X_sub_C_injective (k := k))] at hsum
  simp only [f, repartitionDualComponent_ratFuncWeilDifferential_infty,
    repartitionDualComponent_ratFuncWeilDifferential_adicOfIrreducible_X_sub_C] at hsum
  linear_combination hsum

/-- **The residue theorem for `k(x)` over an algebraically closed field** (Stichtenoth,
Corollary 4.3.3, for `k(x)`): `∑_{a ∈ k} res_{P_a, x - a} (z) = res_{P_∞, x⁻¹} (x² z)` for every
rational function `z`. -/
theorem finsum_residue_adicOfIrreducible_X_sub_C_of_isAlgClosed [IsAlgClosed k]
    (z : RatFunc k) :
    ∑ᶠ a : k, (adicOfIrreducible (irreducible_X_sub_C a)).residue
        (degree_adicOfIrreducible_X_sub_C a) (ord_adicOfIrreducible_X_sub_C_self a) z =
      (infty k).residue (degree_infty k) ord_infty_inv_X (RatFunc.X ^ 2 * z) :=
  finsum_residue_adicOfIrreducible_X_sub_C fun P hP ↦
    absurd (P.degree_eq_one_of_isAlgClosed_of_isFunctionField (IsFunctionField.ratFunc k)) hP

end TauCeti
