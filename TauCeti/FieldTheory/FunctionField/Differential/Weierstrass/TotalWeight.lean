/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Independence
public import TauCeti.FieldTheory.FunctionField.Differential.Weierstrass.Weight
import TauCeti.FieldTheory.FunctionField.Frobenius
import TauCeti.FieldTheory.FunctionField.Place.Approximation
import TauCeti.FieldTheory.FunctionField.SeparablyGenerated

/-!
# The total Weierstrass weight is `g³ - g`

Let `F / k` be an algebraic function field with exact constant field and genus `g`, let `W` be a
canonical divisor, and let `f₁, …, f_g` be a `k`-basis of `L(W)`. At a rational place `P` with a
separating prime element `t`, the order of the Wronskian `W_t(f)` with respect to `t` is
`w(P) - g · W(P)`, where `w(P)` is the Weierstrass weight
(`TauCeti.Place.ord_wronskian_derivativeOfSeparating_basis_eq_weierstrassWeight_sub`). This file
replaces the local parameter `t` by one global separating element `x` and sums the local orders
over all places.

Changing the parameter from `t` to `x` multiplies the Wronskian by `(dt/dx) ^ (g (g - 1) / 2)`
(`TauCeti.wronskian_eq_pow_mul_wronskian_derivativeOfSeparating`), and by the chain rule
`dt = (dt/dx) · dx` the order of `dt/dx` at `P` is `v_P(dt) - v_P(dx)`. A prime element has a
differential of order zero, `v_P(dt) = 0`
(`TauCeti.weilDifferentialOrder_weilDifferentialOfSeparating_eq_zero`). Hence

`ord_P W_x(f) = w(P) - g · W(P) - (g choose 2) · v_P(dx)`

at every rational place `P` whose gaps are pairwise distinct in `k`. When every place is of this
kind, the principal divisor of `W_x(f)` is `∑_P w(P) P - g · W - (g choose 2) · (dx)`. A
principal divisor has degree zero and both `W` and `(dx)` have degree `2g - 2`, so

`∑_P w(P) = g (2g - 2) + (g choose 2) (2g - 2) = g³ - g`.

In particular only finitely many places have nonzero weight: there are finitely many
Weierstrass points, and their weights add up to `g³ - g`. The hypotheses are met over an
algebraically closed field of characteristic zero (the gap condition is then
`Nat.cast_injective.injOn`), and in characteristic `p` whenever `p ≥ 2g - 1`, since every gap
lies in `1, …, 2g - 1`.

## Main results

* `TauCeti.Place.wronskian_derivativeOfSeparating_basis_ne_zero_of_perfectField`: over a perfect
  field, the Wronskian of a canonical basis with respect to any separating element is nonzero as
  soon as the gaps at one rational place are distinct in `k`.
* `TauCeti.Place.ord_wronskian_derivativeOfSeparating_basis_eq`: the order of that Wronskian at a
  rational place, `w(P) - g · W(P) - (g choose 2) · v_P(dx)`.
* `TauCeti.Place.finite_setOf_weierstrassWeight_ne_zero`: over an algebraically closed field,
  only finitely many places have nonzero Weierstrass weight.
* `TauCeti.finsum_weierstrassWeight`: over an algebraically closed field, **the Weierstrass
  weights add up to `g³ - g`**.

## References

* D. M. Goldschmidt, *Algebraic Functions and Projective Curves*, GTM 215, Springer, 2003,
  the Wronskian treatment of Weierstrass points.
* H. M. Farkas and I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Springer, 1992, Section III.5,
  for the count `∑_P w(P) = g³ - g`.
-/

public section

open scoped IntermediateField

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-! ### The Wronskian of a canonical basis with respect to a global parameter -/

namespace Place

variable {W : Divisor k F} {g₀ : ℕ} {x : F}

/-- A canonical basis has exactly `g` elements. -/
private theorem eq_genus_of_basis (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hW : W.IsRiemannRochDivisor g₀) {n : ℕ} (b : Module.Basis (Fin n) k (riemannRochSpace W)) :
    n = genus k F := by
  have h := Module.finrank_eq_card_basis b
  rw [Fintype.card_fin, ← Divisor.dim_def, hW.dim_eq hF hex, hW.genus_eq hF hex] at h
  exact h.symm

variable (P : Place k F) (hP : P.degree = 1)

include hP in
/-- **The Wronskian of a canonical basis is nonzero, for any separating element.** Over a perfect
field, if `W` satisfies the Riemann--Roch identity and the gaps at one rational place `P` are
pairwise distinct in `k`, then the Wronskian of any `k`-basis of `L(W)` with respect to any
separating element `x` is nonzero. -/
theorem wronskian_derivativeOfSeparating_basis_ne_zero_of_perfectField [PerfectField k]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (hW : W.IsRiemannRochDivisor g₀)
    (hgaps : Set.InjOn (Nat.cast : ℕ → k) P.weierstrassGaps) (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] {n : ℕ} (b : Module.Basis (Fin n) k (riemannRochSpace W)) :
    (derivativeOfSeparating hx).wronskian (fun i ↦ (b i : F)) ≠ 0 := by
  obtain ⟨t, ht, -⟩ := P.exists_ord_eq_one_and_forall_mem_ord_eq_zero ∅
  obtain ⟨htr, hsep⟩ := P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hF ht
  rw [wronskian_eq_pow_mul_wronskian_derivativeOfSeparating htr]
  exact mul_ne_zero (pow_ne_zero _ (derivativeOfSeparating_ne_zero hx htr))
    (P.wronskian_derivativeOfSeparating_basis_ne_zero hP ht htr hF hex hW hgaps b)

include hP in
/-- **The order of the Wronskian of a canonical basis, with respect to a global separating
element.** Over a perfect field with infinitely many rational places, let `W` satisfy the
Riemann--Roch identity for a function field with exact constants and genus `g`, let `x` be a
separating element, and let `P` be a rational place whose gaps are pairwise distinct in `k`. Then
the Wronskian with respect to `x` of any `k`-basis of `L(W)` has order
`w(P) - g · W(P) - (g choose 2) · v_P(dx)` at `P`, where `w(P)` is the Weierstrass weight. -/
theorem ord_wronskian_derivativeOfSeparating_basis_eq [PerfectField k]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hinf : {Q : Place k F | Q.degree = 1}.Infinite) (hW : W.IsRiemannRochDivisor g₀)
    (hgaps : Set.InjOn (Nat.cast : ℕ → k) P.weierstrassGaps) (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] {n : ℕ} (b : Module.Basis (Fin n) k (riemannRochSpace W)) :
    P.ord ((derivativeOfSeparating hx).wronskian (fun i ↦ (b i : F))) =
      P.weierstrassWeight - (genus k F : ℤ) * W.coeff P -
        ((genus k F).choose 2 : ℤ) * weilDifferentialOrder hF hex
          (weilDifferentialOfSeparating hF hx).2
          (by simpa using weilDifferentialOfSeparating_ne_zero hF hx) P := by
  let _ := weilDifferentialSpaceModule hF
  -- Change the parameter to a separating prime element `t` at `P`.
  obtain ⟨t, ht, -⟩ := P.exists_ord_eq_one_and_forall_mem_ord_eq_zero ∅
  obtain ⟨htr, hsep⟩ := P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hF ht
  have hd0 := derivativeOfSeparating_ne_zero hx htr
  -- By the chain rule `dt = (dt/dx) · dx`, the order of `dt/dx` at `P` is `-v_P(dx)`.
  have hchain : (weilDifferentialOfSeparating hF htr : Module.Dual k ↥(repartitionSpace k F)) =
      repartitionDualMul hF (Units.mk0 _ hd0 : F) (weilDifferentialOfSeparating hF hx) := by
    rw [weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul hF hex hinf hx htr,
      coe_weilDifferentialSpaceModule_smul, Units.val_mk0]
  have hdx := weilDifferentialDivisor_repartitionDualMul hF hex
    (weilDifferentialOfSeparating hF hx).2
    (by simpa using weilDifferentialOfSeparating_ne_zero hF hx) (Units.mk0 _ hd0)
  rw [← weilDifferentialDivisor_congr hF hex hchain (weilDifferentialOfSeparating hF htr).2
    (by simpa using weilDifferentialOfSeparating_ne_zero hF htr)] at hdx
  have hord := congrArg (fun D : Divisor k F ↦ D.coeff P) hdx
  simp only [coeff_weilDifferentialDivisor,
    weilDifferentialOrder_weilDifferentialOfSeparating_eq_zero hF hex htr hP ht,
    AlgebraicGeometry.WeilDivisor.coeff_add, Divisor.coeff_principal, Units.val_mk0] at hord
  -- Assemble: `W_x(f) = (dt/dx) ^ (g choose 2) · W_t(f)`.
  have hN : n * (n - 1) / 2 = (genus k F).choose 2 := by
    rw [eq_genus_of_basis hF hex hW b, Nat.choose_two_right]
  rw [wronskian_eq_pow_mul_wronskian_derivativeOfSeparating htr, hN,
    P.ord_mul (pow_ne_zero _ hd0)
      (P.wronskian_derivativeOfSeparating_basis_ne_zero hP ht htr hF hex hW hgaps b),
    P.ord_pow, P.ord_wronskian_derivativeOfSeparating_basis_eq_weierstrassWeight_sub hP ht htr hF
      hex hW hgaps b]
  linear_combination -((genus k F).choose 2 : ℤ) * hord

end Place

/-! ### The total Weierstrass weight -/

variable [IsAlgClosed k]

/-- Over an algebraically closed field, the Weierstrass weights are the coefficients of the
divisor `div W_x(f) + g · (dx) + (g choose 2) · (dx)` of a canonical basis `f` of `L((dx))`, for a
separating element `x`. -/
private theorem exists_divisor_coeff_eq_weierstrassWeight (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F)
    (hgaps : ∀ P : Place k F, Set.InjOn (Nat.cast : ℕ → k) P.weierstrassGaps) :
    ∃ D : Divisor k F, (∀ P, D.coeff P = P.weierstrassWeight) ∧
      Divisor.degree D = genus k F * (2 * genus k F - 2) +
        (genus k F).choose 2 * (2 * genus k F - 2) := by
  obtain ⟨x, hx, hsep⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
  have hmem := (weilDifferentialOfSeparating hF hx).2
  have hne : (weilDifferentialOfSeparating hF hx : Module.Dual k ↥(repartitionSpace k F)) ≠ 0 :=
    by simpa using weilDifferentialOfSeparating_ne_zero hF hx
  set W := weilDifferentialDivisor hF hex hmem hne
  have hW := isRiemannRochDivisor_weilDifferentialDivisor hF hex hmem hne
  have hdeg (P : Place k F) : P.degree = 1 := P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF
  have hinf := Place.infinite_setOf_degree_eq_one hF
  obtain ⟨P₀⟩ := Place.nonempty hF
  have := finiteDimensional_riemannRochSpace hF W
  let b := Module.finBasis k (riemannRochSpace W)
  have h0 := P₀.wronskian_derivativeOfSeparating_basis_ne_zero_of_perfectField (hdeg P₀) hF hex hW
    (hgaps P₀) hx b
  refine ⟨Divisor.principal hF (Units.mk0 _ h0) + (genus k F : ℤ) • W +
    ((genus k F).choose 2 : ℤ) • W, fun P ↦ ?_, ?_⟩
  · rw [AlgebraicGeometry.WeilDivisor.coeff_add, AlgebraicGeometry.WeilDivisor.coeff_add,
      AlgebraicGeometry.WeilDivisor.coeff_zsmul, AlgebraicGeometry.WeilDivisor.coeff_zsmul,
      Divisor.coeff_principal, Units.val_mk0,
      P.ord_wronskian_derivativeOfSeparating_basis_eq (hdeg P) hF hex hinf hW (hgaps P) hx b,
      coeff_weilDifferentialDivisor]
    ring
  · rw [Divisor.degree_add, Divisor.degree_add, Divisor.degree_zsmul, Divisor.degree_zsmul,
      Divisor.degree_principal, degree_weilDifferentialDivisor]
    ring

namespace Place

/-- **There are finitely many Weierstrass points**: over an algebraically closed field, if the
gaps at every place of a function field are pairwise distinct in `k`, then only finitely many
places have nonzero Weierstrass weight. In characteristic zero the gap hypothesis is
`fun _ ↦ Nat.cast_injective.injOn`. -/
theorem finite_setOf_weierstrassWeight_ne_zero (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F)
    (hgaps : ∀ P : Place k F, Set.InjOn (Nat.cast : ℕ → k) P.weierstrassGaps) :
    {P : Place k F | P.weierstrassWeight ≠ 0}.Finite := by
  obtain ⟨D, hD, -⟩ := exists_divisor_coeff_eq_weierstrassWeight hF hex hgaps
  refine D.support.finite_toSet.subset fun P hP ↦ ?_
  rw [Finset.mem_coe, AlgebraicGeometry.WeilDivisor.mem_support_iff, hD]
  exact_mod_cast hP

end Place

/-- **The Weierstrass weights add up to `g³ - g`.** Over an algebraically closed field, if the
gaps at every place of a function field with exact constants and genus `g` are pairwise distinct
in `k`, then the sum of the Weierstrass weights of all places, a sum with finitely many nonzero
terms (`TauCeti.Place.finite_setOf_weierstrassWeight_ne_zero`), is `g³ - g`. In characteristic
zero the gap hypothesis is `fun _ ↦ Nat.cast_injective.injOn`. -/
theorem finsum_weierstrassWeight (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hgaps : ∀ P : Place k F, Set.InjOn (Nat.cast : ℕ → k) P.weierstrassGaps) :
    ∑ᶠ P : Place k F, P.weierstrassWeight = genus k F ^ 3 - genus k F := by
  obtain ⟨D, hD, hdeg⟩ := exists_divisor_coeff_eq_weierstrassWeight hF hex hgaps
  -- The sum of the weights is the degree of `D`, since every place has degree one.
  have hsum : ((∑ᶠ P : Place k F, P.weierstrassWeight : ℕ) : ℤ) = Divisor.degree D := by
    rw [finsum_eq_sum_of_support_subset _ (s := D.support) fun P hP ↦ by
        rw [Finset.mem_coe, AlgebraicGeometry.WeilDivisor.mem_support_iff, hD]
        exact_mod_cast hP,
      Divisor.degree_eq_sum_support, Nat.cast_sum]
    refine Finset.sum_congr rfl fun P _ ↦ ?_
    rw [P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF, Nat.cast_one, mul_one]
    simpa only [AlgebraicGeometry.WeilDivisor.coeff] using (hD P).symm
  have hchoose : ((genus k F).choose 2 : ℤ) * 2 = genus k F * (genus k F - 1) := by
    have h := Nat.cast_choose_two ℚ (genus k F)
    field_simp at h
    exact_mod_cast h
  rw [← Nat.cast_inj (R := ℤ), hsum, hdeg,
    Nat.cast_sub (Nat.le_self_pow (by norm_num) _), Nat.cast_pow]
  linear_combination (genus k F - 1 : ℤ) * hchoose

end TauCeti
