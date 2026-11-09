/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.NoncrossingPartition.Mobius
public import TauCeti.Combinatorics.NoncrossingPartition.PowerSeries

/-!
# Boxed convolution of formal power series

The *boxed convolution* of two formal power series `f = ∑ fₙ zⁿ` and `g = ∑ gₙ zⁿ` is the power
series whose coefficient of index `n ≥ 1` is the sum over the noncrossing partitions `π` of `n`
ordered positions

`∑_{π ∈ NC(n)} (∏_{B ∈ π} f_{|B|}) (∏_{B ∈ K(π)} g_{|B|})`,

where `K(π)` is the Kreweras complement of `π`, and whose constant coefficient is `f₀ g₀`. The
sums only involve the coefficients of index at least `1`; the constant coefficient is chosen so
that `1 + z` is a two-sided unit on all power series, and the series with constant coefficient
`0` (Nica and Speicher's convention) and those with constant coefficient `1` (the convention of
free cumulant series `1 + z R(z)`) are both closed under it.

In free probability, the free cumulant series of the product `a b` of two free elements is the
boxed convolution of their free cumulant series, and boxed convolution with `∑ zⁿ` turns free
cumulants into moments. This file develops the operation itself:

* it is commutative, because the Kreweras complement is a bijection of `NC(n)` whose square is a
  rotation, which preserves the sizes of the parts;
* `1 + z` is its unit, because `K(π)` is the partition into singletons only for `π = 1_n`;
* if `C(0) = 1` and `M(z) = C(z M(z))`, then the boxed convolution of `C` with the *zeta series*
  `∑_{n ≥ 0} zⁿ` is `M`;
* the boxed convolution of the zeta series with the *Möbius series*
  `∑_{n ≥ 0} (-1)^(n-1) C_(n-1) zⁿ` (whose constant coefficient is `1`) is `1 + z`: by the
  blockwise formula for the Möbius function `μ` of `NC(n)`, its coefficient of index `n ≥ 1` is
  `∑_{π ∈ NC(n)} μ(0_n, K(π)) = ∑_{σ ∈ NC(n)} μ(0_n, σ)`, which vanishes unless `n = 1`.

## Main definitions

* `PowerSeries.boxedConvolution f g` — the boxed convolution of `f` and `g`.

## Main results

* `PowerSeries.coeff_boxedConvolution` and `PowerSeries.constantCoeff_boxedConvolution` — its
  coefficients, with `PowerSeries.coeff_one_boxedConvolution` for the linear coefficient
  `f₁ g₁`.
* `PowerSeries.boxedConvolution_comm` — commutativity.
* `PowerSeries.boxedConvolution_one_add_X` and `PowerSeries.one_add_X_boxedConvolution` — `1 + z`
  is a two-sided unit.
* `PowerSeries.boxedConvolution_mk_one_eq_of_subst_eq` — the zeta series turns `C` into the
  solution `M` of `M(z) = C(z M(z))`.
* `PowerSeries.boxedConvolution_mk_one_mobius` — the zeta series and the Möbius series are
  inverse to each other.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 17 and 18
  (boxed convolution, its unit, and the zeta and Möbius series).
* A. Nica, R. Speicher, *A "Fourier transform" for multiplicative functions on non-crossing
  partitions*, J. Algebraic Combin. 6 (1997), 141–160.
-/

public section

open Finset IncidenceAlgebra TauCeti TauCeti.NoncrossingPartition

namespace PowerSeries

variable {R : Type*}

section CommSemiring

variable [CommSemiring R]

/-- The *boxed convolution* of the power series `f` and `g`: its coefficient of index `n ≥ 1` is
`∑_{π ∈ NC(n)} (∏_{B ∈ π} f_{|B|}) (∏_{B ∈ K(π)} g_{|B|})`, with `K(π)` the Kreweras complement
of `π`, and its constant coefficient is `f₀ g₀`. -/
noncomputable def boxedConvolution (f g : R⟦X⟧) : R⟦X⟧ :=
  mk fun n => if n = 0 then constantCoeff f * constantCoeff g else
    ∑ π : NoncrossingPartition (univ : Finset (Fin n)),
      (∏ B ∈ π.1.parts, coeff #B f) * ∏ B ∈ (kreweras π).1.parts, coeff #B g

/-- The coefficient of index `n ≥ 1` of the boxed convolution of `f` and `g` is
`∑_{π ∈ NC(n)} (∏_{B ∈ π} f_{|B|}) (∏_{B ∈ K(π)} g_{|B|})`. -/
theorem coeff_boxedConvolution {n : ℕ} (hn : n ≠ 0) (f g : R⟦X⟧) :
    coeff n (boxedConvolution f g) =
      ∑ π : NoncrossingPartition (univ : Finset (Fin n)),
        (∏ B ∈ π.1.parts, coeff #B f) * ∏ B ∈ (kreweras π).1.parts, coeff #B g := by
  rw [boxedConvolution, coeff_mk, ite_eq_right hn]

/-- The constant coefficient of the boxed convolution of `f` and `g` is `f₀ g₀`. -/
@[simp]
theorem constantCoeff_boxedConvolution (f g : R⟦X⟧) :
    constantCoeff (boxedConvolution f g) = constantCoeff f * constantCoeff g := by
  rw [← coeff_zero_eq_constantCoeff_apply, boxedConvolution, coeff_mk, ite_eq_left rfl]

/-- The linear coefficient of the boxed convolution of `f` and `g` is `f₁ g₁`. -/
@[simp]
theorem coeff_one_boxedConvolution (f g : R⟦X⟧) :
    coeff 1 (boxedConvolution f g) = coeff 1 f * coeff 1 g := by
  -- `NC(1)` has the single element `⊥ = ⊤`, whose Kreweras complement is `⊤ = ⊥`.
  have hbt : (⊥ : NoncrossingPartition (univ : Finset (Fin 1))) = ⊤ :=
    bot_eq_top_iff_card_le_one.2 (by simp)
  rw [coeff_boxedConvolution one_ne_zero,
    Fintype.sum_eq_single ⊥ fun π hπ => absurd (le_bot_iff.1 (hbt ▸ le_top)) hπ, kreweras_bot,
    ← hbt]
  simp

/-- *Commutativity of boxed convolution*. -/
theorem boxedConvolution_comm (f g : R⟦X⟧) : boxedConvolution f g = boxedConvolution g f := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [mul_comm]
  rw [coeff_boxedConvolution hn, coeff_boxedConvolution hn]
  -- Reindex the sum by the Kreweras complement.
  exact Fintype.sum_bijective kreweras kreweras_bijective _ _ fun π => by
    rw [prod_parts_kreweras_kreweras π fun k => coeff k f, mul_comm]

/-- The coefficients of `1 + z` of positive index are `1` at index `1` and `0` elsewhere, so their
products over the parts of a noncrossing partition detect the partition into singletons. -/
private theorem prod_parts_coeff_one_add_X {α : Type*} [LinearOrder α] {s : Finset α}
    (σ : NoncrossingPartition s) :
    ∏ B ∈ σ.1.parts, coeff #B (1 + X : R⟦X⟧) = if σ = ⊥ then 1 else 0 := by
  rw [prod_congr rfl fun B hB => show coeff #B (1 + X : R⟦X⟧) = if #B = 1 then 1 else 0 by
    simp [coeff_one, coeff_X, (σ.1.nonempty_of_mem_parts hB).card_pos.ne'], prod_boole]
  exact if_congr (by rw [← Finpartition.eq_bot_iff_forall_card_eq_one, ← coe_bot, Subtype.coe_inj])
    rfl rfl

/-- `1 + z` is a right unit for boxed convolution. -/
@[simp]
theorem boxedConvolution_one_add_X (f : R⟦X⟧) : boxedConvolution f (1 + X) = f := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hne : (univ : Finset (Fin n)) ≠ ∅ := univ_eq_empty_iff.not.2 (not_isEmpty_of_nonempty
    (Fin n) (h := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩))
  -- Only `π = 1_n`, whose Kreweras complement is the partition into singletons, contributes.
  have hK (π : NoncrossingPartition (univ : Finset (Fin n))) : kreweras π = ⊥ ↔ π = ⊤ := by
    rw [← kreweras_top, kreweras_inj]
  simp only [coeff_boxedConvolution hn, prod_parts_coeff_one_add_X, hK, mul_ite, mul_one,
    mul_zero, Fintype.sum_ite_eq', coe_top, Finpartition.parts_top hne, prod_singleton, card_univ,
    Fintype.card_fin]

/-- `1 + z` is a left unit for boxed convolution. -/
@[simp]
theorem one_add_X_boxedConvolution (f : R⟦X⟧) : boxedConvolution (1 + X) f = f := by
  rw [boxedConvolution_comm, boxedConvolution_one_add_X]

end CommSemiring

section CommRing

variable [CommRing R]

/-- *Boxed convolution with the zeta series* `∑_{n ≥ 0} zⁿ`: if `C(0) = 1` and
`M(z) = C(z M(z))`, then the boxed convolution of `C` with the zeta series is `M`. In free
probability, `C` is the free cumulant series and `M` the moment series of a variable. -/
theorem boxedConvolution_mk_one_eq_of_subst_eq {C M : R⟦X⟧} (hC : constantCoeff C = 1)
    (hM : C.subst (X * M) = M) : boxedConvolution C (mk 1) = M := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · -- The constant coefficient of `M` is the weight `1` of the empty partition.
    have h := sum_prod_coeff_eq_coeff_of_subst_eq hC hM (∅ : Finset ℕ)
    rw [Fintype.sum_unique, Finpartition.parts_eq_empty_iff.2 rfl, prod_empty, card_empty] at h
    rw [← h]
    simp [hC]
  simp only [coeff_boxedConvolution hn, coeff_mk, Pi.one_apply, prod_const_one, mul_one]
  rw [sum_prod_coeff_eq_coeff_of_subst_eq hC hM, card_univ, Fintype.card_fin]

/-- *The zeta series and the Möbius series are inverse for boxed convolution*: the boxed
convolution of `∑_{n ≥ 0} zⁿ` with `∑_{n ≥ 0} (-1)^(n-1) C_(n-1) zⁿ` is `1 + z`. Here `C_k` is
the `k`-th Catalan number, and the constant coefficient of the second series is
`(-1)^0 C_0 = 1`, as `0 - 1 = 0` in `ℕ`. -/
theorem boxedConvolution_mk_one_mobius :
    boxedConvolution (mk 1) (mk fun n => (-1) ^ (n - 1) * (catalan (n - 1) : R)) = 1 + X := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  -- The `π`-th term is `μ(0_n, K(π))`, and these values sum to `0` over `NC(n)` unless
  -- `0_n = 1_n`, that is, `n = 1`.
  simp only [coeff_boxedConvolution hn, coeff_mk, Pi.one_apply, prod_const_one, one_mul,
    ← mu_bot_eq_prod]
  rw [Fintype.sum_bijective kreweras kreweras_bijective (fun π => mu R ⊥ (kreweras π))
      (mu R ⊥) fun _ => rfl,
    ← Icc_bot_top (α := NoncrossingPartition (univ : Finset (Fin n))), sum_Icc_mu_right]
  simp [coeff_one, coeff_X, hn, bot_eq_top_iff_card_le_one, Nat.le_one_iff_eq_zero_or_eq_one]

end CommRing

end PowerSeries
