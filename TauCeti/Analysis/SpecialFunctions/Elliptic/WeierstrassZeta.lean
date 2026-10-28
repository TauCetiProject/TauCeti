/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The Weierstrass `ζ` function

For a pair of periods `L` with lattice `Λ`, the Weierstrass `ζ` function is
`ζ(z) = 1 / z + ∑_{l ∈ Λ, l ≠ 0} (1 / (z - l) + 1 / l + z / l²)`
(`PeriodPair.weierstrassZeta`), the series converging absolutely and locally uniformly in `z`,
since its terms are `z² / (l² (z - l)) = O(|l|⁻³)`. It is holomorphic away from `Λ` with
`ζ' = -℘`, and it is odd.

Unlike `℘`, the function `ζ` is not periodic: it is *quasi-periodic*. Since `ζ(z + l) - ζ(z)` has
derivative `℘(z) - ℘(z + l) = 0` on the connected open set `ℂ ∖ Λ`, it is a constant `η(l)`, the
quasi-period of `l` (`PeriodPair.quasiPeriod`), and `η : Λ → ℂ` is additive. At a lattice point
`l`, a pole of `ζ`, the defining series takes the value `η(l)`, so the quasi-periodicity holds at
every `z`, and, as `ζ` is odd, `η(l) = 2 ζ(l / 2)` for every `l ∈ Λ`.

The values of `ζ` at the `N`-division points of `ℤ z + ℤ`, corrected by the quasi-periods so as
to depend only on the division point modulo the lattice, are the building blocks of the weight-one
Eisenstein series of level `Γ(N)`, as the values of `℘` are in weight two.

## Main definitions

* `PeriodPair.weierstrassZeta`: the Weierstrass `ζ` function of `L`.
* `PeriodPair.quasiPeriod`: the quasi-periods `η : Λ →+ ℂ` of `ζ`.

## Main results

* `PeriodPair.weierstrassZeta_bound`: the terms of the series are `O(|l|⁻³)` on balls.
* `PeriodPair.hasSumLocallyUniformly_weierstrassZeta`, `PeriodPair.hasSum_weierstrassZeta`: the
  series converges locally uniformly to `ζ`.
* `PeriodPair.hasDerivAt_weierstrassZeta`: `ζ' = -℘` away from `Λ`.
* `PeriodPair.differentiableOn_weierstrassZeta`: `ζ` is holomorphic away from `Λ`.
* `PeriodPair.weierstrassZeta_neg`: `ζ` is odd.
* `PeriodPair.weierstrassZeta_coe`: the junk value `ζ(l) = η(l)` at a lattice point.
* `PeriodPair.weierstrassZeta_add_coe`: the quasi-periodicity `ζ(z + l) = ζ(z) + η(l)`.
* `PeriodPair.quasiPeriod_eq_intCast_mul_add`: `η(m ω₁ + n ω₂) = m η(ω₁) + n η(ω₂)`.
* `PeriodPair.quasiPeriod_eq_two_mul_weierstrassZeta`: `η(l) = 2 ζ(l / 2)`.

## References

* M. Abramowitz and I. A. Stegun, *Handbook of mathematical functions*, Chapter 18.
* *NIST Digital Library of Mathematical Functions*, §23.2.
* The convergence and differentiability arguments follow those for Mathlib's
  `PeriodPair.weierstrassP` (Andrew Yang).
-/

public section

noncomputable section

open Filter
open scoped Topology PeriodPair

namespace PeriodPair

variable (L : PeriodPair)

/-- The **Weierstrass `ζ` function** of the lattice `Λ` of `L`,
`ζ(z) = 1 / z + ∑_{l ∈ Λ, l ≠ 0} (1 / (z - l) + 1 / l + z / l²)`. With the convention
`1 / 0 = 0`, the term `l = 0` of the series below is `1 / z`. At the points of `Λ` the value is
junk. -/
def weierstrassZeta (z : ℂ) : ℂ := ∑' l : L.lattice, (1 / (z - l) + 1 / l + z / l ^ 2)

/-- The terms `1 / (s - l) + 1 / l + s / l² = s² / (l² (s - l))` of the series of `ζ` are
`O(|l|⁻³)`, uniformly for `s` in a ball. -/
lemma weierstrassZeta_bound {r : ℝ} {s : ℂ} (hs : ‖s‖ < r) {l : ℂ} (h : 2 * r ≤ ‖l‖) :
    ‖1 / (s - l) + 1 / l + s / l ^ 2‖ ≤ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ) := by
  have hl : 0 < ‖l‖ := by linarith [norm_nonneg s]
  have hl0 : l ≠ 0 := norm_pos_iff.mp hl
  have hsl : ‖l‖ / 2 ≤ ‖s - l‖ := by
    rw [norm_sub_rev]
    linarith [norm_sub_norm_le l s]
  have hsl0 : s - l ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hsl
    linarith
  have key : 1 / (s - l) + 1 / l + s / l ^ 2 = s ^ 2 / (l ^ 2 * (s - l)) := by
    field_simp
    ring
  rw [key, norm_div, norm_mul, norm_pow, norm_pow, Real.rpow_neg hl.le]
  calc ‖s‖ ^ 2 / (‖l‖ ^ 2 * ‖s - l‖) ≤ r ^ 2 / (‖l‖ ^ 2 * (‖l‖ / 2)) := by gcongr
    _ = 2 * r ^ 2 * (‖l‖ ^ (3 : ℝ))⁻¹ := by
      norm_cast
      field_simp

/-- The series of `ζ` converges locally uniformly on `ℂ`. -/
theorem hasSumLocallyUniformly_weierstrassZeta :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : ℂ) ↦ 1 / (z - l) + 1 / l + z / l ^ 2)
      L.weierstrassZeta := by
  refine L.hasSumLocallyUniformly_aux (u := (2 * · ^ 2 * ‖·‖ ^ (-3 : ℝ))) _
    (fun _ _ ↦ (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r _ ↦
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  exact weierstrassZeta_bound hs h

/-- The series of `ζ` converges to `ζ`. -/
theorem hasSum_weierstrassZeta (z : ℂ) :
    HasSum (fun l : L.lattice ↦ 1 / (z - l) + 1 / l + z / l ^ 2) (L.weierstrassZeta z) :=
  L.hasSumLocallyUniformly_weierstrassZeta.hasSum

/-- The derivative of a term of the series of `ζ`, away from its pole. -/
private lemma hasDerivAt_weierstrassZeta_term {l z : ℂ} (hz : z ≠ l) :
    HasDerivAt (fun w ↦ 1 / (w - l) + 1 / l + w / l ^ 2) (-(1 / (z - l) ^ 2 - 1 / l ^ 2)) z := by
  have h := ((((hasDerivAt_id z).sub_const l).inv (sub_ne_zero.mpr hz)).add_const
    (1 / l)).add ((hasDerivAt_id z).div_const (l ^ 2))
  convert h using 1
  · ext w
    simp
  · simp only [id_eq, one_div]
    ring

/-- **`ζ' = -℘`** away from the lattice. -/
theorem hasDerivAt_weierstrassZeta {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassZeta (-℘[L] z) z := by
  have hU : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  have hterm (l : L.lattice) {w : ℂ} (hw : w ∉ L.lattice) : w ≠ l := fun h ↦ hw (h ▸ l.2)
  -- the partial sums of the series and their derivatives
  let F (s : Finset L.lattice) (w : ℂ) : ℂ := ∑ l ∈ s, (1 / (w - l) + 1 / (l : ℂ) + w / l ^ 2)
  have hF (s : Finset L.lattice) {w : ℂ} (hw : w ∉ L.lattice) :
      HasDerivAt (F s) (∑ l ∈ s, -(1 / (w - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2)) w :=
    HasDerivAt.fun_sum fun l _ ↦ hasDerivAt_weierstrassZeta_term (hterm l hw)
  have hdiff (s : Finset L.lattice) : DifferentiableOn ℂ (F s) (L.lattice : Set ℂ)ᶜ :=
    fun w hw ↦ (hF s hw).differentiableAt.differentiableWithinAt
  have hζ := L.hasSumLocallyUniformly_weierstrassZeta.tendstoLocallyUniformlyOn
    (s := (L.lattice : Set ℂ)ᶜ)
  -- the derivatives of the partial sums tend to `ζ'(z)`, and they are the partial sums of `-℘`
  have hD := (hζ.deriv (.of_forall hdiff) hU).tendsto_at hz
  have hP : Tendsto (fun s ↦ deriv (F s) z) atTop (𝓝 (-℘[L] z)) := by
    refine Tendsto.congr (fun s ↦ ((hF s hz).deriv).symm) ?_
    exact (L.hasSum_weierstrassP z).neg
  rw [← tendsto_nhds_unique hD hP]
  exact ((hζ.differentiableOn (.of_forall hdiff) hU) z hz).differentiableAt
    (hU.mem_nhds hz) |>.hasDerivAt

/-- `ζ` is holomorphic away from the lattice. -/
theorem differentiableOn_weierstrassZeta :
    DifferentiableOn ℂ L.weierstrassZeta (L.lattice : Set ℂ)ᶜ :=
  fun _ hz ↦ (L.hasDerivAt_weierstrassZeta hz).differentiableAt.differentiableWithinAt

/-- **`ζ` is odd.** -/
@[simp]
theorem weierstrassZeta_neg (z : ℂ) : L.weierstrassZeta (-z) = -L.weierstrassZeta z := by
  rw [weierstrassZeta, weierstrassZeta, ← (Equiv.neg L.lattice).tsum_eq, ← tsum_neg]
  congr with l
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, neg_sq, one_div, div_neg, neg_div]
  rw [neg_sub_neg, ← neg_sub, inv_neg]
  ring

/-- `ζ(0) = 0`, as `ζ` is odd. -/
@[simp]
theorem weierstrassZeta_zero : L.weierstrassZeta 0 = 0 :=
  CharZero.eq_neg_self_iff.mp (by simpa using L.weierstrassZeta_neg 0)

/-- Away from the lattice, `ζ(z + l) - ζ(z)` does not depend on `z`: its derivative
`℘(z) - ℘(z + l)` vanishes on the connected open set `ℂ ∖ Λ`. This is subsumed by
`PeriodPair.weierstrassZeta_add_coe`. -/
private theorem weierstrassZeta_add_coe_sub_eq (l : L.lattice) {z w : ℂ} (hz : z ∉ L.lattice)
    (hw : w ∉ L.lattice) :
    L.weierstrassZeta (z + l) - L.weierstrassZeta z =
      L.weierstrassZeta (w + l) - L.weierstrassZeta w := by
  have hmaps (x : ℂ) (hx : x ∉ L.lattice) : x + l ∉ L.lattice := fun h ↦
    hx (by simpa using sub_mem h l.2)
  have hconn : IsPreconnected (L.lattice : Set ℂ)ᶜ :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).2
  have hderiv (x : ℂ) (hx : x ∉ L.lattice) :
      HasDerivAt (fun x ↦ L.weierstrassZeta (x + l) - L.weierstrassZeta x) 0 x := by
    simpa using ((L.hasDerivAt_weierstrassZeta (hmaps x hx)).comp_add_const x l).fun_sub
      (L.hasDerivAt_weierstrassZeta hx)
  exact L.isClosed_lattice.isOpen_compl.is_const_of_deriv_eq_zero hconn
    (fun x hx ↦ (hderiv x hx).differentiableAt.differentiableWithinAt)
    (fun x hx ↦ (hderiv x hx).deriv) hz hw

/-- The **quasi-periods** of the Weierstrass `ζ` function: `η(l)` is the constant value of
`ζ(z + l) - ζ(z)` (`PeriodPair.weierstrassZeta_add_coe`). It is additive in `l`. -/
def quasiPeriod : L.lattice →+ ℂ where
  toFun l := L.weierstrassZeta (L.ω₁ / 2 + l) - L.weierstrassZeta (L.ω₁ / 2)
  map_zero' := by simp
  map_add' l l' := by
    have h₀ : L.ω₁ / 2 + l ∉ L.lattice := fun h ↦
      L.ω₁_div_two_notMem_lattice (by simpa using sub_mem h l.2)
    rw [Submodule.coe_add, ← add_assoc,
      ← sub_add_sub_cancel _ (L.weierstrassZeta (L.ω₁ / 2 + l)),
      L.weierstrassZeta_add_coe_sub_eq l' h₀ L.ω₁_div_two_notMem_lattice, add_comm]

private lemma quasiPeriod_apply (l : L.lattice) :
    L.quasiPeriod l = L.weierstrassZeta (L.ω₁ / 2 + l) - L.weierstrassZeta (L.ω₁ / 2) :=
  (rfl)

/-- `ζ(z + l) = ζ(z) + ζ(l)` for every `z` and `l ∈ Λ`: reindexing the series of `ζ(z + l)` by
`w ↦ w + l` gives `ζ(z + l) = ζ(z) + ζ(l) + (z + l) ℘(l)`, and `℘(l) = 0`. -/
private theorem weierstrassZeta_add_coe_eq_add (z : ℂ) (l : L.lattice) :
    L.weierstrassZeta (z + l) = L.weierstrassZeta z + L.weierstrassZeta l := by
  have hζ := (Equiv.neg L.lattice).hasSum_iff.mpr (L.hasSum_weierstrassZeta l)
  have h℘ := ((Equiv.neg L.lattice).hasSum_iff.mpr (L.hasSum_weierstrassP l)).mul_left (z + l)
  have h := ((L.hasSum_weierstrassZeta z).add hζ).add h℘
  have hshift := (Equiv.addRight l).hasSum_iff.mpr (L.hasSum_weierstrassZeta (z + l))
  suffices H : L.weierstrassZeta (z + l) =
      L.weierstrassZeta z + L.weierstrassZeta l + (z + l) * ℘[L] l by simpa using H
  refine hshift.unique (h.congr_fun fun w ↦ ?_)
  simp only [Function.comp_apply, Equiv.coe_addRight, Equiv.neg_apply, Submodule.coe_neg,
    Submodule.coe_add, add_sub_add_right_eq_sub, sub_neg_eq_add, inv_neg, neg_sq, div_eq_mul_inv]
  ring

/-- **The value of `ζ` at a lattice point is the quasi-period**: `ζ(l) = η(l)`. The lattice
points are the poles of `ζ`, so this is a junk value (compare `PeriodPair.weierstrassP_coe`); it
is the constant term of the Laurent expansion of `ζ` at `l`. -/
@[simp]
theorem weierstrassZeta_coe (l : L.lattice) : L.weierstrassZeta l = L.quasiPeriod l := by
  rw [quasiPeriod_apply, L.weierstrassZeta_add_coe_eq_add, add_sub_cancel_left]

/-- **The quasi-periodicity of `ζ`**: `ζ(z + l) = ζ(z) + η(l)` for every `z` and `l ∈ Λ`. -/
@[simp]
theorem weierstrassZeta_add_coe (z : ℂ) (l : L.lattice) :
    L.weierstrassZeta (z + l) = L.weierstrassZeta z + L.quasiPeriod l := by
  rw [L.weierstrassZeta_add_coe_eq_add, weierstrassZeta_coe]

/-- `ζ(z - l) = ζ(z) - η(l)` for every `z` and `l ∈ Λ`. -/
@[simp]
theorem weierstrassZeta_sub_coe (z : ℂ) (l : L.lattice) :
    L.weierstrassZeta (z - l) = L.weierstrassZeta z - L.quasiPeriod l := by
  rw [eq_sub_iff_add_eq, ← weierstrassZeta_add_coe, sub_add_cancel]

/-- The quasi-periods are determined by those of the two periods: if `l = m ω₁ + n ω₂`, then
`η(l) = m η(ω₁) + n η(ω₂)`. -/
theorem quasiPeriod_eq_intCast_mul_add (l : L.lattice) {m n : ℤ}
    (h : m * L.ω₁ + n * L.ω₂ = l) :
    L.quasiPeriod l = m * L.quasiPeriod ⟨L.ω₁, L.ω₁_mem_lattice⟩ +
      n * L.quasiPeriod ⟨L.ω₂, L.ω₂_mem_lattice⟩ := by
  have hl : l = m • (⟨L.ω₁, L.ω₁_mem_lattice⟩ : L.lattice) + n • ⟨L.ω₂, L.ω₂_mem_lattice⟩ :=
    Subtype.ext (by simp [← h, zsmul_eq_mul])
  rw [hl, map_add, map_zsmul, map_zsmul, zsmul_eq_mul, zsmul_eq_mul]

/-- Since `ζ` is odd, `η(l) = 2 ζ(l / 2)` for every `l ∈ Λ`. -/
theorem quasiPeriod_eq_two_mul_weierstrassZeta (l : L.lattice) :
    L.quasiPeriod l = 2 * L.weierstrassZeta (l / 2) := by
  have h := L.weierstrassZeta_add_coe (-((l : ℂ) / 2)) l
  rw [neg_add_eq_sub, sub_half, weierstrassZeta_neg] at h
  linear_combination -h

end PeriodPair
