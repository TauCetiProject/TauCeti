/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import TauCeti.Algebra.Category.ModuleCat.Tower.ProZero
import Mathlib.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# `lim` and `lim¹` of the multiplication-by-`p` tower

Let `p` be a prime and consider the tower of integers `ℤ ← ℤ ← ℤ ← ⋯` whose transition maps are
multiplication by `p`, `ModuleTower.multiplicationTower (p : ℤ)`. Its limit vanishes
(`ModuleTower.lim_multiplicationTower_eq_bot`), but its first derived limit is the nonzero group
`ℤ_p ⧸ ℤ`: sending a family `(aₙ)` to the `p`-adically convergent sum `∑ₙ pⁿ aₙ` induces an
isomorphism `lim¹ ≃ ℤ_[p] ⧸ ℤ`. Consequently the tower is not Mittag-Leffler, so the hypothesis
of `ModuleTower.subsingleton_limOne_of_isMittagLeffler` cannot be dropped. The tower is the basic
example of a nonvanishing `lim¹`: for instance the degree-zero homology of the tower of complexes
`ℤ → ℤ/pⁿ⁺¹` is the multiplication-by-`p` tower (up to isomorphism), and its `lim¹` appears in the
Milnor sequence of that tower.

## Main declarations

* `TauCeti.ModuleTower.padicSum`: the `p`-adic summation map `(aₙ) ↦ ∑ₙ pⁿ aₙ` on the product of the
  terms, with `TauCeti.ModuleTower.hasSum_padicSum`.
* `TauCeti.ModuleTower.padicSum_shift`: the telescoping identity `∑ₙ pⁿ (xₙ - p xₙ₊₁) = x₀`.
* `TauCeti.ModuleTower.padicSum_surjective`: every `p`-adic integer is such a sum.
* `TauCeti.ModuleTower.mem_range_shift_multiplicationTower_iff`: a family lies in the image of the
  shift map iff its `p`-adic sum is an integer.
* `TauCeti.ModuleTower.limOneMultiplicationTowerEquiv`: the isomorphism `lim¹ ≃ ℤ_[p] ⧸ ℤ`.
* `TauCeti.ModuleTower.not_isMittagLeffler_multiplicationTower`: the tower is not Mittag-Leffler.

## References

* C. A. Weibel, *An introduction to homological algebra*, §3.5.
* [Stacks: More on Algebra, Lemma 15.88.1, Tag 07KW](https://stacks.math.columbia.edu/tag/07KW)
-/

public section

noncomputable section

namespace TauCeti

namespace ModuleTower

variable (p : ℕ) [Fact p.Prime]

/-- The `p`-adic summation map `(aₙ) ↦ ∑ₙ pⁿ aₙ` from the product of the terms of the
multiplication-by-`p` tower of integers to `ℤ_[p]`. -/
def padicSum : (multiplicationTower (p : ℤ)).Product →+ ℤ_[p] :=
  AddMonoidHom.mk' (fun a ↦
    ∑' n, (p : ℤ_[p]) ^ n * (multiplicationTowerProductEquiv (p : ℤ) a n : ℤ_[p])) fun a b ↦ by
    simp only [map_add, Pi.add_apply, Int.cast_add, mul_add]
    exact (PadicInt.summable_pow_mul _).tsum_add (PadicInt.summable_pow_mul _)

theorem padicSum_apply (a : (multiplicationTower (p : ℤ)).Product) :
    padicSum p a =
      ∑' n, (p : ℤ_[p]) ^ n * (multiplicationTowerProductEquiv (p : ℤ) a n : ℤ_[p]) :=
  (rfl)

/-- The series `∑ₙ pⁿ aₙ` converges in `ℤ_[p]` to `padicSum p a`. -/
theorem hasSum_padicSum (a : (multiplicationTower (p : ℤ)).Product) :
    HasSum (fun n ↦ (p : ℤ_[p]) ^ n * (multiplicationTowerProductEquiv (p : ℤ) a n : ℤ_[p]))
      (padicSum p a) :=
  (PadicInt.summable_pow_mul _).hasSum

/-- **Telescoping**: the `p`-adic sum of the shift of a family `x` is its zeroth term,
`∑ₙ pⁿ (xₙ - xₙ₊₁ p) = x₀`. -/
@[simp]
theorem padicSum_shift (x : (multiplicationTower (p : ℤ)).Product) :
    padicSum p ((multiplicationTower (p : ℤ)).shift x) =
      (multiplicationTowerProductEquiv (p : ℤ) x 0 : ℤ_[p]) := by
  set e := multiplicationTowerProductEquiv (p : ℤ)
  set f : ℕ → ℤ_[p] := fun n ↦ (p : ℤ_[p]) ^ n * (e x n : ℤ_[p])
  have hf : Summable f := PadicInt.summable_pow_mul _
  have hf' : Summable fun n ↦ f (n + 1) := (summable_nat_add_iff 1).2 hf
  have hterm (n : ℕ) : (p : ℤ_[p]) ^ n * (e ((multiplicationTower (p : ℤ)).shift x) n : ℤ_[p]) =
      f n - f (n + 1) := by
    rw [multiplicationTowerProductEquiv_shift]
    push_cast [f]
    ring
  rw [padicSum_apply, tsum_congr hterm, hf.tsum_sub hf', hf.tsum_eq_zero_add, add_sub_cancel_right]
  simp [f]

/-- **Every `p`-adic integer is a `p`-adic sum** `∑ₙ pⁿ aₙ` of integers: take for `aₙ` the
`n`-th base-`p` digit, read off from the truncations `PadicInt.appr`. -/
theorem padicSum_surjective : Function.Surjective (padicSum p) := by
  intro z
  have hd (n : ℕ) : p ^ n ∣ z.appr (n + 1) - z.appr n :=
    PadicInt.dvd_appr_sub_appr z n (n + 1) n.le_succ
  let a := (multiplicationTowerProductEquiv (p : ℤ)).symm fun n ↦
    (((z.appr (n + 1) - z.appr n) / p ^ n : ℕ) : ℤ)
  have hpartial (N : ℕ) : ∑ n ∈ Finset.range N,
      (p : ℤ_[p]) ^ n * (multiplicationTowerProductEquiv (p : ℤ) a n : ℤ_[p]) = z.appr N := by
    induction N with
    | zero => simp [PadicInt.appr_zero_right]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, LinearEquiv.apply_symm_apply, Int.cast_natCast]
      norm_cast
      rw [Nat.mul_div_cancel' (hd N), Nat.add_sub_cancel' (z.appr_mono N.le_succ)]
  refine ⟨a, ((PadicInt.summable_pow_mul _).hasSum_iff_tendsto_nat.2 ?_).tsum_eq⟩
  simpa only [hpartial] using PadicInt.tendsto_appr z

/-- **The image of the shift map of the multiplication-by-`p` tower** consists exactly of the
families `(aₙ)` whose `p`-adic sum `∑ₙ pⁿ aₙ` is an integer. -/
theorem mem_range_shift_multiplicationTower_iff {a : (multiplicationTower (p : ℤ)).Product} :
    a ∈ LinearMap.range (multiplicationTower (p : ℤ)).shift ↔
      ∃ m : ℤ, (m : ℤ_[p]) = padicSum p a := by
  set e := multiplicationTowerProductEquiv (p : ℤ)
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e x 0, (padicSum_shift p x).symm⟩
  · rintro ⟨m, hm⟩
    -- The tail `m - ∑_{n<N} pⁿ aₙ = ∑ₙ pⁿ⁺ᴺ aₙ₊ₙ` is divisible by `p ^ N` in `ℤ_[p]`, hence in `ℤ`.
    have hdvd (N : ℕ) : (p : ℤ) ^ N ∣ m - ∑ n ∈ Finset.range N, (p : ℤ) ^ n * e a n := by
      rw [← PadicInt.pow_p_dvd_int_iff]
      push_cast
      rw [hm, padicSum_apply, ← (PadicInt.summable_pow_mul _).sum_add_tsum_nat_add N,
        add_sub_cancel_left]
      refine ⟨∑' n, (p : ℤ_[p]) ^ n * (e a (n + N) : ℤ_[p]), ?_⟩
      rw [← (PadicInt.summable_pow_mul fun n ↦ (e a (n + N) : ℤ_[p])).tsum_mul_left]
      exact tsum_congr fun n ↦ by ring
    choose x hx using hdvd
    refine ⟨e.symm x, e.injective (funext fun N ↦ ?_)⟩
    rw [multiplicationTowerProductEquiv_shift, LinearEquiv.apply_symm_apply]
    have h := hx (N + 1)
    rw [Finset.sum_range_succ] at h
    refine mul_left_cancel₀ (pow_ne_zero N (Int.natCast_ne_zero.2 (Fact.out : p.Prime).ne_zero)) ?_
    linear_combination h - hx N

/-- **`lim¹` of the multiplication-by-`p` tower is `ℤ_[p] ⧸ ℤ`**, the isomorphism being induced
by the `p`-adic summation map `(aₙ) ↦ ∑ₙ pⁿ aₙ` (`limOneMultiplicationTowerEquiv_mk`). -/
def limOneMultiplicationTowerEquiv :
    (multiplicationTower (p : ℤ)).limOne ≃+ ℤ_[p] ⧸ (Int.castAddHom ℤ_[p]).range :=
  -- The `Submodule` quotient `limOne` is by definition the `QuotientAddGroup` quotient by
  -- `(LinearMap.range shift).toAddSubgroup`, which is the domain of `quotientAddEquivOfEq`.
  (QuotientAddGroup.quotientAddEquivOfEq (by
      ext a
      rw [Submodule.mem_toAddSubgroup, mem_range_shift_multiplicationTower_iff]
      simp [QuotientAddGroup.eq_zero_iff])).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      ((QuotientAddGroup.mk' (Int.castAddHom ℤ_[p]).range).comp (padicSum p))
      ((QuotientAddGroup.mk'_surjective _).comp (padicSum_surjective p)))

@[simp]
theorem limOneMultiplicationTowerEquiv_mk (a : (multiplicationTower (p : ℤ)).Product) :
    limOneMultiplicationTowerEquiv p (Submodule.Quotient.mk a) = (padicSum p a : ℤ_[p] ⧸ _) :=
  -- `Submodule.Quotient.mk a` is by definition `QuotientAddGroup.mk a`, as noted above
  (rfl)

/-- `lim¹` of the multiplication-by-`p` tower is nonzero. -/
instance nontrivial_limOne_multiplicationTower :
    Nontrivial (multiplicationTower (p : ℤ)).limOne :=
  have : Nontrivial (ℤ_[p] ⧸ (Int.castAddHom ℤ_[p]).range) :=
    QuotientAddGroup.nontrivial_iff.2 fun h ↦ PadicInt.intCast_not_surjective fun z ↦
      (h ▸ AddSubgroup.mem_top z : z ∈ (Int.castAddHom ℤ_[p]).range)
  (limOneMultiplicationTowerEquiv p).symm.injective.nontrivial

/-- **The multiplication-by-`p` tower is not Mittag-Leffler**, since its `lim¹` does not
vanish. -/
theorem not_isMittagLeffler_multiplicationTower :
    ¬(multiplicationTower (p : ℤ)).IsMittagLeffler := fun h ↦
  not_subsingleton _ ((multiplicationTower (p : ℤ)).subsingleton_limOne_of_isMittagLeffler h)

end ModuleTower

end TauCeti
