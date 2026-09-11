/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.Finite
public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.InfinitePlace

/-!
# The narrow-versus-ordinary defect of a quadratic field

For a number field `K` the sequence `Kˣ → Cl⁺(K) → Cl(K) → 1` is exact, so the defect between the
narrow and the ordinary class group is the image of the principal-class map `mkPrincipal`. That
image is a quotient of the group of sign patterns of `Kˣ` at the real places, modulo the global
sign, since `(x)` and `(-x)` are the same ideal. A quadratic field has at most two real places, so
the defect has at most two elements.

The quantitative statement proved here is sharper than a place count, and needs no case split on
the signature. Let `σ` be quadratic conjugation and let `x ∈ Kˣ`. The ratio `r = x / σx` has
`σ r = r⁻¹`, so `r / σ r = r²` is totally positive, and
`NumberField.isTotallyPositive_or_isTotallyPositive_neg_of_isTotallyPositive_div_quadraticConj`
puts `r` or `-r` on the totally positive side. In the first case the same lemma applied to `x`
makes `x` or `-x` totally positive, so `(x)` is narrowly trivial. In the second case the generator
`θ` absorbs the discrepancy: `σθ = -θ` gives `(θx) / σ(θx) = -r`, so `θx` or `-θx` is totally
positive and `[x]⁺ = [θ]⁺`. Hence every principal narrow class is `1` or `[θ]⁺`.

This bounds by one the amount by which the ordinary `2`-rank of a quadratic field can fall short
of the narrow `2`-rank `t - 1` computed by genus theory: for a real field the drop does happen,
as `ℚ(√3)` shows.

## Main results

* `NumberField.mkPrincipal_eq_one_or_eq_mkPrincipal_gen`: a principal narrow class of a quadratic
  field is trivial or the narrow class of the generator.
* `NumberField.card_ker_toClassGroup_le_two`: the kernel of `Cl⁺(K) → Cl(K)` has at most two
  elements.
* `NumberField.card_narrowClassGroup_le_two_mul_card_classGroup`: `h⁺(K) ≤ 2 h(K)`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §6.A, and F. Lemmermeyer, *Reciprocity Laws: From
  Euler to Eisenstein*, §2.2, for the narrow class group of a quadratic field and its comparison
  with the ordinary class group, `h⁺(K) ∈ {h(K), 2 h(K)}`, which is the bound
  `card_narrowClassGroup_le_two_mul_card_classGroup` proved here.
-/

public section

open Polynomial NumberField
open scoped NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **The principal narrow classes of a quadratic field are `1` and `[θ]⁺`.** For `K = ℚ(√d)`
presented by `θ` and any `x : Kˣ`, the narrow class of the principal ideal `(x)` is trivial or
equal to the narrow class of `(θ)`.

The ratio `r = x / σx` satisfies `σ r = r⁻¹`, so `r / σ r = r²` is totally positive and hence `r`
or `-r` is. If `r` is, then `x` or `-x` is totally positive and `(x)` is narrowly trivial. If `-r`
is, the same applies to `θx`, because `σθ = -θ` turns `(θx) / σ(θx)` into `-r`. -/
theorem mkPrincipal_eq_one_or_eq_mkPrincipal_gen (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (x : Kˣ) :
    NarrowClassGroup.mkPrincipal x = 1 ∨
      NarrowClassGroup.mkPrincipal x =
        NarrowClassGroup.mkPrincipal (Units.mk0 (θ : K) (coe_gen_ne_zero hmin)) := by
  have hθ : (θ : K) ≠ 0 := coe_gen_ne_zero hmin
  have hx : (x : K) ≠ 0 := x.ne_zero
  have hcj : ∀ {z : K}, z ≠ 0 → quadraticConj hmin hgen z ≠ 0 := fun {z} hz h =>
    hz ((quadraticConj hmin hgen).injective (by rw [h, map_zero]))
  set r : K := (x : K) / quadraticConj hmin hgen (x : K) with hr
  have hr0 : r ≠ 0 := div_ne_zero hx (hcj hx)
  -- `σ r = r⁻¹`, because `σ` is an involution.
  have hσr : quadraticConj hmin hgen r = r⁻¹ := by
    rw [hr, map_div₀, quadraticConj_involutive hmin hgen (x : K), inv_div]
  -- Hence `r / σ r = r ^ 2` is totally positive, and `r` or `-r` is totally positive.
  have hrpos : IsTotallyPositive r ∨ IsTotallyPositive (-r) :=
    isTotallyPositive_or_isTotallyPositive_neg_of_isTotallyPositive_div_quadraticConj hmin hgen
      (by
        have hrr : r / quadraticConj hmin hgen r = r ^ 2 := by
          rw [hσr, pow_two]; field_simp
        rw [hrr]
        exact isTotallyPositive_sq hr0)
  rcases hrpos with hpos | hpos
  · -- `x` or `-x` is totally positive, so the narrow class of `(x)` is trivial.
    refine Or.inl ?_
    rcases isTotallyPositive_or_isTotallyPositive_neg_of_isTotallyPositive_div_quadraticConj
      hmin hgen (z := (x : K)) hpos with h | h
    · exact NarrowClassGroup.mkPrincipal_eq_one_of_isTotallyPositive h
    · rw [← NarrowClassGroup.mkPrincipal_neg x]
      exact NarrowClassGroup.mkPrincipal_eq_one_of_isTotallyPositive (by simpa using h)
  · -- `θx` or `-θx` is totally positive, so the narrow class of `(x)` is that of `(θ)`.
    refine Or.inr ?_
    set u : Kˣ := Units.mk0 (θ : K) hθ * x with hu
    have huval : (u : K) = (θ : K) * (x : K) := by rw [hu, Units.val_mul, Units.val_mk0]
    -- `(θx) / σ(θx) = -r`, since `σθ = -θ`.
    have hratio : (u : K) / quadraticConj hmin hgen (u : K) = -r := by
      rw [huval, map_mul, quadraticConj_gen hmin hgen, hr]
      field_simp
    have huone : NarrowClassGroup.mkPrincipal u = 1 := by
      rcases isTotallyPositive_or_isTotallyPositive_neg_of_isTotallyPositive_div_quadraticConj
        hmin hgen (z := (u : K)) (by rw [hratio]; exact hpos) with h | h
      · exact NarrowClassGroup.mkPrincipal_eq_one_of_isTotallyPositive h
      · rw [← NarrowClassGroup.mkPrincipal_neg u]
        exact NarrowClassGroup.mkPrincipal_eq_one_of_isTotallyPositive (by simpa using h)
    rw [hu, map_mul] at huone
    -- The narrow class of a principal ideal is `2`-torsion, so it is its own inverse.
    have hsq := NarrowClassGroup.mkPrincipal_sq (Units.mk0 (θ : K) hθ)
    rw [pow_two] at hsq
    calc NarrowClassGroup.mkPrincipal x
        = NarrowClassGroup.mkPrincipal (Units.mk0 (θ : K) hθ) *
            (NarrowClassGroup.mkPrincipal (Units.mk0 (θ : K) hθ) *
              NarrowClassGroup.mkPrincipal x) := by rw [← mul_assoc, hsq, one_mul]
      _ = NarrowClassGroup.mkPrincipal (Units.mk0 (θ : K) hθ) := by rw [huone, mul_one]

/-- **The narrow class group of a quadratic field exceeds the ordinary one by at most a factor
of two.** By exactness the kernel of `Cl⁺(K) → Cl(K)` is the image of the principal-class map.
Choosing a presentation `θ` of `K` (`exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top`),
`mkPrincipal_eq_one_or_eq_mkPrincipal_gen` confines that image to the subgroup generated by the
narrow class of `(θ)`, which is `2`-torsion. -/
theorem card_ker_toClassGroup_le_two (hK : Module.finrank ℚ K = 2) :
    Nat.card (MonoidHom.ker (NarrowClassGroup.toClassGroup (K := K))) ≤ 2 := by
  obtain ⟨θ, d, hmin, hgen⟩ := exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top hK
  set c := NarrowClassGroup.mkPrincipal (Units.mk0 (θ : K) (coe_gen_ne_zero hmin)) with hc
  have hle : MonoidHom.ker (NarrowClassGroup.toClassGroup (K := K)) ≤ Subgroup.zpowers c := by
    rw [NarrowClassGroup.toClassGroup_ker]
    rintro _ ⟨x, rfl⟩
    rcases mkPrincipal_eq_one_or_eq_mkPrincipal_gen hmin hgen x with h | h
    · rw [h]; exact one_mem _
    · rw [h, ← hc]; exact Subgroup.mem_zpowers c
  have hzp : Nat.card (Subgroup.zpowers c) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd two_pos
      (orderOf_dvd_of_pow_eq_one (NarrowClassGroup.mkPrincipal_sq _))
  exact le_trans (Nat.card_le_card_of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)) hzp

/-- **The narrow class number of a quadratic field is at most twice the class number.** -/
theorem card_narrowClassGroup_le_two_mul_card_classGroup (hK : Module.finrank ℚ K = 2) :
    Nat.card (NarrowClassGroup K) ≤ 2 * Nat.card (ClassGroup (𝓞 K)) := by
  rw [NarrowClassGroup.card_eq_card_classGroup_mul_card_ker, mul_comm]
  exact Nat.mul_le_mul_right _ (card_ker_toClassGroup_le_two hK)

end NumberField
