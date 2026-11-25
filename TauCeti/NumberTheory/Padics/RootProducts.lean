/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Localization.Integral
import TauCeti.Analysis.Normed.Group.Ultra
import TauCeti.NumberTheory.Padics.Polynomial
import TauCeti.RingTheory.Polynomial.Factors

/-!
# Monic `ℓ`-adic polynomials are determined by the norms of root products

Let `ℓ` be a prime and let `P, Q ∈ ℚ_ℓ[X]` be monic polynomials which split in a normed extension
field `L` of `ℚ_ℓ` (for instance `PadicAlgCl ℓ`), with roots `aᵢ` and `bⱼ` in `L` counted with
multiplicity. If `|∏ᵢ F(aᵢ)| = |∏ⱼ F(bⱼ)|` for every integral test polynomial `F ∈ ℤ[X]`, then
`P = Q`. This is the step which identifies the characteristic polynomial of an endomorphism of an
abelian variety with that of its action on the `ℓ`-adic Tate module: there the two sides of the
hypothesis are the `ℓ`-adic absolute values of the degree of `F(α)` and of the determinant of
`F(α)` on the Tate module.

The test polynomials extend from `ℤ[X]` to every `G ∈ ℚ_ℓ[X]`
(`Polynomial.norm_prod_aroots_aeval_eq_of_forall_int`): the constant test `ℓ` shows that `P` and
`Q` have equally many roots, so the identity is invariant under scaling `G` by a nonzero
`b ∈ ℤ_ℓ`. For suitable `b` the polynomial `b G` has coefficients in `ℤ_ℓ`, so it is a
coefficientwise limit of integral polynomials
(`Polynomial.exists_seq_int_tendsto_aeval_map_coe`). Then for a monic irreducible `f` and large
`k` the test polynomial `f + ℓᵏ` has values of norm `ℓ⁻ᵏ` at the roots of `f` and unchanged norms
elsewhere, so comparing `k` with `k + 1` shows that `P` and `Q` have equally many roots at which
`f` vanishes. By
`Polynomial.Monic.eq_of_forall_card_filter_aroots_eq` this determines the multiplicity of every
irreducible factor. The argument uses the Galois orbits of the roots, the root sets of the
irreducible factors, rather than the rationality of individual roots.

## Main results

* `Polynomial.norm_prod_aroots_aeval_eq_of_forall_int`: equal norms of root products for every
  integral test polynomial give equal norms for every `ℓ`-adic test polynomial.
* `Polynomial.Monic.eq_of_forall_norm_prod_aroots_aeval_eq`: monic polynomials over `ℚ_ℓ` which
  split in `L` and have equal norms of root products for every integral test polynomial are equal.

## References

* J. S. Milne, *Abelian varieties*, version 2.0, 2008, Lemma 10.21.
-/

public section

open Filter Topology

namespace Polynomial

section Padic

variable {ℓ : ℕ} [Fact ℓ.Prime] {L : Type*} [NormedField L] [NormedAlgebra ℚ_[ℓ] L]

/-- **Extension to `ℓ`-adic test polynomials.** Suppose that the roots `aᵢ` of `P` and `bⱼ` of `Q`
in a normed extension field `L` of `ℚ_ℓ` satisfy `|∏ᵢ F(aᵢ)| = |∏ⱼ F(bⱼ)|` for every
`F ∈ ℤ[X]`. Then the same holds for every `G ∈ ℚ_ℓ[X]`. -/
theorem norm_prod_aroots_aeval_eq_of_forall_int {P Q : ℚ_[ℓ][X]}
    (h : ∀ F : ℤ[X], ‖((P.aroots L).map fun a ↦ aeval a F).prod‖ =
      ‖((Q.aroots L).map fun a ↦ aeval a F).prod‖) (G : ℚ_[ℓ][X]) :
    ‖((P.aroots L).map fun a ↦ aeval a G).prod‖ =
      ‖((Q.aroots L).map fun a ↦ aeval a G).prod‖ := by
  set t : ℝ := ‖(ℓ : ℚ_[ℓ])‖
  have ht0 : 0 < t := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero)
  have ht1 : t < 1 := Padic.norm_p_lt_one
  -- The constant test polynomial `ℓ` shows that `P` and `Q` have equally many roots in `L`.
  have hcard : (P.aroots L).card = (Q.aroots L).card := by
    have hℓ := h (ℓ : ℤ[X])
    have hnorm : ‖(ℓ : L)‖ = t := by
      rw [← map_natCast (algebraMap ℚ_[ℓ] L), norm_algebraMap']
    simp only [map_natCast, Multiset.map_const', Multiset.prod_replicate, norm_pow, hnorm] at hℓ
    exact pow_right_injective₀ ht0 ht1.ne hℓ
  -- Scale `G` by a nonzero `b ∈ ℤ_ℓ` to make its coefficients integral.
  obtain ⟨b, hb, hbG⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ_[ℓ]) G
  set c := algebraMap ℤ_[ℓ] ℚ_[ℓ] b
  have hc : c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  rw [Algebra.smul_def, algebraMap_apply] at hbG
  -- Integral approximations of `b G` give the identity for `b G` in the limit.
  obtain ⟨F, hF⟩ := exists_seq_int_tendsto_aeval_map_coe (L := L)
    (IsLocalization.integerNormalization (nonZeroDivisors ℤ_[ℓ]) G)
  have hlim (A : Multiset L) : Tendsto (fun N ↦ ‖(A.map fun a ↦ aeval a (F N)).prod‖) atTop
      (𝓝 (‖c‖ ^ A.card * ‖(A.map fun a ↦ aeval a G).prod‖)) := by
    have hscale : ‖(A.map fun a ↦ aeval a (C c * G)).prod‖ =
        ‖c‖ ^ A.card * ‖(A.map fun a ↦ aeval a G).prod‖ := by
      simp only [aeval_mul, aeval_C, Multiset.prod_map_mul, Multiset.map_const',
        Multiset.prod_replicate, norm_mul, norm_pow, norm_algebraMap']
    rw [← hscale, ← hbG]
    exact (tendsto_multiset_prod A fun a _ ↦ hF a).norm
  have := tendsto_nhds_unique (hlim (P.aroots L))
    ((hlim (Q.aroots L)).congr fun N ↦ (h (F N)).symm)
  rw [hcard] at this
  exact mul_left_cancel₀ (pow_pos (norm_pos_iff.2 hc) _).ne' this

/-- For `k` large, so that `ℓ⁻ᵏ < |f(a)|` whenever `f(a) ≠ 0`, the value of `f + ℓᵏ` at `a` has
norm `ℓ⁻ᵏ` if `f(a) = 0` and `|f(a)|` otherwise. -/
private lemma norm_aeval_add_C_pow [DecidableEq L] {f : ℚ_[ℓ][X]} {a : L} {k : ℕ}
    (hk : aeval a f ≠ 0 → ‖(ℓ : ℚ_[ℓ])‖ ^ k < ‖aeval a f‖) :
    ‖aeval a (f + C ((ℓ : ℚ_[ℓ]) ^ k))‖ =
      if aeval a f = 0 then ‖(ℓ : ℚ_[ℓ])‖ ^ k else ‖aeval a f‖ := by
  have : IsUltrametricDist L := .of_normedAlgebra ℚ_[ℓ]
  rw [aeval_add, aeval_C]
  split_ifs with h0
  · rw [h0, zero_add, norm_algebraMap', norm_pow]
  · refine (IsUltrametricDist.norm_eq_of_norm_sub_lt_left ?_).symm
    rw [sub_add_cancel_left, norm_neg, norm_algebraMap', norm_pow]
    exact hk h0

/-- For `k` large, the product over a multiset `A` of the norms of the values of `f + ℓᵏ` is
`ℓ^{-k c}` times the product of the nonzero `|f(a)|`, where `c` is the number of points of `A` at
which `f` vanishes. -/
private lemma prod_norm_aeval_add_C_pow [DecidableEq L] (A : Multiset L) {f : ℚ_[ℓ][X]} {k : ℕ}
    (hk : ∀ a ∈ A, aeval a f ≠ 0 → ‖(ℓ : ℚ_[ℓ])‖ ^ k < ‖aeval a f‖) :
    ‖(A.map fun a ↦ aeval a (f + C ((ℓ : ℚ_[ℓ]) ^ k))).prod‖ =
      (‖(ℓ : ℚ_[ℓ])‖ ^ k) ^ (A.filter fun a ↦ aeval a f = 0).card *
        ((A.filter fun a ↦ aeval a f ≠ 0).map fun a ↦ ‖aeval a f‖).prod := by
  simp only [Multiset.norm_prod, Multiset.map_map, Function.comp_def]
  rw [Multiset.map_congr rfl fun a ha ↦ norm_aeval_add_C_pow (hk a ha)]
  conv_lhs => rw [← Multiset.filter_add_not (fun a ↦ aeval a f = 0) A, Multiset.map_add,
    Multiset.prod_add]
  congr 1
  · -- At the zeros of `f` every factor is `ℓ⁻ᵏ`.
    rw [Multiset.map_congr rfl fun a ha ↦ ite_eq_left (Multiset.mem_filter.1 ha).2]
    simp
  · -- Away from the zeros of `f` every factor is `|f(a)|`.
    exact congrArg _ (Multiset.map_congr rfl fun a ha ↦ ite_eq_right (Multiset.mem_filter.1 ha).2)

/-- **Milne, Lemma 10.21.** Let `P` and `Q` be monic polynomials over `ℚ_ℓ` which split in a
normed extension field `L` of `ℚ_ℓ`, with roots `aᵢ` and `bⱼ` in `L` counted with
multiplicity. If `|∏ᵢ F(aᵢ)| = |∏ⱼ F(bⱼ)|` for every integral test polynomial `F ∈ ℤ[X]`, then
`P = Q`. -/
theorem Monic.eq_of_forall_norm_prod_aroots_aeval_eq {P Q : ℚ_[ℓ][X]} (hP : P.Monic)
    (hQ : Q.Monic)
    (hPs : (P.map (algebraMap ℚ_[ℓ] L)).Splits) (hQs : (Q.map (algebraMap ℚ_[ℓ] L)).Splits)
    (h : ∀ F : ℤ[X], ‖((P.aroots L).map fun a ↦ aeval a F).prod‖ =
      ‖((Q.aroots L).map fun a ↦ aeval a F).prod‖) :
    P = Q := by
  classical
  refine hP.eq_of_forall_card_filter_aroots_eq hQ hPs hQs fun f _ _ ↦ ?_
  set t : ℝ := ‖(ℓ : ℚ_[ℓ])‖
  have ht0 : 0 < t := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero)
  have ht1 : t < 1 := Padic.norm_p_lt_one
  set S := P.aroots L + Q.aroots L
  -- Choose `k` such that `ℓ⁻ᵏ` and `ℓ⁻ᵏ⁻¹` are below every nonzero `|f(a)|`, `a ∈ S`.
  have hev : ∀ᶠ k in atTop, ∀ a ∈ S.toFinset, aeval a f ≠ 0 → t ^ k < ‖aeval a f‖ :=
    (eventually_all_finset _).2 fun a _ ↦ by
      by_cases h0 : aeval a f = 0
      · exact Eventually.of_forall fun _ h ↦ absurd h0 h
      · exact ((tendsto_pow_atTop_nhds_zero_of_lt_one ht0.le ht1).eventually
          (gt_mem_nhds (norm_pos_iff.2 h0))).mono fun _ hk _ ↦ hk
  obtain ⟨k, hk, hk1⟩ := (hev.and ((tendsto_add_atTop_nat 1).eventually hev)).exists
  -- For such `m`, the products over the roots of `P` and of `Q` of `|f + ℓᵐ|` agree.
  have hcomp (m : ℕ) (hm : ∀ a ∈ S.toFinset, aeval a f ≠ 0 → t ^ m < ‖aeval a f‖) :
      (t ^ m) ^ ((P.aroots L).filter fun a ↦ aeval a f = 0).card *
          (((P.aroots L).filter fun a ↦ aeval a f ≠ 0).map fun a ↦ ‖aeval a f‖).prod =
        (t ^ m) ^ ((Q.aroots L).filter fun a ↦ aeval a f = 0).card *
          (((Q.aroots L).filter fun a ↦ aeval a f ≠ 0).map fun a ↦ ‖aeval a f‖).prod := by
    have hmP : ∀ a ∈ P.aroots L, aeval a f ≠ 0 → t ^ m < ‖aeval a f‖ := fun a ha ↦
      hm a (Multiset.mem_toFinset.2 (Multiset.mem_add.2 (Or.inl ha)))
    have hmQ : ∀ a ∈ Q.aroots L, aeval a f ≠ 0 → t ^ m < ‖aeval a f‖ := fun a ha ↦
      hm a (Multiset.mem_toFinset.2 (Multiset.mem_add.2 (Or.inr ha)))
    rw [← prod_norm_aeval_add_C_pow _ hmP, ← prod_norm_aeval_add_C_pow _ hmQ]
    exact norm_prod_aroots_aeval_eq_of_forall_int h _
  -- Dividing the comparison at `k + 1` by the one at `k` gives `ℓ^{-c_P} = ℓ^{-c_Q}`.
  set CP := (((P.aroots L).filter fun a ↦ aeval a f ≠ 0).map fun a ↦ ‖aeval a f‖).prod
  have hCP : 0 < CP := Multiset.prod_pos fun x hx ↦ by
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hx
    exact norm_pos_iff.2 (Multiset.mem_filter.1 ha).2
  have h0 := hcomp k hk
  -- Since `ℓ^{-(k+1)} = ℓ⁻¹ ℓ^{-k}`, the comparison at `k + 1` is `ℓ^{-c}` times that at `k`.
  have h1 : t ^ ((P.aroots L).filter fun a ↦ aeval a f = 0).card *
        ((t ^ k) ^ ((P.aroots L).filter fun a ↦ aeval a f = 0).card * CP) =
      t ^ ((Q.aroots L).filter fun a ↦ aeval a f = 0).card *
        ((t ^ k) ^ ((Q.aroots L).filter fun a ↦ aeval a f = 0).card *
          (((Q.aroots L).filter fun a ↦ aeval a f ≠ 0).map fun a ↦ ‖aeval a f‖).prod) := by
    simpa only [pow_succ', mul_pow, mul_assoc] using hcomp (k + 1) hk1
  rw [← h0] at h1
  exact pow_right_injective₀ ht0 ht1.ne
    (mul_right_cancel₀ (mul_pos (pow_pos (pow_pos ht0 k) _) hCP).ne' h1)

end Padic

end Polynomial
