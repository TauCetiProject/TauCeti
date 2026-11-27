/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.GaussValuation.RootCounting
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import TauCeti.RingTheory.Valuation.Basic
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Averaging distances from primitive roots of unity

For a real additive valuation normalized at `p`, the primitive `p ^ h`-th roots cannot all be
very close to a given finite multiset of points. The estimates are independent of the
number of points and form the averaging step in polynomial evaluation bounds.

## Provenance

`AddValuation.sum_max_min_primitiveRoots_sub_le` and
`AddValuation.exists_isPrimitiveRoot_sum_max_min_sub_le`, together with its untruncated
consequence `AddValuation.exists_isPrimitiveRoot_sum_sub_le`, adapt
`New.Selmer.sum_min_ellVal_sub_le` and `New.Selmer.exists_sum_min_ellVal_sub_le` in
`src/New/Congruences/Selmer/RootsOfUnity.lean` in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC). The version for arbitrary valued integral domains containing
the required roots of unity and untruncated real additive valuations is new here.

## References

* S. Bosch, U. Güntzer, and R. Remmert, *Non-Archimedean Analysis*, §5.1 (Gauss valuations).
-/

public section

open Polynomial Finset
noncomputable section
namespace AddValuation

variable {K : Type*} [CommRing K] [IsDomain K] {p : ℕ}
  (v : AddValuation K (WithTop ℝ)) (hp : v (p : K) = 1)

omit [IsDomain K] in
include hp in
private lemma shifted_pow_sub_one_coeffs {α : K} (hu : v (1 + α) = 0) (h : ℕ) :
    let f : K[X] := (X + C (1 + α)) ^ p ^ h - 1
    (∀ k, 0 ≤ v (f.coeff k)) ∧ v (f.coeff 1) = h := by
  let f : K[X] := (X + C (1 + α)) ^ p ^ h - 1
  have hcoeff (k : ℕ) : 0 ≤ v (f.coeff k) := by
    dsimp only [f]
    rw [coeff_sub]
    apply v.map_le_sub
    · simp only [coeff_X_add_C_pow, v.map_mul, v.map_pow, hu, smul_zero, zero_add]
      exact v.toValuation.map_natCast_le_one _
    · simp only [coeff_one]
      split_ifs <;> simp
  have hc : f.coeff 1 = (1 + α) ^ (p ^ h - 1) * p ^ h := by
    dsimp only [f]
    rw [coeff_sub, coeff_X_add_C_pow, coeff_one, ite_eq_right one_ne_zero, sub_zero,
      Nat.choose_one_right, Nat.cast_pow]
  have hcval : v (f.coeff 1) = h := by
    rw [hc, v.map_mul, v.map_pow, hu, smul_zero, zero_add, v.map_pow, hp]
    norm_cast
    simp
  exact ⟨hcoeff, hcval⟩

include hp in
/-- The sum of clipped valuations of distances from an arbitrary point to primitive
`p ^ h`-th roots of unity minus one is at most `h + 1`. -/
theorem sum_max_min_primitiveRoots_sub_le (α : K) (h : ℕ) :
    ∑ ζ ∈ primitiveRoots (p ^ h) K, max 0 (min 1 (v (ζ - 1 - α))) ≤ (h + 1 : ℝ) := by
  by_cases hu : v (1 + α) = 0
  · let f : K[X] := (X + C (1 + α)) ^ p ^ h - 1
    obtain ⟨hcoeff, hcval⟩ : (∀ k, 0 ≤ v (f.coeff k)) ∧ v (f.coeff 1) = h :=
      shifted_pow_sub_one_coeffs v hp hu h
    have hf : f ≠ 0 := by
      intro hf
      have H := hcval
      simp [hf] at H
    have hroots : (primitiveRoots (p ^ h) K).val.map (fun ζ ↦ ζ - 1 - α) ≤ f.roots := by
      have hinj : Function.Injective fun ζ : K ↦ ζ - 1 - α :=
        sub_left_injective.comp sub_left_injective
      refine (Multiset.le_iff_subset ((primitiveRoots _ _).nodup.map hinj)).2 fun y hy ↦ ?_
      obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.1 hy
      have hadd : ζ - 1 - α + (1 + α) = ζ := by ring
      rw [mem_roots hf, IsRoot.def]
      simp only [f, eval_sub, eval_pow, eval_add, eval_X, eval_C, eval_one, hadd,
        (isPrimitiveRoot_of_mem_primitiveRoots hζ).pow_eq_one, sub_self]
    have hmass := f.sum_max_min_valuation_roots_le (v := v) hcoeff
      (ρ := 1) zero_le_one 1
    simp only [hcval, one_nsmul, WithTop.coe_one] at hmass
    rw [Finset.sum_eq_multiset_sum]
    refine le_trans ?_ hmass
    obtain ⟨rest, hrest⟩ := Multiset.le_iff_exists_add.1 hroots
    rw [hrest, Multiset.map_add, Multiset.sum_add]
    simpa only [Multiset.map_map, Function.comp_def, WithTop.coe_one] using
      (le_add_of_nonneg_right (Multiset.sum_nonneg (fun a ha ↦ by
        obtain ⟨x, _, rfl⟩ := Multiset.mem_map.1 ha
        exact le_max_left _ _)) :
          ((primitiveRoots (p ^ h) K).val.map fun ζ ↦ max 0 (min 1 (v (ζ - 1 - α)))).sum ≤
            _ + (rest.map fun a ↦ max 0 (min (1 : WithTop ℝ) (v a))).sum)
  have hp0 : p ≠ 0 := by intro hz; simp [hz] at hp
  have hzero : ∀ ζ ∈ primitiveRoots (p ^ h) K, max 0 (min 1 (v (ζ - 1 - α))) = 0 := by
    intro ζ hζ
    have hvζ : v ζ = 0 := by
      have H := congrArg v.toValuation (isPrimitiveRoot_of_mem_primitiveRoots hζ).pow_eq_one
      rw [_root_.map_pow, _root_.map_one] at H
      exact (pow_eq_one_iff_of_nonneg zero_le (pow_ne_zero _ hp0)).1 H
    have heq : ζ - 1 - α = ζ - (1 + α) := by ring
    rw [heq, sub_eq_add_neg, v.map_add_of_distinct_val (by
      rw [hvζ, v.map_neg]
      exact Ne.symm hu), hvζ, v.map_neg]
    exact max_eq_left ((min_le_right _ _).trans (min_le_left _ _))
  rw [sum_eq_zero hzero]
  exact_mod_cast (Nat.zero_le (h + 1))

include hp in
/-- Among the primitive `p ^ h`-th roots, one has total clipped distance valuation from a finite
multiset of points bounded by its cardinality times `(h + 1) / φ(p ^ h)`. -/
theorem exists_isPrimitiveRoot_sum_max_min_sub_le (h : ℕ)
    [HasEnoughRootsOfUnity K (p ^ h)] {R : Multiset K} :
    ∃ ζ : K, IsPrimitiveRoot ζ (p ^ h) ∧
      (R.map fun α ↦ max 0 (min 1 (v (ζ - 1 - α)))).sum ≤
        ((R.card : ℝ) * (Nat.totient (p ^ h) : ℝ)⁻¹ * (h + 1) : ℝ) := by
  classical
  have hp0 : p ≠ 0 := by intro hz; simp [hz] at hp
  have : NeZero (p ^ h) := ⟨pow_ne_zero _ hp0⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K (p ^ h)
  let μ := primitiveRoots (p ^ h) K
  let f : K → WithTop ℝ := fun ζ ↦ (R.map fun α ↦ max 0 (min 1 (v (ζ - 1 - α)))).sum
  have htotal : ∑ ζ ∈ μ, f ζ ≤ ((R.card : ℝ) * (h + 1) : ℝ) := by
    rw [← Multiset.sum_map_sum]
    calc
      (R.map fun α ↦ ∑ ζ ∈ μ, max 0 (min 1 (v (ζ - 1 - α)))).sum
          ≤ (R.map fun _ ↦ ((h + 1 : ℝ) : WithTop ℝ)).sum :=
        Multiset.sum_map_le_sum_map _ _ fun α _ ↦
          sum_max_min_primitiveRoots_sub_le v hp α h
      _ = ((R.card : ℝ) * (h + 1) : ℝ) := by
        rw [Multiset.map_const', Multiset.sum_replicate, ← WithTop.coe_nsmul]
        norm_cast
        simp only [nsmul_eq_mul]
        push_cast
        ring
  have hμ : μ.Nonempty := ⟨ζ₀, (mem_primitiveRoots (NeZero.pos _)).2 hζ₀⟩
  obtain ⟨ζ, hζ, hmin⟩ := μ.exists_min_image f hμ
  have H : μ.card • f ζ ≤ ((R.card : ℝ) * (h + 1) : ℝ) := by
    calc
      μ.card • f ζ = ∑ _η ∈ μ, f ζ := by simp
      _ ≤ ∑ η ∈ μ, f η := sum_le_sum fun η hη ↦ hmin η hη
      _ ≤ _ := htotal
  have hcard : 0 < μ.card := card_pos.2 hμ
  have hfinite : f ζ ≠ ⊤ := by
    intro ht
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hcard.ne'
    rw [hm, succ_nsmul, ht, WithTop.add_top] at H
    exact (WithTop.not_top_le_coe _ ) H
  lift f ζ to ℝ using hfinite with y hy
  norm_cast at H
  rw [nsmul_eq_mul] at H
  have hμcard : μ.card = Nat.totient (p ^ h) := hζ₀.card_primitiveRoots
  refine ⟨ζ, isPrimitiveRoot_of_mem_primitiveRoots hζ, ?_⟩
  have Hgoal : f ζ ≤
      ((R.card : ℝ) * (Nat.totient (p ^ h) : ℝ)⁻¹ * (h + 1) : ℝ) := by
    rw [← hy]
    norm_cast
    rw [← hμcard]
    apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < μ.card by exact_mod_cast hcard)).1
    simpa [mul_assoc, mul_comm, mul_left_comm,
      (Nat.cast_ne_zero.2 hcard.ne' : (μ.card : ℝ) ≠ 0)] using H
  exact Hgoal

include hp in
/-- If the average clipped distance bound is less than one, some primitive root satisfies the
same bound for the untruncated sum of valuations. -/
theorem exists_isPrimitiveRoot_sum_sub_le (h : ℕ)
    [HasEnoughRootsOfUnity K (p ^ h)] {R : Multiset K}
    {δ : ℝ} (hδ : δ < 1)
    (hbound : (R.card : ℝ) * (Nat.totient (p ^ h) : ℝ)⁻¹ * (h + 1) ≤ δ) :
    ∃ ζ : K, IsPrimitiveRoot ζ (p ^ h) ∧
      (R.map fun α ↦ v (ζ - 1 - α)).sum ≤ (δ : WithTop ℝ) := by
  obtain ⟨ζ, hζ, haverage⟩ := v.exists_isPrimitiveRoot_sum_max_min_sub_le hp h
  have hclip := haverage.trans (WithTop.coe_le_coe.2 hbound)
  have hle : ∀ a ∈ R, v (ζ - 1 - a) ≤ max 0 (min 1 (v (ζ - 1 - a))) := by
    intro a ha
    have hsingle : max 0 (min 1 (v (ζ - 1 - a))) ≤ (δ : WithTop ℝ) :=
      (Multiset.single_le_sum (by
        intro x hx
        obtain ⟨b, _, rfl⟩ := Multiset.mem_map.1 hx
        exact le_max_left _ _) _ (Multiset.mem_map_of_mem _ ha)).trans hclip
    have hlt : v (ζ - 1 - a) < 1 := by
      have H := (le_max_right 0 (min 1 (v (ζ - 1 - a)))).trans hsingle
        |>.trans_lt (show (δ : WithTop ℝ) < 1 by exact_mod_cast hδ)
      simpa using H
    rw [min_eq_right hlt.le]
    exact le_max_right _ _
  exact ⟨ζ, hζ, (Multiset.sum_map_le_sum_map _ _ hle).trans hclip⟩

end AddValuation
