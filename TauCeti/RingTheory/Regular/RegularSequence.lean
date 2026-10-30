/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Depth.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

/-!
# Constructing regular sequences

This file produces regular sequences on a module `M` from local information.

If `a, b` is a weakly `M`-regular sequence, then `bʲ` is regular on `M ⧸ aⁿ M` for all `n` and `j`.

Let `M` be a finite module over a Noetherian ring `R` and `I` an ideal of `R`. By prime avoidance,
`I` contains an `M`-regular element exactly when `I` lies in no associated prime of `M`. Iterating,
if `depth M_p ≥ n` at every prime `p ⊇ I`, then `I` contains a weakly `M`-regular sequence of
length `n`: an associated prime containing `I` would give a localization of depth zero, and
dividing by a regular element of `I` lowers each of these local depths by exactly one.

The second statement passes from depth at the points of the closed subset `V(I)` of `Spec R` to a
regular sequence on `M` itself. This is how a depth condition at the points of `V(I)` is used to
extend sections of `M~` across `V(I)` (Stacks, Lemma 31.5.11 (0E9I)).

## Main results

* `RingTheory.Sequence.IsWeaklyRegular.of_subsingleton`: every finite sequence is weakly regular
  on a module with at most one element.
* `RingTheory.Sequence.IsWeaklyRegular.isSMulRegular_quotSMulTop_pow`: for a weakly `M`-regular
  sequence `a, b`, the power `bʲ` is regular on `M ⧸ aⁿ M`.
* `Ideal.exists_mem_isSMulRegular_iff`: `I` contains an `M`-regular element if and only if it lies
  in no associated prime of `M`.
* `TauCeti.exists_isWeaklyRegular_of_le_depth_localizedModule`: if `depth M_p ≥ n` at every prime
  `p ⊇ I`, then `I` contains a weakly `M`-regular sequence of length `n`.

## References

* [Stacks Project, Lemma 31.5.11](https://stacks.math.columbia.edu/tag/0E9I).
-/

public section

universe u v

open IsLocalRing RingTheory.Sequence Module Pointwise

section Pow

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Every finite sequence is weakly regular on a module with at most one element. -/
theorem RingTheory.Sequence.IsWeaklyRegular.of_subsingleton [Subsingleton M] (rs : List R) :
    IsWeaklyRegular M rs :=
  ⟨fun _ _ _ _ _ ↦ Subsingleton.elim _ _⟩

/-- If `a, b` is a weakly `M`-regular sequence, then `bʲ` is regular on `M ⧸ aⁿ M`. -/
theorem RingTheory.Sequence.IsWeaklyRegular.isSMulRegular_quotSMulTop_pow {a b : R}
    (h : IsWeaklyRegular M [a, b]) (n j : ℕ) : IsSMulRegular (QuotSMulTop (a ^ n) M) (b ^ j) := by
  obtain ⟨ha, hb⟩ := (isWeaklyRegular_cons_iff M a [b]).1 h
  rw [isWeaklyRegular_singleton_iff] at hb
  refine isSMulRegular_iff_right_eq_zero_of_smul.2 fun q hq ↦ ?_
  induction q using Submodule.Quotient.induction_on with | H x => ?_
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
  rw [Submodule.Quotient.mk_eq_zero]
  -- Show by induction on `n` that `bʲ x ∈ aⁿ M` implies `x ∈ aⁿ M`.
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hq
    -- First `x ∈ a M`, since `b` is regular on `M ⧸ a M`.
    have hxa : x ∈ a • (⊤ : Submodule R M) := by
      refine (Submodule.Quotient.mk_eq_zero _).1 ((hb.pow j).right_eq_zero_of_smul ?_)
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← hy, pow_succ',
        mul_smul]
      exact Submodule.smul_mem_pointwise_smul _ a ⊤ trivial
    obtain ⟨x', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hxa
    -- Then cancel `a`, which is `M`-regular, and apply the induction hypothesis.
    have hx' : b ^ j • x' = a ^ n • y := ha <| by
      simp only [smul_comm a (b ^ j), ← mul_smul, ← pow_succ', hy]
    obtain ⟨c, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1
      (ih x' (hx' ▸ Submodule.smul_mem_pointwise_smul _ _ ⊤ trivial))
    rw [smul_smul, ← pow_succ']
    exact Submodule.smul_mem_pointwise_smul _ _ ⊤ trivial

end Pow

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {M : Type v} [AddCommGroup M] [Module R M]
  [Module.Finite R M]

/-- **Prime avoidance for regular elements.** An ideal `I` of a Noetherian ring contains an
element that is regular on a finite module `M` if and only if `I` is contained in no associated
prime of `M`. -/
theorem Ideal.exists_mem_isSMulRegular_iff (I : Ideal R) :
    (∃ a ∈ I, IsSMulRegular M a) ↔ ∀ p ∈ associatedPrimes R M, ¬ I ≤ p := by
  have hzd := biUnion_associatedPrimes_eq_compl_regular R M
  refine ⟨fun ⟨a, ha, reg⟩ p hp hle ↦ ?_, fun h ↦ ?_⟩
  · have hmem : a ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := Set.mem_biUnion hp (hle ha)
    rw [hzd] at hmem
    exact hmem reg
  · by_contra! hreg
    obtain ⟨p, hp, hle⟩ := (Ideal.subset_union_prime_finite (associatedPrimes.finite R M)
      (f := id) 0 0 fun _ hp _ _ ↦ hp.isPrime).1 <| by
        simp_rw [id, hzd]
        exact hreg
    exact h p hp hle

namespace TauCeti

/-- Let `M` be a finite module over a Noetherian ring and `I` an ideal. If `depth M_p ≥ n` for
every prime `p` containing `I`, then `I` contains a weakly `M`-regular sequence of length `n`. -/
theorem exists_isWeaklyRegular_of_le_depth_localizedModule (I : Ideal R) (n : ℕ)
    (h : ∀ (p : Ideal R) [p.IsPrime], I ≤ p →
      (n : ℕ∞) ≤ depth (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M))) :
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ IsWeaklyRegular M rs := by
  induction n generalizing M with
  | zero => exact ⟨[], rfl, by simp, IsWeaklyRegular.nil R M⟩
  | succ n ih =>
    -- An associated prime containing `I` would give a localization of depth zero.
    obtain ⟨a, haI, reg⟩ := (I.exists_mem_isSMulRegular_iff (M := M)).2 fun p hp hle ↦ by
      have := hp.isPrime
      have hdepth := h p hle
      rw [depth_localizedModule_eq_zero_iff.2 hp] at hdepth
      exact (Nat.cast_add_one_ne_zero n) (nonpos_iff_eq_zero.1 hdepth)
    -- Dividing by `a` lowers the depth of each localization at a prime `p ⊇ I` by exactly one.
    obtain ⟨rs, hlen, hmem, hrs⟩ := @ih (QuotSMulTop a M) _ _ _ fun p _ hle ↦ by
      let Rₚ := Localization.AtPrime p
      let e : LocalizedModule p.primeCompl (QuotSMulTop a M) ≃ₗ[Rₚ]
          QuotSMulTop (algebraMap R Rₚ a) (LocalizedModule p.primeCompl M) :=
        (localizedQuotientEquiv _ _).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ (by
          rw [Submodule.localized, ← Submodule.ideal_span_singleton_smul,
            Submodule.localized'_smul, Ideal.localized'_eq_map, Submodule.localized'_top,
            Ideal.map_span, Set.image_singleton, Submodule.ideal_span_singleton_smul])
      have hmax : algebraMap R Rₚ a ∈ maximalIdeal Rₚ :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff Rₚ p a).2 (hle haI)
      have hsucc := depth_quotSMulTop_succ_eq_depth (reg.of_isLocalizedModule (S := Rₚ)
        p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M)) hmax
      have hdepth := h p hle
      rw [← hsucc, Nat.cast_add_one] at hdepth
      rw [IsLocalRing.depth_eq_of_linearEquiv e]
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 hdepth
    exact ⟨a :: rs, by simp [hlen], List.forall_mem_cons.2 ⟨haI, hmem⟩,
      (isWeaklyRegular_cons_iff M a rs).2 ⟨reg, hrs⟩⟩

end TauCeti
