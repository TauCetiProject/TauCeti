/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Quotient maps out of an adic completion

Let `I` and `J` be ideals of a commutative ring `R` and `M` an `R`-module. The maps from the
`J`-adic completion `M̂_J` to `M ⧸ (Iⁿ M + Jᵐ M)` annihilate `Iⁿ M̂_J`. If `I = (p)` and `p` is
regular modulo every power of `J`, their common kernel is exactly `pⁿ M̂_J`: division by `pⁿ`
can be performed levelwise, and regularity makes the quotients compatible.

Every compatible system of classes modulo `Iⁿ M + Jᵐ M` lifts to `M̂_J`, without any regularity
hypothesis. Splitting consecutive differences into terms in `Iⁿ M` and `Jᵐ M` gives a `J`-adic
Cauchy sequence with the required images. These kernel and lifting results are the inputs to
the iterated-completion comparison in `TauCeti.RingTheory.AdicCompletion.Iterated`.

## Main results

* `AdicCompletion.exists_eq_smul_of_forall_exists_val_eq_smul`: divisibility by an element regular
  modulo every `Jᵐ M` is detected levelwise.
* `AdicCompletion.factor_val_eq_zero_of_mem`: the quotient maps annihilate `Iⁿ M̂_J`.
* `AdicCompletion.mem_span_singleton_pow_smul_top_iff`: under regularity, these maps detect
  membership in `pⁿ M̂_J`.
* `AdicCompletion.exists_forall_factor_val_eq`: every compatible system of quotient classes lifts
  to the completion.
-/

public noncomputable section

open Submodule

namespace AdicCompletion

variable {R : Type*} [CommRing R] {I J : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]

/-- **Divisibility in a completion is detected levelwise.** If `r` is regular on `M ⧸ Jᵐ M` for
every `m`, and every component of `c ∈ M̂_J` is divisible by `r`, then `c` is divisible by `r`
in `M̂_J`. -/
theorem exists_eq_smul_of_forall_exists_val_eq_smul {r : R}
    (hr : ∀ m : ℕ, IsSMulRegular (M ⧸ (J ^ m • ⊤ : Submodule R M)) r) {c : AdicCompletion J M}
    (hc : ∀ m : ℕ, ∃ d, c.val m = r • d) : ∃ d : AdicCompletion J M, c = r • d := by
  choose d hd using hc
  refine ⟨⟨d, fun {m n} hmn ↦ hr m ?_⟩, ext fun m ↦ hd m⟩
  dsimp only
  rw [← map_smul, ← hd, ← hd, c.prop hmn]

/-- The kernel of `M̂_J → M ⧸ (Iⁿ M + Jᵐ M)`, for all `m`, contains `Iⁿ M̂_J`. -/
theorem factor_val_eq_zero_of_mem {n : ℕ} {c : AdicCompletion J M}
    (hc : c ∈ (I ^ n • ⊤ : Submodule R (AdicCompletion J M))) (m : ℕ) :
    factor (le_sup_right : (J ^ m • ⊤ : Submodule R M) ≤ I ^ n • ⊤ ⊔ J ^ m • ⊤) (c.val m) = 0 := by
  refine smul_induction_on hc (fun r hr c _ ↦ ?_) fun c c' hc hc' ↦ ?_
  · rw [val_smul_apply, map_smul]
    induction c.val m using Submodule.Quotient.induction_on with
    | H a =>
      rw [mapQ_apply, LinearMap.id_apply, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero]
      exact mem_sup_left (smul_mem_smul hr mem_top)
  · rw [val_add_apply, map_add, hc, hc', add_zero]

/-- For `p` regular modulo every `Jᵐ M`, membership in `pⁿ M̂_J` is detected by the maps
`M̂_J → M ⧸ (pⁿ M + Jᵐ M)`. -/
theorem mem_span_singleton_pow_smul_top_iff {p : R}
    (hp : ∀ m : ℕ, IsSMulRegular (M ⧸ (J ^ m • ⊤ : Submodule R M)) p) {n : ℕ}
    {c : AdicCompletion J M} :
    c ∈ (Ideal.span {p} ^ n • ⊤ : Submodule R (AdicCompletion J M)) ↔
      ∀ m : ℕ, factor (le_sup_right : (J ^ m • ⊤ : Submodule R M) ≤
        Ideal.span {p} ^ n • ⊤ ⊔ J ^ m • ⊤) (c.val m) = 0 := by
  constructor
  · exact fun hc m ↦ factor_val_eq_zero_of_mem hc m
  · intro hc
    obtain ⟨d, rfl⟩ := exists_eq_smul_of_forall_exists_val_eq_smul (fun m ↦ (hp m).pow n)
      fun m ↦ by
        have hcm := hc m
        obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (c.val m)
        rw [← ha, mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
          Ideal.span_singleton_pow, ideal_span_singleton_smul] at hcm
        obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.1 hcm
        obtain ⟨b, -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).1 hy
        refine ⟨Submodule.Quotient.mk b, ?_⟩
        rw [← ha, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, add_sub_cancel_left]
        exact hz
    rw [Ideal.span_singleton_pow, ideal_span_singleton_smul]
    exact smul_mem_pointwise_smul _ _ _ mem_top

/-- Every compatible system of classes modulo `Iⁿ M + Jᵐ M`, `m ∈ ℕ`, lifts to `M̂_J`. -/
theorem exists_forall_factor_val_eq (n : ℕ) (s : ℕ → M)
    (hs : ∀ m, s m ≡ s (m + 1) [SMOD (I ^ n • ⊤ ⊔ J ^ m • ⊤ : Submodule R M)]) :
    ∃ c : AdicCompletion J M, ∀ m, factor (le_sup_right : (J ^ m • ⊤ : Submodule R M) ≤
      I ^ n • ⊤ ⊔ J ^ m • ⊤) (c.val m) = Submodule.Quotient.mk (s m) := by
  -- Split each difference `s (m + 1) - s m` into a part `a m ∈ Iⁿ M` and a part `b m ∈ Jᵐ M`.
  have h (m : ℕ) : ∃ a ∈ (I ^ n • ⊤ : Submodule R M), ∃ b ∈ (J ^ m • ⊤ : Submodule R M),
      a + b = s (m + 1) - s m :=
    mem_sup.1 ((SModEq.sub_mem.1 (hs m).symm))
  choose a ha b hb hab using h
  -- The partial sums of the `b m` form a `J`-adic Cauchy sequence.
  let f : AdicCauchySequence J M := AdicCauchySequence.mk J M
    (fun m ↦ s 0 + ∑ k ∈ Finset.range m, b k) fun m ↦ by
      rw [SModEq.sub_mem, Finset.sum_range_succ]
      simpa using neg_mem (hb m)
  have hf (m : ℕ) : s m - f m ∈ (I ^ n • ⊤ : Submodule R M) := by
    induction m with
    | zero => simp [f]
    | succ m ih =>
      have : s (m + 1) - f (m + 1) = (s m - f m) + a m := by
        simp only [f, AdicCauchySequence.mk_coe, Finset.sum_range_succ]
        rw [← sub_add_cancel (s (m + 1)) (s m), ← hab m]
        abel
      rw [this]
      exact add_mem ih (ha m)
  refine ⟨mk J M f, fun m ↦ ?_⟩
  rw [mk_apply_coe, mkQ_apply, mapQ_apply, LinearMap.id_apply, Submodule.Quotient.eq]
  rw [← neg_mem_iff, neg_sub]
  exact mem_sup_left (hf m)

end AdicCompletion
