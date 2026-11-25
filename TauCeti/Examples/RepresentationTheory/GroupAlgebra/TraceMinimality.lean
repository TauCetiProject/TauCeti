/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.Block

/-!
# Trace minimality on `𝔽₂[S₃]`

The relative trace `Tr_1^{S₃}(a) = ∑_g g a g⁻¹` has coefficient `|C_G(c)|` times the coefficient sum
of `a` on the class of `c` at `c`. As `|C_G(1)| = 6`, `|C_G(ρ)| = 3` and `|C_G(t)| = 2`, over `𝔽₂`
only the `3`-cycles survive: `Tr_1^{S₃}(a) = (a(ρ) + a(ρ²)) (ρ + ρ²)`, so
`Tr_1^{S₃}(𝔽₂[S₃]) = 𝔽₂ (ρ + ρ²)`. It contains the block `e₁ = ρ + ρ² = Tr_1^{S₃}(ρ)`, of defect
group `1`, and not the principal block `e₀ = 1 + ρ + ρ²`, for which
`Tr_{⟨t⟩}^{S₃}(e₀) = 3 e₀ = e₀`. Taking maximal instead of minimal subgroups `P` with
`e ∈ Tr_P^{S₃}(𝔽₂[S₃]^P)` would give `S₃` for both blocks.

These are the trace-minimality Checks of §6.2 *Defect groups* of the
RepresentationTheory/ModularCharactersAndBlocks roadmap.
-/

public section

namespace TauCeti.GroupAlgebraTraceMinimalityExamples

open _root_.MonoidAlgebra TauCeti.GroupAlgebraBlockExamples

/-- The transposition `t = (0 1)` of `S₃`. -/
abbrev t : S₃ := Equiv.swap 0 1

/-- The number of `g` with `g⁻¹ c g = h`, read in `𝔽₂`: `|C_G(c)|` if `h` is conjugate to `c`,
which is odd only for the `3`-cycles. -/
private theorem card_filter_conj_eq (c h : S₃) :
    ((Finset.univ.filter fun g : S₃ => g⁻¹ * c * g = h).card : ZMod 2) =
      if (c ≠ 1 ∧ c * c * c = 1) ∧ (h ≠ 1 ∧ h * h * h = 1) then 1 else 0 := by
  revert c h
  decide +kernel

/-- The `3`-cycles of `S₃` are `ρ` and `ρ²`. -/
private theorem filter_threeCycle_eq :
    (Finset.univ.filter fun h : S₃ => h ≠ 1 ∧ h * h * h = 1) = {ρ, ρ ^ 2} := by
  decide +kernel

/-- Summing a function over the conjugates `g⁻¹ c g`, over `𝔽₂`. -/
theorem sum_conj_eq (f : S₃ → ZMod 2) (c : S₃) :
    ∑ g : S₃, f (g⁻¹ * c * g) =
      (if c ≠ 1 ∧ c * c * c = 1 then 1 else 0) * (f ρ + f (ρ ^ 2)) := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun g : S₃ => g⁻¹ * c * g)]
  have hfib (h : S₃) : ∑ g ∈ Finset.univ.filter (fun g : S₃ => g⁻¹ * c * g = h),
      f (g⁻¹ * c * g) =
        (if (c ≠ 1 ∧ c * c * c = 1) ∧ (h ≠ 1 ∧ h * h * h = 1) then 1 else 0) * f h := by
    rw [Finset.sum_congr rfl fun g hg => by rw [(Finset.mem_filter.1 hg).2], Finset.sum_const,
      nsmul_eq_mul, card_filter_conj_eq]
  simp_rw [hfib]
  by_cases hc : c ≠ 1 ∧ c * c * c = 1
  · have hB (h : S₃) : ((c ≠ 1 ∧ c * c * c = 1) ∧ (h ≠ 1 ∧ h * h * h = 1)) ↔
        (h ≠ 1 ∧ h * h * h = 1) := and_iff_right hc
    simp only [hB, ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter, filter_threeCycle_eq, Finset.sum_pair (by decide)]
    exact (ite_eq_left hc).symm
  · simp [hc]

/-- The transversal `g ↦ g` of the trivial subgroup in `S₃`. -/
private theorem bijective_mk_bot :
    Function.Bijective fun g : S₃ =>
      ((⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup S₃)) :
        (⊤ : Subgroup S₃) ⧸ (⊥ : Subgroup S₃).subgroupOf ⊤) := by
  refine ⟨fun a b hab => ?_, fun q => ?_⟩
  · have := QuotientGroup.leftRel_apply.1 (Quotient.exact hab)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot] at this
    simpa [inv_mul_eq_one] using this
  · induction q using QuotientGroup.induction_on with
    | H x => exact ⟨x, rfl⟩

/-- **The trace from the trivial subgroup on `𝔽₂[S₃]`**: `Tr_1^{S₃}(a) = (a(ρ) + a(ρ²)) (ρ + ρ²)`.
In particular `Tr_1^{S₃}(𝔽₂[S₃]) = 𝔽₂ (ρ + ρ²)`. -/
theorem relTrace_bot_top_eq (a : conjInvariants (ZMod 2) (⊥ : Subgroup S₃)) :
    (relTrace (ZMod 2) ⊥ ⊤ a : MonoidAlgebra (ZMod 2) S₃) =
      ((a : MonoidAlgebra (ZMod 2) S₃).coeff ρ + (a : MonoidAlgebra (ZMod 2) S₃).coeff (ρ ^ 2)) •
        (of (ZMod 2) S₃ ρ + of (ZMod 2) S₃ (ρ ^ 2)) := by
  rw [relTrace_apply_eq_sum_of_bijective _ bijective_mk_bot]
  refine ext (Finsupp.ext fun c => ?_)
  rw [coeff_sum, Finsupp.finsetSum_apply]
  simp only [coeff_conjRepresentation, coeff_smul, Finsupp.smul_apply, smul_eq_mul,
    ← coe_blockTwoS₃, coeff_blockTwoS₃]
  rw [sum_conj_eq, mul_comm]

/-- An element of `𝔽₂[S₃]`, as an element of `𝔽₂[S₃]^1`. -/
noncomputable def toBot (x : MonoidAlgebra (ZMod 2) S₃) :
    conjInvariants (ZMod 2) (⊥ : Subgroup S₃) :=
  ⟨x, by rw [conjInvariants_bot]; trivial⟩

/-- `e₁ = ρ + ρ² = Tr_1^{S₃}(ρ)`. -/
theorem relTrace_bot_top_of_ρ :
    (relTrace (ZMod 2) ⊥ ⊤ (toBot (of (ZMod 2) S₃ ρ)) : MonoidAlgebra (ZMod 2) S₃) =
      of (ZMod 2) S₃ ρ + of (ZMod 2) S₃ (ρ ^ 2) := by
  rw [relTrace_bot_top_eq]
  have h : (of (ZMod 2) S₃ ρ).coeff ρ + (of (ZMod 2) S₃ ρ).coeff (ρ ^ 2) = 1 := by
    simp only [of_apply, coeff_single, Finsupp.single_apply]
    decide +kernel
  rw [show (toBot (of (ZMod 2) S₃ ρ) : MonoidAlgebra (ZMod 2) S₃) = of (ZMod 2) S₃ ρ from rfl, h,
    one_smul]

/-- The principal block `e₀ = 1 + ρ + ρ²` is not a trace from the trivial subgroup: every
`Tr_1^{S₃}(a)` has coefficient `0` at `1`. -/
theorem not_mem_relTraceIdeal_bot_one_add_of_ρ_add_of_ρ_sq :
    (⟨_, conjInvariants_top (R := ZMod 2) (G := S₃) ▸ one_add_of_ρ_add_of_ρ_sq_mem_center⟩ :
      conjInvariants (ZMod 2) (⊤ : Subgroup S₃)) ∉
        relTraceIdeal (ZMod 2) (bot_le : (⊥ : Subgroup S₃) ≤ ⊤) := by
  intro hmem
  obtain ⟨a, ha⟩ := (mem_relTraceIdeal_iff _).1 hmem
  have h := congrArg (fun x : conjInvariants (ZMod 2) (⊤ : Subgroup S₃) =>
    (x : MonoidAlgebra (ZMod 2) S₃).coeff 1) ha
  simp only [relTrace_bot_top_eq, coeff_smul, Finsupp.smul_apply, smul_eq_mul,
    ← coe_blockTwoS₃, coeff_blockTwoS₃, ne_eq, not_true_eq_false, false_and, ite_false,
    mul_zero] at h
  revert h
  simp only [coeff_add, Finsupp.add_apply, of_apply, one_def, coeff_single, Finsupp.single_apply]
  decide +kernel

/-- `Tr_{⟨t⟩}^{S₃}(e₀) = 3 e₀ = e₀`: the principal block is a trace from a subgroup of order `2`. -/
theorem relTrace_zpowers_t_top_one_add_of_ρ_add_of_ρ_sq :
    (relTrace (ZMod 2) (Subgroup.zpowers t) ⊤
        ⟨_, conjInvariants_anti le_top
          (conjInvariants_top (R := ZMod 2) (G := S₃) ▸ one_add_of_ρ_add_of_ρ_sq_mem_center)⟩ :
        MonoidAlgebra (ZMod 2) S₃) =
      1 + of (ZMod 2) S₃ ρ + of (ZMod 2) S₃ (ρ ^ 2) := by
  have he₀ : 1 + of (ZMod 2) S₃ ρ + of (ZMod 2) S₃ (ρ ^ 2) ∈
      conjInvariants (ZMod 2) (⊤ : Subgroup S₃) :=
    conjInvariants_top (R := ZMod 2) (G := S₃) ▸ one_add_of_ρ_add_of_ρ_sq_mem_center
  rw [relTrace_apply_of_mem he₀]
  have hindex : ((Subgroup.zpowers t).subgroupOf ⊤).index = 3 := by
    have hcard : Nat.card (Subgroup.zpowers t) = 2 := by
      rw [Nat.card_zpowers]
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by decide) (by decide)
    have hmul := (Subgroup.zpowers t).index_mul_card
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at hmul
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    norm_num [Nat.factorial] at hmul
    omega
  rw [hindex, ← Nat.cast_smul_eq_nsmul (ZMod 2), show ((3 : ℕ) : ZMod 2) = 1 by decide, one_smul]

/-- Taking maximal instead of minimal subgroups would give `S₃` for both blocks: every element of
`𝔽₂[S₃]^{S₃}` is a trace from `S₃` itself. -/
example : relTraceIdeal (ZMod 2) (le_refl (⊤ : Subgroup S₃)) = ⊤ :=
  relTraceIdeal_self

end TauCeti.GroupAlgebraTraceMinimalityExamples
