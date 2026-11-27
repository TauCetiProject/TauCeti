/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Dimension.DirectSum
public import TauCeti.NumberTheory.ArithmeticFunction.Moebius
public import TauCeti.NumberTheory.Divisors
public import TauCeti.NumberTheory.ModularForms.Newforms.DirectSum
public import TauCeti.NumberTheory.ModularForms.TrivialNebentypus

import TauCeti.NumberTheory.ModularForms.SturmBound

/-!
# Dimensions of newspaces by divisor-count Möbius inversion

Because each level-raising operator `V_d` is injective, the all-divisor direct-sum decompositions of
`TauCeti/NumberTheory/ModularForms/Newforms/DirectSum.lean` turn into divisor-count convolutions for
dimensions:

```text
dim S_k(Γ₁(N)) = ∑_{M ∣ N} σ₀(N / M) · dim S_k(Γ₁(M))ⁿᵉʷ,
dim S_k(N, χ)  = ∑_{cond(χ) ∣ M ∣ N} σ₀(N / M) · dim S_k(M, χ_M)ⁿᵉʷ,
dim S_k(Γ₀(N)) = ∑_{M ∣ N} σ₀(N / M) · dim S_k(M, 1)ⁿᵉʷ.
```

Inverting against `(μ * μ) * σ₀ = 1`
(`ArithmeticFunction.eq_sum_divisors_moebius_mul_moebius_mul_of_dvd`) gives the newspace dimension
formulas of Diamond–Shurman, Theorem 5.8.3, in all integral weights `k`, stated in `ℤ` so
subtraction is not truncated:

```text
dim S_k(Γ₁(N))ⁿᵉʷ = ∑_{M ∣ N} (μ * μ)(N / M) · dim S_k(Γ₁(M)),
dim S_k(N, χ)ⁿᵉʷ  = ∑_{cond(χ) ∣ M ∣ N} (μ * μ)(N / M) · dim S_k(M, χ_M),
dim S_k(N, 1)ⁿᵉʷ  = ∑_{M ∣ N} (μ * μ)(N / M) · dim S_k(Γ₀(M)).
```

## Main results

* `TauCeti.finrank_cuspForm_Gamma1_eq_sum_card_divisors_mul`,
  `TauCeti.finrank_cuspFormCharSpace_eq_sum_dite_card_divisors_mul`,
  `TauCeti.finrank_cuspForm_Gamma0_eq_sum_card_divisors_mul`: the divisor-count dimension
  convolutions for `S_k(Γ₁(N))`, `S_k(N, χ)`, and `S_k(Γ₀(N))`.
* `TauCeti.natCast_finrank_cuspFormsNew_eq_sum_divisors`: the Möbius-inverted dimension formula for
  `S_k(Γ₁(N))ⁿᵉʷ`.
* `TauCeti.natCast_finrank_cuspFormsNew_inf_cuspFormCharSpace_eq_sum_divisors`: the Möbius-inverted
  dimension formula for `S_k(N, χ)ⁿᵉʷ`.
* `TauCeti.natCast_finrank_cuspFormsNew_inf_cuspFormCharSpace_one_eq_sum_divisors`: the
  Möbius-inverted dimension formula for the trivial-nebentypus (`Γ₀(N)`) newspace.
* `TauCeti.newDimension`: the dimension `g⁺(N)` of the weight-two trivial-nebentypus newspace,
  and `TauCeti.newDimension_eq_zero_of_index_lt_six`: it vanishes when `[SL(2, ℤ) : Γ₀(N)] < 6`,
  that is at the levels `1`, `2` and `3`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.3.
* G. Martin, *Dimensions of the spaces of cuspforms and newforms on `Γ₀(N)` and `Γ₁(N)`*,
  J. Number Theory 112 (2005), 298–331, for the notation `g⁺(N)`.
-/

public section

open Finset Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup ArithmeticFunction

open scoped MatrixGroups Moebius

namespace TauCeti

open _root_.CuspForm

/-! ### Forward divisor-count dimension convolutions -/

/-- **Divisor-count dimension formula for `S_k(Γ₁(N))`** (Diamond–Shurman, Theorem 5.8.3):
`dim S_k(Γ₁(N)) = ∑_{M ∣ N} #(N / M).divisors * dim S_k(Γ₁(M))ⁿᵉʷ`. -/
theorem finrank_cuspForm_Gamma1_eq_sum_card_divisors_mul {N : ℕ} [NeZero N] (k : ℤ) :
    Module.finrank ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ∑ M : {M : ℕ+ // (M : ℕ) ∣ N},
        #(N / M.val).divisors * Module.finrank ℂ (cuspFormsNew M.val k) := by
  rw [finrank_eq_sum_finrank_of_isInternal (isInternal_map_levelRaiseₗ_cuspFormsNew N k)]
  simp_rw [CuspForm.finrank_map_levelRaiseₗ]
  simpa only [smul_eq_mul] using
    sum_pnatMulDvd_eq_sum_card_divisors_smul (N := N)
      (fun m ↦ Module.finrank ℂ (cuspFormsNew (m : ℕ) k))

/-- **Divisor-count dimension formula for `S_k(N, χ)`** (Diamond–Shurman, Theorem 5.8.3):
`dim S_k(N, χ) = ∑_{cond(χ) ∣ M ∣ N} #(N / M).divisors * dim S_k(M, χ_M)ⁿᵉʷ`. -/
theorem finrank_cuspFormCharSpace_eq_sum_dite_card_divisors_mul {N : ℕ} [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.finrank ℂ (cuspFormCharSpace k χ) =
      ∑ M : {M : ℕ+ // (M : ℕ) ∣ N},
        if h : DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ M.val then
          #(N / M.val).divisors *
            Module.finrank ℂ ↥(cuspFormsNew M.val k ⊓ cuspFormCharSpace k
              (DirichletCharacter.changeLevel h
                (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom)
        else 0 := by
  rw [← iSup_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace N k χ,
    finrank_iSup_eq_sum_finrank_of_iSupIndep
      (iSupIndep_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace N k χ)]
  simp_rw [CuspForm.finrank_map_levelRaiseₗ]
  simpa only [smul_eq_mul] using
    sum_pnatMulDvdAnd_eq_sum_dite_card_divisors_smul
      (N := N) (fun M : ℕ+ ↦ DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ M)
      (fun M h ↦ Module.finrank ℂ ↥(cuspFormsNew M k ⊓ cuspFormCharSpace k
        (DirichletCharacter.changeLevel h
          (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom))

/-- **Divisor-count dimension formula for `S_k(Γ₀(N))`**:
`dim S_k(Γ₀(N)) = ∑_{M ∣ N} #(N / M).divisors * dim S_k(M, 1)ⁿᵉʷ`. -/
theorem finrank_cuspForm_Gamma0_eq_sum_card_divisors_mul {N : ℕ} [NeZero N] (k : ℤ) :
    Module.finrank ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) k) =
      ∑ M : {M : ℕ+ // (M : ℕ) ∣ N},
        #(N / M.val).divisors *
          Module.finrank ℂ ↥(cuspFormsNew M.val k ⊓
            cuspFormCharSpace k (1 : (ZMod M.val)ˣ →* ℂˣ)) := by
  rw [← (cuspFormCharSpaceOneEquiv N k).finrank_eq,
    finrank_cuspFormCharSpace_eq_sum_dite_card_divisors_mul k (1 : (ZMod N)ˣ →* ℂˣ)]
  refine Finset.sum_congr rfl fun M _ ↦ ?_
  have hdvd : DirichletCharacter.conductor (MulChar.ofUnitHom (1 : (ZMod N)ˣ →* ℂˣ)) ∣ M.val := by
    rw [DirichletCharacter.conductor_ofUnitHom_one]
    exact one_dvd _
  rw [dite_eq_left hdvd, DirichletCharacter.changeLevel_primitiveCharacter_ofUnitHom_one_toUnitHom]

/-! ### Möbius-inverted newspace dimension formulas -/

/-- **Dimension of the `Γ₁(N)` newspace** (Diamond–Shurman, Theorem 5.8.3):
`dim S_k(Γ₁(N))ⁿᵉʷ = ∑_{M ∣ N} (μ * μ)(N / M) · dim S_k(Γ₁(M))`, in all integral weights `k`. -/
theorem natCast_finrank_cuspFormsNew_eq_sum_divisors {N : ℕ} [NeZero N] (k : ℤ) :
    (Module.finrank ℂ (cuspFormsNew N k) : ℤ) =
      ∑ M ∈ N.divisors, (μ * μ) (N / M) *
        (Module.finrank ℂ (CuspForm ((Gamma1 M).map (mapGL ℝ)) k) : ℤ) := by
  let f : ℕ → ℤ := fun d ↦
    if hd : d ≠ 0 then
      have : NeZero d := ⟨hd⟩
      (Module.finrank ℂ (cuspFormsNew d k) : ℤ)
    else 0
  have hN : f N = (Module.finrank ℂ (cuspFormsNew N k) : ℤ) := dite_eq_left (NeZero.ne N)
  rw [← hN]
  refine eq_sum_divisors_moebius_mul_moebius_mul_of_dvd (NeZero.ne N)
    (g := fun m ↦ (Module.finrank ℂ (CuspForm ((Gamma1 m).map (mapGL ℝ)) k) : ℤ)) fun m hmN ↦ ?_
  have : NeZero m := NeZero.of_dvd hmN
  have hm := congrArg (Nat.cast : ℕ → ℤ)
    (finrank_cuspForm_Gamma1_eq_sum_card_divisors_mul (N := m) k)
  rw [Nat.cast_sum] at hm
  rw [hm, ← Finset.sum_coe_sort m.divisors, ← Equiv.sum_comp (pnatDvdEquivDivisors m)]
  refine Finset.sum_congr rfl fun M _ ↦ ?_
  dsimp only [f]
  rw [coe_pnatDvdEquivDivisors_apply, dite_eq_left M.val.ne_zero, Nat.cast_mul]

/-- Dimension in `ℤ` of the fixed-nebentypus newspace `S_k(d, χ_d)ⁿᵉʷ` for `cond(χ) ∣ d` and
`d ≠ 0`, extended by `0` elsewhere. -/
private noncomputable def newCharSpaceDim {N : ℕ} (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (d : ℕ) : ℤ :=
  if hd : DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ d ∧ d ≠ 0 then
    have : NeZero d := ⟨hd.2⟩
    (Module.finrank ℂ ↥(cuspFormsNew d k ⊓
      cuspFormCharSpace k (DirichletCharacter.changeLevel hd.1
        (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom) : ℤ)
  else 0

/-- At an intermediate divisor `m ∣ N` divisible by `cond(χ)`, the dimension of `S_k(m, χ_m)` over
`ℤ` expands as the divisor-count sum over `d ∈ m.divisors` of `newCharSpaceDim k χ d`. -/
private lemma finrank_cuspFormCharSpace_changeLevel_eq_sum_divisors {N m : ℕ} [NeZero N]
    (hmN : m ∣ N) (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (hcm : DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ m) :
    (Module.finrank ℂ (cuspFormCharSpace k
      (DirichletCharacter.changeLevel hcm
        (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom) : ℤ) =
      ∑ d ∈ m.divisors, (#(m / d).divisors : ℤ) * newCharSpaceDim k χ d := by
  have : NeZero m := NeZero.of_dvd hmN
  let c := DirichletCharacter.conductor (MulChar.ofUnitHom χ)
  let ψ₀ := DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)
  let χm := (DirichletCharacter.changeLevel hcm ψ₀).toUnitHom
  have hof : MulChar.ofUnitHom χm = DirichletCharacter.changeLevel hcm ψ₀ := by
    dsimp only [χm]
    rw [MulChar.ofUnitHom_eq, MulChar.toUnitHom_eq, Equiv.symm_apply_apply]
  have hcond_m : DirichletCharacter.conductor (MulChar.ofUnitHom χm) = c := by
    rw [hof, DirichletCharacter.conductor_changeLevel]
    exact DirichletCharacter.primitiveCharacter_isPrimitive (MulChar.ofUnitHom χ)
  have hm := congrArg (Nat.cast : ℕ → ℤ)
    (finrank_cuspFormCharSpace_eq_sum_dite_card_divisors_mul (N := m) k χm)
  rw [Nat.cast_sum] at hm
  let F : ℕ → ℤ := fun d ↦ (#(m / d).divisors : ℤ) * newCharSpaceDim k χ d
  rw [hm, ← Finset.sum_coe_sort m.divisors (f := F), ← (pnatDvdEquivDivisors m).sum_comp]
  refine Finset.sum_congr rfl fun M _ ↦ ?_
  dsimp only [F]
  rw [coe_pnatDvdEquivDivisors_apply, newCharSpaceDim]
  by_cases hcM : c ∣ M.val
  · have hcM' : DirichletCharacter.conductor (MulChar.ofUnitHom χm) ∣ M.val := hcond_m ▸ hcM
    have hcM0 : c ∣ M.val ∧ (M.val : ℕ) ≠ 0 := ⟨hcM, M.val.ne_zero⟩
    rw [dite_eq_left hcM0, dite_eq_left hcM', Nat.cast_mul]
    have hchar : (DirichletCharacter.changeLevel hcM'
        (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χm))).toUnitHom =
        (DirichletCharacter.changeLevel hcM ψ₀).toUnitHom :=
      (DirichletCharacter.eq_changeLevel_primitiveCharacter_toUnitHom_of_comp_unitsMap_eq M.property
        (by rw [← DirichletCharacter.changeLevel_toUnitHom, ← DirichletCharacter.changeLevel_trans])
        hcM').symm
    rw [hchar]
  · have hcM' : ¬ DirichletCharacter.conductor (MulChar.ofUnitHom χm) ∣ M.val := hcond_m ▸ hcM
    have hcM0 : ¬ (c ∣ M.val ∧ (M.val : ℕ) ≠ 0) := fun h ↦ hcM h.1
    rw [dite_eq_right hcM0, dite_eq_right hcM', mul_zero, Nat.cast_zero]

/-- **Dimension of the fixed-nebentypus newspace `S_k(N, χ)ⁿᵉʷ`** (Diamond–Shurman,
Theorem 5.8.3): `dim S_k(N, χ)ⁿᵉʷ = ∑_{cond(χ) ∣ M ∣ N} (μ * μ)(N / M) · dim S_k(M, χ_M)` in all
integral weights `k`, where `χ_M` is the raise of the primitive character of `χ` to level `M`. -/
theorem natCast_finrank_cuspFormsNew_inf_cuspFormCharSpace_eq_sum_divisors {N : ℕ} [NeZero N]
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    (Module.finrank ℂ ↥(cuspFormsNew N k ⊓ cuspFormCharSpace k χ) : ℤ) =
      ∑ M ∈ N.divisors,
        if h : DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ M then
          (μ * μ) (N / M) *
            (Module.finrank ℂ (cuspFormCharSpace k
              (DirichletCharacter.changeLevel h
                (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom) : ℤ)
        else 0 := by
  let c := DirichletCharacter.conductor (MulChar.ofUnitHom χ)
  let ψ₀ := DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)
  let g : ℕ → ℤ := fun m ↦
    if hm : c ∣ m then
      (Module.finrank ℂ (cuspFormCharSpace k
        (DirichletCharacter.changeLevel hm ψ₀).toUnitHom) : ℤ)
    else 0
  have hχN : (DirichletCharacter.changeLevel
      (DirichletCharacter.conductor_dvd_level (MulChar.ofUnitHom χ)) ψ₀).toUnitHom = χ := by
    simpa [ψ₀] using DirichletCharacter.changeLevel_primitiveCharacter_toUnitHom_comp_unitsMap
      dvd_rfl (DirichletCharacter.conductor_dvd_level (MulChar.ofUnitHom χ))
  have hcN : c ∣ N ∧ N ≠ 0 :=
    ⟨DirichletCharacter.conductor_dvd_level (MulChar.ofUnitHom χ), NeZero.ne N⟩
  have hfN : newCharSpaceDim k χ N =
      (Module.finrank ℂ ↥(cuspFormsNew N k ⊓ cuspFormCharSpace k χ) : ℤ) := by
    rw [newCharSpaceDim, dite_eq_left hcN, hχN]
  have hsum : newCharSpaceDim k χ N = ∑ M ∈ N.divisors, (μ * μ) (N / M) * g M := by
    refine eq_sum_divisors_moebius_mul_moebius_mul_of_dvd (NeZero.ne N) fun m hmN ↦ ?_
    by_cases hcm : c ∣ m
    · dsimp only [g]
      rw [dite_eq_left hcm]
      exact (finrank_cuspFormCharSpace_changeLevel_eq_sum_divisors hmN k χ hcm).symm
    · dsimp only [g]
      rw [dite_eq_right hcm]
      refine Finset.sum_eq_zero fun d hd ↦ ?_
      have hcd : ¬ (c ∣ d ∧ d ≠ 0) := fun h ↦ hcm (h.1.trans (Nat.dvd_of_mem_divisors hd))
      rw [newCharSpaceDim, dite_eq_right hcd, mul_zero]
  rw [← hfN, hsum]
  refine Finset.sum_congr rfl fun M _ ↦ ?_
  by_cases hcM : c ∣ M
  · dsimp only [g]
    rw [dite_eq_left hcM, dite_eq_left hcM]
  · dsimp only [g]
    rw [dite_eq_right hcM, dite_eq_right hcM, mul_zero]

/-- **Dimension of the trivial-nebentypus (`Γ₀(N)`) newspace** (Diamond–Shurman, Theorem 5.8.3):
`dim S_k(N, 1)ⁿᵉʷ = ∑_{M ∣ N} (μ * μ)(N / M) · dim S_k(Γ₀(M))`, in all integral weights `k`. -/
theorem natCast_finrank_cuspFormsNew_inf_cuspFormCharSpace_one_eq_sum_divisors {N : ℕ} [NeZero N]
    (k : ℤ) :
    (Module.finrank ℂ ↥(cuspFormsNew N k ⊓ cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) : ℤ) =
      ∑ M ∈ N.divisors, (μ * μ) (N / M) *
        (Module.finrank ℂ (CuspForm ((Gamma0 M).map (mapGL ℝ)) k) : ℤ) := by
  rw [natCast_finrank_cuspFormsNew_inf_cuspFormCharSpace_eq_sum_divisors k (1 : (ZMod N)ˣ →* ℂˣ)]
  refine Finset.sum_congr rfl fun M hM ↦ ?_
  have : NeZero M := ⟨(Nat.pos_of_mem_divisors hM).ne'⟩
  have hdvd : DirichletCharacter.conductor (MulChar.ofUnitHom (1 : (ZMod N)ˣ →* ℂˣ)) ∣ M := by
    rw [DirichletCharacter.conductor_ofUnitHom_one]
    exact one_dvd M
  rw [dite_eq_left hdvd, DirichletCharacter.changeLevel_primitiveCharacter_ofUnitHom_one_toUnitHom,
    (cuspFormCharSpaceOneEquiv M k).finrank_eq]

/-! ### The weight-two trivial-nebentypus newspace dimension -/

/-- **The dimension `g⁺(N)` of the weight-two newspace on `Γ₀(N)`**: the complex dimension of the
intersection of the `Γ₁(N)` newspace `S₂(Γ₁(N))ⁿᵉʷ` with the trivial-nebentypus eigenspace. It is
the number of weight-two newforms of level `N` with trivial character. -/
noncomputable def newDimension (N : ℕ) [NeZero N] : ℕ :=
  Module.finrank ℂ ↥(cuspFormsNew N 2 ⊓ cuspFormCharSpace 2 (1 : (ZMod N)ˣ →* ℂˣ))

theorem newDimension_def (N : ℕ) [NeZero N] :
    newDimension N =
      Module.finrank ℂ ↥(cuspFormsNew N 2 ⊓ cuspFormCharSpace 2 (1 : (ZMod N)ˣ →* ℂˣ)) :=
  (rfl)

/-- **No weight-two newforms at levels of index below six.** If `[SL(2, ℤ) : Γ₀(N)] < 6`, already
the whole space `S₂(Γ₀(N))` vanishes by the Sturm bound, so `g⁺(N) = 0`. This covers the levels
`N = 1, 2, 3`, of indices `1, 3, 4`. -/
theorem newDimension_eq_zero_of_index_lt_six {N : ℕ} [NeZero N] (h : (Gamma0 N).index < 6) :
    newDimension N = 0 := by
  rw [newDimension_def, Submodule.finrank_eq_zero, eq_bot_iff]
  intro f hf
  have hf0 : (⟨f, hf.2⟩ : cuspFormCharSpace 2 (1 : (ZMod N)ˣ →* ℂˣ)) = 0 :=
    (cuspFormCharSpaceOneEquiv N 2).injective <| by
      rw [_root_.map_zero]
      exact CuspForm.eq_zero_of_mul_index_lt_twelve (by omega) _
  exact (Submodule.mem_bot ℂ).mpr (congrArg Subtype.val hf0)

/-- There are no weight-two newforms of level one: `g⁺(1) = 0`. -/
@[simp]
theorem newDimension_one : newDimension 1 = 0 :=
  newDimension_eq_zero_of_index_lt_six (by simp)

end TauCeti
