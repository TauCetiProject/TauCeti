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

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.3.
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
        #(N / M.1).divisors * Module.finrank ℂ (cuspFormsNew M.1 k) := by
  rw [finrank_eq_sum_finrank_of_isInternal (isInternal_map_levelRaiseₗ_cuspFormsNew N k)]
  have hmap (p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}) :
      Module.finrank ℂ ↥((cuspFormsNew p.1.1 k).map
        (CuspForm.levelRaiseₗ p.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd p.2))) =
        Module.finrank ℂ (cuspFormsNew p.1.1 k) :=
    ((cuspFormsNew p.1.1 k).equivMapOfInjective _
      (CuspForm.levelRaiseₗ_injective p.1.2
        (Gamma1_map_le_conjAct_scaleGL_of_dvd p.2))).finrank_eq.symm
  simp_rw [hmap]
  rw [← (pnatMulDvdEquivSigma N).symm.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun M _ ↦ ?_
  let f : ℕ+ → ℕ := fun m ↦ Module.finrank ℂ (cuspFormsNew (m : ℕ) k)
  exact (Finset.sum_congr rfl fun d _ ↦
    congrArg f (fst_val_pnatMulDvdEquivSigma_symm_apply ⟨M, d⟩)).trans (by simp [f])

/-- **Divisor-count dimension formula for `S_k(N, χ)`** (Diamond–Shurman, Theorem 5.8.3):
`dim S_k(N, χ) = ∑_{cond(χ) ∣ M ∣ N} #(N / M).divisors * dim S_k(M, χ_M)ⁿᵉʷ`. -/
theorem finrank_cuspFormCharSpace_eq_sum_dite_card_divisors_mul {N : ℕ} [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.finrank ℂ (cuspFormCharSpace k χ) =
      ∑ M : {M : ℕ+ // (M : ℕ) ∣ N},
        if h : DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ M.1 then
          #(N / M.1).divisors *
            Module.finrank ℂ ↥(cuspFormsNew M.1 k ⊓ cuspFormCharSpace k
              (DirichletCharacter.changeLevel h
                (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom)
        else 0 := by
  let c := DirichletCharacter.conductor (MulChar.ofUnitHom χ)
  let ψ₀ := DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)
  rw [← iSup_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace N k χ,
    finrank_iSup_eq_sum_finrank_of_iSupIndep
      (iSupIndep_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace N k χ)]
  have hmap (p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N ∧ c ∣ p.1}) :
      Module.finrank ℂ ↥((cuspFormsNew p.1.1 k ⊓ cuspFormCharSpace k
        (DirichletCharacter.changeLevel p.2.2 ψ₀).toUnitHom).map
        (CuspForm.levelRaiseₗ p.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd p.2.1))) =
        Module.finrank ℂ ↥(cuspFormsNew p.1.1 k ⊓
          cuspFormCharSpace k (DirichletCharacter.changeLevel p.2.2 ψ₀).toUnitHom) :=
    (Submodule.equivMapOfInjective _
      (CuspForm.levelRaiseₗ_injective p.1.2
        (Gamma1_map_le_conjAct_scaleGL_of_dvd p.2.1)) _).finrank_eq.symm
  dsimp only [c, ψ₀] at hmap
  simp_rw [hmap]
  -- Reindex `(M, d)` with `d * M ∣ N` and `c ∣ M` as a sigma over `{M // c ∣ M}` and
  -- `(N / M).divisors`, then sum the constant fiber and rewrite as a `dite` over all `M ∣ N`.
  rw [← (pnatMulDvdAndEquivSigma N (fun M : ℕ+ ↦ c ∣ (M : ℕ))).symm.sum_comp,
    Fintype.sum_sigma]
  let f : {m : ℕ+ // c ∣ (m : ℕ)} → ℕ := fun m ↦
    Module.finrank ℂ ↥(cuspFormsNew (m.1 : ℕ) k ⊓
      cuspFormCharSpace k (DirichletCharacter.changeLevel m.2 ψ₀).toUnitHom)
  have hinner (M : {M : {M : ℕ+ // (M : ℕ) ∣ N} // c ∣ M.1}) :
      (∑ d : (N / M.1.1).divisors,
        f ⟨((pnatMulDvdAndEquivSigma N (fun M : ℕ+ ↦ c ∣ (M : ℕ))).symm ⟨M, d⟩).1.1,
          ((pnatMulDvdAndEquivSigma N (fun M : ℕ+ ↦ c ∣ (M : ℕ))).symm ⟨M, d⟩).2.2⟩) =
        #(N / M.1.1).divisors * f ⟨M.1.1, M.2⟩ := by
    have hterm (d : (N / M.1.1).divisors) :
        f ⟨((pnatMulDvdAndEquivSigma N (fun M : ℕ+ ↦ c ∣ (M : ℕ))).symm ⟨M, d⟩).1.1,
          ((pnatMulDvdAndEquivSigma N (fun M : ℕ+ ↦ c ∣ (M : ℕ))).symm ⟨M, d⟩).2.2⟩ =
          f ⟨M.1.1, M.2⟩ :=
      congrArg f (Subtype.ext
        (fst_val_pnatMulDvdAndEquivSigma_symm_apply (P := fun M : ℕ+ ↦ c ∣ (M : ℕ)) ⟨M, d⟩))
    rw [Finset.sum_congr rfl fun d _ ↦ hterm d, Finset.sum_const, Finset.card_univ,
      Fintype.card_coe, smul_eq_mul]
  rw [Finset.sum_congr rfl fun M _ ↦ hinner M, Finset.sum_dite, Finset.sum_const_zero, add_zero]
  let e : {x : {M : ℕ+ // (M : ℕ) ∣ N} //
      x ∈ ({x ∈ Finset.univ | c ∣ (x.1 : ℕ)} : Finset {M : ℕ+ // (M : ℕ) ∣ N})} ≃
      {M : {M : ℕ+ // (M : ℕ) ∣ N} // c ∣ (M.1 : ℕ)} :=
    Equiv.subtypeEquivRight fun x ↦ Finset.mem_filter_univ x
  exact (e.sum_comp fun M ↦ #(N / M.1.1).divisors * f ⟨M.1.1, M.2⟩).symm

/-- **Divisor-count dimension formula for `S_k(Γ₀(N))`**:
`dim S_k(Γ₀(N)) = ∑_{M ∣ N} #(N / M).divisors * dim S_k(M, 1)ⁿᵉʷ`. -/
theorem finrank_cuspForm_Gamma0_eq_sum_card_divisors_mul {N : ℕ} [NeZero N] (k : ℤ) :
    Module.finrank ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) k) =
      ∑ M : {M : ℕ+ // (M : ℕ) ∣ N},
        #(N / M.1).divisors *
          Module.finrank ℂ ↥(cuspFormsNew M.1 k ⊓
            cuspFormCharSpace k (1 : (ZMod M.1)ˣ →* ℂˣ)) := by
  rw [← (cuspFormCharSpaceOneEquiv N k).finrank_eq,
    finrank_cuspFormCharSpace_eq_sum_dite_card_divisors_mul k (1 : (ZMod N)ˣ →* ℂˣ)]
  refine Finset.sum_congr rfl fun M _ ↦ ?_
  have hdvd : DirichletCharacter.conductor (MulChar.ofUnitHom (1 : (ZMod N)ˣ →* ℂˣ)) ∣ M.1 := by
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
  rw [coe_pnatDvdEquivDivisors_apply, dite_eq_left M.1.ne_zero, Nat.cast_mul]

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
  by_cases hcM : c ∣ M.1
  · have hcM' : DirichletCharacter.conductor (MulChar.ofUnitHom χm) ∣ M.1 := hcond_m ▸ hcM
    have hcM0 : c ∣ M.1 ∧ (M.1 : ℕ) ≠ 0 := ⟨hcM, M.1.ne_zero⟩
    rw [dite_eq_left hcM0, dite_eq_left hcM', Nat.cast_mul]
    have hchar : (DirichletCharacter.changeLevel hcM'
        (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χm))).toUnitHom =
        (DirichletCharacter.changeLevel hcM ψ₀).toUnitHom :=
      (DirichletCharacter.eq_changeLevel_primitiveCharacter_toUnitHom_of_comp_unitsMap_eq M.2
        (by rw [← DirichletCharacter.changeLevel_toUnitHom, ← DirichletCharacter.changeLevel_trans])
        hcM').symm
    rw [hchar]
  · have hcM' : ¬ DirichletCharacter.conductor (MulChar.ofUnitHom χm) ∣ M.1 := hcond_m ▸ hcM
    have hcM0 : ¬ (c ∣ M.1 ∧ (M.1 : ℕ) ≠ 0) := fun h ↦ hcM h.1
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

end TauCeti
