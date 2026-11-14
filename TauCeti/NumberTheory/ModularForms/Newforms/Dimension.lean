/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Dimension.DirectSum
public import TauCeti.NumberTheory.ArithmeticFunction.Moebius
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

* `HeckeRing.GL2.Newform.finrank_cuspFormsNew`: `dim S_k(Γ₁(N))ⁿᵉʷ` equals the number of newforms
  of level `N` and weight `k`.
* `TauCeti.finrank_cuspFormsNew_comap_cuspFormCharSpace_eq_inf`: the two spellings of
  `dim S_k(N, χ)ⁿᵉʷ` (inside `S_k(N, χ)` and in `S_k(Γ₁(N))`) agree.
* `TauCeti.finrank_cuspForm_Gamma1_eq_sum_divisors`,
  `TauCeti.finrank_cuspFormCharSpace_eq_sum_divisors`,
  `TauCeti.finrank_cuspForm_Gamma0_eq_sum_divisors`: the divisor-count dimension convolutions for
  `S_k(Γ₁(N))`, `S_k(N, χ)`, and `S_k(Γ₀(N))`.
* `TauCeti.finrank_cuspFormsNew`: the Möbius-inverted dimension formula for `S_k(Γ₁(N))ⁿᵉʷ`.
* `TauCeti.finrank_cuspFormsNew_inf_cuspFormCharSpace`: the Möbius-inverted dimension formula for
  `S_k(N, χ)ⁿᵉʷ`.
* `TauCeti.finrank_cuspFormsNew_inf_cuspFormCharSpace_one`: the Möbius-inverted dimension formula
  for the trivial-nebentypus (`Γ₀(N)`) newspace.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.3.
-/

public section

open Finset Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup ArithmeticFunction

open scoped MatrixGroups Moebius

namespace HeckeRing.GL2.Newform

/-- **The dimension of `S_k(Γ₁(N))ⁿᵉʷ` is the number of newforms of level `N` and weight `k`.** -/
theorem finrank_cuspFormsNew (N : ℕ) [NeZero N] (k : ℤ) :
    Module.finrank ℂ (TauCeti.cuspFormsNew N k) = Nat.card (Newform N k) :=
  Module.finrank_eq_nat_card_basis (basis N k)

end HeckeRing.GL2.Newform

namespace TauCeti

open _root_.CuspForm

/-! ### Dimension of `S_k(N, χ)ⁿᵉʷ` in the two submodule spellings -/

/-- The dimension of `S_k(N, χ)ⁿᵉʷ` written inside `S_k(N, χ)` via `Submodule.comap` agrees with its
dimension as the intersection `S_k(Γ₁(N))ⁿᵉʷ ⊓ S_k(N, χ)` in `S_k(Γ₁(N))`. -/
theorem finrank_cuspFormsNew_comap_cuspFormCharSpace_eq_inf {N : ℕ} [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.finrank ℂ ↥((cuspFormsNew N k).comap (cuspFormCharSpace k χ).subtype) =
      Module.finrank ℂ ↥(cuspFormsNew N k ⊓ cuspFormCharSpace k χ) := by
  rw [← (cuspFormCharSpace k χ).finrank_map_subtype_eq, Submodule.map_comap_eq,
    Submodule.range_subtype, inf_comm]

/-! ### Forward divisor-count dimension convolutions -/

/-- **Divisor-count dimension formula for `S_k(Γ₁(N))`** (Diamond–Shurman, Theorem 5.8.3):
`dim S_k(Γ₁(N)) = ∑_{M ∣ N} #(N / M).divisors * dim S_k(Γ₁(M))ⁿᵉʷ`. -/
theorem finrank_cuspForm_Gamma1_eq_sum_divisors {N : ℕ} [NeZero N] (k : ℤ) :
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
  rw [Finset.univ_eq_attach]
  exact (Finset.sum_const_nat fun _ _ ↦ (rfl : _ = Module.finrank ℂ (cuspFormsNew M.1 k))).trans
    (by rw [Finset.card_attach])

/-- **Divisor-count dimension formula for `S_k(N, χ)`** (Diamond–Shurman, Theorem 5.8.3):
`dim S_k(N, χ) = ∑_{cond(χ) ∣ M ∣ N} #(N / M).divisors * dim S_k(M, χ_M)ⁿᵉʷ`. -/
theorem finrank_cuspFormCharSpace_eq_sum_divisors {N : ℕ} [NeZero N] (k : ℤ)
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
  let e : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N ∧ c ∣ p.1} ≃
      Σ M : {M : ℕ+ // (M : ℕ) ∣ N}, Subtype fun _ : (N / M.1).divisors ↦ c ∣ M.1 :=
    { toFun p := ⟨⟨p.1.1, dvd_of_mul_left_dvd p.2.1⟩,
        ⟨⟨p.1.2, Nat.mem_divisors.mpr
          ⟨(Nat.dvd_div_iff_mul_dvd (dvd_of_mul_left_dvd p.2.1)).mpr
              (mul_comm (p.1.2 : ℕ) p.1.1 ▸ p.2.1),
            Nat.div_ne_zero_iff.mpr
              ⟨p.1.1.ne_zero, Nat.le_of_dvd (NeZero.pos N) (dvd_of_mul_left_dvd p.2.1)⟩⟩⟩,
          p.2.2⟩⟩
      invFun x := ⟨(x.1.1, ⟨x.2.1.1, Nat.pos_of_mem_divisors x.2.1.2⟩),
        ⟨mul_comm (x.1.1 : ℕ) x.2.1.1 ▸
          (Nat.dvd_div_iff_mul_dvd x.1.2).mp (Nat.dvd_of_mem_divisors x.2.1.2), x.2.2⟩⟩
      left_inv _ := Subtype.ext (Prod.ext rfl (PNat.eq rfl))
      right_inv x := by obtain ⟨_, ⟨⟨_, _⟩, _⟩⟩ := x; rfl }
  let _ : Fintype {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N ∧ c ∣ p.1} :=
    Fintype.ofEquiv _ e.symm
  rw [← iSup_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace N k χ,
    finrank_iSup_eq_sum_finrank_of_iSupIndep
      (iSupIndep_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace N k χ)]
  have hmap (p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N ∧ c ∣ p.1}) :
      Module.finrank ℂ ↥((cuspFormsNew p.1.1 k ⊓ cuspFormCharSpace k
        (DirichletCharacter.changeLevel p.2.2
          (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom).map
        (CuspForm.levelRaiseₗ p.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd p.2.1))) =
        Module.finrank ℂ ↥(cuspFormsNew p.1.1 k ⊓ cuspFormCharSpace k
          (DirichletCharacter.changeLevel p.2.2
            (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom) :=
    (Submodule.equivMapOfInjective _
      (CuspForm.levelRaiseₗ_injective p.1.2
        (Gamma1_map_le_conjAct_scaleGL_of_dvd p.2.1))
      (cuspFormsNew p.1.1 k ⊓ cuspFormCharSpace k
        (DirichletCharacter.changeLevel p.2.2
          (DirichletCharacter.primitiveCharacter
            (MulChar.ofUnitHom χ))).toUnitHom)).finrank_eq.symm
  simp_rw [hmap]
  rw [← e.symm.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun M _ ↦ ?_
  by_cases hcM : c ∣ M.1
  · rw [dite_eq_left hcM]
    let ed : (N / M.1).divisors ≃ Subtype fun _ : (N / M.1).divisors ↦ c ∣ M.1 :=
      { toFun := fun d ↦ ⟨d, hcM⟩
        invFun := Subtype.val
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ Subtype.ext rfl }
    rw [← ed.sum_comp, Finset.univ_eq_attach]
    exact (Finset.sum_const_nat fun _ _ ↦
      (rfl : _ = Module.finrank ℂ ↥(cuspFormsNew M.1 k ⊓ cuspFormCharSpace k
        (DirichletCharacter.changeLevel hcM
          (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom))).trans
      (by rw [Finset.card_attach])
  · rw [dite_eq_right hcM]
    exact Finset.sum_eq_zero fun d _ ↦ (hcM d.2).elim

private lemma conductor_ofUnitHom_one (N : ℕ) [NeZero N] :
    DirichletCharacter.conductor (MulChar.ofUnitHom (1 : (ZMod N)ˣ →* ℂˣ)) = 1 := by
  have h1 : MulChar.ofUnitHom (1 : (ZMod N)ˣ →* ℂˣ) = 1 := MulChar.ext fun _ ↦ by simp
  rw [h1, DirichletCharacter.conductor_one]

/-- **Divisor-count dimension formula for `S_k(Γ₀(N))`**:
`dim S_k(Γ₀(N)) = ∑_{M ∣ N} #(N / M).divisors * dim S_k(M, 1)ⁿᵉʷ`. -/
theorem finrank_cuspForm_Gamma0_eq_sum_divisors {N : ℕ} [NeZero N] (k : ℤ) :
    Module.finrank ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) k) =
      ∑ M : {M : ℕ+ // (M : ℕ) ∣ N},
        #(N / M.1).divisors *
          Module.finrank ℂ ↥(cuspFormsNew M.1 k ⊓
            cuspFormCharSpace k (1 : (ZMod M.1)ˣ →* ℂˣ)) := by
  rw [← (cuspFormCharSpaceOneEquiv N k).finrank_eq,
    finrank_cuspFormCharSpace_eq_sum_divisors k (1 : (ZMod N)ˣ →* ℂˣ)]
  refine Finset.sum_congr rfl fun M _ ↦ ?_
  have hdvd : DirichletCharacter.conductor (MulChar.ofUnitHom (1 : (ZMod N)ˣ →* ℂˣ)) ∣ M.1 :=
    conductor_ofUnitHom_one N ▸ one_dvd _
  rw [dite_eq_left hdvd]
  have h1 : (DirichletCharacter.changeLevel hdvd
      (DirichletCharacter.primitiveCharacter
        (MulChar.ofUnitHom (1 : (ZMod N)ˣ →* ℂˣ)))).toUnitHom =
      (1 : (ZMod M.1)ˣ →* ℂˣ) := by
    refine (MonoidHom.cancel_right (ZMod.unitsMap_surjective M.2)).mp ?_
    rw [← DirichletCharacter.changeLevel_toUnitHom, ← DirichletCharacter.changeLevel_trans,
      DirichletCharacter.changeLevel_primitiveCharacter, MulChar.toUnitHom_eq,
      MulChar.ofUnitHom_eq, Equiv.apply_symm_apply, MonoidHom.one_comp]
  rw [h1]

/-! ### Möbius-inverted newspace dimension formulas -/

/-- **Dimension of the `Γ₁(N)` newspace** (Diamond–Shurman, Theorem 5.8.3):
`dim S_k(Γ₁(N))ⁿᵉʷ = ∑_{M ∣ N} (μ * μ)(N / M) · dim S_k(Γ₁(M))`, in all integral weights `k`. -/
theorem finrank_cuspFormsNew {N : ℕ} [NeZero N] (k : ℤ) :
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
  have hm := congrArg (Nat.cast : ℕ → ℤ) (finrank_cuspForm_Gamma1_eq_sum_divisors (N := m) k)
  rw [Nat.cast_sum] at hm
  rw [hm, ← Finset.sum_coe_sort m.divisors, ← Equiv.sum_comp (pnatDvdEquivDivisors m)]
  refine Finset.sum_congr rfl fun M _ ↦ ?_
  dsimp only [f, coe_pnatDvdEquivDivisors_apply]
  rw [dite_eq_left M.1.ne_zero, Nat.cast_mul]

/-- At an intermediate divisor `m ∣ N` divisible by `cond(χ)`, the dimension of `S_k(m, χ_m)` over
`ℤ` expands as the divisor-count sum over `d ∈ m.divisors` of `dim S_k(d, χ_d)ⁿᵉʷ`. -/
private lemma finrank_cuspFormCharSpace_changeLevel_eq_sum_divisors {N m : ℕ} [NeZero N]
    (hmN : m ∣ N) (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (hcm : DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ m) :
    (Module.finrank ℂ (cuspFormCharSpace k
      (DirichletCharacter.changeLevel hcm
        (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom) : ℤ) =
      ∑ d ∈ m.divisors, (#(m / d).divisors : ℤ) *
        if hd : DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ d ∧ d ≠ 0 then
          have : NeZero d := ⟨hd.2⟩
          (Module.finrank ℂ ↥(cuspFormsNew d k ⊓
            cuspFormCharSpace k (DirichletCharacter.changeLevel hd.1
              (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom) : ℤ)
        else 0 := by
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
    (finrank_cuspFormCharSpace_eq_sum_divisors (N := m) k χm)
  rw [Nat.cast_sum] at hm
  let F : ℕ → ℤ := fun d ↦ (#(m / d).divisors : ℤ) *
    if hd : DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ d ∧ d ≠ 0 then
      have : NeZero d := ⟨hd.2⟩
      (Module.finrank ℂ ↥(cuspFormsNew d k ⊓
        cuspFormCharSpace k (DirichletCharacter.changeLevel hd.1
          (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom) : ℤ)
    else 0
  rw [hm, ← Finset.sum_coe_sort m.divisors (f := F), ← (pnatDvdEquivDivisors m).sum_comp]
  refine Finset.sum_congr rfl fun M _ ↦ ?_
  rw [coe_pnatDvdEquivDivisors_apply]
  dsimp only [F]
  by_cases hcM : c ∣ M.1
  · have hcM' : DirichletCharacter.conductor (MulChar.ofUnitHom χm) ∣ M.1 := hcond_m ▸ hcM
    have hcM0 : DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ M.1 ∧ (M.1 : ℕ) ≠ 0 :=
      ⟨hcM, M.1.ne_zero⟩
    rw [dite_eq_left hcM0, dite_eq_left hcM', Nat.cast_mul]
    have hchar : (DirichletCharacter.changeLevel hcM'
        (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χm))).toUnitHom =
        (DirichletCharacter.changeLevel hcM ψ₀).toUnitHom := by
      refine (MonoidHom.cancel_right (ZMod.unitsMap_surjective M.2)).mp ?_
      rw [← DirichletCharacter.changeLevel_toUnitHom, ← DirichletCharacter.changeLevel_trans,
        DirichletCharacter.changeLevel_primitiveCharacter, MulChar.toUnitHom_eq,
        MulChar.ofUnitHom_eq, Equiv.apply_symm_apply]
      dsimp only [χm]
      rw [← DirichletCharacter.changeLevel_toUnitHom, ← DirichletCharacter.changeLevel_trans]
    rw [hchar]
  · have hcM' : ¬ DirichletCharacter.conductor (MulChar.ofUnitHom χm) ∣ M.1 := hcond_m ▸ hcM
    have hcM0 : ¬ (DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ M.1 ∧ (M.1 : ℕ) ≠ 0) :=
      fun h ↦ hcM h.1
    rw [dite_eq_right hcM0, dite_eq_right hcM', mul_zero, Nat.cast_zero]

/-- **Dimension of the fixed-nebentypus newspace `S_k(N, χ)ⁿᵉʷ`** (Diamond–Shurman,
Theorem 5.8.3): `dim S_k(N, χ)ⁿᵉʷ = ∑_{cond(χ) ∣ M ∣ N} (μ * μ)(N / M) · dim S_k(M, χ_M)` in all
integral weights `k`, where `χ_M` is the raise of the primitive character of `χ` to level `M`. -/
theorem finrank_cuspFormsNew_inf_cuspFormCharSpace {N : ℕ} [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
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
  let f : ℕ → ℤ := fun d ↦
    if hd : c ∣ d ∧ d ≠ 0 then
      have : NeZero d := ⟨hd.2⟩
      (Module.finrank ℂ ↥(cuspFormsNew d k ⊓
        cuspFormCharSpace k (DirichletCharacter.changeLevel hd.1 ψ₀).toUnitHom) : ℤ)
    else 0
  let g : ℕ → ℤ := fun m ↦
    if hm : c ∣ m then
      (Module.finrank ℂ (cuspFormCharSpace k
        (DirichletCharacter.changeLevel hm ψ₀).toUnitHom) : ℤ)
    else 0
  have hχN : (DirichletCharacter.changeLevel
      (DirichletCharacter.conductor_dvd_level (MulChar.ofUnitHom χ)) ψ₀).toUnitHom = χ := by
    rw [DirichletCharacter.changeLevel_primitiveCharacter, MulChar.toUnitHom_eq,
      MulChar.ofUnitHom_eq, Equiv.apply_symm_apply]
  have hcN : c ∣ N ∧ N ≠ 0 :=
    ⟨DirichletCharacter.conductor_dvd_level (MulChar.ofUnitHom χ), NeZero.ne N⟩
  have hfN : f N = (Module.finrank ℂ ↥(cuspFormsNew N k ⊓ cuspFormCharSpace k χ) : ℤ) := by
    dsimp only [f]
    rw [dite_eq_left hcN, hχN]
  have hsum : f N = ∑ M ∈ N.divisors, (μ * μ) (N / M) * g M := by
    refine eq_sum_divisors_moebius_mul_moebius_mul_of_dvd (NeZero.ne N) fun m hmN ↦ ?_
    by_cases hcm : c ∣ m
    · dsimp only [g]
      rw [dite_eq_left hcm]
      exact (finrank_cuspFormCharSpace_changeLevel_eq_sum_divisors hmN k χ hcm).symm
    · dsimp only [g]
      rw [dite_eq_right hcm]
      refine Finset.sum_eq_zero fun d hd ↦ ?_
      have hcd : ¬ (c ∣ d ∧ d ≠ 0) := fun h ↦ hcm (h.1.trans (Nat.dvd_of_mem_divisors hd))
      dsimp only [f]
      rw [dite_eq_right hcd, mul_zero]
  rw [← hfN, hsum]
  refine Finset.sum_congr rfl fun M _ ↦ ?_
  by_cases hcM : c ∣ M
  · dsimp only [g]
    rw [dite_eq_left hcM, dite_eq_left hcM]
  · dsimp only [g]
    rw [dite_eq_right hcM, dite_eq_right hcM, mul_zero]

/-- **Dimension of the trivial-nebentypus (`Γ₀(N)`) newspace** (Diamond–Shurman, Theorem 5.8.3):
`dim S_k(N, 1)ⁿᵉʷ = ∑_{M ∣ N} (μ * μ)(N / M) · dim S_k(Γ₀(M))`, in all integral weights `k`. -/
theorem finrank_cuspFormsNew_inf_cuspFormCharSpace_one {N : ℕ} [NeZero N] (k : ℤ) :
    (Module.finrank ℂ ↥(cuspFormsNew N k ⊓ cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) : ℤ) =
      ∑ M ∈ N.divisors, (μ * μ) (N / M) *
        (Module.finrank ℂ (CuspForm ((Gamma0 M).map (mapGL ℝ)) k) : ℤ) := by
  rw [finrank_cuspFormsNew_inf_cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)]
  refine Finset.sum_congr rfl fun M hM ↦ ?_
  have : NeZero M := ⟨(Nat.pos_of_mem_divisors hM).ne'⟩
  have hdvd : DirichletCharacter.conductor (MulChar.ofUnitHom (1 : (ZMod N)ˣ →* ℂˣ)) ∣ M :=
    conductor_ofUnitHom_one N ▸ one_dvd M
  rw [dite_eq_left hdvd]
  have h1 : (DirichletCharacter.changeLevel hdvd
      (DirichletCharacter.primitiveCharacter
        (MulChar.ofUnitHom (1 : (ZMod N)ˣ →* ℂˣ)))).toUnitHom =
      (1 : (ZMod M)ˣ →* ℂˣ) := by
    refine (MonoidHom.cancel_right
      (ZMod.unitsMap_surjective (Nat.dvd_of_mem_divisors hM))).mp ?_
    rw [← DirichletCharacter.changeLevel_toUnitHom, ← DirichletCharacter.changeLevel_trans,
      DirichletCharacter.changeLevel_primitiveCharacter, MulChar.toUnitHom_eq,
      MulChar.ofUnitHom_eq, Equiv.apply_symm_apply, MonoidHom.one_comp]
  rw [h1, (cuspFormCharSpaceOneEquiv M k).finrank_eq]

end TauCeti
