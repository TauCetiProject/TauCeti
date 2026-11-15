/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.Moebius
public import TauCeti.NumberTheory.ModularForms.Newforms.Decomposition
public import TauCeti.NumberTheory.ModularForms.TrivialNebentypus

import TauCeti.Data.ZMod.Units
import TauCeti.NumberTheory.Divisors
import TauCeti.NumberTheory.MulChar.Basic

/-!
# Newspace dimension formulas via `(μ * μ)`-inversion

Taking `ℂ`-dimensions across the bases of level-raised newforms from
`TauCeti.NumberTheory.ModularForms.Newforms.Decomposition` (`HeckeRing.GL2.Newform.levelRaiseBasis`
and `HeckeRing.GL2.Newform.levelRaiseBasisCharSpace`) yields divisor-count relations for
`S_k(Γ₁(N))`, `S_k(N, χ)`, and `S_k(Γ₀(N))`, and Möbius-square (`μ * μ`) inversion
(`TauCeti.NumberTheory.ArithmeticFunction.Moebius`) expresses the newspace dimensions in terms of
the full cusp-form spaces at divisor levels:

```text
dim S_k(Γ₁(N))ⁿᵉʷ = ∑_{M ∣ N} (μ * μ)(N / M) · dim S_k(Γ₁(M)),
dim S_k(N, χ)ⁿᵉʷ  = ∑_{cond χ ∣ M ∣ N} (μ * μ)(N / M) · dim S_k(M, χ_M),
dim S_k(Γ₀(N))ⁿᵉʷ = ∑_{M ∣ N} (μ * μ)(N / M) · dim S_k(Γ₀(M)).
```

## Main results

* `TauCeti.finrank_cuspForm_Gamma1_eq_sum_divisors`,
  `TauCeti.finrank_cuspFormCharSpace_eq_sum_divisors`,
  `TauCeti.finrank_cuspForm_Gamma0_eq_sum_divisors`: forward dimension identities weighted by
  `#(N / M).divisors`.
* `TauCeti.natCast_finrank_cuspFormsNew_eq_sum_divisors_moebius_mul_moebius`,
  `natCast_finrank_cuspFormsNew_comap_cuspFormCharSpace_eq_sum_divisors_moebius_mul_moebius`,
  `natCast_finrank_cuspFormsNew_comap_cuspFormCharSpace_one_eq_sum_divisors_moebius_mul_moebius`:
  Möbius-square (`μ * μ`) dimension formulas for `S_k(Γ₁(N))ⁿᵉʷ`, `S_k(N, χ)ⁿᵉʷ`, and
  `S_k(Γ₀(N))ⁿᵉʷ`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.3.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.13.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup Finset
open scoped MatrixGroups ArithmeticFunction.Moebius

namespace TauCeti

open _root_.CuspForm HeckeRing.GL2

/-! ### Forward divisor-count dimension identities -/

private lemma natCard_sigma_prod_mul_dvd (N : ℕ) [NeZero N] (α : {M : ℕ // M ∣ N} → Type*)
    [∀ M, Finite (α M)] :
    Nat.card (Σ M : {M : ℕ // M ∣ N}, α M × {d : ℕ // d * M.1 ∣ N}) =
      ∑ M ∈ N.divisors.attach,
        #(N / M.1).divisors * Nat.card (α ⟨M.1, Nat.dvd_of_mem_divisors M.2⟩) := by
  rw [← Nat.card_congr (Equiv.sigmaCongrLeft (Nat.divisorsEquiv N)), Nat.card_sigma,
    Finset.univ_eq_attach]
  refine Finset.sum_congr rfl fun M _ ↦ ?_
  rw [Nat.divisorsEquiv_apply, Nat.card_prod, Nat.card_mul_dvd (Nat.dvd_of_mem_divisors M.2),
    mul_comm]

/-- **Divisor-count dimension formula for `S_k(Γ₁(N))`** (a consequence of Diamond–Shurman,
Theorem 5.8.3): `dim S_k(Γ₁(N)) = ∑_{M ∣ N} #(N / M).divisors · dim S_k(Γ₁(M))ⁿᵉʷ`. -/
theorem finrank_cuspForm_Gamma1_eq_sum_divisors (N : ℕ) [NeZero N] (k : ℤ) :
    Module.finrank ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ∑ M ∈ N.divisors.attach,
        letI : NeZero M.1 := NeZero.of_dvd (Nat.dvd_of_mem_divisors M.2)
        #(N / M.1).divisors * Module.finrank ℂ (cuspFormsNew M.1 k) := by
  have : ∀ M : {M : ℕ // M ∣ N},
      Finite (letI : NeZero M.1 := NeZero.of_dvd M.2; Newform M.1 k) :=
    fun M ↦ letI : NeZero M.1 := NeZero.of_dvd M.2; inferInstance
  rw [Module.finrank_eq_nat_card_basis (Newform.levelRaiseBasis N k), natCard_sigma_prod_mul_dvd]
  refine Finset.sum_congr rfl fun M _ ↦ ?_
  have : NeZero M.1 := NeZero.of_dvd (Nat.dvd_of_mem_divisors M.2)
  rw [Newform.finrank_cuspFormsNew]

private lemma finrank_cuspFormCharSpace_eq_sum_divisors_natCard (M : ℕ) [NeZero M] (k : ℤ)
    (ψ : (ZMod M)ˣ →* ℂˣ) :
    Module.finrank ℂ (cuspFormCharSpace k ψ) =
      ∑ d ∈ M.divisors.attach,
        #(M / d.1).divisors *
          Nat.card (letI : NeZero d.1 := NeZero.of_dvd (Nat.dvd_of_mem_divisors d.2);
            {g : Newform d.1 k //
              g.χ.comp (ZMod.unitsMap (Nat.dvd_of_mem_divisors d.2)) = ψ}) := by
  have : ∀ d : {d : ℕ // d ∣ M},
      Finite (letI : NeZero d.1 := NeZero.of_dvd d.2;
        {g : Newform d.1 k // g.χ.comp (ZMod.unitsMap d.2) = ψ}) :=
    fun d ↦ letI : NeZero d.1 := NeZero.of_dvd d.2; inferInstance
  rw [Module.finrank_eq_nat_card_basis (Newform.levelRaiseBasisCharSpace M k ψ),
    natCard_sigma_prod_mul_dvd]

private lemma natCard_newform_comp_unitsMap_eq {N M d : ℕ} [NeZero N] {k : ℤ}
    {χ : (ZMod N)ˣ →* ℂˣ} (hdM : d ∣ M)
    (hcM : DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ M) (hMN : M ∣ N) :
    (letI : NeZero d := NeZero.of_dvd (hdM.trans hMN);
      Nat.card {g : Newform d k //
        g.χ.comp (ZMod.unitsMap hdM) =
          (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)).toUnitHom.comp
            (ZMod.unitsMap hcM)}) =
      if hcd : DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ d then
        letI : NeZero d := NeZero.of_dvd (hdM.trans hMN)
        Module.finrank ℂ ((cuspFormsNew d k).comap (cuspFormCharSpace k
          ((DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)).toUnitHom.comp
            (ZMod.unitsMap hcd))).subtype)
      else 0 := by
  have : NeZero M := NeZero.of_dvd hMN
  have : NeZero d := NeZero.of_dvd (hdM.trans hMN)
  split_ifs with hcd
  · rw [Newform.finrank_cuspFormsNew_comap_cuspFormCharSpace]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ ZMod.comp_unitsMap_eq_iff hcd hdM hcM)
  · have : IsEmpty {g : Newform d k //
        g.χ.comp (ZMod.unitsMap hdM) =
          (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)).toUnitHom.comp
            (ZMod.unitsMap hcM)} :=
      ⟨fun ⟨g, hg⟩ ↦ hcd <| by
        have hgN : g.χ.comp (ZMod.unitsMap (hdM.trans hMN)) = χ := by
          calc g.χ.comp (ZMod.unitsMap (hdM.trans hMN))
              = (g.χ.comp (ZMod.unitsMap hdM)).comp (ZMod.unitsMap hMN) := by
                rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
            _ = ((DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)).toUnitHom.comp
                  (ZMod.unitsMap hcM)).comp (ZMod.unitsMap hMN) := by rw [hg]
            _ = χ := by
                rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp,
                  DirichletCharacter.primitiveCharacter_toUnitHom_comp_unitsMap]
        exact DirichletCharacter.conductor_ofUnitHom_dvd_of_comp_unitsMap_eq (hdM.trans hMN) hgN⟩
    exact Nat.card_of_isEmpty

/-- **Divisor-count dimension formula for `S_k(N, χ)`** (a consequence of Diamond–Shurman,
Theorem 5.8.3): `dim S_k(N, χ) = ∑_{cond χ ∣ M ∣ N} #(N / M).divisors · dim S_k(M, χ_M)ⁿᵉʷ`, where
`χ_M` is the descent of `χ` to level `M`. -/
theorem finrank_cuspFormCharSpace_eq_sum_divisors (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.finrank ℂ (cuspFormCharSpace k χ) =
      ∑ M ∈ N.divisors.attach,
        if hc : DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ M.1 then
          letI : NeZero M.1 := NeZero.of_dvd (Nat.dvd_of_mem_divisors M.2)
          #(N / M.1).divisors *
            Module.finrank ℂ ((cuspFormsNew M.1 k).comap (cuspFormCharSpace k
              ((DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)).toUnitHom.comp
                (ZMod.unitsMap hc))).subtype)
        else 0 := by
  rw [finrank_cuspFormCharSpace_eq_sum_divisors_natCard N k χ]
  refine Finset.sum_congr rfl fun M _ ↦ ?_
  have hMN : M.1 ∣ N := Nat.dvd_of_mem_divisors M.2
  have hcard := natCard_newform_comp_unitsMap_eq (k := k) (χ := χ) hMN
    (DirichletCharacter.conductor_dvd_level (MulChar.ofUnitHom χ)) dvd_rfl
  rw [DirichletCharacter.primitiveCharacter_toUnitHom_comp_unitsMap] at hcard
  rw [hcard]
  split_ifs <;> simp

/-- **Divisor-count dimension formula for `S_k(Γ₀(N))`** (a consequence of Diamond–Shurman,
Theorem 5.8.3). -/
theorem finrank_cuspForm_Gamma0_eq_sum_divisors (N : ℕ) [NeZero N] (k : ℤ) :
    Module.finrank ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) k) =
      ∑ M ∈ N.divisors.attach,
        letI : NeZero M.1 := NeZero.of_dvd (Nat.dvd_of_mem_divisors M.2)
        #(N / M.1).divisors *
          Module.finrank ℂ ((cuspFormsNew M.1 k).comap
            (cuspFormCharSpace k (1 : (ZMod M.1)ˣ →* ℂˣ)).subtype) := by
  rw [← (cuspFormCharSpaceOneEquiv N k).finrank_eq, finrank_cuspFormCharSpace_eq_sum_divisors]
  refine Finset.sum_congr rfl fun M _ ↦ ?_
  have hc : DirichletCharacter.conductor (MulChar.ofUnitHom (1 : (ZMod N)ˣ →* ℂˣ)) ∣ M.1 := by
    rw [MulChar.ofUnitHom_one, DirichletCharacter.conductor_one]
    exact one_dvd M.1
  rw [dite_eq_left_of_eq_true (eq_true hc),
    DirichletCharacter.primitiveCharacter_ofUnitHom_one_comp_unitsMap hc]

/-! ### Möbius-square (`μ * μ`) newspace dimension formulas -/

/-- **Möbius-square dimension formula for `S_k(Γ₁(N))ⁿᵉʷ`** (a consequence of Diamond–Shurman,
Theorem 5.8.3, via `(μ * μ)`-inversion
`ArithmeticFunction.eq_sum_divisors_moebius_mul_moebius_mul`):
`dim S_k(Γ₁(N))ⁿᵉʷ = ∑_{M ∣ N} (μ * μ)(N / M) · dim S_k(Γ₁(M))`. -/
theorem natCast_finrank_cuspFormsNew_eq_sum_divisors_moebius_mul_moebius (N : ℕ) [NeZero N]
    (k : ℤ) :
    (Module.finrank ℂ (cuspFormsNew N k) : ℤ) =
      ∑ M ∈ N.divisors, (μ * μ) (N / M) *
        (Module.finrank ℂ (CuspForm ((Gamma1 M).map (mapGL ℝ)) k) : ℤ) := by
  let f : ℕ → ℤ := fun m ↦
    if hm : m ≠ 0 then
      letI : NeZero m := ⟨hm⟩
      (Module.finrank ℂ (cuspFormsNew m k) : ℤ)
    else 0
  let g : ℕ → ℤ := fun m ↦ (Module.finrank ℂ (CuspForm ((Gamma1 m).map (mapGL ℝ)) k) : ℤ)
  have hfN : f N = (Module.finrank ℂ (cuspFormsNew N k) : ℤ) := by
    dsimp only [f]
    exact dite_eq_left_of_eq_true (eq_true (NeZero.ne N))
  rw [← hfN]
  refine ArithmeticFunction.eq_sum_divisors_moebius_mul_moebius_mul (f := f) (g := g)
    (NeZero.pos N) fun M hMN ↦ ?_
  have : NeZero M := NeZero.of_dvd hMN
  simp only [g, finrank_cuspForm_Gamma1_eq_sum_divisors M k, Nat.cast_sum, Nat.cast_mul,
    ← Finset.sum_attach M.divisors]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  have hd0 : d.1 ≠ 0 := (Nat.pos_of_mem_divisors d.2).ne'
  dsimp only [f]
  rw [dite_eq_left_of_eq_true (eq_true hd0)]

private lemma natCast_finrank_cuspFormCharSpace_eq_sum_divisors_filter {N M : ℕ} [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) (hcM : DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ M)
    (hMN : M ∣ N) :
    (Module.finrank ℂ (cuspFormCharSpace k
      ((DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)).toUnitHom.comp
        (ZMod.unitsMap hcM))) : ℤ) =
      ∑ d ∈ M.divisors with DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ d,
        (#(M / d).divisors : ℤ) *
          if hm : d ≠ 0 ∧ DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ d then
            letI : NeZero d := ⟨hm.1⟩
            (Module.finrank ℂ ((cuspFormsNew d k).comap
              (cuspFormCharSpace k
                ((DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)).toUnitHom.comp
                  (ZMod.unitsMap hm.2))).subtype) : ℤ)
          else 0 := by
  have : NeZero M := NeZero.of_dvd hMN
  rw [finrank_cuspFormCharSpace_eq_sum_divisors_natCard M k _,
    Nat.cast_sum, Finset.sum_filter, ← Finset.sum_attach M.divisors]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  have hdM : d.1 ∣ M := Nat.dvd_of_mem_divisors d.2
  have hd0 : d.1 ≠ 0 := (Nat.pos_of_mem_divisors d.2).ne'
  rw [Nat.cast_mul, natCard_newform_comp_unitsMap_eq (k := k) (χ := χ) hdM hcM hMN]
  by_cases hcd : DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ d.1
  · rw [dite_eq_left_of_eq_true (eq_true hcd), ite_eq_left hcd,
      dite_eq_left_of_eq_true (eq_true ⟨hd0, hcd⟩)]
  · rw [dite_eq_right_of_eq_false (eq_false hcd), ite_eq_right hcd, Nat.cast_zero, mul_zero]

/-- **Möbius-square dimension formula for `S_k(N, χ)ⁿᵉʷ`** (a consequence of Diamond–Shurman,
Theorem 5.8.3, via `(μ * μ)`-inversion
`ArithmeticFunction.eq_sum_divisors_filter_dvd_moebius_mul_moebius_mul`):
`dim S_k(N, χ)ⁿᵉʷ = ∑_{cond χ ∣ M ∣ N} (μ * μ)(N / M) · dim S_k(M, χ_M)`. -/
theorem natCast_finrank_cuspFormsNew_comap_cuspFormCharSpace_eq_sum_divisors_moebius_mul_moebius
    (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    (Module.finrank ℂ ((cuspFormsNew N k).comap (cuspFormCharSpace k χ).subtype) : ℤ) =
      ∑ M ∈ N.divisors,
        if hc : DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ M then
          (μ * μ) (N / M) *
            (Module.finrank ℂ (cuspFormCharSpace k
              ((DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)).toUnitHom.comp
                (ZMod.unitsMap hc))) : ℤ)
        else 0 := by
  set c := DirichletCharacter.conductor (MulChar.ofUnitHom χ)
  let χ₀ := (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)).toUnitHom
  let f : ℕ → ℤ := fun m ↦
    if hm : m ≠ 0 ∧ c ∣ m then
      letI : NeZero m := ⟨hm.1⟩
      (Module.finrank ℂ ((cuspFormsNew m k).comap
        (cuspFormCharSpace k (χ₀.comp (ZMod.unitsMap hm.2))).subtype) : ℤ)
    else 0
  let g : ℕ → ℤ := fun m ↦
    if hc : c ∣ m then
      (Module.finrank ℂ (cuspFormCharSpace k (χ₀.comp (ZMod.unitsMap hc))) : ℤ)
    else 0
  have hcN : c ∣ N := DirichletCharacter.conductor_dvd_level (MulChar.ofUnitHom χ)
  have hfN : f N =
      (Module.finrank ℂ ((cuspFormsNew N k).comap (cuspFormCharSpace k χ).subtype) : ℤ) := by
    dsimp only [f, χ₀]
    rw [dite_eq_left_of_eq_true (eq_true ⟨NeZero.ne N, hcN⟩),
      DirichletCharacter.primitiveCharacter_toUnitHom_comp_unitsMap]
  have hinv := ArithmeticFunction.eq_sum_divisors_filter_dvd_moebius_mul_moebius_mul (f := f)
    (g := g) hcN (NeZero.pos N) fun M hcM hMN ↦ by
      dsimp only [g, f, χ₀]
      rw [dite_eq_left_of_eq_true (eq_true hcM)]
      exact natCast_finrank_cuspFormCharSpace_eq_sum_divisors_filter k χ hcM hMN
  rw [← hfN, hinv, Finset.sum_filter]
  refine Finset.sum_congr rfl fun M _ ↦ ?_
  dsimp only [g, χ₀]
  split_ifs <;> rfl

/-- **Möbius-square dimension formula for `S_k(Γ₀(N))ⁿᵉʷ`** (a consequence of Diamond–Shurman,
Theorem 5.8.3, via `(μ * μ)`-inversion):
`dim S_k(Γ₀(N))ⁿᵉʷ = ∑_{M ∣ N} (μ * μ)(N / M) · dim S_k(Γ₀(M))`. -/
theorem natCast_finrank_cuspFormsNew_comap_cuspFormCharSpace_one_eq_sum_divisors_moebius_mul_moebius
    (N : ℕ) [NeZero N] (k : ℤ) :
    (Module.finrank ℂ
      ((cuspFormsNew N k).comap (cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)).subtype) : ℤ) =
      ∑ M ∈ N.divisors, (μ * μ) (N / M) *
        (Module.finrank ℂ (CuspForm ((Gamma0 M).map (mapGL ℝ)) k) : ℤ) := by
  rw [natCast_finrank_cuspFormsNew_comap_cuspFormCharSpace_eq_sum_divisors_moebius_mul_moebius]
  refine Finset.sum_congr rfl fun M hM ↦ ?_
  have : NeZero M := ⟨(Nat.pos_of_mem_divisors hM).ne'⟩
  have hc : DirichletCharacter.conductor (MulChar.ofUnitHom (1 : (ZMod N)ˣ →* ℂˣ)) ∣ M := by
    rw [MulChar.ofUnitHom_one, DirichletCharacter.conductor_one]
    exact one_dvd M
  rw [dite_eq_left_of_eq_true (eq_true hc),
    DirichletCharacter.primitiveCharacter_ofUnitHom_one_comp_unitsMap hc,
    (cuspFormCharSpaceOneEquiv M k).finrank_eq]

end TauCeti

end
