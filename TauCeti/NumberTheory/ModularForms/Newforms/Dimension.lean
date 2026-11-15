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
import TauCeti.LinearAlgebra.LinearIndependent.Basic
import TauCeti.LinearAlgebra.Submodule.Independent
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.Divisors
import TauCeti.NumberTheory.MulChar.Basic

/-!
# Linear independence of level-raised newforms and newspace dimension formulas

The spanning half of Diamond–Shurman's Theorem 5.8.3
(`HeckeRing.GL2.Newform.span_levelRaise_eq_top`) expresses every cusp form in `S_k(Γ₁(N))` as a
linear combination of level-raised newforms `V_d g`, `(V_d g)(τ) = g(dτ)`, over divisor levels
`M ∣ N`, newforms `g` of level `M`, and degeneracy divisors `d` with `d * M ∣ N`. This file
supplies the complementary linear independence, promotes the spanning family to bases of
`S_k(Γ₁(N))` and `S_k(N, χ)` and internal direct-sum decompositions

```text
S_k(Γ₁(N)) = ⨁_{M ∣ N} ⨁_{d ∣ N / M} V_d S_k(Γ₁(M))ⁿᵉʷ,
S_k(N, χ)  = ⨁_{cond χ ∣ M ∣ N} ⨁_{d ∣ N / M} V_d S_k(M, χ_M)ⁿᵉʷ,
```

and takes `ℂ`-dimensions to obtain divisor-count relations and their `(μ * μ)`-inversions:

```text
dim S_k(Γ₁(N))ⁿᵉʷ = ∑_{M ∣ N} (μ * μ)(N / M) · dim S_k(Γ₁(M)),
dim S_k(N, χ)ⁿᵉʷ  = ∑_{cond χ ∣ M ∣ N} (μ * μ)(N / M) · dim S_k(M, χ_M),
dim S_k(Γ₀(N))ⁿᵉʷ = ∑_{M ∣ N} (μ * μ)(N / M) · dim S_k(Γ₀(M)).
```

Linear independence is assembled in three steps:
1. For a fixed pair `(M, g)`, the degeneracy images `V_d g` (`d * M ∣ N`) have `q`-expansions
   `(qExpansion 1 g).expand d`, which are linearly independent by
   `CuspForm.linearIndependent_levelRaise`.
2. Within a fixed nebentypus space `S_k(N, χ)`, distinct pairs `(M, g)` whose nebentypes pull back
   to `χ` lie in distinct joint eigenspaces of the good Hecke operators `Tₚ` (`p ∤ N`) by
   cross-level strong multiplicity one
   (`HeckeRing.GL2.Newform.eigenvalue_injective_of_comp_unitsMap_eq`).
3. Across nebentypes `χ`, the character subspaces `S_k(N, χ)` are independent
   (`TauCeti.iSupIndep_cuspFormCharSpace`).

## Main definitions

* `HeckeRing.GL2.Newform.levelRaiseBasis`: the level-raised newforms `V_d g` (`M ∣ N`,
  `d * M ∣ N`), as a `ℂ`-basis of `S_k(Γ₁(N))`.
* `HeckeRing.GL2.Newform.levelRaiseBasisCharSpace`: the level-raised newforms whose nebentypus
  pulls back to `χ`, as a `ℂ`-basis of `S_k(N, χ)`.

## Main results

* `HeckeRing.GL2.Newform.finrank_cuspFormsNew`: `dim S_k(Γ₁(N))ⁿᵉʷ` equals the number of newforms
  of level `N` and weight `k`.
* `HeckeRing.GL2.Newform.eigenvalue_injective_of_comp_unitsMap_eq`: distinct pairs `(M, g)` at a
  fixed lifted nebentypus `χ` have distinct good-prime eigenvalue systems.
* `HeckeRing.GL2.Newform.linearIndependent_levelRaise_of_comp_unitsMap_eq`,
  `HeckeRing.GL2.Newform.linearIndependent_levelRaise`: linear independence of the level-raised
  newforms at a fixed nebentypus and across all nebentypes.
* `TauCeti.iSup_map_levelRaiseₗ_cuspFormsNew_eq_top`,
  `TauCeti.iSupIndep_map_levelRaiseₗ_cuspFormsNew`,
  `TauCeti.isInternal_map_levelRaiseₗ_cuspFormsNew`: internal direct-sum decomposition of
  `S_k(Γ₁(N))` into `V_d S_k(Γ₁(M))ⁿᵉʷ` over all pairs `(M, d)` with `d * M ∣ N`.
* `TauCeti.iSup_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace_eq_cuspFormCharSpace`,
  `TauCeti.iSupIndep_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace`,
  `TauCeti.isInternal_comap_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace`: the
  fixed-character refinement on `S_k(N, χ)` over pairs `(M, d)` with `d * M ∣ N` and `cond χ ∣ M`.
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
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.13 and Corollary 4.6.20.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup Finset
open scoped MatrixGroups ArithmeticFunction.Moebius

namespace HeckeRing.GL2.Newform

open TauCeti _root_.CuspForm

/-! ### Dimension of `S_k(Γ₁(N))ⁿᵉʷ` and linear independence of level-raised newforms -/

/-- **The dimension of `S_k(Γ₁(N))ⁿᵉʷ` is the number of newforms of level `N` and weight `k`.** -/
theorem finrank_cuspFormsNew (N : ℕ) [NeZero N] (k : ℤ) :
    Module.finrank ℂ (cuspFormsNew N k) = Nat.card (Newform N k) :=
  Module.finrank_eq_nat_card_basis (basis N k)

/-- **Cross-level injectivity of good-prime Hecke eigenvalues at a fixed nebentypus.** Distinct
pairs `(M, g)` of a divisor level `M ∣ N` and a newform `g` of level `M` whose nebentypus pulls back
to `χ` have distinct eigenvalue systems at the primes `p ∤ N`. -/
theorem eigenvalue_injective_of_comp_unitsMap_eq (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    Function.Injective
      (fun (mg : Σ M : {M : ℕ // M ∣ N},
          letI : NeZero M.1 := NeZero.of_dvd M.2
          {g : Newform M.1 k // g.χ.comp (ZMod.unitsMap M.2) = χ})
        (p : {p : ℕ // p.Prime ∧ Nat.Coprime p N}) ↦
        letI : NeZero mg.1.1 := NeZero.of_dvd mg.1.2
        mg.2.1.eigenvalue ⟨p.1, p.2.1.pos⟩ (p.2.2.coprime_dvd_right mg.1.2)) := by
  rintro ⟨⟨M₁, hM₁⟩, g₁, hg₁⟩ ⟨⟨M₂, hM₂⟩, g₂, hg₂⟩ h
  have : NeZero M₁ := NeZero.of_dvd hM₁
  have : NeZero M₂ := NeZero.of_dvd hM₂
  obtain ⟨rfl, hcoe⟩ := level_eq_and_coe_eq_of_comp_unitsMap_eq g₁ g₂ hM₁ hM₂ hg₁ hg₂ (S := ∅)
    fun p hp hpN _ ↦ congr_fun h ⟨p, hp, hpN⟩
  have hg : g₁ = g₂ := Newform.ext (DFunLike.coe_injective hcoe)
  subst hg
  rfl

/-- **Linear independence of the level-raised newforms at a fixed nebentypus** (Diamond–Shurman,
Theorem 5.8.3). For a character `χ` modulo `N`, the level-raises `V_d g` over divisor levels
`M ∣ N`, newforms `g` of level `M` whose nebentypus pulls back to `χ`, and `d` with `d * M ∣ N` are
`ℂ`-linearly independent in `S_k(Γ₁(N))`. -/
theorem linearIndependent_levelRaise_of_comp_unitsMap_eq (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    LinearIndependent ℂ
      (fun i : Σ M : {M : ℕ // M ∣ N},
          (letI : NeZero M.1 := NeZero.of_dvd M.2;
            {g : Newform M.1 k // g.χ.comp (ZMod.unitsMap M.2) = χ}) ×
            {d : ℕ // d * M.1 ∣ N} ↦
        letI : NeZero i.1.1 := NeZero.of_dvd i.1.2
        letI : NeZero i.2.2.1 := NeZero.of_dvd (dvd_of_mul_right_dvd i.2.2.2)
        CuspForm.levelRaise i.2.2.1 (Gamma1_map_le_conjAct_scaleGL_of_dvd i.2.2.2)
          i.2.1.1.toCuspForm) := by
  let P := {p : ℕ // p.Prime ∧ Nat.Coprime p N}
  let T : P → Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := fun p ↦
    heckeTCuspNat k p.1 (_hn := ⟨p.2.1.ne_zero⟩)
  let η := Σ M : {M : ℕ // M ∣ N},
    letI : NeZero M.1 := NeZero.of_dvd M.2
    {g : Newform M.1 k // g.χ.comp (ZMod.unitsMap M.2) = χ}
  let fam : ∀ mg : η, {d : ℕ // d * mg.1.1 ∣ N} → CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
    fun mg d ↦
      letI : NeZero mg.1.1 := NeZero.of_dvd mg.1.2
      letI : NeZero d.1 := NeZero.of_dvd (dvd_of_mul_right_dvd d.2)
      CuspForm.levelRaise d.1 (Gamma1_map_le_conjAct_scaleGL_of_dvd d.2) mg.2.1.toCuspForm
  -- Step 1 (`_root_.CuspForm.linearIndependent_levelRaise`) gives independence of `V_d g` for each
  -- `(M, g)`; Step 2 (`eigenvalue_injective_of_comp_unitsMap_eq`) separates distinct `(M, g)` into
  -- independent joint `Tₚ`-eigenspaces (`p ∤ N`).
  have hli_sigma := TauCeti.linearIndependent_sigma_of_iSupIndep (f := fam)
    (fun mg ↦ by
      have : NeZero mg.1.1 := NeZero.of_dvd mg.1.2
      have : ∀ d : {d : ℕ // d * mg.1.1 ∣ N}, NeZero d.1 :=
        fun d ↦ NeZero.of_dvd (dvd_of_mul_right_dvd d.2)
      exact _root_.CuspForm.linearIndependent_levelRaise (one_mem_strictPeriods_Gamma1_map mg.1.1)
        mg.2.1.ne_zero Subtype.val_injective
        fun d ↦ Gamma1_map_le_conjAct_scaleGL_of_dvd d.2)
    ((iSupIndep_iInf_eigenspace T).comp (eigenvalue_injective_of_comp_unitsMap_eq N k χ))
    fun mg d ↦ by
      have : NeZero mg.1.1 := NeZero.of_dvd mg.1.2
      have : NeZero d.1 := NeZero.of_dvd (dvd_of_mul_right_dvd d.2)
      exact (Submodule.mem_iInf _).mpr fun p ↦ Module.End.mem_eigenspace_iff.mpr
        (mg.2.1.heckeTCuspNat_levelRaise_eq_eigenvalue_smul d.2 p.2.1 p.2.2)
  -- Reassociate `(M, (g, d))` with `((M, g), d)` to match the sigma-indexed family `fam`.
  let reindex :
      (Σ M : {M : ℕ // M ∣ N},
        (letI : NeZero M.1 := NeZero.of_dvd M.2;
          {g : Newform M.1 k // g.χ.comp (ZMod.unitsMap M.2) = χ}) ×
          {d : ℕ // d * M.1 ∣ N}) ≃
      Σ mg : η, {d : ℕ // d * mg.1.1 ∣ N} :=
    { toFun := fun i ↦ ⟨⟨i.1, i.2.1⟩, i.2.2⟩
      invFun := fun j ↦ ⟨j.1.1, j.1.2, j.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact hli_sigma.comp reindex reindex.injective

/-- **Linear independence of all level-raised newforms in `S_k(Γ₁(N))`** (Diamond–Shurman,
Theorem 5.8.3). As `M` ranges over the divisors of `N`, `g` over the newforms of level `M`, and `d`
over the positive divisors with `d * M ∣ N`, the cusp forms `V_d g` are `ℂ`-linearly independent. -/
theorem linearIndependent_levelRaise (N : ℕ) [NeZero N] (k : ℤ) :
    LinearIndependent ℂ
      (fun i : Σ M : {M : ℕ // M ∣ N},
          (letI : NeZero M.1 := NeZero.of_dvd M.2; Newform M.1 k) × {d : ℕ // d * M.1 ∣ N} ↦
        letI : NeZero i.1.1 := NeZero.of_dvd i.1.2
        letI : NeZero i.2.2.1 := NeZero.of_dvd (dvd_of_mul_right_dvd i.2.2.2)
        CuspForm.levelRaise i.2.2.1 (Gamma1_map_le_conjAct_scaleGL_of_dvd i.2.2.2)
          i.2.1.toCuspForm) := by
  -- Step 3: glue the fixed-character families across the independent subspaces `S_k(N, χ)`, then
  -- group each `(M, g, d)` under its lifted nebentypus `χ = g.χ ∘ unitsMap`.
  have hli_sigma := TauCeti.linearIndependent_sigma_of_iSupIndep
    (W := cuspFormCharSpace (N := N) k)
    (fun χ ↦ linearIndependent_levelRaise_of_comp_unitsMap_eq N k χ)
    (iSupIndep_cuspFormCharSpace k)
    fun χ i ↦ by
      have : NeZero i.1.1 := NeZero.of_dvd i.1.2
      have : NeZero i.2.2.1 := NeZero.of_dvd (dvd_of_mul_right_dvd i.2.2.2)
      have hmem := CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd i.2.2.2 i.2.1.1.χ
        i.2.1.1.mem_charSpace
      rwa [i.2.1.2] at hmem
  let reindex :
      (Σ M : {M : ℕ // M ∣ N},
        (letI : NeZero M.1 := NeZero.of_dvd M.2; Newform M.1 k) × {d : ℕ // d * M.1 ∣ N}) ≃
      Σ χ : (ZMod N)ˣ →* ℂˣ, Σ M : {M : ℕ // M ∣ N},
        (letI : NeZero M.1 := NeZero.of_dvd M.2;
          {g : Newform M.1 k // g.χ.comp (ZMod.unitsMap M.2) = χ}) ×
          {d : ℕ // d * M.1 ∣ N} :=
    { toFun := fun i ↦
        letI : NeZero i.1.1 := NeZero.of_dvd i.1.2
        ⟨i.2.1.χ.comp (ZMod.unitsMap i.1.2), i.1, ⟨i.2.1, rfl⟩, i.2.2⟩
      invFun := fun j ↦ ⟨j.2.1, j.2.2.1.1, j.2.2.2⟩
      left_inv := fun ⟨_, _, _⟩ ↦ rfl
      right_inv := fun ⟨_, _, ⟨_, rfl⟩, _⟩ ↦ rfl }
  exact hli_sigma.comp reindex reindex.injective

/-! ### Bases of `S_k(Γ₁(N))` and `S_k(N, χ)` from level-raised newforms -/

/-- **The level-raised newforms `V_d g` (`M ∣ N`, `d * M ∣ N`), as a `ℂ`-basis of `S_k(Γ₁(N))`**
(Diamond–Shurman, Theorem 5.8.3). -/
noncomputable def levelRaiseBasis (N : ℕ) [NeZero N] (k : ℤ) :
    Module.Basis
      (Σ M : {M : ℕ // M ∣ N},
        (letI : NeZero M.1 := NeZero.of_dvd M.2; Newform M.1 k) × {d : ℕ // d * M.1 ∣ N})
      ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  Module.Basis.mk (linearIndependent_levelRaise N k) <| by
    refine (span_levelRaise_eq_top N k).ge.trans (Submodule.span_mono ?_)
    rintro _ ⟨M, d, _, _, h, g, rfl⟩
    exact ⟨⟨⟨M, dvd_of_mul_left_dvd h⟩, g, ⟨d, h⟩⟩, rfl⟩

/-- Evaluating `levelRaiseBasis` at `(M, g, d)` gives `V_d g`. -/
@[simp]
theorem levelRaiseBasis_apply (N : ℕ) [NeZero N] (k : ℤ)
    (i : Σ M : {M : ℕ // M ∣ N},
      (letI : NeZero M.1 := NeZero.of_dvd M.2; Newform M.1 k) × {d : ℕ // d * M.1 ∣ N}) :
    levelRaiseBasis N k i =
      (letI : NeZero i.1.1 := NeZero.of_dvd i.1.2;
        letI : NeZero i.2.2.1 := NeZero.of_dvd (dvd_of_mul_right_dvd i.2.2.2);
        CuspForm.levelRaise i.2.2.1 (Gamma1_map_le_conjAct_scaleGL_of_dvd i.2.2.2)
          i.2.1.toCuspForm) := by
  simp [levelRaiseBasis]

private noncomputable def levelRaiseToCharSpace (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (i : Σ M : {M : ℕ // M ∣ N},
      (letI : NeZero M.1 := NeZero.of_dvd M.2;
        {g : Newform M.1 k // g.χ.comp (ZMod.unitsMap M.2) = χ}) ×
        {d : ℕ // d * M.1 ∣ N}) :
    cuspFormCharSpace k χ :=
  letI : NeZero i.1.1 := NeZero.of_dvd i.1.2
  letI : NeZero i.2.2.1 := NeZero.of_dvd (dvd_of_mul_right_dvd i.2.2.2)
  ⟨CuspForm.levelRaise i.2.2.1 (Gamma1_map_le_conjAct_scaleGL_of_dvd i.2.2.2) i.2.1.1.toCuspForm,
    by
      have hmem := CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd i.2.2.2 i.2.1.1.χ
        i.2.1.1.mem_charSpace
      rwa [i.2.1.2] at hmem⟩

private theorem linearIndependent_levelRaiseToCharSpace (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    LinearIndependent ℂ (levelRaiseToCharSpace N k χ) :=
  LinearIndependent.of_comp (cuspFormCharSpace k χ).subtype
    (linearIndependent_levelRaise_of_comp_unitsMap_eq N k χ)

private theorem top_le_span_range_levelRaiseToCharSpace (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    ⊤ ≤ Submodule.span ℂ (Set.range (levelRaiseToCharSpace N k χ)) := by
  rintro F -
  rw [← Submodule.comap_map_eq_of_injective (cuspFormCharSpace k χ).injective_subtype
    (Submodule.span ℂ _), Submodule.mem_comap]
  set S := (Submodule.span ℂ (Set.range (levelRaiseToCharSpace N k χ))).map
    (cuspFormCharSpace k χ).subtype
  set W := ⨆ (ψ : (ZMod N)ˣ →* ℂˣ) (_ : ψ ≠ χ), cuspFormCharSpace (N := N) k ψ
  have hSW : (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ S ⊔ W := by
    refine Submodule.span_le.mpr ?_
      ((span_levelRaise_eq_top N k).ge (Submodule.mem_top (x := F.1)))
    rintro _ ⟨M, d, _, _, hdM, g, rfl⟩
    have hMN : M ∣ N := dvd_of_mul_left_dvd hdM
    by_cases hgχ : g.χ.comp (ZMod.unitsMap hMN) = χ
    · exact Submodule.mem_sup_left (Submodule.mem_map.mpr
        ⟨levelRaiseToCharSpace N k χ ⟨⟨M, hMN⟩, ⟨g, hgχ⟩, ⟨d, hdM⟩⟩,
          Submodule.subset_span (Set.mem_range_self _), rfl⟩)
    · exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hgχ
        (CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd hdM g.χ g.mem_charSpace)))
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp hSW
  have hsχ : s ∈ cuspFormCharSpace k χ :=
    Submodule.map_subtype_le (cuspFormCharSpace k χ) _ hs
  have htχ : t ∈ cuspFormCharSpace k χ := by
    have hsub := Submodule.sub_mem _ F.2 hsχ
    rwa [← hst, add_sub_cancel_left] at hsub
  have ht0 : t = 0 :=
    (Submodule.disjoint_def.mp (iSupIndep_def.mp (iSupIndep_cuspFormCharSpace k) χ)) t htχ ht
  rw [ht0, add_zero] at hst
  rw [Submodule.coe_subtype, ← hst]
  exact hs

/-- **The level-raised newforms whose nebentypus pulls back to `χ`, as a `ℂ`-basis of
`S_k(N, χ)`** (Diamond–Shurman, Theorem 5.8.3). -/
noncomputable def levelRaiseBasisCharSpace (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.Basis
      (Σ M : {M : ℕ // M ∣ N},
        (letI : NeZero M.1 := NeZero.of_dvd M.2;
          {g : Newform M.1 k // g.χ.comp (ZMod.unitsMap M.2) = χ}) ×
          {d : ℕ // d * M.1 ∣ N})
      ℂ (cuspFormCharSpace k χ) :=
  Module.Basis.mk
    (linearIndependent_levelRaiseToCharSpace N k χ)
    (top_le_span_range_levelRaiseToCharSpace N k χ)

/-- Evaluating `levelRaiseBasisCharSpace` at `(M, g, d)` gives `V_d g` inside `S_k(N, χ)`. -/
@[simp]
theorem coe_levelRaiseBasisCharSpace_apply (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (i : Σ M : {M : ℕ // M ∣ N},
      (letI : NeZero M.1 := NeZero.of_dvd M.2;
        {g : Newform M.1 k // g.χ.comp (ZMod.unitsMap M.2) = χ}) ×
        {d : ℕ // d * M.1 ∣ N}) :
    (levelRaiseBasisCharSpace N k χ i : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (letI : NeZero i.1.1 := NeZero.of_dvd i.1.2;
        letI : NeZero i.2.2.1 := NeZero.of_dvd (dvd_of_mul_right_dvd i.2.2.2);
        CuspForm.levelRaise i.2.2.1 (Gamma1_map_le_conjAct_scaleGL_of_dvd i.2.2.2)
          i.2.1.1.toCuspForm) := by
  simp [levelRaiseBasisCharSpace, levelRaiseToCharSpace]

end HeckeRing.GL2.Newform

namespace TauCeti

open _root_.CuspForm HeckeRing.GL2

/-! ### Internal direct-sum decompositions of `S_k(Γ₁(N))` and `S_k(N, χ)` -/

/-- **The level-raised newspaces `V_d S_k(Γ₁(M))ⁿᵉʷ` (`d * M ∣ N`) span `S_k(Γ₁(N))`**
(Diamond–Shurman, Theorem 5.8.3). -/
theorem iSup_map_levelRaiseₗ_cuspFormsNew_eq_top (N : ℕ) [NeZero N] (k : ℤ) :
    (⨆ md : {md : ℕ × ℕ // md.2 * md.1 ∣ N},
      letI : NeZero md.1.1 := NeZero.of_dvd (dvd_of_mul_left_dvd md.2)
      letI : NeZero md.1.2 := NeZero.of_dvd (dvd_of_mul_right_dvd md.2)
      (cuspFormsNew md.1.1 k).map
        (CuspForm.levelRaiseₗ md.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd md.2))) = ⊤ := by
  refine eq_top_iff.mpr ((Newform.span_levelRaise_eq_top N k).ge.trans (Submodule.span_le.mpr ?_))
  rintro _ ⟨M, d, _, _, h, g, rfl⟩
  exact Submodule.mem_iSup_of_mem ⟨(M, d), h⟩ ⟨g.toCuspForm, g.isNew, CuspForm.levelRaiseₗ_apply ..⟩

/-- **The level-raised newspaces `V_d S_k(Γ₁(M))ⁿᵉʷ` (`d * M ∣ N`) are linearly independent**
(Diamond–Shurman, Theorem 5.8.3). -/
theorem iSupIndep_map_levelRaiseₗ_cuspFormsNew (N : ℕ) [NeZero N] (k : ℤ) :
    iSupIndep (fun md : {md : ℕ × ℕ // md.2 * md.1 ∣ N} ↦
      letI : NeZero md.1.1 := NeZero.of_dvd (dvd_of_mul_left_dvd md.2)
      letI : NeZero md.1.2 := NeZero.of_dvd (dvd_of_mul_right_dvd md.2)
      (cuspFormsNew md.1.1 k).map
        (CuspForm.levelRaiseₗ md.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd md.2))) := by
  let v := ⇑(Newform.levelRaiseBasis N k)
  let π : (Σ M : {M : ℕ // M ∣ N},
      (letI : NeZero M.1 := NeZero.of_dvd M.2; Newform M.1 k) × {d : ℕ // d * M.1 ∣ N}) →
      {md : ℕ × ℕ // md.2 * md.1 ∣ N} :=
    fun i ↦ ⟨(i.1.1, i.2.2.1), i.2.2.2⟩
  have hle (md : {md : ℕ × ℕ // md.2 * md.1 ∣ N}) :
      (letI : NeZero md.1.1 := NeZero.of_dvd (dvd_of_mul_left_dvd md.2);
        letI : NeZero md.1.2 := NeZero.of_dvd (dvd_of_mul_right_dvd md.2);
        (cuspFormsNew md.1.1 k).map
          (CuspForm.levelRaiseₗ md.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd md.2))) ≤
        Submodule.span ℂ (v '' {i | π i = md}) := by
    have : NeZero md.1.1 := NeZero.of_dvd (dvd_of_mul_left_dvd md.2)
    have : NeZero md.1.2 := NeZero.of_dvd (dvd_of_mul_right_dvd md.2)
    rw [← Newform.span_range_toCuspForm_eq_cuspFormsNew, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨⟨⟨md.1.1, dvd_of_mul_left_dvd md.2⟩, g, ⟨md.1.2, md.2⟩⟩, ?_, ?_⟩
    · exact Subtype.ext rfl
    · simp [v, CuspForm.levelRaiseₗ_apply]
  refine iSupIndep_def.mpr fun md ↦ ?_
  have hdisj := (Newform.levelRaiseBasis N k).linearIndependent.disjoint_span_image
    (s := {i | π i = md}) (t := {i | π i ≠ md}) (Set.disjoint_left.mpr fun _ h₁ h₂ ↦ h₂ h₁)
  refine hdisj.mono (hle md) (iSup₂_le fun md' hne ↦ (hle md').trans (Submodule.span_mono ?_))
  rintro _ ⟨i, rfl, rfl⟩
  exact ⟨i, hne, rfl⟩

/-- **Internal direct-sum decomposition of `S_k(Γ₁(N))`** into the level-raised newspaces
`V_d S_k(Γ₁(M))ⁿᵉʷ` over all pairs `(M, d)` with `d * M ∣ N` (Diamond–Shurman, Theorem 5.8.3). -/
theorem isInternal_map_levelRaiseₗ_cuspFormsNew (N : ℕ) [NeZero N] (k : ℤ) :
    DirectSum.IsInternal (fun md : {md : ℕ × ℕ // md.2 * md.1 ∣ N} ↦
      letI : NeZero md.1.1 := NeZero.of_dvd (dvd_of_mul_left_dvd md.2)
      letI : NeZero md.1.2 := NeZero.of_dvd (dvd_of_mul_right_dvd md.2)
      (cuspFormsNew md.1.1 k).map
        (CuspForm.levelRaiseₗ md.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd md.2))) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_map_levelRaiseₗ_cuspFormsNew N k)
    (iSup_map_levelRaiseₗ_cuspFormsNew_eq_top N k)

/-- **The level-raised character newspaces `V_d S_k(M, χ_M)ⁿᵉʷ` (`d * M ∣ N`, `cond χ ∣ M`) span
`S_k(N, χ)`** (Diamond–Shurman, Theorem 5.8.3). -/
theorem iSup_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace_eq_cuspFormCharSpace (N : ℕ)
    [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    (⨆ md : {md : ℕ × ℕ //
        md.2 * md.1 ∣ N ∧ DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ md.1},
      letI : NeZero md.1.1 := NeZero.of_dvd (dvd_of_mul_left_dvd md.2.1)
      letI : NeZero md.1.2 := NeZero.of_dvd (dvd_of_mul_right_dvd md.2.1)
      (cuspFormsNew md.1.1 k ⊓ cuspFormCharSpace k
        ((DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)).toUnitHom.comp
          (ZMod.unitsMap md.2.2))).map
        (CuspForm.levelRaiseₗ md.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd md.2.1))) =
      cuspFormCharSpace k χ := by
  refine le_antisymm (iSup_le fun md ↦ ?_) fun F hF ↦ ?_
  · have : NeZero md.1.1 := NeZero.of_dvd (dvd_of_mul_left_dvd md.2.1)
    have : NeZero md.1.2 := NeZero.of_dvd (dvd_of_mul_right_dvd md.2.1)
    rintro _ ⟨g, hg, rfl⟩
    rw [CuspForm.levelRaiseₗ_apply]
    have hmem := CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd md.2.1 _ hg.2
    rwa [MonoidHom.comp_assoc, ZMod.unitsMap_comp,
      DirichletCharacter.primitiveCharacter_toUnitHom_comp_unitsMap] at hmem
  · have hbasis : (⟨F, hF⟩ : cuspFormCharSpace k χ) ∈
        Submodule.span ℂ (Set.range (Newform.levelRaiseBasisCharSpace N k χ)) := by
      rw [(Newform.levelRaiseBasisCharSpace N k χ).span_eq]
      exact Submodule.mem_top
    have hmap := Submodule.mem_map_of_mem (f := (cuspFormCharSpace k χ).subtype) hbasis
    rw [Submodule.map_span, ← Set.range_comp] at hmap
    refine Submodule.span_le.mpr (Set.range_subset_iff.mpr ?_) hmap
    intro i
    have : NeZero i.1.1 := NeZero.of_dvd i.1.2
    have : NeZero i.2.2.1 := NeZero.of_dvd (dvd_of_mul_right_dvd i.2.2.2)
    have hcM : DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ i.1.1 :=
      DirichletCharacter.conductor_ofUnitHom_dvd_of_comp_unitsMap_eq i.1.2 i.2.1.2
    have hgχ : i.2.1.1.χ =
        (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)).toUnitHom.comp
          (ZMod.unitsMap hcM) :=
      (ZMod.comp_unitsMap_eq_iff hcM i.1.2 _).mp
        (i.2.1.2.trans (DirichletCharacter.primitiveCharacter_toUnitHom_comp_unitsMap χ).symm)
    refine Submodule.mem_iSup_of_mem ⟨(i.1.1, i.2.2.1), i.2.2.2, hcM⟩
      ⟨i.2.1.1.toCuspForm, ⟨i.2.1.1.isNew, hgχ ▸ i.2.1.1.mem_charSpace⟩, ?_⟩
    simp [CuspForm.levelRaiseₗ_apply]

/-- **The level-raised character newspaces `V_d S_k(M, χ_M)ⁿᵉʷ` (`d * M ∣ N`, `cond χ ∣ M`) are
linearly independent** (Diamond–Shurman, Theorem 5.8.3). -/
theorem iSupIndep_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    iSupIndep (fun md : {md : ℕ × ℕ //
        md.2 * md.1 ∣ N ∧ DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ md.1} ↦
      letI : NeZero md.1.1 := NeZero.of_dvd (dvd_of_mul_left_dvd md.2.1)
      letI : NeZero md.1.2 := NeZero.of_dvd (dvd_of_mul_right_dvd md.2.1)
      (cuspFormsNew md.1.1 k ⊓ cuspFormCharSpace k
        ((DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)).toUnitHom.comp
          (ZMod.unitsMap md.2.2))).map
        (CuspForm.levelRaiseₗ md.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd md.2.1))) := by
  refine iSupIndep_def.mpr fun md ↦ ?_
  have hind := iSupIndep_def.mp (iSupIndep_map_levelRaiseₗ_cuspFormsNew N k) ⟨md.1, md.2.1⟩
  refine hind.mono (Submodule.map_mono inf_le_left) (iSup₂_le fun md' hne ↦ ?_)
  have hne' : (⟨md'.1, md'.2.1⟩ : {md : ℕ × ℕ // md.2 * md.1 ∣ N}) ≠ ⟨md.1, md.2.1⟩ :=
    fun h ↦ hne (Subtype.ext (Subtype.mk.inj h))
  exact le_iSup₂_of_le ⟨md'.1, md'.2.1⟩ hne' (Submodule.map_mono inf_le_left)

/-- **Internal direct-sum decomposition of `S_k(N, χ)`** into the level-raised character newspaces
`V_d S_k(M, χ_M)ⁿᵉʷ` over all pairs `(M, d)` with `d * M ∣ N` and `cond χ ∣ M` (Diamond–Shurman,
Theorem 5.8.3). -/
theorem isInternal_comap_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace (N : ℕ) [NeZero N]
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    DirectSum.IsInternal (fun md : {md : ℕ × ℕ //
        md.2 * md.1 ∣ N ∧ DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ md.1} ↦
      letI : NeZero md.1.1 := NeZero.of_dvd (dvd_of_mul_left_dvd md.2.1)
      letI : NeZero md.1.2 := NeZero.of_dvd (dvd_of_mul_right_dvd md.2.1)
      ((cuspFormsNew md.1.1 k ⊓ cuspFormCharSpace k
        ((DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)).toUnitHom.comp
          (ZMod.unitsMap md.2.2))).map
        (CuspForm.levelRaiseₗ md.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd md.2.1))).comap
        (cuspFormCharSpace k χ).subtype) :=
  DirectSum.isInternal_comap_subtype_of_iSupIndep_of_iSup_eq
    (iSupIndep_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace N k χ)
    (iSup_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace_eq_cuspFormCharSpace N k χ)

/-! ### Forward divisor-count dimension identities -/

/-- **Divisor-count dimension formula for `S_k(Γ₁(N))`** (a consequence of Diamond–Shurman,
Theorem 5.8.3): `dim S_k(Γ₁(N)) = ∑_{M ∣ N} #(N / M).divisors · dim S_k(Γ₁(M))ⁿᵉʷ`. -/
theorem finrank_cuspForm_Gamma1_eq_sum_divisors (N : ℕ) [NeZero N] (k : ℤ) :
    Module.finrank ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ∑ M ∈ N.divisors.attach,
        letI : NeZero M.1 := NeZero.of_dvd (Nat.dvd_of_mem_divisors M.2)
        #(N / M.1).divisors * Module.finrank ℂ (cuspFormsNew M.1 k) := by
  have : ∀ a : ↥N.divisors,
      Finite ((letI : NeZero (Nat.divisorsEquiv N a).1 := NeZero.of_dvd (Nat.divisorsEquiv N a).2;
        Newform (Nat.divisorsEquiv N a).1 k) × {d : ℕ // d * (Nat.divisorsEquiv N a).1 ∣ N}) :=
    fun a ↦
      letI : NeZero (Nat.divisorsEquiv N a).1 := NeZero.of_dvd (Nat.divisorsEquiv N a).2
      inferInstance
  rw [Module.finrank_eq_nat_card_basis (Newform.levelRaiseBasis N k),
    ← Nat.card_congr (Equiv.sigmaCongrLeft (Nat.divisorsEquiv N)), Nat.card_sigma]
  refine Finset.sum_congr rfl fun M _ ↦ ?_
  have hM : M.1 ∣ N := Nat.dvd_of_mem_divisors M.2
  have : NeZero M.1 := NeZero.of_dvd hM
  rw [Nat.divisorsEquiv_apply, Nat.card_prod, Nat.card_mul_dvd hM, Newform.finrank_cuspFormsNew,
    mul_comm]

private lemma finrank_cuspFormCharSpace_eq_sum_divisors_natCard (M : ℕ) [NeZero M] (k : ℤ)
    (ψ : (ZMod M)ˣ →* ℂˣ) :
    Module.finrank ℂ (cuspFormCharSpace k ψ) =
      ∑ d ∈ M.divisors.attach,
        letI : NeZero d.1 := NeZero.of_dvd (Nat.dvd_of_mem_divisors d.2)
        #(M / d.1).divisors *
          Nat.card {g : Newform d.1 k //
            g.χ.comp (ZMod.unitsMap (Nat.dvd_of_mem_divisors d.2)) = ψ} := by
  have : ∀ a : ↥M.divisors,
      Finite ((letI : NeZero (Nat.divisorsEquiv M a).1 := NeZero.of_dvd (Nat.divisorsEquiv M a).2;
        {g : Newform (Nat.divisorsEquiv M a).1 k //
          g.χ.comp (ZMod.unitsMap (Nat.divisorsEquiv M a).2) = ψ}) ×
        {e : ℕ // e * (Nat.divisorsEquiv M a).1 ∣ M}) :=
    fun a ↦
      letI : NeZero (Nat.divisorsEquiv M a).1 := NeZero.of_dvd (Nat.divisorsEquiv M a).2
      inferInstance
  rw [Module.finrank_eq_nat_card_basis (Newform.levelRaiseBasisCharSpace M k ψ),
    ← Nat.card_congr (Equiv.sigmaCongrLeft (Nat.divisorsEquiv M)), Nat.card_sigma]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  have hdM : d.1 ∣ M := Nat.dvd_of_mem_divisors d.2
  have : NeZero d.1 := NeZero.of_dvd hdM
  rw [Nat.divisorsEquiv_apply, Nat.card_prod, Nat.card_mul_dvd hdM, mul_comm]

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
