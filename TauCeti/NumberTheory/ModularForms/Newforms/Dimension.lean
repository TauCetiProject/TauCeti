/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.Moebius
public import TauCeti.NumberTheory.ModularForms.Newforms.Decomposition
public import TauCeti.NumberTheory.ModularForms.TrivialNebentypus

import Mathlib.SetTheory.Cardinal.Finite

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
   (`HeckeRing.GL2.Newform.level_eq_and_coe_eq_of_comp_unitsMap_eq`).
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
* `HeckeRing.GL2.Newform.linearIndependent_levelRaise_of_comp_unitsMap_eq`,
  `HeckeRing.GL2.Newform.linearIndependent_levelRaise`: linear independence of the level-raised
  newforms at a fixed nebentypus and across all nebentypes.
* `TauCeti.iSup_map_levelRaiseₗ_cuspFormsNew_eq_top`,
  `TauCeti.iSupIndep_map_levelRaiseₗ_cuspFormsNew`,
  `TauCeti.isInternal_map_levelRaiseₗ_cuspFormsNew`: internal direct-sum decomposition of
  `S_k(Γ₁(N))` into `V_d S_k(Γ₁(M))ⁿᵉʷ` over all pairs `(M, d)` with `d * M ∣ N`.
* `TauCeti.iSup_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace`,
  `TauCeti.iSupIndep_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace`,
  `TauCeti.isInternal_comap_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace`: the
  fixed-character refinement on `S_k(N, χ)` over pairs `(M, d)` with `d * M ∣ N` and `cond χ ∣ M`.
* `TauCeti.finrank_cuspForm_Gamma1_eq_sum_divisors`,
  `TauCeti.finrank_cuspFormCharSpace_eq_sum_divisors`,
  `TauCeti.finrank_cuspForm_Gamma0_eq_sum_divisors`: forward dimension identities weighted by
  `#(N / M).divisors`.
* `TauCeti.natCast_finrank_cuspFormsNew`,
  `TauCeti.natCast_finrank_cuspFormsNew_comap_cuspFormCharSpace`,
  `TauCeti.natCast_finrank_cuspFormsNew_comap_cuspFormCharSpace_one`: Möbius-square (`μ * μ`)
  dimension formulas for `S_k(Γ₁(N))ⁿᵉʷ`, `S_k(N, χ)ⁿᵉʷ`, and `S_k(Γ₀(N))ⁿᵉʷ`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.3.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.13 and Corollary 4.6.20.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup Finset
open scoped MatrixGroups ArithmeticFunction.Moebius

/-! ### Gluing linearly independent families across an independent family of submodules -/

private lemma linearIndependent_sigma_of_iSupIndep {R M η α : Type*} [Ring R] [AddCommGroup M]
    [Module R M] {ι : η → Type*} {f : ∀ j : η, ι j → M} {W : α → Submodule R M} {e : η → α}
    (hli : ∀ j, LinearIndependent R (f j)) (hW : iSupIndep W) (he : Function.Injective e)
    (hfW : ∀ j k, f j k ∈ W (e j)) :
    LinearIndependent R (fun jk : Σ j, ι j ↦ f jk.1 jk.2) := by
  refine linearIndependent_iUnion_finite hli fun i t _ hit ↦ (hW (e i)).mono ?_ ?_
  · exact Submodule.span_le.mpr (Set.range_subset_iff.mpr (hfW i))
  · refine iSup₂_le fun j hjt ↦ le_iSup₂_of_le (e j) (he.ne fun hji ↦ hit (hji ▸ hjt)) ?_
    exact Submodule.span_le.mpr (Set.range_subset_iff.mpr (hfW j))

namespace HeckeRing.GL2.Newform

open TauCeti _root_.CuspForm

/-! ### Dimension of `S_k(Γ₁(N))ⁿᵉʷ` and linear independence of level-raised newforms -/

/-- **The dimension of `S_k(Γ₁(N))ⁿᵉʷ` is the number of newforms of level `N` and weight `k`.** -/
theorem finrank_cuspFormsNew (N : ℕ) [NeZero N] (k : ℤ) :
    Module.finrank ℂ (cuspFormsNew N k) = Nat.card (Newform N k) :=
  Module.finrank_eq_nat_card_basis (basis N k)

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
  let eig : η → P → ℂ := fun mg p ↦
    letI : NeZero mg.1.1 := NeZero.of_dvd mg.1.2
    mg.2.1.eigenvalue ⟨p.1, p.2.1.pos⟩ (p.2.2.coprime_dvd_right mg.1.2)
  have heig : Function.Injective eig := by
    rintro ⟨⟨M₁, hM₁⟩, g₁, hg₁⟩ ⟨⟨M₂, hM₂⟩, g₂, hg₂⟩ h
    have : NeZero M₁ := NeZero.of_dvd hM₁
    have : NeZero M₂ := NeZero.of_dvd hM₂
    obtain ⟨rfl, hcoe⟩ := level_eq_and_coe_eq_of_comp_unitsMap_eq g₁ g₂ hM₁ hM₂ hg₁ hg₂ (S := ∅)
      fun p hp hpN _ ↦ congr_fun h ⟨p, hp, hpN⟩
    have hg : g₁ = g₂ := Newform.ext (DFunLike.coe_injective hcoe)
    subst hg
    rfl
  let fam : ∀ mg : η, {d : ℕ // d * mg.1.1 ∣ N} → CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
    fun mg d ↦
      letI : NeZero mg.1.1 := NeZero.of_dvd mg.1.2
      letI : NeZero d.1 := NeZero.of_dvd (dvd_of_mul_right_dvd d.2)
      CuspForm.levelRaise d.1 (Gamma1_map_le_conjAct_scaleGL_of_dvd d.2) mg.2.1.toCuspForm
  have hli_sigma := linearIndependent_sigma_of_iSupIndep (f := fam)
    (W := fun a : P → ℂ ↦ ⨅ p, (T p).eigenspace (a p)) (e := eig)
    (fun mg ↦ by
      have : NeZero mg.1.1 := NeZero.of_dvd mg.1.2
      have : ∀ d : {d : ℕ // d * mg.1.1 ∣ N}, NeZero d.1 :=
        fun d ↦ NeZero.of_dvd (dvd_of_mul_right_dvd d.2)
      exact _root_.CuspForm.linearIndependent_levelRaise (one_mem_strictPeriods_Gamma1_map mg.1.1)
        mg.2.1.ne_zero Subtype.val_injective
        fun d ↦ Gamma1_map_le_conjAct_scaleGL_of_dvd d.2)
    (iSupIndep_iInf_eigenspace T) heig
    fun mg d ↦ by
      have : NeZero mg.1.1 := NeZero.of_dvd mg.1.2
      have : NeZero d.1 := NeZero.of_dvd (dvd_of_mul_right_dvd d.2)
      exact (Submodule.mem_iInf _).mpr fun p ↦ Module.End.mem_eigenspace_iff.mpr
        (mg.2.1.heckeTCuspNat_levelRaise_eq_eigenvalue_smul d.2 p.2.1 p.2.2)
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
  have hli_sigma := linearIndependent_sigma_of_iSupIndep
    (W := cuspFormCharSpace (N := N) k) (e := id)
    (fun χ ↦ linearIndependent_levelRaise_of_comp_unitsMap_eq N k χ)
    (iSupIndep_cuspFormCharSpace k) Function.injective_id
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

/-! ### Character-descent helpers for fixed-nebentypus decompositions and dimensions -/

private lemma primitiveCharacter_toUnitHom_comp_unitsMap {N : ℕ} (χ : (ZMod N)ˣ →* ℂˣ) :
    (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)).toUnitHom.comp
      (ZMod.unitsMap (DirichletCharacter.conductor_dvd_level (MulChar.ofUnitHom χ))) = χ := by
  rw [← DirichletCharacter.changeLevel_toUnitHom, DirichletCharacter.changeLevel_primitiveCharacter,
    MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq, Equiv.apply_symm_apply]

private lemma conductor_dvd_of_comp_unitsMap_eq {N M d : ℕ} [NeZero N] {χ : (ZMod N)ˣ →* ℂˣ}
    (hdM : d ∣ M) (hcM : DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ M)
    (hMN : M ∣ N) {ψ : (ZMod d)ˣ →* ℂˣ}
    (hψ : ψ.comp (ZMod.unitsMap hdM) =
      (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)).toUnitHom.comp
        (ZMod.unitsMap hcM)) :
    DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ d := by
  have hdN : d ∣ N := hdM.trans hMN
  have hψN : ψ.comp (ZMod.unitsMap hdN) = χ := by
    calc ψ.comp (ZMod.unitsMap hdN)
        = (ψ.comp (ZMod.unitsMap hdM)).comp (ZMod.unitsMap hMN) := by
          rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
      _ = ((DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)).toUnitHom.comp
            (ZMod.unitsMap hcM)).comp (ZMod.unitsMap hMN) := by rw [hψ]
      _ = χ := by
          rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
          exact primitiveCharacter_toUnitHom_comp_unitsMap χ
  refine DirichletCharacter.conductor_dvd_of_mem_conductorSet _ ?_
  simpa only [DirichletCharacter.mem_conductorSet_iff, DirichletCharacter.changeLevel_def,
    MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq, Equiv.apply_symm_apply, hψN] using
    DirichletCharacter.changeLevel_factorsThrough (MulChar.ofUnitHom ψ) hdN

private lemma comp_unitsMap_eq_iff {c d M : ℕ} [NeZero M] (hcd : c ∣ d) (hdM : d ∣ M)
    (hcM : c ∣ M) {ψ : (ZMod d)ˣ →* ℂˣ} {χ₀ : (ZMod c)ˣ →* ℂˣ} :
    ψ.comp (ZMod.unitsMap hdM) = χ₀.comp (ZMod.unitsMap hcM) ↔ ψ = χ₀.comp (ZMod.unitsMap hcd) := by
  have hcomp : (χ₀.comp (ZMod.unitsMap hcd)).comp (ZMod.unitsMap hdM) =
      χ₀.comp (ZMod.unitsMap hcM) := by
    rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
  rw [← hcomp]
  exact MonoidHom.cancel_right (ZMod.unitsMap_surjective hdM)

/-- **The level-raised character newspaces `V_d S_k(M, χ_M)ⁿᵉʷ` (`d * M ∣ N`, `cond χ ∣ M`) span
`S_k(N, χ)`** (Diamond–Shurman, Theorem 5.8.3). -/
theorem iSup_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
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
      primitiveCharacter_toUnitHom_comp_unitsMap] at hmem
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
      conductor_dvd_of_comp_unitsMap_eq i.1.2
        (DirichletCharacter.conductor_dvd_level (MulChar.ofUnitHom χ)) dvd_rfl
        (i.2.1.2.trans (primitiveCharacter_toUnitHom_comp_unitsMap χ).symm)
    have hgχ : i.2.1.1.χ =
        (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)).toUnitHom.comp
          (ZMod.unitsMap hcM) :=
      (comp_unitsMap_eq_iff hcM i.1.2 _).mp
        (i.2.1.2.trans (primitiveCharacter_toUnitHom_comp_unitsMap χ).symm)
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

private lemma isInternal_comap_subtype_of_iSupIndep_of_iSup_eq {R M ι : Type*} [DecidableEq ι]
    [Ring R] [AddCommGroup M] [Module R M] {W : Submodule R M} {U : ι → Submodule R M}
    (hU : iSupIndep U) (hsup : ⨆ i, U i = W) :
    DirectSum.IsInternal (fun i ↦ (U i).comap W.subtype) := by
  have hle (i : ι) : U i ≤ LinearMap.range W.subtype := by
    rw [Submodule.range_subtype]
    exact hsup ▸ le_iSup U i
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · refine iSupIndep_def.mpr fun i ↦ Submodule.disjoint_def.mpr fun x hx₁ hx₂ ↦ ?_
    have hmap := Submodule.mem_map_of_mem (f := W.subtype) hx₂
    rw [Submodule.map_iSup] at hmap
    have hsub : (⨆ j, (⨆ (_ : j ≠ i), (U j).comap W.subtype).map W.subtype) ≤
        ⨆ j ≠ i, U j := by
      refine iSup_le fun j ↦ ?_
      by_cases h : j = i
      · rw [iSup_neg (not_not.mpr h), Submodule.map_bot]
        exact bot_le
      · simpa only [iSup_pos h, Submodule.map_comap_eq_self (hle j)] using
          le_iSup₂ (f := fun j (_ : j ≠ i) ↦ U j) j h
    exact Subtype.ext
      ((Submodule.disjoint_def.mp (iSupIndep_def.mp hU i)) x.1 hx₁ (hsub hmap))
  · refine eq_top_iff.mpr fun x _ ↦ ?_
    have hx : (x : M) ∈ (⨆ i, (U i).comap W.subtype).map W.subtype := by
      rw [Submodule.map_iSup]
      simpa only [Submodule.map_comap_eq_self (hle _), hsup] using x.2
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
    rwa [← Subtype.ext hyx]

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
  isInternal_comap_subtype_of_iSupIndep_of_iSup_eq
    (iSupIndep_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace N k χ)
    (iSup_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace N k χ)

/-! ### Forward divisor-count dimension identities -/

private def divisorsEquiv (N : ℕ) [NeZero N] : ↥N.divisors ≃ {M : ℕ // M ∣ N} where
  toFun M := ⟨M.1, Nat.dvd_of_mem_divisors M.2⟩
  invFun M := ⟨M.1, Nat.mem_divisors.mpr ⟨M.2, NeZero.ne N⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
private lemma divisorsEquiv_apply (N : ℕ) [NeZero N] (M : ↥N.divisors) :
    divisorsEquiv N M = ⟨M.1, Nat.dvd_of_mem_divisors M.2⟩ :=
  rfl

private def mulDvdEquivDivDivisors {M N : ℕ} [NeZero N] (hM : M ∣ N) :
    {d : ℕ // d * M ∣ N} ≃ ↥(N / M).divisors where
  toFun d := ⟨d.1, Nat.mem_divisors.mpr
    ⟨by
      have hM0 : M ≠ 0 := (NeZero.of_dvd hM).out
      refine (mul_dvd_mul_iff_left hM0).mp ?_
      rw [mul_comm, Nat.mul_div_cancel' hM]
      exact d.2,
      fun h0 ↦ NeZero.ne N
        (by have := Nat.mul_div_cancel' hM; rw [h0, mul_zero] at this; exact this.symm)⟩⟩
  invFun d := ⟨d.1,
    (mul_comm d.1 M ▸ mul_dvd_mul_left M (Nat.dvd_of_mem_divisors d.2)).trans
      (dvd_of_eq (Nat.mul_div_cancel' hM))⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma finite_mul_dvd {M N : ℕ} [NeZero N] (hM : M ∣ N) :
    Finite {d : ℕ // d * M ∣ N} :=
  Finite.of_equiv _ (mulDvdEquivDivDivisors hM).symm

private lemma natCard_mul_dvd {M N : ℕ} [NeZero N] (hM : M ∣ N) :
    Nat.card {d : ℕ // d * M ∣ N} = #(N / M).divisors := by
  rw [Nat.card_congr (mulDvdEquivDivDivisors hM), Nat.card_eq_fintype_card, Fintype.card_coe]

/-- **Divisor-count dimension formula for `S_k(Γ₁(N))`** (Diamond–Shurman, Theorem 5.8.3):
`dim S_k(Γ₁(N)) = ∑_{M ∣ N} #(N / M).divisors · dim S_k(Γ₁(M))ⁿᵉʷ`. -/
theorem finrank_cuspForm_Gamma1_eq_sum_divisors (N : ℕ) [NeZero N] (k : ℤ) :
    Module.finrank ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ∑ M ∈ N.divisors.attach,
        letI : NeZero M.1 := NeZero.of_dvd (Nat.dvd_of_mem_divisors M.2)
        #(N / M.1).divisors * Module.finrank ℂ (cuspFormsNew M.1 k) := by
  have : ∀ a : ↥N.divisors,
      Finite ((letI : NeZero (divisorsEquiv N a).1 := NeZero.of_dvd (divisorsEquiv N a).2;
        Newform (divisorsEquiv N a).1 k) × {d : ℕ // d * (divisorsEquiv N a).1 ∣ N}) :=
    fun a ↦
      letI : NeZero (divisorsEquiv N a).1 := NeZero.of_dvd (divisorsEquiv N a).2
      letI := finite_mul_dvd (divisorsEquiv N a).2
      inferInstance
  rw [Module.finrank_eq_nat_card_basis (Newform.levelRaiseBasis N k),
    ← Nat.card_congr (Equiv.sigmaCongrLeft (divisorsEquiv N)), Nat.card_sigma]
  refine Finset.sum_congr rfl fun M _ ↦ ?_
  have hM : M.1 ∣ N := Nat.dvd_of_mem_divisors M.2
  have : NeZero M.1 := NeZero.of_dvd hM
  rw [divisorsEquiv_apply, Nat.card_prod, natCard_mul_dvd hM, Newform.finrank_cuspFormsNew,
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
      Finite ((letI : NeZero (divisorsEquiv M a).1 := NeZero.of_dvd (divisorsEquiv M a).2;
        {g : Newform (divisorsEquiv M a).1 k //
          g.χ.comp (ZMod.unitsMap (divisorsEquiv M a).2) = ψ}) ×
        {e : ℕ // e * (divisorsEquiv M a).1 ∣ M}) :=
    fun a ↦
      letI : NeZero (divisorsEquiv M a).1 := NeZero.of_dvd (divisorsEquiv M a).2
      letI := finite_mul_dvd (divisorsEquiv M a).2
      inferInstance
  rw [Module.finrank_eq_nat_card_basis (Newform.levelRaiseBasisCharSpace M k ψ),
    ← Nat.card_congr (Equiv.sigmaCongrLeft (divisorsEquiv M)), Nat.card_sigma]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  have hdM : d.1 ∣ M := Nat.dvd_of_mem_divisors d.2
  have : NeZero d.1 := NeZero.of_dvd hdM
  rw [divisorsEquiv_apply, Nat.card_prod, natCard_mul_dvd hdM, mul_comm]

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
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g ↦ comp_unitsMap_eq_iff hcd hdM hcM)
  · have : IsEmpty {g : Newform d k //
        g.χ.comp (ZMod.unitsMap hdM) =
          (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ)).toUnitHom.comp
            (ZMod.unitsMap hcM)} :=
      ⟨fun ⟨g, hg⟩ ↦ hcd (conductor_dvd_of_comp_unitsMap_eq hdM hcM hMN hg)⟩
    exact Nat.card_of_isEmpty

/-- **Divisor-count dimension formula for `S_k(N, χ)`** (Diamond–Shurman, Theorem 5.8.3):
`dim S_k(N, χ) = ∑_{cond χ ∣ M ∣ N} #(N / M).divisors · dim S_k(M, χ_M)ⁿᵉʷ`, where `χ_M` is the
descent of `χ` to level `M`. -/
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
  rw [primitiveCharacter_toUnitHom_comp_unitsMap] at hcard
  rw [hcard]
  split_ifs <;> simp

private lemma ofUnitHom_one (N : ℕ) :
    (MulChar.ofUnitHom (1 : (ZMod N)ˣ →* ℂˣ) : DirichletCharacter ℂ N) = 1 :=
  MulChar.ext fun _ ↦ by simp

private lemma primitiveCharacter_ofUnitHom_one_comp_unitsMap {N M : ℕ} [NeZero N]
    (hc : DirichletCharacter.conductor (MulChar.ofUnitHom (1 : (ZMod N)ˣ →* ℂˣ)) ∣ M) :
    (DirichletCharacter.primitiveCharacter
        (MulChar.ofUnitHom (1 : (ZMod N)ˣ →* ℂˣ))).toUnitHom.comp (ZMod.unitsMap hc) =
      (1 : (ZMod M)ˣ →* ℂˣ) := by
  have h1 : DirichletCharacter.primitiveCharacter
      (MulChar.ofUnitHom (1 : (ZMod N)ˣ →* ℂˣ)) = 1 := by
    rw [ofUnitHom_one]
    exact DirichletCharacter.primitiveCharacter_one
  rw [h1]
  exact MonoidHom.ext fun u ↦ Units.ext <| by
    rw [MonoidHom.comp_apply, MulChar.coe_toUnitHom, MulChar.one_apply_coe,
      MonoidHom.one_apply, Units.val_one]

/-- **Divisor-count dimension formula for `S_k(Γ₀(N))`** (Diamond–Shurman, Theorem 5.8.3). -/
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
    rw [ofUnitHom_one, DirichletCharacter.conductor_one]
    exact one_dvd M.1
  rw [dite_eq_left_of_eq_true (eq_true hc), primitiveCharacter_ofUnitHom_one_comp_unitsMap hc]

/-! ### Möbius-square (`μ * μ`) newspace dimension formulas -/

/-- **Möbius-square dimension formula for `S_k(Γ₁(N))ⁿᵉʷ`** (Diamond–Shurman, Theorem 5.8.3):
`dim S_k(Γ₁(N))ⁿᵉʷ = ∑_{M ∣ N} (μ * μ)(N / M) · dim S_k(Γ₁(M))`. -/
theorem natCast_finrank_cuspFormsNew (N : ℕ) [NeZero N] (k : ℤ) :
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

/-- **Möbius-square dimension formula for `S_k(N, χ)ⁿᵉʷ`** (Diamond–Shurman, Theorem 5.8.3):
`dim S_k(N, χ)ⁿᵉʷ = ∑_{cond χ ∣ M ∣ N} (μ * μ)(N / M) · dim S_k(M, χ_M)`. -/
theorem natCast_finrank_cuspFormsNew_comap_cuspFormCharSpace (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
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
      primitiveCharacter_toUnitHom_comp_unitsMap]
  have hinv := ArithmeticFunction.eq_sum_divisors_filter_dvd_moebius_mul_moebius_mul (f := f)
    (g := g) hcN (NeZero.pos N) fun M hcM hMN ↦ by
      have : NeZero M := NeZero.of_dvd hMN
      dsimp only [g]
      rw [dite_eq_left_of_eq_true (eq_true hcM),
        finrank_cuspFormCharSpace_eq_sum_divisors_natCard M k (χ₀.comp (ZMod.unitsMap hcM)),
        Nat.cast_sum, Finset.sum_filter, ← Finset.sum_attach M.divisors]
      refine Finset.sum_congr rfl fun d _ ↦ ?_
      have hdM : d.1 ∣ M := Nat.dvd_of_mem_divisors d.2
      have hd0 : d.1 ≠ 0 := (Nat.pos_of_mem_divisors d.2).ne'
      have hcard := natCard_newform_comp_unitsMap_eq (k := k) (χ := χ) hdM hcM hMN
      rw [Nat.cast_mul, hcard]
      by_cases hcd : c ∣ d.1
      · rw [dite_eq_left_of_eq_true (eq_true hcd), ite_eq_left hcd]
        dsimp only [f]
        rw [dite_eq_left_of_eq_true (eq_true ⟨hd0, hcd⟩)]
      · rw [dite_eq_right_of_eq_false (eq_false hcd), ite_eq_right hcd, Nat.cast_zero, mul_zero]
  rw [← hfN, hinv, Finset.sum_filter]
  refine Finset.sum_congr rfl fun M _ ↦ ?_
  dsimp only [g, χ₀]
  split_ifs <;> rfl

/-- **Möbius-square dimension formula for `S_k(Γ₀(N))ⁿᵉʷ`** (Diamond–Shurman, Theorem 5.8.3):
`dim S_k(Γ₀(N))ⁿᵉʷ = ∑_{M ∣ N} (μ * μ)(N / M) · dim S_k(Γ₀(M))`. -/
theorem natCast_finrank_cuspFormsNew_comap_cuspFormCharSpace_one (N : ℕ) [NeZero N] (k : ℤ) :
    (Module.finrank ℂ
      ((cuspFormsNew N k).comap (cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)).subtype) : ℤ) =
      ∑ M ∈ N.divisors, (μ * μ) (N / M) *
        (Module.finrank ℂ (CuspForm ((Gamma0 M).map (mapGL ℝ)) k) : ℤ) := by
  rw [natCast_finrank_cuspFormsNew_comap_cuspFormCharSpace]
  refine Finset.sum_congr rfl fun M hM ↦ ?_
  have : NeZero M := ⟨(Nat.pos_of_mem_divisors hM).ne'⟩
  have hc : DirichletCharacter.conductor (MulChar.ofUnitHom (1 : (ZMod N)ˣ →* ℂˣ)) ∣ M := by
    rw [ofUnitHom_one, DirichletCharacter.conductor_one]
    exact one_dvd M
  rw [dite_eq_left_of_eq_true (eq_true hc), primitiveCharacter_ofUnitHom_one_comp_unitsMap hc,
    (cuspFormCharSpaceOneEquiv M k).finrank_eq]

end TauCeti

end
