/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.Decomposition
import TauCeti.Algebra.DirectSum.Internal

/-!
# The all-divisor newform basis and direct-sum decomposition of cusp forms

Every cusp form of level `Γ₁(N)` and weight `k` is a linear combination of the level-raised
newforms `V_d g`, `(V_d g)(τ) = g(dτ)`, as `(M, d)` ranges over positive integers with `d * M ∣ N`
and `g` over the newforms of level `M` (`HeckeRing.GL2.Newform.span_levelRaise_eq_top`). This file
proves that those level-raised newforms are `ℂ`-linearly independent, hence form a basis of
`S_k(Γ₁(N))`, and deduces the internal direct-sum decompositions of `S_k(Γ₁(N))` and of each
nebentypus space `S_k(N, χ)` (Diamond–Shurman, Theorem 5.8.3):

```text
S_k(Γ₁(N)) = ⨁_{d * M ∣ N} V_d(S_k(Γ₁(M))ⁿᵉʷ),
S_k(N, χ)  = ⨁_{d * M ∣ N, cond(χ) ∣ M} V_d(S_k(M, χ_M)ⁿᵉʷ).
```

*Linear independence.* Each `V_d g` is a joint eigenvector of the diamond operators `⟨u⟩` for
`u ∈ (ZMod N)ˣ` and the good Hecke operators `T_q` for primes `q ∤ N`, with joint eigenvalue system
determined by `(M, g)`. Strong multiplicity one across divisor levels
(`HeckeRing.GL2.Newform.level_eq_and_coe_eq_of_comp_unitsMap_eq`) shows that distinct pairs `(M, g)`
carry distinct joint eigenvalue systems, so their spans lie in supremum-independent joint
eigenspaces (`TauCeti.iSupIndep_iInf_eigenspace`). Within the span attached to a single `(M, g)`,
the forms `V_d g` at distinct positive `d` are linearly independent by `q`-expansion
(`CuspForm.linearIndependent_levelRaise`).

## Main definitions

* `HeckeRing.GL2.Newform.levelRaiseBasis N k`: the basis of `S_k(Γ₁(N))` indexed by
  `Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.1.1 k`, sending `⟨(M, d), g⟩` to `V_d g`.
* `HeckeRing.GL2.Newform.levelRaiseBasisCharSpace N k χ`: the basis of `S_k(N, χ)` formed by the
  level-raised newforms `V_d g` whose nebentypus `g.χ` pulls back to `χ` modulo `N`.

## Main results

* `HeckeRing.GL2.Newform.linearIndependent_levelRaise`: all level-raised newforms `V_d g` with
  `d * M ∣ N` are `ℂ`-linearly independent in `S_k(Γ₁(N))`.
* `TauCeti.iSup_map_levelRaiseₗ_cuspFormsNew_eq_top`,
  `TauCeti.iSupIndep_map_levelRaiseₗ_cuspFormsNew`,
  `TauCeti.isInternal_map_levelRaiseₗ_cuspFormsNew`: `S_k(Γ₁(N))` is the internal direct sum of
  `V_d(S_k(Γ₁(M))ⁿᵉʷ)` over positive `(M, d)` with `d * M ∣ N`.
* `TauCeti.iSup_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace`,
  `TauCeti.iSupIndep_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace`,
  `TauCeti.isInternal_comap_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace`: `S_k(N, χ)` is the
  internal direct sum of `V_d(S_k(M, χ_M)ⁿᵉʷ)` over positive `(M, d)` with `d * M ∣ N` and
  `cond(χ) ∣ M`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.3.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.19 and Corollary 4.6.20.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups

namespace HeckeRing.GL2

open TauCeti _root_.CuspForm

variable {N : ℕ} {k : ℤ}

namespace Newform

/-! ### Linear independence and basis of level-raised newforms -/

/-- The joint eigenvalue system of `V_d g` on `(ZMod N)ˣ ⊕ {q : ℕ // q.Prime ∧ q.Coprime N}`,
depending only on the divisor level `M ∣ N` and the newform `g : Newform M k`. -/
private noncomputable def levelRaiseEigenvalues (N : ℕ) (k : ℤ)
    (j : Σ M : {M : ℕ+ // (M : ℕ) ∣ N}, Newform M.1 k) :
    (ZMod N)ˣ ⊕ {q : ℕ // q.Prime ∧ Nat.Coprime q N} → ℂ :=
  Sum.elim (fun u ↦ (j.2.χ (ZMod.unitsMap j.1.2 u) : ℂ))
    (fun q ↦ j.2.eigenvalue ⟨q.1, q.2.1.pos⟩ (q.2.2.coprime_dvd_right j.1.2))

/-- Strong multiplicity one across divisor levels makes `levelRaiseEigenvalues` injective. -/
private theorem levelRaiseEigenvalues_injective [NeZero N] (k : ℤ) :
    Function.Injective (levelRaiseEigenvalues N k) := by
  rintro ⟨⟨M₁, hM₁⟩, g₁⟩ ⟨⟨M₂, hM₂⟩, g₂⟩ heq
  have hχ : g₁.χ.comp (ZMod.unitsMap hM₁) = g₂.χ.comp (ZMod.unitsMap hM₂) :=
    MonoidHom.ext fun u ↦ Units.ext (congrFun heq (Sum.inl u))
  obtain ⟨hM, hcoe⟩ := level_eq_and_coe_eq_of_comp_unitsMap_eq g₁ g₂ hM₁ hM₂ rfl hχ.symm
    (S := ∅) fun p hp hpN _ ↦ congrFun heq (Sum.inr ⟨p, hp, hpN⟩)
  obtain rfl : M₁ = M₂ := PNat.eq hM
  exact Sigma.ext (Subtype.ext rfl) (heq_of_eq (Newform.ext (DFunLike.coe_injective hcoe)))

/-- The endomorphism family of diamond operators and good Hecke operators on `S_k(Γ₁(N))`. -/
private noncomputable def levelRaiseEndFamily (N : ℕ) [NeZero N] (k : ℤ) :
    (ZMod N)ˣ ⊕ {q : ℕ // q.Prime ∧ Nat.Coprime q N} →
      Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  Sum.elim (diamondOpCuspHom k) (fun q ↦ heckeTCuspNat k q.1 (_hn := ⟨q.2.1.ne_zero⟩))

/-- The fiber `d ↦ V_d g` in `S_k(Γ₁(N))` attached to `j = ⟨M, g⟩`. -/
private noncomputable def levelRaiseFiber (N : ℕ) (k : ℤ)
    (j : Σ M : {M : ℕ+ // (M : ℕ) ∣ N}, Newform M.1 k)
    (d : {d : ℕ+ // (d : ℕ) * j.1.1 ∣ N}) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  CuspForm.levelRaise d.1 (Gamma1_map_le_conjAct_scaleGL_of_dvd d.2) j.2.toCuspForm

private theorem span_range_levelRaiseFiber_le_iInf_eigenspace [NeZero N] (k : ℤ)
    (j : Σ M : {M : ℕ+ // (M : ℕ) ∣ N}, Newform M.1 k) :
    Submodule.span ℂ (Set.range (levelRaiseFiber N k j)) ≤
      ⨅ i, (levelRaiseEndFamily N k i).eigenspace (levelRaiseEigenvalues N k j i) := by
  rw [Submodule.span_le, Set.range_subset_iff]
  intro d
  refine (Submodule.mem_iInf _).mpr ?_
  rintro (u | q)
  · have hχ := (mem_cuspFormCharSpace_iff k _ _).mp
      (CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd d.2 j.2.χ j.2.mem_charSpace) u
    rw [Module.End.mem_eigenspace_iff]
    exact hχ
  · rw [Module.End.mem_eigenspace_iff]
    exact j.2.heckeTCuspNat_levelRaise_eq_eigenvalue_smul d.2 q.2.1 q.2.2

private theorem linearIndependent_levelRaiseFiber_sigma (N : ℕ) [NeZero N] (k : ℤ) :
    LinearIndependent ℂ
      (fun ji : Σ j : (Σ M : {M : ℕ+ // (M : ℕ) ∣ N}, Newform M.1 k),
        {d : ℕ+ // (d : ℕ) * j.1.1 ∣ N} ↦ levelRaiseFiber N k ji.1 ji.2) := by
  have hfib (j : Σ M : {M : ℕ+ // (M : ℕ) ∣ N}, Newform M.1 k) :
      LinearIndependent ℂ (levelRaiseFiber N k j) :=
    _root_.CuspForm.linearIndependent_levelRaise (one_mem_strictPeriods_Gamma1_map _)
      (d := fun d : {d : ℕ+ // (d : ℕ) * j.1.1 ∣ N} ↦ (d.1 : ℕ))
      (fun _ _ h ↦ Subtype.ext (PNat.eq h))
      (fun d ↦ Gamma1_map_le_conjAct_scaleGL_of_dvd d.2) j.2.ne_zero
  have hindep : iSupIndep fun j ↦ Submodule.span ℂ (Set.range (levelRaiseFiber N k j)) :=
    ((iSupIndep_iInf_eigenspace (levelRaiseEndFamily N k)).comp
      (levelRaiseEigenvalues_injective k)).mono
      (span_range_levelRaiseFiber_le_iInf_eigenspace k)
  exact linearIndependent_iUnion_finite hfib fun _ _ _ hjt ↦ hindep.disjoint_biSup hjt

/-- **The level-raised newforms are linearly independent** (Diamond–Shurman, Theorem 5.8.3):
as `p = (M, d)` ranges over pairs of positive integers with `d * M ∣ N` and `g` over `Newform M k`,
the cusp forms `V_d g` in `S_k(Γ₁(N))` are `ℂ`-linearly independent. -/
theorem linearIndependent_levelRaise (N : ℕ) [NeZero N] (k : ℤ) :
    LinearIndependent ℂ
      (fun x : Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.1.1 k ↦
        CuspForm.levelRaise x.1.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd x.1.2)
          x.2.toCuspForm) := by
  exact (linearIndependent_levelRaiseFiber_sigma N k).comp
    (fun x : Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.1.1 k ↦
      ⟨⟨⟨x.1.1.1, dvd_of_mul_left_dvd x.1.2⟩, x.2⟩, ⟨x.1.1.2, x.1.2⟩⟩)
    fun ⟨⟨⟨M₁, d₁⟩, h₁⟩, g₁⟩ ⟨⟨⟨M₂, d₂⟩, h₂⟩, g₂⟩ h ↦ by
      simp only [Sigma.mk.inj_iff, Subtype.mk.injEq] at h
      obtain ⟨⟨rfl, hg⟩, hd⟩ := h
      obtain rfl : d₁ = d₂ := Subtype.ext_iff.mp (eq_of_heq hd)
      obtain rfl : g₁ = g₂ := eq_of_heq hg
      rfl

private theorem top_le_span_range_levelRaise (N : ℕ) [NeZero N] (k : ℤ) :
    ⊤ ≤ Submodule.span ℂ (Set.range
      (fun x : Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.1.1 k ↦
        CuspForm.levelRaise x.1.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd x.1.2)
          x.2.toCuspForm)) := by
  rw [← span_levelRaise_eq_top N k]
  refine Submodule.span_mono ?_
  rintro _ ⟨M, d, _, _, h, g, rfl⟩
  exact ⟨⟨⟨(⟨M, NeZero.pos M⟩, ⟨d, NeZero.pos d⟩), h⟩, g⟩, rfl⟩

/-- **The level-raised newforms, as a basis of `S_k(Γ₁(N))`** (Diamond–Shurman, Theorem 5.8.3). -/
noncomputable def levelRaiseBasis (N : ℕ) [NeZero N] (k : ℤ) :
    Module.Basis (Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.1.1 k) ℂ
      (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  Module.Basis.mk (linearIndependent_levelRaise N k) (top_le_span_range_levelRaise N k)

/-- The basis vector of `Newform.levelRaiseBasis` at `⟨(M, d), g⟩` is `V_d g`. -/
@[simp]
theorem levelRaiseBasis_apply [NeZero N]
    (x : Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.1.1 k) :
    levelRaiseBasis N k x =
      CuspForm.levelRaise x.1.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd x.1.2)
        x.2.toCuspForm := by
  simp [levelRaiseBasis]

/-! ### Fixed-nebentypus basis -/

/-- A level-raised newform whose nebentypus pulls back to `χ`, as an element of `S_k(N, χ)`. -/
private noncomputable def toLevelRaiseCharSpace (χ : (ZMod N)ˣ →* ℂˣ)
    (x : {x : Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.1.1 k //
      x.2.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd x.1.2)) = χ}) :
    cuspFormCharSpace k χ :=
  ⟨CuspForm.levelRaise x.1.1.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd x.1.1.2) x.1.2.toCuspForm, by
    have hmem :=
      CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd x.1.1.2 x.1.2.χ x.1.2.mem_charSpace
    rwa [x.2] at hmem⟩

private theorem linearIndependent_toLevelRaiseCharSpace [NeZero N] (χ : (ZMod N)ˣ →* ℂˣ) :
    LinearIndependent ℂ (toLevelRaiseCharSpace (N := N) (k := k) χ) :=
  LinearIndependent.of_comp (cuspFormCharSpace k χ).subtype
    ((linearIndependent_levelRaise N k).comp
      (fun x : {x : Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.1.1 k //
        x.2.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd x.1.2)) = χ} ↦ x.1)
      Subtype.val_injective)

private theorem top_le_span_range_toLevelRaiseCharSpace [NeZero N] (χ : (ZMod N)ˣ →* ℂˣ) :
    ⊤ ≤ Submodule.span ℂ (Set.range (toLevelRaiseCharSpace (N := N) (k := k) χ)) := by
  classical
  rw [top_le_iff, ← Submodule.span_val_image_eq_iff, ← Set.range_comp]
  have hrange : Set.range (Subtype.val ∘ toLevelRaiseCharSpace (N := N) (k := k) χ) =
      levelRaiseBasis N k '' {x | x.2.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd x.1.2)) = χ} := by
    ext g
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨x, hx, by simp [toLevelRaiseCharSpace]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, by simp [toLevelRaiseCharSpace]⟩
  rw [hrange]
  -- Split `levelRaiseBasis N k` along the nebentypus map `w`: each `ψ`-fiber span lies in
  -- `cuspFormCharSpace k ψ`, and their supremum is `⊤` while the `cuspFormCharSpace k ψ` are
  -- independent, forcing equality at every `ψ` (in particular at `χ`).
  let w : (Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.1.1 k) → ((ZMod N)ˣ →* ℂˣ) :=
    fun x ↦ x.2.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd x.1.2))
  exact congrFun (((iSupIndep_cuspFormCharSpace k).le_iff_eq_of_iSup_eq_top
    ((levelRaiseBasis N k).isInternal_span_image_fiber w).submodule_iSup_eq_top).mp
    fun ψ ↦ Submodule.span_le.mpr <| by
      rintro _ ⟨x, hx : w x = ψ, rfl⟩
      subst hx
      dsimp only [w]
      rw [levelRaiseBasis_apply, SetLike.mem_coe]
      exact CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd x.1.2 x.2.χ x.2.mem_charSpace) χ

/-- **The level-raised newforms with compatible nebentypus, as a basis of `S_k(N, χ)`**
(Diamond–Shurman, Theorem 5.8.3). -/
noncomputable def levelRaiseBasisCharSpace (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.Basis {x : Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.1.1 k //
      x.2.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd x.1.2)) = χ} ℂ
      (cuspFormCharSpace k χ) :=
  Module.Basis.mk (linearIndependent_toLevelRaiseCharSpace χ)
    (top_le_span_range_toLevelRaiseCharSpace χ)

/-- The basis vector of `Newform.levelRaiseBasisCharSpace` at `⟨⟨(M, d), g⟩, h⟩` is `V_d g`. -/
@[simp]
theorem coe_levelRaiseBasisCharSpace_apply [NeZero N] (χ : (ZMod N)ˣ →* ℂˣ)
    (x : {x : Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.1.1 k //
      x.2.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd x.1.2)) = χ}) :
    (levelRaiseBasisCharSpace N k χ x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      CuspForm.levelRaise x.1.1.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd x.1.1.2)
        x.1.2.toCuspForm := by
  simp [levelRaiseBasisCharSpace, toLevelRaiseCharSpace]

end Newform

end HeckeRing.GL2

namespace TauCeti

open _root_.CuspForm HeckeRing.GL2

variable {N : ℕ} {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-! ### All-divisor direct-sum decomposition of `S_k(Γ₁(N))` -/

private lemma map_levelRaiseₗ_cuspFormsNew_eq_span [NeZero N]
    (p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}) :
    (cuspFormsNew p.1.1 k).map
      (CuspForm.levelRaiseₗ p.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd p.2)) =
      Submodule.span ℂ (Newform.levelRaiseBasis N k '' {x | x.1 = p}) := by
  rw [← Newform.span_range_toCuspForm_eq_cuspFormsNew, Submodule.map_span, ← Set.range_comp]
  congr 1
  ext F
  simp only [Set.mem_range, Function.comp_apply, Set.mem_image, Set.mem_ofPred_eq,
    CuspForm.levelRaiseₗ_apply]
  refine ⟨fun ⟨g, hg⟩ ↦ ⟨⟨p, g⟩, rfl, by simpa using hg⟩, ?_⟩
  rintro ⟨⟨p', g⟩, rfl, hg⟩
  exact ⟨g, by simpa using hg⟩

/-- **All-divisor internal direct-sum decomposition of `S_k(Γ₁(N))`** (Diamond–Shurman,
Theorem 5.8.3): `S_k(Γ₁(N))` is the internal direct sum of the level-raised new subspaces
`V_d(S_k(Γ₁(M))ⁿᵉʷ)` over positive `(M, d)` with `d * M ∣ N`. -/
theorem isInternal_map_levelRaiseₗ_cuspFormsNew (N : ℕ) [NeZero N] (k : ℤ) :
    DirectSum.IsInternal (fun p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N} ↦
      (cuspFormsNew p.1.1 k).map
        (CuspForm.levelRaiseₗ p.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd p.2))) := by
  simpa only [map_levelRaiseₗ_cuspFormsNew_eq_span] using
    (Newform.levelRaiseBasis N k).isInternal_span_image_fiber Sigma.fst

/-- **All-divisor spanning of `S_k(Γ₁(N))`**: the images `V_d(S_k(Γ₁(M))ⁿᵉʷ)` over pairs `(M, d)`
of positive integers with `d * M ∣ N` span `S_k(Γ₁(N))`. -/
theorem iSup_map_levelRaiseₗ_cuspFormsNew_eq_top (N : ℕ) [NeZero N] (k : ℤ) :
    (⨆ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N},
      (cuspFormsNew p.1.1 k).map
        (CuspForm.levelRaiseₗ p.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd p.2))) = ⊤ :=
  (isInternal_map_levelRaiseₗ_cuspFormsNew N k).submodule_iSup_eq_top

/-- **All-divisor independence in `S_k(Γ₁(N))`**: the images `V_d(S_k(Γ₁(M))ⁿᵉʷ)` over pairs
`(M, d)` of positive integers with `d * M ∣ N` are supremum-independent. -/
theorem iSupIndep_map_levelRaiseₗ_cuspFormsNew (N : ℕ) [NeZero N] (k : ℤ) :
    iSupIndep (fun p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N} ↦
      (cuspFormsNew p.1.1 k).map
        (CuspForm.levelRaiseₗ p.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd p.2))) :=
  (isInternal_map_levelRaiseₗ_cuspFormsNew N k).submodule_iSupIndep

/-! ### All-divisor direct-sum decomposition of `S_k(N, χ)` -/

/-- **All-divisor decomposition of `S_k(N, χ)`** (Diamond–Shurman, Theorem 5.8.3; Miyake, §4.6):
the nebentypus space `S_k(N, χ)` is the supremum of `V_d(S_k(M, χ_M)ⁿᵉʷ)` over positive `(M, d)`
with `d * M ∣ N` and `cond(χ) ∣ M`, where `χ_M` is the raise of the primitive character of `χ` to
level `M`. -/
theorem iSup_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace
    (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    (⨆ p : {p : ℕ+ × ℕ+ //
        (p.2 : ℕ) * p.1 ∣ N ∧ DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ p.1},
      (cuspFormsNew p.1.1 k ⊓ cuspFormCharSpace k
        (DirichletCharacter.changeLevel p.2.2
          (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom).map
        (CuspForm.levelRaiseₗ p.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd p.2.1))) =
      cuspFormCharSpace k χ := by
  refine le_antisymm ?_ fun F hFχ ↦ ?_
  · refine iSup_le fun p ↦ ?_
    rintro _ ⟨g, ⟨_, hgχ⟩, rfl⟩
    rw [CuspForm.levelRaiseₗ_apply]
    have hmem := CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd p.2.1 _ hgχ
    rwa [DirichletCharacter.changeLevel_primitiveCharacter_toUnitHom_comp_unitsMap
      (dvd_of_mul_left_dvd p.2.1) p.2.2] at hmem
  · have hspan := (Newform.levelRaiseBasisCharSpace N k χ).span_eq
    have hmem : (⟨F, hFχ⟩ : cuspFormCharSpace k χ) ∈
        Submodule.span ℂ (Set.range (Newform.levelRaiseBasisCharSpace N k χ)) :=
      hspan ▸ Submodule.mem_top
    have hmap := Submodule.mem_map_of_mem (f := (cuspFormCharSpace k χ).subtype) hmem
    rw [Submodule.map_span, ← Set.range_comp] at hmap
    refine Submodule.span_le.mpr ?_ hmap
    rintro _ ⟨x, rfl⟩
    simp only [Function.comp_apply, Submodule.coe_subtype,
      Newform.coe_levelRaiseBasisCharSpace_apply]
    obtain ⟨hc, hψ⟩ := DirichletCharacter.conductor_dvd_and_eq_changeLevel_primitiveCharacter
      (dvd_of_mul_left_dvd x.1.1.2) x.2
    refine Submodule.mem_iSup_of_mem ⟨x.1.1.1, x.1.1.2, hc⟩ ?_
    rw [← CuspForm.levelRaiseₗ_apply]
    exact Submodule.mem_map_of_mem ⟨x.1.2.isNew, hψ ▸ x.1.2.mem_charSpace⟩

/-- **All-divisor independence in `S_k(N, χ)`**: the summands `V_d(S_k(M, χ_M)ⁿᵉʷ)` over positive
`(M, d)` with `d * M ∣ N` and `cond(χ) ∣ M` are supremum-independent. -/
theorem iSupIndep_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace
    (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    iSupIndep
      (fun p : {p : ℕ+ × ℕ+ //
          (p.2 : ℕ) * p.1 ∣ N ∧ DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ p.1} ↦
        (cuspFormsNew p.1.1 k ⊓ cuspFormCharSpace k
          (DirichletCharacter.changeLevel p.2.2
            (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom).map
          (CuspForm.levelRaiseₗ p.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd p.2.1))) :=
  have hind := (iSupIndep_map_levelRaiseₗ_cuspFormsNew N k).comp
    (f := fun p : {p : ℕ+ × ℕ+ //
        (p.2 : ℕ) * p.1 ∣ N ∧ DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ p.1} ↦
      (⟨p.1, p.2.1⟩ : {q : ℕ+ × ℕ+ // (q.2 : ℕ) * q.1 ∣ N}))
    fun _ _ h ↦ Subtype.ext (by simpa using h)
  hind.mono fun _ ↦ Submodule.map_mono inf_le_left

/-- **All-divisor internal direct-sum decomposition inside `S_k(N, χ)`** (Diamond–Shurman,
Theorem 5.8.3): pulled back to submodules of `S_k(N, χ)`, the summands `V_d(S_k(M, χ_M)ⁿᵉʷ)` over
positive `(M, d)` with `d * M ∣ N` and `cond(χ) ∣ M` form an internal direct sum. -/
theorem isInternal_comap_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace
    (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    DirectSum.IsInternal
      (fun p : {p : ℕ+ × ℕ+ //
          (p.2 : ℕ) * p.1 ∣ N ∧ DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ p.1} ↦
        ((cuspFormsNew p.1.1 k ⊓ cuspFormCharSpace k
          (DirichletCharacter.changeLevel p.2.2
            (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom).map
          (CuspForm.levelRaiseₗ p.1.2
            (Gamma1_map_le_conjAct_scaleGL_of_dvd p.2.1))).comap
          (cuspFormCharSpace k χ).subtype) :=
  DirectSum.isInternal_submodule_comap_subtype
    (iSupIndep_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace N k χ)
    (iSup_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace N k χ)

end TauCeti
