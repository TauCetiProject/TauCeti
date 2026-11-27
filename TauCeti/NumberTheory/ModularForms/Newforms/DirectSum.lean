/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.Decomposition
import TauCeti.Algebra.DirectSum.Internal
import TauCeti.LinearAlgebra.LinearIndependent.Basic

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

*Linear independence.* Within a single `(M, g)` fiber, the forms `V_d g` at distinct positive `d`
are linearly independent by `q`-expansion (`CuspForm.linearIndependent_levelRaise`). At a fixed
nebentypus `χ` modulo `N`, strong multiplicity one across divisor levels makes the good-prime Hecke
eigenvalue systems injective (`HeckeRing.GL2.Newform.eigenvalue_injective_of_comp_unitsMap_eq`), so
gluing along the independent joint eigenspaces (`TauCeti.iSupIndep_iInf_eigenspace`) via
`TauCeti.linearIndependent_sigma_of_iSupIndep` proves fixed-character linear independence
(`HeckeRing.GL2.Newform.linearIndependent_levelRaise_of_comp_unitsMap_eq`). Gluing once more across
the independent nebentypus spaces (`TauCeti.iSupIndep_cuspFormCharSpace`) gives full linear
independence (`HeckeRing.GL2.Newform.linearIndependent_levelRaise`).

## Main definitions

* `HeckeRing.GL2.Newform.levelRaiseBasis N k`: the basis of `S_k(Γ₁(N))` indexed by
  `Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.val.1 k`, sending `⟨(M, d), g⟩` to `V_d g`.
* `HeckeRing.GL2.Newform.levelRaiseBasisCharSpace N k χ`: the basis of `S_k(N, χ)` formed by the
  level-raised newforms `V_d g` whose nebentypus `g.χ` pulls back to `χ` modulo `N`.

## Main results

* `HeckeRing.GL2.Newform.linearIndependent_levelRaise_of_comp_unitsMap_eq`,
  `HeckeRing.GL2.Newform.linearIndependent_levelRaise`: the level-raised newforms `V_d g` with
  `d * M ∣ N` are `ℂ`-linearly independent at a fixed nebentypus `χ` and across all nebentypes in
  `S_k(Γ₁(N))`.
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

/-- **Linear independence of the level-raised newforms at a fixed nebentypus** (Diamond–Shurman,
Theorem 5.8.3). For a character `χ` modulo `N`, the level-raises `V_d g` over pairs `p = (M, d)` of
positive integers with `d * M ∣ N` and newforms `g` of level `M` whose nebentypus pulls back to `χ`
are `ℂ`-linearly independent in `S_k(Γ₁(N))`. -/
theorem linearIndependent_levelRaise_of_comp_unitsMap_eq (N : ℕ) [NeZero N] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    LinearIndependent ℂ
      (fun x : {x : Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.val.1 k //
          x.2.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd x.1.property)) = χ} ↦
        CuspForm.levelRaise x.val.1.val.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd x.val.1.property)
          x.val.2.toCuspForm) := by
  let P := {q : ℕ // q.Prime ∧ Nat.Coprime q N}
  let T : P → Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := fun q ↦
    heckeTCuspNat k q.val (_hn := ⟨q.property.1.ne_zero⟩)
  let η := Σ M : {M : ℕ+ // (M : ℕ) ∣ N},
    {g : Newform M.val k // g.χ.comp (ZMod.unitsMap M.property) = χ}
  let fam : ∀ mg : η, {d : ℕ+ // (d : ℕ) * mg.1.val ∣ N} →
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k := fun mg d ↦
    CuspForm.levelRaise d.val (Gamma1_map_le_conjAct_scaleGL_of_dvd d.property) mg.2.val.toCuspForm
  have hli_sigma := TauCeti.linearIndependent_sigma_of_iSupIndep (f := fam)
    (fun mg ↦ _root_.CuspForm.linearIndependent_levelRaise (one_mem_strictPeriods_Gamma1_map _)
      (d := fun d : {d : ℕ+ // (d : ℕ) * mg.1.val ∣ N} ↦ (d.val : ℕ))
      (fun _ _ h ↦ Subtype.ext (PNat.eq h))
      (fun d ↦ Gamma1_map_le_conjAct_scaleGL_of_dvd d.property) mg.2.val.ne_zero)
    ((iSupIndep_iInf_eigenspace T).comp (eigenvalue_injective_of_comp_unitsMap_eq N k χ))
    fun mg d ↦ by
      rw [Function.comp_apply, Submodule.mem_iInf]
      exact fun q ↦ Module.End.mem_eigenspace_iff.mpr
        (mg.2.val.heckeTCuspNat_levelRaise_eq_eigenvalue_smul d.property q.property.1 q.property.2)
  let reindex :
      {x : Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.val.1 k //
        x.2.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd x.1.property)) = χ} ≃
      Σ mg : η, {d : ℕ+ // (d : ℕ) * mg.1.val ∣ N} :=
    { toFun := fun x ↦
        ⟨⟨⟨x.val.1.val.1, dvd_of_mul_left_dvd x.val.1.property⟩, ⟨x.val.2, x.property⟩⟩,
          ⟨x.val.1.val.2, x.val.1.property⟩⟩
      invFun := fun y ↦ ⟨⟨⟨(y.1.1.val, y.2.val), y.2.property⟩, y.1.2.val⟩, y.1.2.property⟩
      left_inv := fun ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩ ↦ rfl
      right_inv := fun ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩ ↦ rfl }
  exact hli_sigma.comp reindex reindex.injective

/-- **The level-raised newforms are linearly independent** (Diamond–Shurman, Theorem 5.8.3):
as `p = (M, d)` ranges over pairs of positive integers with `d * M ∣ N` and `g` over `Newform M k`,
the cusp forms `V_d g` in `S_k(Γ₁(N))` are `ℂ`-linearly independent. -/
theorem linearIndependent_levelRaise (N : ℕ) [NeZero N] (k : ℤ) :
    LinearIndependent ℂ
      (fun x : Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.val.1 k ↦
        CuspForm.levelRaise x.1.val.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd x.1.property)
          x.2.toCuspForm) := by
  let v : (Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.val.1 k) →
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k := fun x ↦
    CuspForm.levelRaise x.1.val.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd x.1.property) x.2.toCuspForm
  let w : (Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.val.1 k) → ((ZMod N)ˣ →* ℂˣ) :=
    fun x ↦ x.2.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd x.1.property))
  have hli_sigma := TauCeti.linearIndependent_sigma_of_iSupIndep
    (W := cuspFormCharSpace (N := N) k)
    (fun χ ↦ linearIndependent_levelRaise_of_comp_unitsMap_eq N k χ)
    (iSupIndep_cuspFormCharSpace k)
    fun χ x ↦ by
      have hmem := CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd x.val.1.property x.val.2.χ
        x.val.2.mem_charSpace
      rwa [x.property] at hmem
  let reindex := (Equiv.sigmaFiberEquiv w).symm
  have h := hli_sigma.comp reindex reindex.injective
  have hcomp : (fun jk : Σ χ, {x // w x = χ} ↦ v jk.2.val) ∘ reindex = v :=
    funext fun x ↦ congrArg v (Equiv.sigmaFiberEquiv_symm_apply_snd_coe w x)
  rwa [hcomp] at h

private theorem top_le_span_range_levelRaise (N : ℕ) [NeZero N] (k : ℤ) :
    ⊤ ≤ Submodule.span ℂ (Set.range
      (fun x : Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.val.1 k ↦
        CuspForm.levelRaise x.1.val.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd x.1.property)
          x.2.toCuspForm)) := by
  rw [← span_levelRaise_eq_top N k]
  refine Submodule.span_mono ?_
  rintro _ ⟨M, d, _, _, h, g, rfl⟩
  exact ⟨⟨⟨(⟨M, NeZero.pos M⟩, ⟨d, NeZero.pos d⟩), h⟩, g⟩, rfl⟩

/-- **The level-raised newforms, as a basis of `S_k(Γ₁(N))`** (Diamond–Shurman, Theorem 5.8.3). -/
noncomputable def levelRaiseBasis (N : ℕ) [NeZero N] (k : ℤ) :
    Module.Basis (Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.val.1 k) ℂ
      (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  Module.Basis.mk (linearIndependent_levelRaise N k) (top_le_span_range_levelRaise N k)

/-- The basis vector of `Newform.levelRaiseBasis` at `⟨(M, d), g⟩` is `V_d g`. -/
@[simp]
theorem levelRaiseBasis_apply [NeZero N]
    (x : Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.val.1 k) :
    levelRaiseBasis N k x =
      CuspForm.levelRaise x.1.val.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd x.1.property)
        x.2.toCuspForm := by
  simp [levelRaiseBasis]

/-! ### Fixed-nebentypus basis -/

/-- A level-raised newform whose nebentypus pulls back to `χ`, as an element of `S_k(N, χ)`. -/
private noncomputable def toLevelRaiseCharSpace (χ : (ZMod N)ˣ →* ℂˣ)
    (x : {x : Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.val.1 k //
      x.2.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd x.1.property)) = χ}) :
    cuspFormCharSpace k χ :=
  ⟨CuspForm.levelRaise x.val.1.val.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd x.val.1.property)
      x.val.2.toCuspForm, by
    have hmem :=
      CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd x.val.1.property x.val.2.χ
          x.val.2.mem_charSpace
    rwa [x.property] at hmem⟩

private theorem linearIndependent_toLevelRaiseCharSpace [NeZero N] (χ : (ZMod N)ˣ →* ℂˣ) :
    LinearIndependent ℂ (toLevelRaiseCharSpace (N := N) (k := k) χ) :=
  LinearIndependent.of_comp (cuspFormCharSpace k χ).subtype
    (linearIndependent_levelRaise_of_comp_unitsMap_eq N k χ)

private theorem top_le_span_range_toLevelRaiseCharSpace [NeZero N] (χ : (ZMod N)ˣ →* ℂˣ) :
    ⊤ ≤ Submodule.span ℂ (Set.range (toLevelRaiseCharSpace (N := N) (k := k) χ)) := by
  classical
  rw [top_le_iff, ← Submodule.span_val_image_eq_iff, ← Set.range_comp]
  have hrange : Set.range (Subtype.val ∘ toLevelRaiseCharSpace (N := N) (k := k) χ) =
      levelRaiseBasis N k '' {x | x.2.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd x.1.property)) = χ}
          := by
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
  let w : (Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.val.1 k) → ((ZMod N)ˣ →* ℂˣ) :=
    fun x ↦ x.2.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd x.1.property))
  exact congrFun (((iSupIndep_cuspFormCharSpace k).le_iff_eq_of_iSup_eq_top
    ((levelRaiseBasis N k).isInternal_span_image_fiber w).submodule_iSup_eq_top).mp
    fun ψ ↦ Submodule.span_le.mpr <| by
      rintro _ ⟨x, hx : w x = ψ, rfl⟩
      subst hx
      dsimp only [w]
      rw [levelRaiseBasis_apply, SetLike.mem_coe]
      exact CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd x.1.property x.2.χ x.2.mem_charSpace) χ

/-- **The level-raised newforms with compatible nebentypus, as a basis of `S_k(N, χ)`**
(Diamond–Shurman, Theorem 5.8.3). -/
noncomputable def levelRaiseBasisCharSpace (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.Basis {x : Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.val.1 k //
      x.2.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd x.1.property)) = χ} ℂ
      (cuspFormCharSpace k χ) :=
  Module.Basis.mk (linearIndependent_toLevelRaiseCharSpace χ)
    (top_le_span_range_toLevelRaiseCharSpace χ)

/-- The basis vector of `Newform.levelRaiseBasisCharSpace` at `⟨⟨(M, d), g⟩, h⟩` is `V_d g`. -/
@[simp]
theorem coe_levelRaiseBasisCharSpace_apply [NeZero N] (χ : (ZMod N)ˣ →* ℂˣ)
    (x : {x : Σ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}, Newform p.val.1 k //
      x.2.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd x.1.property)) = χ}) :
    (levelRaiseBasisCharSpace N k χ x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      CuspForm.levelRaise x.val.1.val.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd x.val.1.property)
        x.val.2.toCuspForm := by
  simp [levelRaiseBasisCharSpace, toLevelRaiseCharSpace]

end Newform

end HeckeRing.GL2

namespace TauCeti

open _root_.CuspForm HeckeRing.GL2

variable {N : ℕ} {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-! ### All-divisor direct-sum decomposition of `S_k(Γ₁(N))` -/

private lemma map_levelRaiseₗ_cuspFormsNew_eq_span [NeZero N]
    (p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N}) :
    (cuspFormsNew p.val.1 k).map
      (CuspForm.levelRaiseₗ p.val.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd p.property)) =
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
      (cuspFormsNew p.val.1 k).map
        (CuspForm.levelRaiseₗ p.val.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd p.property))) := by
  simpa only [map_levelRaiseₗ_cuspFormsNew_eq_span] using
    (Newform.levelRaiseBasis N k).isInternal_span_image_fiber Sigma.fst

/-- **All-divisor spanning of `S_k(Γ₁(N))`**: the images `V_d(S_k(Γ₁(M))ⁿᵉʷ)` over pairs `(M, d)`
of positive integers with `d * M ∣ N` span `S_k(Γ₁(N))`. -/
theorem iSup_map_levelRaiseₗ_cuspFormsNew_eq_top (N : ℕ) [NeZero N] (k : ℤ) :
    (⨆ p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N},
      (cuspFormsNew p.val.1 k).map
        (CuspForm.levelRaiseₗ p.val.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd p.property))) = ⊤ :=
  (isInternal_map_levelRaiseₗ_cuspFormsNew N k).submodule_iSup_eq_top

/-- **All-divisor independence in `S_k(Γ₁(N))`**: the images `V_d(S_k(Γ₁(M))ⁿᵉʷ)` over pairs
`(M, d)` of positive integers with `d * M ∣ N` are supremum-independent. -/
theorem iSupIndep_map_levelRaiseₗ_cuspFormsNew (N : ℕ) [NeZero N] (k : ℤ) :
    iSupIndep (fun p : {p : ℕ+ × ℕ+ // (p.2 : ℕ) * p.1 ∣ N} ↦
      (cuspFormsNew p.val.1 k).map
        (CuspForm.levelRaiseₗ p.val.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd p.property))) :=
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
      (cuspFormsNew p.val.1 k ⊓ cuspFormCharSpace k
        (DirichletCharacter.changeLevel p.property.2
          (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom).map
        (CuspForm.levelRaiseₗ p.val.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd p.property.1))) =
      cuspFormCharSpace k χ := by
  refine le_antisymm ?_ fun F hFχ ↦ ?_
  · refine iSup_le fun p ↦ ?_
    rintro _ ⟨g, ⟨_, hgχ⟩, rfl⟩
    rw [CuspForm.levelRaiseₗ_apply]
    have hmem := CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd p.property.1 _ hgχ
    rwa [DirichletCharacter.changeLevel_primitiveCharacter_toUnitHom_comp_unitsMap
      (dvd_of_mul_left_dvd p.property.1) p.property.2] at hmem
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
    obtain ⟨hc, hψ⟩ :=
      DirichletCharacter.conductor_dvd_and_eq_changeLevel_primitiveCharacter_toUnitHom
        (dvd_of_mul_left_dvd x.val.1.property) x.property
    refine Submodule.mem_iSup_of_mem ⟨x.val.1.val, x.val.1.property, hc⟩ ?_
    rw [← CuspForm.levelRaiseₗ_apply]
    exact Submodule.mem_map_of_mem ⟨x.val.2.isNew, hψ ▸ x.val.2.mem_charSpace⟩

/-- **All-divisor independence in `S_k(N, χ)`**: the summands `V_d(S_k(M, χ_M)ⁿᵉʷ)` over positive
`(M, d)` with `d * M ∣ N` and `cond(χ) ∣ M` are supremum-independent. -/
theorem iSupIndep_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace
    (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    iSupIndep
      (fun p : {p : ℕ+ × ℕ+ //
          (p.2 : ℕ) * p.1 ∣ N ∧ DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ p.1} ↦
        (cuspFormsNew p.val.1 k ⊓ cuspFormCharSpace k
          (DirichletCharacter.changeLevel p.property.2
            (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom).map
          (CuspForm.levelRaiseₗ p.val.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd p.property.1))) :=
  have hind := (iSupIndep_map_levelRaiseₗ_cuspFormsNew N k).comp
    (f := fun p : {p : ℕ+ × ℕ+ //
        (p.2 : ℕ) * p.1 ∣ N ∧ DirichletCharacter.conductor (MulChar.ofUnitHom χ) ∣ p.1} ↦
      (⟨p.val, p.property.1⟩ : {q : ℕ+ × ℕ+ // (q.2 : ℕ) * q.1 ∣ N}))
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
        ((cuspFormsNew p.val.1 k ⊓ cuspFormCharSpace k
          (DirichletCharacter.changeLevel p.property.2
            (DirichletCharacter.primitiveCharacter (MulChar.ofUnitHom χ))).toUnitHom).map
          (CuspForm.levelRaiseₗ p.val.2
            (Gamma1_map_le_conjAct_scaleGL_of_dvd p.property.1))).comap
          (cuspFormCharSpace k χ).subtype) :=
  DirectSum.isInternal_submodule_comap_subtype
    (iSupIndep_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace N k χ)
    (iSup_map_levelRaiseₗ_cuspFormsNew_inf_cuspFormCharSpace N k χ)

end TauCeti
