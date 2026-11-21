/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Modular.Invariants.Basic
import TauCeti.Combinatorics.PermutationTriple.ComputedInvariants
import TauCeti.Combinatorics.PermutationTriple.Decidable
import TauCeti.Combinatorics.PermutationTriple.Mirror

/-!
# Non-completeness of the classical modular invariant vector

A finite-index subgroup of `PSL(2, ℤ)` and its mirror under `conjJAut` share the same invariant
vector `(index, genus, e₂, e₃, cuspWidths)`. Using a chiral permutation triple of degree `7`
which is not equivalent to its mirror, Millington's theorem produces two non-conjugate index-`7`
subgroups sharing `(7, 0, 1, 1, {6, 1})` (`TauCeti.ModularGroup.exists_not_conj_invariants_eq`).
-/

open Equiv Equiv.Perm
open scoped MatrixGroups Pointwise

public section

namespace TauCeti.ModularGroup

open PermutationTriple

private def chiralS : Perm (Fin 7) :=
  Equiv.swap 1 2 * Equiv.swap 3 4 * Equiv.swap 5 6

private def chiralT : Perm (Fin 7) :=
  Equiv.swap 0 2 * Equiv.swap 2 1 * Equiv.swap 1 4 * Equiv.swap 4 6 * Equiv.swap 6 3

private def chiralTriple : PermutationTriple 7 where
  σ0 := (chiralT * chiralS)⁻¹
  σ1 := chiralS
  σinf := chiralT
  product_eq_one := mul_inv_cancel _

private theorem chiralTriple_isConnected : chiralTriple.IsConnected := by decide

private theorem not_equivalent_chiralTriple_mirror :
    ¬ chiralTriple.Equivalent chiralTriple.mirror := by
  intro heq
  obtain ⟨τ, hτ⟩ := equivalent_iff_exists_smul_eq.mp heq
  have h1 : τ * chiralTriple.σ1 * τ⁻¹ = chiralTriple.σ1 := by
    have hinv : chiralTriple.σ1⁻¹ = chiralTriple.σ1 := by decide
    simpa [hinv] using congrArg PermutationTriple.σ1 hτ
  have hinf : τ * chiralTriple.σinf * τ⁻¹ = chiralTriple.σinf⁻¹ := by
    simpa using congrArg PermutationTriple.σinf hτ
  have hcommS (x : Fin 7) : τ (chiralTriple.σ1 x) = chiralTriple.σ1 (τ x) := by
    simpa using congrFun (congrArg DFunLike.coe h1) (τ x)
  have hcommT (x : Fin 7) : τ (chiralTriple.σinf x) = chiralTriple.σinf⁻¹ (τ x) := by
    simpa using congrFun (congrArg DFunLike.coe hinf) (τ x)
  have hτ0 : τ 0 = 0 :=
    (by decide : ∀ x : Fin 7, chiralTriple.σ1 x = x → x = 0) (τ 0)
      (by rw [← hcommS 0, (by decide : chiralTriple.σ1 0 = 0)])
  have hτ2 : τ 2 = 3 := by
    rw [← (by decide : chiralTriple.σinf 0 = 2), hcommT 0, hτ0]; decide
  have hτ1 : τ 1 = 6 := by
    rw [← (by decide : chiralTriple.σinf 2 = 1), hcommT 2, hτ2]; decide
  have h35 : (3 : Fin 7) = 5 := by
    rw [← hτ2, ← (by decide : chiralTriple.σ1 1 = 2), hcommS 1, hτ1]; decide
  exact absurd h35 (by decide)

/-- **Non-completeness of the classical invariant vector.** There exist two non-conjugate
index-`7` subgroups of `PSL(2, ℤ)` — a chiral subgroup and its mirror under `conjJAut` —
sharing the same invariant vector `(7, 0, 1, 1, {6, 1})`. -/
theorem exists_not_conj_invariants_eq :
    ∃ (Γ₁ Γ₂ : Subgroup PSL(2, ℤ)) (e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin 7)
      (e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin 7),
      invariants Γ₁ e₁ = ⟨7, 0, 1, 1, {6, 1}⟩ ∧
      invariants Γ₂ e₂ = ⟨7, 0, 1, 1, {6, 1}⟩ ∧
      ¬ ∃ g : ConjAct PSL(2, ℤ), g • Γ₁ = Γ₂ := by
  obtain ⟨Γ₁, _, e₁, -, heq₁⟩ :=
    exists_modularTriple_equivalent chiralTriple_isConnected (by decide) (by decide)
  let Γ₂ : Subgroup PSL(2, ℤ) := Γ₁.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))
  let e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin 7 :=
    (TauCeti.QuotientGroup.congrOfMapEq conjJAut (rfl : Γ₁.map _ = Γ₂)).symm.trans e₁
  have hinv₁ : invariants Γ₁ e₁ = ⟨7, 0, 1, 1, {6, 1}⟩ := by
    refine Invariants.ext (invariants_index Γ₁ e₁) ?_ ?_ ?_ ?_
    · rw [invariants_genus, genus_def, PermutationTriple.genus_eq_of_equivalent heq₁,
        ← computedGenus_eq]; decide
    · rw [invariants_ellipticTwo, ellipticTwo_eq_count_fullCycleType, fullCycleType_def,
        ← cycleData_σ1, cycleData_eq_of_equivalent heq₁, cycleData_σ1, ← fullCycleType_def,
        ← computedCycleType_eq_fullCycleType]; decide
    · rw [invariants_ellipticThree, ellipticThree_eq_count_fullCycleType, fullCycleType_def,
        ← cycleData_σ0, cycleData_eq_of_equivalent heq₁, cycleData_σ0, ← fullCycleType_def,
        ← computedCycleType_eq_fullCycleType]; decide
    · rw [invariants_cuspWidths, cuspWidths_eq_cycleData, cycleData_eq_of_equivalent heq₁,
        cycleData_σinf, ← fullCycleType_def, ← computedCycleType_eq_fullCycleType]; decide
  refine ⟨Γ₁, Γ₂, e₁, e₂, hinv₁, by rw [invariants_map_conjJAut Γ₁ e₁ e₂, hinv₁], fun hconj ↦ ?_⟩
  refine not_equivalent_chiralTriple_mirror (IsoClass.mk_eq_mk_iff.mp ?_)
  exact (IsoClass.mk_eq_mk_iff.mpr heq₁).symm.trans <|
    (IsoClass.mk_eq_mk_iff.mpr ((millington e₁ e₂).mpr hconj)).trans <|
    (IsoClass.mk_eq_mk_iff.mpr (equivalent_mirror_modularTriple Γ₁ e₁ e₂)).trans
    (IsoClass.mk_eq_mk_iff.mpr heq₁.mirror)

end TauCeti.ModularGroup
