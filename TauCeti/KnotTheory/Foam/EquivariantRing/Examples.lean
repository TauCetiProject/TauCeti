/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Foam.EquivariantRing.Idempotent
import Mathlib.Tactic.FinCases
import TauCeti.Algebra.Category.GradedModuleCat.Free.Coordinates
import TauCeti.Algebra.Category.GradedModuleCat.Free.Range
import TauCeti.LinearAlgebra.Pi

/-!
# Concrete examples for equivariant foam ring idempotents

Four concrete checks exercising `TauCeti.EquivariantRing.exists_homogeneous_basis_range_idempotent`,
`TauCeti.GradedModuleCat.basisOfApplyEqSmul`, and
`TauCeti.GradedModuleCat.multiset_map_eq_singleton_of_homogeneous_basis_range` on zero,
identity, diagonal, and off-diagonal degree-zero idempotents over `EquivariantRing N`.
-/

public section

namespace TauCeti.EquivariantRing.Examples

/-- Zero idempotent: the homogeneous basis produced has rank `0`. -/
theorem exists_homogeneous_basis_zero_rank (N m : ℕ) (s : Fin m → ℤ) :
    ∃ (b : Module.Basis (Fin 0) (EquivariantRing N)
        (LinearMap.range
          (0 : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N] (Fin m → EquivariantRing N))))
      (d : Fin 0 → ℤ),
      ∀ i j, (b i).val j ∈ EquivariantRing.grading N (d i - s j) := by
  obtain ⟨n, b, d, hb⟩ := exists_homogeneous_basis_range_idempotent N m s 0 (by ext; simp)
    (fun _ _ _ _ ↦ Submodule.zero_mem _)
  have : Subsingleton (LinearMap.range
      (0 : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N] (Fin m → EquivariantRing N))) := by
    rw [LinearMap.range_zero]
    infer_instance
  have : IsEmpty (Fin n) := (linearIndependent_subsingleton_iff _).mp b.linearIndependent
  obtain rfl : n = 0 := by simpa only [Fintype.card_fin] using Fintype.card_eq_zero (α := Fin n)
  exact ⟨b, d, hb⟩

/-- Identity on a single summand of shift `3`: there exists a homogeneous basis of the range with
degree multiset `{3}`. -/
theorem id_shift_three_degree (N : ℕ) :
    ∃ (n : ℕ)
      (b : Module.Basis (Fin n) (EquivariantRing N)
        (LinearMap.range (LinearMap.id :
          (Fin 1 → EquivariantRing N) →ₗ[EquivariantRing N] (Fin 1 → EquivariantRing N))))
      (d : Fin n → ℤ),
      (∀ i j, (b i).val j ∈ EquivariantRing.grading N (d i - (fun _ ↦ 3) j)) ∧
      Multiset.map d Finset.univ.val = {3} := by
  have hw : ∀ j : Fin 1, (fun _ : Fin 1 ↦ (1 : EquivariantRing N)) j ∈
      EquivariantRing.grading N (3 - 3) := fun _ ↦ by
    simpa using EquivariantRing.C_mem_grading_zero N 1
  obtain ⟨n, b, d, hb⟩ := exists_homogeneous_basis_range_idempotent N 1 (fun _ ↦ 3) LinearMap.id
    (LinearMap.comp_id _) (fun _ _ hv j ↦ hv j)
  refine ⟨n, b, d, hb, GradedModuleCat.multiset_map_eq_singleton_of_homogeneous_basis_range
    (fun _ ↦ EquivariantRing.grading_eq_bot_of_lt_zero N)
    (fun _ hx ↦ EquivariantRing.grading_zero_eq_range N ▸ hx)
    (fun _ ↦ 3) 0 (w := fun _ ↦ 1) (fun v ↦ funext fun j ↦ ?_) rfl hw b d hb⟩
  rw [Fin.eq_zero j]
  simp

/-- Diagonal projection `diag(1, 0)` on shifts `![a, b]`: there exists a `Fin 1` homogeneous basis
of the range whose sole vector is `![1, 0]`, with degree multiset `{a}`, independent of `b`. -/
theorem diag_one_zero_degree (N : ℕ) (a b : ℤ) :
    let proj₀ : (Fin 2 → EquivariantRing N) →ₗ[EquivariantRing N] EquivariantRing N :=
      LinearMap.proj 0
    let p := (LinearMap.toSpanSingleton (EquivariantRing N)
      (Fin 2 → EquivariantRing N) ![1, 0]).comp proj₀
    ∃ (basis : Module.Basis (Fin 1) (EquivariantRing N) (LinearMap.range p))
      (d : Fin 1 → ℤ),
      (basis 0).val = ![1, 0] ∧
      (∀ i j, (basis i).val j ∈ EquivariantRing.grading N (d i - ![a, b] j)) ∧
      Multiset.map d Finset.univ.val = {a} := by
  intro proj₀ p
  have hw : ∀ j : Fin 2, (![1, 0] : Fin 2 → EquivariantRing N) j ∈
      EquivariantRing.grading N (![a, b] 0 - ![a, b] j) := by
    intro j
    fin_cases j
    · simpa using EquivariantRing.C_mem_grading_zero N 1
    · simp
  have hp_eq : ∀ v, p v = v 0 • ![1, 0] := fun _ ↦ rfl
  let basis := GradedModuleCat.basisOfApplyEqSmul (p := p) (0 : Fin 2) hp_eq rfl
  have hb : ∀ (i : Fin 1) (j : Fin 2), (basis i).val j ∈
      EquivariantRing.grading N ((fun _ : Fin 1 ↦ a) i - ![a, b] j) := fun i j ↦ by
    dsimp only [basis]
    rw [GradedModuleCat.coe_basisOfApplyEqSmul_apply (0 : Fin 2) hp_eq rfl]
    exact hw j
  exact ⟨basis, fun _ ↦ a, GradedModuleCat.coe_basisOfApplyEqSmul_apply _ hp_eq rfl 0, hb,
    GradedModuleCat.multiset_map_eq_singleton_of_homogeneous_basis_range
      (fun _ ↦ EquivariantRing.grading_eq_bot_of_lt_zero N)
      (fun _ hx ↦ EquivariantRing.grading_zero_eq_range N ▸ hx)
      ![a, b] 0 hp_eq rfl hw basis (fun _ ↦ a) hb⟩

/-- Off-diagonal projection `p(x, y) = (x, e₁ x)` on shifts `![2, 0]` for `N + 1 ≥ 1`: `p` is
idempotent and its range admits a `Fin 1` homogeneous basis whose sole vector is `![1, X 0]` of
degree `2` (degree multiset `{2}`), exercising the shift sign `2 - 0 = 2`. -/
theorem e1_offDiag_degree (N : ℕ) :
    let proj₀ : (Fin 2 → EquivariantRing (N + 1)) →ₗ[EquivariantRing (N + 1)]
      EquivariantRing (N + 1) := LinearMap.proj 0
    let w : Fin 2 → EquivariantRing (N + 1) := ![1, MvPolynomial.X 0]
    let p := (LinearMap.toSpanSingleton (EquivariantRing (N + 1))
      (Fin 2 → EquivariantRing (N + 1)) w).comp proj₀
    p.comp p = p ∧
    (∃ (basis : Module.Basis (Fin 1) (EquivariantRing (N + 1)) (LinearMap.range p))
      (d : Fin 1 → ℤ),
      (basis 0).val = w ∧
      (∀ i j, (basis i).val j ∈ EquivariantRing.grading (N + 1) (d i - ![2, 0] j)) ∧
      Multiset.map d Finset.univ.val = {2}) := by
  intro proj₀ w p
  have hw : ∀ j : Fin 2, w j ∈ EquivariantRing.grading (N + 1) (![2, 0] 0 - ![2, 0] j) := by
    intro j
    fin_cases j
    · simpa [w] using EquivariantRing.C_mem_grading_zero (N + 1) 1
    · simpa [w] using EquivariantRing.X_mem_grading (N + 1) 0
  have hp_eq : ∀ v, p v = v 0 • w := fun _ ↦ rfl
  have hp : p.comp p = p := idempotent_of_apply_eq_smul (0 : Fin 2) (w := w) hp_eq rfl
  let basis := GradedModuleCat.basisOfApplyEqSmul (p := p) (0 : Fin 2) hp_eq rfl
  have hb : ∀ (i : Fin 1) (j : Fin 2), (basis i).val j ∈
      EquivariantRing.grading (N + 1) ((fun _ : Fin 1 ↦ (2 : ℤ)) i - ![2, 0] j) := fun i j ↦ by
    dsimp only [basis]
    rw [GradedModuleCat.coe_basisOfApplyEqSmul_apply (0 : Fin 2) hp_eq rfl]
    exact hw j
  exact ⟨hp, basis, fun _ ↦ 2, GradedModuleCat.coe_basisOfApplyEqSmul_apply _ hp_eq rfl 0, hb,
    GradedModuleCat.multiset_map_eq_singleton_of_homogeneous_basis_range
      (fun _ ↦ EquivariantRing.grading_eq_bot_of_lt_zero (N + 1))
      (fun _ hx ↦ EquivariantRing.grading_zero_eq_range (N + 1) ▸ hx)
      ![2, 0] 0 hp_eq rfl hw basis (fun _ ↦ 2) hb⟩

end TauCeti.EquivariantRing.Examples
