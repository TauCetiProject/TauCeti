/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Basic
import Mathlib.GroupTheory.Perm.Finite

/-!
# Paired wedges on concatenated tuples

The paired wedge `φ ∧ ψ` of a `k`-form and an `l`-form, evaluated on a concatenated tuple
`(a₁, …, a_k, b₁, …, b_l)`, is a normalized sum over all permutations of `k + l` letters. When
`ψ` vanishes on every tuple having one of the `aᵢ` as an entry, only the permutations preserving
the two blocks contribute, each of them the value `μ (φ a) (ψ b)`, so
`(φ ∧ ψ)(a, b) = μ (φ a) (ψ b)`
(`ContinuousAlternatingMap.pairedWedge_apply_append_of_forall`). This is how a wedge of forms
pulled back from the two factors of a product is evaluated on a frame adapted to the product.
-/

public section

open Equiv

namespace ContinuousAlternatingMap

variable {E F₁ F₂ F₃ : Type*}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F₁] [Module ℝ F₁] [TopologicalSpace F₁]
  [AddCommGroup F₂] [Module ℝ F₂] [TopologicalSpace F₂]
  [AddCommGroup F₃] [Module ℝ F₃] [TopologicalSpace F₃]
  [IsTopologicalAddGroup F₃] [ContinuousConstSMul ℝ F₃]
  {k l : ℕ}

/-- **The paired wedge on a concatenated tuple.** If `ψ` vanishes on every tuple one of whose
entries is a vector `a i`, then `(φ ∧ ψ)(a₁, …, a_k, b₁, …, b_l) = μ (φ a) (ψ b)`: only the
permutations preserving the two blocks contribute to the shuffle sum. -/
theorem pairedWedge_apply_append_of_forall (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) (a : Fin k → E) (b : Fin l → E)
    (hψ : ∀ (y : Fin l → E) (i : Fin k) (j : Fin l), ψ (Function.update y j (a i)) = 0) :
    pairedWedge μ hμ φ ψ (Fin.append a b) = μ (φ a) (ψ b) := by
  classical
  let e : Fin k ⊕ Fin l ≃ Fin (k + l) := finSumFinEquiv
  let c : Fin k ⊕ Fin l → E := Sum.elim a b
  have hc (x : Fin k ⊕ Fin l) : Fin.append a b (e x) = c x := by
    rcases x with i | j <;> simp [e, c]
  -- Reindex the shuffle sum by permutations of `Fin k ⊕ Fin l`.
  let g : Perm (Fin k ⊕ Fin l) → F₃ := fun τ ↦
    Perm.sign τ • μ (φ fun i ↦ c (τ (.inl i))) (ψ fun j ↦ c (τ (.inr j)))
  have hreindex : ∑ σ : Perm (Fin (k + l)), Perm.sign σ •
      μ (φ fun i ↦ Fin.append a b (σ (Fin.castAdd l i)))
        (ψ fun j ↦ Fin.append a b (σ (Fin.natAdd k j))) = ∑ τ, g τ := by
    refine (Fintype.sum_equiv (e.permCongr.symm) _ _ fun σ ↦ ?_)
    simp only [g, Perm.sign_permCongr, e.permCongr_symm, Equiv.permCongr_apply, ← hc,
      Equiv.symm_symm, Equiv.apply_symm_apply]
    simp [e]
  -- Permutations exchanging the blocks contribute nothing.
  have hout (τ : Perm (Fin k ⊕ Fin l)) (hτ : τ ∉ Set.range (Perm.sumCongrHom (Fin k) (Fin l))) :
      g τ = 0 := by
    have hmaps : ¬Set.MapsTo τ (Set.range Sum.inr) (Set.range Sum.inr) := fun h ↦
      hτ (Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
        ((Perm.perm_mapsTo_inl_iff_mapsTo_inr τ).2 h))
    obtain ⟨j, hj⟩ : ∃ j, ∀ j', τ (.inr j) ≠ .inr j' := by
      simpa [Set.MapsTo, eq_comm] using hmaps
    obtain ⟨i, hi⟩ : ∃ i, τ (.inr j) = .inl i := by
      rcases h : τ (.inr j) with i | j'
      · exact ⟨i, rfl⟩
      · exact absurd h (hj j')
    have hzero : ψ (fun j' ↦ c (τ (.inr j'))) = 0 := by
      have := hψ (fun j' ↦ c (τ (.inr j'))) i j
      rwa [show a i = c (τ (.inr j)) by simp [hi, c], Function.update_eq_self] at this
    simp [g, hzero]
  -- Each block-preserving permutation contributes `μ (φ a) (ψ b)`.
  have hin (p : Perm (Fin k) × Perm (Fin l)) : μ (φ a) (ψ b) = g (Perm.sumCongrHom _ _ p) := by
    have hφ := φ.toAlternatingMap.map_perm a p.1
    have hψ' := ψ.toAlternatingMap.map_perm b p.2
    simp only [coe_toAlternatingMap] at hφ hψ'
    simp only [g, Perm.sumCongrHom_apply, Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr, c,
      Sum.elim_inl, Sum.elim_inr, Perm.sign_sumCongr]
    rw [show (fun i ↦ a (p.1 i)) = a ∘ p.1 from rfl, show (fun j ↦ b (p.2 j)) = b ∘ p.2 from rfl,
      hφ, hψ']
    rcases Int.units_eq_one_or (Perm.sign p.1) with h₁ | h₁ <;>
      rcases Int.units_eq_one_or (Perm.sign p.2) with h₂ | h₂ <;> simp [h₁, h₂]
  rw [pairedWedge_apply, hreindex, ← Fintype.sum_of_injective _ Perm.sumCongrHom_injective
    (fun _ ↦ μ (φ a) (ψ b)) g hout hin]
  -- The `k! l!` block-preserving permutations cancel the normalization.
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_perm,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  convert one_smul ℝ (μ (φ a) (ψ b))
  push_cast
  field_simp

end ContinuousAlternatingMap
