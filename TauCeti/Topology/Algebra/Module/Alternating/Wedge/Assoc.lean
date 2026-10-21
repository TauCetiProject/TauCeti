/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Basic
import TauCeti.GroupTheory.Perm.Basic

/-!
# Associativity of topological paired wedges

Paired wedges are associative whenever the two composites of their coefficient pairings agree.
The domain and coefficient spaces need no norms. This permits iterated wedges on tangent fibres
and on general topological vector bundles. Joint continuity of each pairing is stated explicitly;
separate continuity alone does not suffice.

The iterated evaluation formulas flatten the nested alternatizations into a single signed
permutation sum with coefficient `1 / (k! l! m!)`. They use signed-sum reindexing for the nested
alternatizations.
The normalization follows John M. Lee, *Introduction to Smooth Manifolds*, second edition,
Chapter 14.
-/

public section

namespace ContinuousAlternatingMap

open Equiv TauCeti

variable {E F₁ F₂ F₃ F₁₂ F₂₃ G : Type*}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F₁] [Module ℝ F₁] [TopologicalSpace F₁]
  [AddCommGroup F₂] [Module ℝ F₂] [TopologicalSpace F₂]
  [AddCommGroup F₃] [Module ℝ F₃] [TopologicalSpace F₃]
  [AddCommGroup F₁₂] [Module ℝ F₁₂] [TopologicalSpace F₁₂]
  [IsTopologicalAddGroup F₁₂] [ContinuousSMul ℝ F₁₂]
  [AddCommGroup F₂₃] [Module ℝ F₂₃] [TopologicalSpace F₂₃]
  [IsTopologicalAddGroup F₂₃] [ContinuousSMul ℝ F₂₃]
  [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G]
  {k l m : ℕ}

/-- A paired wedge whose left factor is itself a paired wedge is the signed sum over all
permutations of `k + l + m` slots, divided by `k! l! m!`. -/
theorem pairedWedge_pairedWedge_left_apply (mu₁₂ : F₁ →L[ℝ] F₂ →L[ℝ] F₁₂)
    (mu₁₂₃ : F₁₂ →L[ℝ] F₃ →L[ℝ] G)
    (h₁₂ : Continuous (Function.uncurry fun x y ↦ mu₁₂ x y))
    (h₁₂₃ : Continuous (Function.uncurry fun x y ↦ mu₁₂₃ x y))
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂)
    (chi : E [⋀^Fin m]→L[ℝ] F₃) (v : Fin (k + l + m) → E) :
    pairedWedge mu₁₂₃ h₁₂₃ (pairedWedge mu₁₂ h₁₂ phi psi) chi v =
      ((k.factorial : ℝ) * l.factorial * m.factorial)⁻¹ •
        ∑ sigma : Perm (Fin (k + l + m)), Perm.sign sigma •
          mu₁₂₃ (mu₁₂ (phi fun i => v (sigma (Fin.castAdd m (Fin.castAdd l i))))
              (psi fun j => v (sigma (Fin.castAdd m (Fin.natAdd k j)))))
            (chi fun r => v (sigma (Fin.natAdd (k + l) r))) := by
  have key := sum_sign_smul_sum_sign_smul_eq_card_nsmul
    (fun tau => finSumFinEquiv.permCongr (Perm.sumCongr tau (1 : Perm (Fin m))))
    (fun tau => by simp [Perm.sign_sumCongr])
    (fun sigma : Perm (Fin (k + l + m)) =>
      mu₁₂₃ (mu₁₂ (phi fun i => v (sigma (Fin.castAdd m (Fin.castAdd l i))))
          (psi fun j => v (sigma (Fin.castAdd m (Fin.natAdd k j)))))
        (chi fun r => v (sigma (Fin.natAdd (k + l) r))))
  simp only [Perm.mul_apply, permCongr_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Perm.coe_one, id,
    Fintype.card_perm, Fintype.card_fin] at key
  simp only [pairedWedge_apply, map_smul, _root_.map_sum, _root_.smul_apply,
    FunLike.coe_sum, Finset.sum_apply, Units.smul_def, _root_.map_zsmul] at key ⊢
  simp_rw [smul_comm _ ((k.factorial : ℝ) * l.factorial)⁻¹, ← Finset.smul_sum, key, smul_smul,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  have : ((k + l).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- A paired wedge whose right factor is itself a paired wedge is the signed sum over all
permutations of `k + (l + m)` slots, divided by `k! l! m!`. -/
theorem pairedWedge_pairedWedge_right_apply (mu₂₃ : F₂ →L[ℝ] F₃ →L[ℝ] F₂₃)
    (mu₁₂₃' : F₁ →L[ℝ] F₂₃ →L[ℝ] G)
    (h₂₃ : Continuous (Function.uncurry fun x y ↦ mu₂₃ x y))
    (h₁₂₃' : Continuous (Function.uncurry fun x y ↦ mu₁₂₃' x y))
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂)
    (chi : E [⋀^Fin m]→L[ℝ] F₃) (v : Fin (k + (l + m)) → E) :
    pairedWedge mu₁₂₃' h₁₂₃' phi (pairedWedge mu₂₃ h₂₃ psi chi) v =
      ((k.factorial : ℝ) * l.factorial * m.factorial)⁻¹ •
        ∑ sigma : Perm (Fin (k + (l + m))), Perm.sign sigma •
          mu₁₂₃' (phi fun i => v (sigma (Fin.castAdd (l + m) i)))
            (mu₂₃ (psi fun j => v (sigma (Fin.natAdd k (Fin.castAdd m j))))
              (chi fun r => v (sigma (Fin.natAdd k (Fin.natAdd l r))))) := by
  have key := sum_sign_smul_sum_sign_smul_eq_card_nsmul
    (fun tau => finSumFinEquiv.permCongr (Perm.sumCongr (1 : Perm (Fin k)) tau))
    (fun tau => by simp [Perm.sign_sumCongr])
    (fun sigma : Perm (Fin (k + (l + m))) =>
      mu₁₂₃' (phi fun i => v (sigma (Fin.castAdd (l + m) i)))
        (mu₂₃ (psi fun j => v (sigma (Fin.natAdd k (Fin.castAdd m j))))
          (chi fun r => v (sigma (Fin.natAdd k (Fin.natAdd l r))))))
  simp only [Perm.mul_apply, permCongr_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Perm.coe_one, id,
    Fintype.card_perm, Fintype.card_fin] at key
  simp only [pairedWedge_apply, map_smul, _root_.map_sum, Units.smul_def, _root_.map_zsmul] at key ⊢
  simp_rw [smul_comm _ ((l.factorial : ℝ) * m.factorial)⁻¹, ← Finset.smul_sum, key, smul_smul,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  have : ((l + m).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- Associativity of the paired wedge, for pairings whose two composites agree:
`mu₁₂₃ (mu₁₂ a b) c = mu₁₂₃' a (mu₂₃ b c)`. For the multiplication of a normed algebra this
hypothesis is `mul_assoc`; for a Lie bracket it does not hold in general. -/
theorem pairedWedge_assoc (mu₁₂ : F₁ →L[ℝ] F₂ →L[ℝ] F₁₂) (mu₁₂₃ : F₁₂ →L[ℝ] F₃ →L[ℝ] G)
    (mu₂₃ : F₂ →L[ℝ] F₃ →L[ℝ] F₂₃) (mu₁₂₃' : F₁ →L[ℝ] F₂₃ →L[ℝ] G)
    (h₁₂ : Continuous (Function.uncurry fun x y ↦ mu₁₂ x y))
    (h₁₂₃ : Continuous (Function.uncurry fun x y ↦ mu₁₂₃ x y))
    (h₂₃ : Continuous (Function.uncurry fun x y ↦ mu₂₃ x y))
    (h₁₂₃' : Continuous (Function.uncurry fun x y ↦ mu₁₂₃' x y))
    (h : ∀ a b c, mu₁₂₃ (mu₁₂ a b) c = mu₁₂₃' a (mu₂₃ b c))
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) (chi : E [⋀^Fin m]→L[ℝ] F₃)
    (v : Fin (k + l + m) → E) :
    pairedWedge mu₁₂₃ h₁₂₃ (pairedWedge mu₁₂ h₁₂ phi psi) chi v =
      pairedWedge mu₁₂₃' h₁₂₃' phi (pairedWedge mu₂₃ h₂₃ psi chi)
        (v ∘ Fin.cast (Nat.add_assoc k l m).symm) := by
  rw [pairedWedge_pairedWedge_left_apply, pairedWedge_pairedWedge_right_apply]
  congr 1
  refine Fintype.sum_equiv (finCongr (Nat.add_assoc k l m)).permCongr _ _ fun sigma => ?_
  have h₁ (i : Fin k) : Fin.cast (Nat.add_assoc k l m).symm (Fin.castAdd (l + m) i) =
      Fin.castAdd m (Fin.castAdd l i) := Fin.ext rfl
  have h₂ (j : Fin l) : Fin.cast (Nat.add_assoc k l m).symm (Fin.natAdd k (Fin.castAdd m j)) =
      Fin.castAdd m (Fin.natAdd k j) := Fin.ext rfl
  have h₃ (r : Fin m) : Fin.cast (Nat.add_assoc k l m).symm (Fin.natAdd k (Fin.natAdd l r)) =
      Fin.natAdd (k + l) r := Fin.ext (Nat.add_assoc k l r).symm
  simp [h, h₁, h₂, h₃, Perm.sign_permCongr]

end ContinuousAlternatingMap
