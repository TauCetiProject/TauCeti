/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Dense
public import TauCeti.Geometry.Neuromanifold.MLP.Basic

/-!
# Parameter coordinates of MLPs

For an MLP specification `A`, the affine parameters are indexed by the finite type
`A.ParameterIndex`: for each layer `i : Fin L`, one index for each entry of the weight matrix
`Wᵢ₊₁` and one for each coordinate of the bias `bᵢ₊₁`. The bias-free parameters are indexed by
`A.WeightIndex`, the matrix entries alone. The equivalences `MLPSpec.parameterEquiv` and
`MLPSpec.weightEquiv` reassemble the parameter tuples from these coordinates, layer by layer
through `denseParameterEquiv` and `linearParameterEquiv`. The index types are finite, with
`∑ i, (dᵢ₊₁ dᵢ + dᵢ₊₁)` and `∑ i, dᵢ₊₁ dᵢ` elements, so `Fintype.equivFin` numbers them as
`Fin p` for that count `p`.
-/

public section

namespace TauCeti.Neuromanifold

namespace MLPSpec

variable {K : Type*} {L : ℕ}

/-- The coordinates of the affine parameters of `A`: for the layer at `i`, a matrix position
`(o, j)` of `Wᵢ₊₁` or an output coordinate `o` of `bᵢ₊₁`. -/
abbrev ParameterIndex (A : MLPSpec K L) : Type :=
  Σ i : Fin L, Fin (A.width i.succ) × Fin (A.width i.castSucc) ⊕ Fin (A.width i.succ)

/-- The coordinates of the bias-free parameters of `A`: for the layer at `i`, a matrix position
`(o, j)` of `Wᵢ₊₁`. -/
abbrev WeightIndex (A : MLPSpec K L) : Type :=
  Σ i : Fin L, Fin (A.width i.succ) × Fin (A.width i.castSucc)

/-- The number of affine parameters of `A`: the sizes of all weight matrices and biases. -/
theorem card_parameterIndex (A : MLPSpec K L) :
    Fintype.card A.ParameterIndex =
      ∑ i : Fin L, (A.width i.succ * A.width i.castSucc + A.width i.succ) := by
  simp

/-- The number of bias-free parameters of `A`: the sizes of all weight matrices. -/
theorem card_weightIndex (A : MLPSpec K L) :
    Fintype.card A.WeightIndex = ∑ i : Fin L, A.width i.succ * A.width i.castSucc := by
  simp

/-- The affine parameters of `A`, read off from their coordinates layer by layer. -/
def parameterEquiv (A : MLPSpec K L) : (A.ParameterIndex → K) ≃ A.Parameters :=
  (Equiv.piCurry fun _ _ => K).trans (Equiv.piCongrRight fun _ => denseParameterEquiv K _ _)

/-- The bias-free parameters of `A`, read off from their coordinates layer by layer. -/
def weightEquiv (A : MLPSpec K L) : (A.WeightIndex → K) ≃ A.Weights :=
  (Equiv.piCurry fun _ _ => K).trans (Equiv.piCongrRight fun _ => linearParameterEquiv K _ _)

/-- The weight matrices read off from affine parameter coordinates. -/
@[simp] theorem parameterEquiv_apply_fst (A : MLPSpec K L) (v : A.ParameterIndex → K)
    (i : Fin L) (o : Fin (A.width i.succ)) (j : Fin (A.width i.castSucc)) :
    (A.parameterEquiv v i).1 o j = v ⟨i, .inl (o, j)⟩ := by
  simp [parameterEquiv, Sigma.curry]

/-- The biases read off from affine parameter coordinates. -/
@[simp] theorem parameterEquiv_apply_snd (A : MLPSpec K L) (v : A.ParameterIndex → K)
    (i : Fin L) (o : Fin (A.width i.succ)) :
    (A.parameterEquiv v i).2 o = v ⟨i, .inr o⟩ := by
  simp [parameterEquiv, Sigma.curry]

/-- The affine parameter coordinate at a matrix position is the corresponding weight. -/
@[simp] theorem parameterEquiv_symm_apply_inl (A : MLPSpec K L) (θ : A.Parameters) (i : Fin L)
    (o : Fin (A.width i.succ)) (j : Fin (A.width i.castSucc)) :
    A.parameterEquiv.symm θ ⟨i, .inl (o, j)⟩ = (θ i).1 o j := by
  simp [parameterEquiv, Sigma.uncurry]

/-- The affine parameter coordinate at a bias position is the corresponding bias. -/
@[simp] theorem parameterEquiv_symm_apply_inr (A : MLPSpec K L) (θ : A.Parameters) (i : Fin L)
    (o : Fin (A.width i.succ)) :
    A.parameterEquiv.symm θ ⟨i, .inr o⟩ = (θ i).2 o := by
  simp [parameterEquiv, Sigma.uncurry]

/-- The weight matrices read off from bias-free parameter coordinates. -/
@[simp] theorem weightEquiv_apply (A : MLPSpec K L) (v : A.WeightIndex → K) (i : Fin L)
    (o : Fin (A.width i.succ)) (j : Fin (A.width i.castSucc)) :
    A.weightEquiv v i o j = v ⟨i, (o, j)⟩ := by
  simp [weightEquiv, Sigma.curry]

/-- The bias-free parameter coordinate at a matrix position is the corresponding weight. -/
@[simp] theorem weightEquiv_symm_apply (A : MLPSpec K L) (w : A.Weights) (i : Fin L)
    (o : Fin (A.width i.succ)) (j : Fin (A.width i.castSucc)) :
    A.weightEquiv.symm w ⟨i, (o, j)⟩ = w i o j := by
  simp [weightEquiv, Sigma.uncurry]

end MLPSpec

end TauCeti.Neuromanifold
