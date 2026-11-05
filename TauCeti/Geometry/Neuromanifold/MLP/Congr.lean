/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.MLP.Basic

/-!
# Extensionality of MLP evaluation

An MLP prefix depends only on the weights, biases, and hidden activations below that prefix.
In particular, later activations may change without affecting an earlier prefix. More generally,
two networks with the same widths and the same state at a layer have the same state at a later
layer if their parameters and hidden activations agree between those layers. This comparison
allows the inputs and the earlier parts of the two networks to differ.

The comparison uses a record update of the activations, keeping the widths and hence the
parameter spaces unchanged. The affine and bias-free realization comparisons retain the
linear output-head convention: there is no output activation to compare. The statements include
zero depth and zero widths.

The realization convention follows Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3, equation (2).
The extensionality statements are elementary consequences of layerwise evaluation.
-/

public section

namespace TauCeti.Neuromanifold.MLPSpec

variable {K : Type*} {L : ℕ} [NonUnitalNonAssocSemiring K]

/-- Agreement of two prefix states propagates through an interval of layers on which the
parameters and hidden activations agree. Nothing is required of layers outside the interval. -/
theorem evalPrefix_congr_activation_of_le (A : MLPSpec K L) (σ : Fin (L - 1) → K → K)
    {θ θ' : A.Parameters} {x x' : Fin (A.width 0) → K} {k : Fin (L + 1)}
    (hk : A.evalPrefix θ x k = ({ A with activation := σ } : MLPSpec K L).evalPrefix θ' x' k)
    (i : Fin (L + 1)) (hi : k ≤ i)
    (hθ : ∀ j : Fin L, k ≤ j.castSucc → j.castSucc < i → θ j = θ' j)
    (hσ : ∀ j : Fin (L - 1), k.val ≤ j.val → j.val < i.val → A.activation j = σ j) :
    A.evalPrefix θ x i = ({ A with activation := σ } : MLPSpec K L).evalPrefix θ' x' i := by
  induction i using Fin.induction with
  | zero => rwa [Fin.le_zero_iff.mp hi] at hk
  | succ i ih =>
    rcases hi.lt_or_eq with hlt | rfl
    · have hki : k ≤ i.castSucc := Fin.le_castSucc_iff.mpr hlt
      have ha : A.layerActivation i =
          ({ A with activation := σ } : MLPSpec K L).layerActivation i := by
        by_cases hh : i.val + 1 < L
        · rw [layerActivation_of_lt _ i hh, layerActivation_of_lt _ i hh]
          exact hσ ⟨i.val, by omega⟩ (Fin.le_iff_val_le_val.mp hki) (by simp)
        · rw [layerActivation_of_val_add_one_eq _ i (by omega),
            layerActivation_of_val_add_one_eq _ i (by omega)]
      rw [evalPrefix_succ, evalPrefix_succ, hθ i hki (Fin.castSucc_lt_succ ..), ha,
        ih hki (fun j hj hji => hθ j hj (hji.trans (Fin.castSucc_lt_succ ..)))
          (fun j hj hji => hσ j hj (Nat.lt_trans hji (Nat.lt_succ_self i.val)))]
    · exact hk

/-- Changing parameters and hidden activations above a prefix does not affect that prefix.
The input is fixed; parameters and activations below the prefix may be compared independently. -/
theorem evalPrefix_congr_activation (A : MLPSpec K L) (σ : Fin (L - 1) → K → K)
    {θ θ' : A.Parameters} (x : Fin (A.width 0) → K) (i : Fin (L + 1))
    (hθ : ∀ j : Fin L, j.castSucc < i → θ j = θ' j)
    (hσ : ∀ j : Fin (L - 1), j.val < i.val → A.activation j = σ j) :
    A.evalPrefix θ x i = ({ A with activation := σ } : MLPSpec K L).evalPrefix θ' x i := by
  apply evalPrefix_congr_activation_of_le A σ (by simp) i (Fin.zero_le i)
  · exact fun j _ hj => hθ j hj
  · exact fun j _ hj => hσ j hj

/-- Two affine networks with equal states at a layer realize the same output at the chosen
inputs if their remaining parameters and hidden activations agree. -/
theorem realize_congr_of_prefix (A : MLPSpec K L) (σ : Fin (L - 1) → K → K)
    {θ θ' : A.Parameters} {x x' : Fin (A.width 0) → K} (k : Fin (L + 1))
    (hk : A.evalPrefix θ x k = ({ A with activation := σ } : MLPSpec K L).evalPrefix θ' x' k)
    (hθ : ∀ j : Fin L, k ≤ j.castSucc → θ j = θ' j)
    (hσ : ∀ j : Fin (L - 1), k.val ≤ j.val → A.activation j = σ j) :
    A.realize θ x = ({ A with activation := σ } : MLPSpec K L).realize θ' x' := by
  rw [realize_def, realize_def]
  exact evalPrefix_congr_activation_of_le A σ hk _ (Fin.le_last k)
    (fun j hj _ => hθ j hj) (fun j hj _ => hσ j hj)

/-- The same prefix-state comparison for weight-only networks. There are no auxiliary bias
parameters in either network. -/
theorem realizeWeights_congr_of_prefix (A : MLPSpec K L) (σ : Fin (L - 1) → K → K)
    {w w' : A.Weights} {x x' : Fin (A.width 0) → K} (k : Fin (L + 1))
    (hk : A.evalPrefix (A.zeroBias w) x k =
      ({ A with activation := σ } : MLPSpec K L).evalPrefix
        (({ A with activation := σ } : MLPSpec K L).zeroBias w') x' k)
    (hw : ∀ j : Fin L, k ≤ j.castSucc → w j = w' j)
    (hσ : ∀ j : Fin (L - 1), k.val ≤ j.val → A.activation j = σ j) :
    A.realizeWeights w x = ({ A with activation := σ } : MLPSpec K L).realizeWeights w' x' := by
  rw [realizeWeights_def, realizeWeights_def]
  exact realize_congr_of_prefix A σ k hk (fun j hj => by simp [hw j hj]) hσ

end TauCeti.Neuromanifold.MLPSpec
