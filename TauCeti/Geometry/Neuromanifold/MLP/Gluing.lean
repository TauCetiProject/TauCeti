/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.MLP.Append
public import TauCeti.Geometry.Neuromanifold.MLP.Congr

/-!
# Parameters and realization of concatenated MLPs

For two positive-depth specifications `A` and `B` with matching boundary widths,
`appendParameters` and `appendWeights` identify the parameters of `A.append B σ` with the
complete parameter products of `A` and `B`. In particular the weight-only identification
introduces no bias coordinates.

`realize_appendParameters_symm` and `realizeWeights_appendWeights_symm` evaluate joined
parameters directly in the original specifications, rather than in the extracted lower and
upper parts. The junction applies `σ`, and the output head of `B` remains affine, or linear
in the weight-only case. Input, junction, and output index casts only identify finite types
whose widths are equal; they do not change any coordinate value.

The compositional convention follows Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3, equation (2).
-/

public section

namespace TauCeti.Neuromanifold.MLPSpec

variable {K : Type*} {L M : ℕ}
variable (A : MLPSpec K (L + 1)) (B : MLPSpec K (M + 1)) (σ : K → K)

/-- The affine parameters of a concatenation are exactly the parameters of its two factors,
provided their boundary widths match. -/
def appendParameters (h : A.width (Fin.last (L + 1)) = B.width 0) :
    (A.append B σ).Parameters ≃ A.Parameters × B.Parameters :=
  (A.append B σ).splitParameters.trans
    (Equiv.prodCongr (Equiv.cast (congrArg Parameters (lowerLayers_append A B σ h)))
      (Equiv.cast (congrArg Parameters (upperLayers_append A B σ))))

/-- Splitting affine parameters transports the two extracted parts back to the original
specifications. -/
@[simp] theorem appendParameters_apply
    (h : A.width (Fin.last (L + 1)) = B.width 0) (θ : (A.append B σ).Parameters) :
    A.appendParameters B σ h θ =
      (cast (congrArg Parameters (lowerLayers_append A B σ h))
        ((A.append B σ).splitParameters θ).1,
       cast (congrArg Parameters (upperLayers_append A B σ))
        ((A.append B σ).splitParameters θ).2) := (rfl)

/-- Joining affine parameters first transports them to the extracted parts, then joins those
parts using `splitParameters`. -/
@[simp] theorem appendParameters_symm_apply
    (h : A.width (Fin.last (L + 1)) = B.width 0) (p : A.Parameters × B.Parameters) :
    (A.appendParameters B σ h).symm p =
      (A.append B σ).splitParameters.symm
        (cast (congrArg Parameters (lowerLayers_append A B σ h).symm) p.1,
         cast (congrArg Parameters (upperLayers_append A B σ).symm) p.2) := (rfl)

/-- The weight-only parameters of a concatenation are exactly the weights of its two factors,
provided their boundary widths match. -/
def appendWeights (h : A.width (Fin.last (L + 1)) = B.width 0) :
    (A.append B σ).Weights ≃ A.Weights × B.Weights :=
  (A.append B σ).splitWeights.trans
    (Equiv.prodCongr (Equiv.cast (congrArg Weights (lowerLayers_append A B σ h)))
      (Equiv.cast (congrArg Weights (upperLayers_append A B σ))))

/-- Splitting weight-only parameters transports the extracted parts to the original
specifications. -/
@[simp] theorem appendWeights_apply
    (h : A.width (Fin.last (L + 1)) = B.width 0) (w : (A.append B σ).Weights) :
    A.appendWeights B σ h w =
      (cast (congrArg Weights (lowerLayers_append A B σ h))
        ((A.append B σ).splitWeights w).1,
       cast (congrArg Weights (upperLayers_append A B σ))
        ((A.append B σ).splitWeights w).2) := (rfl)

/-- Joining weight-only parameters transports them to the extracted parts and joins those
parts without adding biases. -/
@[simp] theorem appendWeights_symm_apply
    (h : A.width (Fin.last (L + 1)) = B.width 0) (p : A.Weights × B.Weights) :
    (A.appendWeights B σ h).symm p =
      (A.append B σ).splitWeights.symm
        (cast (congrArg Weights (lowerLayers_append A B σ h).symm) p.1,
         cast (congrArg Weights (upperLayers_append A B σ).symm) p.2) := (rfl)

/-- The parameter-product identification respects the zero-bias embeddings in both factors. -/
-- Simplify the zero-bias interaction before expanding the parameter equivalence.
@[simp↓] theorem appendParameters_zeroBias [Zero K]
    (h : A.width (Fin.last (L + 1)) = B.width 0) (w : (A.append B σ).Weights) :
    A.appendParameters B σ h ((A.append B σ).zeroBias w) =
      (A.zeroBias (A.appendWeights B σ h w).1, B.zeroBias (A.appendWeights B σ h w).2) := by
  simp only [appendParameters_apply, appendWeights_apply, splitParameters_zeroBias]
  exact Prod.ext (zeroBias_cast (lowerLayers_append A B σ h) _).symm
    (zeroBias_cast (upperLayers_append A B σ) _).symm

/-- Joining weights and then assigning zero biases agrees with joining the zero-bias
parameters of the factors. -/
-- Keep joined zero-bias parameters in the affine API before expanding joined weights.
@[simp↓] theorem zeroBias_appendWeights_symm [Zero K]
    (h : A.width (Fin.last (L + 1)) = B.width 0) (w : A.Weights) (v : B.Weights) :
    (A.append B σ).zeroBias ((A.appendWeights B σ h).symm (w, v)) =
      (A.appendParameters B σ h).symm (A.zeroBias w, B.zeroBias v) := by
  apply (A.appendParameters B σ h).injective
  rw [appendParameters_zeroBias, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

section Evaluation

variable [NonUnitalNonAssocSemiring K]

/-- Joined affine parameters realize `B` after the junction activation and `A`, with the
canonical identifications of equal boundary, input, and output widths. -/
theorem realize_appendParameters_symm
    (h : A.width (Fin.last (L + 1)) = B.width 0) (θ : A.Parameters) (η : B.Parameters)
    (x : Fin ((A.append B σ).width 0) → K)
    (j : Fin ((A.append B σ).width (Fin.last (L + 1 + (M + 1))))) :
    (A.append B σ).realize ((A.appendParameters B σ h).symm (θ, η)) x j =
      B.realize η
        (fun i => σ (A.realize θ (x ∘ Fin.cast (append_width_zero A B σ).symm)
          (Fin.cast h.symm i)))
        (Fin.cast (append_width_last A B σ) j) := by
  rw [appendParameters_symm_apply, realize_eq_upperLayers_realize]
  simp only [Equiv.apply_symm_apply]
  -- The endpoint indices of the extracted parts agree definitionally with those of the
  -- concatenation; `erw` sees through the unexposed `append` to compare them. The final
  -- index casts have identical values, independently of their equality proofs.
  erw [realize_cast (upperLayers_append A B σ).symm η]
  congr 1
  funext i
  dsimp only [Function.comp_def]
  erw [realize_cast (lowerLayers_append A B σ h).symm θ]
  rw [junctionActivation_append]
  rfl

/-- Joined bias-free parameters realize the same composition using only the original weight
spaces; no artificial bias parameters occur. -/
theorem realizeWeights_appendWeights_symm
    (h : A.width (Fin.last (L + 1)) = B.width 0) (w : A.Weights) (v : B.Weights)
    (x : Fin ((A.append B σ).width 0) → K)
    (j : Fin ((A.append B σ).width (Fin.last (L + 1 + (M + 1))))) :
    (A.append B σ).realizeWeights ((A.appendWeights B σ h).symm (w, v)) x j =
      B.realizeWeights v
        (fun i => σ (A.realizeWeights w (x ∘ Fin.cast (append_width_zero A B σ).symm)
          (Fin.cast h.symm i)))
        (Fin.cast (append_width_last A B σ) j) := by
  simp only [realizeWeights_def, Function.comp_apply]
  rw [zeroBias_appendWeights_symm, realize_appendParameters_symm]

end Evaluation

end TauCeti.Neuromanifold.MLPSpec
