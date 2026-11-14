/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Normed
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Jets of derivative fields for `C^{k,α}` spaces

The spaces `C^{k,α}` of `TauCeti.CkHolderSpace` (on the whole space) and
`TauCeti.CkHolderSpaceOn` (on an open set) are both closed subspaces of a space of jets: bounded
continuous derivative fields on a metric space `X` of orders below `k`, with the `ℓ¹` norm,
together with a bounded Hölder field of order `k`. This file provides the jet space, its
construction from fields, its field projections, through which both spaces state the derivative
identities cutting them out, and the description of equality and of the norm of jets through the
fields. The field domain `X` is `E` for the whole space and the open set for
`TauCeti.CkHolderSpaceOn`.

## Main declarations

* `TauCeti.CkHolderJet k α X E F`: the jet space.
* `TauCeti.CkHolderJet.ofFields`: the jet with given fields.
* `TauCeti.CkHolderJet.fieldL`: the derivative field of order `i ≤ k`, as a continuous linear
  map.
* `TauCeti.CkHolderJet.ext`, `TauCeti.CkHolderJet.norm_eq`: a jet is determined by its fields,
  and its norm is the sum of the supremum norms of the fields and the Hölder seminorm of the top
  field.
-/

public section

noncomputable section

namespace TauCeti

open scoped NNReal BoundedContinuousFunction

universe u v w

variable (k : ℕ) (α : ℝ≥0) (X : Type u) [MetricSpace X] (E : Type v) (F : Type w)
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps. Without it, instance
search for the module structure of `ℓ¹` products of these fields indexed by the order `n` exceeds
the default synthesis depth. It is local so that the instance path for these fields is unchanged
outside this file. -/
local instance CkHolderJet.instNormedAddCommGroupBoundedContinuousFunction (n : ℕ) :
    NormedAddCommGroup (X →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps, needed for the
module structure of `ℓ¹` products of these fields. It is local for the same reason. -/
local instance CkHolderJet.instNormedSpaceBoundedContinuousFunction (n : ℕ) :
    NormedSpace ℝ (X →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- The jet space of `C^{k,α}` maps with derivative fields on `X`: bounded continuous fields of
`i`-multilinear maps on `X` for orders `i < k`, with the `ℓ¹` norm, together with a bounded
`α`-Hölder field of `k`-multilinear maps on `X`. -/
abbrev CkHolderJet := WithLp 1
  ((PiLp 1 fun i : Fin k ↦ X →ᵇ (E [×i]→L[ℝ] F)) × HolderSpace α X (E [×k]→L[ℝ] F))

namespace CkHolderJet

variable {k α X E F}

/-- The derivative field of order `i ≤ k` of a jet, as a bounded continuous field. -/
def fieldL (i : Fin (k + 1)) : CkHolderJet k α X E F →L[ℝ] (X →ᵇ (E [×i]→L[ℝ] F)) :=
  Fin.lastCases (motive := fun i : Fin (k + 1) ↦
      CkHolderJet k α X E F →L[ℝ] (X →ᵇ (E [×i]→L[ℝ] F)))
    (HolderSpace.toBoundedContinuousFunctionCLM.comp (WithLp.sndL 1 ℝ _ _))
    (fun j ↦ (PiLp.proj 1 _ j).comp (WithLp.fstL 1 ℝ _ _)) i

/-- The derivative fields below order `k` are the components of the first factor. -/
theorem fieldL_castSucc (j : Fin k) (J : CkHolderJet k α X E F) :
    fieldL j.castSucc J = J.ofLp.1 j :=
  (congrArg (· J) (Fin.lastCases_castSucc (motive := fun i : Fin (k + 1) ↦
    CkHolderJet k α X E F →L[ℝ] (X →ᵇ (E [×i]→L[ℝ] F))) j)).trans (by simp)

/-- The derivative field of order `k` is the Hölder field. -/
theorem fieldL_last (J : CkHolderJet k α X E F) :
    fieldL (Fin.last k) J = J.ofLp.2.toBoundedContinuousFunction :=
  (congrArg (· J) (Fin.lastCases_last (motive := fun i : Fin (k + 1) ↦
    CkHolderJet k α X E F →L[ℝ] (X →ᵇ (E [×i]→L[ℝ] F)))
    (last := HolderSpace.toBoundedContinuousFunctionCLM.comp (WithLp.sndL 1 ℝ _ _))
    (cast := fun j ↦ (PiLp.proj 1 _ j).comp (WithLp.fstL 1 ℝ _ _)))).trans (by simp)

/-- A jet is determined by its derivative fields. -/
theorem ext {J K : CkHolderJet k α X E F} (h : ∀ i, fieldL i J = fieldL i K) : J = K := by
  apply WithLp.ofLp_injective 1
  apply Prod.ext
  · apply WithLp.ofLp_injective 1
    funext j
    simpa only [fieldL_castSucc] using h j.castSucc
  · apply HolderSpace.toBoundedContinuousFunction_injective
    simpa only [fieldL_last] using h (Fin.last k)

/-- The norm of a jet is the sum of the supremum norms of its fields and the `α`-Hölder seminorm
of its field of order `k`. -/
theorem norm_eq (J : CkHolderJet k α X E F) :
    ‖J‖ = ∑ i : Fin (k + 1), ‖fieldL i J‖ + nnHolderNorm α ⇑(fieldL (Fin.last k) J) := by
  rw [WithLp.prod_norm_eq_of_L1, PiLp.norm_eq_of_L1, Fin.sum_univ_castSucc, HolderSpace.norm_def,
    add_assoc]
  simp only [fieldL_castSucc, fieldL_last, HolderSpace.coe_toBoundedContinuousFunction,
    WithLp.ofLp_fst, WithLp.ofLp_snd]

/-- The jet with fields `g j` below order `k` and Hölder field `h` of order `k`. -/
def ofFields (g : ∀ j : Fin k, X →ᵇ (E [×j]→L[ℝ] F)) (h : HolderSpace α X (E [×k]→L[ℝ] F)) :
    CkHolderJet k α X E F :=
  WithLp.toLp 1 (WithLp.toLp 1 g, h)

/-- The fields below order `k` of `ofFields g h` are the `g j`. -/
theorem fieldL_castSucc_ofFields (g : ∀ j : Fin k, X →ᵇ (E [×j]→L[ℝ] F))
    (h : HolderSpace α X (E [×k]→L[ℝ] F)) (j : Fin k) :
    fieldL j.castSucc (ofFields g h) = g j := by
  rw [ofFields, fieldL_castSucc]

/-- The field of order `k` of `ofFields g h` is `h`. -/
theorem fieldL_last_ofFields (g : ∀ j : Fin k, X →ᵇ (E [×j]→L[ℝ] F))
    (h : HolderSpace α X (E [×k]→L[ℝ] F)) :
    fieldL (Fin.last k) (ofFields g h) = h.toBoundedContinuousFunction := by
  rw [ofFields, fieldL_last]

end CkHolderJet

end TauCeti
