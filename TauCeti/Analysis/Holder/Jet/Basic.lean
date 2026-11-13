/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Normed
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Jets of derivative fields for `C^{k,α}` spaces

The spaces `C^{k,α}` of `TauCeti.CkHolderSpace` (on the whole space) and
`TauCeti.CkHolderSpaceOn` (on an open set) are both closed subspaces of a space of jets: bounded
continuous derivative fields on a metric space `X` of orders below `k`, with the `ℓ¹` norm,
together with a bounded Hölder field of order `k`. This file provides the jet space, its field
projections, and left currying of multilinear maps as a continuous linear map, which together
state the derivative identities cutting out both spaces. The field domain `X` is `E` for the
whole space and the open set for `TauCeti.CkHolderSpaceOn`.

## Main declarations

* `TauCeti.CkHolderJet k α X E F`: the jet space.
* `TauCeti.CkHolderJet.fieldL`: the derivative field of order `i ≤ k`, as a continuous linear
  map.
* `TauCeti.CkHolderJet.curryLeftL`: left currying of `(j + 1)`-multilinear maps, as a
  continuous linear map.
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
  congrArg (· J) (Fin.lastCases_castSucc (motive := fun i : Fin (k + 1) ↦
    CkHolderJet k α X E F →L[ℝ] (X →ᵇ (E [×i]→L[ℝ] F))) j)

/-- The derivative field of order `k` is the Hölder field. -/
theorem fieldL_last (J : CkHolderJet k α X E F) :
    fieldL (Fin.last k) J = J.ofLp.2.toBoundedContinuousFunction :=
  (congrArg (· J) (Fin.lastCases_last (motive := fun i : Fin (k + 1) ↦
    CkHolderJet k α X E F →L[ℝ] (X →ᵇ (E [×i]→L[ℝ] F)))
    (last := HolderSpace.toBoundedContinuousFunctionCLM.comp (WithLp.sndL 1 ℝ _ _))
    (cast := fun j ↦ (PiLp.proj 1 _ j).comp (WithLp.fstL 1 ℝ _ _)))).trans (by simp)

variable (E F) in
/-- Left currying of `(j + 1)`-multilinear maps, as a continuous linear map. -/
def curryLeftL (j : ℕ) : (E [×j + 1]→L[ℝ] F) →L[ℝ] E →L[ℝ] (E [×j]→L[ℝ] F) :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F).toContinuousLinearEquiv

theorem curryLeftL_apply (j : ℕ) (g : E [×j + 1]→L[ℝ] F) :
    curryLeftL E F j g = g.curryLeft := by
  ext x v
  simp [curryLeftL]

end CkHolderJet

end TauCeti
