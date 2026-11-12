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
# Jets of derivative fields for Hölder spaces of every order

The spaces `C^{k,α}` of `TauCeti.CkHolderSpace` (on the whole space `E`) and
`TauCeti.CkHolderOnSpace` (on an open set `Ω ⊆ E`) are both carved out of the same ambient normed
space: bounded continuous fields `X →ᵇ (E [×i]→L[ℝ] F)` of `i`-multilinear maps for `i < k`, with
the `ℓ¹` norm, together with a bounded `α`-Hölder field `X → E [×k]→L[ℝ] F`. Here `X` is the
domain of the fields (`E` itself, or `Ω`) and `E` is the space of derivative directions. This file
defines that jet space, the projection onto the field of each order `i ≤ k`, and left currying of
multilinear maps as a continuous linear map, which together express the derivative identities
cutting out each `C^{k,α}` space.

## Main declarations

* `TauCeti.HolderJet k α X E F`: the jet space.
* `TauCeti.HolderJet.fieldL`: the field of order `i ≤ k` of a jet, as a continuous linear map.
* `TauCeti.HolderJet.curryLeftL`: left currying of `(j + 1)`-multilinear maps, as a continuous
  linear map.
-/

public section

noncomputable section

namespace TauCeti

open scoped NNReal BoundedContinuousFunction

universe u v w

variable (k : ℕ) (α : ℝ≥0) (X : Type u) (E : Type v) (F : Type w) [MetricSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps. Without it, instance
search for the module structure of `ℓ¹` products of these fields indexed by the order `n` exceeds
the default synthesis depth. It is local so that the instance path for these fields is unchanged
outside this file. -/
local instance HolderJet.instNormedAddCommGroupBoundedContinuousFunction (n : ℕ) :
    NormedAddCommGroup (X →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps, needed for continuous
linear maps into these fields indexed by the order `n`. It is local for the same reason. -/
local instance HolderJet.instNormedSpaceBoundedContinuousFunction (n : ℕ) :
    NormedSpace ℝ (X →ᵇ (E [×n]→L[ℝ] F)) :=
  inferInstance

/-- The ambient jet space of the `C^{k,α}` spaces: bounded continuous fields on `X` of
`i`-multilinear maps on `E` for `i < k`, with the `ℓ¹` norm, together with a bounded `α`-Hölder
field of `k`-multilinear maps. -/
abbrev HolderJet := WithLp 1
  ((PiLp 1 fun i : Fin k ↦ X →ᵇ (E [×i]→L[ℝ] F)) × HolderSpace α X (E [×k]→L[ℝ] F))

namespace HolderJet

variable {k α X E F}

/-- The field of order `i ≤ k` of a jet: a bounded continuous field for `i < k`, and the Hölder
field, as a bounded continuous field, for `i = k`. -/
-- Exposed so that the carriers of the `C^{k,α}` spaces, which state the derivative identities
-- through the same projections, unfold to statements about `fieldL`.
@[expose] def fieldL (i : Fin (k + 1)) : HolderJet k α X E F →L[ℝ] (X →ᵇ (E [×i]→L[ℝ] F)) :=
  Fin.lastCases (motive := fun i : Fin (k + 1) ↦ HolderJet k α X E F →L[ℝ] (X →ᵇ (E [×i]→L[ℝ] F)))
    (HolderSpace.toBoundedContinuousFunctionCLM.comp (WithLp.sndL 1 ℝ _ _))
    (fun j ↦ (PiLp.proj 1 _ j).comp (WithLp.fstL 1 ℝ _ _)) i

theorem fieldL_castSucc (j : Fin k) (J : HolderJet k α X E F) :
    fieldL j.castSucc J = J.ofLp.1 j :=
  congrArg (· J) (Fin.lastCases_castSucc (motive := fun i : Fin (k + 1) ↦
    HolderJet k α X E F →L[ℝ] (X →ᵇ (E [×i]→L[ℝ] F))) j)

theorem fieldL_last (J : HolderJet k α X E F) :
    fieldL (Fin.last k) J = J.ofLp.2.toBoundedContinuousFunction :=
  (congrArg (· J) (Fin.lastCases_last (motive := fun i : Fin (k + 1) ↦
    HolderJet k α X E F →L[ℝ] (X →ᵇ (E [×i]→L[ℝ] F)))
    (last := HolderSpace.toBoundedContinuousFunctionCLM.comp (WithLp.sndL 1 ℝ _ _))
    (cast := fun j ↦ (PiLp.proj 1 _ j).comp (WithLp.fstL 1 ℝ _ _)))).trans (by simp)

variable (E F) in
/-- Left currying of `(j + 1)`-multilinear maps, as a continuous linear map. -/
-- Exposed so that it unfolds to `continuousMultilinearCurryLeftEquiv` in those carriers.
@[expose] def curryLeftL (j : ℕ) : (E [×j + 1]→L[ℝ] F) →L[ℝ] E →L[ℝ] (E [×j]→L[ℝ] F) :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F).toContinuousLinearEquiv

@[simp]
theorem curryLeftL_apply (j : ℕ) (g : E [×j + 1]→L[ℝ] F) :
    curryLeftL E F j g = g.curryLeft := by
  ext x v
  simp [curryLeftL]

end HolderJet

end TauCeti
