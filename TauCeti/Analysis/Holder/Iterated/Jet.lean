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
defines that jet space, the projection onto the field of each order `i ≤ k`, through which the
derivative identities cutting out each `C^{k,α}` space are expressed, the norm of a jet in terms
of these fields, and the jet with prescribed fields.

## Main declarations

* `TauCeti.HolderJet k α X E F`: the jet space.
* `TauCeti.HolderJet.fieldL`: the field of order `i ≤ k` of a jet, as a continuous linear map.
* `TauCeti.HolderJet.ext_fieldL`: a jet is determined by its fields.
* `TauCeti.HolderJet.norm_eq`: the norm of a jet is the sum of the supremum norms of its fields and
  the Hölder seminorm of its top field.
* `TauCeti.HolderJet.ofFields`: the jet with prescribed fields.
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

/-- A jet is determined by its fields of all orders `i ≤ k`. -/
theorem ext_fieldL {J K : HolderJet k α X E F} (h : ∀ i, fieldL i J = fieldL i K) : J = K := by
  apply WithLp.ofLp_injective 1
  apply Prod.ext
  · apply WithLp.ofLp_injective 1
    funext j
    have := h j.castSucc
    rwa [fieldL_castSucc, fieldL_castSucc] at this
  · apply HolderSpace.ext
    intro x
    have := DFunLike.congr_fun (h (Fin.last k)) x
    rwa [fieldL_last, fieldL_last, HolderSpace.toBoundedContinuousFunction_apply,
      HolderSpace.toBoundedContinuousFunction_apply] at this

/-- The norm of a jet is the sum of the supremum norms of its fields through order `k` and the
`α`-Hölder seminorm of its field of order `k`. -/
theorem norm_eq (J : HolderJet k α X E F) :
    ‖J‖ = ∑ i : Fin (k + 1), ‖fieldL i J‖ +
      nnHolderNorm α (J.ofLp.2 : X → E [×k]→L[ℝ] F) := by
  rw [WithLp.prod_norm_eq_of_L1, PiLp.norm_eq_of_L1, Fin.sum_univ_castSucc,
    HolderSpace.norm_def, ← HolderSpace.coe_toBoundedContinuousFunction, add_assoc]
  simp only [fieldL_castSucc, fieldL_last, WithLp.ofLp_fst, WithLp.ofLp_snd]

/-- The jet with prescribed bounded continuous fields of all orders `i ≤ k`, the field of order
`k` being `α`-Hölder. -/
def ofFields (g : ∀ i : Fin (k + 1), X →ᵇ (E [×i]→L[ℝ] F))
    (hg : MemHolder α (g (Fin.last k) : X → E [×k]→L[ℝ] F)) : HolderJet k α X E F :=
  WithLp.toLp 1 (WithLp.toLp 1 fun j : Fin k ↦ g j.castSucc,
    HolderSpace.ofBoundedContinuousFunction (g (Fin.last k)) hg)

@[simp]
theorem fieldL_ofFields (g : ∀ i : Fin (k + 1), X →ᵇ (E [×i]→L[ℝ] F))
    (hg : MemHolder α (g (Fin.last k) : X → E [×k]→L[ℝ] F)) (i : Fin (k + 1)) :
    fieldL i (ofFields g hg) = g i := by
  induction i using Fin.lastCases with
  | last =>
    rw [fieldL_last, ofFields, HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction]
  | cast j =>
    rw [fieldL_castSucc, ofFields]

end HolderJet

end TauCeti
