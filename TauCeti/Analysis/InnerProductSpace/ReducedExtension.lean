/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti: additions to `Mathlib/Analysis/InnerProductSpace/`
(a home next to `Submodule.starProjection`).

The quadratic-form identity
below had been proved four times: twice inside
`…/BoundedOperator/SinTheta.lean`'s `sinTheta_directed_coercive` and twice inside
`…/SinTheta/OperatorNorm.lean`'s `exists_isSymmetric_comp_sub_comp_eq`, at about
31 lines each.  Earlier consolidation reduced that to one private copy per
module; this module reduces it to one.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Quadratic forms of reduced extensions

A *reduced extension* of an operator `R` along a subspace `W` is the operator
agreeing with `R` on `W` and acting as a real scalar `κ` on `Wᗮ`:

`R ∘ P_W + κ (1 - P_W)`.

It is the standard device for turning a *local* form bound — `R` is coercive on
`W`, or bounded above on `W` — into a *global* one, which is what a Sylvester
estimate consumes.  Davis–Kahan `sin Θ` proofs build two of them and need the
quadratic form of each.

The main result, `TauCeti.re_inner_reducedExtension_self`, computes that form:
the cross terms vanish by orthogonality, leaving

`re ⟪R (P x), P x⟫ + κ ‖x - P x‖²`.

## Design

The statement is about the **value** `R (P x) + κ • (x - P x)` rather than about
a bundled operator.  That is deliberate and it is what lets one lemma serve both
callers: one packages its extension as `E →L[𝕜] E` and needs no
finite-dimensionality, the other arrives with `R : E →ₗ[𝕜] E` and reaches
`E →L[𝕜] E` through `toContinuousLinearMap`, which does.  Phrased pointwise,
neither packaging appears, and the caller discharges the one-line `simp` that its
operator applied at `x` is that value.

Only **invariance** of `W` under `R` is assumed — not `Reduces`, and nothing
about `Wᗮ`.  That is all the argument uses.

## Sources

*Follows nothing in particular*: the identity is the standard orthogonal
splitting of a quadratic form, and the proof is Pythagoras plus the vanishing of
the cross terms.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: extracted from the bodies of
  `ForTauCeti/Analysis/InnerProductSpace/BoundedOperator/SinTheta.lean`
  (`sinTheta_directed_coercive`) and
  `ForTauCeti/Analysis/InnerProductSpace/SinTheta/OperatorNorm.lean`
  (`exists_isSymmetric_comp_sub_comp_eq`), where it had been proved four times
  inline.
* Extraction class: **de-duplicated in place** — no statement is new; the four
  inline copies become one named lemma and its two callers.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — imports only Mathlib.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Pythagoras for an orthogonal projection.**  A vector splits into its
projection and the complementary part, and the squared norms add. -/
theorem norm_sq_eq_starProjection_add_sub {W : Submodule 𝕜 E}
    [W.HasOrthogonalProjection] (x : E) :
    ‖x‖ ^ 2 = ‖W.starProjection x‖ ^ 2 + ‖x - W.starProjection x‖ ^ 2 := by
  have hpx : W.starProjection x ∈ W := W.starProjection_apply_mem x
  have hrest : x - W.starProjection x ∈ Wᗮ :=
    W.sub_starProjection_mem_orthogonal x
  have h0 : RCLike.re ⟪W.starProjection x, x - W.starProjection x⟫_𝕜 = 0 := by
    rw [Submodule.inner_right_of_mem_orthogonal hpx hrest]; simp
  have hns := norm_add_sq (𝕜 := 𝕜) (W.starProjection x) (x - W.starProjection x)
  rw [show W.starProjection x + (x - W.starProjection x) = x by abel, h0] at hns
  linarith

/-- **The quadratic form of a reduced extension splits.**  If `W` is invariant
under `R`, then the extension agreeing with `R` on `W` and with the real scalar
`κ` on `Wᗮ` has quadratic form

`re ⟪R (P x), P x⟫ + κ ‖x - P x‖²`,

both cross terms vanishing by orthogonality.

Stated at the value `R (P x) + κ • (x - P x)` rather than at a bundled operator,
so that callers packaging the extension as a `ContinuousLinearMap` — by any
route, with or without finite-dimensionality — can use it after a one-line
`simp`. -/
theorem re_inner_reducedExtension_self {R : E →ₗ[𝕜] E} {W : Submodule 𝕜 E}
    [W.HasOrthogonalProjection] (hinv : ∀ x ∈ W, R x ∈ W) (κ : ℝ) (x : E) :
    RCLike.re ⟪R (W.starProjection x)
        + ((κ : ℝ) : 𝕜) • (x - W.starProjection x), x⟫_𝕜
      = RCLike.re ⟪R (W.starProjection x), W.starProjection x⟫_𝕜
        + κ * ‖x - W.starProjection x‖ ^ 2 := by
  have hpx : W.starProjection x ∈ W := W.starProjection_apply_mem x
  have hrest : x - W.starProjection x ∈ Wᗮ :=
    W.sub_starProjection_mem_orthogonal x
  have hre : RCLike.re ⟪R (W.starProjection x)
        + ((κ : ℝ) : 𝕜) • (x - W.starProjection x), x⟫_𝕜
      = RCLike.re ⟪R (W.starProjection x), x⟫_𝕜
        + κ * RCLike.re ⟪x - W.starProjection x, x⟫_𝕜 := by
    rw [inner_add_left, inner_smul_left, RCLike.conj_ofReal, map_add,
      RCLike.re_ofReal_mul]
  have h1 : RCLike.re ⟪R (W.starProjection x), x⟫_𝕜
      = RCLike.re ⟪R (W.starProjection x), W.starProjection x⟫_𝕜 := by
    have hz : ⟪R (W.starProjection x), x - W.starProjection x⟫_𝕜 = 0 :=
      Submodule.inner_right_of_mem_orthogonal (hinv _ hpx) hrest
    have hsplit : ⟪R (W.starProjection x), x⟫_𝕜
        = ⟪R (W.starProjection x), W.starProjection x⟫_𝕜
          + ⟪R (W.starProjection x), x - W.starProjection x⟫_𝕜 := by
      rw [← inner_add_right]; congr 1; abel
    rw [hsplit, hz, add_zero]
  have h2 : RCLike.re ⟪x - W.starProjection x, x⟫_𝕜
      = ‖x - W.starProjection x‖ ^ 2 := by
    have hz : ⟪x - W.starProjection x, W.starProjection x⟫_𝕜 = 0 :=
      Submodule.inner_left_of_mem_orthogonal hpx hrest
    have hsplit : ⟪x - W.starProjection x, x⟫_𝕜
        = ⟪x - W.starProjection x, x - W.starProjection x⟫_𝕜 := by
      have h' : ⟪x - W.starProjection x, x⟫_𝕜
          = ⟪x - W.starProjection x, W.starProjection x⟫_𝕜
            + ⟪x - W.starProjection x, x - W.starProjection x⟫_𝕜 := by
        rw [← inner_add_right]; congr 1; abel
      rw [h', hz, zero_add]
    rw [hsplit, inner_self_eq_norm_sq]
  rw [hre, h1, h2]

end TauCeti
