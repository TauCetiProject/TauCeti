/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Basic

/-!
# Coefficient and group multipliers of twisted convolution

Let `α` be a point-norm continuous action of a topological group `G` on a C⋆-algebra `A`. The
coefficient algebra and the group act on `C_c(G, A)` on the left by

`(a • f) s = a * f s` and `(r • f) s = α r (f (r⁻¹ * s))`,

the second being `CStarAction.translate`. These are the formulas of Williams's canonical maps
`i_A(a)` and `i_G(r)` into the multiplier algebra of the crossed product, evaluated on the dense
subalgebra `C_c(G, A)`. Both commute with twisted convolution in the first variable,
`(a • f) ⋆ g = a • (f ⋆ g)` and `(r • f) ⋆ g = r • (f ⋆ g)`; the second identity needs a
left-invariant measure. The coefficient action is Mathlib's pointwise scalar action of `A` on
`C_c(G, A)`, and its identity `TauCeti.CStarAction.smul_convolution` lives beside the convolution
itself, so only the group action and its identity are developed here.

An integrated covariant representation turns these multipliers into its coefficient and group
operators; this is how a covariant pair is recovered from its integrated form.

The conventions follow Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2, where these
are the maps `i_A` and `i_G`.

## Main definitions

* `TauCeti.CStarAction.translate`: the left action `(r • f) s = α r (f (r⁻¹ * s))` of `G` on
  `C_c(G, A)`.

## Main statements

* `TauCeti.CStarAction.translate_convolution`: `(r • f) ⋆ g = r • (f ⋆ g)`.
-/

public section

open MeasureTheory
open scoped CompactlySupported

namespace TauCeti.CStarAction

variable {G A : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  (α : CStarAction G A)

section ContinuousMul

variable [ContinuousMul G]

/-- The twisted left translate of a single function, before bundling. -/
private noncomputable def translateAux (r : G) (f : C_c(G, A)) : C_c(G, A) where
  toFun s := α r (f (r⁻¹ * s))
  continuous_toFun := by fun_prop
  hasCompactSupport' :=
    (f.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft r⁻¹)).comp_left (map_zero _)

private theorem translateAux_apply (r : G) (f : C_c(G, A)) (s : G) :
    translateAux α r f s = α r (f (r⁻¹ * s)) :=
  rfl

/-- The left action of `G` on `C_c(G, A)` twisted by `α`: `(r • f) s = α r (f (r⁻¹ * s))`. -/
noncomputable def translate (r : G) : C_c(G, A) →ₗ[ℂ] C_c(G, A) where
  toFun := translateAux α r
  map_add' f g := by ext; simp [translateAux_apply]
  map_smul' c f := by ext; simp [translateAux_apply]

@[simp]
theorem translate_apply (r : G) (f : C_c(G, A)) (s : G) :
    α.translate r f s = α r (f (r⁻¹ * s)) :=
  (rfl)

/-- The identity translates trivially. -/
@[simp]
theorem translate_one (f : C_c(G, A)) : α.translate 1 f = f := by
  ext; simp

/-- The twisted translations form a left action of `G`. -/
theorem translate_mul (r t : G) (f : C_c(G, A)) :
    α.translate (r * t) f = α.translate r (α.translate t f) := by
  ext; simp [mul_assoc, mul_apply]

end ContinuousMul

variable [IsTopologicalGroup G] [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G)
  [IsFiniteMeasureOnCompacts μ]

/-- The twisted left translation commutes with twisted convolution with respect to a
left-invariant measure. -/
theorem translate_convolution [MeasurableMul G] [μ.IsMulLeftInvariant] (r : G)
    (f g : C_c(G, A)) :
    α.convolution μ (α.translate r f) g = α.translate r (α.convolution μ f g) := by
  ext s
  simp only [convolution_apply, translate_apply]
  -- Substitute `t ↦ r * t`, then pull `α r` out of the integral.
  rw [← integral_mul_left_eq_self _ r, ← α.integral_comp_comm]
  simp [mul_assoc, mul_apply]

end TauCeti.CStarAction
