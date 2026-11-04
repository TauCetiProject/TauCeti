/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.Algebra.Lie.ExteriorPower
public import TauCeti.LinearAlgebra.Complex.Conjugation

/-!
# The `(p,q)` type of complexified exterior powers

Let `J` be a real-linear endomorphism of a real vector space `V`, typically a complex structure,
`J² = -1`. It acts on the exterior power `⋀ᵏ V` as the derivation `exteriorPower.lieMap k J`, which
applies `J` to one factor of a wedge at a time, and complex-linearly on the complexified exterior
power `ℂ ⊗[ℝ] ⋀ᵏ V`. A complexified `k`-vector has type `(p,q)`, `p + q = k`, when this action is
multiplication by `(p - q) * I` (`exteriorPower.typeSubmodule`). These are the usual
`(p,q)`-vectors: read in the exterior algebra of the complexification of `V`, a wedge of `p`
vectors of type `(1,0)`, the `I`-eigenvectors of `J`, and `q` vectors of type `(0,1)`, the
`-I`-eigenvectors, is an eigenvector of the derivation with eigenvalue `p * I - q * I`.

The eigenvalue formula is the one of `ContinuousAlternatingMap.IsOfType` for complex-valued forms,
where `J` is likewise applied to one argument at a time, so the types agree under the evaluation
pairing of vectors with forms. They do not agree under the metric identification
`TauCeti.alternatingFormEquiv`, `x ↦ ⟪x, ·⟫`: for skew-adjoint `J` the derivation is
skew-adjoint, so its complex-linear extension sends vectors of type `(p,q)` to forms of type
`(q,p)`. The type laws for the complex Hodge star and `barStar` are unchanged by this exchange.

Since `J` is real, conjugation of the coefficients exchanges the types `(p,q)` and `(q,p)`
(`exteriorPower.tmulConj_mem_typeSubmodule_iff`). The complex Hodge star of an oriented inner
product space carries these types to the complementary ones when `J` is orthogonal; see
`TauCeti.Analysis.InnerProductSpace.HodgeStar.Complex`.

## Main declarations

* `exteriorPower.typeSubmodule`: the complexified `k`-vectors of type `(p,q)` for `J`.
* `exteriorPower.mem_typeSubmodule`: the eigenvalue characterization of the type in degree
  `p + q`.
* `exteriorPower.typeSubmodule_eq_bot`: there are no nonzero vectors of type `(p,q)` in a degree
  other than `p + q`.
* `exteriorPower.tmulConj_mem_typeSubmodule_iff`: conjugation exchanges the types `(p,q)` and
  `(q,p)`.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 1.2.
-/

public section

noncomputable section

open Complex TauCeti
open scoped TensorProduct

namespace exteriorPower

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The complexified `k`-vectors of type `(p,q)` for an endomorphism `J` of `V`: in degree
`k = p + q`, those on which the complexified derivation action of `J` is multiplication by
`(p - q) * I`. In a degree other than `p + q` it is `⊥`. -/
def typeSubmodule (k : ℕ) (J : Module.End ℝ V) (p q : ℕ) : Submodule ℂ (ℂ ⊗[ℝ] ⋀[ℝ]^k V) :=
  ⨆ _ : p + q = k, Module.End.eigenspace ((lieMap k J).baseChange ℂ) (((p : ℂ) - q) * I)

variable {J : Module.End ℝ V} {k p q : ℕ} {x : ℂ ⊗[ℝ] ⋀[ℝ]^k V}

/-- In degree `k = p + q`, a complexified `k`-vector has type `(p,q)` exactly when the derivation
action of `J` on it is multiplication by `(p - q) * I`. -/
theorem mem_typeSubmodule (h : p + q = k) :
    x ∈ typeSubmodule k J p q ↔ (lieMap k J).baseChange ℂ x = (((p : ℂ) - q) * I) • x := by
  simp [typeSubmodule, h]

/-- There are no nonzero complexified `k`-vectors of type `(p,q)` unless `p + q = k`. -/
theorem typeSubmodule_eq_bot (h : p + q ≠ k) : typeSubmodule k J p q = ⊥ := by
  simp [typeSubmodule, h]

/-- Conjugation of the coefficients exchanges the types `(p,q)` and `(q,p)`, because the derivation
action of the real endomorphism `J` commutes with it. -/
@[simp]
theorem tmulConj_mem_typeSubmodule_iff :
    tmulConj _ x ∈ typeSubmodule k J q p ↔ x ∈ typeSubmodule k J p q := by
  by_cases h : p + q = k
  swap
  · rw [typeSubmodule_eq_bot h, typeSubmodule_eq_bot (by omega), Submodule.mem_bot,
      Submodule.mem_bot, map_eq_zero_iff _ (tmulConj_involutive _).injective]
  rw [mem_typeSubmodule (by omega), mem_typeSubmodule h, ← tmulConj_baseChange]
  -- The eigenvalue `(q - p) * I` is the conjugate of `(p - q) * I`.
  have hc : ((q : ℂ) - p) * I = starRingEnd ℂ (((p : ℂ) - q) * I) := by
    simp only [map_mul, map_sub, map_natCast, conj_I]
    ring
  rw [hc, ← LinearMap.map_smulₛₗ, (tmulConj_involutive _).injective.eq_iff]

end exteriorPower
