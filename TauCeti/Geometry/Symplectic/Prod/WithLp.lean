/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Geometry.Symplectic.Complex.Line
public import TauCeti.Geometry.Symplectic.Prod.Basic
public import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# Direct sums of compatible pairs on the Euclidean product

`TauCeti.Geometry.Symplectic.Prod.Basic` builds the direct sums `ω₁.prod ω₂` and `J₁.prod J₂` on
the bare product `V × W`. When `V` and `W` are real inner product spaces, the inner product of
the direct sum lives on the Euclidean product `WithLp 2 (V × W)`. This file transports both direct
sums there and shows that if each `ωᵢ` is compatible with the inner product of its factor through
`Jᵢ`, in the sense `ωᵢ(v, Jᵢ w) = ⟪v, w⟫`, then so is the transported direct sum. It also records
this compatibility for the area form and multiplication by `i` on `ℂ`.

These are the compatible linear models used when a product target, such as the graph
`ℂ × V` of a Floer solution in Gromov's construction, is fed into results stated for one fixed
compatible pair on a Euclidean space.

## Main declarations

* `TauCeti.SymplecticForm.prod_transport_withLp_apply`: the transported direct-sum form evaluates
  as the sum of the factor forms on the components.
* `TauCeti.SymplecticForm.prod_transport_withLp_apply_transport`: the transported direct sum of
  compatible pairs is compatible with the `L²` inner product.
* `TauCeti.stdComplexSymplecticForm_apply_ofComplexModule_eq_inner`: the area form of `ℂ` is
  compatible with the real inner product through multiplication by `i`.
-/

public section

namespace TauCeti

open Complex

/-- The area form of `ℂ` paired with multiplication by `i` is the real inner product. -/
theorem stdComplexSymplecticForm_apply_ofComplexModule_eq_inner (z w : ℂ) :
    stdComplexSymplecticForm z (AlmostComplexStructure.ofComplexModule ℂ w) = inner ℝ z w := by
  simp [AlmostComplexStructure.ofComplexModule_apply, Complex.inner, Complex.mul_re]
  ring

namespace SymplecticForm

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The direct sum of `ω₁` and `ω₂`, transported to the Euclidean product `WithLp 2 (V × W)`,
is the sum of the factor forms on the components. -/
theorem prod_transport_withLp_apply (ω₁ : SymplecticForm V) (ω₂ : SymplecticForm W)
    (p q : WithLp 2 (V × W)) :
    (ω₁.prod ω₂).transport (WithLp.linearEquiv 2 ℝ (V × W)).symm p q =
      ω₁ p.fst q.fst + ω₂ p.snd q.snd := by
  simp

/-- **Direct sums of compatible pairs on the Euclidean product.** If `ω₁(v, J₁ w) = ⟪v, w⟫` on
`V` and `ω₂(v, J₂ w) = ⟪v, w⟫` on `W`, then the direct sums of the forms and of the complex
structures, transported to `WithLp 2 (V × W)`, satisfy the same identity for the `L²` inner
product. -/
theorem prod_transport_withLp_apply_transport {ω₁ : SymplecticForm V} {ω₂ : SymplecticForm W}
    {J₁ : AlmostComplexStructure V} {J₂ : AlmostComplexStructure W}
    (h₁ : ∀ v w, ω₁ v (J₁ w) = inner ℝ v w) (h₂ : ∀ v w, ω₂ v (J₂ w) = inner ℝ v w)
    (p q : WithLp 2 (V × W)) :
    (ω₁.prod ω₂).transport (WithLp.linearEquiv 2 ℝ (V × W)).symm p
        ((J₁.prod J₂).transport (WithLp.linearEquiv 2 ℝ (V × W)).symm q) = inner ℝ p q := by
  simp [h₁, h₂, WithLp.prod_inner_apply]

end SymplecticForm

end TauCeti
