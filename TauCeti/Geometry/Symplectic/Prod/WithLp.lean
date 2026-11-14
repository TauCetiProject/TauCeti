/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Geometry.Symplectic.Prod.Basic
public import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# Direct sums of compatible pairs on the Euclidean product

`TauCeti.Geometry.Symplectic.Prod.Basic` builds the direct sums `ω₁.prod ω₂` and `J₁.prod J₂` on
the bare product `V × W`. When `V` and `W` are real inner product spaces, the inner product of
the direct sum lives on the Euclidean product `WithLp 2 (V × W)`. This file transports both direct
sums there and shows that if each `ωᵢ` is compatible with the inner product of its factor through
`Jᵢ`, in the sense `ωᵢ(v, Jᵢ w) = ⟪v, w⟫`, then so is the transported direct sum.

These are the compatible linear models used when a product target, such as the graph
`ℂ × V` of a Floer solution in Gromov's construction, is fed into results stated for one fixed
compatible pair on a Euclidean space.

## Main declarations

* `TauCeti.SymplecticForm.prod_transport_withLpLinearEquiv_symm_apply_prod_transport_eq_inner`:
  the transported direct sum of compatible pairs is compatible with the `L²` inner product.
-/

public section

namespace TauCeti

namespace SymplecticForm

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- **Direct sums of compatible pairs on the Euclidean product.** If `ω₁(v, J₁ w) = ⟪v, w⟫` on
`V` and `ω₂(v, J₂ w) = ⟪v, w⟫` on `W`, then the direct sums of the forms and of the complex
structures, transported to `WithLp 2 (V × W)`, satisfy the same identity for the `L²` inner
product. -/
theorem prod_transport_withLpLinearEquiv_symm_apply_prod_transport_eq_inner
    {ω₁ : SymplecticForm V} {ω₂ : SymplecticForm W}
    {J₁ : AlmostComplexStructure V} {J₂ : AlmostComplexStructure W}
    (h₁ : ∀ v w, ω₁ v (J₁ w) = inner ℝ v w) (h₂ : ∀ v w, ω₂ v (J₂ w) = inner ℝ v w)
    (p q : WithLp 2 (V × W)) :
    (ω₁.prod ω₂).transport (WithLp.linearEquiv 2 ℝ (V × W)).symm p
        ((J₁.prod J₂).transport (WithLp.linearEquiv 2 ℝ (V × W)).symm q) = inner ℝ p q := by
  simp [h₁, h₂, WithLp.prod_inner_apply]

end SymplecticForm

end TauCeti
