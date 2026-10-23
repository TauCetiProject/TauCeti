/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Cone.Orbit.Basic

/-!
# Dimension of an affine toric orbit

For a face of a regular cone, the vanishing ray coordinates are exactly the rays of the
face. Thus the complex dimension of its affine orbit is the rank of the lattice minus
the number of those rays. The count is independent of the basis extending the primitive
ray generators and of the monomial generators used to topologize the affine chart.

The orbit model and its complex manifold structure are constructed in `Orbit.Basic`.

## References

* W. Fulton, *Introduction to Toric Varieties*, §3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.2.
-/

public section

namespace TauCeti.Toric

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

/-- The complex dimension of an affine torus orbit is the lattice rank minus the real
dimension of its indexing face. The left side is the dimension of the complex vector
space used by the orbit's manifold charts. -/
theorem finrank_affineConeOrbit_model
    (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ)
    (b : Module.Basis (ToricRay σ ⊕ ι) ℤ N) (F : σ.Face) :
    Module.finrank ℂ
        (({ρ : ToricRay σ // ρ ∉ hσ.faceOrderIso hi F} → ℂ) × (ι → ℂ)) =
      Module.finrank ℤ N -
        Module.finrank ℝ (Submodule.span ℝ (F.toPointedCone : Set V)) := by
  rw [IsRegularCone.finrank_span_face_eq_card_rays hi hσ F]
  let _ : Module.Finite ℤ N := hi.finite
  let _ : Finite (ToricRay σ) := ToricRay.finite_of_fg hσ.fg
  let _ : Finite (ToricRay σ ⊕ ι) := Module.Finite.finite_basis b
  let _ : Finite ι := Finite.sum_right (ToricRay σ) (β := ι)
  classical
  let _ : Fintype (ToricRay σ) := Fintype.ofFinite _
  let _ : Fintype ι := Fintype.ofFinite _
  have hrank : Module.finrank ℤ N = Fintype.card (ToricRay σ) + Fintype.card ι := by
    simpa [Fintype.card_sum] using (Module.finrank_eq_card_basis b)
  rw [Nat.card_eq_fintype_card, Module.finrank_prod, Module.finrank_pi, Module.finrank_pi,
    Fintype.card_subtype_compl, hrank]
  have hle : Fintype.card {ρ : ToricRay σ // ρ ∈ hσ.faceOrderIso hi F} ≤
      Fintype.card (ToricRay σ) := Fintype.card_subtype_le _
  omega

end TauCeti.Toric
