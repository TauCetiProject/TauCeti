/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Descent
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic

/-!
# The standard almost complex structure on a torus of two circles

For positive periods `p` and `q`, the torus `T = ℝ / pℤ × ℝ / qℤ` is the quotient of the plane
`ℝ × ℝ` by the lattice `pℤ × qℤ`, and the quotient map `(s, t) ↦ ([s], [t])` is a surjective smooth
local diffeomorphism whose differential is the identity of `ℝ × ℝ` in the charts of `T`. The
standard complex structure `(a, b) ↦ (-b, a)` of the plane is invariant under translations, so it
descends to a smooth almost complex structure
`TauCeti.SmoothAlmostComplexStructure.addCircleProd p q` on `T`. In the coordinates of `T` it sends
`a ∂_s + b ∂_t` to `-b ∂_s + a ∂_t`, so `∂_s ↦ ∂_t` and `∂_t ↦ -∂_s`. This is the complex structure
of the torus `ℂ / (pℤ + i qℤ)`, read in the real coordinates `s + i t`.

It is the domain structure of pseudoholomorphic tori parametrized by two circle coordinates, such
as the tori `(s, θ) ↦ (s, γ θ)` over closed orbits `γ` of the suspension flow of a mapping torus.

## Main definitions

* `TauCeti.SmoothAlmostComplexStructure.addCircleProd p q`: the standard almost complex structure
  on `AddCircle p × AddCircle q`.

## Main results

* `TauCeti.SmoothAlmostComplexStructure.addCircleProd_apply`: it sends `a ∂_s + b ∂_t` to
  `-b ∂_s + a ∂_t`.
* `TauCeti.SmoothAlmostComplexStructure.isPseudoholomorphic_prodMap_coe`: the quotient map
  `ℝ × ℝ → AddCircle p × AddCircle q` is pseudoholomorphic for the standard structure of the plane.
* `TauCeti.SmoothAlmostComplexStructure.eq_addCircleProd_iff`: the standard structure is the only
  almost complex structure on the torus for which the quotient map is pseudoholomorphic.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.2 (almost complex structures).
-/

public noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothAlmostComplexStructure

variable (p q : ℝ) [Fact (0 < p)] [Fact (0 < q)]

/-- Tangent vectors at equal points of the torus with the same coordinates in `ℝ × ℝ` keep equal
coordinates after applying a map of `ℝ × ℝ`. -/
private theorem tangentSpaceProdEquiv_symm_map_eq {y y' : AddCircle p × AddCircle q} (hy : y = y')
    (f : ℝ × ℝ → ℝ × ℝ) {u u' : ℝ × ℝ}
    (h : (Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓘(ℝ)) y).symm u =
      (Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓘(ℝ)) y').symm u') :
    (Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓘(ℝ)) y).symm (f u) =
      (Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓘(ℝ)) y').symm (f u') := by
  subst hy
  obtain rfl := (Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓘(ℝ)) y).symm.injective h
  rfl

/-- The standard almost complex structure on the torus `AddCircle p × AddCircle q`, descended from
the standard structure `(a, b) ↦ (-b, a)` of the plane along the quotient map. In the coordinates
of the torus it sends `a ∂_s + b ∂_t` to `-b ∂_s + a ∂_t`
(`TauCeti.SmoothAlmostComplexStructure.addCircleProd_apply`). -/
def addCircleProd :
    SmoothAlmostComplexStructure (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle p × AddCircle q) :=
  descend (AddCircle.isLocalDiffeomorph_prodMap_coe p q ∞) (AddCircle.surjective_prodMap_coe p q)
    (AlmostComplexStructure.product ℝ).constSmooth fun x x' v v' hx h ↦ by
      -- The differentials of the quotient map are the identity of `ℝ × ℝ`, and the standard
      -- structure of the plane is constant.
      rw [AddCircle.mfderiv_prodMap_coe_apply, AddCircle.mfderiv_prodMap_coe_apply] at h ⊢
      rw [AlmostComplexStructure.fromTangentSpace_constSmooth_apply,
        AlmostComplexStructure.fromTangentSpace_constSmooth_apply]
      exact tangentSpaceProdEquiv_symm_map_eq p q hx _ h

/-- The differentials of the quotient map are complex linear. -/
private theorem addCircleProd_apply_mfderiv (z : ℝ × ℝ) (w : TangentSpace 𝓘(ℝ, ℝ × ℝ) z) :
    addCircleProd p q (Prod.map ((↑) : ℝ → AddCircle p) ((↑) : ℝ → AddCircle q) z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ))
          (Prod.map ((↑) : ℝ → AddCircle p) ((↑) : ℝ → AddCircle q)) z w) =
      mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ))
        (Prod.map ((↑) : ℝ → AddCircle p) ((↑) : ℝ → AddCircle q)) z
        ((AlmostComplexStructure.product ℝ).constSmooth z w) :=
  descend_apply_mfderiv _ _ _ _ z w

/-- The quotient map `ℝ × ℝ → AddCircle p × AddCircle q` is pseudoholomorphic, for the standard
structure of the plane and the standard structure of the torus. -/
theorem isPseudoholomorphic_prodMap_coe :
    IsPseudoholomorphic (AlmostComplexStructure.product ℝ).constSmooth (addCircleProd p q)
      (Prod.map ((↑) : ℝ → AddCircle p) ((↑) : ℝ → AddCircle q)) :=
  isPseudoholomorphic_iff.2 fun z ↦ isPseudoholomorphicAt_iff_mfderiv.2
    ⟨(AddCircle.isLocalDiffeomorph_prodMap_coe p q ∞ z).mdifferentiableAt (by simp),
      fun w ↦ (addCircleProd_apply_mfderiv p q z w).symm⟩

/-- The standard structure is the only almost complex structure on the torus for which the
quotient map `ℝ × ℝ → AddCircle p × AddCircle q` is pseudoholomorphic. -/
theorem eq_addCircleProd_iff
    (K : SmoothAlmostComplexStructure (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle p × AddCircle q)) :
    K = addCircleProd p q ↔
      IsPseudoholomorphic (AlmostComplexStructure.product ℝ).constSmooth K
        (Prod.map ((↑) : ℝ → AddCircle p) ((↑) : ℝ → AddCircle q)) := by
  refine ⟨fun h ↦ h ▸ isPseudoholomorphic_prodMap_coe p q, fun h ↦ ?_⟩
  refine (eq_descend_iff (AddCircle.isLocalDiffeomorph_prodMap_coe p q ∞)
    (AddCircle.surjective_prodMap_coe p q) _ _ K).2 fun z v ↦ ?_
  exact ((isPseudoholomorphic_iff.1 h z).mfderiv_apply_commute v).symm

/-- In the coordinates of the torus, the standard structure sends `a ∂_s + b ∂_t` to
`-b ∂_s + a ∂_t`. -/
theorem addCircleProd_apply (z : AddCircle p × AddCircle q) (a b : ℝ) :
    addCircleProd p q z ((Manifold.tangentSpaceProdEquiv z).symm (a, b)) =
      (Manifold.tangentSpaceProdEquiv z).symm (-b, a) := by
  obtain ⟨w, rfl⟩ := AddCircle.surjective_prodMap_coe p q z
  have h := addCircleProd_apply_mfderiv p q w ((NormedSpace.fromTangentSpace w).symm (a, b))
  rw [AddCircle.mfderiv_prodMap_coe_apply, AddCircle.mfderiv_prodMap_coe_apply,
    AlmostComplexStructure.fromTangentSpace_constSmooth_apply,
    ContinuousLinearEquiv.apply_symm_apply, AlmostComplexStructure.product_apply] at h
  exact h

end TauCeti.SmoothAlmostComplexStructure
