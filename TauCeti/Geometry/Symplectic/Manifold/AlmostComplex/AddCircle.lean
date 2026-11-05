/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Descent

/-!
# The standard almost complex structure on a product of two circles

For positive periods `p` and `q`, the torus `ℝ / pℤ × ℝ / qℤ` is the quotient of the plane
`ℝ × ℝ` by the lattice `pℤ × qℤ`, and the quotient map `(s, t) ↦ ([s], [t])` is a surjective
smooth local diffeomorphism whose differential is the identity in the real coordinates of the
two circles. The standard complex structure `(a, b) ↦ (-b, a)` of the plane is invariant under
translations, so it descends to a smooth almost complex structure on the torus,
`TauCeti.SmoothAlmostComplexStructure.addCircleProd p q`. It sends the direction `∂_s` of the
first circle to the direction `∂_t` of the second, and `∂_t` to `-∂_s`.

These are the source tori `(s, t) ↦ (s, [t, x])` over periodic orbits in a symplectic suspension
`(ℝ / ℤ) × Y_φ`, which are pseudoholomorphic for the block almost complex structures sending `∂_s`
to the suspension vector field.

## Main definitions

* `TauCeti.SmoothAlmostComplexStructure.addCircleProd p q`: the almost complex structure
  `a ∂_s + b ∂_t ↦ -b ∂_s + a ∂_t` on `AddCircle p × AddCircle q`.

## Main results

* `TauCeti.SmoothAlmostComplexStructure.addCircleProd_apply_symm`: its value in the real
  coordinates of the two circles, which determines it.
* `TauCeti.SmoothAlmostComplexStructure.addCircleProd_apply`: the same formula
  `v ↦ (-v.2, v.1)` for a tangent vector viewed directly as a pair, in simp-normal form.
* `TauCeti.SmoothAlmostComplexStructure.isPseudoholomorphic_prodMap_coe`: the quotient map
  `ℝ × ℝ → AddCircle p × AddCircle q` is pseudoholomorphic for the standard structure of the plane.
* `TauCeti.SmoothAlmostComplexStructure.eq_addCircleProd_iff`: the standard structure is the only
  almost complex structure on the torus for which the quotient map is pseudoholomorphic.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.2 (almost complex structures and the standard structure of the plane).
-/

public noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothAlmostComplexStructure

variable (p q : ℝ) [Fact (0 < p)] [Fact (0 < q)]

/-- The standard structure of the plane respects the identifications of the quotient map
`ℝ × ℝ → AddCircle p × AddCircle q`. -/
private theorem product_respects ⦃z z' : ℝ × ℝ⦄ (v : TangentSpace 𝓘(ℝ, ℝ × ℝ) z)
    (v' : TangentSpace 𝓘(ℝ, ℝ × ℝ) z')
    (_ : Prod.map ((↑) : ℝ → AddCircle p) ((↑) : ℝ → AddCircle q) z =
      Prod.map ((↑) : ℝ → AddCircle p) ((↑) : ℝ → AddCircle q) z')
    (hvv' : mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ))
        (Prod.map ((↑) : ℝ → AddCircle p) ((↑) : ℝ → AddCircle q)) z v =
      mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ))
        (Prod.map ((↑) : ℝ → AddCircle p) ((↑) : ℝ → AddCircle q)) z' v') :
    mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ))
        (Prod.map ((↑) : ℝ → AddCircle p) ((↑) : ℝ → AddCircle q)) z (product ℝ z v) =
      mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ))
        (Prod.map ((↑) : ℝ → AddCircle p) ((↑) : ℝ → AddCircle q)) z' (product ℝ z' v') := by
  -- Both differentials are the identity, so `v = v'` and the claim is `J v = J v'`. The identity
  -- of `ℝ × ℝ` is applied here to tangent vectors, which `ContinuousLinearMap.id_apply` does not
  -- match syntactically; it reduces to them by definition.
  simp only [AddCircle.mfderiv_prodMap_coe] at hvv' ⊢
  exact (product_apply z v).trans
    ((congrArg (fun w : ℝ × ℝ ↦ (-w.2, w.1)) hvv').trans (product_apply z' v').symm)

/-- The standard almost complex structure on the product `AddCircle p × AddCircle q` of two
circles: in the real coordinates of the circles it sends `a ∂_s + b ∂_t` to `-b ∂_s + a ∂_t`
(`TauCeti.SmoothAlmostComplexStructure.addCircleProd_apply_symm`). It is the descent of the standard
structure `(a, b) ↦ (-b, a)` of the plane along `(s, t) ↦ ([s], [t])`. -/
def addCircleProd : SmoothAlmostComplexStructure (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle p × AddCircle q) :=
  descend (AddCircle.isLocalDiffeomorph_prodMap_coe p q ∞) (AddCircle.prodMap_coe_surjective p q)
    (product ℝ) (product_respects p q)

/-- In the real coordinates of the two circles, the standard almost complex structure of
`AddCircle p × AddCircle q` sends `a ∂_s + b ∂_t` to `-b ∂_s + a ∂_t`. -/
-- Not a `simp` lemma: `simp` first erases `Manifold.tangentSpaceProdEquiv` from the left-hand side
-- through `Manifold.tangentSpaceProdEquiv_symm_apply`.
theorem addCircleProd_apply_symm (x : AddCircle p × AddCircle q) (a b : ℝ) :
    addCircleProd p q x ((Manifold.tangentSpaceProdEquiv x).symm (a, b)) =
      (Manifold.tangentSpaceProdEquiv x).symm (-b, a) := by
  obtain ⟨z, rfl⟩ := AddCircle.prodMap_coe_surjective p q x
  have h := descend_apply_mfderiv (AddCircle.isLocalDiffeomorph_prodMap_coe p q ∞)
    (AddCircle.prodMap_coe_surjective p q) (product ℝ) (product_respects p q) z (a, b)
  rw [Manifold.tangentSpaceProdEquiv_symm_apply, Manifold.tangentSpaceProdEquiv_symm_apply]
  -- Both differentials in `h` are the identity of `ℝ × ℝ`, which reduces to its argument.
  simp only [AddCircle.mfderiv_prodMap_coe] at h
  exact h.trans (product_apply z (a, b))

/-- The standard almost complex structure of `AddCircle p × AddCircle q` sends a tangent vector
`v = (a, b)`, written in the real coordinates of the two circles, to `(-b, a)`. This is the
simp-normal form of `TauCeti.SmoothAlmostComplexStructure.addCircleProd_apply_symm`. -/
@[simp]
theorem addCircleProd_apply (x : AddCircle p × AddCircle q)
    (v : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) x) :
    addCircleProd p q x v = (-v.2, v.1) := by
  have h := addCircleProd_apply_symm p q x v.1 v.2
  rw [Manifold.tangentSpaceProdEquiv_symm_apply, Manifold.tangentSpaceProdEquiv_symm_apply] at h
  -- `h` is the claim for the pair `(v.1, v.2)`, which is `v` by eta.
  exact h

/-- The quotient map `ℝ × ℝ → AddCircle p × AddCircle q` is pseudoholomorphic, for the standard
structure of the plane and the standard structure of the torus. -/
theorem isPseudoholomorphic_prodMap_coe :
    IsPseudoholomorphic (product ℝ) (addCircleProd p q)
      (Prod.map ((↑) : ℝ → AddCircle p) ((↑) : ℝ → AddCircle q)) :=
  isPseudoholomorphic_descend _ _ _ (product_respects p q)

/-- The standard structure is the only almost complex structure on the torus for which the
quotient map `ℝ × ℝ → AddCircle p × AddCircle q` is pseudoholomorphic. -/
theorem eq_addCircleProd_iff
    (K : SmoothAlmostComplexStructure (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle p × AddCircle q)) :
    K = addCircleProd p q ↔
      IsPseudoholomorphic (product ℝ) K
        (Prod.map ((↑) : ℝ → AddCircle p) ((↑) : ℝ → AddCircle q)) :=
  eq_descend_iff_isPseudoholomorphic _ _ _ (product_respects p q) K

end TauCeti.SmoothAlmostComplexStructure
