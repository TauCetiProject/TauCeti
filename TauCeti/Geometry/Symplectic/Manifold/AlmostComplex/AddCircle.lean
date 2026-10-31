/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Descent
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod

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

* `TauCeti.SmoothAlmostComplexStructure.addCircleProd_apply`: its value in the real coordinates
  of the two circles, which determines it.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.2 (almost complex structures and the standard structure of the plane).
-/

public noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothAlmostComplexStructure

variable (p q : ℝ)

/-- The quotient map `(s, t) ↦ ([s], [t])` from the plane onto the product of the circles of
periods `p` and `q`. -/
private def addCircleProdCover (z : ℝ × ℝ) : AddCircle p × AddCircle q :=
  ((z.1 : AddCircle p), (z.2 : AddCircle q))

private theorem addCircleProdCover_surjective : Surjective (addCircleProdCover p q) := by
  rintro ⟨x, y⟩
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective y
  exact ⟨(s, t), rfl⟩

variable [Fact (0 < p)] [Fact (0 < q)]

private theorem isLocalDiffeomorph_addCircleProdCover :
    IsLocalDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) ∞ (addCircleProdCover p q) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact IsLocalDiffeomorph.prodMap (AddCircle.isLocalDiffeomorph_coe p ∞)
    (AddCircle.isLocalDiffeomorph_coe q ∞)

/-- The quotient map has the identity as differential, in the real coordinates of the circles. -/
private theorem hasMFDerivAt_addCircleProdCover (z : ℝ × ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) (addCircleProdCover p q) z
      (ContinuousLinearMap.id ℝ (ℝ × ℝ)) := by
  have h : HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) (addCircleProdCover p q) z _ :=
    ((AddCircle.hasMFDerivAt_coe p z.1).comp z hasFDerivAt_fst.hasMFDerivAt).prodMk
      ((AddCircle.hasMFDerivAt_coe q z.2).comp z hasFDerivAt_snd.hasMFDerivAt)
  refine h.congr_mfderiv ?_
  -- Both sides send `(a, b)` to `(a, b)`.
  ext <;> rfl

private theorem mfderiv_addCircleProdCover_apply (z : ℝ × ℝ) (v : TangentSpace 𝓘(ℝ, ℝ × ℝ) z) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) (addCircleProdCover p q) z v = v := by
  rw [(hasMFDerivAt_addCircleProdCover p q z).mfderiv]
  rfl

/-- The standard structure of the plane respects the identifications of the quotient map. -/
private theorem product_respects ⦃z z' : ℝ × ℝ⦄ (v : TangentSpace 𝓘(ℝ, ℝ × ℝ) z)
    (v' : TangentSpace 𝓘(ℝ, ℝ × ℝ) z') (_ : addCircleProdCover p q z = addCircleProdCover p q z')
    (hvv' : mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) (addCircleProdCover p q) z v =
      mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) (addCircleProdCover p q) z' v') :
    mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) (addCircleProdCover p q) z (product ℝ z v) =
      mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) (addCircleProdCover p q) z' (product ℝ z' v') := by
  -- Both differentials are the identity, so `v = v'` and the claim is `J v = J v'`.
  have hv : v = v' := (mfderiv_addCircleProdCover_apply p q z v).symm.trans
    (hvv'.trans (mfderiv_addCircleProdCover_apply p q z' v'))
  refine (mfderiv_addCircleProdCover_apply p q z _).trans
    (Eq.trans ?_ (mfderiv_addCircleProdCover_apply p q z' _).symm)
  exact (product_apply z v).trans
    ((congrArg (fun w : ℝ × ℝ ↦ (-w.2, w.1)) hv).trans (product_apply z' v').symm)

/-- The standard almost complex structure on the product `AddCircle p × AddCircle q` of two
circles: in the real coordinates of the circles it sends `a ∂_s + b ∂_t` to `-b ∂_s + a ∂_t`
(`TauCeti.SmoothAlmostComplexStructure.addCircleProd_apply`). It is the descent of the standard
structure `(a, b) ↦ (-b, a)` of the plane along `(s, t) ↦ ([s], [t])`. -/
def addCircleProd : SmoothAlmostComplexStructure (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle p × AddCircle q) :=
  descend (isLocalDiffeomorph_addCircleProdCover p q) (addCircleProdCover_surjective p q)
    (product ℝ) (product_respects p q)

/-- In the real coordinates of the two circles, the standard almost complex structure of
`AddCircle p × AddCircle q` sends `a ∂_s + b ∂_t` to `-b ∂_s + a ∂_t`. -/
-- Not a `simp` lemma: `simp` first erases `Manifold.tangentSpaceProdEquiv` from the left-hand side
-- through `Manifold.tangentSpaceProdEquiv_symm_apply`.
theorem addCircleProd_apply (x : AddCircle p × AddCircle q) (a b : ℝ) :
    addCircleProd p q x ((Manifold.tangentSpaceProdEquiv x).symm (a, b)) =
      (Manifold.tangentSpaceProdEquiv x).symm (-b, a) := by
  obtain ⟨z, rfl⟩ := addCircleProdCover_surjective p q x
  have h := descend_apply_mfderiv (isLocalDiffeomorph_addCircleProdCover p q)
    (addCircleProdCover_surjective p q) (product ℝ) (product_respects p q) z (a, b)
  rw [Manifold.tangentSpaceProdEquiv_symm_apply, Manifold.tangentSpaceProdEquiv_symm_apply]
  -- Both differentials in `h` are the identity of `ℝ × ℝ`.
  exact (congrArg (addCircleProd p q (addCircleProdCover p q z))
    (mfderiv_addCircleProdCover_apply p q z (a, b)).symm).trans
      (h.trans ((mfderiv_addCircleProdCover_apply p q z _).trans (product_apply z (a, b))))

end TauCeti.SmoothAlmostComplexStructure
