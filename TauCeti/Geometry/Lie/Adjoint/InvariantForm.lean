/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.InvariantForm
public import TauCeti.Geometry.Lie.Adjoint.Derivation
import TauCeti.Geometry.Lie.Adjoint.Representation.Basic
import TauCeti.Geometry.Lie.Subgroup.LieAlgebra
import TauCeti.RepresentationTheory.Compact.Unitarizable

/-!
# Invariant forms on the Lie algebra of a Lie group

The Lie algebra of a compact Lie group carries an inner product invariant under the adjoint
representation, obtained by averaging over the group. Differentiating the invariance along a
one-parameter subgroup shows that each `ad X` is skew for such a form. This is the form that
turns a critical point of an adjoint orbit into a vanishing bracket, the argument behind the
conjugacy of maximal tori.

## Main results

* `TauCeti.Lie.lieInvariant_of_forall_Ad_apply`: a bilinear form invariant under `Ad` is invariant
  under `ad`, in the sense of Mathlib's `LinearMap.BilinForm.lieInvariant`.
* `TauCeti.Lie.exists_isSymm_bilinForm_Ad_invariant`: the Lie algebra of a compact Lie group has
  an `Ad`-invariant symmetric positive-definite bilinear form.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter II, § 1.
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- **A form invariant under `Ad` is invariant under `ad`**: if
`B (Ad g X) (Ad g Y) = B X Y` for all `g`, then `B ⁅Z, X⁆ Y = -B X ⁅Z, Y⁆`. -/
theorem lieInvariant_of_forall_Ad_apply
    {B : LinearMap.BilinForm ℝ (LeftInvariantDerivation I G)}
    (hB : ∀ g X Y, B (Ad (I := I) g X) (Ad (I := I) g Y) = B X Y) :
    B.lieInvariant (LeftInvariantDerivation I G) := by
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  intro Z X Y
  -- Moving `Ad (exp (s • Z))` across the form inverts it; differentiate both sides at `s = 0`.
  have hleft := (LinearMap.toContinuousLinearMap (B.flip Y)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_Ad_lieExp_smul_apply_zero (I := I) Z X)
  have hright := (LinearMap.toContinuousLinearMap (B X)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_Ad_lieExp_smul_apply_zero (I := I) (-Z) Y)
  have hfun : (LinearMap.toContinuousLinearMap (B.flip Y)) ∘
        (fun s : ℝ ↦ Ad (I := I) (lieExp (I := I) (s • Z)) X) =
      (LinearMap.toContinuousLinearMap (B X)) ∘
        (fun s : ℝ ↦ Ad (I := I) (lieExp (I := I) (s • -Z)) Y) := by
    funext s
    have h := hB (lieExp (I := I) (s • Z)) X (Ad (I := I) (lieExp (I := I) (s • -Z)) Y)
    rw [smul_neg, lieExp_neg, Ad_inv, LieEquiv.apply_symm_apply] at h
    simpa [smul_neg, lieExp_neg, Ad_inv] using h
  rw [hfun] at hleft
  have h := hleft.unique hright
  rw [neg_lie, map_neg] at h
  simpa only [LinearMap.coe_toContinuousLinearMap', LinearMap.BilinForm.flip_apply] using h

/-- **The Lie algebra of a compact Lie group has an `Ad`-invariant inner product**, presented as a
symmetric positive-definite bilinear form. -/
theorem exists_isSymm_bilinForm_Ad_invariant [CompactSpace G] :
    ∃ B : LinearMap.BilinForm ℝ (LeftInvariantDerivation I G), B.IsSymm ∧
      (∀ X, X ≠ 0 → 0 < B X X) ∧ ∀ g X Y, B (Ad (I := I) g X) (Ad (I := I) g Y) = B X Y := by
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  simpa using ContRepresentation.exists_isSymm_bilinForm_invariant _
    (contMDiff_continuousAdjointRepresentation (I := I) (G := G)).continuous

end TauCeti.Lie
