/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.InvariantForm
public import TauCeti.Geometry.Lie.Adjoint.Derivation
public import TauCeti.Geometry.Lie.Adjoint.Representation.Basic
public import TauCeti.RepresentationTheory.InvariantForm
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

* `TauCeti.Lie.lieInvariant_of_isInvariantForm`: a bilinear form invariant under `Ad` is invariant
  under `ad`, in the sense of Mathlib's `LinearMap.BilinForm.lieInvariant`.
* `TauCeti.Lie.exists_isSymm_bilinForm_Ad_invariant`: the Lie algebra of a compact Lie group has
  an `Ad`-invariant symmetric positive-definite bilinear form.
* `LeftInvariantDerivation.exists_Ad_lie_eq_zero`: **Hunt's lemma**, for `X Y : 𝔤` in the Lie
  algebra of a compact Lie group, some adjoint translate of `X` brackets to zero with `Y`.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter II, § 1.
* G. A. Hunt, *A theorem of Élie Cartan*, Proc. Amer. Math. Soc. **7** (1956), 307–308.
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
theorem lieInvariant_of_isInvariantForm
    {B : LinearMap.BilinForm ℝ (LeftInvariantDerivation I G)}
    (hB : Representation.IsInvariantForm
      (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation B) :
    B.lieInvariant (LeftInvariantDerivation I G) := by
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  have hAd : ∀ g X Y, B (Ad (I := I) g X) (Ad (I := I) g Y) = B X Y := fun g X Y ↦ by
    rw [← continuousAdjointRepresentation_apply, ← continuousAdjointRepresentation_apply]
    exact hB.apply g X Y
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
    have h := hAd (lieExp (I := I) (s • Z)) X (Ad (I := I) (lieExp (I := I) (s • -Z)) Y)
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
      (∀ X, X ≠ 0 → 0 < B X X) ∧ Representation.IsInvariantForm
        (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation B := by
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  exact ContRepresentation.exists_isSymm_bilinForm_invariant _
    (contMDiff_continuousAdjointRepresentation (I := I) (G := G)).continuous

/-- **Hunt's lemma.** For `X` and `Y` in the Lie algebra of a compact Lie group, some adjoint
translate of `X` brackets to zero with `Y`. -/
theorem _root_.LeftInvariantDerivation.exists_Ad_lie_eq_zero [CompactSpace G]
    (X Y : LeftInvariantDerivation I G) :
    ∃ g : G, ⁅Ad (I := I) g X, Y⁆ = 0 := by
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  obtain ⟨B, -, hpos, hAd⟩ := exists_isSymm_bilinForm_Ad_invariant (I := I) (G := G)
  have hinv := lieInvariant_of_isInvariantForm hAd
  -- Let `g` maximize `g ↦ B (Ad g X) Y` over the compact group.
  let φ := LinearMap.toContinuousLinearMap (B.flip Y)
  have hcont : Continuous fun g : G ↦ φ (Ad (I := I) g X) :=
    φ.continuous.comp ((contMDiff_Ad_apply (I := I) (G := G)).continuous.comp
      (continuous_id.prodMk continuous_const))
  obtain ⟨g, -, hg⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn
  refine ⟨g, ?_⟩
  set X' := Ad (I := I) g X with hX'
  set Z := ⁅X', Y⁆
  -- Along the one-parameter subgroup of `Z`, the value at `g` is still maximal.
  have hmax : IsLocalMax (fun s : ℝ ↦ φ (Ad (I := I) (lieExp (I := I) (s • Z)) X')) 0 := by
    refine Filter.Eventually.of_forall fun s ↦ ?_
    have := hg (Set.mem_univ (lieExp (I := I) (s • Z) * g))
    simpa [hX', Ad_mul] using this
  have hderiv := φ.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_Ad_lieExp_smul_apply_zero (I := I) Z X')
  have hzero : B ⁅Z, X'⁆ Y = 0 := by
    simpa [φ] using hmax.hasDerivAt_eq_zero hderiv
  -- By invariance the derivative at the maximum is `B Z Z`.
  have hnorm : B Z Z = 0 := by
    have h := hinv X' Z Y
    rw [← lie_skew, map_neg, LinearMap.neg_apply, hzero, neg_zero] at h
    exact neg_eq_zero.mp h.symm
  by_contra hne
  exact (hpos Z hne).ne' hnorm

end TauCeti.Lie
