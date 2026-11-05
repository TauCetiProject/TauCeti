/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.InvariantForm
public import TauCeti.Geometry.Lie.Adjoint.Derivation
public import TauCeti.Geometry.Lie.Adjoint.Infinitesimal
public import TauCeti.Geometry.Lie.Adjoint.Representation.Basic
public import TauCeti.RepresentationTheory.InvariantForm
import TauCeti.Geometry.Lie.Exponential.Derivative.Basic
import TauCeti.Geometry.Lie.Subgroup.LieAlgebra
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.RepresentationTheory.Compact.Unitarizable

/-!
# Invariant forms on the Lie algebra of a Lie group

The Lie algebra of a compact Lie group carries an inner product invariant under the adjoint
representation, obtained by averaging over the group. Differentiating the invariance along a
one-parameter subgroup shows that each `ad X` is skew for such a form. This is the form that
turns a critical point of an adjoint orbit into a vanishing bracket, the argument behind the
conjugacy of maximal tori.

The tangent-algebra API also characterizes Ad-invariance by infinitesimal invariance on
connected groups, without symmetry or positivity assumptions. This connects the inner products
defining bi-invariant metrics with their Levi-Civita connection and curvature calculations.
It uses `TauCeti.Lie.hasDerivAt_tangentAd_mulInvariantExp_smul_apply_zero` for `d Ad = ad`.

## Main results

* `TauCeti.Lie.lieInvariant_of_isInvariantForm`: a bilinear form invariant under `Ad` is invariant
  under `ad`, in the sense of Mathlib's `LinearMap.BilinForm.lieInvariant`.
* `TauCeti.Lie.exists_isSymm_bilinForm_Ad_invariant`: the Lie algebra of a compact Lie group has
  an `Ad`-invariant symmetric positive-definite bilinear form.
* `LeftInvariantDerivation.exists_Ad_lie_eq_zero`: **Hunt's lemma**, for `X Y : 𝔤` in the Lie
  algebra of a compact Lie group, some adjoint translate of `X` brackets to zero with `Y`.
* `TauCeti.Lie.lieInvariant_iff_adjoint_invariant`: on a connected group, tangent bilinear forms
  are infinitesimally invariant exactly when they are Ad-invariant.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 3.
* J. Milnor, *Curvatures of left invariant metrics on Lie groups*, Advances in Math. 21
  (1976), 293–329.
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

public noncomputable section

open Manifold
open scoped ContDiff Manifold

namespace TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {b : GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G →L[ℝ] ℝ}

/-- Along an exponential line, the derivative at zero of a bilinear form applied to two
adjoint orbits is the sum of its two Lie-bracket terms. -/
theorem _root_.ContinuousLinearMap.hasDerivAt_tangentAd_mulInvariantExp_smul_zero
    (b : GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G →L[ℝ] ℝ)
    (X Y Z : GroupLieAlgebra I G) :
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    HasDerivAt (fun t : ℝ ↦ b (tangentAd (mulInvariantExp (t • X)) Y)
      (tangentAd (mulInvariantExp (t • X)) Z)) (b Y ⁅X, Z⁆ + b ⁅X, Y⁆ Z) 0 := by
  let : T2Space G := I.t2Space_of_lieGroup ∞
  let : NormedAddCommGroup (GroupLieAlgebra I G) := inferInstanceAs (NormedAddCommGroup E)
  let : NormedSpace ℝ (GroupLieAlgebra I G) := inferInstanceAs (NormedSpace ℝ E)
  have hY := hasDerivAt_tangentAd_mulInvariantExp_smul_apply_zero (I := I) X Y
  have hZ := hasDerivAt_tangentAd_mulInvariantExp_smul_apply_zero (I := I) X Z
  convert! ContinuousLinearMap.hasDerivAt_of_bilinear (B := b)
    (fun _ ↦ hY) (fun _ ↦ hZ) using 1
  simp only [zero_smul, mulInvariantExp_zero, tangentAd_one, LieEquiv.refl_apply,
    LieAlgebra.ad_apply]
  -- The derivative theorem uses `show E from` for each tangent vector. Here the tangent Lie
  -- algebra has exactly the model's norm instances, so the remaining model/tangent casts reduce.
  rfl

/-- An Ad-invariant bilinear form is invariant under the tangent Lie algebra. The group may
be disconnected, and the form need not be symmetric or nondegenerate. -/
theorem lieInvariant_of_adjoint_invariant
    (hb : ∀ (g : G) (Y Z : GroupLieAlgebra I G),
      b (adjointContinuousLinearMap g Y) (adjointContinuousLinearMap g Z) = b Y Z) :
    b.toBilinForm.lieInvariant (GroupLieAlgebra I G) := by
  let : T2Space G := I.t2Space_of_lieGroup ∞
  intro X Y Z
  have h := b.hasDerivAt_tangentAd_mulInvariantExp_smul_zero X Y Z
  have heq : (fun t : ℝ ↦ b (tangentAd (mulInvariantExp (t • X)) Y)
      (tangentAd (mulInvariantExp (t • X)) Z)) = fun _ ↦ b Y Z := by
    funext t
    simpa only [tangentAd_apply] using hb (mulInvariantExp (t • X)) Y Z
  rw [heq] at h
  simp only [ContinuousLinearMap.toBilinForm_apply]
  linarith [h.unique (hasDerivAt_const 0 (b Y Z))]

/-- On a connected Lie group, an infinitesimally invariant bilinear form is Ad-invariant. -/
theorem adjoint_invariant_of_lieInvariant [PreconnectedSpace G]
    (hb : b.toBilinForm.lieInvariant (GroupLieAlgebra I G))
    (g : G) (Y Z : GroupLieAlgebra I G) :
    b (adjointContinuousLinearMap g Y) (adjointContinuousLinearMap g Z) = b Y Z := by
  let : T2Space G := I.t2Space_of_lieGroup ∞
  -- Use the model's normed-space structure for smoothness and bilinear precomposition.
  let : NormedAddCommGroup (GroupLieAlgebra I G) := inferInstanceAs (NormedAddCommGroup E)
  let : NormedSpace ℝ (GroupLieAlgebra I G) := inferInstanceAs (NormedSpace ℝ E)
  let : IsNormableSpace ℝ (GroupLieAlgebra I G) := inferInstanceAs (IsNormableSpace ℝ E)
  let f : G → ℝ := fun x ↦ b (tangentAd x Y) (tangentAd x Z)
  have hf : ContMDiff I 𝓘(ℝ) ∞ f :=
    (b.contMDiff.comp (contMDiff_tangentAd_apply_const (I := I) (G := G) Y)).clm_apply
      (contMDiff_tangentAd_apply_const (I := I) (G := G) Z)
  have hzero (x : G) : mfderiv I 𝓘(ℝ) f x = 0 := by
    ext v
    obtain ⟨X, rfl⟩ := exists_mulInvariantVectorField_eq v
    have hpath := (hf.mdifferentiable (by simp) x).hasMFDerivAt
      |>.hasDerivAt_comp_mul_mulInvariantExp_smul_zero X
    let A : GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G := adjointContinuousLinearMap (I := I) x
    have h : HasDerivAt (fun t : ℝ ↦ f (x * mulInvariantExp (t • X)))
        (b (tangentAd x Y) (tangentAd x ⁅X, Z⁆) +
          b (tangentAd x ⁅X, Y⁆) (tangentAd x Z)) 0 := by
      simpa only [ContinuousLinearMap.bilinearComp_apply, A, f, tangentAd_apply,
        adjointContinuousLinearMap_mul, ContinuousLinearMap.comp_apply] using
        (b.bilinearComp A A).hasDerivAt_tangentAd_mulInvariantExp_smul_zero X Y Z
    have hskew := hb (tangentAd x X) (tangentAd x Y) (tangentAd x Z)
    have hderiv : HasDerivAt (fun t : ℝ ↦ f (x * mulInvariantExp (t • X))) 0 0 := by
      apply h.congr_deriv
      simp only [LieEquiv.map_lie, ContinuousLinearMap.toBilinForm_apply] at hskew ⊢
      linarith
    exact hpath.unique hderiv
  have heq := (hf.mdifferentiable (by simp)).apply_eq_of_mfderiv_eq_zero hzero g 1
  simpa only [f, tangentAd_apply, adjointContinuousLinearMap_one,
    ContinuousLinearMap.id_apply] using heq

/-- On a connected Lie group, group-level and infinitesimal invariance of a bilinear form
are equivalent. -/
theorem lieInvariant_iff_adjoint_invariant [PreconnectedSpace G] :
    b.toBilinForm.lieInvariant (GroupLieAlgebra I G) ↔
      ∀ (g : G) (Y Z : GroupLieAlgebra I G),
        b (adjointContinuousLinearMap g Y) (adjointContinuousLinearMap g Z) = b Y Z :=
  ⟨adjoint_invariant_of_lieInvariant, lieInvariant_of_adjoint_invariant⟩

end TauCeti.Lie
