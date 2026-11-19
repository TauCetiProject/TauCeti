/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Integral
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables
import TauCeti.Geometry.Manifold.Orientation.Pullback

/-!
# Volume of a Riemannian immersion

The **immersion volume** `TauCeti.immersionVolume` of an oriented smooth immersion `f : N → M` into
a Riemannian manifold `(M, g)` is defined as `integralTopForm o (riemannianVolumeForm o)` for the
pulled-back metric `f^* g`. On a compact source `N`, it equals the total Riemannian volume
`TauCeti.riemannianTotalVolume` of `N` equipped with `f^* g`
(`TauCeti.immersionVolume_eq_riemannianTotalVolume`); on a noncompact source `N`, it evaluates to
`0` by `TauCeti.integralTopForm`'s compact-support convention
(`TauCeti.immersionVolume_eq_zero_of_not_compactSpace`), even when `f^* g` has finite Riemannian
volume. In all cases it is independent of the choice of orientation on `N`
(`TauCeti.immersionVolume_congr_orientation`) and of the smoothness and injectivity witnesses of
equal maps (`TauCeti.immersionVolume_congr`).

## Main definitions

* `TauCeti.immersionVolume`: the top-form integral over `N` of the Riemannian volume form of the
  pulled-back Riemannian metric `f^* g`.

## Main results

* `TauCeti.immersionVolume_eq_riemannianTotalVolume` and
  `TauCeti.immersionVolume_eq_zero_of_not_compactSpace`: identification with
  `riemannianTotalVolume` on compact `N` and `0` fallback on noncompact `N`.
* `TauCeti.immersionVolume_congr_orientation`, `TauCeti.immersionVolume_congr`,
  `TauCeti.immersionVolume_neg`, `TauCeti.immersionVolume_nonneg`, and
  `TauCeti.immersionVolume_pos`: orientation independence, congruence under map equality,
  nonnegativity, and positivity on nonempty compact sources.
* `TauCeti.immersionVolume_comp_diffeomorph`: invariance of `immersionVolume` under arbitrary
  diffeomorphisms of the source.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (Riemannian submanifolds and immersions, pullback metrics, and induced volume forms).
-/

public section

noncomputable section

open Bundle Manifold
open scoped Bundle ContDiff Manifold

namespace TauCeti

section Immersions

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' 1 N]

/-- The volume of a smooth immersion `f : N → M` of an oriented `k`-manifold: the top-form integral
over `N`, against its orientation `o`, of the Riemannian volume form of the pulled-back metric
`f^* g`. On compact `N` this equals the total Riemannian volume of `f^* g`
(`immersionVolume_eq_riemannianTotalVolume`), whereas on noncompact `N` it returns `0` via
`integralTopForm`'s compact-support convention (`immersionVolume_eq_zero_of_not_compactSpace`). It
does not depend on the orientation chosen (`immersionVolume_congr_orientation`). -/
def immersionVolume {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) : ℝ :=
  letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
  integralTopForm o (riemannianVolumeForm o)

/-- Unfolding lemma for `immersionVolume`. -/
theorem immersionVolume_def {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    immersionVolume g f hf hinj o =
      letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
        ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
      integralTopForm o (riemannianVolumeForm o) :=
  (rfl)

/-- On a noncompact source `N`, `immersionVolume` evaluates to `0` via `integralTopForm`'s
compact-support fallback, because `riemannianVolumeForm` has support `Set.univ`. -/
theorem immersionVolume_eq_zero_of_not_compactSpace {k : ℕ} (hnc : ¬CompactSpace N)
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    immersionVolume g f hf hinj o = 0 := by
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
  rw [immersionVolume_def]
  exact integralTopForm_riemannianVolumeForm_eq_zero_of_not_compactSpace o hnc

/-- On a compact source `N`, `immersionVolume` equals the total Riemannian volume of `N` equipped
with the pulled-back metric `f^* g` (`WithMetric (g.pullback f hf hinj)`), in every degree
`k : ℕ`. -/
theorem immersionVolume_eq_riemannianTotalVolume [CompactSpace N] {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    immersionVolume g f hf hinj o =
      riemannianTotalVolume I' (WithMetric (g.pullback f hf hinj)) := by
  set g' := g.pullback f hf hinj
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) := ⟨g'.toRiemannianMetric⟩
  let Φ : WithMetric g' ≃ₘ^∞⟮I', I'⟯ N := WithMetric.diffeomorph g' ∞
  let oW : Manifold.Orientation I' (WithMetric g') (Fin k) :=
    o.pullback (Φ.contMDiff.of_le (by simp)) (fun x ↦ Φ.isInvertible_mfderiv (by simp)) o.card_eq
  have ho : ∀ x, oW.IsOrientationPreservingAt o Φ x :=
    o.isOrientationPreservingAt_pullback (Φ.contMDiff.of_le (by simp))
      (fun x ↦ Φ.isInvertible_mfderiv (by simp)) o.card_eq
  have hvol : mpullback I' I' Φ (riemannianVolumeForm o) = riemannianVolumeForm oW :=
    mpullback_riemannianVolumeForm_of_isOrientationPreservingAt ho fun x v w ↦ by
      rw [WithMetric.coe_diffeomorph, g'.inner_riemannianBundle]
      exact (WithMetric.inner_def x v w).symm
  let : MeasurableSpace (WithMetric g') := borel (WithMetric g')
  have : BorelSpace (WithMetric g') := ⟨rfl⟩
  rw [immersionVolume_def,
    ← Φ.toHomeomorph.isOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt ho
      (by simp),
    Φ.coe_toHomeomorph, hvol, integralTopForm_riemannianVolumeForm oW]

/-- `immersionVolume` is independent of the orientation chosen on `N` (even across disconnected
components). -/
theorem immersionVolume_congr_orientation {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o₁ o₂ : Manifold.Orientation I' N (Fin k)) :
    immersionVolume g f hf hinj o₁ = immersionVolume g f hf hinj o₂ := by
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E' (fun x : N ↦ TangentSpace I' x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I') (n := ∞)
  rw [immersionVolume_def, immersionVolume_def]
  exact integralTopForm_riemannianVolumeForm_congr o₁ o₂

/-- Equal immersions have the same `immersionVolume`, regardless of the smoothness proofs,
injectivity proofs, or source orientations supplied. -/
theorem immersionVolume_congr {k : ℕ}
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {f₁ f₂ : N → M} (h : f₁ = f₂)
    {hf₁ : ContMDiff I' I ∞ f₁} {hinj₁ : ∀ x, Function.Injective (mfderiv I' I f₁ x)}
    {hf₂ : ContMDiff I' I ∞ f₂} {hinj₂ : ∀ x, Function.Injective (mfderiv I' I f₂ x)}
    {o₁ o₂ : Manifold.Orientation I' N (Fin k)} :
    immersionVolume g f₁ hf₁ hinj₁ o₁ = immersionVolume g f₂ hf₂ hinj₂ o₂ := by
  subst h
  exact immersionVolume_congr_orientation g f₁ hf₁ hinj₁ o₁ o₂

/-- Reversing the orientation of the source does not change `immersionVolume`. -/
@[simp]
theorem immersionVolume_neg {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    immersionVolume g f hf hinj (-o) = immersionVolume g f hf hinj o :=
  immersionVolume_congr_orientation g f hf hinj (-o) o

/-- The volume of an oriented smooth immersion is nonnegative. -/
theorem immersionVolume_nonneg {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    0 ≤ immersionVolume g f hf hinj o := by
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
  rw [immersionVolume_def]
  exact integralTopForm_riemannianVolumeForm_nonneg o

/-- The volume of a nonempty compact oriented smooth immersion is positive. -/
theorem immersionVolume_pos [CompactSpace N] [Nonempty N] {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    0 < immersionVolume g f hf hinj o := by
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E' (fun x : N ↦ TangentSpace I' x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I') (n := ∞)
  rw [immersionVolume_def]
  exact integralTopForm_riemannianVolumeForm_pos o

section Transport

variable {E'' H'' N' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [FiniteDimensional ℝ E''] [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
  [TopologicalSpace N'] [ChartedSpace H'' N'] [IsManifold I'' 1 N']

/-- Precomposing an immersion with any diffeomorphism preserves `immersionVolume` (regardless of
whether the diffeomorphism preserves or reverses orientations). -/
theorem immersionVolume_comp_diffeomorph {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (Φ : N' ≃ₘ^∞⟮I'', I'⟯ N)
    (o' : Manifold.Orientation I'' N' (Fin k)) :
    immersionVolume g (f ∘ Φ) (hf.comp Φ.contMDiff)
        (fun x ↦ (Φ.mfderiv_comp_diffeomorph_injective_iff (by simp)).2 (hinj (Φ x))) o' =
      immersionVolume g f hf hinj o := by
  let oΦ : Manifold.Orientation I'' N' (Fin k) :=
    o.pullback (Φ.contMDiff.of_le (by simp)) (fun x ↦ Φ.isInvertible_mfderiv (by simp)) o'.card_eq
  have ho : ∀ x, oΦ.IsOrientationPreservingAt o Φ x :=
    o.isOrientationPreservingAt_pullback (Φ.contMDiff.of_le (by simp))
      (fun x ↦ Φ.isInvertible_mfderiv (by simp)) o'.card_eq
  rw [immersionVolume_congr_orientation g (f ∘ Φ) _ _ o' oΦ]
  set gN := g.pullback f hf hinj
  set gN' := g.pullback (f ∘ Φ) (hf.comp Φ.contMDiff)
    (fun x ↦ (Φ.mfderiv_comp_diffeomorph_injective_iff (by simp)).2 (hinj (Φ x)))
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) := ⟨gN.toRiemannianMetric⟩
  let : RiemannianBundle (fun x : N' ↦ TangentSpace I'' x) := ⟨gN'.toRiemannianMetric⟩
  have hvol : mpullback I'' I' Φ (riemannianVolumeForm o) = riemannianVolumeForm oΦ :=
    mpullback_riemannianVolumeForm_of_isOrientationPreservingAt ho fun x v w ↦ by
      rw [gN.inner_riemannianBundle, gN'.inner_riemannianBundle]
      exact (g.pullback_comp_inner _ (Φ.mdifferentiable (by simp) x) _ _ _ v w).symm
  rw [immersionVolume_def, immersionVolume_def, ← hvol, ← Φ.coe_toHomeomorph]
  exact Φ.toHomeomorph.isOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt ho
    (by simp)

end Transport

end Immersions

end TauCeti
