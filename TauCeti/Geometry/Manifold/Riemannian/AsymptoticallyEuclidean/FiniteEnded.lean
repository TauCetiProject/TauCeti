/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic
public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Rescale
import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Asymptotics

/-!
# Finite-ended asymptotically Euclidean manifolds

A **finite-ended asymptotically Euclidean structure** of order `t` on an `n`-dimensional Riemannian
manifold `M` is a finite nonempty family of asymptotically Euclidean ends with pairwise disjoint
ranges whose union has compact complement. Requiring at least one end (`0 < numEnds`) excludes the
vacuous zero-end structure on compact manifolds.

## Main definitions

* `TauCeti.FiniteEndedAE`: a finite-ended asymptotically Euclidean structure of order `t`.
* `TauCeti.FiniteEndedAE.ofLe`: monotonicity in the decay order `t' ≤ t`.
* `TauCeti.FiniteEndedAE.compRiemannianIsometry`: pushforward along a smooth Riemannian isometry.
* `TauCeti.FiniteEndedAE.rescale`: constant metric rescaling `g ↦ c • g`.
* `TauCeti.FiniteEndedAE.euclidean`: the standard one-ended structure on flat `ℝⁿ`.

## Main results

* `TauCeti.FiniteEndedAE.isOpen_iUnion_range`: the union of the end ranges is open.
* `TauCeti.FiniteEndedAE.riemannianVolume_univ_eq_top`: every finite-ended asymptotically Euclidean
  manifold of positive order in dimension `1 ≤ n` has infinite Riemannian volume.
* `TauCeti.FiniteEndedAE.not_compactSpace`: no compact `C¹` manifold of dimension `1 ≤ n` with a
  continuous Riemannian metric admits a finite-ended asymptotically Euclidean structure of positive
  order.

## References

* R. Bartnik, *The mass of an asymptotically flat manifold*, Comm. Pure Appl. Math. 39 (1986),
  661–693.
* S. Cecchini and R. Zeidler, *The positive mass theorem and distance estimates in the spin
  setting*, Ann. Global Anal. Geom. 63 (2023), Definition 2.3.
-/

public section

noncomputable section

open Bundle MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff ENNReal Manifold Topology

namespace TauCeti

/-- A **finite-ended asymptotically Euclidean structure** of order `t` on an `n`-dimensional
Riemannian manifold `M`: a finite nonempty family of asymptotically Euclidean ends with pairwise
disjoint ranges whose union has compact complement. Requiring `0 < numEnds` excludes the vacuous
zero-end structure on compact manifolds. -/
structure FiniteEndedAE (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] (t : ℝ) where
  /-- The number of ends. -/
  numEnds : ℕ
  /-- There is at least one end. -/
  numEnds_pos : 0 < numEnds
  /-- The family of ends. -/
  ends : Fin numEnds → AsymptoticallyEuclideanEnd n M t
  /-- Distinct ends have disjoint ranges. -/
  pairwise_disjoint : Pairwise fun a b ↦
    Disjoint (Set.range (ends a).toFun) (Set.range (ends b).toFun)
  /-- The complement of the union of the end ranges is compact. -/
  isCompact_compl : IsCompact (⋃ a, Set.range (ends a).toFun)ᶜ

namespace FiniteEndedAE

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] {t : ℝ}

/-- Two finite-ended asymptotically Euclidean structures are equal if they have the same number of
ends and equal ends at each index. -/
@[ext (iff := false)]
theorem ext {A₁ A₂ : FiniteEndedAE n M t} (hn : A₁.numEnds = A₂.numEnds)
    (he : ∀ i : Fin A₁.numEnds, A₁.ends i = A₂.ends (i.cast hn)) : A₁ = A₂ := by
  cases A₁
  cases A₂
  dsimp only at hn he
  subst hn
  congr 1
  funext i
  exact he i

/-- For `1 ≤ n`, any manifold carrying a finite-ended asymptotically Euclidean structure is
nonempty. -/
theorem nonempty_of_pos (hn : 1 ≤ n) (A : FiniteEndedAE n M t) : Nonempty M :=
  (A.ends ⟨0, A.numEnds_pos⟩).nonempty_of_pos hn

/-- The union of the ranges of the ends is open in `M`. -/
theorem isOpen_iUnion_range [IsManifold (𝓡 n) 1 M] (A : FiniteEndedAE n M t) :
    IsOpen (⋃ a, Set.range (A.ends a).toFun) :=
  isOpen_iUnion fun a ↦ (A.ends a).isOpen_range

/-- A finite-ended asymptotically Euclidean structure of order `t` is also one of every smaller
order `t' ≤ t`. -/
def ofLe (A : FiniteEndedAE n M t) {t' : ℝ} (ht : t' ≤ t) : FiniteEndedAE n M t' where
  numEnds := A.numEnds
  numEnds_pos := A.numEnds_pos
  ends := fun a ↦ (A.ends a).ofLe ht
  pairwise_disjoint := fun a b hab ↦ by
    simpa only [AsymptoticallyEuclideanEnd.range_ofLe] using A.pairwise_disjoint hab
  isCompact_compl := by
    simpa only [AsymptoticallyEuclideanEnd.range_ofLe] using A.isCompact_compl

@[simp]
theorem numEnds_ofLe (A : FiniteEndedAE n M t) {t' : ℝ} (ht : t' ≤ t) :
    (A.ofLe ht).numEnds = A.numEnds := by
  rfl

@[simp]
theorem ends_ofLe (A : FiniteEndedAE n M t) {t' : ℝ} (ht : t' ≤ t)
    (a : Fin (A.ofLe ht).numEnds) :
    (A.ofLe ht).ends a = (A.ends (a.cast (numEnds_ofLe A ht))).ofLe ht := by
  rfl

/-- Push a finite-ended asymptotically Euclidean structure forward along a smooth Riemannian
isometry. -/
def compRiemannianIsometry {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [RiemannianBundle (fun y : N ↦ TangentSpace (𝓡 n) y)]
    (A : FiniteEndedAE n M t) (Φ : RiemannianIsometry (𝓡 n) (𝓡 n) M N) :
    FiniteEndedAE n N t where
  numEnds := A.numEnds
  numEnds_pos := A.numEnds_pos
  ends := fun a ↦ (A.ends a).compRiemannianIsometry Φ
  pairwise_disjoint := fun a b hab ↦ by
    dsimp only
    rw [AsymptoticallyEuclideanEnd.range_compRiemannianIsometry,
      AsymptoticallyEuclideanEnd.range_compRiemannianIsometry]
    exact Disjoint.image (A.pairwise_disjoint hab) (f := (Φ : M → N))
      (Φ.injective.injOn (s := Set.univ)) (Set.subset_univ _) (Set.subset_univ _)
  isCompact_compl := by
    have hU : (⋃ a, Set.range ((A.ends a).compRiemannianIsometry Φ).toFun) =
        Φ '' (⋃ a, Set.range (A.ends a).toFun) := by
      simp_rw [AsymptoticallyEuclideanEnd.range_compRiemannianIsometry, ← Set.image_iUnion]
    have hcomp : (⋃ a, Set.range ((A.ends a).compRiemannianIsometry Φ).toFun)ᶜ =
        Φ '' (⋃ a, Set.range (A.ends a).toFun)ᶜ := by
      rw [hU, (Set.image_compl_eq (f := (Φ : M → N)) Φ.bijective).symm]
    rw [hcomp]
    exact A.isCompact_compl.image Φ.toDiffeomorph.continuous

@[simp]
theorem numEnds_compRiemannianIsometry {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [RiemannianBundle (fun y : N ↦ TangentSpace (𝓡 n) y)]
    (A : FiniteEndedAE n M t) (Φ : RiemannianIsometry (𝓡 n) (𝓡 n) M N) :
    (A.compRiemannianIsometry Φ).numEnds = A.numEnds := by
  rfl

@[simp]
theorem ends_compRiemannianIsometry {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [RiemannianBundle (fun y : N ↦ TangentSpace (𝓡 n) y)]
    (A : FiniteEndedAE n M t) (Φ : RiemannianIsometry (𝓡 n) (𝓡 n) M N)
    (a : Fin (A.compRiemannianIsometry Φ).numEnds) :
    (A.compRiemannianIsometry Φ).ends a =
      (A.ends (a.cast (numEnds_compRiemannianIsometry A Φ))).compRiemannianIsometry Φ := by
  rfl

/-- Constant metric rescaling `g ↦ c • g` of a finite-ended asymptotically Euclidean
structure. -/
def rescale (m : ℕ∞ω) [IsManifold (𝓡 n) 1 M]
    [IsContMDiffRiemannianBundle (𝓡 n) m (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x)]
    (A : FiniteEndedAE n M t) {c : ℝ} (hc : 0 < c) :
    FiniteEndedAE n (WithMetric (AsymptoticallyEuclideanEnd.rescaledMetric (n := n) (M := M) m hc))
      t where
  numEnds := A.numEnds
  numEnds_pos := A.numEnds_pos
  ends := fun a ↦ (A.ends a).rescale m hc
  pairwise_disjoint := fun a b hab ↦ by
    dsimp only
    rw [AsymptoticallyEuclideanEnd.range_rescale, AsymptoticallyEuclideanEnd.range_rescale]
    exact Disjoint.image (A.pairwise_disjoint hab)
      (f := WithMetric.toWithMetric
        (AsymptoticallyEuclideanEnd.rescaledMetric (n := n) (M := M) m hc))
      ((WithMetric.toWithMetric_injective _).injOn (s := Set.univ))
      (Set.subset_univ _) (Set.subset_univ _)
  isCompact_compl := by
    let g_c := AsymptoticallyEuclideanEnd.rescaledMetric (n := n) (M := M) m hc
    have hU : (⋃ a, Set.range ((A.ends a).rescale m hc).toFun) =
        WithMetric.toWithMetric g_c '' (⋃ a, Set.range (A.ends a).toFun) := by
      simp_rw [AsymptoticallyEuclideanEnd.range_rescale, ← Set.image_iUnion]
      rfl
    have hbij : Function.Bijective (WithMetric.toWithMetric g_c) :=
      ⟨WithMetric.toWithMetric_injective g_c,
        fun y ↦ ⟨y.ofWithMetric, WithMetric.toWithMetric_ofWithMetric g_c y⟩⟩
    have hcomp : (⋃ a, Set.range ((A.ends a).rescale m hc).toFun)ᶜ =
        WithMetric.toWithMetric g_c '' (⋃ a, Set.range (A.ends a).toFun)ᶜ := by
      rw [hU, (Set.image_compl_eq hbij).symm]
    rw [hcomp]
    exact A.isCompact_compl.image WithMetric.continuous_toWithMetric

@[simp]
theorem numEnds_rescale (m : ℕ∞ω) [IsManifold (𝓡 n) 1 M]
    [IsContMDiffRiemannianBundle (𝓡 n) m (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x)]
    (A : FiniteEndedAE n M t) {c : ℝ} (hc : 0 < c) :
    (A.rescale m hc).numEnds = A.numEnds := by
  rfl

@[simp]
theorem ends_rescale (m : ℕ∞ω) [IsManifold (𝓡 n) 1 M]
    [IsContMDiffRiemannianBundle (𝓡 n) m (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x)]
    (A : FiniteEndedAE n M t) {c : ℝ} (hc : 0 < c) (a : Fin (A.rescale m hc).numEnds) :
    (A.rescale m hc).ends a =
      (A.ends (a.cast (numEnds_rescale m A hc))).rescale m hc := by
  rfl

/-- The standard one-ended asymptotically Euclidean structure on flat `EuclideanSpace ℝ (Fin n)`
with excised radius `R > 0`, of any order `t : ℝ`. -/
def euclidean (n : ℕ) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    FiniteEndedAE n (EuclideanSpace ℝ (Fin n)) t where
  numEnds := 1
  numEnds_pos := one_pos
  ends := fun _ ↦ AsymptoticallyEuclideanEnd.euclidean n hR t
  pairwise_disjoint := fun a b hab ↦ absurd (Subsingleton.elim a b) hab
  isCompact_compl := by
    have hcompl :
        (⋃ _ : Fin 1, Set.range (AsymptoticallyEuclideanEnd.euclidean n hR t).toFun)ᶜ =
          closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
      ext x
      simp [AsymptoticallyEuclideanEnd.range_euclidean, mem_exteriorBall, mem_closedBall,
        dist_zero_right]
    rw [hcompl]
    exact isCompact_closedBall 0 R

@[simp]
theorem numEnds_euclidean (n : ℕ) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    (euclidean n hR t).numEnds = 1 := by
  rfl

@[simp]
theorem ends_euclidean (n : ℕ) {R : ℝ} (hR : 0 < R) (t : ℝ)
    (a : Fin (euclidean n hR t).numEnds) :
    (euclidean n hR t).ends a = AsymptoticallyEuclideanEnd.euclidean n hR t := by
  rfl

/-- Every finite-ended asymptotically Euclidean manifold of positive order in dimension `1 ≤ n`
has infinite Riemannian volume. -/
theorem riemannianVolume_univ_eq_top [IsManifold (𝓡 n) 1 M]
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x)]
    (hn : 1 ≤ n) (ht : 0 < t) (A : FiniteEndedAE n M t) :
    riemannianVolume (𝓡 n) M univ = ⊤ :=
  top_unique (((A.ends ⟨0, A.numEnds_pos⟩).riemannianVolume_range_eq_top hn ht).symm.trans_le
    (measure_mono (subset_univ _)))

/-- No compact `C¹` manifold of dimension `1 ≤ n` with a continuous Riemannian metric admits a
finite-ended asymptotically Euclidean structure of positive order `t > 0`. -/
theorem not_compactSpace [IsManifold (𝓡 n) 1 M]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x)]
    (hn : 1 ≤ n) (ht : 0 < t) (A : FiniteEndedAE n M t) :
    ¬ CompactSpace M :=
  (A.ends ⟨0, A.numEnds_pos⟩).not_compactSpace hn ht

end FiniteEndedAE

end TauCeti

end
