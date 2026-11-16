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
* `TauCeti.FiniteEndedAE.transRiemannianIsometry`: pushforward along a smooth Riemannian isometry.
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
  setting*, Trans. Amer. Math. Soc. 377 (2024), 5271–5288, Definition 2.3 (arXiv:2108.11972v2).
-/

public section

noncomputable section

open Bundle MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff ENNReal Manifold Topology

namespace TauCeti

/-- A **finite-ended asymptotically Euclidean structure** of order `t` on a Riemannian manifold `M`
modelled on `I`: a finite nonempty family of `n`-dimensional asymptotically Euclidean ends with
pairwise disjoint ranges whose union has compact complement. Requiring `0 < numEnds` excludes the
vacuous zero-end structure on compact manifolds. -/
structure FiniteEndedAE (n : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] (t : ℝ) where
  /-- The number of ends. -/
  numEnds : ℕ
  /-- There is at least one end. -/
  numEnds_pos : 0 < numEnds
  /-- The family of ends. -/
  ends : Fin numEnds → AsymptoticallyEuclideanEnd n I M t
  /-- Distinct ends have disjoint ranges. -/
  pairwise_disjoint : Pairwise fun a b ↦
    Disjoint (Set.range (ends a).toFun) (Set.range (ends b).toFun)
  /-- The complement of the union of the end ranges is compact. -/
  isCompact_compl : IsCompact (⋃ a, Set.range (ends a).toFun)ᶜ

namespace FiniteEndedAE

variable {n : ℕ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {t : ℝ}

/-- Two finite-ended asymptotically Euclidean structures are equal if they have the same number of
ends and equal ends at each index. -/
@[ext (iff := false)]
theorem ext {A₁ A₂ : FiniteEndedAE n I M t} (hn : A₁.numEnds = A₂.numEnds)
    (he : ∀ i : Fin A₁.numEnds, A₁.ends i = A₂.ends (i.cast hn)) : A₁ = A₂ := by
  cases A₁; cases A₂; dsimp only at hn he; subst hn; congr 1; funext i; exact he i

/-- For `1 ≤ n`, any manifold carrying a finite-ended asymptotically Euclidean structure is
nonempty. -/
protected theorem nonempty (hn : 1 ≤ n) (A : FiniteEndedAE n I M t) : Nonempty M :=
  (A.ends ⟨0, A.numEnds_pos⟩).nonempty hn

variable (A : FiniteEndedAE n I M t)

/-- The union of the ranges of the ends is open in `M`. -/
theorem isOpen_iUnion_range [IsManifold I 1 M] : IsOpen (⋃ a, Set.range (A.ends a).toFun) :=
  isOpen_iUnion fun a ↦ (A.ends a).isOpen_range

section OfLe

variable {t' : ℝ} (ht : t' ≤ t)

/-- A finite-ended asymptotically Euclidean structure of order `t` is also one of every smaller
order `t' ≤ t`. -/
def ofLe : FiniteEndedAE n I M t' where
  numEnds := A.numEnds; numEnds_pos := A.numEnds_pos; ends a := (A.ends a).ofLe ht
  pairwise_disjoint a b hab := by
    simpa only [AsymptoticallyEuclideanEnd.range_ofLe] using A.pairwise_disjoint hab
  isCompact_compl := by
    simpa only [AsymptoticallyEuclideanEnd.range_ofLe] using A.isCompact_compl

@[simp]
theorem numEnds_ofLe : (A.ofLe ht).numEnds = A.numEnds := by rfl

@[simp]
theorem ends_ofLe (a : Fin (A.ofLe ht).numEnds) :
    (A.ofLe ht).ends a = (A.ends (a.cast (numEnds_ofLe A ht))).ofLe ht := by rfl

end OfLe

section TransRiemannianIsometry

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] (Φ : RiemannianIsometry I J M N)

/-- Push a finite-ended asymptotically Euclidean structure forward along a smooth Riemannian
isometry. -/
def transRiemannianIsometry : FiniteEndedAE n J N t where
  numEnds := A.numEnds; numEnds_pos := A.numEnds_pos
  ends a := (A.ends a).transRiemannianIsometry Φ
  pairwise_disjoint a b hab := by
    dsimp only
    rw [AsymptoticallyEuclideanEnd.range_transRiemannianIsometry,
      AsymptoticallyEuclideanEnd.range_transRiemannianIsometry]
    exact Disjoint.image (A.pairwise_disjoint hab) (f := (Φ : M → N))
      (Φ.injective.injOn (s := Set.univ)) (Set.subset_univ _) (Set.subset_univ _)
  isCompact_compl := by
    have hU : (⋃ a, Set.range ((A.ends a).transRiemannianIsometry Φ).toFun) =
        Φ '' (⋃ a, Set.range (A.ends a).toFun) := by
      simp_rw [AsymptoticallyEuclideanEnd.range_transRiemannianIsometry, ← Set.image_iUnion]
    rw [hU, (Set.image_compl_eq (f := (Φ : M → N)) Φ.bijective).symm]
    exact A.isCompact_compl.image Φ.toDiffeomorph.continuous

@[simp]
theorem numEnds_transRiemannianIsometry : (A.transRiemannianIsometry Φ).numEnds = A.numEnds := by
  rfl

@[simp]
theorem ends_transRiemannianIsometry (a : Fin (A.transRiemannianIsometry Φ).numEnds) :
    (A.transRiemannianIsometry Φ).ends a =
      (A.ends (a.cast (numEnds_transRiemannianIsometry A Φ))).transRiemannianIsometry Φ := by rfl

end TransRiemannianIsometry

section Rescale

variable (m : ℕ∞ω) [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [IsContMDiffRiemannianBundle I m E (fun x : M ↦ TangentSpace I x)] {c : ℝ} (hc : 0 < c)

/-- Constant metric rescaling `g ↦ c • g` of a finite-ended asymptotically Euclidean
structure. -/
def rescale : FiniteEndedAE n I (WithMetric (rescaledMetric I M m hc)) t where
  numEnds := A.numEnds; numEnds_pos := A.numEnds_pos; ends a := (A.ends a).rescale m hc
  pairwise_disjoint a b hab := by
    dsimp only
    rw [AsymptoticallyEuclideanEnd.range_rescale, AsymptoticallyEuclideanEnd.range_rescale]
    exact Disjoint.image (A.pairwise_disjoint hab)
      (f := WithMetric.toWithMetric (rescaledMetric I M m hc))
      ((WithMetric.toWithMetric_injective _).injOn (s := Set.univ))
      (Set.subset_univ _) (Set.subset_univ _)
  isCompact_compl := by
    let g_c := rescaledMetric I M m hc
    have hU : (⋃ a, Set.range ((A.ends a).rescale m hc).toFun) =
        WithMetric.toWithMetric g_c '' (⋃ a, Set.range (A.ends a).toFun) := by
      simp_rw [AsymptoticallyEuclideanEnd.range_rescale, ← Set.image_iUnion]; rfl
    rw [hU, ← WithMetric.coe_homeomorph_symm g_c, ← (WithMetric.homeomorph g_c).symm.image_compl]
    exact A.isCompact_compl.image (WithMetric.homeomorph g_c).symm.continuous

@[simp]
theorem numEnds_rescale : (A.rescale m hc).numEnds = A.numEnds := by rfl

@[simp]
theorem ends_rescale (a : Fin (A.rescale m hc).numEnds) :
    (A.rescale m hc).ends a = (A.ends (a.cast (numEnds_rescale A m hc))).rescale m hc := by rfl

end Rescale

section Euclidean

variable (n : ℕ) {R : ℝ} (hR : 0 < R) (t : ℝ)

/-- The standard one-ended asymptotically Euclidean structure on flat `EuclideanSpace ℝ (Fin n)`
with excised radius `R > 0`, of any order `t : ℝ`. -/
def euclidean : FiniteEndedAE n (𝓡 n) (EuclideanSpace ℝ (Fin n)) t where
  numEnds := 1; numEnds_pos := one_pos
  ends _ := AsymptoticallyEuclideanEnd.euclidean n hR t
  pairwise_disjoint a b hab := absurd (Subsingleton.elim a b) hab
  isCompact_compl := by
    have hcompl :
        (⋃ _ : Fin 1, Set.range (AsymptoticallyEuclideanEnd.euclidean n hR t).toFun)ᶜ =
          closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by simp [Set.iUnion_const]
    rw [hcompl]; exact isCompact_closedBall 0 R

@[simp]
theorem numEnds_euclidean : (euclidean n hR t).numEnds = 1 := by rfl

@[simp]
theorem ends_euclidean (a : Fin (euclidean n hR t).numEnds) :
    (euclidean n hR t).ends a = AsymptoticallyEuclideanEnd.euclidean n hR t := by rfl

end Euclidean

/-- Every finite-ended asymptotically Euclidean manifold of positive order in dimension `1 ≤ n`
has infinite Riemannian volume. -/
theorem riemannianVolume_univ_eq_top [FiniteDimensional ℝ E] [IsManifold I 1 M]
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (A : FiniteEndedAE n I M t) (hn : 1 ≤ n) (ht : 0 < t) : riemannianVolume I M univ = ⊤ :=
  top_unique (((A.ends ⟨0, A.numEnds_pos⟩).riemannianVolume_range_eq_top hn ht).symm.trans_le
    (measure_mono (subset_univ _)))

/-- No compact `C¹` manifold of dimension `1 ≤ n` with a continuous Riemannian metric admits a
finite-ended asymptotically Euclidean structure of positive order `t > 0`. -/
theorem not_compactSpace [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (hn : 1 ≤ n) (ht : 0 < t) (A : FiniteEndedAE n I M t) : ¬ CompactSpace M :=
  (A.ends ⟨0, A.numEnds_pos⟩).not_compactSpace hn ht

end FiniteEndedAE

end TauCeti

end
