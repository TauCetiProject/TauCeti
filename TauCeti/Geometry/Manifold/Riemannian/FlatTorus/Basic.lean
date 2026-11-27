/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import TauCeti.Geometry.Manifold.Algebra.Quotient
public import TauCeti.Geometry.Manifold.Riemannian.Distance
public import TauCeti.Geometry.Manifold.Riemannian.FlatTorus.Lattice
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local
import TauCeti.Algebra.Module.ZLattice.Covolume

/-!
# The flat torus `ℝⁿ / ℤⁿ`

The integer lattice `ℤⁿ ⊆ ℝⁿ` (`TauCeti.FlatTorus.lattice n`, the `ℤ`-span of the standard basis
of `EuclideanSpace ℝ (Fin n)`) is a discrete submodule, and a full lattice. Translations by its
elements form a free, properly discontinuous action of `ℤⁿ` on `ℝⁿ` by isometries, so the orbit
space `AddAction.orbitRel.Quotient (lattice n) ℝⁿ` is a compact connected smooth manifold modelled
on `ℝⁿ`, for which the orbit projection `π : ℝⁿ → ℝⁿ / ℤⁿ` is a local diffeomorphism and a covering
map (`TauCeti.instIsManifoldAddQuotient`, `Submodule.instCompactSpaceOrbitRelQuotient`).

The charts of the orbit space are local inverses of `π`, so `π` read in charts is locally a
translation and its differential is the identity of `ℝⁿ` at every point
(`TauCeti.FlatTorus.hasMFDerivAt_mk`). Translations preserve the Euclidean metric, so the Euclidean
metric descends along `π` (`Bundle.ContMDiffRiemannianMetric.descend`) to the *flat metric* of the
torus: in the charts of the torus it is the Euclidean inner product
(`TauCeti.FlatTorus.inner_mfderiv_mk`), and `π` is a local Riemannian isometry
(`TauCeti.FlatTorus.isLocalRiemannianIsometry_mk`).

`TauCeti.FlatTorus n` is a copy of the orbit space, with the same charts, smooth structure and
flat metric, whose metric space structure is the Riemannian distance of the flat metric, given by
`TauCeti.MetricSpace.ofRiemannianMetric`. Its topology is by construction the quotient topology,
and it satisfies `IsRiemannianManifold`. This follows the construction of the round sphere
`TauCeti.RoundSphere`.

## Main definitions

* `TauCeti.FlatTorus.lattice n`: the integer lattice `ℤⁿ` of `ℝⁿ = EuclideanSpace ℝ (Fin n)`.
* `TauCeti.FlatTorus n`: the flat torus `ℝⁿ / ℤⁿ`, with its Riemannian distance.
* `TauCeti.FlatTorus.mk`: the projection `π : ℝⁿ → ℝⁿ / ℤⁿ`.
* `TauCeti.FlatTorus.flatMetric n`: the flat metric, descended from the Euclidean metric.

## Main statements

* `TauCeti.FlatTorus.mem_lattice_iff`: the points of the lattice are the vectors with integer
  coordinates.
* `TauCeti.FlatTorus.mk_eq_mk_iff`: `π x = π y` exactly when `x - y ∈ ℤⁿ`.
* `TauCeti.FlatTorus.isCoveringMap_mk`, `TauCeti.FlatTorus.isLocalDiffeomorph_mk`: the projection
  is a covering map and a local diffeomorphism.
* `TauCeti.FlatTorus.symm_apply_of_mem_atlas`,
  `TauCeti.FlatTorus.exists_eventuallyEq_sub_of_mem_atlas`: the inverse of a chart is the
  projection, and the projection read in a chart is locally a translation by a lattice vector.
* `TauCeti.FlatTorus.hasMFDerivAt_mk`: the differential of the projection is the identity of `ℝⁿ`.
* `TauCeti.FlatTorus.inner_mfderiv_mk`, `TauCeti.FlatTorus.norm_mfderiv_mk`,
  `TauCeti.FlatTorus.norm_tangentSpace_mk`: the flat metric is the Euclidean inner product.
* `TauCeti.FlatTorus.isLocalRiemannianIsometry_mk`: the projection is a local isometry.
* `TauCeti.FlatTorus.riemannianIsometryFlatQuotient`: the identification with the general
  flat lattice quotient, commuting with the projections.
* `TauCeti.FlatTorus.riemannianVolume_univ`: the standard flat torus has unit volume.
* `TauCeti.FlatTorus.instIsRiemannianManifold`, `TauCeti.FlatTorus.instCompactSpace`,
  `TauCeti.FlatTorus.instConnectedSpace`: the flat torus is a compact connected Riemannian
  manifold.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2 (Riemannian coverings and quotients by isometric group actions, flat tori).
-/

public section

open Bundle Filter Function Manifold Module Set Topology
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace TauCeti

local notation "ℝ^" n => EuclideanSpace ℝ (Fin n)

namespace FlatTorus

/-- The integer lattice `ℤⁿ` of `ℝⁿ`: the `ℤ`-span of the standard basis of
`EuclideanSpace ℝ (Fin n)`. -/
def lattice (n : ℕ) : Submodule ℤ (ℝ^n) :=
  Submodule.span ℤ (range (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)

variable {n : ℕ}

/-- A vector lies in the integer lattice exactly when all its coordinates are integers. -/
theorem mem_lattice_iff {x : ℝ^n} : x ∈ lattice n ↔ ∀ i, ∃ k : ℤ, x i = k := by
  rw [lattice, Basis.mem_span_iff_repr_mem]
  simp [eq_comm]

/-- The integer multiples of the standard basis vectors lie in the integer lattice. -/
theorem single_mem_lattice (i : Fin n) (z : ℤ) : EuclideanSpace.single i (z : ℝ) ∈ lattice n := by
  rw [mem_lattice_iff]
  intro j
  by_cases h : j = i
  · exact ⟨z, by simp [h]⟩
  · exact ⟨0, by simp [h]⟩

/-- A bounded set contains finitely many points of the integer lattice. -/
theorem finite_inter_lattice {s : Set (ℝ^n)} (hs : Bornology.IsBounded s) :
    (s ∩ lattice n).Finite :=
  ZSpan.setFinite_inter (EuclideanSpace.basisFun (Fin n) ℝ).toBasis hs

instance instDiscreteTopologyLattice : DiscreteTopology (lattice n) :=
  inferInstanceAs (DiscreteTopology
    (Submodule.span ℤ (range (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)))

instance instIsZLatticeLattice : IsZLattice ℝ (lattice n) :=
  inferInstanceAs (IsZLattice ℝ
    (Submodule.span ℤ (range (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)))

/-- The standard integer lattice has Euclidean covolume one. -/
@[simp]
theorem covolume_lattice : ZLattice.covolume (lattice n) MeasureTheory.volume = 1 := by
  rw [lattice, ZLattice.covolume_eq_measure_fundamentalDomain _ _
    (ZSpan.isAddFundamentalDomain (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      MeasureTheory.volume)]
  simp only [OrthonormalBasis.volume_real_fundamentalDomain]

end FlatTorus

/-- The flat torus `ℝⁿ / ℤⁿ`, the orbit space of the translation action of the integer lattice on
`ℝⁿ`, to be equipped with its flat metric and the Riemannian distance of that metric. -/
@[expose] def FlatTorus (n : ℕ) : Type :=
  AddAction.orbitRel.Quotient (FlatTorus.lattice n) (ℝ^n)

namespace FlatTorus

variable {n : ℕ}

local notation "𝕋" n => AddAction.orbitRel.Quotient (FlatTorus.lattice n) (ℝ^n)

/-! ### The orbit projection -/

/-- The orbit projection `π : ℝⁿ → ℝⁿ / ℤⁿ`, valued in the orbit space. -/
private abbrev proj (n : ℕ) : (ℝ^n) → 𝕋 n :=
  Quotient.mk (AddAction.orbitRel (lattice n) (ℝ^n))

/-! ### The flat metric -/

/-- The flat metric of `ℝⁿ / ℤⁿ`: the Euclidean metric of `ℝⁿ`, descended along the orbit
projection. -/
def flatMetric (n : ℕ) :
    ContMDiffRiemannianMetric 𝓘(ℝ, ℝ^n) ∞ (ℝ^n) (fun x : 𝕋 n ↦ TangentSpace 𝓘(ℝ, ℝ^n) x) :=
  Submodule.orbitRelQuotientMetric (lattice n)

/-- The standard flat metric is the descended metric of the integer-lattice orbit space. -/
theorem flatMetric_def (n : ℕ) :
    flatMetric n = Submodule.orbitRelQuotientMetric (lattice n) :=
  (rfl)

/-! ### The flat torus as a Riemannian manifold -/

/-- The Riemannian distance of the flat metric. -/
instance instMetricSpace : MetricSpace (FlatTorus n) :=
  letI := (lattice n).orbitRelQuotientRiemannianBundle
  letI : IsContinuousRiemannianBundle (ℝ^n) (fun x : 𝕋 n ↦ TangentSpace 𝓘(ℝ, ℝ^n) x) :=
    Bundle.instIsContinuousRiemannianBundle
      (Submodule.orbitRelQuotientMetric (lattice n)).toContinuousRiemannianMetric
  (MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℝ^n) (𝕋 n) : MetricSpace (𝕋 n))

instance instChartedSpace : ChartedSpace (ℝ^n) (FlatTorus n) :=
  inferInstanceAs (ChartedSpace (ℝ^n) (𝕋 n))

instance instIsManifold {k : ℕ∞ω} : IsManifold 𝓘(ℝ, ℝ^n) k (FlatTorus n) :=
  inferInstanceAs (IsManifold 𝓘(ℝ, ℝ^n) k (𝕋 n))

/-- The flat metric. -/
instance instRiemannianBundle :
    RiemannianBundle (fun x : FlatTorus n ↦ TangentSpace 𝓘(ℝ, ℝ^n) x) :=
  (lattice n).orbitRelQuotientRiemannianBundle

instance instIsContMDiffRiemannianBundle :
    IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ^n) ∞ (ℝ^n)
      (fun x : FlatTorus n ↦ TangentSpace 𝓘(ℝ, ℝ^n) x) :=
  Bundle.instIsContMDiffRiemannianBundle (flatMetric n)

instance instIsContinuousRiemannianBundle :
    IsContinuousRiemannianBundle (ℝ^n) (fun x : FlatTorus n ↦ TangentSpace 𝓘(ℝ, ℝ^n) x) :=
  Bundle.instIsContinuousRiemannianBundle (flatMetric n).toContinuousRiemannianMetric

/-- **The flat torus is a Riemannian manifold**: its distance is the Riemannian distance of the
flat metric. -/
instance instIsRiemannianManifold : IsRiemannianManifold 𝓘(ℝ, ℝ^n) (FlatTorus n) :=
  ⟨fun _ _ ↦ rfl⟩

instance instCompactSpace : CompactSpace (FlatTorus n) :=
  inferInstanceAs (CompactSpace (𝕋 n))

instance instConnectedSpace : ConnectedSpace (FlatTorus n) :=
  inferInstanceAs (ConnectedSpace (𝕋 n))

instance instSecondCountableTopology : SecondCountableTopology (FlatTorus n) :=
  inferInstanceAs (SecondCountableTopology (𝕋 n))

instance instMeasurableSpace : MeasurableSpace (FlatTorus n) :=
  borel _

instance instBorelSpace : BorelSpace (FlatTorus n) :=
  ⟨rfl⟩

/-! ### The projection `ℝⁿ → ℝⁿ / ℤⁿ` -/

/-- The projection `π : ℝⁿ → ℝⁿ / ℤⁿ` onto the flat torus. -/
def mk : (ℝ^n) → FlatTorus n :=
  proj n

/-- The flat metric at the image of a vector is the Euclidean inner product in quotient
coordinates. -/
@[simp]
theorem flatMetric_inner_mk (x v w : ℝ^n) :
    (flatMetric n).inner (mk x) v w = ⟪v, w⟫_ℝ := by
  rw [flatMetric_def, mk]
  exact Submodule.orbitRelQuotientMetric_inner_mk (lattice n) x v w

theorem mk_surjective : Surjective (mk : (ℝ^n) → FlatTorus n) :=
  Quotient.mk_surjective

/-- Two vectors have the same image in the flat torus exactly when they differ by a vector of the
integer lattice. -/
theorem mk_eq_mk_iff {x y : ℝ^n} : mk x = mk y ↔ x - y ∈ lattice n :=
  Submodule.orbitRelQuotient_mk_eq_mk_iff _

/-- The projection is invariant under translations by the integer lattice. -/
@[simp]
theorem mk_add_of_mem (x : ℝ^n) {l : ℝ^n} (hl : l ∈ lattice n) : mk (x + l) = mk x := by
  rw [mk_eq_mk_iff, add_sub_cancel_left]
  exact hl

/-- The inverse of a chart of the flat torus is the projection on the chart target. -/
theorem symm_apply_of_mem_atlas {c : OpenPartialHomeomorph (FlatTorus n) (ℝ^n)}
    (hc : c ∈ atlas (ℝ^n) (FlatTorus n)) {w : ℝ^n} (hw : w ∈ c.target) : c.symm w = mk w :=
  TauCeti.symm_eq_addQuotientMk_of_mem_atlas_addQuotient hc hw

/-- Read in a chart of the flat torus, the projection is locally a translation by a lattice
vector. -/
theorem exists_eventuallyEq_sub_of_mem_atlas {c : OpenPartialHomeomorph (FlatTorus n) (ℝ^n)}
    (hc : c ∈ atlas (ℝ^n) (FlatTorus n)) {x : ℝ^n} (hx : mk x ∈ c.source) :
    ∃ l ∈ lattice n, (c ∘ mk) =ᶠ[𝓝 x] fun y ↦ y - l :=
  (lattice n).exists_eventuallyEq_sub_of_mem_atlas_orbitRelQuotient hc hx

/-- The projection is a covering map, the quotient map of the translation action of `ℤⁿ`. -/
theorem isAddQuotientCoveringMap_mk :
    IsAddQuotientCoveringMap (mk : (ℝ^n) → FlatTorus n) (lattice n) :=
  isAddQuotientCoveringMap_quotientMk_of_properlyDiscontinuousVAdd

/-- The projection is a covering map. -/
theorem isCoveringMap_mk : IsCoveringMap (mk : (ℝ^n) → FlatTorus n) :=
  isAddQuotientCoveringMap_mk.isCoveringMap

theorem continuous_mk : Continuous (mk : (ℝ^n) → FlatTorus n) :=
  continuous_quotient_mk'

/-- The projection is a local diffeomorphism. -/
theorem isLocalDiffeomorph_mk {k : ℕ∞ω} :
    IsLocalDiffeomorph 𝓘(ℝ, ℝ^n) 𝓘(ℝ, ℝ^n) k (mk : (ℝ^n) → FlatTorus n) :=
  TauCeti.isLocalDiffeomorph_addQuotientMk

theorem contMDiff_mk {k : ℕ∞ω} : ContMDiff 𝓘(ℝ, ℝ^n) 𝓘(ℝ, ℝ^n) k (mk : (ℝ^n) → FlatTorus n) :=
  isLocalDiffeomorph_mk.contMDiff

/-- **The differential of the projection is the identity of `ℝⁿ`**, the tangent spaces of the
flat torus being read in its charts. -/
theorem hasMFDerivAt_mk (x : ℝ^n) :
    HasMFDerivAt 𝓘(ℝ, ℝ^n) 𝓘(ℝ, ℝ^n) (mk : (ℝ^n) → FlatTorus n) x
      (ContinuousLinearMap.id ℝ (ℝ^n)) :=
  (lattice n).hasMFDerivAt_orbitRelQuotient_mk x

@[simp]
theorem mfderiv_mk (x : ℝ^n) :
    mfderiv 𝓘(ℝ, ℝ^n) 𝓘(ℝ, ℝ^n) (mk : (ℝ^n) → FlatTorus n) x = ContinuousLinearMap.id ℝ (ℝ^n) :=
  (hasMFDerivAt_mk x).mfderiv

/-- **The flat metric is the Euclidean inner product**: the differential of the projection
preserves inner products. -/
theorem inner_mfderiv_mk (x v w : ℝ^n) :
    ⟪mfderiv 𝓘(ℝ, ℝ^n) 𝓘(ℝ, ℝ^n) (mk : (ℝ^n) → FlatTorus n) x v,
      mfderiv 𝓘(ℝ, ℝ^n) 𝓘(ℝ, ℝ^n) (mk : (ℝ^n) → FlatTorus n) x w⟫_ℝ = ⟪v, w⟫_ℝ := by
  rw [mfderiv_mk]
  exact flatMetric_inner_mk x v w

/-- The flat norm of the image of a vector under the differential of the projection is its
Euclidean norm. -/
theorem norm_mfderiv_mk (x v : ℝ^n) :
    ‖mfderiv 𝓘(ℝ, ℝ^n) 𝓘(ℝ, ℝ^n) (mk : (ℝ^n) → FlatTorus n) x v‖ = ‖v‖ := by
  rw [norm_eq_sqrt_real_inner, inner_mfderiv_mk, ← norm_eq_sqrt_real_inner]

/-- The flat norm of a tangent vector at a point of the torus is its Euclidean norm, the tangent
space being read in the charts of the torus. -/
@[simp]
theorem norm_tangentSpace_mk (x v : ℝ^n) :
    @norm (TangentSpace 𝓘(ℝ, ℝ^n) (mk x)) _ v = ‖v‖ := by
  have h := norm_mfderiv_mk x v
  rw [mfderiv_mk] at h
  exact h

/-- **The projection is a local Riemannian isometry.** -/
theorem isLocalRiemannianIsometry_mk :
    IsLocalRiemannianIsometry 𝓘(ℝ, ℝ^n) 𝓘(ℝ, ℝ^n) (mk : (ℝ^n) → FlatTorus n) := by
  -- FlatTorus inherits the orbit-space charts and the named descended bundle.
  rw [mk]
  exact (lattice n).isLocalRiemannianIsometry_orbitRelQuotient_mk

/-- The standard flat torus is Riemannian isometric to the general flat lattice quotient. -/
def riemannianIsometryFlatQuotient (n : ℕ) :
    RiemannianIsometry 𝓘(ℝ, ℝ^n) 𝓘(ℝ, ℝ^n)
      (FlatTorus n) (Submodule.FlatQuotient (lattice n)) :=
  -- FlatTorus inherits the orbit-space charts and the named descended bundle.
  letI := (lattice n).orbitRelQuotientRiemannianBundle
  (WithMetric.riemannianIsometry (Submodule.orbitRelQuotientMetric (lattice n))).symm

/-- The identification with the lattice quotient commutes with the Euclidean projections. -/
@[simp]
theorem riemannianIsometryFlatQuotient_mk (x : ℝ^n) :
    riemannianIsometryFlatQuotient n (mk x) = (lattice n).flatQuotientMk x := by
  let := (lattice n).orbitRelQuotientRiemannianBundle
  rw [riemannianIsometryFlatQuotient, mk, Submodule.flatQuotientMk_eq_comp, comp_apply]
  exact congrFun
    (WithMetric.coe_riemannianIsometry_symm (Submodule.orbitRelQuotientMetric (lattice n)))
    (proj n x)

/-- The standard flat torus has unit Riemannian volume in every dimension. -/
@[simp]
theorem riemannianVolume_univ : riemannianVolume 𝓘(ℝ, ℝ^n) (FlatTorus n) univ = 1 := by
  have h := (riemannianIsometryFlatQuotient n).measurePreserving_riemannianVolume.measure_preimage
    (s := univ) MeasurableSet.univ.nullMeasurableSet
  rw [preimage_univ, Submodule.riemannianVolume_univ_flatQuotient_eq_covolume, covolume_lattice,
    ENNReal.ofReal_one] at h
  exact h

end FlatTorus

end TauCeti
