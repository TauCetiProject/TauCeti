/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import TauCeti.Geometry.Manifold.Algebra.Quotient
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Descent
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.InnerProductSpace
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Isometry

/-!
# Flat quotients by Euclidean lattices

Translation by a lattice vector preserves the Euclidean metric. The induced flat metric on
the quotient makes the natural projection a local Riemannian isometry. For a full lattice the
Riemannian volume of the quotient is its covolume.
-/

public section

noncomputable section

open Bundle Function MeasureTheory Module Set TauCeti ZLattice
open scoped ContDiff InnerProductSpace Manifold

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L]

local notation "𝓘E" => 𝓘(ℝ, E)
local notation "Q" => AddAction.orbitRel.Quotient L E
local notation "q" => _root_.Quotient.mk (AddAction.orbitRel L E)

private abbrev sourceMetric :
    ContMDiffRiemannianMetric 𝓘E ∞ E (fun x : E ↦ TangentSpace 𝓘E x) :=
  ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle

omit [FiniteDimensional ℝ E] in
private theorem sourceMetric_inner (x : E) (v w : TangentSpace 𝓘E x) :
    sourceMetric.inner x v w = ⟪(v : E), (w : E)⟫_ℝ := by
  rw [ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
  rfl

private theorem compatible_inner (x x' : E) (v w : TangentSpace 𝓘E x) (v' w' : TangentSpace 𝓘E x')
    (_h : q x = q x') (hv : mfderiv 𝓘E 𝓘E q x v = mfderiv 𝓘E 𝓘E q x' v')
    (hw : mfderiv 𝓘E 𝓘E q x w = mfderiv 𝓘E 𝓘E q x' w') :
    sourceMetric.inner x v w = sourceMetric.inner x' v' w' := by
  simp only [L.mfderiv_orbitRelQuotient_mk] at hv hw
  rw [sourceMetric_inner, sourceMetric_inner]
  exact congrArg₂ (fun a b : E ↦ ⟪a, b⟫_ℝ) hv hw

/-- The Euclidean metric descended to the quotient by translations in a discrete subgroup. -/
def orbitRelQuotientMetric : ContMDiffRiemannianMetric 𝓘E ∞ E (fun x : Q ↦ TangentSpace 𝓘E x) :=
  sourceMetric.descend (f := q) TauCeti.isLocalDiffeomorph_addQuotientMk
    _root_.Quotient.mk_surjective (compatible_inner L)

/-- The tangent bundle of the orbit space equipped with the descended Euclidean metric. -/
abbrev orbitRelQuotientRiemannianBundle : RiemannianBundle (fun x : Q ↦ TangentSpace 𝓘E x) :=
  ⟨(orbitRelQuotientMetric L).toRiemannianMetric⟩

/-- In the quotient charts the descended metric is the Euclidean inner product. -/
@[simp]
theorem orbitRelQuotientMetric_inner_mk (x v w : E) :
    (orbitRelQuotientMetric L).inner (q x) v w = ⟪v, w⟫_ℝ := by
  have h := sourceMetric.descend_inner_mfderiv (f := q) TauCeti.isLocalDiffeomorph_addQuotientMk
    _root_.Quotient.mk_surjective (compatible_inner L) x v w
  rw [L.mfderiv_orbitRelQuotient_mk] at h
  exact h.trans (sourceMetric_inner x v w)

/-- The quotient by a discrete subgroup equipped with its descended Euclidean metric. -/
abbrev FlatQuotient := WithMetric (orbitRelQuotientMetric L)

/-- The projection from the Euclidean space to its flat quotient. -/
def flatQuotientMk (x : E) : FlatQuotient L := WithMetric.toWithMetric _ (q x)

/-- The flat projection is the orbit projection followed by the metric-copy inclusion. -/
theorem flatQuotientMk_eq_comp :
    flatQuotientMk L = WithMetric.toWithMetric (orbitRelQuotientMetric L) ∘ q :=
  (rfl)

/-- Forgetting the chosen metric recovers the native orbit projection. -/
@[simp]
theorem ofWithMetric_flatQuotientMk (x : E) :
    WithMetric.ofWithMetric (flatQuotientMk L x) = q x :=
  (rfl)

/-- The native orbit projection is a local Riemannian isometry for the descended metric. -/
theorem isLocalRiemannianIsometry_orbitRelQuotient_mk :
    letI := orbitRelQuotientRiemannianBundle L
    IsLocalRiemannianIsometry 𝓘E 𝓘E q := by
  let := orbitRelQuotientRiemannianBundle L
  have hd : IsLocalDiffeomorph 𝓘E 𝓘E ∞ q := TauCeti.isLocalDiffeomorph_addQuotientMk
  refine ⟨hd.contMDiff, hd.isInvertible_mfderiv (by simp), fun x v w ↦ ?_⟩
  rw [L.mfderiv_orbitRelQuotient_mk]
  exact orbitRelQuotientMetric_inner_mk L x v w

/-- The projection to a flat quotient preserves the metric locally. -/
theorem isLocalRiemannianIsometry_flatQuotientMk :
    IsLocalRiemannianIsometry 𝓘E 𝓘E (flatQuotientMk L) := by
  let := orbitRelQuotientRiemannianBundle L
  rw [flatQuotientMk_eq_comp]
  simpa only [WithMetric.coe_riemannianIsometry_symm] using
    (WithMetric.riemannianIsometry (orbitRelQuotientMetric L)).symm.isLocalRiemannianIsometry.comp
      (isLocalRiemannianIsometry_orbitRelQuotient_mk L)

/-- The flat quotient projection is smooth of every order. -/
theorem contMDiff_flatQuotientMk {k : ℕ∞ω} : ContMDiff 𝓘E 𝓘E k (flatQuotientMk L) := by
  rw [flatQuotientMk_eq_comp]
  exact WithMetric.contMDiff_toWithMetric.comp TauCeti.isLocalDiffeomorph_addQuotientMk.contMDiff

/-- The flat quotient projection is continuous. -/
theorem continuous_flatQuotientMk : Continuous (flatQuotientMk L) :=
  (contMDiff_flatQuotientMk L (k := 0)).continuous

/-- The differential of the flat quotient projection is the identity in quotient charts. -/
theorem hasMFDerivAt_flatQuotientMk (x : E) :
    HasMFDerivAt 𝓘E 𝓘E (flatQuotientMk L) x (ContinuousLinearMap.id ℝ E) := by
  rw [flatQuotientMk_eq_comp]
  -- Both tangent spaces are the model space; composing their identity maps computes to `id`.
  convert (WithMetric.hasMFDerivAt_toWithMetric (g := orbitRelQuotientMetric L) (q x)).comp x
    (L.hasMFDerivAt_orbitRelQuotient_mk x) using 1
  rfl

/-- In quotient charts the tangent map of the projection is the identity. -/
@[simp]
theorem mfderiv_flatQuotientMk (x : E) :
    mfderiv 𝓘E 𝓘E (flatQuotientMk L) x = ContinuousLinearMap.id ℝ E :=
  (hasMFDerivAt_flatQuotientMk L x).mfderiv

/-- The flat quotient projection is a local diffeomorphism of every order. -/
theorem isLocalDiffeomorph_flatQuotientMk {k : ℕ∞ω} :
    IsLocalDiffeomorph 𝓘E 𝓘E k (flatQuotientMk L) := by
  rw [flatQuotientMk_eq_comp, ← WithMetric.coe_diffeomorph_symm (g := orbitRelQuotientMetric L) k]
  intro x
  exact (TauCeti.isLocalDiffeomorph_addQuotientMk x).comp 𝓘E (FlatQuotient L)
    ((WithMetric.diffeomorph (orbitRelQuotientMetric L) k).symm.isLocalDiffeomorph _)

/-- Every point of the flat quotient has a Euclidean representative. -/
theorem flatQuotientMk_surjective : Surjective (flatQuotientMk L) := by
  rintro ⟨x⟩
  obtain ⟨y, rfl⟩ := _root_.Quotient.mk_surjective x
  exact ⟨y, rfl⟩

/-- Two points have the same image exactly when their difference belongs to the lattice. -/
@[simp]
theorem flatQuotientMk_eq_flatQuotientMk_iff {x y : E} :
    flatQuotientMk L x = flatQuotientMk L y ↔ x - y ∈ L := by
  rw [flatQuotientMk, flatQuotientMk, WithMetric.toWithMetric_inj]
  exact Submodule.orbitRelQuotient_mk_eq_mk_iff L

/-- Translation by a lattice vector leaves the flat quotient projection unchanged. -/
@[simp]
theorem flatQuotientMk_add_of_mem (x : E) {l : E} (hl : l ∈ L) :
    flatQuotientMk L (x + l) = flatQuotientMk L x := by
  rw [flatQuotientMk_eq_flatQuotientMk_iff, add_sub_cancel_left]
  exact hl

/-- A half-open fundamental parallelepiped parametrizes the entire flat torus bijectively. -/
theorem bijOn_flatQuotientMk_fundamentalDomain [IsZLattice ℝ L] {ι : Type*}
    (b : Basis ι ℤ L) :
    BijOn (flatQuotientMk L) (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) univ := by
  have : Finite ι := Module.Finite.finite_basis b
  let := Fintype.ofFinite ι
  let B := b.ofZLatticeBasis ℝ
  refine ⟨mapsTo_univ _ _, ?_, ?_⟩
  · intro x hx y hy hxy
    have hL := (flatQuotientMk_eq_flatQuotientMk_iff L).mp hxy
    have heq : ZSpan.fract B y = ZSpan.fract B x := (ZSpan.fract_eq_fract B y x).mpr (by
      simpa only [B, b.ofZLatticeBasis_span ℝ, neg_add_eq_sub] using hL)
    exact ((ZSpan.fract_eq_self (b := B)).mpr hx).symm.trans
      (heq.symm.trans (ZSpan.fract_eq_self.mpr hy))
  · rintro ⟨y⟩ _
    obtain ⟨x, rfl⟩ := _root_.Quotient.mk_surjective y
    refine ⟨ZSpan.fract B x, ZSpan.fract_mem_fundamentalDomain B x, ?_⟩
    apply (flatQuotientMk_eq_flatQuotientMk_iff L).2
    rw [ZSpan.fract_apply, sub_right_comm, sub_self, zero_sub]
    exact L.neg_mem (b.ofZLatticeBasis_span ℝ ▸ (ZSpan.floor B x).property)

variable [IsZLattice ℝ L] [MeasurableSpace E] [BorelSpace E]

/-- Euclidean volume restricted to a fundamental parallelepiped pushes forward to the
Riemannian volume of the flat torus. -/
theorem measurePreserving_flatQuotientMk {ι : Type*} (b : Basis ι ℤ L) :
    MeasurePreserving (flatQuotientMk L)
      (volume.restrict (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)))
      (riemannianVolume 𝓘E (FlatQuotient L)) := by
  have : Finite ι := Module.Finite.finite_basis b
  let := Fintype.ofFinite ι
  let D := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)
  have hD : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet _
  have hb := bijOn_flatQuotientMk_fundamentalDomain L b
  have hq := isLocalRiemannianIsometry_flatQuotientMk L
  have hm := hq.contMDiff.continuous.measurable
  have : IsContinuousRiemannianBundle E (fun x : E ↦ TangentSpace 𝓘E x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := 𝓘E) (n := ∞)
  refine ⟨hm, Measure.ext fun s hs ↦ ?_⟩
  rw [Measure.map_apply hm hs, Measure.restrict_apply (hm hs)]
  have hi : flatQuotientMk L '' ((flatQuotientMk L ⁻¹' s) ∩ D) = s := by
    rw [image_preimage_inter, hb.image_eq, inter_univ]
  have hv := riemannianVolume_image_of_inner_mfderiv ((hm hs).inter hD)
    (hb.injOn.mono inter_subset_right) (fun x _ ↦ hq.inner_mfderiv x)
  rw [hi, riemannianVolume_eq_volume] at hv
  exact hv.symm

/-- The Riemannian volume of a flat torus is the Euclidean covolume of its lattice. -/
theorem riemannianVolume_univ_flatQuotient_eq_covolume :
    riemannianVolume 𝓘E (FlatQuotient L) univ = ENNReal.ofReal (covolume L volume) := by
  let b := Free.chooseBasis ℤ L
  have h := (measurePreserving_flatQuotientMk L b).measure_preimage
    (s := univ) MeasurableSet.univ.nullMeasurableSet
  rw [preimage_univ, Measure.restrict_apply_univ] at h
  rw [← h,
    covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain b volume), measureReal_def,
    ENNReal.ofReal_toReal (ne_of_lt (ZSpan.fundamentalDomain_isBounded _).measure_lt_top)]

/-- The real-valued Riemannian volume of a flat torus is its lattice covolume. -/
theorem riemannianVolume_real_univ_flatQuotient_eq_covolume :
    (riemannianVolume 𝓘E (FlatQuotient L)).real univ = covolume L volume := by
  rw [measureReal_def, riemannianVolume_univ_flatQuotient_eq_covolume,
    ENNReal.toReal_ofReal (covolume_pos L volume).le]

end Submodule
