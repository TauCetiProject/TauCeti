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

open Bundle Function MeasureTheory Module Set TauCeti
open scoped ContDiff InnerProductSpace Manifold

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L]

local notation "𝓘E" => 𝓘(ℝ, E)
local notation "Q" => AddAction.orbitRel.Quotient L E
local notation "q" => Quotient.mk (AddAction.orbitRel L E)

private abbrev sourceMetric :
    ContMDiffRiemannianMetric 𝓘E ∞ E (fun x : E ↦ TangentSpace 𝓘E x) :=
  ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle

private theorem compatible_inner (x x' : E) (v w : TangentSpace 𝓘E x) (v' w' : TangentSpace 𝓘E x')
    (hv : mfderiv 𝓘E 𝓘E q x v = mfderiv 𝓘E 𝓘E q x' v')
    (hw : mfderiv 𝓘E 𝓘E q x w = mfderiv 𝓘E 𝓘E q x' w') :
    sourceMetric.inner x v w = sourceMetric.inner x' v' w' := by
  simp only [L.mfderiv_orbitRelQuotient_mk] at hv hw
  rw [ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner,
    ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
  exact congrArg₂ (fun a b : E ↦ ⟪a, b⟫_ℝ) hv hw

/-- The Euclidean metric descended to the quotient by translations in a discrete subgroup. -/
def quotientMetric : ContMDiffRiemannianMetric 𝓘E ∞ E (fun x : Q ↦ TangentSpace 𝓘E x) :=
  sourceMetric.descend (f := q) TauCeti.isLocalDiffeomorph_addQuotientMk
    Quotient.mk_surjective (fun x y v w v' w' _ ↦ compatible_inner L x y v w v' w')

/-- In the quotient charts the descended metric is the Euclidean inner product. -/
theorem quotientMetric_inner_mk (x v w : E) :
    (quotientMetric L).inner (q x) v w = ⟪v, w⟫_ℝ := by
  have h := sourceMetric.descend_inner_mfderiv (f := q) TauCeti.isLocalDiffeomorph_addQuotientMk
    Quotient.mk_surjective (fun x y v w v' w' _ ↦ compatible_inner L x y v w v' w') x v w
  rw [L.mfderiv_orbitRelQuotient_mk] at h
  have he (v w : TangentSpace 𝓘E x) : sourceMetric.inner x v w = ⟪(v : E), (w : E)⟫_ℝ := by
    rw [ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
    rfl
  exact h.trans (he v w)

/-- The quotient by a discrete subgroup equipped with its descended Euclidean metric. -/
abbrev FlatQuotient := WithMetric (quotientMetric L)

/-- The projection from the Euclidean space to its flat quotient. -/
def flatQuotientMk (x : E) : FlatQuotient L := WithMetric.toWithMetric _ (q x)

/-- The projection to a flat quotient preserves the metric locally. -/
theorem isLocalRiemannianIsometry_flatQuotientMk :
    IsLocalRiemannianIsometry 𝓘E 𝓘E (flatQuotientMk L) := by
  let : RiemannianBundle (fun x : Q ↦ TangentSpace 𝓘E x) := ⟨(quotientMetric L).toRiemannianMetric⟩
  have hq : IsLocalRiemannianIsometry 𝓘E 𝓘E q := by
    have hd : IsLocalDiffeomorph 𝓘E 𝓘E ∞ q := TauCeti.isLocalDiffeomorph_addQuotientMk
    refine ⟨hd.contMDiff, hd.isInvertible_mfderiv (by simp), fun x v w ↦ ?_⟩
    rw [L.mfderiv_orbitRelQuotient_mk]
    exact quotientMetric_inner_mk L x v w
  change IsLocalRiemannianIsometry 𝓘E 𝓘E (WithMetric.toWithMetric (quotientMetric L) ∘ q)
  simpa only [WithMetric.coe_riemannianIsometry_symm] using
    (WithMetric.riemannianIsometry (quotientMetric L)).symm.isLocalRiemannianIsometry.comp hq

/-- Every point of the flat quotient has a Euclidean representative. -/
theorem surjective_flatQuotientMk : Surjective (flatQuotientMk L) := by
  rintro ⟨x⟩
  obtain ⟨y, rfl⟩ := Quotient.mk_surjective x
  exact ⟨y, rfl⟩

/-- Two points have the same image exactly when their difference belongs to the lattice. -/
@[simp]
theorem flatQuotientMk_eq_iff {x y : E} :
    flatQuotientMk L x = flatQuotientMk L y ↔ x - y ∈ L := by
  rw [flatQuotientMk, flatQuotientMk, WithMetric.toWithMetric_inj]
  exact Submodule.orbitRelQuotient_mk_eq_mk_iff L

/-- A half-open fundamental parallelepiped parametrizes the entire flat torus bijectively. -/
theorem bijOn_flatQuotientMk_fundamentalDomain [IsZLattice ℝ L] {ι : Type*}
    (b : Basis ι ℤ L) :
    BijOn (flatQuotientMk L) (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) univ := by
  have : Finite ι := Module.Finite.finite_basis b
  let := Fintype.ofFinite ι
  let B := b.ofZLatticeBasis ℝ
  refine ⟨mapsTo_univ _ _, ?_, ?_⟩
  · intro x hx y hy hxy
    have hL := (flatQuotientMk_eq_iff L).mp hxy
    have heq : ZSpan.fract B y = ZSpan.fract B x := (ZSpan.fract_eq_fract B y x).mpr (by
      simpa only [B, b.ofZLatticeBasis_span ℝ, neg_add_eq_sub] using hL)
    exact ((ZSpan.fract_eq_self (b := B)).mpr hx).symm.trans
      (heq.symm.trans (ZSpan.fract_eq_self.mpr hy))
  · rintro ⟨y⟩ _
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective y
    refine ⟨ZSpan.fract B x, ZSpan.fract_mem_fundamentalDomain B x, ?_⟩
    apply (flatQuotientMk_eq_iff L).2
    rw [ZSpan.fract, sub_right_comm, sub_self, zero_sub]
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
theorem volume_real_flatQuotient :
    (riemannianVolume 𝓘E (FlatQuotient L)).real univ = covolume L volume := by
  let b := Free.chooseBasis ℤ L
  rw [← (measurePreserving_flatQuotientMk L b).map_eq, measureReal_def, Measure.map_apply
    (measurePreserving_flatQuotientMk L b).measurable MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply_univ, covolume_eq_measure_fundamentalDomain _ _
      (isAddFundamentalDomain b volume), measureReal_def]

end ZLattice
