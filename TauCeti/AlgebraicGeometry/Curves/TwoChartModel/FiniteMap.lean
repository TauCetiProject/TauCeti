/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.FiniteExtension
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Proper
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finite morphisms between two-chart models

An extension of algebraic function fields induces a morphism of their two-chart models. The
normalization maps on both affine charts are finite. The model over the larger field is proper
over the constant field, while the target model is separated. Thus the induced morphism is
proper. It is locally quasi-finite on the two source charts, and therefore finite.

This is the global finiteness assertion for the normalization morphism. It applies to inseparable
extensions as well. The chart finiteness comes from finite normalization of polynomial rings;
the passage from proper and locally quasi-finite to finite is Mathlib's Zariski main theorem.

See Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.2 and
Appendix B.
-/

public section

open CategoryTheory _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.twoChartModel

universe u

variable {k F F' : Type u} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
  [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']

/-- The morphism of two-chart models induced by a finite function-field extension is finite.
This includes inseparable extensions. -/
theorem isFinite_map (hF : IsFunctionField k F) (hF' : IsFunctionField k F')
    {x : F} (hx : x ≠ 0) {x' : F'} (hx' : x' ≠ 0)
    (h : algebraMap F F' x = x') (hxt : Transcendental k x) :
    IsFinite (map hF hF' hx hx' h) := by
  have hxt' : Transcendental k x' := by
    rw [← h]
    exact (transcendental_algebraMap_iff (algebraMap F F').injective).mpr hxt
  let f := map hF hF' hx hx' h
  have hproper : IsProper f := by
    have : IsProper (f ≫ (twoChartModel hF hx ↘ Spec (.of k))) := by
      rw [(Scheme.Hom.isOver_iff (Spec (.of k))).mp
        (inferInstance : f.IsOver (Spec (.of k)))]
      exact isProper hxt'
    exact IsProper.of_comp f (twoChartModel hF hx ↘ Spec (.of k))
  let 𝒰 : (twoChartModel hF' hx').OpenCover := Scheme.Cover.mkOfCovers Bool
    (fun b ↦ b.rec (Spec (.of (holomorphyRing {P : Place k F' | x'⁻¹ ∈ P.integers})))
      (Spec (.of (holomorphyRing {P : Place k F' | x' ∈ P.integers}))))
    (fun b ↦ match b with | false => ιInfinity hF' hx' | true => ιFinite hF' hx')
    (fun p ↦ by
      rcases (Set.ext_iff.mp (range_ιFinite_union_range_ιInfinity hF' hx') p).mpr trivial with
        ⟨q, rfl⟩ | ⟨q, rfl⟩
      exacts [⟨true, q, rfl⟩, ⟨false, q, rfl⟩])
    (fun b ↦ by cases b <;> infer_instance)
  have hqf : LocallyQuasiFinite f := by
    have hloc : IsZariskiLocalAtSource @LocallyQuasiFinite :=
      @HasRingHomProperty.instIsZariskiLocalAtSource _ RingHom.QuasiFinite
        instHasRingHomPropertyLocallyQuasiFiniteQuasiFinite
    apply hloc.of_openCover 𝒰
    intro b
    cases b
    -- The two Bool cases reduce to the named infinity and finite chart inclusions.
    · change LocallyQuasiFinite (ιInfinity hF' hx' ≫ f)
      rw [ιInfinity_map]
      have : IsFinite (Spec.map (CommRingCat.ofHom (infinityChartMap (k := k) h))) :=
        isFinite_specMap_infinityChartMap hF' hxt h
      infer_instance
    · change LocallyQuasiFinite (ιFinite hF' hx' ≫ f)
      rw [ιFinite_map]
      have : IsFinite (Spec.map (CommRingCat.ofHom (finiteChartMap (k := k) h))) :=
        isFinite_specMap_finiteChartMap hF' hxt h
      infer_instance
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end TauCeti.AlgebraicGeometry.twoChartModel
