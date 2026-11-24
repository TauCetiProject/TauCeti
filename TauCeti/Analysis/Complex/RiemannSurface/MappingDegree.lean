/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.FundamentalClass
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Automorphism
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Topology.Perfect

/-!
# The mapping degree of a holomorphic map between compact Riemann surfaces

A compact Riemann surface carries the canonical orientation of its complex structure
(`TauCeti.complexManifoldOrientation`), here reindexed from `Fin (2 * finrank ℂ ℂ)` to `Fin 2`,
the degree of top forms on the underlying real surface. For these orientations a smooth map
`f : X → Y` between compact Riemann surfaces, with `Y` connected, has a mapping degree
`TauCeti.degree`, the signed count of the preimages of a regular value. This is the degree of the
degree formula `∫_X f^* φ = deg(f) ∫_Y φ` (`TauCeti.integralTopForm_mpullback_eq_degree_mul`),
through which symplectic areas of maps from a surface are computed.

This file shows that for a holomorphic map the mapping degree is the analytic degree
`TauCeti.RiemannSurface.degree`, the number of preimages of any point counted with local
multiplicities
(`TauCeti.RiemannSurface.FiniteHolomorphicMap.degree_reindex_complexManifoldOrientation`). Both
are the degree defined through local homology: the mapping degree by
`TauCeti.Manifold.Orientation.degree_toHomologicalOrientation_eq_degree`, and the analytic degree
by `TauCeti.RiemannSurface.FiniteHolomorphicMap.degree_complexHomologicalOrientation`.

Consequently, for a holomorphic map `f : X → Y` from a compact connected Riemann surface to a
connected one, the mapping degree has the rigidity of the analytic degree:

* it is nonnegative (`MDifferentiable.degree_reindex_complexManifoldOrientation_nonneg`), and it
  vanishes exactly when `f` is constant
  (`MDifferentiable.degree_reindex_complexManifoldOrientation_eq_zero_iff`);
* it is `1` exactly when `f` is a biholomorphism
  (`MDifferentiable.degree_reindex_complexManifoldOrientation_eq_one_iff`).

On the Riemann sphere `OnePoint ℂ`, whose biholomorphisms are the Möbius transformations
(`Diffeomorph.exists_coe_eq_smul`), a holomorphic map therefore has mapping degree one exactly when
it is `z ↦ g • z` for some `g ∈ GL(2, ℂ)`
(`MDifferentiable.degree_reindex_complexManifoldOrientation_eq_one_iff_exists_smul`). So a
holomorphic map whose degree is read off from an area, as for the projection of a
pseudoholomorphic sphere to a sphere factor of the target, is a biholomorphism, and on the sphere a
Möbius transformation, when that degree is `1`. A map between complex manifolds is
pseudoholomorphic for their almost complex structures exactly when it is holomorphic
(`TauCeti.isPseudoholomorphic_ofComplexManifold_iff`), so these statements apply to
pseudoholomorphic maps as well.

## Main results

* `TauCeti.RiemannSurface.FiniteHolomorphicMap.degree_reindex_complexManifoldOrientation`: the
  mapping degree of a finite holomorphic map is its analytic degree.
* `MDifferentiable.degree_reindex_complexManifoldOrientation_of_ne`: the same for a nonconstant
  holomorphic map from a compact connected Riemann surface.
* `MDifferentiable.degree_reindex_complexManifoldOrientation_nonneg`: the mapping degree of a
  holomorphic map is nonnegative.
* `MDifferentiable.degree_reindex_complexManifoldOrientation_eq_zero_iff`: it vanishes exactly for
  constant maps.
* `MDifferentiable.degree_reindex_complexManifoldOrientation_eq_one_iff`: it is `1` exactly for
  biholomorphisms.
* `MDifferentiable.degree_reindex_complexManifoldOrientation_eq_one_iff_exists_smul`: a holomorphic
  map of the Riemann sphere has mapping degree one exactly when it is a Möbius transformation.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §4 (the degree of a holomorphic map between compact Riemann surfaces).
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 17 (the degree of a smooth map).
-/

public section

open Function Module Set Topology
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti.RiemannSurface

variable {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y] [T2Space X] [T2Space Y]

namespace FiniteHolomorphicMap

/-- **The mapping degree of a finite holomorphic map is its analytic degree.** For the canonical
orientations of compact Riemann surfaces `X` and `Y`, with `Y` connected, the signed count
`TauCeti.degree` of the preimages of a regular value of a finite holomorphic map `f : X → Y` is
the number `TauCeti.RiemannSurface.degree f` of preimages of any point counted with local
multiplicities. -/
theorem degree_reindex_complexManifoldOrientation [CompactSpace X] [PreconnectedSpace Y]
    (f : FiniteHolomorphicMap X Y) :
    TauCeti.degree ((complexManifoldOrientation ℂ X).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      ((complexManifoldOrientation ℂ Y).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex))) f =
      degree f := by
  have := f.compactSpace_codomain
  have hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 (⟨f, f.holomorphic.continuous⟩ : C(X, Y)) := by
    simpa only [modelWithCornersSelf_restrictScalars, ContinuousMap.coe_mk] using
      (f.holomorphic.contMDiff (n := 1)).restrictScalars ℝ
  have h := Manifold.Orientation.degree_toHomologicalOrientation_eq_degree
    Complex.finrank_real_complex
    ((complexManifoldOrientation ℂ X).reindex
      (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
    ((complexManifoldOrientation ℂ Y).reindex
      (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
    hf f.holomorphic.continuous.isProperMap
  rw [ContinuousMap.coe_mk, ← complexHomologicalOrientation_def,
    ← complexHomologicalOrientation_def] at h
  rw [← h]
  exact degree_complexHomologicalOrientation f

end FiniteHolomorphicMap

end TauCeti.RiemannSurface

namespace MDifferentiable

open TauCeti TauCeti.RiemannSurface

variable {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y] [T2Space X] [T2Space Y]
  [CompactSpace X] [PreconnectedSpace X] [PreconnectedSpace Y] {f : X → Y}

/-- The mapping degree of a holomorphic map from a compact connected Riemann surface to a connected
one is its analytic degree when the map is not constant. -/
theorem degree_reindex_complexManifoldOrientation_of_ne (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hne : ∃ x x', f x ≠ f x') :
    TauCeti.degree ((complexManifoldOrientation ℂ X).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      ((complexManifoldOrientation ℂ Y).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex))) f =
      RiemannSurface.degree f := by
  simpa using
    (FiniteHolomorphicMap.ofMDifferentiable hf hne).degree_reindex_complexManifoldOrientation

/-- **The mapping degree of a holomorphic map is nonnegative**, for the canonical orientations of
a compact connected Riemann surface and a connected one. -/
theorem degree_reindex_complexManifoldOrientation_nonneg (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    0 ≤ TauCeti.degree ((complexManifoldOrientation ℂ X).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      ((complexManifoldOrientation ℂ Y).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex))) f := by
  by_cases hc : ∀ x x', f x = f x'
  · exact (degree_eq_zero_of_forall_eq (by simp) hc).ge
  · push Not at hc
    rw [degree_reindex_complexManifoldOrientation_of_ne hf hc]
    exact Int.natCast_nonneg _

/-- **A holomorphic map has mapping degree zero exactly when it is constant**, for the canonical
orientations of a compact connected Riemann surface and a connected one. -/
theorem degree_reindex_complexManifoldOrientation_eq_zero_iff
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    TauCeti.degree ((complexManifoldOrientation ℂ X).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      ((complexManifoldOrientation ℂ Y).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex))) f = 0 ↔
      ∀ x x', f x = f x' := by
  refine ⟨fun h ↦ ?_, degree_eq_zero_of_forall_eq (by simp)⟩
  by_contra hc
  push Not at hc
  rw [degree_reindex_complexManifoldOrientation_of_ne hf hc, Nat.cast_eq_zero] at h
  have hpos := degree_pos (FiniteHolomorphicMap.ofMDifferentiable hf hc)
  rw [FiniteHolomorphicMap.coe_ofMDifferentiable] at hpos
  omega

/-- **A holomorphic map has mapping degree one exactly when it is a biholomorphism**, for the
canonical orientations of a nonempty compact connected Riemann surface and a connected one. -/
theorem degree_reindex_complexManifoldOrientation_eq_one_iff [Nonempty X]
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    TauCeti.degree ((complexManifoldOrientation ℂ X).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      ((complexManifoldOrientation ℂ Y).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex))) f = 1 ↔
      ∃ Φ : X ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ Y, ⇑Φ = f := by
  -- In either direction `f` is not constant: a degree-one map is not constant, and a bijection out
  -- of a Riemann surface, which has more than one point, is not constant.
  have hne_of_injective (hinj : Injective f) : ∃ x x', f x ≠ f x' := by
    have := ChartedSpace.perfectSpace (H := ℂ) (X := X)
    have := PerfectSpace.nontrivial X
    obtain ⟨x, x', hxx'⟩ := exists_pair_ne X
    exact ⟨x, x', hinj.ne hxx'⟩
  constructor
  · intro h
    have hne : ∃ x x', f x ≠ f x' := by
      by_contra hc
      push Not at hc
      rw [degree_eq_zero_of_forall_eq (by simp) hc] at h
      exact zero_ne_one h
    rw [degree_reindex_complexManifoldOrientation_of_ne hf hne, Nat.cast_eq_one] at h
    exact ⟨biholomorphOfDegreeEqOne (FiniteHolomorphicMap.ofMDifferentiable hf hne)
      (by rwa [FiniteHolomorphicMap.coe_ofMDifferentiable]), by simp⟩
  · rintro ⟨Φ, rfl⟩
    have hne := hne_of_injective Φ.injective
    rw [degree_reindex_complexManifoldOrientation_of_ne hf hne, Nat.cast_eq_one]
    obtain ⟨x⟩ := ‹Nonempty X›
    have h := degree_eq_one_of_injOn (FiniteHolomorphicMap.ofMDifferentiable hf hne) (x := x)
      (t := univ) Filter.univ_mem (by simpa using Φ.injective)
      fun _ h ↦ Φ.injective (by simpa using h)
    rwa [FiniteHolomorphicMap.coe_ofMDifferentiable] at h

/-- **The holomorphic maps of the Riemann sphere of degree one are the Möbius transformations.** A
holomorphic map `f` of the Riemann sphere has mapping degree one, for the canonical orientation of
the sphere, exactly when it is `z ↦ g • z` for some `g ∈ GL(2, ℂ)`. -/
theorem degree_reindex_complexManifoldOrientation_eq_one_iff_exists_smul
    {f : OnePoint ℂ → OnePoint ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    TauCeti.degree ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      f = 1 ↔ ∃ g : GL (Fin 2) ℂ, f = (g • ·) := by
  rw [hf.degree_reindex_complexManifoldOrientation_eq_one_iff]
  constructor
  · rintro ⟨Φ, rfl⟩
    exact Φ.exists_coe_eq_smul (by simp)
  · rintro ⟨g, rfl⟩
    exact ⟨Diffeomorph.constSmul 𝓘(ℂ) _ g, funext fun x ↦ Diffeomorph.constSmul_apply g x⟩

end MDifferentiable
