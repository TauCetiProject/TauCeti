/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Brauer
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Kummer.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Kummer.Comparison

/-!
# Field-level orthogonality of the isogeny Kummer images

For an isogeny `φ : E₁ → E₂` of degree `n` invertible in an arbitrary field `K`, the Kummer
images of `E₂(K)` in `H¹(K, E₁[φ])` and of `E₁(K)` in `H¹(K, E₂[φ̂])` are orthogonal under both
the isogeny Weil cup product in `H²(K, μ_n)` and its Brauer-valued pairing in `Br K`. The kernels
of the maps to point-coefficient cohomology satisfy the same vanishing.

No local-field or unramified-cohomology hypotheses are needed here; nonarchimedean local Tate
duality is in `TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/WeilPairing/Local.lean`,
and unramified orthogonality is in
`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/WeilPairing/Orthogonality.lean`.

The proof reduces the cup product via `TauCeti.Isogeny.kerH1WeilPairing_kummerMap` to the
multiplication-by-`n` Kummer images, whose isotropy is proved in
`WeierstrassCurve.torsionH1WeilPairing_kummerMap_kummerMap_eq_zero`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, §§2–3.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
-/

public section

noncomputable section

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti.ContCohomology
open Hom (ofIsogeny)

variable {K : Type*} [Field K] [DecidableEq K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine) (hn : IsUnit (φ.degree : K))

/-- The Kummer images of an isogeny and its dual are orthogonal for the Weil cup product.
The vanishing holds over every field in which the degree is invertible. -/
-- Apply before the simplifier unfolds the Kummer maps into connecting maps.
@[simp↓]
theorem kerH1WeilPairing_kummerMap_kummerMap_eq_zero
    (Q : W₂.toAffine.Point) (P : W₁.toAffine.Point) :
    letI := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
    letI := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
    φ.kerH1WeilPairing hn (φ.kummerMap Q) (φ.dual.kummerMap P) = 0 := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
  rw [φ.kerH1WeilPairing_kummerMap hn]
  exact W₁.torsionH1WeilPairing_kummerMap_kummerMap_eq_zero φ.degree hn _ _

/-- The Weil cup product vanishes on the two Kummer subgroups, without a choice of
representing rational points. -/
theorem kerH1WeilPairing_eq_zero_of_mem_range_kummerMap
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff} :
    letI := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
    letI := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
    a ∈ φ.kummerMap.range → b ∈ φ.dual.kummerMap.range → φ.kerH1WeilPairing hn a b = 0 := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
  rintro ⟨Q, rfl⟩ ⟨P, rfl⟩
  exact φ.kerH1WeilPairing_kummerMap_kummerMap_eq_zero hn Q P

omit [DecidableEq K] in
/-- The kernels defining the isogeny and dual-isogeny Selmer local conditions are orthogonal.
A class whose image in the point-coefficient cohomology vanishes pairs trivially with every
such class for the dual isogeny. -/
theorem kerH1WeilPairing_eq_zero_of_mem_ker
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl
      continuous_of_discreteTopology).ker)
    (hb : b ∈ (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl
      continuous_of_discreteTopology).ker) :
    φ.kerH1WeilPairing hn a b = 0 := by
  classical
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
  rw [← range_kummerMap] at ha hb
  exact φ.kerH1WeilPairing_eq_zero_of_mem_range_kummerMap hn ha hb

/-- The Brauer-valued isogeny Weil pairing vanishes on the Kummer classes of rational points. -/
@[simp↓]
theorem kerWeilBrauerPairing_kummerMap_kummerMap_eq_zero
    (Q : W₂.toAffine.Point) (P : W₁.toAffine.Point) :
    letI := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
    letI := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
    φ.kerWeilBrauerPairing hn (φ.kummerMap Q) (φ.dual.kummerMap P) = 0 := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
  simp only [kerWeilBrauerPairing_apply, kerH1WeilPairing_kummerMap_kummerMap_eq_zero, map_zero]

/-- The Brauer-valued isogeny Weil pairing vanishes on the two Kummer subgroups. -/
theorem kerWeilBrauerPairing_eq_zero_of_mem_range_kummerMap
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff} :
    letI := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
    letI := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
    a ∈ φ.kummerMap.range → b ∈ φ.dual.kummerMap.range → φ.kerWeilBrauerPairing hn a b = 0 := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
  intro ha hb
  simp only [kerWeilBrauerPairing_apply, φ.kerH1WeilPairing_eq_zero_of_mem_range_kummerMap hn ha hb,
    map_zero]

omit [DecidableEq K] in
/-- The Selmer local-condition kernels for an isogeny and its dual pair to zero in `Br K`.
This applies over every field in which `deg φ` is invertible, including `ℝ` and `ℂ`. -/
theorem kerWeilBrauerPairing_eq_zero_of_mem_ker
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl
      continuous_of_discreteTopology).ker)
    (hb : b ∈ (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl
      continuous_of_discreteTopology).ker) :
    φ.kerWeilBrauerPairing hn a b = 0 := by
  simp only [kerWeilBrauerPairing_apply, φ.kerH1WeilPairing_eq_zero_of_mem_ker hn ha hb, map_zero]

end TauCeti.Isogeny

end
