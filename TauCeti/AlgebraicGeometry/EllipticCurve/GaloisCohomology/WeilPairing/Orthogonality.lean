/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.KummerComparison

/-!
# Orthogonality of the isogeny Kummer images

For an isogeny `φ : E₁ → E₂` of degree `n` invertible in the field `K`, the Kummer images of
`E₂(K)` in `H¹(K, E₁[φ])` and of `E₁(K)` in `H¹(K, E₂[φ̂])` are orthogonal under the isogeny
Weil cup product. The vanishing holds in `H²(K, μ_n)` over any field, before applying a local
Brauer invariant. Consequently the images are orthogonal under local Tate duality over a
nonarchimedean local field, including at places dividing `n`.

The kernels of the maps to point-coefficient cohomology satisfy the same vanishing
(`kerH1WeilPairing_eq_zero_of_mem_ker`). These kernels define the Selmer local conditions,
so the result applies over both finite and infinite completions of a number field.
Orthogonality is the input needed to identify the two local conditions as exact annihilators;
equality with the annihilators additionally requires an order calculation.

The proof uses the adjoint inclusion `E₁[φ] → E₁[n]` and projection `E₁[n] → E₂[φ̂]` to reduce
the cup product to the multiplication-by-`n` Kummer images, whose isotropy is proved in
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

section Local

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DecidableEq K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine) (hn : IsUnit (φ.degree : K))

/-- The local Tate pairing of the Kummer classes for an isogeny and its dual vanishes,
with no restriction on the residue characteristic. -/
-- Apply before the local invariant and the Kummer maps are simplified separately.
@[simp↓]
theorem localTateKerWeilPairing_kummerMap_kummerMap_eq_zero
    (Q : W₂.toAffine.Point) (P : W₁.toAffine.Point) :
    letI := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
    letI := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
    φ.localTateKerWeilPairing hn (φ.kummerMap Q) (φ.dual.kummerMap P) = 0 := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
  simp only [localTateKerWeilPairing_apply, kerH1WeilPairing_kummerMap_kummerMap_eq_zero,
    map_zero]

/-- The two local Kummer subgroups are orthogonal under local Tate duality, including at
places dividing the degree of the isogeny. -/
theorem localTateKerWeilPairing_eq_zero_of_mem_range_kummerMap
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff} :
    letI := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
    letI := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
    a ∈ φ.kummerMap.range → b ∈ φ.dual.kummerMap.range →
      φ.localTateKerWeilPairing hn a b = 0 := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
  intro ha hb
  simp only [localTateKerWeilPairing_apply,
    φ.kerH1WeilPairing_eq_zero_of_mem_range_kummerMap hn ha hb, map_zero]

end Local

end TauCeti.Isogeny
