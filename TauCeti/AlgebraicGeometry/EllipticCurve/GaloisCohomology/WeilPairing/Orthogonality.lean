/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Restriction
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Unramified
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.KummerComparison

/-!
# Orthogonality of the isogeny Kummer images and unramified cohomology

For an isogeny `φ : E₁ → E₂` of degree `n` invertible in the field `K`, the Kummer images of
`E₂(K)` in `H¹(K, E₁[φ])` and of `E₁(K)` in `H¹(K, E₂[φ̂])` are orthogonal under the isogeny
Weil cup product. The vanishing holds in `H²(K, μ_n)` over any field, before applying a local
Brauer invariant. Consequently the images are orthogonal under local Tate duality over a
nonarchimedean local field, including at places dividing `n`.

The kernels of the maps to point-coefficient cohomology satisfy the same vanishing
(`kerH1WeilPairing_eq_zero_of_mem_ker`). These kernels define the Selmer local conditions,
so the result applies over both finite and infinite completions of a number field.
For global classes satisfying the Selmer local conditions over an extension `L/K` in which the
degree is invertible, the Brauer-valued cup product of their restrictions, for the base change of
`φ` and its dual, vanishes (`kerWeilBrauerPairing_kerRes_dualKerRes_eq_zero`).
Over a nonarchimedean local field, the unramified subgroups `W.unramifiedTorsionCohomology m`,
`φ.unramifiedKerCohomology`, and `φ.dual.unramifiedKerCohomology` are likewise orthogonal under
both the Weil cup product and local Tate duality
(`WeierstrassCurve.torsionH1WeilPairing_eq_zero_of_mem_unramifiedTorsionCohomology`,
`WeierstrassCurve.localTateWeilPairing_eq_zero_of_mem_unramifiedTorsionCohomology`,
`TauCeti.Isogeny.kerH1WeilPairing_eq_zero_of_mem_unramifiedKerCohomology`, and
`TauCeti.Isogeny.localTateKerWeilPairing_eq_zero_of_mem_unramifiedKerCohomology`), since
`H²(G_K ⧸ I_K, μ_n^{I_K})` vanishes (`AddMonoidHom.explicitCup11_eq_zero_of_mem_unramifiedH1`).
Orthogonality is the input needed to identify the two local conditions as exact annihilators;
equality with the annihilators additionally requires an order calculation.

The Kummer proof uses the adjoint inclusion `E₁[φ] → E₁[n]` and projection `E₁[n] → E₂[φ̂]` to
reduce the cup product to the multiplication-by-`n` Kummer images, whose isotropy is proved in
`WeierstrassCurve.torsionH1WeilPairing_kummerMap_kummerMap_eq_zero`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, §§2–3.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology

section Unramified

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (W : WeierstrassCurve K) [W.IsElliptic]
  {m : ℕ} (hm : IsUnit (m : K))

/-- **Unramified `m`-torsion cohomology is isotropic for the Weil cup product** over any
nonarchimedean local field in which `m` is invertible; no good-reduction hypothesis is required
and the residue characteristic may divide `m`. -/
theorem torsionH1WeilPairing_eq_zero_of_mem_unramifiedTorsionCohomology
    {a b : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)}
    (ha : a ∈ W.unramifiedTorsionCohomology m) (hb : b ∈ W.unramifiedTorsionCohomology m) :
    W.torsionH1WeilPairing m hm a b = 0 := by
  have := hm.neZero_natCast
  rw [unramifiedTorsionCohomology_eq_unramifiedH1] at ha hb
  rw [W.torsionH1WeilPairing_eq_explicitCup11 m hm]
  exact (W.torsionCoeffWeilPairing m hm).explicitCup11_eq_zero_of_mem_unramifiedH1
    continuous_of_discreteTopology (W.torsionCoeffWeilPairing_smul m hm) ha hb

end Unramified

section UnramifiedLocalTate

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (W : WeierstrassCurve K) [W.IsElliptic]
  {m : ℕ} (hm : IsUnit (m : K))

/-- **Unramified `m`-torsion cohomology is isotropic for the local Tate pairing** over any
nonarchimedean local field in which `m` is invertible; no good-reduction hypothesis is required
and the residue characteristic may divide `m`. -/
theorem localTateWeilPairing_eq_zero_of_mem_unramifiedTorsionCohomology
    {a b : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)}
    (ha : a ∈ W.unramifiedTorsionCohomology m) (hb : b ∈ W.unramifiedTorsionCohomology m) :
    W.localTateWeilPairing m hm a b = 0 := by
  rw [localTateWeilPairing_apply,
    W.torsionH1WeilPairing_eq_zero_of_mem_unramifiedTorsionCohomology hm ha hb, map_zero, map_zero]

end UnramifiedLocalTate

end WeierstrassCurve

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti.ContCohomology
open Hom (ofIsogeny)

section Kummer

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

end Kummer

section Restriction

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- **The Selmer local conditions are orthogonal after restriction.** Let `L/K` be any extension
in which the degree of `φ` is invertible. If the images of `a ∈ H¹(K, E₁[φ])` and
`b ∈ H¹(K, E₂[φ̂])` in `H¹(L, E₁)` and `H¹(L, E₂)` are trivial, then the Brauer-valued isogeny
Weil cup of their restrictions, for the base change of `φ` and its dual, vanishes. -/
theorem kerWeilBrauerPairing_kerRes_dualKerRes_eq_zero
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    {L : Type*} [Field L] [Algebra K L] (τ : SeparableClosure K →ₐ[K] SeparableClosure L)
    (hnL : IsUnit ((φ.baseChange L).degree : L))
    (ha : W₁.pointRes τ
      (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology a) = 0)
    (hb : W₂.pointRes τ
      (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl continuous_of_discreteTopology b) = 0) :
    (φ.baseChange L).kerWeilBrauerPairing hnL (φ.kerRes τ a) (φ.dualKerRes τ b) = 0 := by
  refine ((φ.baseChange L).kerWeilBrauerPairing_eq_zero_iff hnL _ _).2
    ((φ.baseChange L).kerH1WeilPairing_eq_zero_of_mem_ker hnL ?_ ?_)
  · rw [AddMonoidHom.mem_ker, ← pointRes_kerCoeffIncl, ha]
  · rw [AddMonoidHom.mem_ker, ← pointRes_dualKerCoeffIncl, hb]

end Restriction

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

section Unramified

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- **Unramified classes of `φ` and `φ̂` are orthogonal for the isogeny Weil cup product.** Only
invertibility of `deg φ` in `K` is needed; `K` may divide `deg φ` in residue characteristic and no
good-reduction hypothesis is required. -/
theorem kerH1WeilPairing_eq_zero_of_mem_unramifiedKerCohomology (hn : IsUnit (φ.degree : K))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ φ.unramifiedKerCohomology) (hb : b ∈ φ.dual.unramifiedKerCohomology) :
    φ.kerH1WeilPairing hn a b = 0 := by
  have := hn.neZero_natCast
  rw [unramifiedKerCohomology_eq_unramifiedH1] at ha hb
  rw [φ.kerH1WeilPairing_eq_explicitCup11 hn]
  exact (φ.kerCoeffWeilPairing hn).explicitCup11_eq_zero_of_mem_unramifiedH1
    continuous_of_discreteTopology (φ.kerCoeffWeilPairing_smul hn) ha hb

end Unramified

section UnramifiedLocalTate

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- **Unramified classes of `φ` and `φ̂` are orthogonal under local Tate duality.** Only
invertibility of `deg φ` in `K` is needed; `K` may divide `deg φ` in residue characteristic and no
good-reduction hypothesis is required. -/
theorem localTateKerWeilPairing_eq_zero_of_mem_unramifiedKerCohomology
    (hn : IsUnit (φ.degree : K))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ φ.unramifiedKerCohomology) (hb : b ∈ φ.dual.unramifiedKerCohomology) :
    φ.localTateKerWeilPairing hn a b = 0 := by
  rw [localTateKerWeilPairing_apply,
    φ.kerH1WeilPairing_eq_zero_of_mem_unramifiedKerCohomology hn ha hb, map_zero, map_zero]

end UnramifiedLocalTate

end TauCeti.Isogeny
