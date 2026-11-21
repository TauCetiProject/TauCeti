/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Unramified
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.KummerOrthogonality
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Local

/-!
# Local and unramified orthogonality for the isogeny Weil cup product

Over a nonarchimedean local field `K`, for an isogeny `φ : E₁ → E₂` of degree `n` invertible in
`K`, the field-level Kummer orthogonality of
`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/WeilPairing/KummerOrthogonality.lean`
specializes to local Tate duality, including at places dividing `n`:

* `TauCeti.Isogeny.localTateKerWeilPairing_kummerMap_kummerMap_eq_zero`,
  `TauCeti.Isogeny.localTateKerWeilPairing_eq_zero_of_mem_range_kummerMap`, and
  `TauCeti.Isogeny.localTateKerWeilPairing_eq_zero_of_mem_ker`: the local `φ`- and `φ̂`-Selmer
  kernels are orthogonal under `localTateKerWeilPairing`, which therefore descends to
  `TauCeti.Isogeny.localTateKerWeilQuotientPairing`.
* `TauCeti.Isogeny.kerH1WeilPairing_eq_zero_of_mem_unramifiedKerCohomology` and
  `TauCeti.Isogeny.localTateKerWeilPairing_eq_zero_of_mem_unramifiedKerCohomology`: the unramified
  subgroups `φ.unramifiedKerCohomology` and `φ.dual.unramifiedKerCohomology` are likewise
  orthogonal under both the Weil cup product and local Tate duality, since
  `H²(G_K ⧸ I_K, μ_n^{I_K})` vanishes (`AddMonoidHom.explicitCup11_eq_zero_of_mem_unramifiedH1`).

Orthogonality is the input needed to identify the two local conditions as exact annihilators;
equality with the annihilators additionally requires an order calculation.

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

omit [DecidableEq K] in
/-- The kernels defining the local Selmer conditions of an isogeny and of its dual are orthogonal
under local Tate duality, including at places dividing the degree of the isogeny. -/
theorem localTateKerWeilPairing_eq_zero_of_mem_ker
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl
      continuous_of_discreteTopology).ker)
    (hb : b ∈ (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl
      continuous_of_discreteTopology).ker) :
    φ.localTateKerWeilPairing hn a b = 0 := by
  simp only [localTateKerWeilPairing_apply, φ.kerH1WeilPairing_eq_zero_of_mem_ker hn ha hb,
    map_zero]

omit [DecidableEq K] in
/-- **The local Tate pairing on the local Selmer quotient.** Because the local Selmer kernels of
`φ` and `φ̂` are orthogonal under `localTateKerWeilPairing`, restricting the second variable to the
local `φ̂`-Selmer kernel descends the first variable to the quotient by the local `φ`-Selmer
kernel. -/
def localTateKerWeilQuotientPairing :
    (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff ⧸
      (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology).ker) →+
    (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl continuous_of_discreteTopology).ker →+
    ZMod φ.degree :=
  QuotientAddGroup.lift _
    ((φ.localTateKerWeilPairing hn).compl₂
      (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl
        continuous_of_discreteTopology).ker.subtype)
    fun _ ha ↦ AddMonoidHom.ext fun b ↦
      φ.localTateKerWeilPairing_eq_zero_of_mem_ker hn ha b.property

omit [DecidableEq K] in
/-- Evaluating `localTateKerWeilQuotientPairing` on a quotient class computes
`localTateKerWeilPairing`. -/
@[simp]
theorem localTateKerWeilQuotientPairing_mk
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff)
    (b : (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl
      continuous_of_discreteTopology).ker) :
    φ.localTateKerWeilQuotientPairing hn (QuotientAddGroup.mk a) b =
      φ.localTateKerWeilPairing hn a b :=
  (rfl)

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

end
