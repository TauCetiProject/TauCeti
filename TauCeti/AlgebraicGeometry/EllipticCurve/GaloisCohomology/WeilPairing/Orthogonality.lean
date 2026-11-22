/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Unramified
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Local

/-!
# Unramified orthogonality for the isogeny Weil cup product

Over a nonarchimedean local field `K`, for an isogeny `φ : E₁ → E₂` of degree `n` invertible in
`K`:

* `TauCeti.Isogeny.kerH1WeilPairing_eq_zero_of_mem_unramifiedKerCohomology` and
  `TauCeti.Isogeny.localTateKerWeilPairing_eq_zero_of_mem_unramifiedKerCohomology`: the unramified
  subgroups `φ.unramifiedKerCohomology` and `φ.dual.unramifiedKerCohomology` are orthogonal under
  both the Weil cup product and local Tate duality, since `H²(G_K ⧸ I_K, μ_n^{I_K})` vanishes
  (`AddMonoidHom.explicitCup11_eq_zero_of_mem_unramifiedH1`).

Field-level Kummer orthogonality is in
`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/WeilPairing/Kummer/Orthogonality.lean`,
and local Tate Kummer and Selmer-kernel orthogonality (including
`TauCeti.Isogeny.localTateKerWeilQuotientPairing`) are in
`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/WeilPairing/Local.lean`.

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
