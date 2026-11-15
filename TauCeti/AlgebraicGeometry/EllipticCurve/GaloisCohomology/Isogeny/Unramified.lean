/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Unramified
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Local
public import TauCeti.NumberTheory.LocalField.Unramified.Cohomology
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.AlmostEverywhere

/-!
# Unramified Galois cohomology and the unramified local condition of an isogeny

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a nonarchimedean local field `K`. The
**unramified kernel cohomology**

```text
φ.unramifiedKerCohomology = unramifiedH1 K (ofIsogeny φ).KerCoeff ≤ H¹(G_K, E₁[φ])
```

consists of the degree-one classes vanishing on the inertia subgroup `I_K`. Since `E₁(Kˢ)[φ]` is
finite (`TauCeti.Isogeny.finite_kerCoeff_ofIsogeny`), the Frobenius order formula
(`TauCeti.natCard_unramifiedH1_eq_natCard_H0`) and the invariant identification `H⁰(G_K, E₁[φ]) ≃+
E₁(K)[φ]` (`TauCeti.Isogeny.Hom.kerPointMapEquivInvariants`) give

```text
#φ.unramifiedKerCohomology = #E₁(K)[φ]
```

for every isogeny `φ`, with no separability, good-reduction, or residue-characteristic assumption
(`TauCeti.Isogeny.natCard_unramifiedKerCohomology_eq_natCard_ker`). Likewise, when `deg φ` is
invertible in `K`, the unramified subgroups `φ.unramifiedKerCohomology` and
`φ.dual.unramifiedKerCohomology` are orthogonal under the isogeny Weil cup product and under local
Tate duality (`TauCeti.Isogeny.kerH1WeilPairing_eq_zero_of_mem_unramifiedKerCohomology` and
`TauCeti.Isogeny.localTateKerWeilPairing_eq_zero_of_mem_unramifiedKerCohomology`).

When `W₁` has good reduction over `𝒪[K]` and `deg φ` is prime to the residue characteristic, any
point `Q ∈ E₁(Kˢ)` with `φ(Q) = P ∈ E₂(K)` satisfies `deg φ • Q = φ̂(P) ∈ E₁(K)`, so inertia fixes
`Q` (`TauCeti.Isogeny.smul_pointCoeff_eq_self_of_pointCoeffMap_eq_basePointCoeff`). Thus the local
Kummer image is unramified (`TauCeti.Isogeny.range_kummerMap_le_unramifiedKerCohomology`).

At the completion `F_u` of the fraction field `F` of a Dedekind domain `A` at a height-one prime `u`
with finite residue field, if both `W₁` and `W₂` have elliptic integral models over `𝒪[F_u]` and
`deg φ ∉ u`, the local Kummer-cokernel index `[E₂(F_u) : φ(E₁(F_u))]` equals `#E₁(F_u)[φ]`
(`TauCeti.Isogeny.Hom.index_range_eq_card_ker_of_isElliptic_integralModel`), matching
`#φ.unramifiedKerCohomology`. Hence the local Kummer condition **coincides** with the unramified
cohomology (`TauCeti.Isogeny.ker_explicitCoeff1_kerCoeffIncl_eq_unramifiedKerCohomology` and
`TauCeti.Isogeny.range_kummerMap_eq_unramifiedKerCohomology`). Globally over a Dedekind domain with
finite residue fields, for any isogeny of degree nonzero in `K`:

* every `φ`-Selmer class is unramified outside the bad primes and the divisors of `deg φ`
  (`TauCeti.Isogeny.selmerGroup_le_unramifiedOutsideKerCohomology` and
  `TauCeti.Isogeny.exists_finset_selmerGroup_le_unramifiedOutsideKerCohomology`);
* for all but finitely many places `v`, the local condition of `φ.selmerStructure τ` at `v` equals
  `(φ.baseChange K_v).unramifiedKerCohomology`
  (`TauCeti.Isogeny.eventually_localCondition_selmerStructure_eq_unramifiedKerCohomology`).

## Main definitions

* `TauCeti.Isogeny.unramifiedKerCohomology`: the subgroup `unramifiedH1 K E₁[φ]` of
  `H¹(G_K, E₁[φ])`.
* `TauCeti.Isogeny.unramifiedOutsideKerCohomology`: the global subgroup of `H¹(G_K, E₁[φ])`
  consisting of classes unramified at every prime `v ∉ S`.

## Main results

* `TauCeti.Isogeny.natCard_unramifiedKerCohomology_eq_natCard_ker`: `#H¹_ur(K, E₁[φ]) = #E₁(K)[φ]`.
* `TauCeti.Isogeny.kerH1WeilPairing_eq_zero_of_mem_unramifiedKerCohomology`,
  `TauCeti.Isogeny.localTateKerWeilPairing_eq_zero_of_mem_unramifiedKerCohomology`: orthogonality of
  unramified classes of `φ` and `φ̂` under the isogeny Weil cup product and local Tate duality.
* `TauCeti.Isogeny.range_kummerMap_le_unramifiedKerCohomology`: at good reduction of `W₁` prime to
  `deg φ`, every Kummer class is unramified.
* `TauCeti.Isogeny.ker_explicitCoeff1_kerCoeffIncl_eq_unramifiedKerCohomology`,
  `TauCeti.Isogeny.range_kummerMap_eq_unramifiedKerCohomology`: at good reduction of `W₁` and `W₂`
  over a Dedekind completion prime to `deg φ`, the local Kummer image equals `H¹_ur(F_u, E₁[φ])`.
* `TauCeti.Isogeny.selmerGroup_le_unramifiedOutsideKerCohomology`,
  `TauCeti.Isogeny.eventually_localCondition_selmerStructure_eq_unramifiedKerCohomology`: global
  unramifiedness of `Sel_φ` and identification of the Selmer local condition at almost every place.

## References

* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, Lemma 3.2 and §6.
* E. F. Schaefer, *Class groups and Selmer groups*, J. Number Theory 56 (1996), 79–114, §3.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.1.5 and X.4.
-/

public noncomputable section

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti.ContCohomology _root_.ValuativeRel
open Hom (ofIsogeny)

section Local

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- **The unramified kernel cohomology `H¹_ur(K, E₁[φ])`**: the subgroup of `H¹(G_K, E₁[φ])`
consisting of classes whose restriction to the inertia subgroup vanishes. -/
def unramifiedKerCohomology :
    AddSubgroup (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) :=
  unramifiedH1 K (ofIsogeny φ).KerCoeff

/-- `unramifiedKerCohomology` is `TauCeti.unramifiedH1` on `(ofIsogeny φ).KerCoeff`. -/
theorem unramifiedKerCohomology_eq_unramifiedH1 :
    φ.unramifiedKerCohomology = unramifiedH1 K (ofIsogeny φ).KerCoeff :=
  (rfl)

/-- A class in `H¹(G_K, E₁[φ])` is unramified exactly when its restriction to inertia vanishes. -/
@[simp]
theorem mem_unramifiedKerCohomology_iff
    {c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff} :
    c ∈ φ.unramifiedKerCohomology ↔
      explicitRes1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) c = 0 :=
  mem_unramifiedH1_iff

/-- `φ.unramifiedKerCohomology` is finite, since `(ofIsogeny φ).KerCoeff` is finite. -/
instance finite_unramifiedKerCohomology : Finite φ.unramifiedKerCohomology :=
  inferInstanceAs (Finite (unramifiedH1 K (ofIsogeny φ).KerCoeff))

/-- **The unramified cohomology of `E₁[φ]` has the order of the rational kernel `E₁(K)[φ]`.** No
separability, good-reduction, or residue-characteristic assumption is needed. -/
theorem natCard_unramifiedKerCohomology_eq_natCard_ker [DecidableEq K] :
    Nat.card φ.unramifiedKerCohomology = Nat.card (ofIsogeny φ).pointMapHom.ker :=
  (natCard_unramifiedH1_eq_natCard_H0 K (ofIsogeny φ).KerCoeff).trans
    (Nat.card_congr (ofIsogeny φ).kerPointMapEquivInvariants.symm.toEquiv)

/-- Inclusion `E₁[φ] → E₁[deg φ]` carries unramified classes to unramified classes. -/
theorem explicitCoeff1_kerCoeffToTorsionCoeff_mem_unramifiedTorsionCohomology
    {c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    (hc : c ∈ φ.unramifiedKerCohomology) :
    explicitCoeff1 _ _ φ.kerCoeffToTorsionCoeff continuous_of_discreteTopology c ∈
      W₁.unramifiedTorsionCohomology φ.degree := by
  rw [mem_unramifiedTorsionCohomology_iff, ← mem_unramifiedH1_iff]
  exact explicitCoeff1_mem_unramifiedH1 φ.kerCoeffToTorsionCoeff continuous_of_discreteTopology hc

/-- Projection `E₁[deg φ] → E₂[φ̂]` carries unramified classes to unramified classes. -/
theorem explicitCoeff1_torsionCoeffToDualKerCoeff_mem_unramifiedKerCohomology
    {c : H1 (AbsoluteGaloisGroup K) (W₁.TorsionCoeff φ.degree)}
    (hc : c ∈ W₁.unramifiedTorsionCohomology φ.degree) :
    explicitCoeff1 _ _ φ.torsionCoeffToDualKerCoeff continuous_of_discreteTopology c ∈
      φ.dual.unramifiedKerCohomology := by
  refine explicitCoeff1_mem_unramifiedH1 φ.torsionCoeffToDualKerCoeff
    continuous_of_discreteTopology ?_
  rwa [mem_unramifiedH1_iff, ← mem_unramifiedTorsionCohomology_iff]

/-- **Unramified kernel classes restrict to unramified classes** along any valuative extension of
nonarchimedean local fields, with no reduction hypothesis on `W₁` or `W₂`. -/
theorem kerRes_mem_unramifiedKerCohomology {L : Type*} [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    (τ : SeparableClosure K →ₐ[K] SeparableClosure L)
    {c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    (hc : c ∈ φ.unramifiedKerCohomology) :
    φ.kerRes τ c ∈ (φ.baseChange L).unramifiedKerCohomology := by
  rw [unramifiedKerCohomology_eq_unramifiedH1, kerRes_eq_explicitMap1]
  exact explicitMap1_mem_unramifiedH1 τ (φ.kerCoeffBaseChange τ) continuous_of_discreteTopology
    (φ.kerCoeffBaseChange_smul τ) hc

/-- **Unramified classes of `φ` and `φ̂` are orthogonal for the isogeny Weil cup product.** Only
invertibility of `deg φ` in `K` is needed; `K` may divide `deg φ` in residue characteristic and no
good-reduction hypothesis is required. -/
theorem kerH1WeilPairing_eq_zero_of_mem_unramifiedKerCohomology (hn : IsUnit (φ.degree : K))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ φ.unramifiedKerCohomology) (hb : b ∈ φ.dual.unramifiedKerCohomology) :
    φ.kerH1WeilPairing hn a b = 0 := by
  have := hn.neZero_natCast
  rw [φ.kerH1WeilPairing_eq_explicitCup11 hn]
  exact explicitCup11_eq_zero_of_mem_unramifiedH1 (φ.kerCoeffWeilPairing hn)
    (φ.kerCoeffWeilPairing_smul hn) ha hb

end Local

section LocalTate

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- **Unramified classes of `φ` and `φ̂` are orthogonal under local Tate duality.** -/
theorem localTateKerWeilPairing_eq_zero_of_mem_unramifiedKerCohomology
    (hn : IsUnit (φ.degree : K))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ φ.unramifiedKerCohomology) (hb : b ∈ φ.dual.unramifiedKerCohomology) :
    φ.localTateKerWeilPairing hn a b = 0 := by
  rw [localTateKerWeilPairing_apply,
    φ.kerH1WeilPairing_eq_zero_of_mem_unramifiedKerCohomology hn ha hb, map_zero, map_zero]

end LocalTate

/-! ### Good reduction away from the degree -/

section GoodReduction

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  [IsIntegral 𝒪[K] W₁] [(integralModel 𝒪[K] W₁).IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

variable {φ} in
/-- **At good reduction of `W₁` prime to `deg φ`, inertia fixes every `φ`-preimage of a `K`-rational
point of `W₂`.** Indeed `φ̂ ∘ φ = [deg φ]` sends `Q` to the `K`-rational point `φ̂(P)`. -/
theorem smul_pointCoeff_eq_self_of_pointCoeffMap_eq_basePointCoeff [DecidableEq K]
    (hdeg : (φ.degree : 𝓀[K]) ≠ 0) {P : W₂.toAffine.Point} {Q : W₁.PointCoeff}
    (hQ : (ofIsogeny φ).pointCoeffMap Q = W₂.basePointCoeff P)
    {σ : Gal(AlgebraicClosure K/K)} (hσ : σ ∈ inertiaSubgroup K) :
    absoluteGaloisGroupRestrictEquiv K σ • Q = Q := by
  cases Subsingleton.elim ‹DecidableEq K› (fun a b ↦ Classical.propDecidable (a = b))
  classical
  have hdegQ : φ.degree • Q = W₁.basePointCoeff ((ofIsogeny φ.dual).pointMap P) := by
    rw [← φ.pointCoeffMap_dual_pointCoeffMap Q, hQ, Hom.pointCoeffMap_basePointCoeff]
  exact W₁.smul_pointCoeff_eq_self_of_mem_inertiaSubgroup hdeg hdegQ hσ

/-- **At good reduction of `W₁` prime to `deg φ`, inertia acts trivially on `E₁(Kˢ)[φ]`.** -/
theorem smul_kerCoeff_eq_self_of_mem_inertiaSubgroup (hdeg : (φ.degree : 𝓀[K]) ≠ 0)
    (Q : (ofIsogeny φ).KerCoeff) {σ : Gal(AlgebraicClosure K/K)} (hσ : σ ∈ inertiaSubgroup K) :
    absoluteGaloisGroupRestrictEquiv K σ • Q = Q := by
  classical
  have hQ : (ofIsogeny φ).pointCoeffMap (Q : W₁.PointCoeff) = W₂.basePointCoeff 0 := by
    rw [map_zero]
    exact Q.2
  exact Subtype.ext (smul_pointCoeff_eq_self_of_pointCoeffMap_eq_basePointCoeff hdeg hQ hσ)

variable {φ} in
/-- The Kummer cocycle of a `φ`-preimage of a `K`-rational point vanishes on inertia when `W₁` has
good reduction and `deg φ` is prime to the residue characteristic. -/
theorem kummerCocycle_eq_zero_of_mem_inertiaSubgroup [DecidableEq K]
    (hdeg : (φ.degree : 𝓀[K]) ≠ 0) {P : W₂.toAffine.Point} {Q : W₁.PointCoeff}
    (hQ : (ofIsogeny φ).pointCoeffMap Q = W₂.basePointCoeff P)
    {σ : Gal(AlgebraicClosure K/K)} (hσ : σ ∈ inertiaSubgroup K) :
    Hom.kummerCocycle hQ (absoluteGaloisGroupRestrictEquiv K σ) = 0 := by
  apply Subtype.ext
  rw [Hom.coe_kummerCocycle,
    smul_pointCoeff_eq_self_of_pointCoeffMap_eq_basePointCoeff hdeg hQ hσ, sub_self]
  rfl

/-- **At good reduction of `W₁` prime to `deg φ`, every Kummer class of `φ` is unramified.** -/
theorem kummerMap_mem_unramifiedKerCohomology [DecidableEq K]
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField]
    (hdeg : (φ.degree : 𝓀[K]) ≠ 0) (P : W₂.toAffine.Point) :
    φ.kummerMap P ∈ φ.unramifiedKerCohomology := by
  obtain ⟨Q, hQ⟩ := φ.pointCoeffMap_ofIsogeny_surjective (W₂.basePointCoeff P)
  rw [mem_unramifiedKerCohomology_iff, kummerMap_eq_H1pi hQ]
  have hzero : cocyclesMap1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff
      ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom)
      (ofIsogeny φ).KerCoeff (ContinuousMonoidHom.subgroupSubtype _)
      (AddMonoidHom.id _) continuous_id
      (ContinuousMonoidHom.id_subgroupSubtype_smul _ _)
      ⟨Hom.kummerCocycle hQ, Hom.kummerCocycle_mem_Z1 hQ⟩ = 0 := by
    apply Subtype.ext
    funext σ
    rw [cocyclesMap1_apply, AddMonoidHom.id_apply, ContinuousMonoidHom.subgroupSubtype_apply]
    obtain ⟨τ, hτ, hτσ⟩ := σ.2
    rw [← hτσ]
    exact kummerCocycle_eq_zero_of_mem_inertiaSubgroup hdeg hQ hτ
  exact (explicitRes1_mk _ _ _ _).trans (congrArg (H1pi _ _) hzero)

/-- **At good reduction of `W₁` prime to `deg φ`, the local Kummer image lies in the unramified
cohomology.** -/
theorem range_kummerMap_le_unramifiedKerCohomology [DecidableEq K]
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField]
    (hdeg : (φ.degree : 𝓀[K]) ≠ 0) :
    φ.kummerMap.range ≤ φ.unramifiedKerCohomology := by
  rintro _ ⟨P, rfl⟩
  exact φ.kummerMap_mem_unramifiedKerCohomology hdeg P

private theorem natCast_ne_zero_of_residue_ne_zero {L : Type*} [Field L] [ValuativeRel L]
    {n : ℕ} (hn : (n : 𝓀[L]) ≠ 0) : (n : L) ≠ 0 := by
  have hu := (IsLocalRing.residue_ne_zero_iff_isUnit (n : 𝒪[L])).mp (by simpa using hn)
  exact (by simpa using hu.map (algebraMap 𝒪[L] L) : IsUnit (n : L)).ne_zero

/-- **At good reduction of `W₁` prime to `deg φ`, the kernel of `H¹(G_K, E₁[φ]) → H¹(G_K, E₁)` is
contained in `H¹_ur(K, E₁[φ])`.** Unlike `range_kummerMap_le_unramifiedKerCohomology`, this form
needs no `DecidableEq K` or explicit separability instance. -/
theorem ker_explicitCoeff1_kerCoeffIncl_le_unramifiedKerCohomology
    (hdeg : (φ.degree : 𝓀[K]) ≠ 0) :
    (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology).ker ≤
      φ.unramifiedKerCohomology := by
  classical
  have := (φ.isSeparable_dual_and_self_iff.2 (natCast_ne_zero_of_residue_ne_zero hdeg)).2
  rw [← range_kummerMap]
  exact φ.range_kummerMap_le_unramifiedKerCohomology hdeg

end GoodReduction

/-! ### Equality with the local Kummer condition at good reduction -/

section AdicCompletion

open IsDedekindDomain

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A) [Finite (A ⧸ u.asIdeal)]
  {W₁ W₂ : WeierstrassCurve (u.adicCompletion F)} [W₁.IsElliptic] [W₂.IsElliptic]
  [IsIntegral 𝒪[u.adicCompletion F] W₁] [(integralModel 𝒪[u.adicCompletion F] W₁).IsElliptic]
  [IsIntegral 𝒪[u.adicCompletion F] W₂] [(integralModel 𝒪[u.adicCompletion F] W₂).IsElliptic]
  (ψ : Isogeny W₁.toAffine W₂.toAffine)

/-- **At good reduction prime to `deg ψ`, the local Selmer condition equals the unramified kernel
cohomology.** Containment is `ker_explicitCoeff1_kerCoeffIncl_le_unramifiedKerCohomology`, and both
subgroups have the finite order `#E₁(F_u)[ψ]` by
`TauCeti.Isogeny.Hom.index_range_eq_card_ker_of_isElliptic_integralModel` and
`natCard_unramifiedKerCohomology_eq_natCard_ker`. -/
theorem ker_explicitCoeff1_kerCoeffIncl_eq_unramifiedKerCohomology
    (hψ : (ψ.degree : A) ∉ u.asIdeal) :
    (explicitCoeff1 _ _ (ofIsogeny ψ).kerCoeffIncl continuous_of_discreteTopology).ker =
      ψ.unramifiedKerCohomology := by
  classical
  have hdeg : (ψ.degree : 𝓀[u.adicCompletion F]) ≠ 0 := by
    rw [Ne, ringChar.spec, u.ringChar_residueField_adicCompletion_dvd_iff]
    exact hψ
  have := (ψ.isSeparable_dual_and_self_iff.2 (natCast_ne_zero_of_residue_ne_zero hdeg)).2
  refine AddSubgroup.eq_of_le_of_card_ge
    (ψ.ker_explicitCoeff1_kerCoeffIncl_le_unramifiedKerCohomology hdeg) ?_
  rw [ψ.natCard_unramifiedKerCohomology_eq_natCard_ker, ← range_kummerMap, natCard_range_kummerMap,
    Hom.index_range_eq_card_ker_of_isElliptic_integralModel (ofIsogeny ψ)
      (by rwa [Hom.degree_ofIsogeny])]

/-- **At good reduction prime to `deg ψ`, the image of the local Kummer map equals the unramified
kernel cohomology `H¹_ur(F_u, E₁[ψ])`.** -/
theorem range_kummerMap_eq_unramifiedKerCohomology [DecidableEq (u.adicCompletion F)]
    [Algebra.IsSeparable ψ.fieldPullback.fieldRange W₁.toAffine.FunctionField]
    (hψ : (ψ.degree : A) ∉ u.asIdeal) :
    ψ.kummerMap.range = ψ.unramifiedKerCohomology := by
  rw [range_kummerMap]
  exact ψ.ker_explicitCoeff1_kerCoeffIncl_eq_unramifiedKerCohomology u hψ

end AdicCompletion

/-! ### Global classes unramified outside `S` and Selmer local conditions -/

section Global

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)
  (τ : ∀ v : HeightOneSpectrum R,
    SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))

/-- **The classes of `H¹(G_K, E₁[φ])` unramified outside `S`**: those whose restriction to `K_v`
along `τ v` is unramified for every height-one prime `v ∉ S`. -/
def unramifiedOutsideKerCohomology (S : Set (HeightOneSpectrum R)) :
    AddSubgroup (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) :=
  ⨅ (v : HeightOneSpectrum R) (_ : v ∉ S),
    ((φ.baseChange (v.adicCompletion K)).unramifiedKerCohomology).comap (φ.kerRes (τ v))

/-- `unramifiedOutsideKerCohomology` is the infimum over `v ∉ S` of the pullbacks along `φ.kerRes`
of the local unramified kernel cohomology subgroups. -/
theorem unramifiedOutsideKerCohomology_def (S : Set (HeightOneSpectrum R)) :
    φ.unramifiedOutsideKerCohomology τ S =
      ⨅ (v : HeightOneSpectrum R) (_ : v ∉ S),
        ((φ.baseChange (v.adicCompletion K)).unramifiedKerCohomology).comap (φ.kerRes (τ v)) :=
  (rfl)

variable {φ τ} in
/-- A class in `H¹(G_K, E₁[φ])` is unramified outside `S` iff its restriction to every `K_v` with
`v ∉ S` lies in `(φ.baseChange K_v).unramifiedKerCohomology`. -/
@[simp]
theorem mem_unramifiedOutsideKerCohomology_iff {S : Set (HeightOneSpectrum R)}
    {c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff} :
    c ∈ φ.unramifiedOutsideKerCohomology τ S ↔
      ∀ v ∉ S, φ.kerRes (τ v) c ∈ (φ.baseChange (v.adicCompletion K)).unramifiedKerCohomology := by
  simp only [unramifiedOutsideKerCohomology, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]

/-- Enlarging the exceptional set `S` enlarges `unramifiedOutsideKerCohomology`. -/
theorem unramifiedOutsideKerCohomology_mono {S T : Set (HeightOneSpectrum R)} (hST : S ⊆ T) :
    φ.unramifiedOutsideKerCohomology τ S ≤ φ.unramifiedOutsideKerCohomology τ T := fun _ hc ↦
  mem_unramifiedOutsideKerCohomology_iff.2 fun v hv ↦
    mem_unramifiedOutsideKerCohomology_iff.1 hc v (fun hvS ↦ hv (hST hvS))

/-- **`φ`-Selmer classes are unramified outside the bad primes of `W₁` and the divisors of
`deg φ`.** -/
theorem selmerGroup_le_unramifiedOutsideKerCohomology {S : Set (HeightOneSpectrum R)}
    (hgood : ∀ v ∉ S, ∃ _ : IsIntegral 𝒪[v.adicCompletion K] (W₁⁄(v.adicCompletion K)),
      (integralModel 𝒪[v.adicCompletion K] (W₁⁄(v.adicCompletion K))).IsElliptic)
    (hS : ∀ v ∉ S, (φ.degree : R) ∉ v.asIdeal) :
    φ.selmerGroup τ ≤ φ.unramifiedOutsideKerCohomology τ S := by
  intro c hc
  rw [mem_unramifiedOutsideKerCohomology_iff]
  intro v hv
  obtain ⟨_, _⟩ := hgood v hv
  have hd : (φ.baseChange (v.adicCompletion K)).degree = φ.degree := degree_map φ _
  have hdeg : ((φ.baseChange (v.adicCompletion K)).degree : 𝓀[v.adicCompletion K]) ≠ 0 := by
    rw [hd, Ne, ringChar.spec, v.ringChar_residueField_adicCompletion_dvd_iff]
    exact hS v hv
  have hloc : φ.kerRes (τ v) c ∈
      (explicitCoeff1 _ _ (ofIsogeny (φ.baseChange (v.adicCompletion K))).kerCoeffIncl
        continuous_of_discreteTopology).ker := by
    rw [AddMonoidHom.mem_ker, ← pointRes_kerCoeffIncl]
    exact (W₁.mem_shafarevichTateGroup_iff τ).1 ((φ.mem_selmerGroup_iff τ).1 hc) v
  exact
    (φ.baseChange (v.adicCompletion K)).ker_explicitCoeff1_kerCoeffIncl_le_unramifiedKerCohomology
      hdeg hloc

variable (R) in
/-- **There is a finite set of primes containing `S` outside which every `φ`-Selmer class is
unramified**, whenever `deg φ` is nonzero in `K`. -/
theorem exists_finset_selmerGroup_le_unramifiedOutsideKerCohomology
    (hφ : (φ.degree : K) ≠ 0) (S : Finset (HeightOneSpectrum R)) :
    ∃ T : Finset (HeightOneSpectrum R), S ⊆ T ∧
      φ.selmerGroup τ ≤ φ.unramifiedOutsideKerCohomology τ T := by
  obtain ⟨T, hST, hgood, hprime⟩ := exists_finset_isElliptic_integralModel_adicCompletion R W₁ hφ S
  exact ⟨T, hST, φ.selmerGroup_le_unramifiedOutsideKerCohomology τ hgood hprime⟩

/-- **At a place `v` of good reduction for `W₁` and `W₂` prime to `deg φ`, the local condition of
`φ.selmerStructure τ` is the unramified kernel cohomology.** -/
theorem localCondition_selmerStructure_eq_unramifiedKerCohomology (v : HeightOneSpectrum R)
    [IsIntegral 𝒪[v.adicCompletion K] (W₁⁄(v.adicCompletion K))]
    [(integralModel 𝒪[v.adicCompletion K] (W₁⁄(v.adicCompletion K))).IsElliptic]
    [IsIntegral 𝒪[v.adicCompletion K] (W₂⁄(v.adicCompletion K))]
    [(integralModel 𝒪[v.adicCompletion K] (W₂⁄(v.adicCompletion K))).IsElliptic]
    (hdeg : (φ.degree : R) ∉ v.asIdeal) :
    (φ.selmerStructure τ).localCondition v =
      (φ.baseChange (v.adicCompletion K)).unramifiedKerCohomology := by
  have hd : (φ.baseChange (v.adicCompletion K)).degree = φ.degree := degree_map φ _
  rw [selmerStructure_localCondition]
  exact
    (φ.baseChange (v.adicCompletion K)).ker_explicitCoeff1_kerCoeffIncl_eq_unramifiedKerCohomology
      v (by rwa [hd])

variable (R) in
/-- **At all but finitely many places `v`, the local condition of `φ.selmerStructure τ` equals the
unramified kernel cohomology `(φ.baseChange K_v).unramifiedKerCohomology`.** -/
theorem eventually_localCondition_selmerStructure_eq_unramifiedKerCohomology
    (hφ : (φ.degree : K) ≠ 0) :
    ∀ᶠ v in Filter.cofinite, (φ.selmerStructure τ).localCondition v =
      (φ.baseChange (v.adicCompletion K)).unramifiedKerCohomology := by
  obtain ⟨T, -, hT₁, hTdeg⟩ := exists_finset_isElliptic_integralModel_adicCompletion R W₁ hφ ∅
  filter_upwards [T.finite_toSet.eventually_cofinite_notMem,
    eventually_isElliptic_integralModel_adicCompletion R W₂] with v hv ⟨_, _⟩
  obtain ⟨_, _⟩ := hT₁ v hv
  exact φ.localCondition_selmerStructure_eq_unramifiedKerCohomology τ v (hTdeg v hv)

end Global

end TauCeti.Isogeny
