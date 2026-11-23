/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Restriction
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Torsion
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Unramified
public import TauCeti.NumberTheory.LocalField.Unramified.Cohomology
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability
import TauCeti.NumberTheory.LocalField.NatCastValuation

/-!
# Unramified Galois cohomology and the unramified local condition of an isogeny

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a nonarchimedean local field `K`. The
**unramified kernel cohomology**

```text
φ.unramifiedKerCohomology = unramifiedH1 K (ofIsogeny φ).KerCoeff ≤ H¹(G_K, E₁[φ])
```

consists of the degree-one classes vanishing on the inertia subgroup `I_K`. This is the isogeny
analogue of `WeierstrassCurve.unramifiedTorsionCohomology` and
`WeierstrassCurve.unramifiedOutsideTorsionCohomology` in
`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/Unramified.lean`. Downstream, these
local identifications and order formulas feed finite-support ramification control for `Sel_φ`
(`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/Selmer/Isogeny/Unramified.lean`) and
local Tate duality comparisons between `Sel_φ` and `Sel_φ̂` (such as Cassels' isogeny-invariance
formula for the Birch–Swinnerton-Dyer quotient).

Since `E₁(Kˢ)[φ]` is finite (`TauCeti.Isogeny.finite_kerCoeff_ofIsogeny`), the Frobenius order
formula (`TauCeti.natCard_unramifiedH1_eq_natCard_H0`) and the invariant identification
`H⁰(G_K, E₁[φ]) ≃+ E₁(K)[φ]` (`TauCeti.Isogeny.Hom.kerPointMapEquivInvariants`) give

```text
#φ.unramifiedKerCohomology = #E₁(K)[φ]
```

for every isogeny `φ`, with no separability, good-reduction, or residue-characteristic assumption
(`TauCeti.Isogeny.natCard_unramifiedKerCohomology_eq_natCard_ker`).

When `W₁` has good reduction over `𝒪[K]` and `deg φ` is prime to the residue characteristic, any
point `Q ∈ E₁(Kˢ)` with `φ(Q) = P ∈ E₂(K)` satisfies `deg φ • Q = φ̂(P) ∈ E₁(K)`, so inertia fixes
`Q` (`TauCeti.Isogeny.smul_pointCoeff_eq_self_of_pointCoeffMap_eq_basePointCoeff`). Thus the local
Kummer image is unramified (`TauCeti.Isogeny.range_kummerMap_le_unramifiedKerCohomology`).

At the completion `F_u` of the fraction field `F` of a Dedekind domain `A` at a height-one prime `u`
with finite residue field, if both `W₁` and `W₂` have elliptic integral models over `𝒪[F_u]` and
`deg φ ∉ u`, the local Kummer-cokernel index `[E₂(F_u) : φ(E₁(F_u))]` equals `#E₁(F_u)[φ]`
(`TauCeti.Isogeny.Hom.index_range_eq_card_ker_of_isElliptic_integralModel`), matching
`#φ.unramifiedKerCohomology`. Hence the local Kummer condition **coincides** with the unramified
cohomology (`TauCeti.Isogeny.localKummerCondition_eq_unramifiedKerCohomology` and
`TauCeti.Isogeny.range_kummerMap_eq_unramifiedKerCohomology`).

## Main definitions

* `TauCeti.Isogeny.unramifiedKerCohomology`: the subgroup `unramifiedH1 K E₁[φ]` of
  `H¹(G_K, E₁[φ])`.
* `TauCeti.Isogeny.unramifiedOutsideKerCohomology`: the global subgroup of `H¹(G_K, E₁[φ])`
  consisting of classes unramified at every prime `v ∉ S`.

## Main results

* `TauCeti.Isogeny.natCard_unramifiedKerCohomology_eq_natCard_ker`: `#H¹_ur(K, E₁[φ]) = #E₁(K)[φ]`.
* `TauCeti.Isogeny.range_kummerMap_le_unramifiedKerCohomology`: at good reduction of `W₁` prime to
  `deg φ`, every Kummer class is unramified.
* `TauCeti.Isogeny.localKummerCondition_eq_unramifiedKerCohomology`,
  `TauCeti.Isogeny.range_kummerMap_eq_unramifiedKerCohomology`: over a Dedekind completion `F_u`
  with finite residue field, when both `W₁` and `W₂` have elliptic integral models over `𝒪[F_u]`
  and `deg φ ∉ u`, the local Kummer image equals `H¹_ur(F_u, E₁[φ])`.

## References

* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, Lemma 3.2 and §6.
* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Princeton University Press, 2000,
  I.5 and I.6.
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
        (separableClosureInertiaSubgroup K) c = 0 := by
  rw [unramifiedKerCohomology_eq_unramifiedH1, mem_unramifiedH1_iff]

/-- `φ.unramifiedKerCohomology` is finite, since `(ofIsogeny φ).KerCoeff` is finite. -/
instance finite_unramifiedKerCohomology : Finite φ.unramifiedKerCohomology := by
  rw [unramifiedKerCohomology_eq_unramifiedH1]
  infer_instance

/-- **The unramified cohomology of `E₁[φ]` has the order of the rational kernel `E₁(K)[φ]`.** No
separability, good-reduction, or residue-characteristic assumption is needed. -/
theorem natCard_unramifiedKerCohomology_eq_natCard_ker [DecidableEq K] :
    Nat.card φ.unramifiedKerCohomology = Nat.card (ofIsogeny φ).pointMapHom.ker := by
  rw [unramifiedKerCohomology_eq_unramifiedH1]
  exact (natCard_unramifiedH1_eq_natCard_H0 K (ofIsogeny φ).KerCoeff).trans
    (Nat.card_congr (ofIsogeny φ).kerPointMapEquivInvariants.symm.toEquiv)

/-- Inclusion `E₁[φ] → E₁[deg φ]` carries unramified classes to unramified classes. -/
theorem explicitCoeff1_kerCoeffToTorsionCoeff_mem_unramifiedTorsionCohomology
    {c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    (hc : c ∈ φ.unramifiedKerCohomology) :
    explicitCoeff1 _ _ φ.kerCoeffToTorsionCoeff continuous_of_discreteTopology c ∈
      W₁.unramifiedTorsionCohomology φ.degree := by
  rw [unramifiedTorsionCohomology_eq_unramifiedH1]
  rw [unramifiedKerCohomology_eq_unramifiedH1] at hc
  exact φ.kerCoeffToTorsionCoeff.explicitCoeff1_mem_unramifiedH1 continuous_of_discreteTopology hc

/-- Projection `E₁[deg φ] → E₂[φ̂]` carries unramified classes to unramified classes. -/
theorem explicitCoeff1_torsionCoeffToDualKerCoeff_mem_unramifiedKerCohomology
    {c : H1 (AbsoluteGaloisGroup K) (W₁.TorsionCoeff φ.degree)}
    (hc : c ∈ W₁.unramifiedTorsionCohomology φ.degree) :
    explicitCoeff1 _ _ φ.torsionCoeffToDualKerCoeff continuous_of_discreteTopology c ∈
      φ.dual.unramifiedKerCohomology := by
  rw [unramifiedKerCohomology_eq_unramifiedH1]
  rw [unramifiedTorsionCohomology_eq_unramifiedH1] at hc
  exact φ.torsionCoeffToDualKerCoeff.explicitCoeff1_mem_unramifiedH1
    continuous_of_discreteTopology hc

/-- **Unramified kernel classes restrict to unramified classes** along any valuative extension of
nonarchimedean local fields, with no reduction hypothesis on `W₁` or `W₂`. -/
theorem kerRes_mem_unramifiedKerCohomology {L : Type*} [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    (τ : SeparableClosure K →ₐ[K] SeparableClosure L)
    {c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    (hc : c ∈ φ.unramifiedKerCohomology) :
    φ.kerRes τ c ∈ (φ.baseChange L).unramifiedKerCohomology := by
  rw [unramifiedKerCohomology_eq_unramifiedH1] at hc ⊢
  rw [kerRes_eq_explicitMap1]
  exact τ.explicitMap1_mem_unramifiedH1 (φ.kerCoeffBaseChange τ) continuous_of_discreteTopology
    (φ.kerCoeffBaseChange_smul τ) hc

end Local

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
    exact Q.property
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
  rw [unramifiedKerCohomology_eq_unramifiedH1, kummerMap_eq_H1pi hQ,
    QuotientAddGroup.mk'_apply]
  exact mk_mem_unramifiedH1_of_forall_mem_inertiaSubgroup
    (f := ⟨Hom.kummerCocycle hQ, Hom.kummerCocycle_mem_Z1 hQ⟩)
    fun _ hσ ↦ kummerCocycle_eq_zero_of_mem_inertiaSubgroup hdeg hQ hσ

/-- **At good reduction of `W₁` prime to `deg φ`, the local Kummer image lies in the unramified
cohomology.** -/
theorem range_kummerMap_le_unramifiedKerCohomology [DecidableEq K]
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField]
    (hdeg : (φ.degree : 𝓀[K]) ≠ 0) :
    φ.kummerMap.range ≤ φ.unramifiedKerCohomology := by
  rintro _ ⟨P, rfl⟩
  exact φ.kummerMap_mem_unramifiedKerCohomology hdeg P

/-- **At good reduction of `W₁` prime to `deg φ`, the kernel of `H¹(G_K, E₁[φ]) → H¹(G_K, E₁)` is
contained in `H¹_ur(K, E₁[φ])`.** Unlike `range_kummerMap_le_unramifiedKerCohomology`, this form
needs no `DecidableEq K` or explicit separability instance. -/
theorem localKummerCondition_le_unramifiedKerCohomology
    (hdeg : (φ.degree : 𝓀[K]) ≠ 0) :
    φ.localKummerCondition ≤
      φ.unramifiedKerCohomology := by
  classical
  have := (φ.isSeparable_dual_and_self_iff.2
    (natCast_ne_zero_of_residueField_natCast_ne_zero hdeg)).2
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

/-- Over the completion `F_u` of the fraction field `F` of a Dedekind domain `A` at a height-one
prime `u` with finite residue field, if both `W₁` and `W₂` have elliptic integral models over
`𝒪[F_u]` and `deg ψ ∉ u`, then the local Selmer condition
`ker(H¹(G_{F_u}, E₁[ψ]) → H¹(G_{F_u}, E₁))` equals `ψ.unramifiedKerCohomology`. -/
theorem localKummerCondition_eq_unramifiedKerCohomology
    (hψ : (ψ.degree : A) ∉ u.asIdeal) :
    ψ.localKummerCondition =
      ψ.unramifiedKerCohomology := by
  classical
  have hdeg : (ψ.degree : 𝓀[u.adicCompletion F]) ≠ 0 := by
    rw [Ne, ringChar.spec, u.ringChar_residueField_adicCompletion_dvd_iff]
    exact hψ
  have := (ψ.isSeparable_dual_and_self_iff.2
    (natCast_ne_zero_of_residueField_natCast_ne_zero hdeg)).2
  refine AddSubgroup.eq_of_le_of_card_ge
    (ψ.localKummerCondition_le_unramifiedKerCohomology hdeg) ?_
  rw [ψ.natCard_unramifiedKerCohomology_eq_natCard_ker, ← range_kummerMap, natCard_range_kummerMap,
    Hom.index_range_eq_card_ker_of_isElliptic_integralModel (ofIsogeny ψ)
      (by rwa [Hom.degree_ofIsogeny])]

/-- Over the completion `F_u` of the fraction field `F` of a Dedekind domain `A` at a height-one
prime `u` with finite residue field, if both `W₁` and `W₂` have elliptic integral models over
`𝒪[F_u]` and `deg ψ ∉ u`, then the image of the local Kummer map equals
`ψ.unramifiedKerCohomology`. -/
theorem range_kummerMap_eq_unramifiedKerCohomology [DecidableEq (u.adicCompletion F)]
    [Algebra.IsSeparable ψ.fieldPullback.fieldRange W₁.toAffine.FunctionField]
    (hψ : (ψ.degree : A) ∉ u.asIdeal) :
    ψ.kummerMap.range = ψ.unramifiedKerCohomology := by
  rw [range_kummerMap]
  exact ψ.localKummerCondition_eq_unramifiedKerCohomology u hψ

end AdicCompletion

/-! ### Global classes unramified outside `S` -/

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

end Global

end TauCeti.Isogeny
