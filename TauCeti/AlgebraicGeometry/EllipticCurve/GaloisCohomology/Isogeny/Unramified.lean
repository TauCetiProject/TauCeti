/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Finiteness
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Torsion
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Unramified

import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.AlmostEverywhere

/-!
# Unramified Galois cohomology and local Kummer conditions for an isogeny

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a nonarchimedean local field `K`. Its
**unramified kernel cohomology** `TauCeti.Isogeny.unramifiedKerCohomology φ` is the subgroup
`H¹_ur(G_K, E₁[φ])` of classes vanishing on the inertia subgroup of `K`
(`TauCeti.unramifiedCohomology`). Because the geometric kernel `E₁(Kˢ)[φ]` is finite,
`H¹_ur(G_K, E₁[φ])` is always finite of order `#E₁(K)[φ]`
(`TauCeti.Isogeny.natCard_unramifiedKerCohomology`).

At good reduction of `W₁`, if `deg φ` is prime to the residue characteristic, every Kummer class
`δ_φ(P)` of `P ∈ E₂(K)` is unramified (`TauCeti.Isogeny.kummerMap_mem_unramifiedKerCohomology`):
for any `Q ∈ E₁(Kˢ)` with `φ(Q) = P`, we have `[deg φ] Q = φ̂(P) ∈ E₁(K)`, so inertia fixes `Q`.
Over the completion `F_u` of the fraction field of a Dedekind domain at a height-one prime `u` with
finite residue field not dividing `deg φ`, if both `W₁` and `W₂` have good reduction, the index
identity `[E₂(F_u) : φ(E₁(F_u))] = #E₁(F_u)[φ]`
(`TauCeti.Isogeny.Hom.index_range_eq_card_ker_of_isElliptic_integralModel`) upgrades this inclusion
to equality:

```text
im(δ_φ : E₂(F_u) → H¹(G_{F_u}, E₁[φ])) = H¹_ur(G_{F_u}, E₁[φ]).
```

Globally, over the fraction field `K` of a Dedekind domain `R` with finite residue fields, the
local condition of the `φ`-Selmer structure agrees with `H¹_ur(G_{K_v}, E₁[φ])` at every finite
place `v` prime to `deg φ` where `W₁` and `W₂` have good reduction, hence at all but finitely many
finite places. Consequently, if `S` contains the bad places of `W₁` and `W₂` and the places
dividing `deg φ`, `Sel_φ` relative to all finite completions equals the classes in
`H¹_S(G_K, E₁[φ])` (`TauCeti.Isogeny.unramifiedOutsideKerCohomology`) satisfying the local Kummer
condition at the finitely many places in `S`.

## Main definitions

* `TauCeti.Isogeny.unramifiedKerCohomology`: the subgroup `H¹_ur(G_K, E₁[φ])`.
* `TauCeti.Isogeny.unramifiedOutsideKerCohomology`: global classes in `H¹(G_K, E₁[φ])` unramified
  outside a set `S` of height-one primes.

## Main results

* `TauCeti.Isogeny.finite_unramifiedKerCohomology` and `natCard_unramifiedKerCohomology`:
  `H¹_ur(G_K, E₁[φ])` is finite of order `#E₁(K)[φ]`.
* `TauCeti.Isogeny.kummerMap_mem_unramifiedKerCohomology` and
  `range_kummerMap_le_unramifiedKerCohomology`: at good reduction of `W₁` away from `deg φ`,
  `im(δ_φ) ≤ H¹_ur(G_K, E₁[φ])`.
* `TauCeti.Isogeny.range_kummerMap_eq_unramifiedKerCohomology`: at good reduction of `W₁` and `W₂`
  away from `deg φ` over `u.adicCompletion F`, `im(δ_φ) = H¹_ur(G_{F_u}, E₁[φ])`.
* `TauCeti.Isogeny.localCondition_selmerStructure_eq_unramifiedKerCohomology`,
  `eventually_localCondition_selmerStructure_eq_unramifiedKerCohomology`,
  `selmerGroup_le_unramifiedOutsideKerCohomology`, and
  `mem_selmerGroup_iff_mem_unramifiedOutsideKerCohomology_and_forall_mem`: global Selmer local
  conditions and finite-`S` presentation of `Sel_φ`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, Proposition 3.8 and §4.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.1.5 and X.4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
-/

public section

noncomputable section

open WeierstrassCurve TauCeti.ContCohomology _root_.ValuativeRel

namespace TauCeti.Isogeny

open Hom (ofIsogeny)

/-! ### Unramified kernel cohomology over a local field -/

section Local

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- **Unramified first cohomology `H¹_ur(G_K, E₁[φ])`** of the kernel of an isogeny `φ : W₁ → W₂`
over a nonarchimedean local field `K`. -/
def unramifiedKerCohomology :
    AddSubgroup (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) :=
  unramifiedCohomology K (ofIsogeny φ).KerCoeff

/-- `unramifiedKerCohomology` is `TauCeti.unramifiedCohomology` on `(ofIsogeny φ).KerCoeff`. -/
theorem unramifiedKerCohomology_eq_unramifiedCohomology :
    φ.unramifiedKerCohomology = unramifiedCohomology K (ofIsogeny φ).KerCoeff :=
  (rfl)

/-- A class in `H¹(G_K, E₁[φ])` is unramified if and only if its restriction to inertia is zero. -/
@[simp]
theorem mem_unramifiedKerCohomology_iff
    {c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff} :
    c ∈ φ.unramifiedKerCohomology ↔
      explicitRes1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) c = 0 :=
  mem_unramifiedCohomology_iff

/-- **Unramified kernel classes pull back to unramified kernel classes** along an extension `L/K`
of nonarchimedean local fields. -/
theorem kerRes_mem_unramifiedKerCohomology
    {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [ValuativeExtension K L] (τ : SeparableClosure K →ₐ[K] SeparableClosure L)
    {c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    (hc : c ∈ φ.unramifiedKerCohomology) :
    φ.kerRes τ c ∈ (φ.baseChange L).unramifiedKerCohomology := by
  rw [unramifiedKerCohomology_eq_unramifiedCohomology, kerRes_eq_explicitMap1]
  exact explicitMap1_mem_unramifiedCohomology τ (φ.kerCoeffBaseChange τ)
    continuous_of_discreteTopology (φ.kerCoeffBaseChange_smul τ) hc

/-- `H¹_ur(G_K, E₁[φ])` is finite for every isogeny `φ`, with no separability or reduction
assumption. -/
instance finite_unramifiedKerCohomology : Finite φ.unramifiedKerCohomology := by
  have := (ofIsogeny φ).finite_kerCoeff (Hom.ofIsogeny_ne_zero φ)
  exact inferInstanceAs (Finite (unramifiedCohomology K (ofIsogeny φ).KerCoeff))

/-- **Order of unramified isogeny-kernel cohomology**: `#H¹_ur(G_K, E₁[φ]) = #E₁(K)[φ]`. -/
theorem natCard_unramifiedKerCohomology [DecidableEq K] :
    Nat.card φ.unramifiedKerCohomology = Nat.card (ofIsogeny φ).pointMapHom.ker := by
  have := (ofIsogeny φ).finite_kerCoeff (Hom.ofIsogeny_ne_zero φ)
  rw [unramifiedKerCohomology, natCard_unramifiedCohomology_eq_natCard_H0]
  exact Nat.card_congr (ofIsogeny φ).kerPointMapEquivInvariants.symm.toEquiv

section GoodReduction

variable [IsIntegral 𝒪[K] W₁] [(integralModel 𝒪[K] W₁).IsElliptic] [DecidableEq K]

variable {φ} in
/-- At good reduction of `W₁` away from `deg φ`, the Kummer cocycle of a preimage under `φ` of a
`K`-rational point of `W₂` vanishes on inertia: `[deg φ] Q = φ̂(P) ∈ E₁(K)`, so inertia fixes
`Q`. -/
theorem kummerCocycle_eq_zero_of_mem_inertiaSubgroup
    (hdeg : (φ.degree : 𝓀[K]) ≠ 0) {P : W₂.toAffine.Point} {Q : W₁.PointCoeff}
    (hQ : (ofIsogeny φ).pointCoeffMap Q = W₂.basePointCoeff P)
    {σ : Gal(AlgebraicClosure K/K)} (hσ : σ ∈ inertiaSubgroup K) :
    Hom.kummerCocycle hQ (absoluteGaloisGroupRestrictEquiv K σ) = 0 := by
  cases Subsingleton.elim ‹DecidableEq K› (Classical.decEq K)
  classical
  have hQ' : φ.degree • Q = W₁.basePointCoeff ((ofIsogeny φ.dual).pointMap P) := by
    rw [← φ.pointCoeffMap_dual_pointCoeffMap, hQ, Hom.pointCoeffMap_basePointCoeff]
  apply Subtype.ext
  rw [Hom.coe_kummerCocycle,
    WeierstrassCurve.smul_pointCoeff_eq_self_of_mem_inertiaSubgroup hdeg hQ' hσ, sub_self]
  rfl

/-- **At good reduction of `W₁` away from `deg φ`, every `φ`-Kummer class is unramified.** -/
theorem kummerMap_mem_unramifiedKerCohomology
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField]
    (hdeg : (φ.degree : 𝓀[K]) ≠ 0) (P : W₂.toAffine.Point) :
    φ.kummerMap P ∈ φ.unramifiedKerCohomology := by
  obtain ⟨Q, hQ⟩ := φ.pointCoeffMap_ofIsogeny_surjective (W₂.basePointCoeff P)
  rw [mem_unramifiedKerCohomology_iff, φ.kummerMap_eq_H1pi hQ]
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

/-- **At good reduction of `W₁` away from `deg φ`, the `φ`-Kummer image is unramified.** -/
theorem range_kummerMap_le_unramifiedKerCohomology
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField]
    (hdeg : (φ.degree : 𝓀[K]) ≠ 0) :
    φ.kummerMap.range ≤ φ.unramifiedKerCohomology := by
  rintro _ ⟨P, rfl⟩
  exact φ.kummerMap_mem_unramifiedKerCohomology hdeg P

end GoodReduction

end Local

/-! ### Equality with the local Kummer image over completions of Dedekind domains -/

section AdicCompletion

open IsDedekindDomain

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A) [Finite (A ⧸ u.asIdeal)] [DecidableEq (u.adicCompletion F)]
  {V₁ V₂ : WeierstrassCurve (u.adicCompletion F)} [V₁.IsElliptic] [V₂.IsElliptic]
  [IsIntegral 𝒪[u.adicCompletion F] V₁] [(integralModel 𝒪[u.adicCompletion F] V₁).IsElliptic]
  [IsIntegral 𝒪[u.adicCompletion F] V₂] [(integralModel 𝒪[u.adicCompletion F] V₂).IsElliptic]
  (ψ : Isogeny V₁.toAffine V₂.toAffine)
  [Algebra.IsSeparable ψ.fieldPullback.fieldRange V₁.toAffine.FunctionField]

/-- **At good reduction away from `deg ψ`, the local `ψ`-Kummer image equals unramified
cohomology** (Milne, *ADT* I, Proposition 3.8): over `u.adicCompletion F` with finite residue
field, if `V₁` and `V₂` have good reduction and `deg ψ ∉ u`, then
`im(δ_ψ : E₂(F_u) → H¹(G_{F_u}, E₁[ψ])) = H¹_ur(G_{F_u}, E₁[ψ])`. -/
theorem range_kummerMap_eq_unramifiedKerCohomology (hdeg : (ψ.degree : A) ∉ u.asIdeal) :
    ψ.kummerMap.range = ψ.unramifiedKerCohomology := by
  have hdeg_res : (ψ.degree : 𝓀[u.adicCompletion F]) ≠ 0 := by
    rw [Ne, ringChar.spec, u.ringChar_residueField_adicCompletion_dvd_iff]
    exact hdeg
  apply AddSubgroup.eq_of_le_of_card_ge (ψ.range_kummerMap_le_unramifiedKerCohomology hdeg_res)
  rw [ψ.natCard_unramifiedKerCohomology, ψ.natCard_range_kummerMap,
    Hom.index_range_eq_card_ker_of_isElliptic_integralModel (ofIsogeny ψ)
      (by rwa [Hom.degree_ofIsogeny])]

end AdicCompletion

/-! ### Global Selmer local conditions and classes unramified outside `S` -/

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
along `τ v`, for every finite place `v ∉ S`, lies in `H¹_ur(G_{K_v}, E₁[φ])`. -/
def unramifiedOutsideKerCohomology (S : Set (HeightOneSpectrum R)) :
    AddSubgroup (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) :=
  ⨅ (v : HeightOneSpectrum R) (_ : v ∉ S),
    (φ.baseChange (v.adicCompletion K)).unramifiedKerCohomology.comap (φ.kerRes (τ v))

/-- A class in `H¹(G_K, E₁[φ])` is unramified outside `S` exactly when its restriction to every
`K_v` with `v ∉ S` is unramified. -/
@[simp]
theorem mem_unramifiedOutsideKerCohomology_iff {S : Set (HeightOneSpectrum R)}
    {c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff} :
    c ∈ φ.unramifiedOutsideKerCohomology τ S ↔
      ∀ v ∉ S, φ.kerRes (τ v) c ∈
        (φ.baseChange (v.adicCompletion K)).unramifiedKerCohomology := by
  simp only [unramifiedOutsideKerCohomology, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]

/-- **At a place `v` of good reduction of `W₁` and `W₂` prime to `deg φ`, the local condition of
`Sel_φ` is `H¹_ur(G_{K_v}, E₁[φ])`.** -/
theorem localCondition_selmerStructure_eq_unramifiedKerCohomology
    (v : HeightOneSpectrum R)
    [IsIntegral 𝒪[v.adicCompletion K] (W₁⁄(v.adicCompletion K))]
    [(integralModel 𝒪[v.adicCompletion K] (W₁⁄(v.adicCompletion K))).IsElliptic]
    [IsIntegral 𝒪[v.adicCompletion K] (W₂⁄(v.adicCompletion K))]
    [(integralModel 𝒪[v.adicCompletion K] (W₂⁄(v.adicCompletion K))).IsElliptic]
    (hdeg : (φ.degree : R) ∉ v.asIdeal) :
    (φ.selmerStructure τ).localCondition v =
      (φ.baseChange (v.adicCompletion K)).unramifiedKerCohomology := by
  classical
  have hdeg_bc : (φ.baseChange (v.adicCompletion K)).degree = φ.degree :=
    degree_map φ (algebraMap K (v.adicCompletion K))
  have hd : ((φ.baseChange (v.adicCompletion K)).degree : R) ∉ v.asIdeal := hdeg_bc ▸ hdeg
  have hne : (φ.degree : K) ≠ 0 := fun h ↦ hdeg <| by
    have h0 : (φ.degree : R) = 0 := IsFractionRing.injective R K (by simpa using h)
    exact h0 ▸ v.asIdeal.zero_mem
  have := (φ.isSeparable_dual_and_self_iff.2 hne).2
  rw [selmerStructure_localCondition, ← range_kummerMap]
  exact (φ.baseChange (v.adicCompletion K)).range_kummerMap_eq_unramifiedKerCohomology v hd

/-- **For all but finitely many finite places `v`, the local condition of `Sel_φ` equals
`H¹_ur(G_{K_v}, E₁[φ])`.** -/
theorem eventually_localCondition_selmerStructure_eq_unramifiedKerCohomology
    (hφ : (φ.degree : K) ≠ 0) :
    ∀ᶠ v in Filter.cofinite, (φ.selmerStructure τ).localCondition v =
      (φ.baseChange (v.adicCompletion K)).unramifiedKerCohomology := by
  obtain ⟨T, -, hT₁, hTdeg⟩ := exists_finset_isElliptic_integralModel_adicCompletion R W₁ hφ ∅
  filter_upwards [T.finite_toSet.eventually_cofinite_notMem,
    eventually_isElliptic_integralModel_adicCompletion R W₂] with v hv ⟨_, _⟩
  obtain ⟨_, _⟩ := hT₁ v hv
  exact φ.localCondition_selmerStructure_eq_unramifiedKerCohomology τ v (hTdeg v hv)

/-- **Every `φ`-Selmer class is unramified outside the bad places of `W₁` and the places dividing
`deg φ`.** Note that good reduction of `W₂` is not needed for this inclusion. -/
theorem selmerGroup_le_unramifiedOutsideKerCohomology {S : Set (HeightOneSpectrum R)}
    (hgood₁ : ∀ v ∉ S, ∃ _ : IsIntegral 𝒪[v.adicCompletion K] (W₁⁄(v.adicCompletion K)),
      (integralModel 𝒪[v.adicCompletion K] (W₁⁄(v.adicCompletion K))).IsElliptic)
    (hS : ∀ v ∉ S, (φ.degree : R) ∉ v.asIdeal)
    (hφ : (φ.degree : K) ≠ 0) :
    φ.selmerGroup τ ≤ φ.unramifiedOutsideKerCohomology τ S := by
  classical
  have := (φ.isSeparable_dual_and_self_iff.2 hφ).2
  intro c hc
  rw [mem_unramifiedOutsideKerCohomology_iff]
  intro v hv
  obtain ⟨_, _⟩ := hgood₁ v hv
  have hdeg_bc : (φ.baseChange (v.adicCompletion K)).degree = φ.degree :=
    degree_map φ (algebraMap K (v.adicCompletion K))
  have hdeg_res : ((φ.baseChange (v.adicCompletion K)).degree : 𝓀[v.adicCompletion K]) ≠ 0 := by
    rw [hdeg_bc, Ne, ringChar.spec, v.ringChar_residueField_adicCompletion_dvd_iff]
    exact hS v hv
  exact (φ.baseChange (v.adicCompletion K)).range_kummerMap_le_unramifiedKerCohomology hdeg_res
    ((φ.mem_selmerGroup_iff_forall_kerRes_mem_range_kummerMap τ).mp hc v)

/-- **Finite-`S` presentation of `Sel_φ` over a Dedekind domain.** If `W₁` and `W₂` have good
reduction outside `S` and no prime outside `S` divides `deg φ`, then a class in `H¹(G_K, E₁[φ])`
belongs to `Sel_φ` (relative to all height-one completions) if and only if it is unramified outside
`S` and satisfies the local condition at the primes in `S`. -/
theorem mem_selmerGroup_iff_mem_unramifiedOutsideKerCohomology_and_forall_mem
    {S : Set (HeightOneSpectrum R)}
    (hgood₁ : ∀ v ∉ S, ∃ _ : IsIntegral 𝒪[v.adicCompletion K] (W₁⁄(v.adicCompletion K)),
      (integralModel 𝒪[v.adicCompletion K] (W₁⁄(v.adicCompletion K))).IsElliptic)
    (hgood₂ : ∀ v ∉ S, ∃ _ : IsIntegral 𝒪[v.adicCompletion K] (W₂⁄(v.adicCompletion K)),
      (integralModel 𝒪[v.adicCompletion K] (W₂⁄(v.adicCompletion K))).IsElliptic)
    (hS : ∀ v ∉ S, (φ.degree : R) ∉ v.asIdeal)
    (hφ : (φ.degree : K) ≠ 0)
    {c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff} :
    c ∈ φ.selmerGroup τ ↔
      c ∈ φ.unramifiedOutsideKerCohomology τ S ∧
        ∀ v ∈ S, φ.kerRes (τ v) c ∈ (φ.selmerStructure τ).localCondition v := by
  have hmem : c ∈ φ.selmerGroup τ ↔
      ∀ v, φ.kerRes (τ v) c ∈ (φ.selmerStructure τ).localCondition v := by
    simp only [mem_selmerGroup_iff, mem_shafarevichTateGroup_iff, pointRes_kerCoeffIncl,
      selmerStructure_localCondition, AddMonoidHom.mem_ker]
  refine ⟨fun hc ↦ ⟨φ.selmerGroup_le_unramifiedOutsideKerCohomology τ hgood₁ hS hφ hc,
    fun v _ ↦ hmem.mp hc v⟩, ?_⟩
  rintro ⟨hur, hloc⟩
  rw [hmem]
  intro v
  by_cases hv : v ∈ S
  · exact hloc v hv
  · obtain ⟨_, _⟩ := hgood₁ v hv
    obtain ⟨_, _⟩ := hgood₂ v hv
    rw [φ.localCondition_selmerStructure_eq_unramifiedKerCohomology τ v (hS v hv)]
    exact (φ.mem_unramifiedOutsideKerCohomology_iff τ).mp hur v hv

end Global

end TauCeti.Isogeny
