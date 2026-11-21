/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Unramified
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.AlmostEverywhere

/-!
# Unramified local conditions of the `φ`-Selmer structure

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a field `K`, and fix a family `(L i)` of
field extensions of `K` with embeddings `τ i : Kˢ →ₐ[K] (L i)ˢ` of separable closures. This file
connects the local conditions of `φ.selmerStructure τ` and the global Selmer group `φ.selmerGroup τ`
(`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/Selmer/Isogeny/Basic.lean`) to the
unramified kernel cohomology `unramifiedKerCohomology` and `unramifiedOutsideKerCohomology`
(`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/Isogeny/Unramified.lean`).

Downstream, these results supply two essential global inputs for Selmer-group arithmetic:

* **Finite-support ramification control**: every `φ`-Selmer class is unramified outside a finite
  set of places (those of bad reduction for `W₁` or dividing `deg φ`), reducing finiteness and
  Poitou–Tate exact sequences for `Sel_φ` to a finite set `S` of places.
* **Almost-everywhere coincidence with the unramified condition**: for all but finitely many primes
  `v` of a Dedekind domain with finite residue fields, the local condition of `φ.selmerStructure τ`
  equals `(φ.baseChange K_v).unramifiedKerCohomology`, which is needed for local Tate duality
  comparisons between `Sel_φ` and `Sel_φ̂` (such as Cassels' isogeny-invariance formula for the
  Birch–Swinnerton-Dyer quotient).

The statements and organization adapt the `[m]`-torsion and local-Selmer analogues:

* `WeierstrassCurve.unramifiedTorsionCohomology`,
  `WeierstrassCurve.torsionRes_mem_unramifiedTorsionCohomology_of_mem_selmerGroup`, and
  `WeierstrassCurve.unramifiedOutsideTorsionCohomology`
  (`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/Unramified.lean`);
* `TauCeti.exists_finset_torsionRes_mem_unramifiedTorsionCohomology`
  (`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/FiniteRamification.lean`);
* `TauCeti.Isogeny.eventually_natCard_localCondition_selmerStructure_eq`
  (`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/Selmer/Isogeny/Local.lean`).

## Main results

* `TauCeti.Isogeny.localCondition_selmerStructure_le_unramifiedKerCohomology`,
  `TauCeti.Isogeny.kerRes_mem_unramifiedKerCohomology_of_mem_selmerGroup`: for an arbitrary
  localization family `τ`, at any nonarchimedean local field `L i` where `W₁⁄(L i)` has good
  reduction and `deg φ ≠ 0` in `𝓀[L i]`, the local condition of `φ.selmerStructure τ` lies in
  `(φ.baseChange (L i)).unramifiedKerCohomology` and every `φ`-Selmer class restricts into it.
* `TauCeti.Isogeny.localCondition_selmerStructure_eq_unramifiedKerCohomology`: at a height-one
  prime `v` of a Dedekind domain with finite residue field where both `W₁⁄K_v` and `W₂⁄K_v` have
  elliptic integral models over `𝒪[K_v]` and `deg φ ∉ v`, the local condition of
  `φ.selmerStructure τ` equals `(φ.baseChange K_v).unramifiedKerCohomology`.
* `TauCeti.Isogeny.selmerGroup_le_unramifiedOutsideKerCohomology`,
  `TauCeti.Isogeny.exists_finset_selmerGroup_le_unramifiedOutsideKerCohomology`: over a Dedekind
  domain with finite residue fields, every `φ`-Selmer class is unramified outside the bad primes of
  `W₁` and the divisors of `deg φ` (a finite set whenever `deg φ ≠ 0` in `K`).
* `TauCeti.Isogeny.eventually_localCondition_selmerStructure_eq_unramifiedKerCohomology`: over a
  Dedekind domain with finite residue fields, whenever `deg φ ≠ 0` in `K`, the local condition of
  `φ.selmerStructure τ` equals `(φ.baseChange K_v).unramifiedKerCohomology` for all but finitely
  many height-one primes `v`.

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

/-! ### Arbitrary localization families -/

section ArbitraryFamily

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  {ι : Type*} {L : ι → Type*} [∀ j, Field (L j)] [∀ j, Algebra K (L j)]
  (φ : Isogeny W₁.toAffine W₂.toAffine)
  (τ : ∀ j, SeparableClosure K →ₐ[K] SeparableClosure (L j)) (i : ι)
  [ValuativeRel (L i)] [TopologicalSpace (L i)] [IsNonarchimedeanLocalField (L i)]
  [IsIntegral 𝒪[L i] (W₁⁄(L i))] [(integralModel 𝒪[L i] (W₁⁄(L i))).IsElliptic]

/-- For an arbitrary localization family `τ`, at any nonarchimedean local field `L i` where
`W₁⁄(L i)` has good reduction and `deg φ` is nonzero in `𝓀[L i]`, the local condition of
`φ.selmerStructure τ` at `i` is contained in `(φ.baseChange (L i)).unramifiedKerCohomology`.
No valuation or good-reduction assumption is made at indices `j ≠ i`. -/
theorem localCondition_selmerStructure_le_unramifiedKerCohomology
    (hdeg : (φ.degree : 𝓀[L i]) ≠ 0) :
    (φ.selmerStructure τ).localCondition i ≤ (φ.baseChange (L i)).unramifiedKerCohomology := by
  rw [selmerStructure_localCondition]
  have hd : (φ.baseChange (L i)).degree = φ.degree := degree_map φ _
  exact (φ.baseChange (L i)).ker_explicitCoeff1_kerCoeffIncl_le_unramifiedKerCohomology
    (by rwa [hd])

/-- For an arbitrary localization family `τ`, every `φ`-Selmer class restricts into the unramified
kernel cohomology at any nonarchimedean local field `L i` where `W₁⁄(L i)` has good reduction and
`deg φ` is nonzero in `𝓀[L i]`. No valuation or good-reduction assumption is made at indices
`j ≠ i`. -/
theorem kerRes_mem_unramifiedKerCohomology_of_mem_selmerGroup
    (hdeg : (φ.degree : 𝓀[L i]) ≠ 0)
    {c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff} (hc : c ∈ φ.selmerGroup τ) :
    φ.kerRes (τ i) c ∈ (φ.baseChange (L i)).unramifiedKerCohomology :=
  φ.localCondition_selmerStructure_le_unramifiedKerCohomology τ i hdeg
    ((φ.mem_selmerGroup_iff_forall_kerRes_mem_localCondition τ).1 hc i)

end ArbitraryFamily

/-! ### Dedekind completions -/

section DedekindSinglePlace

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)
  (τ : ∀ v : HeightOneSpectrum R,
    SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))

/-- Over the fraction field `K` of a Dedekind domain `R`, at a height-one prime `v` with finite
residue field `R ⧸ v.asIdeal`, if both `W₁⁄K_v` and `W₂⁄K_v` have elliptic integral models over
`𝒪[K_v]` and `deg φ ∉ v`, then the local condition of `φ.selmerStructure τ` at `v` equals
`(φ.baseChange K_v).unramifiedKerCohomology`. No finiteness assumption is made on residue fields at
primes `w ≠ v`. -/
theorem localCondition_selmerStructure_eq_unramifiedKerCohomology (v : HeightOneSpectrum R)
    [Finite (R ⧸ v.asIdeal)]
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

end DedekindSinglePlace

section DedekindGlobal

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)
  (τ : ∀ v : HeightOneSpectrum R,
    SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))

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
  refine φ.kerRes_mem_unramifiedKerCohomology_of_mem_selmerGroup τ v ?_ hc
  rw [Ne, ringChar.spec, v.ringChar_residueField_adicCompletion_dvd_iff]
  exact hS v hv

variable (R) in
/-- **There is a finite set of primes containing `S` outside which every `φ`-Selmer class is
unramified**, whenever `deg φ` is nonzero in `K`. -/
theorem exists_finset_selmerGroup_le_unramifiedOutsideKerCohomology
    (hφ : (φ.degree : K) ≠ 0) (S : Finset (HeightOneSpectrum R)) :
    ∃ T : Finset (HeightOneSpectrum R), S ⊆ T ∧
      φ.selmerGroup τ ≤ φ.unramifiedOutsideKerCohomology τ T := by
  obtain ⟨T, hST, hgood, hprime⟩ := exists_finset_isElliptic_integralModel_adicCompletion R W₁ hφ S
  exact ⟨T, hST, φ.selmerGroup_le_unramifiedOutsideKerCohomology τ hgood hprime⟩

variable (R) in
/-- **At all but finitely many places `v`, the local condition of `φ.selmerStructure τ` equals the
unramified kernel cohomology `(φ.baseChange K_v).unramifiedKerCohomology`**, whenever `deg φ` is
nonzero in `K`. -/
theorem eventually_localCondition_selmerStructure_eq_unramifiedKerCohomology
    (hφ : (φ.degree : K) ≠ 0) :
    ∀ᶠ v in Filter.cofinite, (φ.selmerStructure τ).localCondition v =
      (φ.baseChange (v.adicCompletion K)).unramifiedKerCohomology := by
  obtain ⟨T, -, hT₁, hTdeg⟩ := exists_finset_isElliptic_integralModel_adicCompletion R W₁ hφ ∅
  filter_upwards [T.finite_toSet.eventually_cofinite_notMem,
    eventually_isElliptic_integralModel_adicCompletion R W₂] with v hv ⟨_, _⟩
  obtain ⟨_, _⟩ := hT₁ v hv
  exact φ.localCondition_selmerStructure_eq_unramifiedKerCohomology τ v (hTdeg v hv)

/-- **Presentation of `Sel_φ` relative to an exceptional set `S` over a Dedekind domain with
finite residue fields at every height-one prime.** If `W₁` and `W₂` have good reduction outside
`S` and no prime outside `S` divides `deg φ`, then a class in `H¹(G_K, E₁[φ])` belongs to
`Sel_φ` (relative to all height-one completions) if and only if it is unramified outside `S` and
satisfies the local condition at the primes in `S`. When `S` is finite, this reduces `Sel_φ` to
finitely many local conditions outside the unramified locus. -/
theorem mem_selmerGroup_iff_mem_unramifiedOutsideKerCohomology_and_forall_mem
    {S : Set (HeightOneSpectrum R)}
    (hgood₁ : ∀ v ∉ S, ∃ _ : IsIntegral 𝒪[v.adicCompletion K] (W₁⁄(v.adicCompletion K)),
      (integralModel 𝒪[v.adicCompletion K] (W₁⁄(v.adicCompletion K))).IsElliptic)
    (hgood₂ : ∀ v ∉ S, ∃ _ : IsIntegral 𝒪[v.adicCompletion K] (W₂⁄(v.adicCompletion K)),
      (integralModel 𝒪[v.adicCompletion K] (W₂⁄(v.adicCompletion K))).IsElliptic)
    (hS : ∀ v ∉ S, (φ.degree : R) ∉ v.asIdeal)
    {c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff} :
    c ∈ φ.selmerGroup τ ↔
      c ∈ φ.unramifiedOutsideKerCohomology τ S ∧
        ∀ v ∈ S, φ.kerRes (τ v) c ∈ (φ.selmerStructure τ).localCondition v := by
  refine ⟨fun hc ↦ ⟨φ.selmerGroup_le_unramifiedOutsideKerCohomology τ hgood₁ hS hc,
    fun v _ ↦ (φ.mem_selmerGroup_iff_forall_kerRes_mem_localCondition τ).1 hc v⟩, ?_⟩
  rintro ⟨hur, hloc⟩
  rw [mem_selmerGroup_iff_forall_kerRes_mem_localCondition]
  intro v
  by_cases hv : v ∈ S
  · exact hloc v hv
  · obtain ⟨_, _⟩ := hgood₁ v hv
    obtain ⟨_, _⟩ := hgood₂ v hv
    rw [φ.localCondition_selmerStructure_eq_unramifiedKerCohomology τ v (hS v hv)]
    exact mem_unramifiedOutsideKerCohomology_iff.mp hur v hv

end DedekindGlobal

end TauCeti.Isogeny
