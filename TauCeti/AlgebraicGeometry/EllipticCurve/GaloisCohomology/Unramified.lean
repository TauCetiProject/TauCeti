/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Inertia
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.NumberTheory.LocalField.Unramified.Inertia.SeparableClosure

/-!
# Unramified Kummer classes at good reduction

For a Weierstrass curve over a nonarchimedean local field `K`, the unramified subgroup of
`H¹(K, E[m])` is the kernel of restriction to inertia. The coefficient module uses the separable
closure, so inertia is transported from the algebraic closure through
`TauCeti.absoluteGaloisGroupRestrictEquiv`.

At good reduction, if `m` is prime to the residue characteristic, every Kummer class is
unramified. Indeed inertia fixes every `m`-division point of a rational point, so the cocycle
`σ ↦ σ Q - Q` vanishes on inertia. This gives the containment of the local Kummer condition in
the unramified local condition used to control ramification of Selmer classes.
Consequently a Selmer class restricts to an unramified class at each nonarchimedean local
field in its defining family where the equation has good reduction and `m` is a residue unit.
Unramifiedness is also stable under restriction to any extension of nonarchimedean local fields,
since the inertia subgroup of the larger field maps into that of the smaller one. This carries the
local conditions at the places of a number field to the places of a finite extension, such as the
`m`-division field, as the proof of the finiteness of Selmer groups requires (Silverman X.4.2).

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.4.1, VIII.1.5 and X.4.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology ValuativeRel

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (W : WeierstrassCurve K) (m : ℕ)

/-- The unramified classes in `H¹(K, E[m])`: the kernel of restriction to inertia, transported
to the automorphisms of the separable closure used by `W.TorsionCoeff m`. -/
def unramifiedTorsionCohomology : AddSubgroup (H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) :=
  (explicitRes1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)
    ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom)).ker

/-- A class is unramified exactly when its restriction to inertia is zero. -/
@[simp]
theorem mem_unramifiedTorsionCohomology_iff
    {c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)} :
    c ∈ W.unramifiedTorsionCohomology m ↔
      explicitRes1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) c = 0 :=
  (Iff.rfl)

/-- **Unramified classes restrict to unramified classes.** For an extension `L/K` of
nonarchimedean local fields and a `K`-embedding `τ : Kˢ → Lˢ` of separable closures, restriction
`H¹(K, E[m]) → H¹(L, E[m])` along `τ` sends unramified classes to unramified classes, because the
inertia subgroup of `L` maps into that of `K`. No reduction hypothesis on `W` is needed. -/
theorem torsionRes_mem_unramifiedTorsionCohomology {L : Type*} [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    (τ : SeparableClosure K →ₐ[K] SeparableClosure L)
    {c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)}
    (hc : c ∈ W.unramifiedTorsionCohomology m) :
    W.torsionRes τ m c ∈ (W⁄L).unramifiedTorsionCohomology m := by
  rw [mem_unramifiedTorsionCohomology_iff, torsionRes_eq_explicitMap1]
  exact (absoluteGaloisGroupMap τ).explicitRes1_explicitMap1_eq_zero_of_map_le _ _ _
    (τ.map_absoluteGaloisGroupMap_inertiaSubgroup_le) hc

variable [IsIntegral 𝒪[K] W] [(integralModel 𝒪[K] W).IsElliptic]

local instance : W.IsElliptic := by
  rw [← baseChange_integralModel_eq 𝒪[K] W]
  infer_instance

open scoped Classical in
variable {W m} in
/-- At good reduction, inertia fixes an `m`-division point of a `K`-rational point when `m`
is prime to the residue characteristic. The action here is on the discrete coefficient module
over the separable closure. -/
theorem smul_pointCoeff_eq_self_of_mem_inertiaSubgroup
    (hm : (m : 𝓀[K]) ≠ 0) {P : W.toAffine.Point} {Q : W.PointCoeff}
    (hQ : m • Q = W.basePointCoeff P) {σ : Gal(AlgebraicClosure K/K)}
    (hσ : σ ∈ inertiaSubgroup K) : absoluteGaloisGroupRestrictEquiv K σ • Q = Q := by
  classical
  let i : SeparableClosure K →ₐ[K] AlgebraicClosure K :=
    (separableClosure K (AlgebraicClosure K)).val
  have hfix : Affine.Point.map σ.toAlgHom
      (m • Affine.Point.map i (W.pointCoeffEquiv.symm Q)) =
        m • Affine.Point.map i (W.pointCoeffEquiv.symm Q) := by
    rw [← map_nsmul, ← map_nsmul, hQ]
    rw [Affine.Point.map_map_separableClosure_val, ← pointCoeffEquiv_symm_smul,
      smul_basePointCoeff]
  have h := Affine.Point.map_eq_self_of_mem_inertiaSubgroup_algebraicClosure hm hσ hfix
  apply W.pointCoeffEquiv.symm.injective
  rw [pointCoeffEquiv_symm_smul]
  apply Affine.Point.map_injective i
  rw [← Affine.Point.map_map_separableClosure_val]
  exact h

open scoped Classical in
variable {W m} in
/-- The Kummer cocycle of a division point of a rational point vanishes on inertia at good
reduction, when its multiplier is prime to the residue characteristic. -/
theorem kummerCocycle_eq_zero_of_mem_inertiaSubgroup
    (hm : (m : 𝓀[K]) ≠ 0) {P : W.toAffine.Point} {Q : W.PointCoeff}
    (hQ : m • Q = W.basePointCoeff P) {σ : Gal(AlgebraicClosure K/K)}
    (hσ : σ ∈ inertiaSubgroup K) :
    kummerCocycle hQ (absoluteGaloisGroupRestrictEquiv K σ) = 0 := by
  classical
  apply Subtype.ext
  rw [coe_kummerCocycle, smul_pointCoeff_eq_self_of_mem_inertiaSubgroup hm hQ hσ, sub_self]
  rfl

open scoped Classical in
/-- At good reduction, the Kummer class of a rational point is unramified when the multiplier is
prime to the residue characteristic. -/
theorem kummerMap_mem_unramifiedTorsionCohomology
    (hmres : (m : 𝓀[K]) ≠ 0) (P : W.toAffine.Point) :
    W.kummerMap m (by
      have hm := (IsLocalRing.residue_ne_zero_iff_isUnit (m : 𝒪[K])).mp
        (by simpa using hmres)
      simpa using hm.map (algebraMap 𝒪[K] K)) P ∈ W.unramifiedTorsionCohomology m := by
  classical
  generalize_proofs
  rename_i hm
  obtain ⟨Q, hQ⟩ := (W.kummerShortExact m hm).proj_surjective (W.basePointCoeff P)
  rw [kummerShortExact_proj, nsmulAddMonoidHom_apply] at hQ
  rw [mem_unramifiedTorsionCohomology_iff, kummerMap_eq_H1pi hm hQ]
  have hzero : cocyclesMap1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)
      ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom)
      (W.TorsionCoeff m) (ContinuousMonoidHom.subgroupSubtype _)
      (AddMonoidHom.id _) continuous_id
      (ContinuousMonoidHom.id_subgroupSubtype_smul _ _)
      ⟨kummerCocycle hQ, kummerCocycle_mem_Z1 hQ⟩ = 0 := by
    apply Subtype.ext
    funext σ
    rw [cocyclesMap1_apply, AddMonoidHom.id_apply, ContinuousMonoidHom.subgroupSubtype_apply]
    obtain ⟨τ, hτ, hτσ⟩ := σ.2
    rw [← hτσ]
    exact kummerCocycle_eq_zero_of_mem_inertiaSubgroup hmres hQ hτ
  exact (explicitRes1_mk _ _ _ _).trans (congrArg (H1pi _ _) hzero)

open scoped Classical in
/-- At good reduction away from the multiplier, the local Kummer condition is contained in
the unramified local condition. -/
theorem range_kummerMap_le_unramifiedTorsionCohomology
    (hmres : (m : 𝓀[K]) ≠ 0) :
    (W.kummerMap m (by
      have hm := (IsLocalRing.residue_ne_zero_iff_isUnit (m : 𝒪[K])).mp
        (by simpa using hmres)
      simpa using hm.map (algebraMap 𝒪[K] K))).range ≤ W.unramifiedTorsionCohomology m := by
  classical
  rintro c ⟨P, rfl⟩
  exact W.kummerMap_mem_unramifiedTorsionCohomology m hmres P

end WeierstrassCurve

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology ValuativeRel

variable {K : Type*} [Field K] (W : WeierstrassCurve K)
  {ι : Type*} {L : ι → Type*} [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
  (τ : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i)) (i : ι)
  [ValuativeRel (L i)] [TopologicalSpace (L i)] [IsNonarchimedeanLocalField (L i)]
  [IsIntegral 𝒪[L i] (W⁄(L i))] [(integralModel 𝒪[L i] (W⁄(L i))).IsElliptic]

/-- A Selmer class is unramified at each nonarchimedean local field in its defining family
where the equation has good reduction and the multiplier is prime to the residue characteristic.
No good-reduction assumption is made at the other fields in the family. -/
theorem torsionRes_mem_unramifiedTorsionCohomology_of_mem_selmerGroup {m : ℕ}
    (hmres : (m : 𝓀[L i]) ≠ 0)
    {c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)} (hc : c ∈ W.selmerGroup τ m) :
    W.torsionRes (τ i) m c ∈ (W⁄(L i)).unramifiedTorsionCohomology m := by
  classical
  have : (W⁄(L i)).IsElliptic := by
    rw [← baseChange_integralModel_eq 𝒪[L i] (W⁄(L i))]
    infer_instance
  have : W.IsElliptic := by
    rw [isElliptic_iff, isUnit_iff_ne_zero]
    intro hΔ
    have hΔL := (W⁄(L i)).isUnit_Δ.ne_zero
    rw [baseChange, map_Δ, hΔ, map_zero] at hΔL
    exact hΔL rfl
  have hmL : IsUnit (m : L i) := by
    have hm := (IsLocalRing.residue_ne_zero_iff_isUnit (m : 𝒪[L i])).mp
      (by simpa using hmres)
    simpa using hm.map (algebraMap 𝒪[L i] (L i))
  have hm : IsUnit (m : K) := by
    rw [isUnit_iff_ne_zero]
    intro h
    apply hmL.ne_zero
    simpa using congrArg (algebraMap K (L i)) h
  exact (W⁄(L i)).range_kummerMap_le_unramifiedTorsionCohomology m
    hmres
    ((W.mem_selmerGroup_iff_forall_torsionRes_mem_range_kummerMap τ hm).mp hc i)

/-! ### Classes unramified outside `S` -/

section Dedekind

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K)
  (τ : ∀ v : HeightOneSpectrum R,
    SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
  (S : Set (HeightOneSpectrum R)) (m : ℕ)

/-- **The classes of `H¹(G_K, E[m])` unramified outside `S`**: those whose restriction to the
completion `K_v` along `τ v`, for every prime `v ∉ S`, is unramified, that is, vanishes on the
inertia subgroup of `K_v`. -/
def unramifiedOutsideTorsionCohomology :
    AddSubgroup (H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) :=
  ⨅ (v : HeightOneSpectrum R) (_ : v ∉ S),
    ((W⁄(v.adicCompletion K)).unramifiedTorsionCohomology m).comap (W.torsionRes (τ v) m)

variable {W τ S m}

/-- A class is unramified outside `S` exactly when its restriction to every `K_v` with `v ∉ S`
is unramified. -/
@[simp]
theorem mem_unramifiedOutsideTorsionCohomology_iff
    {c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)} :
    c ∈ W.unramifiedOutsideTorsionCohomology τ S m ↔
      ∀ v ∉ S, W.torsionRes (τ v) m c ∈ (W⁄(v.adicCompletion K)).unramifiedTorsionCohomology m := by
  simp only [unramifiedOutsideTorsionCohomology, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]

/-- **Selmer classes are unramified outside the bad primes.** If `W` has good reduction at every
prime `v ∉ S` and no prime outside `S` divides `m`, then every class of the `m`-Selmer group
relative to the completions `K_v` is unramified outside `S`. -/
theorem selmerGroup_le_unramifiedOutsideTorsionCohomology
    (hgood : ∀ v ∉ S, ∃ _ : IsIntegral 𝒪[v.adicCompletion K] (W⁄(v.adicCompletion K)),
      (integralModel 𝒪[v.adicCompletion K] (W⁄(v.adicCompletion K))).IsElliptic)
    (hS : ∀ v ∉ S, (m : R) ∉ v.asIdeal) :
    W.selmerGroup τ m ≤ W.unramifiedOutsideTorsionCohomology τ S m := by
  intro c hc
  rw [mem_unramifiedOutsideTorsionCohomology_iff]
  intro v hv
  obtain ⟨_, _⟩ := hgood v hv
  refine W.torsionRes_mem_unramifiedTorsionCohomology_of_mem_selmerGroup τ v ?_ hc
  rw [Ne, ringChar.spec, v.ringChar_residueField_adicCompletion_dvd_iff]
  exact hS v hv

end Dedekind

end WeierstrassCurve
