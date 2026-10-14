/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Inertia

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
  have hcomm : σ.toAlgHom.comp i =
      i.comp (absoluteGaloisGroupRestrictEquiv K σ).toAlgHom := by
    ext x
    exact (coe_absoluteGaloisGroupRestrictEquiv_apply K σ x).symm
  have hfix : Affine.Point.map σ.toAlgHom
      (m • Affine.Point.map i (W.pointCoeffEquiv.symm Q)) =
        m • Affine.Point.map i (W.pointCoeffEquiv.symm Q) := by
    rw [← map_nsmul, ← map_nsmul, hQ]
    rw [Affine.Point.map_map, hcomm, ← Affine.Point.map_map,
      ← pointCoeffEquiv_symm_smul, smul_basePointCoeff]
  have h := Affine.Point.map_eq_self_of_mem_inertiaSubgroup_algebraicClosure hm hσ hfix
  apply W.pointCoeffEquiv.symm.injective
  rw [pointCoeffEquiv_symm_smul]
  apply Affine.Point.map_injective i
  rw [Affine.Point.map_map, ← hcomm, ← Affine.Point.map_map]
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

end WeierstrassCurve
