/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Inertia
public import TauCeti.NumberTheory.LocalField.Unramified.Cohomology
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.LocalField

/-!
# Unramified Kummer classes at integral elliptic models

For a Weierstrass curve over a nonarchimedean local field `K`, the unramified subgroup of
`H¹(K, E[m])` is the kernel of restriction to inertia (`TauCeti.unramifiedH1`). The
coefficient module uses the separable closure, so inertia is transported from the algebraic closure
through `TauCeti.absoluteGaloisGroupRestrictEquiv`. When `W` is elliptic and `m ≠ 0`, this
unramified subgroup is finite of order `#E(K)[m]`.

When the chosen equation `W` is integral over `𝒪[K]` with an elliptic integral model (unit
discriminant), if `m` is prime to the residue characteristic, every Kummer class is unramified.
Indeed inertia fixes every `m`-division point of a rational point, so the cocycle `σ ↦ σ Q - Q`
vanishes on inertia. Over any nonarchimedean local field `K` where `(m : 𝓀[K]) ≠ 0` and the
chosen equation `W` is integral over `𝒪[K]` with unit discriminant, comparing orders with
`[E(K) : m E(K)] = #E(K)[m]` upgrades this inclusion to equality: the kernel of
`H¹(G_K, E[m]) → H¹(G_K, E)` equals `W.unramifiedTorsionCohomology m`, and hence
`(W.kummerMap m hm).range = W.unramifiedTorsionCohomology m` (in particular over Dedekind-domain
completions `F_u` at finite-residue-field primes `u` not dividing `m`).

Consequently a Selmer class restricts to an unramified class at each nonarchimedean local
field in its defining family where the base-changed equation is integral with unit discriminant and
`m` is a residue unit.
Unramifiedness is also stable under restriction to any extension of nonarchimedean local fields,
since the inertia subgroup of the larger field maps into that of the smaller one. This carries the
local conditions at the places of a number field to the places of a finite extension, such as the
`m`-division field, as the proof of the finiteness of Selmer groups requires (Silverman X.4.2).

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.4.1, VIII.1.5 and X.4.
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, Proposition 3.8.
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
  unramifiedH1 K (W.TorsionCoeff m)

/-- `unramifiedTorsionCohomology` is `TauCeti.unramifiedH1` on `W.TorsionCoeff m`. -/
theorem unramifiedTorsionCohomology_eq_unramifiedH1 :
    W.unramifiedTorsionCohomology m = unramifiedH1 K (W.TorsionCoeff m) :=
  (rfl)

/-- A class is unramified exactly when its restriction to inertia is zero. -/
@[simp]
theorem mem_unramifiedTorsionCohomology_iff
    {c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)} :
    c ∈ W.unramifiedTorsionCohomology m ↔
      explicitRes1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)
        (separableClosureInertiaSubgroup K) c = 0 := by
  rw [unramifiedTorsionCohomology_eq_unramifiedH1, mem_unramifiedH1_iff]

/-- For an elliptic curve and `m ≠ 0`, `unramifiedTorsionCohomology` is finite. -/
instance finite_unramifiedTorsionCohomology [W.IsElliptic] [NeZero m] :
    Finite (W.unramifiedTorsionCohomology m) := by
  rw [unramifiedTorsionCohomology_eq_unramifiedH1]
  infer_instance

/-- **Order of unramified `m`-torsion cohomology**: `#H¹_ur(G_K, E[m]) = #E(K)[m]` for `m ≠ 0`. -/
theorem natCard_unramifiedTorsionCohomology [DecidableEq K] [W.IsElliptic] [NeZero m] :
    Nat.card (W.unramifiedTorsionCohomology m) =
      Nat.card (AddSubgroup.torsionBy W.toAffine.Point m) := by
  rw [unramifiedTorsionCohomology_eq_unramifiedH1,
    natCard_unramifiedH1_eq_natCard_H0]
  exact Nat.card_congr (W.baseTorsionEquivInvariants m).symm.toEquiv

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
  rw [unramifiedTorsionCohomology_eq_unramifiedH1] at hc ⊢
  rw [torsionRes_eq_explicitMap1]
  exact τ.explicitMap1_mem_unramifiedH1 (W.torsionCoeffBaseChange τ m)
    continuous_of_discreteTopology (W.torsionCoeffBaseChange_smul τ m) hc

variable [IsIntegral 𝒪[K] W] [(integralModel 𝒪[K] W).IsElliptic]

local instance : W.IsElliptic := by
  rw [← baseChange_integralModel_eq 𝒪[K] W]
  infer_instance

variable {W m} in
/-- When `W` is integral over `𝒪[K]` with unit discriminant (an elliptic integral model), inertia
fixes an `m`-division point of a `K`-rational point when `m` is prime to the residue
characteristic. The action here is on the discrete coefficient module over the separable
closure. -/
theorem smul_pointCoeff_eq_self_of_mem_inertiaSubgroup [DecidableEq K]
    (hm : (m : 𝓀[K]) ≠ 0) {P : W.toAffine.Point} {Q : W.PointCoeff}
    (hQ : m • Q = W.basePointCoeff P) {σ : Gal(AlgebraicClosure K/K)}
    (hσ : σ ∈ inertiaSubgroup K) : absoluteGaloisGroupRestrictEquiv K σ • Q = Q := by
  let := Classical.decEq (AlgebraicClosure K)
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

variable {W m} in
/-- When `W` is integral over `𝒪[K]` with unit discriminant (an elliptic integral model), the
Kummer cocycle of a division point of a rational point vanishes on inertia when its multiplier is
prime to the residue characteristic. -/
theorem kummerCocycle_eq_zero_of_mem_inertiaSubgroup [DecidableEq K]
    (hm : (m : 𝓀[K]) ≠ 0) {P : W.toAffine.Point} {Q : W.PointCoeff}
    (hQ : m • Q = W.basePointCoeff P) {σ : Gal(AlgebraicClosure K/K)}
    (hσ : σ ∈ inertiaSubgroup K) :
    kummerCocycle hQ (absoluteGaloisGroupRestrictEquiv K σ) = 0 := by
  apply Subtype.ext
  rw [coe_kummerCocycle, smul_pointCoeff_eq_self_of_mem_inertiaSubgroup hm hQ hσ, sub_self]
  rfl

/-- When `W` is integral over `𝒪[K]` with unit discriminant (an elliptic integral model), the
Kummer class of a rational point is unramified when the multiplier is prime to the residue
characteristic. -/
theorem kummerMap_mem_unramifiedTorsionCohomology [DecidableEq K]
    (hmres : (m : 𝓀[K]) ≠ 0) (P : W.toAffine.Point) :
    W.kummerMap m (natCast_ne_zero_of_residueField_natCast_ne_zero hmres).isUnit P ∈
      W.unramifiedTorsionCohomology m := by
  generalize_proofs
  rename_i hm
  obtain ⟨Q, hQ⟩ := (W.kummerShortExact m hm).proj_surjective (W.basePointCoeff P)
  rw [kummerShortExact_proj, nsmulAddMonoidHom_apply] at hQ
  rw [unramifiedTorsionCohomology_eq_unramifiedH1, kummerMap_eq_H1pi hm hQ,
    QuotientAddGroup.mk'_apply]
  exact mk_mem_unramifiedH1_of_forall_mem_inertiaSubgroup
    (f := ⟨kummerCocycle hQ, kummerCocycle_mem_Z1 hQ⟩)
    fun _ hσ ↦ kummerCocycle_eq_zero_of_mem_inertiaSubgroup hmres hQ hσ

/-- When `W` is integral over `𝒪[K]` with unit discriminant (an elliptic integral model) and `m` is
prime to the residue characteristic, the local Kummer condition is contained in the unramified
local condition. -/
theorem range_kummerMap_le_unramifiedTorsionCohomology [DecidableEq K]
    (hmres : (m : 𝓀[K]) ≠ 0) :
    (W.kummerMap m (natCast_ne_zero_of_residueField_natCast_ne_zero hmres).isUnit).range ≤
      W.unramifiedTorsionCohomology m := by
  rintro c ⟨P, rfl⟩
  exact W.kummerMap_mem_unramifiedTorsionCohomology m hmres P

/-- When `W` is integral over `𝒪[K]` with unit discriminant (an elliptic integral model) and `m` is
prime to the residue characteristic, the kernel of `H¹(G_K, E[m]) → H¹(G_K, E)` is contained in
`W.unramifiedTorsionCohomology m`. Unlike `range_kummerMap_le_unramifiedTorsionCohomology`, this
form needs no `DecidableEq K`. -/
theorem ker_explicitCoeff1_torsionCoeffIncl_le_unramifiedTorsionCohomology
    (hmres : (m : 𝓀[K]) ≠ 0) :
    (explicitCoeff1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) (W.torsionCoeffIncl m)
      continuous_of_discreteTopology).ker ≤ W.unramifiedTorsionCohomology m := by
  classical
  rw [← W.range_kummerMap m (natCast_ne_zero_of_residueField_natCast_ne_zero hmres).isUnit]
  exact W.range_kummerMap_le_unramifiedTorsionCohomology m hmres

private theorem natCard_submodule_torsionBy_eq_addSubgroup (A : Type*) [AddCommGroup A] (m : ℕ) :
    Nat.card (Submodule.torsionBy ℤ A m) = Nat.card (AddSubgroup.torsionBy A m) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun P ↦ by
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul, AddSubgroup.torsionBy.nsmul_iff])

private theorem index_range_nsmul_eq_natCard_torsionBy [DecidableEq K] (hmres : (m : 𝓀[K]) ≠ 0) :
    (nsmulAddMonoidHom (α := W.toAffine.Point) m).range.index =
      Nat.card (AddSubgroup.torsionBy W.toAffine.Point m) := by
  have hmU : IsUnit (m : K) := (natCast_ne_zero_of_residueField_natCast_ne_zero hmres).isUnit
  have hmO : IsUnit (m : 𝒪[K]) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit (m : 𝒪[K])).mp (by simpa using hmres)
  have hcard : Nat.card (𝒪[K] ⧸ Ideal.span {(m : 𝒪[K])}) = 1 :=
    have : Subsingleton (𝒪[K] ⧸ Ideal.span {(m : 𝒪[K])}) :=
      Ideal.Quotient.subsingleton_iff.mpr (Ideal.span_singleton_eq_top.mpr hmO)
    Nat.card_unique
  rw [W.index_range_nsmul_eq_natCard_torsionBy_mul_of_localField hmU.ne_zero,
    hcard, mul_one, natCard_submodule_torsionBy_eq_addSubgroup]

/-- **When `W` is integral over `𝒪[K]` with unit discriminant away from `m`, the local Selmer
condition equals unramified cohomology** (Milne, *ADT* I, Proposition 3.8): over a nonarchimedean
local field `K`, if `W` is integral over `𝒪[K]` with unit discriminant (an elliptic integral model)
and `(m : 𝓀[K]) ≠ 0`, then `ker(H¹(G_K, E[m]) → H¹(G_K, E)) = W.unramifiedTorsionCohomology m`.
Needs no `DecidableEq K`. -/
theorem ker_explicitCoeff1_torsionCoeffIncl_eq_unramifiedTorsionCohomology
    (hmres : (m : 𝓀[K]) ≠ 0) :
    (explicitCoeff1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) (W.torsionCoeffIncl m)
      continuous_of_discreteTopology).ker = W.unramifiedTorsionCohomology m := by
  classical
  have hmU : IsUnit (m : K) := (natCast_ne_zero_of_residueField_natCast_ne_zero hmres).isUnit
  have : NeZero m := NeZero.of_neZero_natCast K (h := ⟨hmU.ne_zero⟩)
  -- Compare orders: `#(im δ_m) = [E(K) : m E(K)] = #E(K)[m] = #H¹_ur(K, E[m])`.
  have hcard : Nat.card (W.unramifiedTorsionCohomology m) ≤
      Nat.card ((explicitCoeff1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)
        (W.torsionCoeffIncl m) continuous_of_discreteTopology).ker) := by
    rw [W.natCard_unramifiedTorsionCohomology m, ← W.range_kummerMap m hmU,
      ← AddSubgroup.index_ker, W.ker_kummerMap m hmU,
      W.index_range_nsmul_eq_natCard_torsionBy m hmres]
  exact AddSubgroup.eq_of_le_of_card_ge
    (W.ker_explicitCoeff1_torsionCoeffIncl_le_unramifiedTorsionCohomology m hmres) hcard

/-- **When `W` is integral over `𝒪[K]` with unit discriminant away from `m`, the local Kummer image
equals unramified cohomology** over any nonarchimedean local field `K`. -/
theorem range_kummerMap_eq_unramifiedTorsionCohomology_of_localField [DecidableEq K]
    (hmres : (m : 𝓀[K]) ≠ 0) :
    (W.kummerMap m (natCast_ne_zero_of_residueField_natCast_ne_zero hmres).isUnit).range =
      W.unramifiedTorsionCohomology m := by
  rw [W.range_kummerMap m (natCast_ne_zero_of_residueField_natCast_ne_zero hmres).isUnit]
  exact W.ker_explicitCoeff1_torsionCoeffIncl_eq_unramifiedTorsionCohomology m hmres

section AdicCompletion

open IsDedekindDomain

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A) [Finite (A ⧸ u.asIdeal)] [DecidableEq (u.adicCompletion F)]
  (V : WeierstrassCurve (u.adicCompletion F))
  [IsIntegral 𝒪[u.adicCompletion F] V] [(integralModel 𝒪[u.adicCompletion F] V).IsElliptic]

/-- **When the chosen equation is integral with unit discriminant away from `m`, the local Kummer
image equals unramified cohomology** (Milne, *ADT* I, Proposition 3.8): over the `u`-adic
completion of the fraction field of a Dedekind domain with finite residue field `A ⧸ u`, if the
chosen equation `V` is integral over `𝒪[F_u]` with an elliptic integral model (unit discriminant)
and `m ∉ u`, then `im(δ_m : E(F_u) → H¹(G_{F_u}, E[m])) = H¹_ur(G_{F_u}, E[m])`. -/
theorem range_kummerMap_eq_unramifiedTorsionCohomology
    (hm : (m : A) ∉ u.asIdeal) :
    (V.kummerMap m (natCast_ne_zero_of_residueField_natCast_ne_zero
      (u.residueField_adicCompletion_natCast_ne_zero_of_notMem (K := F) hm)).isUnit).range =
      V.unramifiedTorsionCohomology m :=
  V.range_kummerMap_eq_unramifiedTorsionCohomology_of_localField m
    (u.residueField_adicCompletion_natCast_ne_zero_of_notMem hm)

end AdicCompletion

end WeierstrassCurve

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology ValuativeRel

variable {K : Type*} [Field K] (W : WeierstrassCurve K)
  {ι : Type*} {L : ι → Type*} [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
  (τ : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i)) (i : ι)
  [ValuativeRel (L i)] [TopologicalSpace (L i)] [IsNonarchimedeanLocalField (L i)]
  [IsIntegral 𝒪[L i] (W⁄(L i))] [(integralModel 𝒪[L i] (W⁄(L i))).IsElliptic]

/-- A Selmer class is unramified at each nonarchimedean local field in its defining family
where the base-changed equation is integral with unit discriminant and the multiplier is prime to
the residue characteristic. No good-reduction assumption is made at the other fields in the
family. -/
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
  have hmL : IsUnit (m : L i) := (natCast_ne_zero_of_residueField_natCast_ne_zero hmres).isUnit
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
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K)
  (τ : ∀ v : HeightOneSpectrum R,
    SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
  (S : Set (HeightOneSpectrum R)) (m : ℕ)

/-- **The classes of `H¹(G_K, E[m])` unramified outside `S`**: those whose restriction to the
completion `K_v` along `τ v`, for every prime `v ∉ S`, is unramified, that is, vanishes on the
inertia subgroup of `K_v`. -/
def unramifiedOutsideTorsionCohomology (hfinite : ∀ v ∉ S, Finite (R ⧸ v.asIdeal)) :
    AddSubgroup (H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) :=
  ⨅ (v : HeightOneSpectrum R) (hv : v ∉ S),
    letI : Finite (R ⧸ v.asIdeal) := hfinite v hv
    ((W⁄(v.adicCompletion K)).unramifiedTorsionCohomology m).comap (W.torsionRes (τ v) m)

variable {W τ S m}

/-- A class is unramified outside `S` exactly when its restriction to every `K_v` with `v ∉ S`
is unramified. -/
@[simp]
theorem mem_unramifiedOutsideTorsionCohomology_iff
    {hfinite : ∀ v ∉ S, Finite (R ⧸ v.asIdeal)}
    {c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)} :
    c ∈ W.unramifiedOutsideTorsionCohomology τ S m hfinite ↔
      ∀ (v : HeightOneSpectrum R) (hv : v ∉ S),
        letI : Finite (R ⧸ v.asIdeal) := hfinite v hv
        W.torsionRes (τ v) m c ∈ (W⁄(v.adicCompletion K)).unramifiedTorsionCohomology m := by
  simp only [unramifiedOutsideTorsionCohomology, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]

/-- **Selmer classes are unramified outside the bad primes.** If the base-changed equation `W⁄K_v`
is integral over `𝒪[K_v]` with an elliptic integral model at every prime `v ∉ S` and no prime
outside `S` divides `m`, then every class of the `m`-Selmer group relative to the completions `K_v`
is unramified outside `S`. -/
theorem selmerGroup_le_unramifiedOutsideTorsionCohomology
    (hfinite : ∀ v ∉ S, Finite (R ⧸ v.asIdeal))
    (hgood : ∀ v ∉ S, ∃ _ : IsIntegral 𝒪[v.adicCompletion K] (W⁄(v.adicCompletion K)),
      (integralModel 𝒪[v.adicCompletion K] (W⁄(v.adicCompletion K))).IsElliptic)
    (hS : ∀ v ∉ S, (m : R) ∉ v.asIdeal) :
    W.selmerGroup τ m ≤ W.unramifiedOutsideTorsionCohomology τ S m hfinite := by
  intro c hc
  rw [mem_unramifiedOutsideTorsionCohomology_iff]
  intro v hv
  have : Finite (R ⧸ v.asIdeal) := hfinite v hv
  obtain ⟨_, _⟩ := hgood v hv
  exact W.torsionRes_mem_unramifiedTorsionCohomology_of_mem_selmerGroup τ v
    (v.residueField_adicCompletion_natCast_ne_zero_of_notMem (hS v hv)) hc

end Dedekind

end WeierstrassCurve
