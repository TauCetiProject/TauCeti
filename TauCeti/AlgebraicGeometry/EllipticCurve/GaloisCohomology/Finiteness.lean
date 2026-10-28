/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Unramified
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Basic
public import TauCeti.NumberTheory.NumberField.Kummer.SelmerGroup

/-!
# Finiteness of the `m`-Selmer group when `E[m]` is rational

Let `R` be a Dedekind domain with finite residue fields and fraction field `K`, and let `W` be a
Weierstrass curve over `K`. For each prime `v` of `R` fix a `K`-embedding `τ v : Kˢ → K_vˢ` of
separable closures. A class of `H¹(G_K, E[m])` is **unramified outside** a set `S` of primes when,
for every `v ∉ S`, its restriction to `K_v` along `τ v` vanishes on the inertia subgroup of `K_v`
(`WeierstrassCurve.unramifiedOutsideTorsionCohomology`).

At a prime `v ∉ S` where `W` has good reduction and which does not divide `m`, local Kummer
classes are unramified, so every class of the `m`-Selmer group relative to the completions
`K_v` is unramified outside `S`
(`WeierstrassCurve.selmerGroup_le_unramifiedOutsideTorsionCohomology`).

For a rational point `T ∈ E(K)[m]`, the Weil pairing `e_m(·, T) : E[m] → μ_m` carries classes
unramified outside `S` to Kummer classes unramified outside `S`
(`WeierstrassCurve.explicitCoeff1_weilPairingCoeff_mem_unramifiedOutsideKummerCohomology`),
because restriction to `K_v` commutes with it and a coefficient map preserves vanishing on
inertia. Over a number field the latter form a finite group for finite `S`
(`TauCeti.finite_unramifiedOutsideKummerCohomology`). When `G_K` fixes every point of
`E(Kˢ)[m]`, the maps `e_m(·, T)` jointly detect every class
(`WeierstrassCurve.finite_of_forall_finite_image_explicitCoeff1_weilPairingCoeff`), so the
classes unramified outside a finite `S` are finitely many
(`WeierstrassCurve.finite_unramifiedOutsideTorsionCohomology`), and so is the `m`-Selmer group
(`WeierstrassCurve.finite_selmerGroup_of_forall_smul_eq`). This is the case `E[m] ⊆ E(K)` of the
finiteness of `Sel_m(E/K)` (Silverman X.4.2), to which the general case reduces by restriction to
the `m`-division field.

## Main definitions

* `WeierstrassCurve.unramifiedOutsideTorsionCohomology τ S m`: the classes of `H¹(G_K, E[m])`
  whose restriction to every `K_v` with `v ∉ S` is unramified.

## Main results

* `WeierstrassCurve.selmerGroup_le_unramifiedOutsideTorsionCohomology`: `m`-Selmer classes are
  unramified outside the primes of bad reduction and the primes dividing `m`.
* `WeierstrassCurve.explicitCoeff1_weilPairingCoeff_mem_unramifiedOutsideKummerCohomology`: the
  Weil pairing with a rational `m`-torsion point preserves being unramified outside `S`.
* `WeierstrassCurve.finite_unramifiedOutsideTorsionCohomology`: over a number field with
  `E[m] ⊆ E(K)`, finitely many classes are unramified outside a finite `S`.
* `WeierstrassCurve.finite_selmerGroup_of_forall_smul_eq`: over a number field with
  `E[m] ⊆ E(K)`, the `m`-Selmer group relative to the completions at the finite places is finite.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.1, Proposition X.4.2
  and its proof.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology IsDedekindDomain ValuativeRel

/-! ### Weil pairings on classes unramified outside `S` -/

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K)
  (τ : ∀ v : HeightOneSpectrum R,
    SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
  (S : Set (HeightOneSpectrum R)) (m : ℕ)

variable {W τ S m}

open scoped Classical in
/-- **The Weil pairing preserves being unramified outside `S`.** For a rational point
`T ∈ E(K)[m]`, the map `H¹(G_K, E[m]) → H¹(G_K, μ_m)` induced by `e_m(·, T)` carries classes
unramified outside `S` to Kummer classes unramified outside `S`. -/
theorem explicitCoeff1_weilPairingCoeff_mem_unramifiedOutsideKummerCohomology [W.IsElliptic]
    (hm : IsUnit (m : K)) (T : AddSubgroup.torsionBy W.toAffine.Point m)
    {c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)}
    (hc : c ∈ W.unramifiedOutsideTorsionCohomology τ S m) :
    explicitCoeff1 _ _ (W.weilPairingCoeff m hm T) continuous_of_discreteTopology c ∈
      unramifiedOutsideKummerCohomology τ S m := by
  rw [mem_unramifiedOutsideKummerCohomology_iff]
  intro v hv
  -- the image of `T` in `E(K_v)[m]`
  let T' : AddSubgroup.torsionBy (W⁄(v.adicCompletion K)).toAffine.Point m :=
    ⟨W.toAffine.pointMap _ T, AddSubgroup.torsionBy.nsmul_iff.2 <| by
      rw [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.1 T.2, map_zero]⟩
  -- restriction to `K_v` commutes with `e_m(·, T)`, and a coefficient map over `G_{K_v}`
  -- preserves vanishing on inertia
  rw [W.explicitMap1_explicitCoeff1_weilPairingCoeff m hm (τ v) (T' := T') rfl,
    explicitCoeff1_eq_explicitMap1]
  exact (ContinuousMonoidHom.id _).explicitRes1_explicitMap1_eq_zero_of_map_le _ _ _
    (by rintro _ ⟨g, hg, rfl⟩; exact hg)
    ((mem_unramifiedTorsionCohomology_iff _ _).1
      (mem_unramifiedOutsideTorsionCohomology_iff.1 hc v hv))

end Dedekind

/-! ### Finiteness over a number field -/

section NumberField

open NumberField

variable {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K)
  {τ : ∀ v : HeightOneSpectrum (𝓞 K),
    SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)}
  {S : Set (HeightOneSpectrum (𝓞 K))} {m : ℕ}

/-- **Finiteness of the classes unramified outside `S` when `E[m]` is rational.** Over a number
field `K`, if `m ≠ 0`, `G_K` fixes every point of `E(Kˢ)[m]` and `S` is finite, only finitely many
classes of `H¹(G_K, E[m])` are unramified outside `S`. Through the Weil pairing with the points of
`E(K)[m]` they embed into finitely many copies of the finite group of Kummer classes unramified
outside `S`. -/
theorem finite_unramifiedOutsideTorsionCohomology [W.IsElliptic] (hSf : S.Finite) (hm : m ≠ 0)
    (h : ∀ (σ : AbsoluteGaloisGroup K) (P : W.TorsionCoeff m), σ • P = P) :
    Finite (W.unramifiedOutsideTorsionCohomology τ S m) := by
  classical
  have hmK : IsUnit (m : K) := (Nat.cast_ne_zero.2 hm).isUnit
  have := finite_unramifiedOutsideKummerCohomology (τ := τ) hSf hmK
  refine Set.Finite.to_subtype
    (W.finite_of_forall_finite_image_explicitCoeff1_weilPairingCoeff m hmK h fun T ↦ ?_)
  refine (Set.finite_coe_iff.1 this).subset ?_
  rintro _ ⟨c, hc, rfl⟩
  exact explicitCoeff1_weilPairingCoeff_mem_unramifiedOutsideKummerCohomology hmK T hc

/-- **Finiteness of the `m`-Selmer group when `E[m]` is rational** (Silverman X.4.2, case
`E[m] ⊆ E(K)`). Over a number field `K`, let `W` have good reduction at every prime outside a
finite set `S`. If `m ≠ 0` and `G_K` fixes every point of `E(Kˢ)[m]`, the `m`-Selmer group of `W`
relative to the completions of `K` at its finite places is finite. -/
theorem finite_selmerGroup_of_forall_smul_eq [W.IsElliptic] (hSf : S.Finite)
    (hgood : ∀ v ∉ S, ∃ _ : IsIntegral 𝒪[v.adicCompletion K] (W⁄(v.adicCompletion K)),
      (integralModel 𝒪[v.adicCompletion K] (W⁄(v.adicCompletion K))).IsElliptic)
    (hm : m ≠ 0) (h : ∀ (σ : AbsoluteGaloisGroup K) (P : W.TorsionCoeff m), σ • P = P) :
    Finite (W.selmerGroup τ m) := by
  -- enlarge `S` by the finitely many primes dividing `m`
  let T := S ∪ {v : HeightOneSpectrum (𝓞 K) | (m : 𝓞 K) ∈ v.asIdeal}
  have hTf : T.Finite := hSf.union <|
    (Ideal.finite_factors (I := Ideal.span {(m : 𝓞 K)})
      (by simpa only [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using
        (Nat.cast_ne_zero.2 hm : (m : 𝓞 K) ≠ 0))).subset
      fun v hv ↦ Ideal.dvd_span_singleton.2 hv
  have := W.finite_unramifiedOutsideTorsionCohomology (τ := τ) hTf hm h
  exact Finite.of_injective _ (AddSubgroup.inclusion_injective
    (selmerGroup_le_unramifiedOutsideTorsionCohomology (S := T)
      (fun v hv ↦ hgood v fun hvS ↦ hv (Or.inl hvS)) fun v hv hvm ↦ hv (Or.inr hvm)))

end NumberField

end WeierstrassCurve
