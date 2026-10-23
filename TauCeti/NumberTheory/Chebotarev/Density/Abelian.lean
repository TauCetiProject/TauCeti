/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DirichletDensity
public import TauCeti.NumberTheory.Chebotarev.FrobeniusPrimeSet
import TauCeti.NumberTheory.Chebotarev.AuxiliaryPrime
import TauCeti.NumberTheory.Chebotarev.Crossing.CrossingConstant
import TauCeti.NumberTheory.Chebotarev.Crossing.TaggedFibres
import TauCeti.NumberTheory.Chebotarev.Density.Cyclotomic
import TauCeti.NumberTheory.Chebotarev.Density.FixedField
import TauCeti.NumberTheory.Chebotarev.TaggedFixedField

/-!
# Chebotarev density for abelian extensions

Let `L / K` be a finite Galois extension of number fields with abelian group `G`. For every
`σ ∈ G`, the primes of `𝓞 K` whose Frobenius in `L` is `σ` have Dirichlet density `1 / #G`.

## Main results

* `NumberField.Chebotarev.hasDirichletDensity_abelianFrobenius`: the Frobenius fibre of any
  element of an abelian Galois group `G` has Dirichlet density `1 / #G`.

## References

* R. Sharifi, *Algebraic Number Theory*, Theorem 7.2.2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, Section 13.
* The same Deuring crossing argument is formalized as `Chebotarev.chebotarev_abelian` in
  AINTLIB, <https://github.com/CBirkbeck/aintlib> (Apache-2.0), commit
  `8102fa09bbf570f3e991adfdb2d6d70b48cb5b5e`, file
  `projects/Chebotarev/CebotarevDensity/Abelian.lean`.
-/

open NumberField NumberField.Set Filter
open scoped NumberField Topology
open TauCeti.NumberField.Chebotarev

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

-- **One auxiliary prime.** In an abelian extension, the Frobenius fibre of `σ` has lower
-- Dirichlet density at least `(1 - 2 ^ (-r)) ^ #(orderOf σ).primeFactors / #G`, for every
-- `r ≥ 1`.
private theorem isLowerDirichletDensityBound_abelianFrobenius
    (hab : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) (σ : L ≃ₐ[K] L) {r : ℕ} (hr : 0 < r) :
    IsLowerDirichletDensityBound (frobeniusPrimeSet K L (ConjClasses.mk σ))
      ((1 - (2 : ℝ) ^ (-(r : ℤ))) ^ (orderOf σ).primeFactors.card /
        (Nat.card (L ≃ₐ[K] L) : ℝ)) := by
  set f := orderOf σ
  -- Cross with `M = L(μ_q)` for a prime `q` with `f ^ r ∣ q - 1` and `|disc L| < q`; then
  -- `Gal(M/K) ≃ Gal(L/K) × (ZMod q)ˣ`.
  obtain ⟨q, hq, hqN, -, hfq, -, -, -⟩ := exists_auxiliaryPrime K L (f ^ r) (discr L).natAbs
    (pow_ne_zero _ (orderOf_pos σ).ne')
  have : Fact q.Prime := ⟨hq⟩
  -- `q` exceeds `|disc L|`, so it is coprime to it.
  have hcop : (discr L).natAbs.Coprime q :=
    (Nat.coprime_of_lt_prime (Int.natAbs_ne_zero.mpr (discr_ne_zero L)) hqN hq).symm
  let M := CyclotomicField q L
  have hζ := IsCyclotomicExtension.zeta_spec q L M
  have : IsGalois K M := IsCyclotomicExtension.isGalois_of_isGalois_of_isCyclotomicExtension K L M q
  set e := IsCyclotomicExtension.galEquivProd K L M q hcop hζ
  have hcard : Nat.card (M ≃ₐ[K] M) = Nat.card (L ≃ₐ[K] L) * Nat.card (ZMod q)ˣ := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  have hcomm (ρ ρ' : M ≃ₐ[K] M) : ρ * ρ' = ρ' * ρ :=
    e.injective (by rw [map_mul, map_mul, Prod.mul_def, Prod.mul_def, hab, mul_comm (e ρ).2])
  -- Each tagged fibre has the density of one element of `Gal(M/K)`: for a tag `τ`, the field
  -- fixed by `(σ, τ)` has `M` as a `q`-th cyclotomic extension, so the cyclotomic density and
  -- the fixed-field contraction apply, and `(σ, τ)` is central, so its class is a singleton.
  have hdens (τ : (ZMod q)ˣ) (hτ : τ ∈ taggedElements f) :
      (frobeniusPrimeSet K M (ConjClasses.mk (e.symm (σ, τ)))).HasDirichletDensity
        (1 / ((Nat.card (L ≃ₐ[K] L) : ℝ) * Nat.card (ZMod q)ˣ)) := by
    have := TauCeti.fixedField_zpowers_isCyclotomicExtension K L M q hcop hζ σ τ
      (mem_taggedElements_iff.mp hτ)
    have h := hasDirichletDensity_frobeniusPrimeSet_of_fixedField _ _ ConjClasses.mem_carrier_mk <|
      AlgEquiv.card_algEquiv_fixedField_zpowers (e.symm (σ, τ)) ▸
        hasDirichletDensity_cyclotomicFrobenius _ M q (e.symm (σ, τ)).toFixedFieldAlgEquiv
    rwa [Nat.card_coe_set_eq, ConjClasses.ncard_carrier_mk_of_mem_center
      (Subgroup.mem_center_iff.mpr fun ρ ↦ hcomm ρ _), hcard, Nat.cast_one, Nat.cast_mul] at h
  -- Distinct tags give disjoint fibres, so the tagged fibres' densities add.
  have hunion := hasDirichletDensity_biUnion_finset hdens fun τ _ υ _ hτυ ↦ by
    simpa using disjoint_taggedFrobeniusPrimeSet K L M q hcop hζ σ σ hτυ
  refine (hunion.isLowerDirichletDensityBound.mono_set ?_).mono ?_
  · -- A tagged fibre restricts to the fibre of `σ`.
    refine Set.iUnion₂_subset fun τ _ ↦ ?_
    have h := frobeniusPrimeSet_subset_map_restrictNormalHom (M := L)
      (ConjClasses.mk (e.symm (σ, τ)))
    rwa [ConjClasses.map_mk, AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply,
      IsCyclotomicExtension.restrictNormal_galEquivProd_symm] at h
  · -- Their total density is the crossing constant, bounded below uniformly in `q`.
    have hf : f ^ r ∣ Nat.card (ZMod q)ˣ := by
      rwa [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hq]
    refine (le_crossingConstant K L f r hr hf).trans_eq ?_
    rw [crossingConstant_def, Finset.sum_const, nsmul_eq_mul, mul_one_div]

-- Letting the level of the auxiliary prime grow, the Frobenius fibre of every element of an
-- abelian Galois group has lower Dirichlet density at least `1 / #G`.
private theorem isLowerDirichletDensityBound_one_div_card_abelianFrobenius
    (hab : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) (σ : L ≃ₐ[K] L) : IsLowerDirichletDensityBound
      (frobeniusPrimeSet K L (ConjClasses.mk σ)) (1 / (Nat.card (L ≃ₐ[K] L) : ℝ)) := by
  -- The bound of one auxiliary prime tends to `1 / #G` as its level grows.
  have h2 : Tendsto (fun r : ℕ ↦ (2 : ℝ) ^ (-(r : ℤ))) atTop (𝓝 0) := by
    simpa [zpow_neg, zpow_natCast, inv_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
  have hlim := (((tendsto_const_nhds (x := (1 : ℝ))).sub h2).pow
    (orderOf σ).primeFactors.card).div_const (Nat.card (L ≃ₐ[K] L) : ℝ)
  rw [sub_zero, one_pow] at hlim
  refine isLowerDirichletDensityBound_of_forall_lt fun δ hδ ↦ ?_
  obtain ⟨r, hr, hδr⟩ := ((eventually_gt_atTop 0).and (hlim.eventually (lt_mem_nhds hδ))).exists
  exact (isLowerDirichletDensityBound_abelianFrobenius hab σ hr).mono hδr.le

public section

variable (K L) in
/-- **Chebotarev density for abelian extensions.** If `Gal(L/K)` is abelian, then for every
`σ ∈ Gal(L/K)` the primes of `𝓞 K` whose Frobenius in `L` is `σ` have Dirichlet density
`1 / #Gal(L/K)`. -/
theorem hasDirichletDensity_abelianFrobenius
    (hab : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) (σ : L ≃ₐ[K] L) :
    NumberField.Set.HasDirichletDensity (frobeniusPrimeSet K L (ConjClasses.mk σ))
      (1 / (Nat.card (L ≃ₐ[K] L) : ℝ)) := by
  -- In an abelian group distinct elements have distinct classes, hence disjoint fibres; the
  -- lower bounds `1 / #G` sum to `1` over the whole group, so each of them is the density.
  refine hasDirichletDensity_of_squeeze (s := Finset.univ)
    (f := fun ρ ↦ frobeniusPrimeSet K L (ConjClasses.mk ρ)) (d := fun _ ↦ _) (Finset.mem_univ σ)
    (fun ρ _ ρ' _ hρ ↦ disjoint_frobeniusPrimeSet fun h ↦ hρ ?_)
    (isUpperDirichletDensityBound_one _)
    (fun ρ _ ↦ isLowerDirichletDensityBound_one_div_card_abelianFrobenius hab ρ) ?_
  · obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp h)
    rw [← hc, hab c, mul_inv_cancel_right]
  · simp [Nat.card_eq_fintype_card]

end

end NumberField.Chebotarev
