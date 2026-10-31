/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.SupSeminorm

import Mathlib.RingTheory.Polynomial.RationalRoot
import TauCeti.Analysis.Normed.Unbundled.RootBound
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.RingTheory.Affinoid.MaximumModulus
import TauCeti.RingTheory.Affinoid.MinimalPolynomial
import TauCeti.RingTheory.Affinoid.NoetherNormalization
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniqueFactorization

/-!
# Integral equations attaining the spectral value

Let `B` be an affinoid algebra which is integral over an affinoid algebra `A`, over a complete
nonarchimedean field `K`. Every `f : B` satisfies a monic equation
`f ^ d + ∑_{i < d} aᵢ f ^ i = 0` with `aᵢ ∈ A` whose coefficients are bounded by the supremum
seminorm of `f`:

`|aᵢ|sup ≤ |f|sup ^ (d - i)` for every `i`.

Combined with the reverse inequality valid for every monic equation,
`TauCeti.IsAffinoidAlgebra.supSeminorm_le_iSup_coeff_rpow_of_eval_eq_zero`, such an equation
attains the spectral value: `|f|sup = max_{i < d} |aᵢ|sup ^ (1 / (d - i))`. No injectivity,
torsion-freeness or reducedness is assumed, and `A` need not be integrally closed, so the minimal
polynomial is in general not such an equation.

The equation is assembled from the minimal primes `𝔮` of `B`. Choose a Tate presentation
`π : K⟨X₁, …, Xₙ⟩ → A`. The image of `K⟨X₁, …, Xₙ⟩` in the affinoid domain `B ⧸ 𝔮` admits a
Noether normalisation `K⟨Y₁, …, Y_d⟩ → B ⧸ 𝔮` through a Gauss-norm-preserving map
`ι : K⟨Y₁, …, Y_d⟩ → K⟨X₁, …, Xₙ⟩` (`AlgHom.exists_norm_eq_finite_injective_comp`). The minimal
polynomial of the residue of `f` over this integrally closed Tate algebra has coefficients bounded
by `|f|sup` (`TauCeti.IsAffinoidAlgebra.supSeminorm_eq_iSup_minpoly_coeff_rpow`), and `π ∘ ι`
carries it to a monic polynomial over `A` with the same bounds, vanishing at `f` modulo `𝔮`.
The product over all minimal primes vanishes at `f` modulo the nilradical, so a power of it
vanishes at `f`, and the bounds pass to products and powers
(`Polynomial.apply_coeff_prod_le_pow`, `Polynomial.apply_coeff_pow_le_pow`).

## Main results

* `TauCeti.IsAffinoidAlgebra.exists_monic_aeval_eq_zero_supSeminorm_coeff_le`: for `B` integral
  over `A`, every `f : B` is a root of a monic polynomial over `A` with
  `|aᵢ|sup ≤ |f|sup ^ (d - i)`.
* `TauCeti.IsAffinoidAlgebra.exists_monic_aeval_eq_zero_supSeminorm_eq_iSup_coeff_rpow`: such an
  equation attains the spectral value, `|f|sup = max_{i < d} |aᵢ|sup ^ (1 / (d - i))`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.2.2,
  Proposition 4.
-/

public section

namespace TauCeti.IsAffinoidAlgebra

open Polynomial

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A] {B : Type*} [CommRing B] [Algebra K B]
  [Algebra A B] [IsScalarTower K A B]

local notation "Tate " σ:max => MvPowerSeries.IsRestricted.subring (R := K) (fun _ : σ ↦ 1)

/-- Modulo a prime `𝔮` of `B`, an element `f` is a root of a monic polynomial over `A` whose
coefficients satisfy `|aᵢ|sup ≤ |f|sup ^ (d - i)`. -/
private theorem exists_monic_aeval_mem_supSeminorm_coeff_le (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) [Algebra.IsIntegral A B] (𝔮 : Ideal B) [𝔮.IsPrime] (f : B) :
    ∃ p : A[X], p.Monic ∧ aeval f p ∈ 𝔮 ∧
      ∀ i, supSeminorm K (p.coeff i) ≤ supSeminorm K f ^ (p.natDegree - i) := by
  obtain ⟨n, π, hπ⟩ := (isAffinoidAlgebra_iff K A).mp hA
  let C := B ⧸ 𝔮
  have hC : IsAffinoidAlgebra K C := hB.quotient 𝔮
  have : Nontrivial A := (algebraMap A C).domain_nontrivial
  -- Normalise the image of `K⟨X₁, …, Xₙ⟩` in the domain `C` through a norm-preserving `ι`.
  let ψ : Tate (Fin n) →ₐ[K] C :=
    (Ideal.Quotient.mkₐ K 𝔮).comp ((IsScalarTower.toAlgHom K A B).comp π)
  obtain ⟨d, ι, hι, hinj, hfin⟩ :=
    ψ.rangeRestrict.exists_norm_eq_finite_injective_comp ψ.rangeRestrict_surjective
  let T := Tate (Fin d)
  let g : T →ₐ[K] C := ψ.comp ι
  let := g.toRingHom.toAlgebra
  have : IsScalarTower K T C := IsScalarTower.of_algebraMap_eq fun c ↦ (g.commutes c).symm
  have : FaithfulSMul T C := (faithfulSMul_iff_algebraMap_injective T C).mpr <| by
    -- The algebra map is `g`, which is `ψ.rangeRestrict.comp ι` followed by the inclusion.
    exact Subtype.val_injective.comp hinj
  -- `C` is integral over the image of `K⟨X₁, …, Xₙ⟩`, which is finite over `T`.
  have : Algebra.IsIntegral T C := by
    have hψ : ψ.toRingHom.IsIntegral :=
      .trans _ _ (.trans _ _ (RingHom.isIntegral_of_surjective _ hπ)
        (algebraMap_isIntegral_iff.mpr ‹_›))
        (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)
    have hval : ψ.range.val.toRingHom.IsIntegral :=
      RingHom.IsIntegral.tower_top ψ.rangeRestrict.toRingHom _ hψ
    -- The algebra map `g` is `ψ.rangeRestrict.comp ι` followed by the inclusion of the range.
    have h := RingHom.IsIntegral.trans (ψ.rangeRestrict.comp ι).toRingHom _
      (RingHom.Finite.to_isIntegral hfin) hval
    exact ⟨h⟩
  -- The minimal polynomial `p` of the residue `x` of `f` over `T` has bounded coefficients.
  set x : C := Ideal.Quotient.mk 𝔮 f
  set p := minpoly T x
  have hx := Algebra.IsIntegral.isIntegral (R := T) x
  have hp := minpoly.monic hx
  have hxf : supSeminorm K x ≤ supSeminorm K f :=
    hB.supSeminorm_map_le hC (Ideal.Quotient.mkₐ K 𝔮) f
  have hcoeff (i : ℕ) : ‖p.coeff i‖ ≤ supSeminorm K f ^ (p.natDegree - i) := by
    refine le_trans ?_ (pow_le_pow_left₀ (supSeminorm_nonneg x) hxf _)
    rcases lt_trichotomy i p.natDegree with hi | rfl | hi
    · rw [← MvPowerSeries.supSeminorm_eq_norm]
      refine (Real.rpow_one_div_natCast_sub_le_iff (supSeminorm_nonneg _)
        (supSeminorm_nonneg x) hi).mp ?_
      rw [hC.supSeminorm_eq_iSup_minpoly_coeff_rpow (A := T) x]
      exact le_ciSup (f := fun j : Fin p.natDegree ↦
        supSeminorm K (p.coeff j) ^ (1 / (p.natDegree - j : ℝ)))
        (Set.finite_range _).bddAbove ⟨i, hi⟩
    · rw [hp.coeff_natDegree, norm_one, Nat.sub_self, pow_zero]
    · rw [coeff_eq_zero_of_natDegree_lt hi, norm_zero]
      exact pow_nonneg (supSeminorm_nonneg x) _
  -- Carry `p` to `A` along `π ∘ ι`, which does not increase supremum seminorms.
  refine ⟨p.map (π.comp ι).toRingHom, hp.map _, ?_, fun i ↦ ?_⟩
  · -- Modulo `𝔮`, evaluating the image of `p` at `f` evaluates `p` at `x` along `T → C`.
    have hcomp : ((Ideal.Quotient.mk 𝔮).comp (algebraMap A B)).comp (π.comp ι).toRingHom =
        algebraMap T C := rfl
    rw [← Ideal.Quotient.eq_zero_iff_mem, aeval_def, hom_eval₂, eval₂_map, hcomp]
    exact minpoly.aeval T x
  · rw [coeff_map, hp.natDegree_map]
    calc supSeminorm K ((π.comp ι).toRingHom (p.coeff i))
        ≤ supSeminorm K (ι (p.coeff i)) :=
          isAffinoidAlgebra_tate.supSeminorm_map_le hA π (ι (p.coeff i))
      _ = ‖p.coeff i‖ := by rw [MvPowerSeries.supSeminorm_eq_norm, hι]
      _ ≤ supSeminorm K f ^ (p.natDegree - i) := hcoeff i

/-- **Integral equations bounded by the supremum seminorm.** Let `B` be an affinoid algebra
integral over an affinoid algebra `A`. Every `f : B` is a root of a monic polynomial
`p = X ^ d + ∑_{i < d} aᵢ X ^ i` over `A` with `|aᵢ|sup ≤ |f|sup ^ (d - i)` for every `i`. -/
theorem exists_monic_aeval_eq_zero_supSeminorm_coeff_le (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) [Algebra.IsIntegral A B] (f : B) :
    ∃ p : A[X], p.Monic ∧ aeval f p = 0 ∧
      ∀ i, supSeminorm K (p.coeff i) ≤ supSeminorm K f ^ (p.natDegree - i) := by
  classical
  have := hB.isNoetherianRing
  have : Finite (minimalPrimes B) := (minimalPrimes.finite_of_isNoetherianRing B).to_subtype
  let := Fintype.ofFinite (minimalPrimes B)
  -- One monic polynomial for each minimal prime, vanishing at `f` modulo that prime.
  choose q hqm hq hqc using fun 𝔮 : minimalPrimes B ↦
    have : 𝔮.1.IsPrime := Ideal.IsMinimalPrime.isPrime 𝔮.2
    exists_monic_aeval_mem_supSeminorm_coeff_le hA hB 𝔮.1 f
  -- Their product vanishes at `f` modulo every prime, hence up to a nilpotent.
  set Q := ∏ 𝔮, q 𝔮
  obtain ⟨N, hN⟩ : IsNilpotent (aeval f Q) := by
    refine nilpotent_iff_mem_prime.mpr fun J hJ ↦ ?_
    obtain ⟨𝔮, h𝔮, h𝔮J⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ J)
    rw [map_prod]
    exact h𝔮J (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ ⟨𝔮, h𝔮⟩))
      (hq ⟨𝔮, h𝔮⟩))
  have hQm : Q.Monic := monic_prod_of_monic _ _ fun 𝔮 _ ↦ hqm 𝔮
  -- The coefficient bounds pass to products and powers.
  have hf1 : hA.supRingSeminorm 1 ≤ 1 := by
    rcases subsingleton_or_nontrivial A with _ | _
    · simp [supSeminorm_eq_zero_of_subsingleton]
    · simp [supSeminorm_one]
  have hna : IsNonarchimedean hA.supRingSeminorm := by
    rw [coe_supRingSeminorm]
    exact hA.isNonarchimedean_supSeminorm
  have hQc (i : ℕ) : hA.supRingSeminorm (Q.coeff i) ≤ supSeminorm K f ^ (Q.natDegree - i) := by
    rw [natDegree_prod_of_monic _ _ fun 𝔮 _ ↦ hqm 𝔮]
    exact apply_coeff_prod_le_pow hf1 hna (supSeminorm_nonneg f) _ _
      (fun 𝔮 _ ↦ by simpa only [coe_supRingSeminorm] using hqc 𝔮) i
  refine ⟨Q ^ N, hQm.pow N, by rw [map_pow, hN], fun i ↦ ?_⟩
  rw [hQm.natDegree_pow]
  simpa only [coe_supRingSeminorm] using
    apply_coeff_pow_le_pow hf1 hna (supSeminorm_nonneg f) hQc N i

/-- **An integral equation attaining the spectral value.** Let `B` be an affinoid algebra
integral over an affinoid algebra `A`. Every `f : B` is a root of a monic polynomial
`p = X ^ d + ∑_{i < d} aᵢ X ^ i` over `A` with `|f|sup = max_{i < d} |aᵢ|sup ^ (1 / (d - i))`.
-/
theorem exists_monic_aeval_eq_zero_supSeminorm_eq_iSup_coeff_rpow (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) [Algebra.IsIntegral A B] (f : B) :
    ∃ p : A[X], p.Monic ∧ aeval f p = 0 ∧ supSeminorm K f =
      ⨆ i : Fin p.natDegree, supSeminorm K (p.coeff i) ^ (1 / (p.natDegree - i : ℝ)) := by
  obtain ⟨p, hp, hpf, hc⟩ := hA.exists_monic_aeval_eq_zero_supSeminorm_coeff_le hB f
  refine ⟨p, hp, hpf, le_antisymm ?_ (Real.iSup_le (fun i ↦
    (Real.rpow_one_div_natCast_sub_le_iff (supSeminorm_nonneg _) (supSeminorm_nonneg f)
      i.2).mpr (hc i)) (supSeminorm_nonneg f))⟩
  rcases subsingleton_or_nontrivial B with _ | _
  · rw [supSeminorm_eq_zero_of_subsingleton]
    exact Real.iSup_nonneg fun _ ↦ Real.rpow_nonneg (supSeminorm_nonneg _) _
  -- The reverse inequality holds for every monic equation, and `A → B` contracts `|·|sup`.
  have h := hB.supSeminorm_le_iSup_coeff_rpow_of_eval_eq_zero (hp.map (algebraMap A B))
    (f := f) (by rwa [eval_map_algebraMap])
  rw [hp.natDegree_map] at h
  refine h.trans (ciSup_mono (Set.finite_range _).bddAbove fun i ↦ ?_)
  rw [coeff_map]
  exact Real.rpow_le_rpow (supSeminorm_nonneg _)
    (hA.supSeminorm_map_le hB (IsScalarTower.toAlgHom K A B) _)
    (one_div_nonneg.mpr (sub_nonneg.mpr (mod_cast i.2.le)))

end TauCeti.IsAffinoidAlgebra
