/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RamificationInertia.Inertia
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Local Euler factors and Dedekind zeta coefficients from residue degrees

For a number field `K`, the local Euler product formula expresses the prime-power ideal counts
`normCoeff K 1 (p ^ k)` at a rational prime `p` in terms of the canonical local factors at the
primes of `𝓞 K` above `p`. Each such prime `P` has absolute norm `p ^ f_P`, where `f_P` is its
residue degree over `𝓞 ℚ`, so the multiset of residue degrees above `p` completely determines the
ideal counts at powers of `p` (`TauCeti.normCoeff_one_apply_prime_pow_eq_prod_ofPowerSeries`).

By multiplicativity of `normCoeff K 1`, two number fields with the same multiset of residue
degrees above every height-one prime of `𝓞 ℚ` have the same number of integral ideals of every
absolute norm (`TauCeti.dedekindZetaCoeff_eq_of_forall_map_inertiaDeg_eq`).

## Main results

* `TauCeti.normCoeff_one_apply_prime_pow_eq_prod_ofPowerSeries`: the ideal count at a rational
  prime power `p ^ k` is the coefficient of the product of `ofPowerSeries (p ^ d) (1 + X + ⋯)`
  over the multiset of residue degrees `d` above `p`.
* `TauCeti.dedekindZetaCoeff_eq_of_forall_map_inertiaDeg_eq`: equal residue-degree multisets above
  every rational prime imply equal Dedekind zeta coefficients.
-/

public section

open Ideal IsDedekindDomain NumberField
open scoped NumberField

namespace TauCeti

open scoped Classical in
/-- **The prime-power ideal count from residue degrees.** At a rational prime `v` of `𝓞 ℚ` with
absolute norm `p`, the value of `normCoeff K 1` at `p ^ k` equals the `p ^ k`-th coefficient of the
Dirichlet product of `ArithmeticFunction.ofPowerSeries (p ^ d) (PowerSeries.mk fun _ ↦ 1)` over
the multiset of residue degrees `d` of the primes of `𝓞 K` above `v`. -/
theorem normCoeff_one_apply_prime_pow_eq_prod_ofPowerSeries (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℕ) :
    normCoeff K (1 : IdealArithmeticFunction K) (Ideal.absNorm v.asIdeal ^ k) =
      (((Finset.univ : Finset (v.asIdeal.primesOver (𝓞 K))).val.map
          (fun P ↦ P.val.inertiaDeg (𝓞 ℚ))).map
        (fun d ↦ ArithmeticFunction.ofPowerSeries (Ideal.absNorm v.asIdeal ^ d)
          (PowerSeries.mk fun _ ↦ (1 : ℂ)))).prod (Ideal.absNorm v.asIdeal ^ k) := by
  have hp : (Ideal.absNorm v.asIdeal).Prime := by
    rw [Rat.HeightOneSpectrum.absNorm_asIdeal]
    exact Rat.HeightOneSpectrum.prime_natGenerator v
  -- Identify `v.asIdeal.primesOver (𝓞 K)` with the height-one primes above `v`.
  let e := HeightOneSpectrum.equivPrimesOver (𝓞 K) (p := v.asIdeal) v.ne_bot
  let toSpec : v.asIdeal.primesOver (𝓞 K) → HeightOneSpectrum (𝓞 K) := fun P ↦ (e.symm P).val
  have htoSpec_inj : Function.Injective toSpec := Subtype.val_injective.comp e.symm.injective
  have htoSpec_asIdeal : ∀ P, (toSpec P).asIdeal = P.val := fun P ↦ by
    rw [← HeightOneSpectrum.equivPrimesOver_apply (𝓞 K) (p := v.asIdeal) v.ne_bot (e.symm P)]
    exact congrArg Subtype.val (e.apply_symm_apply P)
  -- Every height-one prime of `𝓞 K` containing `N(v)` divides the lift of `v.asIdeal`.
  have hmem : ∀ Q : HeightOneSpectrum (𝓞 K),
      (Ideal.absNorm v.asIdeal : 𝓞 K) ∈ Q.asIdeal → Q ∈ Finset.univ.image toSpec := by
    intro Q hQ
    have hdvd : Q.asIdeal ∣ Ideal.map (algebraMap (𝓞 ℚ) (𝓞 K)) v.asIdeal := by
      rw [Ideal.dvd_iff_le, ← Rat.RingOfIntegers.ideal_span_absNorm_eq_self v.asIdeal,
        Ideal.map_span, Set.image_singleton, map_natCast, Ideal.span_singleton_le_iff_mem]
      exact hQ
    exact Finset.mem_image.mpr ⟨e ⟨Q, hdvd⟩, Finset.mem_univ _, by simp [toSpec]⟩
  -- Apply the local Euler product formula over `Finset.univ.image toSpec`.
  rw [IdealArithmeticFunction.normCoeff_apply_prime_pow_eq_prod_localArithmeticFactor
      IdealArithmeticFunction.isMultiplicative_one hp _ hmem k,
    Finset.prod_image (fun _ _ _ _ h ↦ htoSpec_inj h)]
  congr 1
  rw [Multiset.map_map, Function.comp_def, Finset.prod_eq_multiset_prod]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun P _ ↦ ?_)
  have := P.property.1
  have := P.property.2
  rw [IdealArithmeticFunction.localArithmeticFactor_def, htoSpec_asIdeal,
    ← Ideal.absNorm_pow_inertiaDeg v.asIdeal P.val]
  congr 1
  ext n
  simp

open scoped Classical in
/-- **Equal residue-degree multisets imply equal Dedekind zeta coefficients.** If two number fields
`K` and `L` have the same multiset of residue degrees above every height-one prime of `𝓞 ℚ`, then
they have the same number of integral ideals of every absolute norm. -/
theorem dedekindZetaCoeff_eq_of_forall_map_inertiaDeg_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    (h : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      (Finset.univ : Finset (v.asIdeal.primesOver (𝓞 K))).val.map
          (fun P ↦ P.val.inertiaDeg (𝓞 ℚ)) =
        (Finset.univ : Finset (v.asIdeal.primesOver (𝓞 L))).val.map
          (fun P ↦ P.val.inertiaDeg (𝓞 ℚ))) (n : ℕ) :
    dedekindZetaCoeff K n = dedekindZetaCoeff L n := by
  by_cases hn : n = 0
  · subst hn
    simp
  have hfun : normCoeff K (1 : IdealArithmeticFunction K) =
      normCoeff L (1 : IdealArithmeticFunction L) := by
    rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
      IdealArithmeticFunction.isMultiplicative_one.normCoeff _
      IdealArithmeticFunction.isMultiplicative_one.normCoeff]
    intro p k hp
    obtain ⟨v, hv⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq hp
    rw [← hv, normCoeff_one_apply_prime_pow_eq_prod_ofPowerSeries,
      normCoeff_one_apply_prime_pow_eq_prod_ofPowerSeries, h v]
  have hn_eq := congrArg (fun f : ArithmeticFunction ℂ ↦ f n) hfun
  simp only [normCoeff_one_apply, hn, ite_false] at hn_eq
  exact Nat.cast_injective hn_eq

end TauCeti
