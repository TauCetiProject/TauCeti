/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.FiniteComponent
public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Shift
public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Weight
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Primitive
import TauCeti.NumberTheory.LocalField.Uniformizer
import TauCeti.NumberTheory.NumberField.FinitePlace.Basic
import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Ideal
import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Conductor
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# The primitive unitary ideal weight of a Hecke character

Every Hecke character `χ` of a number field `K` decomposes as `χ = χ_u · ‖·‖ ^ σ` into its unitary
part `χ_u` and a real power of the idele class norm
(`HeckeCharacter.unitaryPart_mul_normPow_shift`). Since the norm character `‖·‖ ^ s` is trivial on
the local integral units `𝓞_vˣ` at every finite place `v`
(`HeckeCharacter.conductorExponent_normPow`), twisting by it does not alter local ramification:
`χ_u` and `χ` have the same conductor exponents and the same finite conductor
(`HeckeCharacter.finiteConductor_unitaryPart`).

Evaluating the canonical ideal character of `χ_u` (`HeckeCharacter.idealCharacter`) on the integral
ideals prime to `χ.finiteConductor` and extending by zero on all ideals meeting `χ.finiteConductor`
produces a completely multiplicative unitary ideal weight `HeckeCharacter.unitaryIdealWeight`. Its
bad primes are precisely the prime divisors of `χ.finiteConductor`, and at every unramified prime
`v ∤ χ.finiteConductor` its value is the local component of `χ_u` at any uniformizer of `K_v`.

For a character factoring through a ray class group at a modulus `𝔪`, the ray-class ideal weight
at `𝔪` (`HeckeCharacter.toUnitaryIdealWeightAt`) is obtained from `χ.unitaryIdealWeight` by
restricting away from the primes of `𝔪`; when the ray class character is primitive, the two weights
coincide on the nose.

## Main definitions

* `TauCeti.GlobalNumberFields.HeckeCharacter.unitaryIdealWeight`: the canonical unitary ideal
  weight of `χ.unitaryPart` away from `χ.finiteConductor`.

## Main results

* `TauCeti.GlobalNumberFields.HeckeCharacter.conductorExponent_normPow` and
  `TauCeti.GlobalNumberFields.HeckeCharacter.finiteConductor_normPow`: norm-power characters are
  unramified at every finite place.
* `TauCeti.GlobalNumberFields.HeckeCharacter.conductorExponent_unitaryPart` and
  `TauCeti.GlobalNumberFields.HeckeCharacter.finiteConductor_unitaryPart`: passing to the unitary
  part preserves every finite conductor exponent and the finite conductor.
* `TauCeti.GlobalNumberFields.HeckeCharacter.unitaryIdealWeight_apply_prime`: at a prime outside
  the finite conductor, the unitary ideal weight equals the local component of `χ.unitaryPart` on
  any uniformizer.
* `TauCeti.GlobalNumberFields.HeckeCharacter.toUnitaryIdealWeightAt_eq_restrictAway`:
  the weight of a finite-order character at a ray modulus `𝔪` is the restriction of
  `unitaryIdealWeight` away from `𝔪.support`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6.
* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels and
  A. Fröhlich, eds., *Algebraic Number Theory*, §3.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField NNReal

namespace TauCeti.GlobalNumberFields.HeckeCharacter

variable {K : Type*} [Field K] [NumberField K]

/-! ### Finite conductor of norm powers and of the unitary part -/

/-- At a finite place `v`, a local unit `u` of `v`-adic valuation `1` has idele norm `1`, so every
norm character `‖·‖ ^ s` is trivial on `u`. -/
theorem finiteComponent_normPow_of_valued_eq_one (s : ℂ) (v : HeightOneSpectrum (𝓞 K))
    {u : (v.adicCompletion K)ˣ} (hu : Valued.v (u : v.adicCompletion K) = 1) :
    (normPow K s).finiteComponent v u = 1 := by
  apply Units.ext
  rw [finiteComponent_apply, IdeleClassGroup.ofAdicCompletion_apply, normPow_apply,
    ideleClassNorm_mk, coe_ideleNorm_ofAdicCompletion,
    FinitePlace.norm_adicCompletion_eq_absNorm_zpow v u.ne_zero, hu, WithZero.log_one, zpow_zero,
    Complex.ofReal_one, Complex.one_cpow, Units.val_one]

/-- **Every norm-power Hecke character is unramified at every finite place.** -/
@[simp]
theorem conductorExponent_normPow (s : ℂ) (v : HeightOneSpectrum (𝓞 K)) :
    (normPow K s).conductorExponent v = 0 :=
  Nat.eq_zero_of_le_zero <| ((normPow K s).conductorExponent_le_iff v 0).mpr fun _ hu ↦
    finiteComponent_normPow_of_valued_eq_one s v
      ((HeightOneSpectrum.mem_unitFiltration_zero_adicCompletion_iff v).mp hu)

/-- **Every norm-power Hecke character has trivial finite conductor.** -/
@[simp]
theorem finiteConductor_normPow (s : ℂ) : (normPow K s).finiteConductor = ⊤ :=
  (finiteConductor_eq_top_iff _).mpr (conductorExponent_normPow s)

/-- **Passing to the unitary part preserves every finite conductor exponent**, since `χ` and
`χ.unitaryPart` differ by a power of the idele class norm. -/
@[simp]
theorem conductorExponent_unitaryPart (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    χ.unitaryPart.conductorExponent v = χ.conductorExponent v := by
  refine le_antisymm ?_ ?_
  · calc χ.unitaryPart.conductorExponent v
      _ ≤ max (χ.conductorExponent v) ((normPow K (-χ.shift)).conductorExponent v) := by
          rw [unitaryPart_def]
          exact conductorExponent_mul_le _ _ v
      _ = χ.conductorExponent v := by simp
  · calc χ.conductorExponent v
      _ = (χ.unitaryPart * normPow K χ.shift).conductorExponent v := by
          rw [unitaryPart_mul_normPow_shift]
      _ ≤ max (χ.unitaryPart.conductorExponent v) ((normPow K χ.shift).conductorExponent v) :=
          conductorExponent_mul_le _ _ v
      _ = χ.unitaryPart.conductorExponent v := by simp

/-- **Passing to the unitary part preserves the finite conductor.** -/
@[simp]
theorem finiteConductor_unitaryPart (χ : HeckeCharacter K) :
    χ.unitaryPart.finiteConductor = χ.finiteConductor := by
  simp [finiteConductor_def]

/-! ### The canonical unitary ideal weight -/

/-- The restriction of `χ.unitaryPart.idealCharacter` to integral ideals prime to the finite
conductor of `χ.unitaryPart`. -/
private def unitaryOnIntegralIdeals (χ : HeckeCharacter K) :
    integralIdealsPrimeTo ⟨χ.unitaryPart.finiteConductor, χ.unitaryPart.finiteConductor_ne_bot, ∅⟩
      →* ℂˣ :=
  χ.unitaryPart.idealCharacter.comp (NumberFieldArithmetic.integralIdealsAwayHom K _)

/-- The underlying completely multiplicative ideal weight of `χ.unitaryPart`, extended by zero at
the ideals not prime to `χ.finiteConductor`. -/
private def toMultiplicativeIdealWeight (χ : HeckeCharacter K) : MultiplicativeIdealWeight K where
  toMonoidWithZeroHom :=
    let 𝔣 : Modulus K := ⟨χ.unitaryPart.finiteConductor, χ.unitaryPart.finiteConductor_ne_bot, ∅⟩
    { toFun I :=
        open Classical in
        if h : Ideal.IsPrimeTo I 𝔣.support then
          (χ.unitaryOnIntegralIdeals
            ⟨I, NumberFieldArithmetic.mem_integralIdealsAway_iff.mpr
              (Ideal.isPrimeTo_iff.mp h)⟩ : ℂ)
        else 0
      map_zero' := by simp
      map_one' := by
        classical
        simp only [Ideal.one_eq_top, Ideal.isPrimeTo_top, dite_true]
        have htop : (⟨⊤, NumberFieldArithmetic.mem_integralIdealsAway_iff.mpr
            (Ideal.isPrimeTo_iff.mp Ideal.isPrimeTo_top)⟩ : integralIdealsPrimeTo 𝔣) = 1 :=
          Subtype.ext (by simp [Ideal.one_eq_top])
        rw [htop, map_one, Units.val_one]
      map_mul' I J := by
        classical
        by_cases hI : Ideal.IsPrimeTo I 𝔣.support <;>
          by_cases hJ : Ideal.IsPrimeTo J 𝔣.support
        · have hIJ : Ideal.IsPrimeTo (I * J) 𝔣.support :=
            Ideal.isPrimeTo_mul_iff.mpr ⟨hI, hJ⟩
          simp only [hI, hJ, hIJ, dite_true]
          exact_mod_cast map_mul χ.unitaryOnIntegralIdeals
            ⟨I, NumberFieldArithmetic.mem_integralIdealsAway_iff.mpr
              (Ideal.isPrimeTo_iff.mp hI)⟩
            ⟨J, NumberFieldArithmetic.mem_integralIdealsAway_iff.mpr
              (Ideal.isPrimeTo_iff.mp hJ)⟩
        · have hIJ : ¬ Ideal.IsPrimeTo (I * J) 𝔣.support :=
            fun h ↦ hJ (Ideal.isPrimeTo_mul_iff.mp h).2
          simp [hIJ, hJ]
        · have hIJ : ¬ Ideal.IsPrimeTo (I * J) 𝔣.support :=
            fun h ↦ hI (Ideal.isPrimeTo_mul_iff.mp h).1
          simp [hIJ, hI]
        · have hIJ : ¬ Ideal.IsPrimeTo (I * J) 𝔣.support :=
            fun h ↦ hI (Ideal.isPrimeTo_mul_iff.mp h).1
          simp [hIJ, hI] }
  finite_setOf_apply_eq_zero := by
    let 𝔣 : Modulus K := ⟨χ.unitaryPart.finiteConductor, χ.unitaryPart.finiteConductor_ne_bot, ∅⟩
    convert 𝔣.support.finite_toSet using 1
    ext 𝔭
    classical
    simp only [Set.mem_ofPred_eq, Finset.mem_coe]
    -- Expose the `dite` body of the `MonoidWithZeroHom` to split on primality to the support.
    change (if h : Ideal.IsPrimeTo 𝔭.asIdeal 𝔣.support then _ else 0) = 0 ↔ 𝔭 ∈ 𝔣.support
    by_cases h : 𝔭 ∈ 𝔣.support
    · have hbad : ¬ Ideal.IsPrimeTo 𝔭.asIdeal 𝔣.support :=
        fun hg ↦ (Ideal.isPrimeTo_asIdeal_iff.mp hg) (by simpa using h)
      simp [h, hbad]
    · have hgood : Ideal.IsPrimeTo 𝔭.asIdeal 𝔣.support :=
        Ideal.isPrimeTo_asIdeal_iff.mpr h
      simp [h, hgood]

private theorem toMultiplicativeIdealWeight_apply_of_dvd (χ : HeckeCharacter K)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ χ.finiteConductor) :
    χ.toMultiplicativeIdealWeight v.asIdeal = 0 := by
  classical
  let 𝔣 : Modulus K := ⟨χ.unitaryPart.finiteConductor, χ.unitaryPart.finiteConductor_ne_bot, ∅⟩
  have hmem : v ∈ 𝔣.support := (𝔣.mem_support_iff v).mpr (by simpa [𝔣] using hv)
  have hbad : ¬ Ideal.IsPrimeTo v.asIdeal 𝔣.support :=
    fun hg ↦ (Ideal.isPrimeTo_asIdeal_iff.mp hg) (by simpa using hmem)
  -- Expose the `dite` body at `v.asIdeal` and discharge the bad-prime branch.
  change (if h : Ideal.IsPrimeTo v.asIdeal 𝔣.support then _ else 0) = 0
  simp [hbad]

private theorem toMultiplicativeIdealWeight_apply_prime (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ χ.finiteConductor)
    (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = WithZero.exp (-1)) :
    χ.toMultiplicativeIdealWeight v.asIdeal = χ.unitaryPart.finiteComponent v u := by
  classical
  let 𝔣 : Modulus K := ⟨χ.unitaryPart.finiteConductor, χ.unitaryPart.finiteConductor_ne_bot, ∅⟩
  have hv' : v ∉ 𝔣.support := (𝔣.mem_support_iff v).not.mpr (by simpa [𝔣] using hv)
  have hgood : Ideal.IsPrimeTo v.asIdeal 𝔣.support := Ideal.isPrimeTo_asIdeal_iff.mpr hv'
  -- Expose the `dite` body at `v.asIdeal` to evaluate `idealCharacter` on the uniformizer `u`.
  have hval : χ.toMultiplicativeIdealWeight v.asIdeal =
      (χ.unitaryOnIntegralIdeals ⟨v.asIdeal,
        NumberFieldArithmetic.mem_integralIdealsAway_iff.mpr (Ideal.isPrimeTo_iff.mp hgood)⟩ :
          ℂ) := by
    change (if h : Ideal.IsPrimeTo v.asIdeal 𝔣.support then _ else 0) = _
    simp [hgood]
  rw [hval, unitaryOnIntegralIdeals, MonoidHom.comp_apply,
    χ.unitaryPart.idealCharacter_apply_prime _ v
      (NumberFieldArithmetic.coe_integralIdealsAwayHom _ _) u hu]

/-- **The primitive unitary ideal weight of a Hecke character** `χ`: the completely multiplicative
unitary weight of `χ.unitaryPart`, extended by zero at the ideals not prime to `χ.finiteConductor`.
At every prime `v ∤ χ.finiteConductor`, its value is the local component of `χ.unitaryPart` at any
uniformizer of `K_v` (`unitaryIdealWeight_apply_prime`). -/
def unitaryIdealWeight (χ : HeckeCharacter K) : TauCeti.UnitaryIdealWeight K :=
  ⟨χ.toMultiplicativeIdealWeight, fun 𝔭 h𝔭 ↦ by
    have hv : ¬ 𝔭.asIdeal ∣ χ.finiteConductor := fun hdvd ↦ h𝔭 <| by
      rw [MultiplicativeIdealWeight.mem_badPrimes]
      exact toMultiplicativeIdealWeight_apply_of_dvd χ hdvd
    have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient 𝔭.ne_bot
    obtain ⟨u, hu⟩ := TauCeti.exists_isUniformizer (𝔭.adicCompletion K)
    rw [toMultiplicativeIdealWeight_apply_prime χ 𝔭 hv u
      (𝔭.isUniformizer_iff_valued_eq_exp_neg_one.mp hu), finiteComponent_apply]
    exact χ.norm_unitaryPart _⟩

/-- **At a prime outside the finite conductor, the unitary ideal weight evaluates the local
component of `χ.unitaryPart` on any uniformizer.** -/
theorem unitaryIdealWeight_apply_prime (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ v.asIdeal ∣ χ.finiteConductor) (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = WithZero.exp (-1)) :
    χ.unitaryIdealWeight.1 v.asIdeal = χ.unitaryPart.finiteComponent v u :=
  toMultiplicativeIdealWeight_apply_prime χ v hv u hu

/-- **A prime is bad for `χ.unitaryIdealWeight` exactly when it divides `χ.finiteConductor`.** -/
theorem mem_badPrimes_unitaryIdealWeight_iff (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ χ.unitaryIdealWeight.1.badPrimes ↔ v.asIdeal ∣ χ.finiteConductor := by
  refine ⟨fun h ↦ ?_, fun hv ↦ ?_⟩
  · by_contra hv
    have : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    obtain ⟨u, hu⟩ := TauCeti.exists_isUniformizer (v.adicCompletion K)
    rw [MultiplicativeIdealWeight.mem_badPrimes, unitaryIdealWeight_apply_prime χ v hv u
      (v.isUniformizer_iff_valued_eq_exp_neg_one.mp hu)] at h
    exact (χ.unitaryPart.finiteComponent v u).ne_zero h
  · rw [MultiplicativeIdealWeight.mem_badPrimes]
    exact toMultiplicativeIdealWeight_apply_of_dvd χ hv

/-- The unitary ideal weight vanishes at every prime dividing `χ.finiteConductor`. -/
theorem unitaryIdealWeight_apply_of_dvd (χ : HeckeCharacter K) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v.asIdeal ∣ χ.finiteConductor) :
    χ.unitaryIdealWeight.1 v.asIdeal = 0 :=
  toMultiplicativeIdealWeight_apply_of_dvd χ hv

/-- The unitary ideal weight vanishes on every ideal not prime to the prime divisors of
`χ.finiteConductor`. -/
theorem unitaryIdealWeight_apply_of_not_isPrimeTo (χ : HeckeCharacter K) {I : Ideal (𝓞 K)}
    (hI : ¬ Ideal.IsPrimeTo I {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ χ.finiteConductor}) :
    χ.unitaryIdealWeight.1 I = 0 := by
  refine (χ.unitaryIdealWeight.1.apply_eq_zero_iff_not_isGood I).mpr fun hg ↦ hI ?_
  convert hg using 1
  ext v
  exact (χ.mem_badPrimes_unitaryIdealWeight_iff v).symm

/-- The trivial Hecke character has the trivial unitary ideal weight. -/
@[simp]
theorem unitaryIdealWeight_one : (1 : HeckeCharacter K).unitaryIdealWeight = 1 := by
  refine Subtype.ext (MultiplicativeIdealWeight.ext_heightOneSpectrum fun v ↦ ?_)
  have hv : ¬ v.asIdeal ∣ (1 : HeckeCharacter K).finiteConductor := by
    rw [finiteConductor_one]
    exact fun h ↦ v.isPrime.ne_top (top_le_iff.mp (Ideal.dvd_iff_le.mp h))
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  obtain ⟨u, hu⟩ := TauCeti.exists_isUniformizer (v.adicCompletion K)
  rw [unitaryIdealWeight_apply_prime 1 v hv u (v.isUniformizer_iff_valued_eq_exp_neg_one.mp hu)]
  simp [MultiplicativeIdealWeight.one_apply, v.ne_bot]

/-- Passing to the unitary part leaves `unitaryIdealWeight` unchanged. -/
@[simp]
theorem unitaryIdealWeight_unitaryPart (χ : HeckeCharacter K) :
    χ.unitaryPart.unitaryIdealWeight = χ.unitaryIdealWeight := by
  refine Subtype.ext (MultiplicativeIdealWeight.ext_heightOneSpectrum fun v ↦ ?_)
  by_cases hv : v.asIdeal ∣ χ.finiteConductor
  · rw [unitaryIdealWeight_apply_of_dvd _ (by rwa [finiteConductor_unitaryPart]),
      unitaryIdealWeight_apply_of_dvd _ hv]
  · have : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    obtain ⟨u, hu⟩ := TauCeti.exists_isUniformizer (v.adicCompletion K)
    have hu' := v.isUniformizer_iff_valued_eq_exp_neg_one.mp hu
    rw [unitaryIdealWeight_apply_prime _ v (by rwa [finiteConductor_unitaryPart]) u hu',
      unitaryIdealWeight_apply_prime _ v hv u hu', unitaryPart_unitaryPart]

/-- Every real norm-power Hecke character `‖·‖ ^ σ` has trivial unitary part. -/
@[simp]
theorem unitaryPart_normPow_ofReal (σ : ℝ) : (normPow K σ).unitaryPart = 1 := by
  have h := unitaryPart_mul_normPow (K := K) (ψ := 1) shift_one σ
  rwa [one_mul (normPow K σ)] at h

/-- Every real norm-power Hecke character `‖·‖ ^ σ` has unitary ideal weight `1`, as its unitary
part is `1`. -/
@[simp]
theorem unitaryIdealWeight_normPow_ofReal (σ : ℝ) :
    (normPow K σ).unitaryIdealWeight = 1 := by
  rw [← unitaryIdealWeight_unitaryPart, unitaryPart_normPow_ofReal, unitaryIdealWeight_one]

/-- Inverting a Hecke character conjugates its unitary ideal weight. -/
@[simp]
theorem unitaryIdealWeight_inv (χ : HeckeCharacter K) :
    χ⁻¹.unitaryIdealWeight = χ.unitaryIdealWeight.conj := by
  refine Subtype.ext (MultiplicativeIdealWeight.ext_heightOneSpectrum fun v ↦ ?_)
  by_cases hv : v.asIdeal ∣ χ.finiteConductor
  · rw [unitaryIdealWeight_apply_of_dvd _ (by rwa [finiteConductor_inv]),
      UnitaryIdealWeight.val_conj, MultiplicativeIdealWeight.conj_apply,
      unitaryIdealWeight_apply_of_dvd _ hv, map_zero]
  · have : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    obtain ⟨u, hu⟩ := TauCeti.exists_isUniformizer (v.adicCompletion K)
    have hu' := v.isUniformizer_iff_valued_eq_exp_neg_one.mp hu
    rw [unitaryIdealWeight_apply_prime _ v (by rwa [finiteConductor_inv]) u hu',
      UnitaryIdealWeight.val_conj, MultiplicativeIdealWeight.conj_apply,
      unitaryIdealWeight_apply_prime _ v hv u hu', unitaryPart_inv, finiteComponent_inv,
      ← zpow_neg_one, ContinuousMonoidHom.zpow_apply, zpow_neg_one, Units.val_inv_eq_inv_val,
      finiteComponent_apply]
    exact Complex.inv_eq_conj
      (χ.norm_unitaryPart (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u))

/-! ### Comparison with ray-class ideal weights -/

/-- **For a ray class character `η` of `𝔪`, its ray-class ideal weight is the restriction away from
`𝔪.support` of `(ofRayClassCharacter 𝔪 η).unitaryIdealWeight`.** -/
theorem _root_.TauCeti.GlobalNumberFields.RayClassCharacter.toUnitaryIdealWeight_eq_restrictAway
    {𝔪 : Modulus K} (η : RayClassCharacter 𝔪) :
    η.toUnitaryIdealWeight =
      (ofRayClassCharacter 𝔪 η).unitaryIdealWeight.restrictAway
        𝔪.support 𝔪.support.finite_toSet := by
  classical
  refine Subtype.ext (MultiplicativeIdealWeight.ext_heightOneSpectrum fun v ↦ ?_)
  by_cases hv : v ∈ 𝔪.support
  · have hbad : ¬ Ideal.IsPrimeTo v.asIdeal 𝔪.support :=
      fun hg ↦ (Ideal.isPrimeTo_asIdeal_iff.mp hg) (by simpa using hv)
    rw [RayClassCharacter.val_toUnitaryIdealWeight,
      RayClassCharacter.toMultiplicativeIdealWeight_apply_of_not_isPrimeTo η hbad,
      UnitaryIdealWeight.val_restrictAway, MultiplicativeIdealWeight.restrictAway_apply]
    simp [hbad]
  · have hgood : Ideal.IsPrimeTo v.asIdeal 𝔪.support := Ideal.isPrimeTo_asIdeal_iff.mpr hv
    have hndvd : ¬ v.asIdeal ∣ (ofRayClassCharacter 𝔪 η).finiteConductor := by
      intro hdvd
      have hexp := ((ofRayClassCharacter 𝔪 η).dvd_finiteConductor_iff v).mp hdvd
      have hle := conductorExponent_le_exponent_of_mem_range ⟨η, rfl⟩ v
      have h0 : 𝔪.exponent v = 0 := by
        rw [← not_ne_iff]
        exact fun hne ↦ hv ((𝔪.mem_support_iff_exponent_ne_zero v).mpr hne)
      exact hexp (Nat.eq_zero_of_le_zero (hle.trans_eq h0))
    have : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    obtain ⟨u, hu⟩ := TauCeti.exists_isUniformizer (v.adicCompletion K)
    rw [UnitaryIdealWeight.val_restrictAway, MultiplicativeIdealWeight.restrictAway_apply,
      ite_eq_left_iff.mpr fun h ↦ (h hgood).elim,
      unitaryIdealWeight_apply_prime _ v hndvd u (v.isUniformizer_iff_valued_eq_exp_neg_one.mp hu),
      (unitaryPart_eq_self_iff _).mpr (shift_ofRayClassCharacter η),
      finiteComponent_ofRayClassCharacter_of_isUniformizer η hv hu]
    simp [hgood]

/-- **For a Hecke character factoring through `RayClassGroup 𝔪`, its weight at `𝔪` is the
restriction of `χ.unitaryIdealWeight` away from `𝔪.support`.** -/
theorem toUnitaryIdealWeightAt_eq_restrictAway {𝔪 : Modulus K}
    (χ : HeckeCharacter K) (hχ : χ ∈ (ofRayClassCharacter 𝔪).range) :
    χ.toUnitaryIdealWeightAt 𝔪 hχ =
      χ.unitaryIdealWeight.restrictAway 𝔪.support 𝔪.support.finite_toSet := by
  have h := RayClassCharacter.toUnitaryIdealWeight_eq_restrictAway (χ.rayClassCharacterAt 𝔪 hχ)
  rw [ofRayClassCharacter_rayClassCharacterAt] at h
  exact Subtype.ext ((val_toUnitaryIdealWeightAt χ 𝔪 hχ).trans
    ((RayClassCharacter.val_toUnitaryIdealWeight _).symm.trans (congrArg Subtype.val h)))

/-- **For a primitive ray class character `η`, `(ofRayClassCharacter 𝔪 η).unitaryIdealWeight`
agrees with `η.toUnitaryIdealWeight` on the nose.** -/
@[simp]
theorem unitaryIdealWeight_ofRayClassCharacter_of_isPrimitive {𝔪 : Modulus K}
    {η : RayClassCharacter 𝔪} (hη : η.IsPrimitive) :
    (ofRayClassCharacter 𝔪 η).unitaryIdealWeight = η.toUnitaryIdealWeight := by
  classical
  rw [RayClassCharacter.toUnitaryIdealWeight_eq_restrictAway]
  refine Subtype.ext (MultiplicativeIdealWeight.ext_heightOneSpectrum fun v ↦ ?_)
  rw [UnitaryIdealWeight.val_restrictAway, MultiplicativeIdealWeight.restrictAway_apply]
  by_cases hv : Ideal.IsPrimeTo v.asIdeal 𝔪.support
  · simp [hv]
  · simp only [hv, ite_false]
    have hmem : v ∈ 𝔪.support := by
      by_contra hnot
      exact hv (Ideal.isPrimeTo_asIdeal_iff.mpr hnot)
    have hcond : 𝔪.finitePart = (ofRayClassCharacter 𝔪 η).finiteConductor := by
      have hm : η.conductor = 𝔪 := (RayClassCharacter.isPrimitive_iff_conductor_eq η).mp hη
      calc 𝔪.finitePart
        _ = η.conductor.finitePart := congrArg Modulus.finitePart hm.symm
        _ = ((ofRayClassCharacter 𝔪 η).conductor
              (isFiniteOrder_ofRayClassCharacter η)).finitePart :=
            congrArg Modulus.finitePart
              (conductor_ofRayClassCharacter η (isFiniteOrder_ofRayClassCharacter η)).symm
        _ = (ofRayClassCharacter 𝔪 η).finiteConductor := finitePart_conductor _
    exact unitaryIdealWeight_apply_of_dvd _ (hcond ▸ (𝔪.mem_support_iff v).mp hmem)

end TauCeti.GlobalNumberFields.HeckeCharacter
