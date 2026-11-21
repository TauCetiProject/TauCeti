/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import TauCeti.RingTheory.DedekindDomain.SInteger.Congruence

import TauCeti.NumberTheory.NumberField.Global.Approximation.Weak
import TauCeti.RingTheory.Ideal.Quotient.DedekindDomain

/-!
# Reduction modulo the finite part of a modulus

For a modulus `𝔪` of a number field `K`, this file constructs the reduction homomorphism from
the elements of `Kˣ` that are units at the primes dividing `𝔪.finitePart` to the units of
`𝓞 K ⧸ 𝔪.finitePart`.

The generic ring map `Ideal.sIntegerToQuotient` supplies the construction. An element `x` in
`primeToSubgroup 𝔪` can be written as `x = a / b` with the denominator
congruent to one modulo the finite part. The class of `a` modulo `𝔪.finitePart` is independent
of this presentation and defines `residueHom 𝔪`. Its kernel records exactly the finite-place
conditions in `IsCongrOne`, and every residue unit is attained: a nonzero integral representative
of a unit class is already prime to the finite part, so it is itself a field unit reducing to that
class.

## Main definitions

* `TauCeti.GlobalNumberFields.residue`: the residue-ring-valued reduction homomorphism.
* `TauCeti.GlobalNumberFields.residueHom`: its residue-unit-valued form.
* `TauCeti.GlobalNumberFields.finiteUnitsMap`: the transition map on residue units when the
  modulus grows.

## Main results

* `Ideal.exists_algebraMap_eq_mul_and_sub_one_mem_of_valuation_le_one`: a locally integral element
  has a denominator congruent to one modulo an ideal, over an arbitrary Dedekind domain.
* `TauCeti.GlobalNumberFields.residue_eq_one_iff`: reduction to one is equivalent to the
  finite-place conditions in `IsCongrOne`.
* `TauCeti.GlobalNumberFields.residueHom_eq_one_of_mem_congruenceSubgroup`: an element congruent to
  one maps to one under reduction.
* `TauCeti.GlobalNumberFields.isCongrOne_iff_residueHom_eq_one_of_finitePart_eq`: for two moduli
  with the same finite part, congruence to one modulo one of them is reduction to one modulo the
  other together with positivity at its real places.
* `IsCongrOne.exists_sub_one_mem_and_ne_zero_and_isTotallyPositive_and_algebraMap_eq_mul`:
  an element congruent to one is a quotient of two algebraic integers congruent to one, the
  denominator nonzero and totally positive.
* `TauCeti.GlobalNumberFields.residueHom_surjective`: every residue unit modulo the finite part is
  the reduction of an element of `Kˣ` that is a unit at that finite part.
* `TauCeti.GlobalNumberFields.finiteUnitsMap_refl` and
  `TauCeti.GlobalNumberFields.finiteUnitsMap_comp_finiteUnitsMap`: the transition maps are
  functorial in finite-part divisibility.
* `TauCeti.GlobalNumberFields.finiteUnitsMap_residueHom`: reduction commutes with changing the
  modulus.
* `TauCeti.GlobalNumberFields.finiteUnitsMap_surjective`: every residue unit lifts to a larger
  finite modulus.
* `TauCeti.GlobalNumberFields.exists_primeToSubgroup_div_eq`: every fraction prime to `𝔪` is a
  quotient of two algebraic integers prime to `𝔪`.
* `TauCeti.GlobalNumberFields.exists_primeToSubgroup_approx_localUnit`: weak approximation in
  `primeToSubgroup 𝔪` for a local unit at a place of `𝔪`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-! ### Reduction modulo the finite part -/

/-- **The reduction of an element that is a unit at the finite part of `𝔪`**: the class modulo
`𝔪.finitePart` of a numerator in any presentation `x = a / b` with `b ≡ 1 mod 𝔪.finitePart`.  The
class does not depend on the presentation (`residue_eq`). -/
noncomputable def residue (𝔪 : Modulus K) : primeToSubgroup 𝔪 →* 𝓞 K ⧸ 𝔪.finitePart where
  toFun x := 𝔪.finitePart.sIntegerToQuotient (K := K)
    ⟨((x : Kˣ) : K), fun v hv ↦ (mem_primeToSubgroup.mp x.property v (by simpa using hv)).le⟩
  map_one' := map_one (𝔪.finitePart.sIntegerToQuotient (K := K))
  map_mul' x y := map_mul (𝔪.finitePart.sIntegerToQuotient (K := K))
    ⟨((x : Kˣ) : K), fun v hv ↦ (mem_primeToSubgroup.mp x.property v (by simpa using hv)).le⟩
    ⟨((y : Kˣ) : K), fun v hv ↦ (mem_primeToSubgroup.mp y.property v (by simpa using hv)).le⟩

/-- **The reduction is computed by any presentation with denominator congruent to one.** -/
theorem residue_eq {𝔪 : Modulus K} (x : primeToSubgroup 𝔪) {a b : 𝓞 K}
    (hb : b - 1 ∈ 𝔪.finitePart)
    (hab : algebraMap (𝓞 K) K a = algebraMap (𝓞 K) K b * ((x : Kˣ) : K)) :
    residue 𝔪 x = Ideal.Quotient.mk 𝔪.finitePart a := by
  exact 𝔪.finitePart.sIntegerToQuotient_eq _ hb hab

/-- **Reduction modulo the finite part of a modulus**, as a homomorphism from the elements that are
units at the primes dividing `𝔪.finitePart` to the residue units.  This is the carrier of the
residue-unit factor in the ray class number formula. -/
noncomputable def residueHom (𝔪 : Modulus K) :
    primeToSubgroup 𝔪 →* (𝓞 K ⧸ 𝔪.finitePart)ˣ :=
  MonoidHom.toHomUnits (residue 𝔪)

@[simp] theorem coe_residueHom (𝔪 : Modulus K) (x : primeToSubgroup 𝔪) :
    ((residueHom 𝔪 x : (𝓞 K ⧸ 𝔪.finitePart)ˣ) : 𝓞 K ⧸ 𝔪.finitePart) = residue 𝔪 x :=
  MonoidHom.coe_toHomUnits _ x

/-- **Reduction to one is exactly congruence to one at the primes dividing the finite part.**  The
reduction carries the finite conditions of `IsCongrOne` and nothing else, so the archimedean
conditions are independent of it and have to be supplied separately. -/
theorem residue_eq_one_iff {𝔪 : Modulus K} (x : primeToSubgroup 𝔪) :
    residue 𝔪 x = 1 ↔ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.finitePart →
      v.valuation K (((x : Kˣ) : K) - 1) ≤ WithZero.exp (-(𝔪.exponent v : ℤ)) := by
  simp only [Modulus.exponent_def]
  exact 𝔪.finitePart.sIntegerToQuotient_eq_one_iff 𝔪.finitePart_ne_bot
      ⟨((x : Kˣ) : K), fun v hv ↦ (mem_primeToSubgroup.mp x.property v (by simpa using hv)).le⟩

/-- **An element reducing to one and positive at the real places of `𝔪` is congruent to one.** -/
theorem isCongrOne_of_residue_eq_one {𝔪 : Modulus K} {x : Kˣ} (hx : x ∈ primeToSubgroup 𝔪)
    (hres : residue 𝔪 ⟨x, hx⟩ = 1)
    (hpos : ∀ w ∈ 𝔪.infinitePart, 0 < InfinitePlace.embedding_of_isReal w.property (x : K)) :
    IsCongrOne 𝔪 x :=
  isCongrOne_iff.mpr ⟨(residue_eq_one_iff ⟨x, hx⟩).mp hres, hpos⟩

/-- **Congruence to one sees the finite part only through the reduction.**  For two moduli with the
same finite part, an element that is a unit at that finite part is congruent to one modulo `𝔪`
exactly when it reduces to one modulo `𝔫` and is positive at the real places of `𝔪`.  This is how
the finite conditions of one modulus are read off the reduction attached to another. -/
theorem isCongrOne_iff_residueHom_eq_one_of_finitePart_eq {𝔪 𝔫 : Modulus K}
    (hfin : 𝔪.finitePart = 𝔫.finitePart) {x : Kˣ} (hx : x ∈ primeToSubgroup 𝔫) :
    IsCongrOne 𝔪 x ↔ residueHom 𝔫 ⟨x, hx⟩ = 1 ∧
      ∀ w ∈ 𝔪.infinitePart, 0 < InfinitePlace.embedding_of_isReal w.property (x : K) := by
  have hexp : ∀ v, 𝔪.exponent v = 𝔫.exponent v := fun v ↦ by
    rw [Modulus.exponent_def, Modulus.exponent_def, hfin]
  rw [isCongrOne_iff, Units.ext_iff, coe_residueHom, Units.val_one, residue_eq_one_iff]
  simp only [hfin, hexp]

/-- **An element congruent to one modulo `𝔪` reduces to one**: the congruence subgroup lies in the
kernel of `residueHom 𝔪`. -/
theorem residueHom_eq_one_of_mem_congruenceSubgroup {𝔪 : Modulus K} {x : primeToSubgroup 𝔪}
    (hx : (x : Kˣ) ∈ congruenceSubgroup 𝔪) : residueHom 𝔪 x = 1 := by
  refine Units.ext ?_
  rw [coe_residueHom, Units.val_one]
  exact (residue_eq_one_iff x).mpr fun v hv ↦
    (mem_congruenceSubgroup.mp hx).valuation_sub_one_le hv

/-- **An element congruent to one is a quotient of integers congruent to one, with a nonzero
totally positive denominator.** If `IsCongrOne 𝔪 x`, then `x = a / b` with `a b : 𝓞 K` both
congruent to one modulo `𝔪.finitePart` and `b` nonzero and totally positive. In particular `a` is
nonzero and has the sign of `x` at every real place. -/
theorem IsCongrOne.exists_sub_one_mem_and_ne_zero_and_isTotallyPositive_and_algebraMap_eq_mul
    {𝔪 : Modulus K} {x : Kˣ} (hx : IsCongrOne 𝔪 x) :
    ∃ a b : 𝓞 K, a - 1 ∈ 𝔪.finitePart ∧ b - 1 ∈ 𝔪.finitePart ∧ b ≠ 0 ∧
      IsTotallyPositive (b : K) ∧ algebraMap (𝓞 K) K a = algebraMap (𝓞 K) K b * (x : K) := by
  have hxp : x ∈ primeToSubgroup 𝔪 :=
    congruenceSubgroup_le_primeToSubgroup _ (mem_congruenceSubgroup.mpr hx)
  obtain ⟨a, b, hb, hab⟩ :=
    𝔪.finitePart.exists_algebraMap_eq_mul_and_sub_one_mem_of_valuation_le_one
      (fun v hv ↦ (mem_primeToSubgroup.mp hxp v hv).le)
  -- the reduction of `x` modulo the finite part is that of `a`, and is one
  have ha : a - 1 ∈ 𝔪.finitePart := by
    refine Ideal.Quotient.eq.mp ?_
    rw [map_one, ← residue_eq ⟨x, hxp⟩ hb hab, ← coe_residueHom,
      residueHom_eq_one_of_mem_congruenceSubgroup (mem_congruenceSubgroup.mpr hx), Units.val_one]
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (x : K)
  have hq0 : algebraMap (𝓞 K) K q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr (nonZeroDivisors.ne_zero hq)
  have hH : 𝔪.finitePart * Ideal.span {q} ≠ ⊥ := mul_ne_zero 𝔪.finitePart_ne_bot
    (Ideal.span_singleton_eq_bot.not.mpr (nonZeroDivisors.ne_zero hq))
  -- Moving `b` inside `𝔪.finitePart * (q)` keeps it a denominator of `x` congruent to one, and
  -- makes it nonzero and totally positive.
  obtain ⟨c, hc0, hcb, hcpos⟩ := exists_isTotallyPositive_sub_mem hH b
  obtain ⟨f, hf, hfq⟩ := Ideal.mem_mul_span_singleton.mp hcb
  refine ⟨a + f * p, c, ?_, ?_, hc0, hcpos, ?_⟩
  · rw [add_sub_right_comm]
    exact 𝔪.finitePart.add_mem ha (𝔪.finitePart.mul_mem_right p hf)
  · rw [← sub_add_sub_cancel c b 1]
    exact 𝔪.finitePart.add_mem (Ideal.mul_le_left hcb) hb
  · have hqx : algebraMap (𝓞 K) K q * (x : K) = algebraMap (𝓞 K) K p := by
      rw [← hpq]
      field_simp
    rw [← sub_add_cancel c b, ← hfq]
    simp only [map_add, map_mul]
    linear_combination hab - algebraMap (𝓞 K) K f * hqx

/-! ### Surjectivity of the reduction -/

/-- **Every residue unit modulo the finite part is the reduction of a field unit prime to it.**
This is what makes the residue-unit factor of the ray class number formula the *whole* of
`(𝓞 K ⧸ 𝔪.finitePart)ˣ` rather than the image of the algebraic integers prime to `𝔪`. -/
theorem residueHom_surjective (𝔪 : Modulus K) : Function.Surjective (residueHom 𝔪) := by
  intro u
  obtain ⟨z, hz⟩ := 𝔪.finitePart.units_map_sIntegerToQuotient_surjective
    (K := K) u
  let e := Set.unitEquivUnitsInteger
    ({v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔪.finitePart}ᶜ) K
  let y := e.symm z
  have hy : (y : Kˣ) ∈ primeToSubgroup 𝔪 := mem_primeToSubgroup.mpr fun v hv ↦
    Set.unit_valuation_eq_one _ K y (by simpa using hv)
  refine ⟨⟨y, hy⟩, Units.ext ?_⟩
  rw [coe_residueHom]
  calc
    residue 𝔪 ⟨y, hy⟩ = 𝔪.finitePart.sIntegerToQuotient (e y).val := by
      apply congrArg (𝔪.finitePart.sIntegerToQuotient (K := K))
      exact Subtype.ext (Set.val_unitEquivUnitsInteger_apply_coe _ K y).symm
    _ = 𝔪.finitePart.sIntegerToQuotient z.val :=
      congrArg (fun t ↦ 𝔪.finitePart.sIntegerToQuotient t.val) (e.apply_symm_apply z)
    _ = u.val := congrArg Units.val hz

/-! ### Transition maps for residue units -/

/-- The reduction map on residue units from a larger finite part to a divisor of it.  It is induced
by the canonical quotient map between the two ideal quotients; in particular, it does not choose a
ring-level inverse. -/
noncomputable def finiteUnitsMap {𝔪 𝔫 : Modulus K} (h : 𝔪.finitePart ∣ 𝔫.finitePart) :
    ((𝓞 K) ⧸ 𝔫.finitePart)ˣ →* ((𝓞 K) ⧸ 𝔪.finitePart)ˣ :=
  Units.map (Ideal.Quotient.factor (Ideal.le_of_dvd h)).toMonoidHom

/-- The value of the transition map is the image under the canonical quotient map of the
underlying residue-unit value. -/
@[simp]
theorem coe_finiteUnitsMap {𝔪 𝔫 : Modulus K} (h : 𝔪.finitePart ∣ 𝔫.finitePart)
    (x : ((𝓞 K) ⧸ 𝔫.finitePart)ˣ) :
    (finiteUnitsMap h x : (𝓞 K) ⧸ 𝔪.finitePart) =
      Ideal.Quotient.factor (Ideal.le_of_dvd h)
        (x : (𝓞 K) ⧸ 𝔫.finitePart) := by
  rfl

/-- Every residue unit modulo the smaller finite part lifts to a residue unit modulo the larger
finite part. The lift need not be the reduction of a global integer unit. -/
theorem finiteUnitsMap_surjective {𝔪 𝔫 : Modulus K} (h : 𝔪.finitePart ∣ 𝔫.finitePart) :
    Function.Surjective (finiteUnitsMap h) :=
  units_map_quotient_factor_surjective (Ideal.le_of_dvd h) 𝔫.finitePart_ne_bot

/-- Changing the finite part along reflexivity gives the identity map. -/
@[simp]
theorem finiteUnitsMap_refl (𝔪 : Modulus K) :
    finiteUnitsMap (_root_.dvd_refl 𝔪.finitePart) = MonoidHom.id _ := by
  ext x
  simp [finiteUnitsMap]

/-- Transition maps compose along a chain of finite-part divisibility. -/
@[simp]
theorem finiteUnitsMap_comp_finiteUnitsMap {𝔪 𝔫 𝔭 : Modulus K}
    (h₁ : 𝔪.finitePart ∣ 𝔫.finitePart) (h₂ : 𝔫.finitePart ∣ 𝔭.finitePart) :
    (finiteUnitsMap h₁).comp (finiteUnitsMap h₂) =
      finiteUnitsMap (h₁.trans h₂) := by
  ext x
  simp [finiteUnitsMap, Ideal.Quotient.factor_comp_apply]

/-- Reduction of a prime-to element commutes with passing to a modulus with smaller finite part. -/
@[simp]
theorem finiteUnitsMap_residueHom {𝔪 𝔫 : Modulus K} (h : 𝔪.finitePart ∣ 𝔫.finitePart)
    (x : primeToSubgroup 𝔫) :
    finiteUnitsMap h (residueHom 𝔫 x) =
      residueHom 𝔪 (Subgroup.inclusion (primeToSubgroup_le_of_dvd h) x) := by
  obtain ⟨a, b, hb, hab⟩ :=
    𝔫.finitePart.exists_algebraMap_eq_mul_and_sub_one_mem_of_valuation_le_one
      (fun v hv ↦ (mem_primeToSubgroup.mp x.property v hv).le)
  have hbm : b - 1 ∈ 𝔪.finitePart :=
    (Ideal.le_of_dvd h) hb
  have habm : algebraMap (𝓞 K) K a = algebraMap (𝓞 K) K b *
      (((Subgroup.inclusion (primeToSubgroup_le_of_dvd h) x : primeToSubgroup 𝔪) : Kˣ) : K) := by
    simpa only [Subgroup.coe_inclusion] using hab
  apply Units.ext
  -- Expose the underlying quotient values so `residue_eq` can be applied on both sides.
  change Ideal.Quotient.factor (Ideal.le_of_dvd h) (residue 𝔫 x) =
    residue 𝔪 (Subgroup.inclusion (primeToSubgroup_le_of_dvd h) x)
  rw [residue_eq (x := x) (a := a) (b := b) hb hab,
    Ideal.Quotient.factor_mk,
    residue_eq (x := Subgroup.inclusion (primeToSubgroup_le_of_dvd h) x)
      (a := a) (b := b) hbm habm]

/-! ### Quotients and weak approximation in `primeToSubgroup` -/

/-- Every element of `primeToSubgroup 𝔪` is a quotient of two algebraic integers in
`primeToSubgroup 𝔪`. -/
theorem exists_primeToSubgroup_div_eq {𝔪 : Modulus K} (x : primeToSubgroup 𝔪) :
    ∃ (a b : 𝓞 K) (xa xb : primeToSubgroup 𝔪),
      algebraMap (𝓞 K) K a = ((xa : Kˣ) : K) ∧ algebraMap (𝓞 K) K b = ((xb : Kˣ) : K) ∧
        xa = xb * x := by
  obtain ⟨a, b, hb, hab⟩ :=
    𝔪.finitePart.exists_algebraMap_eq_mul_and_sub_one_mem_of_valuation_le_one
      (fun v hv ↦ (mem_primeToSubgroup.mp x.property v hv).le)
  by_cases hb0 : b = 0
  · have htop : 𝔪.finitePart = ⊤ := by
      rw [hb0, zero_sub] at hb
      exact Ideal.eq_top_of_isUnit_mem _ (by simpa using 𝔪.finitePart.neg_mem hb) isUnit_one
    obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := 𝓞 K) ((x : Kˣ) : K)
    have hq0 : algebraMap (𝓞 K) K q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr (nonZeroDivisors.ne_zero hq)
    have hpqx : algebraMap (𝓞 K) K p = algebraMap (𝓞 K) K q * ((x : Kˣ) : K) := by
      rw [← hpq, mul_div_cancel₀ _ hq0]
    have hp0 : algebraMap (𝓞 K) K p ≠ 0 := by
      rw [hpqx]
      exact mul_ne_zero hq0 (x : Kˣ).ne_zero
    have hmem_all (y : Kˣ) : y ∈ primeToSubgroup 𝔪 :=
      mem_primeToSubgroup.mpr fun v hv ↦
        absurd (top_le_iff.mp (Ideal.le_of_dvd (htop ▸ hv))) v.isPrime.ne_top
    refine ⟨p, q, ⟨Units.mk0 _ hp0, hmem_all _⟩, ⟨Units.mk0 _ hq0, hmem_all _⟩, rfl, rfl,
      Subtype.ext (Units.ext hpqx)⟩
  · have hxb0 : algebraMap (𝓞 K) K b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hb0
    let xb_u : Kˣ := Units.mk0 (algebraMap (𝓞 K) K b) hxb0
    have hxb : xb_u ∈ primeToSubgroup 𝔪 := by
      refine mem_primeToSubgroup.mpr fun v hv ↦ ?_
      rw [Units.val_mk0, v.valuation_of_algebraMap]
      refine v.intValuation_eq_one_iff.mpr fun hbv ↦ v.isPrime.ne_top ?_
      have h1 : (1 : 𝓞 K) ∈ v.asIdeal := by
        have hsub : b - 1 ∈ v.asIdeal := Ideal.le_of_dvd hv hb
        simpa using v.asIdeal.sub_mem hbv hsub
      exact Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one
    have hxa0 : algebraMap (𝓞 K) K a ≠ 0 := by
      rw [hab]
      exact mul_ne_zero hxb0 (x : Kˣ).ne_zero
    let xa_u : Kˣ := Units.mk0 (algebraMap (𝓞 K) K a) hxa0
    have hxeq : xa_u = xb_u * (x : Kˣ) := Units.ext hab
    exact ⟨a, b, ⟨xa_u, hxeq ▸ mul_mem hxb x.property⟩, ⟨xb_u, hxb⟩, rfl, rfl, Subtype.ext hxeq⟩

/-- Given a prime `v₀ ∈ 𝔪.support` and a local unit `z ∈ U(K_{v₀}, k)` with `k ≤ 𝔪.exponent v₀`,
there is a nonzero global element `x ∈ primeToSubgroup 𝔪`, a local unit at every prime dividing
`𝔪`, approximating `z` to level `𝔪.exponent v₀` at `v₀` and `1` to level `𝔪.exponent v` at every
other `v ∈ 𝔪.support`. -/
theorem exists_primeToSubgroup_approx_localUnit {𝔪 : Modulus K} {v₀ : HeightOneSpectrum (𝓞 K)}
    (hv₀ : v₀ ∈ 𝔪.support) {k : ℕ} (hk : k ≤ 𝔪.exponent v₀)
    (z : (v₀.adicCompletion K)ˣ)
    (hz : z ∈ TauCeti.unitFiltration (v₀.adicCompletion K) k) :
    ∃ x : primeToSubgroup 𝔪,
      Units.map (algebraMap K (v₀.adicCompletion K)).toMonoidHom (x : Kˣ) * z⁻¹ ∈
          TauCeti.unitFiltration (v₀.adicCompletion K) (𝔪.exponent v₀) ∧
        (∀ v ∈ 𝔪.support, v ≠ v₀ →
          Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom (x : Kˣ) ∈
            TauCeti.unitFiltration (v.adicCompletion K) (𝔪.exponent v)) ∧
        v₀.valuation K (((x : Kˣ) : K) - 1) ≤ WithZero.exp (-(k : ℤ)) := by
  classical
  obtain ⟨a₀, ha₀⟩ := v₀.exists_algebraMap_adicCompletion_sub_lt (z : v₀.adicCompletion K)
    (𝔪.exponent v₀)
  obtain ⟨x, hxf, -⟩ := exists_fieldUnit_valuation_sub_lt_and_signHom_eq (S := 𝔪.support)
    (fun v ↦ if v = v₀ then a₀ else 1)
    (fun v ↦ WithZero.exp (-(𝔪.exponent v : ℤ)))
    (fun _ _ ↦ WithZero.exp_ne_zero) 1
  have hvpos (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ 𝔪.support) :
      WithZero.exp (-(𝔪.exponent v : ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
    have hne : 𝔪.exponent v ≠ 0 := (Modulus.mem_support_iff_exponent_ne_zero 𝔪 v).mp hv
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hxz : Valued.v (algebraMap K (v₀.adicCompletion K) (x : K) - (z : v₀.adicCompletion K)) <
      WithZero.exp (-(𝔪.exponent v₀ : ℤ)) := by
    have hxa : Valued.v (algebraMap K (v₀.adicCompletion K) (x : K) -
        algebraMap K (v₀.adicCompletion K) a₀) < WithZero.exp (-(𝔪.exponent v₀ : ℤ)) := by
      rw [← map_sub, valued_algebraMap_adicCompletion]
      simpa using hxf v₀ hv₀
    have heq : algebraMap K (v₀.adicCompletion K) (x : K) - (z : v₀.adicCompletion K) =
        (algebraMap K (v₀.adicCompletion K) (x : K) - algebraMap K (v₀.adicCompletion K) a₀) +
          (algebraMap K (v₀.adicCompletion K) a₀ - (z : v₀.adicCompletion K)) := by ring
    rw [heq]
    exact (Valuation.map_add _ _ _).trans_lt (max_lt hxa ha₀)
  have hz_mem := (v₀.mem_unitFiltration_adicCompletion_iff (K := K)).mp hz
  have hx0_val : Valued.v (algebraMap K (v₀.adicCompletion K) (x : K)) = 1 := by
    have hlt : Valued.v (algebraMap K (v₀.adicCompletion K) (x : K) -
        (z : v₀.adicCompletion K)) < Valued.v (z : v₀.adicCompletion K) :=
      hxz.trans ((hvpos v₀ hv₀).trans_eq hz_mem.1.symm)
    rw [Valuation.map_eq_of_sub_lt _ hlt, hz_mem.1]
  have hx_mem : x ∈ primeToSubgroup 𝔪 := by
    refine mem_primeToSubgroup.mpr fun v hv ↦ ?_
    have hv' : v ∈ 𝔪.support := (𝔪.mem_support_iff v).mpr hv
    by_cases heq : v = v₀
    · subst heq
      simpa only [valued_algebraMap_adicCompletion] using hx0_val
    · have hlt : v.valuation K ((x : K) - 1) < v.valuation K 1 := by
        rw [map_one]
        exact (by simpa [heq] using hxf v hv' : _ < _).trans (hvpos v hv')
      rw [Valuation.map_eq_of_sub_lt _ hlt, map_one]
  refine ⟨⟨x, hx_mem⟩,
    v₀.mul_inv_mem_unitFiltration_of_sub_lt hz_mem.1 (by simpa using hxz),
    fun v hv hne ↦ (v.unitsMap_algebraMap_mem_unitFiltration_iff (𝔪.exponent v) x).mpr
      ⟨mem_primeToSubgroup.mp hx_mem v ((𝔪.mem_support_iff v).mp hv),
        (by simpa [hne] using hxf v hv : _ < _).le⟩,
    ?_⟩
  have hle : WithZero.exp (-(𝔪.exponent v₀ : ℤ)) ≤ WithZero.exp (-(k : ℤ)) :=
    WithZero.exp_le_exp.mpr (by omega)
  have hsub : Valued.v (algebraMap K (v₀.adicCompletion K) ((x : K) - 1)) ≤
      WithZero.exp (-(k : ℤ)) := by
    have heq : algebraMap K (v₀.adicCompletion K) ((x : K) - 1) =
        (algebraMap K (v₀.adicCompletion K) (x : K) - (z : v₀.adicCompletion K)) +
          ((z : v₀.adicCompletion K) - 1) := by
      rw [map_sub, map_one]; ring
    rw [heq]
    exact (Valuation.map_add _ _ _).trans (max_le (hxz.le.trans hle) hz_mem.2)
  simpa only [valued_algebraMap_adicCompletion] using hsub

end TauCeti.GlobalNumberFields
