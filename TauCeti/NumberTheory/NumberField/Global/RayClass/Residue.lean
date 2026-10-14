/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import TauCeti.RingTheory.DedekindDomain.SInteger.Quotient

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

* `Ideal.exists_algebraMap_eq_mul_of_valuation_le_one`: a locally integral element has a
  denominator congruent to one modulo an ideal, over an arbitrary Dedekind domain.
* `TauCeti.GlobalNumberFields.residue_eq_one_iff`: reduction to one is equivalent to the
  finite-place conditions in `IsCongrOne`.
* `TauCeti.GlobalNumberFields.residueHom_eq_one_of_mem_congruenceSubgroup`: an element congruent to
  one maps to one under reduction.
* `TauCeti.GlobalNumberFields.isCongrOne_iff_residueHom_eq_one_of_finitePart_eq`: for two moduli
  with the same finite part, congruence to one modulo one of them is reduction to one modulo the
  other together with positivity at its real places.
* `TauCeti.GlobalNumberFields.IsCongrOne.exists_sub_one_mem_and_algebraMap_eq_mul`: an element
  congruent to one is a quotient of two algebraic integers congruent to one.
* `TauCeti.GlobalNumberFields.residueHom_surjective`: every residue unit modulo the finite part is
  the reduction of an element of `Kˣ` that is a unit at that finite part.
* `TauCeti.GlobalNumberFields.finiteUnitsMap_refl` and
  `TauCeti.GlobalNumberFields.finiteUnitsMap_comp_finiteUnitsMap`: the transition maps are
  functorial in finite-part divisibility.
* `TauCeti.GlobalNumberFields.finiteUnitsMap_residueHom`: reduction commutes with changing the
  modulus.
* `TauCeti.GlobalNumberFields.finiteUnitsMap_surjective`: every residue unit lifts to a larger
  finite modulus.

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
    ⟨((x : Kˣ) : K), fun v hv ↦ (mem_primeToSubgroup.mp x.2 v (by simpa using hv)).le⟩
  map_one' := map_one (𝔪.finitePart.sIntegerToQuotient (K := K))
  map_mul' x y := map_mul (𝔪.finitePart.sIntegerToQuotient (K := K))
    ⟨((x : Kˣ) : K), fun v hv ↦ (mem_primeToSubgroup.mp x.2 v (by simpa using hv)).le⟩
    ⟨((y : Kˣ) : K), fun v hv ↦ (mem_primeToSubgroup.mp y.2 v (by simpa using hv)).le⟩

private theorem exists_residue_eq (𝔪 : Modulus K) (x : primeToSubgroup 𝔪) :
    ∃ a b : 𝓞 K, b - 1 ∈ 𝔪.finitePart ∧
      algebraMap (𝓞 K) K a = algebraMap (𝓞 K) K b * ((x : Kˣ) : K) ∧
      residue 𝔪 x = Ideal.Quotient.mk 𝔪.finitePart a := by
  obtain ⟨a, b, hb, hab⟩ := 𝔪.finitePart.exists_algebraMap_eq_mul_of_valuation_le_one
    (fun v hv ↦ (mem_primeToSubgroup.mp x.2 v hv).le)
  exact ⟨a, b, hb, hab, 𝔪.finitePart.sIntegerToQuotient_eq _ hb hab⟩

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
  obtain ⟨a, b, hb, hab, hr⟩ := exists_residue_eq 𝔪 x
  -- The reduction is one exactly when the numerator is congruent to one.
  have hnum : residue 𝔪 x = 1 ↔ a - 1 ∈ 𝔪.finitePart := by
    rw [hr, ← map_one (Ideal.Quotient.mk 𝔪.finitePart)]
    exact Ideal.Quotient.eq
  -- At a prime dividing the finite part the denominator is a unit, so `x - 1` and `a - b` have
  -- the same valuation there.
  have hval : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.finitePart →
      v.valuation K (((x : Kˣ) : K) - 1) = v.intValuation (a - b) := by
    intro v hv
    -- `b` is a unit at `v`, since it is congruent to one modulo an ideal contained in `v`.
    have hbv : b ∉ v.asIdeal := by
      intro hbv
      refine v.isPrime.ne_top (Ideal.eq_top_iff_one _ |>.mpr ?_)
      have hone : (1 : 𝓞 K) = b - (b - 1) := by ring
      rw [hone]
      exact Ideal.sub_mem _ hbv (Ideal.le_of_dvd hv hb)
    have hb0 : algebraMap (𝓞 K) K b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr fun h ↦
        hbv (h ▸ v.asIdeal.zero_mem)
    have hbval : v.valuation K (algebraMap (𝓞 K) K b) = 1 := by
      rw [valuation_of_algebraMap]
      exact intValuation_eq_one_iff.mpr hbv
    have hxsub : ((x : Kˣ) : K) - 1 = algebraMap (𝓞 K) K (a - b) / algebraMap (𝓞 K) K b := by
      rw [map_sub, hab]
      field_simp
    rw [hxsub, map_div₀, valuation_of_algebraMap, hbval, div_one]
  rw [hnum]
  refine ⟨fun ha1 v hv ↦ ?_, fun h ↦ ?_⟩
  · -- Both `a` and `b` are congruent to one, so `a - b` lies in the finite part.
    have hab' : a - b ∈ 𝔪.finitePart := by
      have hsub : a - b = (a - 1) - (b - 1) := by ring
      rw [hsub]
      exact Ideal.sub_mem _ ha1 hb
    rw [hval v hv]
    exact (v.intValuation_le_pow_iff_mem (a - b) (𝔪.exponent v)).mpr
      (Ideal.le_of_dvd (𝔪.pow_exponent_dvd_finitePart v) hab')
  · -- Conversely the local conditions on `a - b` assemble into membership in the finite part.
    have hab' : a - b ∈ 𝔪.finitePart :=
      𝔪.mem_finitePart_of_forall_mem_pow_exponent fun v hv ↦
        (v.intValuation_le_pow_iff_mem (a - b) (𝔪.exponent v)).mp (hval v hv ▸ h v hv)
    have hsum : a - 1 = (a - b) + (b - 1) := by ring
    rw [hsum]
    exact Ideal.add_mem _ hab' hb

/-- **An element reducing to one and positive at the real places of `𝔪` is congruent to one.** -/
theorem isCongrOne_of_residue_eq_one {𝔪 : Modulus K} {x : Kˣ} (hx : x ∈ primeToSubgroup 𝔪)
    (hres : residue 𝔪 ⟨x, hx⟩ = 1)
    (hpos : ∀ w ∈ 𝔪.infinitePart, 0 < InfinitePlace.embedding_of_isReal w.2 (x : K)) :
    IsCongrOne 𝔪 x :=
  isCongrOne_iff.mpr ⟨(residue_eq_one_iff ⟨x, hx⟩).mp hres, hpos⟩

/-- **Congruence to one sees the finite part only through the reduction.**  For two moduli with the
same finite part, an element that is a unit at that finite part is congruent to one modulo `𝔪`
exactly when it reduces to one modulo `𝔫` and is positive at the real places of `𝔪`.  This is how
the finite conditions of one modulus are read off the reduction attached to another. -/
theorem isCongrOne_iff_residueHom_eq_one_of_finitePart_eq {𝔪 𝔫 : Modulus K}
    (hfin : 𝔪.finitePart = 𝔫.finitePart) {x : Kˣ} (hx : x ∈ primeToSubgroup 𝔫) :
    IsCongrOne 𝔪 x ↔ residueHom 𝔫 ⟨x, hx⟩ = 1 ∧
      ∀ w ∈ 𝔪.infinitePart, 0 < InfinitePlace.embedding_of_isReal w.2 (x : K) := by
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

/-- **An element congruent to one is a quotient of integers congruent to one.** If
`IsCongrOne 𝔪 x`, then `x = a / b` with `a b : 𝓞 K` both congruent to one modulo
`𝔪.finitePart`. -/
theorem IsCongrOne.exists_sub_one_mem_and_algebraMap_eq_mul {𝔪 : Modulus K} {x : Kˣ}
    (hx : IsCongrOne 𝔪 x) : ∃ a b : 𝓞 K, a - 1 ∈ 𝔪.finitePart ∧ b - 1 ∈ 𝔪.finitePart ∧
      algebraMap (𝓞 K) K a = algebraMap (𝓞 K) K b * (x : K) := by
  have hxp : x ∈ primeToSubgroup 𝔪 :=
    congruenceSubgroup_le_primeToSubgroup _ (mem_congruenceSubgroup.mpr hx)
  obtain ⟨a, b, hb, hab⟩ := 𝔪.finitePart.exists_algebraMap_eq_mul_of_valuation_le_one
    (fun v hv ↦ (mem_primeToSubgroup.mp hxp v hv).le)
  -- the reduction of `x` modulo the finite part is that of `a`, and is one
  refine ⟨a, b, Ideal.Quotient.eq.mp ?_, hb, hab⟩
  rw [map_one, ← residue_eq ⟨x, hxp⟩ hb hab, ← coe_residueHom,
    residueHom_eq_one_of_mem_congruenceSubgroup (mem_congruenceSubgroup.mpr hx), Units.val_one]

/-! ### Surjectivity of the reduction -/

/-- **Every residue unit modulo the finite part is the reduction of a field unit prime to it.**
This is what makes the residue-unit factor of the ray class number formula the *whole* of
`(𝓞 K ⧸ 𝔪.finitePart)ˣ` rather than the image of the algebraic integers prime to `𝔪`.

The generic unit-lifting theorem for `Ideal.sIntegerToQuotient` supplies a locally integral
unit. Mathlib's `Set.unitEquivUnitsInteger` reads that unit as an element of `Kˣ` prime to the
finite part. -/
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
    residue 𝔪 ⟨y, hy⟩ = 𝔪.finitePart.sIntegerToQuotient (e y).val :=
      -- Both inputs are the locally integral element underlying the same field unit.
      (rfl)
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
  obtain ⟨a, b, hb, hab⟩ := 𝔫.finitePart.exists_algebraMap_eq_mul_of_valuation_le_one
    (fun v hv ↦ (mem_primeToSubgroup.mp x.2 v hv).le)
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

end TauCeti.GlobalNumberFields
