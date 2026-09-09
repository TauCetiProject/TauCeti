/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

/-!
# The ray class group of a modulus is finite

Let `𝔪` be a modulus of a number field `K`.  This file proves that `RayClassGroup 𝔪` is finite.

The argument runs along the two steps of the ray class exact sequence.  The transition map to the
ordinary class group has finite image because the class group of a number field is finite, and its
kernel is the group of *principal* ideals prime to `𝔪`, modulo the ray.  That kernel is a quotient
of `primeToSubgroup 𝔪 ⧸ congruenceSubgroup 𝔪`, so everything rests on

`TauCeti.GlobalNumberFields.congruenceSubgroup_finiteIndex`: the elements congruent to one modulo
`𝔪` have finite index among the elements that are units at the primes dividing the finite part.

That finiteness is proved by *reduction*.  An `x : Kˣ` that is a unit at every prime dividing the
finite part `𝔪₀` can be written as `x = a / b` with `a b : 𝓞 K` and `b ≡ 1 mod 𝔪₀`
(`exists_algebraMap_eq_mul_of_mem_primeToSubgroup`): the denominator of `x` is prime to `𝔪₀`
precisely because `x` has no pole there, and a denominator prime to `𝔪₀` may be corrected to one
congruent to one.  The class of `a` in `𝓞 K ⧸ 𝔪₀` does not depend on the chosen presentation, so
it defines the reduction homomorphism `residueHom 𝔪` into the finite group `(𝓞 K ⧸ 𝔪₀)ˣ`.  An
element that reduces to one and is totally positive is congruent to one modulo `𝔪`; since the
totally positive elements already have finite index in `Kˣ`, so does the congruence subgroup
relative to `primeToSubgroup 𝔪`.

The unit-group form `unitsCongruenceSubgroup_finiteIndex` — the units of `𝓞 K` congruent to one
modulo `𝔪` have finite index in `(𝓞 K)ˣ` — is the same statement pulled back along
`(𝓞 K)ˣ → Kˣ`; it is the unit correction appearing in the ray class number formula, and the
finite-index input to the geometry-of-numbers count of ideals in a ray class.

## Main definitions

* `TauCeti.GlobalNumberFields.residue`, `TauCeti.GlobalNumberFields.residueHom`: reduction of an
  element that is a unit at the finite part of `𝔪` to the residue units modulo `𝔪₀`.

## Main results

* `TauCeti.GlobalNumberFields.exists_algebraMap_eq_mul_of_mem_primeToSubgroup`: an element that is
  a unit at the primes dividing `𝔪₀` has a denominator congruent to one modulo `𝔪₀`.
* `TauCeti.GlobalNumberFields.residue_eq_one_iff`: reducing to one is congruence to one at the
  primes dividing `𝔪₀`, with `TauCeti.GlobalNumberFields.isCongrOne_of_residue_eq_one` and
  `TauCeti.GlobalNumberFields.residueHom_eq_one_of_mem_congruenceSubgroup` the two directions
  read off against `IsCongrOne`.
* `TauCeti.GlobalNumberFields.congruenceSubgroup_finiteIndex` and
  `TauCeti.GlobalNumberFields.unitsCongruenceSubgroup_finiteIndex`: the two finite-index
  statements.
* `TauCeti.GlobalNumberFields.finite_rayClassGroup`: the ray class group of a modulus is finite.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-! ### Denominators prime to the finite part -/

/-- **An element that is a unit at the finite part has a denominator congruent to one.**  If `x` is
a unit at every prime dividing `𝔪.finitePart`, then `x = a / b` with `a b : 𝓞 K` and
`b ≡ 1 mod 𝔪.finitePart`.  Such a presentation is what makes the reduction `residue` of `x`
modulo the finite part available. -/
theorem exists_algebraMap_eq_mul_of_mem_primeToSubgroup {𝔪 : Modulus K} {x : Kˣ}
    (hx : x ∈ primeToSubgroup 𝔪) :
    ∃ a b : 𝓞 K, b - 1 ∈ 𝔪.finitePart ∧
      algebraMap (𝓞 K) K a = algebraMap (𝓞 K) K b * (x : K) := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exists_integer_multiple (𝓞 K)⁰ (x : K)
  obtain ⟨c, hc⟩ := hd
  rw [Algebra.smul_def] at hc
  have hd0 : (d : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero d.2
  set D : Ideal (𝓞 K) := Ideal.span {(d : 𝓞 K)} with hD
  set C : Ideal (𝓞 K) := Ideal.span {c} with hCdef
  set G : Ideal (𝓞 K) := C ⊔ D with hG
  have hD0 : D ≠ ⊥ := by
    simpa only [hD, ne_eq, Ideal.span_singleton_eq_bot] using hd0
  obtain ⟨L, hL⟩ : G ∣ D := Ideal.dvd_iff_le.mpr le_sup_right
  have hG0 : G ≠ ⊥ := fun h ↦ hD0 (by simp [hL, h])
  have hL0 : L ≠ ⊥ := fun h ↦ hD0 (by simp [hL, h])
  -- The complementary factor of the denominator is prime to the finite part.
  have hLcop : L ⊔ 𝔪.finitePart = ⊤ := by
    refine (Modulus.isCoprimeTo_iff_sup_eq_top.mp
      (Modulus.isCoprimeTo_iff.mpr ⟨hL0, fun v hv hdiv ↦ ?_⟩)).2
    set n : ℕ := (Associates.mk v.asIdeal).count (Associates.mk D).factors with hn
    -- The denominator lies in `vⁿ`, and so does the numerator, since `x` is a unit at `v`.
    have hDn : D ≤ v.asIdeal ^ n := (le_count_associates_iff_le_pow v hD0 n).mp le_rfl
    have hxv : v.valuation K (x : K) = 1 :=
      mem_primeToSubgroup.mp hx v ((Modulus.mem_support_iff _ _).mp hv)
    have hcd : v.intValuation c = v.intValuation (d : 𝓞 K) := by
      have hK : v.valuation K (algebraMap (𝓞 K) K c) =
          v.valuation K (algebraMap (𝓞 K) K (d : 𝓞 K)) := by
        rw [hc, map_mul, hxv, mul_one]
      rwa [valuation_of_algebraMap, valuation_of_algebraMap] at hK
    have hCn : C ≤ v.asIdeal ^ n := by
      rw [hCdef, ← Ideal.dvd_iff_le]
      refine (v.intValuation_le_pow_iff_dvd c n).mp (hcd ▸ ?_)
      rw [hD] at hDn
      exact (v.intValuation_le_pow_iff_dvd (d : 𝓞 K) n).mpr (Ideal.dvd_iff_le.mpr hDn)
    -- Hence the gcd already has multiplicity `n`, leaving nothing for `L`.
    have hGn : n ≤ (Associates.mk v.asIdeal).count (Associates.mk G).factors :=
      (le_count_associates_iff_le_pow v hG0 n).mpr (sup_le hCn hDn)
    have hcount : (Associates.mk v.asIdeal).count (Associates.mk D).factors =
        (Associates.mk v.asIdeal).count (Associates.mk G).factors +
          (Associates.mk v.asIdeal).count (Associates.mk L).factors := by
      rw [hL, ← Associates.mk_mul_mk]
      exact Associates.count_mul (Associates.mk_ne_zero.mpr hG0) (Associates.mk_ne_zero.mpr hL0)
        v.associates_irreducible
    have hLne : (Associates.mk v.asIdeal).count (Associates.mk L).factors ≠ 0 :=
      (Associates.count_ne_zero_iff_dvd hL0 v.irreducible).mpr hdiv
    omega
  -- Pick a denominator inside that factor and congruent to one.
  obtain ⟨b, hb, m, hm, hbm⟩ :=
    Submodule.mem_sup.mp (hLcop ▸ Submodule.mem_top : (1 : 𝓞 K) ∈ L ⊔ 𝔪.finitePart)
  have hb1 : b - 1 ∈ 𝔪.finitePart := by
    have : b - 1 = -m := by rw [← hbm]; ring
    rw [this]
    exact neg_mem hm
  -- The denominator divides `c * b`, since `G ∣ C` and `L ∣ (b)`.
  have hdvd : (d : 𝓞 K) ∣ c * b := by
    have hmul : D ∣ C * Ideal.span {b} := by
      rw [hL]
      exact mul_dvd_mul (Ideal.dvd_iff_le.mpr le_sup_left)
        (Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hb))
    rw [hD, hCdef, Ideal.span_singleton_mul_span_singleton] at hmul
    rwa [← Ideal.mem_span_singleton, ← Ideal.span_singleton_le_iff_mem, ← Ideal.dvd_iff_le]
  obtain ⟨a, ha⟩ := hdvd
  refine ⟨a, b, hb1, mul_left_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hd0)
    ?_⟩
  rw [← map_mul, ← ha, map_mul, hc]
  ring

/-! ### Reduction modulo the finite part -/

/-- **The reduction of an element that is a unit at the finite part of `𝔪`**: the class modulo
`𝔪.finitePart` of a numerator in any presentation `x = a / b` with `b ≡ 1 mod 𝔪.finitePart`.  The
class does not depend on the presentation (`residue_eq`). -/
noncomputable def residue (𝔪 : Modulus K) (x : primeToSubgroup 𝔪) : 𝓞 K ⧸ 𝔪.finitePart :=
  Ideal.Quotient.mk _ (exists_algebraMap_eq_mul_of_mem_primeToSubgroup x.2).choose

private theorem exists_residue_eq (𝔪 : Modulus K) (x : primeToSubgroup 𝔪) :
    ∃ a b : 𝓞 K, b - 1 ∈ 𝔪.finitePart ∧
      algebraMap (𝓞 K) K a = algebraMap (𝓞 K) K b * ((x : Kˣ) : K) ∧
      residue 𝔪 x = Ideal.Quotient.mk 𝔪.finitePart a := by
  obtain ⟨b, hb, hab⟩ := (exists_algebraMap_eq_mul_of_mem_primeToSubgroup x.2).choose_spec
  exact ⟨_, b, hb, hab, rfl⟩

/-- **The reduction is computed by any presentation with denominator congruent to one.** -/
theorem residue_eq {𝔪 : Modulus K} (x : primeToSubgroup 𝔪) {a b : 𝓞 K}
    (hb : b - 1 ∈ 𝔪.finitePart)
    (hab : algebraMap (𝓞 K) K a = algebraMap (𝓞 K) K b * ((x : Kˣ) : K)) :
    residue 𝔪 x = Ideal.Quotient.mk 𝔪.finitePart a := by
  obtain ⟨a', b', hb', hab', hr⟩ := exists_residue_eq 𝔪 x
  have hmk : ∀ {y : 𝓞 K}, y - 1 ∈ 𝔪.finitePart → Ideal.Quotient.mk 𝔪.finitePart y = 1 := by
    intro y hy
    rw [← map_one (Ideal.Quotient.mk 𝔪.finitePart)]
    exact Ideal.Quotient.eq.mpr hy
  have key : a * b' = a' * b :=
    IsFractionRing.injective (𝓞 K) K (by rw [map_mul, map_mul, hab, hab']; ring)
  have := congrArg (Ideal.Quotient.mk 𝔪.finitePart) key
  rw [map_mul, map_mul, hmk hb, hmk hb', mul_one, mul_one] at this
  rw [hr, this]

@[simp] theorem residue_one (𝔪 : Modulus K) : residue 𝔪 1 = 1 := by
  rw [residue_eq (a := 1) (b := 1) 1 (by simp) (by simp), map_one]

@[simp] theorem residue_mul (𝔪 : Modulus K) (x y : primeToSubgroup 𝔪) :
    residue 𝔪 (x * y) = residue 𝔪 x * residue 𝔪 y := by
  obtain ⟨a₁, b₁, hb₁, hab₁, hr₁⟩ := exists_residue_eq 𝔪 x
  obtain ⟨a₂, b₂, hb₂, hab₂, hr₂⟩ := exists_residue_eq 𝔪 y
  rw [hr₁, hr₂, ← map_mul]
  refine residue_eq (b := b₁ * b₂) (x * y) ?_ ?_
  · have hexp : b₁ * b₂ - 1 = (b₁ - 1) * b₂ + (b₂ - 1) := by ring
    rw [hexp]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hb₁) hb₂
  · rw [map_mul, map_mul, hab₁, hab₂, Subgroup.coe_mul, Units.val_mul]
    ring

/-- **Reduction modulo the finite part of a modulus**, as a homomorphism from the elements that are
units at the primes dividing `𝔪.finitePart` to the residue units.  This is the carrier of the
residue-unit factor in the ray class number formula. -/
noncomputable def residueHom (𝔪 : Modulus K) :
    primeToSubgroup 𝔪 →* (𝓞 K ⧸ 𝔪.finitePart)ˣ :=
  MonoidHom.toHomUnits
    { toFun := residue 𝔪, map_one' := residue_one 𝔪, map_mul' := residue_mul 𝔪 }

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

/-- **An element congruent to one modulo `𝔪` reduces to one**: the congruence subgroup lies in the
kernel of `residueHom 𝔪`. -/
theorem residueHom_eq_one_of_mem_congruenceSubgroup {𝔪 : Modulus K} {x : primeToSubgroup 𝔪}
    (hx : (x : Kˣ) ∈ congruenceSubgroup 𝔪) : residueHom 𝔪 x = 1 := by
  refine Units.ext ?_
  rw [coe_residueHom, Units.val_one]
  exact (residue_eq_one_iff x).mpr fun v hv ↦
    (mem_congruenceSubgroup.mp hx).valuation_sub_one_le hv

/-! ### Finiteness of the index -/

/-- **The elements congruent to one modulo `𝔪` have finite index among the elements that are units
at the primes dividing the finite part.**  This relative finite index is the arithmetic content
behind the finiteness of the ray class group. -/
instance congruenceSubgroup_finiteIndex (𝔪 : Modulus K) :
    ((congruenceSubgroup 𝔪).subgroupOf (primeToSubgroup 𝔪)).FiniteIndex := by
  let _ : NeZero 𝔪.finitePart := ⟨𝔪.finitePart_ne_bot⟩
  have hker : (residueHom 𝔪).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  have hle : (residueHom 𝔪).ker ⊓
      (totallyPositiveUnits.subgroupOf (primeToSubgroup 𝔪)) ≤
        (congruenceSubgroup 𝔪).subgroupOf (primeToSubgroup 𝔪) := by
    rintro ⟨x, hx⟩ ⟨h1, h2⟩
    refine Subgroup.mem_subgroupOf.mpr (mem_congruenceSubgroup.mpr ?_)
    refine isCongrOne_of_residue_eq_one hx ?_
      fun w _ ↦ isTotallyPositive_iff.mp (mem_totallyPositiveUnits.mp h2) w.1 w.2
    rw [← coe_residueHom 𝔪 ⟨x, hx⟩, MonoidHom.mem_ker.mp h1, Units.val_one]
  exact Subgroup.finiteIndex_of_le hle

/-- The image of an integer unit is a unit at every finite place, hence lies in
`primeToSubgroup 𝔪`. -/
private theorem unitsMap_mem_primeToSubgroup (𝔪 : Modulus K) (u : (𝓞 K)ˣ) :
    Units.map (algebraMap (𝓞 K) K).toMonoidHom u ∈ primeToSubgroup 𝔪 := by
  refine mem_primeToSubgroup.mpr fun v _ ↦ ?_
  rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, valuation_of_algebraMap]
  refine intValuation_eq_one_iff.mpr fun hu ↦ v.isPrime.ne_top ?_
  exact Ideal.eq_top_of_isUnit_mem _ hu u.isUnit

/-- The inclusion of the integer units into the elements that are units at the finite part. -/
private noncomputable def unitsToPrimeToSubgroup (𝔪 : Modulus K) :
    (𝓞 K)ˣ →* primeToSubgroup 𝔪 :=
  MonoidHom.codRestrict (Units.map (algebraMap (𝓞 K) K).toMonoidHom) _
    (unitsMap_mem_primeToSubgroup 𝔪)

@[simp] private theorem coe_unitsToPrimeToSubgroup (𝔪 : Modulus K) (u : (𝓞 K)ˣ) :
    ((unitsToPrimeToSubgroup 𝔪 u : primeToSubgroup 𝔪) : Kˣ) =
      Units.map (algebraMap (𝓞 K) K).toMonoidHom u := by
  rw [unitsToPrimeToSubgroup, MonoidHom.codRestrict_apply]

/-- **The units congruent to one modulo `𝔪` have finite index in `(𝓞 K)ˣ`.**  This is the unit
correction in the ray class number formula, and the input that makes the implied constants of the
ray-class ideal count uniform in the class. -/
instance unitsCongruenceSubgroup_finiteIndex (𝔪 : Modulus K) :
    (unitsCongruenceSubgroup 𝔪).FiniteIndex := by
  have hcomap : ((congruenceSubgroup 𝔪).subgroupOf (primeToSubgroup 𝔪)).comap
      (unitsToPrimeToSubgroup 𝔪) = unitsCongruenceSubgroup 𝔪 := by
    ext u
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, mem_unitsCongruenceSubgroup,
      mem_congruenceSubgroup, coe_unitsToPrimeToSubgroup]
  rw [← hcomap]
  infer_instance

/-! ### Finiteness of the ray class group -/

/-- The class of an invertible fractional ideal prime to `𝔪` in the group of invertible fractional
ideals modulo the principal ones.  Its kernel is the group of principal ideals prime to `𝔪`, and
its range lies in a finite group. -/
private noncomputable def classHom (𝔪 : Modulus K) :
    idealsPrimeTo 𝔪 →* (FractionalIdeal (𝓞 K)⁰ K)ˣ ⧸ (toPrincipalIdeal (𝓞 K) K).range :=
  (QuotientGroup.mk' _).comp (idealsPrimeTo 𝔪).subtype

/-- The invertible fractional ideals modulo the principal ones form a finite group: this is the
class group of `𝓞 K` in a different presentation. -/
private instance instFiniteQuotientPrincipal :
    Finite ((FractionalIdeal (𝓞 K)⁰ K)ˣ ⧸ (toPrincipalIdeal (𝓞 K) K).range) :=
  Finite.of_equiv _ (ClassGroup.equiv (R := 𝓞 K) K).toEquiv

/-- The principal ideal of an element that is a unit at the finite part, viewed among the ideals
prime to the modulus. -/
private noncomputable def principalIdealPrimeToHom (𝔪 : Modulus K) :
    primeToSubgroup 𝔪 →* idealsPrimeTo 𝔪 :=
  MonoidHom.codRestrict ((toPrincipalIdeal (𝓞 K) K).comp (primeToSubgroup 𝔪).subtype)
    (idealsPrimeTo 𝔪) fun x ↦ toPrincipalIdeal_mem_idealsPrimeTo_iff.mpr x.2

@[simp] private theorem coe_principalIdealPrimeToHom (𝔪 : Modulus K)
    (x : primeToSubgroup 𝔪) :
    ((principalIdealPrimeToHom 𝔪 x : idealsPrimeTo 𝔪) :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      toPrincipalIdeal (𝓞 K) K (x : Kˣ) := by
  simp only [principalIdealPrimeToHom, MonoidHom.codRestrict_apply, MonoidHom.comp_apply,
    Subgroup.subtype_apply]

/-- The principal ideal of an element that is a unit at the finite part, viewed in the kernel of
`classHom`. -/
private noncomputable def principalIdealHom (𝔪 : Modulus K) :
    primeToSubgroup 𝔪 →* (classHom 𝔪).ker :=
  MonoidHom.codRestrict (principalIdealPrimeToHom 𝔪) (classHom 𝔪).ker fun x ↦ by
      rw [MonoidHom.mem_ker, classHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact ⟨(x : Kˣ), (coe_principalIdealPrimeToHom 𝔪 x).symm⟩

@[simp] private theorem coe_principalIdealHom (𝔪 : Modulus K) (x : primeToSubgroup 𝔪) :
    (((principalIdealHom 𝔪 x : (classHom 𝔪).ker) : idealsPrimeTo 𝔪) :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      toPrincipalIdeal (𝓞 K) K (x : Kˣ) := by
  rw [principalIdealHom, MonoidHom.codRestrict_apply, coe_principalIdealPrimeToHom]

private theorem principalIdealHom_surjective (𝔪 : Modulus K) :
    Function.Surjective (principalIdealHom 𝔪) := by
  rintro ⟨⟨I, hI⟩, hker⟩
  rw [MonoidHom.mem_ker, classHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, MonoidHom.mem_range] at hker
  obtain ⟨x, hx⟩ := hker
  refine ⟨⟨x, toPrincipalIdeal_mem_idealsPrimeTo_iff.mp (hx ▸ hI)⟩, ?_⟩
  exact Subtype.ext (Subtype.ext hx)

/-- **The ray has finite index in the invertible fractional ideals prime to `𝔪`.**  This index is
the ray class number, and its finiteness is what makes `RayClassGroup 𝔪` a finite group. -/
instance finiteIndex_ray (𝔪 : Modulus K) : (ray 𝔪).FiniteIndex := by
  refine ⟨?_⟩
  have hle : ray 𝔪 ≤ (classHom 𝔪).ker := by
    intro I hI
    obtain ⟨x, _, hxI⟩ := mem_ray_iff.mp hI
    rw [MonoidHom.mem_ker, classHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact ⟨x, hxI⟩
  let _ : (classHom 𝔪).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  have hkerindex : (classHom 𝔪).ker.index ≠ 0 :=
    Subgroup.FiniteIndex.index_ne_zero
  have hrel : (ray 𝔪).relIndex (classHom 𝔪).ker ≠ 0 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    refine Nat.card_ne_zero.mpr ⟨⟨1⟩, ?_⟩
    have hsurj : Function.Surjective
        ((QuotientGroup.mk' ((ray 𝔪).subgroupOf (classHom 𝔪).ker)).comp
          (principalIdealHom 𝔪)) :=
      (QuotientGroup.mk'_surjective _).comp (principalIdealHom_surjective 𝔪)
    have hkerle : ∀ x ∈ (congruenceSubgroup 𝔪).subgroupOf (primeToSubgroup 𝔪),
        ((QuotientGroup.mk' ((ray 𝔪).subgroupOf (classHom 𝔪).ker)).comp
          (principalIdealHom 𝔪)) x = 1 := by
      intro x hxmem
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf]
      exact mem_ray_iff.mpr
        ⟨(x : Kˣ), mem_congruenceSubgroup.mp (Subgroup.mem_subgroupOf.mp hxmem),
          (coe_principalIdealHom 𝔪 x).symm⟩
    refine Finite.of_surjective (QuotientGroup.lift _ _ hkerle) fun z ↦ ?_
    obtain ⟨y, hy⟩ := hsurj z
    exact ⟨QuotientGroup.mk y, hy⟩
  rw [← Subgroup.relIndex_mul_index hle]
  exact mul_ne_zero hrel hkerindex

/-- **The ray class group of a modulus is finite.**  This is the finiteness underlying the ray class
number, and what makes a ray class character a character of a finite abelian group. -/
instance finite_rayClassGroup (𝔪 : Modulus K) : Finite (RayClassGroup 𝔪) := by
  have hquot : Finite (idealsPrimeTo 𝔪 ⧸ ray 𝔪) := Subgroup.finite_quotient_of_finiteIndex
  refine Finite.of_surjective
    (QuotientGroup.lift (ray 𝔪) (rayClassMk 𝔪) fun x hx ↦ rayClassMk_eq_one_iff.mpr hx)
    fun c ↦ ?_
  obtain ⟨I, hI⟩ := rayClassMk_surjective 𝔪 c
  exact ⟨QuotientGroup.mk I, hI⟩

end TauCeti.GlobalNumberFields
