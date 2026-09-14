/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

import TauCeti.RingTheory.Ideal.Quotient.Representative

/-!
# Reduction modulo the finite part of a modulus

For a modulus `𝔪` of a number field `K`, this file constructs the reduction homomorphism from
the elements of `Kˣ` that are units at the primes dividing `𝔪.finitePart` to the units of
`𝓞 K ⧸ 𝔪.finitePart`.

An element `x` in `primeToSubgroup 𝔪` can be written as `x = a / b` with the denominator
congruent to one modulo the finite part. The class of `a` modulo `𝔪.finitePart` is independent
of this presentation and defines `residueHom 𝔪`. Its kernel records exactly the finite-place
conditions in `IsCongrOne`, and every residue unit is attained: a nonzero integral representative
of a unit class is already prime to the finite part, so it is itself a field unit reducing to that
class.

## Main definitions

* `TauCeti.GlobalNumberFields.residue`, `TauCeti.GlobalNumberFields.residueHom`: reduction of an
  element that is a unit at the finite part of `𝔪` to the residue units modulo that finite part.
* `TauCeti.GlobalNumberFields.finiteUnitsMap`: the transition map on residue units when the
  modulus grows.

## Main results

* `TauCeti.GlobalNumberFields.exists_algebraMap_eq_mul_of_mem_primeToSubgroup`: a prime-to element
  has a denominator congruent to one modulo the finite part.
* `TauCeti.GlobalNumberFields.residue_eq_one_iff`: reduction to one is equivalent to the
  finite-place conditions in `IsCongrOne`.
* `TauCeti.GlobalNumberFields.residueHom_eq_one_of_mem_congruenceSubgroup`: an element congruent to
  one maps to one under reduction.
* `TauCeti.GlobalNumberFields.residueHom_surjective`: every residue unit modulo the finite part is
  the reduction of an element of `Kˣ` that is a unit at that finite part.
* `TauCeti.GlobalNumberFields.finiteUnitsMap_refl` and
  `TauCeti.GlobalNumberFields.finiteUnitsMap_comp_finiteUnitsMap`: the transition maps are
  functorial in finite-part divisibility.
* `TauCeti.GlobalNumberFields.finiteUnitsMap_residueHom`: reduction commutes with changing the
  modulus.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
* `TauCetiRoadmap/GlobalNumberFields/Suggested.lean` (`GlobalNumberFields.finiteUnitsMap`).
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

/-! ### Surjectivity of the reduction -/

/-- An integral representative of a *unit* residue class lies outside every prime dividing the
finite part: a common prime factor would make `1` divisible by that prime. -/
private theorem notMem_of_quotient_mk_eq_unit {𝔪 : Modulus K} {a : 𝓞 K}
    {u : (𝓞 K ⧸ 𝔪.finitePart)ˣ} (ha : Ideal.Quotient.mk 𝔪.finitePart a = u)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ 𝔪.finitePart) : a ∉ v.asIdeal := by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (𝓞 K ⧸ 𝔪.finitePart)ˣ) :
    𝓞 K ⧸ 𝔪.finitePart)
  have hab : a * b - 1 ∈ 𝔪.finitePart := by
    refine Ideal.Quotient.eq.mp ?_
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  intro hav
  refine v.isPrime.ne_top (Ideal.eq_top_iff_one _ |>.mpr ?_)
  have hone : (1 : 𝓞 K) = a * b - (a * b - 1) := by ring
  rw [hone]
  exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hav) (Ideal.le_of_dvd hv hab)

/-- **Every residue unit modulo the finite part is the reduction of a field unit prime to it.**
This is what makes the residue-unit factor of the ray class number formula the *whole* of
`(𝓞 K ⧸ 𝔪.finitePart)ˣ` rather than the image of the algebraic integers prime to `𝔪`.

A nonzero integral representative of the class does the job by itself: being a unit residue it
avoids every prime dividing the finite part, so its image in `Kˣ` lies in `primeToSubgroup 𝔪` and
reduces back to the class. -/
theorem residueHom_surjective (𝔪 : Modulus K) : Function.Surjective (residueHom 𝔪) := fun u ↦ by
  obtain ⟨a, ha0, ha⟩ := Ideal.Quotient.exists_ne_zero_mk_eq 𝔪.finitePart_ne_bot
    ((u : 𝓞 K ⧸ 𝔪.finitePart))
  have haK : algebraMap (𝓞 K) K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha0
  have hmem : Units.mk0 _ haK ∈ primeToSubgroup 𝔪 := mem_primeToSubgroup.mpr fun v hv ↦ by
    rw [Units.val_mk0, valuation_of_algebraMap]
    exact intValuation_eq_one_iff.mpr (notMem_of_quotient_mk_eq_unit ha hv)
  refine ⟨⟨_, hmem⟩, Units.ext ?_⟩
  rw [coe_residueHom, residue_eq (a := a) (b := 1) _ (by simp) (by simp), ha]

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
  obtain ⟨a, b, hb, hab⟩ := exists_algebraMap_eq_mul_of_mem_primeToSubgroup x.2
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
