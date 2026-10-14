/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.SInteger.Basic
import TauCeti.RingTheory.Ideal.CoprimeCoset

/-!
# Reduction of locally integral elements modulo an ideal

Let `R` be a Dedekind domain with fraction field `K` and `I` an ideal. An element of `K`
integral at every prime dividing `I` admits a denominator congruent to one modulo `I`.
Its numerator therefore has a well-defined residue class modulo `I`.

`Ideal.sIntegerToQuotient` packages this reduction as a surjective ring homomorphism from
Mathlib's ring of `S`-integers, where `S` is the complement of the primes dividing `I`,
to `R ⧸ I`. Its kernel is the extension of `I`. Its restriction to units enters the
ray-class exact sequence, without imposing a number-field or finite-residue-ring hypothesis.

The denominator argument uses `IsDedekindDomain.denIdeal_not_le`: local integrality makes
the denominator ideal coprime to `I`. The construction includes the unit ideal, where the
residue ring is the zero ring. The numerator construction generalizes the existing
`TauCeti.GlobalNumberFields.residueHom` for number-field moduli.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section
noncomputable section

open IsDedekindDomain

namespace Ideal

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- An element integral at the primes dividing `I` has a denominator congruent to one
modulo `I`. The numerator and denominator need not be globally invertible. -/
theorem exists_algebraMap_eq_mul_of_valuation_le_one (I : Ideal R) {x : K}
    (hx : ∀ v : HeightOneSpectrum R, v.asIdeal ∣ I → v.valuation K x ≤ 1) :
    ∃ a b : R, b - 1 ∈ I ∧ algebraMap R K a = algebraMap R K b * x := by
  have hcop : IsCoprime (Algebra.denIdeal K x) I := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ h
    have hden : Algebra.denIdeal K x ≤ P := le_sup_left.trans hle
    have hP0 : P ≠ ⊥ := fun h0 ↦
      Algebra.denIdeal_ne_bot K x (le_bot_iff.mp (h0 ▸ hden))
    let v : HeightOneSpectrum R := ⟨P, hP.isPrime, hP0⟩
    exact denIdeal_not_le K (hx v (Ideal.dvd_iff_le.mpr (le_sup_right.trans hle))) hden
  obtain ⟨b, hb, hbI⟩ := Ideal.isCoprime_iff_exists_mem_and_sub_one_mem.mp hcop
  obtain ⟨a, ha⟩ := (Algebra.mem_denIdeal_iff K).mp hb
  exact ⟨a, b, hbI, ha.symm⟩

private def sIntegerResidue (I : Ideal R)
    (x : ({v : HeightOneSpectrum R | v.asIdeal ∣ I}ᶜ).integer K) : R ⧸ I :=
  Ideal.Quotient.mk I (I.exists_algebraMap_eq_mul_of_valuation_le_one
    (fun v hv ↦ x.2 v (by simpa using hv))).choose

private theorem exists_sIntegerResidue_eq (I : Ideal R)
    (x : ({v : HeightOneSpectrum R | v.asIdeal ∣ I}ᶜ).integer K) :
    ∃ a b : R, b - 1 ∈ I ∧ algebraMap R K a = algebraMap R K b * (x : K) ∧
      sIntegerResidue I x = Ideal.Quotient.mk I a := by
  obtain ⟨b, hb, hab⟩ := (I.exists_algebraMap_eq_mul_of_valuation_le_one
    (fun v hv ↦ x.2 v (by simpa using hv))).choose_spec
  exact ⟨_, b, hb, hab, rfl⟩

private theorem sIntegerResidue_eq (I : Ideal R)
    (x : ({v : HeightOneSpectrum R | v.asIdeal ∣ I}ᶜ).integer K) {a b : R}
    (hb : b - 1 ∈ I) (hab : algebraMap R K a = algebraMap R K b * (x : K)) :
    sIntegerResidue I x = Ideal.Quotient.mk I a := by
  obtain ⟨a', b', hb', hab', hr⟩ := exists_sIntegerResidue_eq I x
  have hmk {y : R} (hy : y - 1 ∈ I) : Ideal.Quotient.mk I y = 1 := by
    rw [← map_one (Ideal.Quotient.mk I)]
    exact Ideal.Quotient.eq.mpr hy
  have key : a * b' = a' * b :=
    IsFractionRing.injective R K (by rw [map_mul, map_mul, hab, hab']; ring)
  have h := congrArg (Ideal.Quotient.mk I) key
  rw [map_mul, map_mul, hmk hb, hmk hb', mul_one, mul_one] at h
  exact hr.trans h.symm

/-- Reduction modulo `I` on the ring of fraction-field elements integral at all primes
dividing `I`. Its kernel is the extension of `I` to that ring. -/
def sIntegerToQuotient (I : Ideal R) :
    ({v : HeightOneSpectrum R | v.asIdeal ∣ I}ᶜ).integer K →+* R ⧸ I where
  toFun := sIntegerResidue I
  map_zero' := by
    rw [sIntegerResidue_eq I 0 (a := 0) (b := 1) (by simp) (by simp), map_zero]
  map_one' := by
    rw [sIntegerResidue_eq I 1 (a := 1) (b := 1) (by simp) (by simp), map_one]
  map_add' x y := by
    obtain ⟨a, b, hb, hab, hr⟩ := exists_sIntegerResidue_eq I x
    obtain ⟨c, d, hd, hcd, hs⟩ := exists_sIntegerResidue_eq I y
    have hbd : b * d - 1 ∈ I := by
      have heq : b * d - 1 = (b - 1) * d + (d - 1) := by ring
      rw [heq]
      exact I.add_mem (I.mul_mem_right _ hb) hd
    rw [sIntegerResidue_eq I (x + y) (a := a * d + c * b) (b := b * d) hbd
      (by simp only [map_add, map_mul, Subalgebra.coe_add, hab, hcd]; ring),
      map_add, map_mul, map_mul, ← hr, ← hs]
    have hbm : Ideal.Quotient.mk I b = 1 := by
      simpa using (Ideal.Quotient.eq.mpr hb : Ideal.Quotient.mk I b = Ideal.Quotient.mk I 1)
    have hdm : Ideal.Quotient.mk I d = 1 := by
      simpa using (Ideal.Quotient.eq.mpr hd : Ideal.Quotient.mk I d = Ideal.Quotient.mk I 1)
    simp [hbm, hdm]
  map_mul' x y := by
    obtain ⟨a, b, hb, hab, hr⟩ := exists_sIntegerResidue_eq I x
    obtain ⟨c, d, hd, hcd, hs⟩ := exists_sIntegerResidue_eq I y
    have hbd : b * d - 1 ∈ I := by
      have heq : b * d - 1 = (b - 1) * d + (d - 1) := by ring
      rw [heq]
      exact I.add_mem (I.mul_mem_right _ hb) hd
    rw [sIntegerResidue_eq I (x * y) (a := a * c) (b := b * d) hbd
      (by simp only [map_mul, Subalgebra.coe_mul, hab, hcd]; ring), map_mul, hr, hs]

/-- Any denominator congruent to one computes the reduction. -/
theorem sIntegerToQuotient_eq (I : Ideal R)
    (x : ({v : HeightOneSpectrum R | v.asIdeal ∣ I}ᶜ).integer K) {a b : R}
    (hb : b - 1 ∈ I) (hab : algebraMap R K a = algebraMap R K b * (x : K)) :
    I.sIntegerToQuotient x = Ideal.Quotient.mk I a :=
  sIntegerResidue_eq I x hb hab

/-- On elements of the base ring, reduction is the ordinary quotient map. -/
@[simp]
theorem sIntegerToQuotient_algebraMap (I : Ideal R) (a : R) :
    I.sIntegerToQuotient (algebraMap R
      (({v : HeightOneSpectrum R | v.asIdeal ∣ I}ᶜ).integer K) a) = Ideal.Quotient.mk I a :=
  I.sIntegerToQuotient_eq _ (b := 1) (by simp) (by simp)

/-- Reduction from the locally integral ring onto the residue ring is surjective. -/
theorem sIntegerToQuotient_surjective (I : Ideal R) :
    Function.Surjective (I.sIntegerToQuotient (K := K)) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨algebraMap R _ a, I.sIntegerToQuotient_algebraMap a⟩

/-- The kernel of reduction is precisely the extension of the ideal. -/
@[simp]
theorem ker_sIntegerToQuotient (I : Ideal R) :
    RingHom.ker (I.sIntegerToQuotient (K := K)) = Ideal.map
      (algebraMap R (({v : HeightOneSpectrum R | v.asIdeal ∣ I}ᶜ).integer K)) I := by
  let A := ({v : HeightOneSpectrum R | v.asIdeal ∣ I}ᶜ).integer K
  let f := algebraMap R A
  have hle : Ideal.map f I ≤ RingHom.ker (I.sIntegerToQuotient (K := K)) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    simpa only [f, A, Ideal.mem_comap, RingHom.mem_ker, sIntegerToQuotient_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem] using ha
  refine le_antisymm (fun x hx ↦ ?_) hle
  obtain ⟨a, b, hb, hab, -⟩ := exists_sIntegerResidue_eq I x
  have ha : a ∈ I := by
    rw [RingHom.mem_ker, I.sIntegerToQuotient_eq x hb hab,
      Ideal.Quotient.eq_zero_iff_mem] at hx
    exact hx
  have habA : f a = f b * x := Subtype.ext (by simpa [f] using hab)
  have hax : f b * x ∈ Ideal.map f I := habA ▸ Ideal.mem_map_of_mem f ha
  have hbx : (f b - 1) * x ∈ Ideal.map f I := by
    rw [← map_one f, ← map_sub]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem f hb)
  have heq : f b * x - (f b - 1) * x = x := by ring
  exact heq ▸ Ideal.sub_mem _ hax hbx

/-- Every residue unit lifts to a unit of the locally integral ring.
The lift need not be a unit of the base ring. -/
theorem units_map_sIntegerToQuotient_surjective (I : Ideal R) :
    Function.Surjective (Units.map (I.sIntegerToQuotient (K := K)).toMonoidHom) := by
  by_cases hI : I = ⊤
  · subst I
    exact Function.surjective_to_subsingleton _
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  intro u
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : R ⧸ I)
  have ha0 : a ≠ 0 := fun h ↦ u.ne_zero (by rw [← ha, h, map_zero])
  have haK : algebraMap R K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha0
  have hav (v : HeightOneSpectrum R) (hv : v.asIdeal ∣ I) :
      v.valuation K (algebraMap R K a) = 1 := by
    let : v.asIdeal.IsMaximal := v.isMaximal
    have hu : IsUnit (Ideal.Quotient.mk v.asIdeal a) := by
      rw [← Ideal.Quotient.factor_mk (Ideal.le_of_dvd hv), ha]
      exact u.isUnit.map (Ideal.Quotient.factor (Ideal.le_of_dvd hv))
    exact v.valuation_eq_one_iff_notMem.mpr
      (fun h ↦ hu.ne_zero (Ideal.Quotient.eq_zero_iff_mem.mpr h))
  let z : ({v : HeightOneSpectrum R | v.asIdeal ∣ I}ᶜ).unit K :=
    ⟨Units.mk0 _ haK, fun v hv ↦ hav v (by simpa using hv)⟩
  refine ⟨Set.unitEquivUnitsInteger _ K z, Units.ext ?_⟩
  simp only [Units.coe_map]
  exact (I.sIntegerToQuotient_eq _ (b := 1) (by simp) (by simp [z])).trans ha

end Ideal
