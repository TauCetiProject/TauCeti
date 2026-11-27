/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuartic.OrbitWeight
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ProjGenLinGroup.Cartan
public import TauCeti.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Integral translates of binary quartics over a discrete valuation ring

If an integral quartic has an integral translate in the Cartan double coset of
`diag(1, ϖᵏ)`, then `ϖ²ᵏ` divides its discriminant. This bounds the possible double cosets
for a nonsingular quartic, and shows that its local orbit weight is one whenever the
discriminant is not divisible by the square of the uniformizer.

## References

* M. Bhargava and A. Shankar, *Binary quartic forms having bounded invariants, and the
  boundedness of the average rank of elliptic curves*, Ann. of Math. 181 (2015),
  proof of Proposition 3.18.
-/

public section

open Matrix DoubleCoset
open scoped MatrixGroups

namespace TauCeti.BinaryQuartic

variable {R : Type*} [CommRing R]

/-- For a diagonal translate to have coefficients in the source ring, it is necessary
and sufficient that `r²` divide the leading coefficient and `r` divide the next coefficient,
where `r` maps to the unit `u` defining the diagonal. -/
theorem mk_diagGL_smul_mem_coefficientRange_iff {S : Type*} [CommRing S]
    {φ : R →+* S} (hφ : Function.Injective φ) {r : R} {u : Sˣ}
    (hu : φ r = u) (f : BinaryQuartic R) :
    ProjGenLinGroup.mk (diagGL ![1, u]) • (φ ∘ f) ∈ coefficientRange φ ↔
      r ^ 2 ∣ f 0 ∧ r ∣ f 1 := by
  rw [coefficientRange_eq_range]
  have hcoeff := sq_mul_mk_diagGL_smul_apply u (φ ∘ f)
  constructor
  · rintro ⟨q, hq⟩
    have h (i : Fin 5) := (congrArg ((u : S) ^ 2 * ·) (congrFun hq i)).trans (hcoeff i)
    constructor
    · refine ⟨q 0, hφ ?_⟩
      simpa only [map_mul, map_pow, hu, Function.comp_apply, Fin.val_zero, pow_zero, one_mul]
        using (h 0).symm
    · refine ⟨q 1, hφ ?_⟩
      rw [map_mul, hu]
      apply u.mul_right_inj.mp
      simpa only [Function.comp_apply, Fin.val_one, pow_one, pow_two, mul_assoc]
        using (h 1).symm
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨![a, b, f 2, r * f 3, r ^ 2 * f 4], funext fun i ↦ ?_⟩
    apply (u.isUnit.pow 2).mul_right_inj.mp
    rw [hcoeff i]
    fin_cases i <;> simp [ha, hb, hu, Function.comp_apply] <;> ring

/-- If a projective translate of an integral quartic is integral and the translating element
lies in the double coset of `diag(1, π ^ k)`, then `ϖ ^ (k * 2)` divides the discriminant,
where the coefficient map sends `ϖ` to the unit `π`. -/
theorem pow_mul_two_dvd_disc_of_mem_doubleCoset {S : Type*} [CommRing S]
    {φ : R →+* S} (hφ : Function.Injective φ) {ϖ : R} {π : Sˣ}
    (hπ : φ ϖ = π) {k : ℕ} {g : PGL(2, S)} (f : BinaryQuartic R)
    (hg : g ∈ doubleCoset (ProjGenLinGroup.mk (diagGL ![1, π ^ k]))
      (GeneralLinearGroup.map (n := Fin 2) φ).projectiveImage
      (GeneralLinearGroup.map (n := Fin 2) φ).projectiveImage)
    (hf : g • (φ ∘ f) ∈ coefficientRange φ) :
    ϖ ^ (k * 2) ∣ f.disc := by
  obtain ⟨l, hl, r, hr, rfl⟩ := mem_doubleCoset.mp hg
  obtain ⟨a, rfl⟩ := (MonoidHom.mem_projectiveImage _).mp hr
  have htranslate := (smul_mem_coefficientRange_iff hl _).mp (by
    simpa only [mul_smul] using hf)
  rw [← ProjGenLinGroup.map_mk, projGenLinGroup_map_smul_comp] at htranslate
  rw [pow_mul, ← disc_smul_projGenLinGroup (ProjGenLinGroup.mk a) f]
  have h := (mk_diagGL_smul_mem_coefficientRange_iff (r := ϖ ^ k) hφ
    (by simp [map_pow, hπ]) _).mp htranslate
  exact dvd_disc_of_dvd_coeff_zero_of_dvd_sq_coeff_one h.1 (pow_dvd_pow_of_dvd h.2 2)

section FractionField

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- Away from square divisibility of the discriminant, the only projective elements
that take an integral form to an integral form are in the integral projective subgroup. -/
theorem smul_mem_coefficientRange_iff_of_not_sq_dvd_disc {ϖ : R} (hϖ : Irreducible ϖ)
    (f : BinaryQuartic R) (hf : ¬ϖ ^ 2 ∣ f.disc) (g : PGL(2, K)) :
    g • (algebraMap R K ∘ f) ∈ coefficientRange (algebraMap R K) ↔
      g ∈ (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).projectiveImage := by
  let π := Units.mk0 (algebraMap R K ϖ)
    (map_ne_zero_iff _ (IsFractionRing.injective R K) |>.2 hϖ.ne_zero)
  have hπ : algebraMap R K ϖ = π := rfl
  refine ⟨fun hg ↦ ?_, fun hg ↦ (smul_mem_coefficientRange_iff hg _).mpr
    (comp_mem_coefficientRange _ _)⟩
  obtain ⟨k, hk⟩ := exists_mem_doubleCoset_mk_diagGL_pow hϖ hπ g
  rcases k with _ | k
  · rwa [doubleCoset_mk_diagGL_pow_zero] at hk
  · have hdiv := pow_mul_two_dvd_disc_of_mem_doubleCoset (IsFractionRing.injective R K) hπ f hk hg
    exact (hf ((pow_dvd_pow ϖ (by omega)).trans hdiv)).elim

/-- For a nonsingular integral quartic over a DVR with finite residue field, the set of
right cosets that admit an integral translate is finite. -/
theorem finite_orbitWeightCosets_of_disc_ne_zero [Finite (IsLocalRing.ResidueField R)]
    {ϖ : R} (hϖ : Irreducible ϖ) (f : BinaryQuartic R) (hf : f.disc ≠ 0) :
    ((GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).projectiveImage.orbitWeightCosets
      (coefficientRange (algebraMap R K)) (algebraMap R K ∘ f)).Finite := by
  let π := Units.mk0 (algebraMap R K ϖ)
    (map_ne_zero_iff _ (IsFractionRing.injective R K) |>.2 hϖ.ne_zero)
  have hπ : algebraMap R K ϖ = π := rfl
  let Γ := (GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).projectiveImage
  let mk := Quotient.mk (QuotientGroup.rightRel Γ)
  let cosets (k : ℕ) := mk '' doubleCoset (ProjGenLinGroup.mk (diagGL ![1, π ^ k])) Γ Γ
  have hfinite (k : ℕ) : (cosets k).Finite := by
    rcases eq_or_ne k 0 with rfl | hk
    · have hzero : cosets 0 = mk '' (Γ : Set PGL(2, K)) := by
        exact congrArg (Set.image mk) (doubleCoset_mk_diagGL_pow_zero (R := R) (π := π))
      rw [hzero]
      apply (Set.finite_singleton (mk 1)).subset
      rintro _ ⟨g, hg, rfl⟩
      exact Set.mem_singleton_iff.mpr (Quotient.sound
        (QuotientGroup.rightRel_apply.mpr (by simpa using Γ.inv_mem hg)))
    · have hcard := natCard_image_mk_rightRel_doubleCoset_mk_diagGL_pow hϖ hπ hk
      have hq : Nat.card (IsLocalRing.ResidueField R) ≠ 0 := Nat.card_pos.ne'
      have : Finite (cosets k) := Nat.finite_of_card_ne_zero <|
        hcard.trans_ne (mul_ne_zero (pow_ne_zero _ hq) (by omega))
      exact Set.toFinite _
  refine ((Set.finite_le_nat (multiplicity ϖ f.disc)).biUnion
    (fun k _ ↦ hfinite k)).subset ?_
  intro c hc
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_orbitWeightCosets.mp hc
  obtain ⟨k, hk⟩ := exists_mem_doubleCoset_mk_diagGL_pow hϖ hπ g
  have hdiv := pow_mul_two_dvd_disc_of_mem_doubleCoset (IsFractionRing.injective R K) hπ f hk hg
  have hmul : FiniteMultiplicity ϖ f.disc := .of_not_isUnit hϖ.not_isUnit hf
  have hk' : k * 2 ≤ multiplicity ϖ f.disc := hmul.pow_dvd_iff_le_multiplicity.mp hdiv
  exact Set.mem_iUnion₂.mpr ⟨k, Nat.le_trans (by omega : k ≤ k * 2) hk', ⟨g, hk, rfl⟩⟩

/-- The local orbit weight is positive for a nonsingular integral form over a DVR
with finite residue field. -/
theorem integralOrbitWeight_pos_of_disc_ne_zero [Finite (IsLocalRing.ResidueField R)]
    {ϖ : R} (hϖ : Irreducible ϖ) (f : BinaryQuartic R) (hf : f.disc ≠ 0) :
    0 < integralOrbitWeight (algebraMap R K ∘ f) (algebraMap R K) := by
  rw [integralOrbitWeight_def]
  exact Subgroup.orbitWeight_pos (comp_mem_coefficientRange _ _)
    (finite_orbitWeightCosets_of_disc_ne_zero hϖ f hf)

/-- The local orbit weight is one if the square of a uniformizer does not divide the
discriminant. -/
theorem integralOrbitWeight_eq_one_of_not_sq_dvd_disc {ϖ : R} (hϖ : Irreducible ϖ)
    (f : BinaryQuartic R) (hf : ¬ϖ ^ 2 ∣ f.disc) :
    integralOrbitWeight (algebraMap R K ∘ f) (algebraMap R K) = 1 := by
  rw [integralOrbitWeight_eq_one_iff (comp_mem_coefficientRange _ _)]
  ext g
  exact smul_mem_coefficientRange_iff_of_not_sq_dvd_disc hϖ f hf g

end FractionField

/-- At any prime `p`, a nonsingular integral quartic has only finitely many local
right cosets of integral translates. -/
theorem finite_padic_orbitWeightCosets_of_disc_ne_zero {p : ℕ} [Fact p.Prime]
    (f : BinaryQuartic ℤ_[p]) (hf : f.disc ≠ 0) :
    ((GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[p] ℚ_[p])).projectiveImage
      |>.orbitWeightCosets
      (coefficientRange (algebraMap ℤ_[p] ℚ_[p])) (algebraMap ℤ_[p] ℚ_[p] ∘ f)).Finite :=
  finite_orbitWeightCosets_of_disc_ne_zero PadicInt.irreducible_p f hf

/-- At any prime `p`, the local orbit weight is one if `p²` does not divide the discriminant. -/
theorem integralOrbitWeight_padic_eq_one_of_not_sq_dvd_disc {p : ℕ} [Fact p.Prime]
    (f : BinaryQuartic ℤ_[p]) (hf : ¬(p : ℤ_[p]) ^ 2 ∣ f.disc) :
    integralOrbitWeight (algebraMap ℤ_[p] ℚ_[p] ∘ f) (algebraMap ℤ_[p] ℚ_[p]) = 1 :=
  integralOrbitWeight_eq_one_of_not_sq_dvd_disc PadicInt.irreducible_p f hf

end TauCeti.BinaryQuartic
