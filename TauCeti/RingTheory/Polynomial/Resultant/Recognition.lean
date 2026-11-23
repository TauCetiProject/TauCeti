/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import TauCeti.RingTheory.Polynomial.Resultant.AdjoinRoot
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# Resultant recognition over a discrete valuation ring

A monic polynomial `P : O[X]` over a discrete valuation ring `O` is uniquely determined by the
valuations of its nonzero resultants `P.resultant (ψ.map φ)` against monic polynomials `ψ : D[X]`
lifted from a ring `D` whose image under `φ : D →+* O` is dense modulo every power of a
uniformizer `π`. No equal-degree, completeness, separability, characteristic-zero, or finite-
residue-field assumption is required.

The key mechanism is a shifted-factor test: for any monic `R : O[X]` of positive degree `d`,
if `ψ : O[X]` is monic of degree `d` and congruent to `R + C (π ^ n)` modulo `π ^ (2 * n)` with
`n ≥ 1`, then in `AdjoinRoot R` we have `mk R ψ = π ^ n * (1 + π ^ n * H)` for a polynomial
`H`, so its norm `R.resultant ψ` equals `π ^ (n * d) * u` for a unit `u ≡ 1 (mod π ^ n)` and
thus has additive valuation `n * d`. When `P = R ^ e * S` with `S.resultant R ≠ 0`, the second
factor `S.resultant ψ` stabilizes in valuation once `n > addVal O (S.resultant R)`, giving
`addVal O (P.resultant ψ) = n * d * e + addVal O (S.resultant R)`. Comparing slopes across two
large values of `n` recovers the multiplicity `e` of every monic irreducible factor over
`FractionRing O`.

## Main results

* `AdjoinRoot.norm_mk_one_add_sub_one_mem`: if `g : R[X]` is monic and every coefficient of `h`
  lies in an ideal `I`, then `Algebra.norm R (AdjoinRoot.mk g (1 + h)) - 1 ∈ I`.
* `Polynomial.exists_resultant_eq_pow_mul_of_coeff_mem_span_mul`: for monic `g`, if `ψ` has the
  same degree as `g` and `ψ - (g + C a)` has all coefficients in `Ideal.span {a * b}`, then
  `g.resultant ψ = a ^ g.natDegree * u` with `u - 1 ∈ Ideal.span {b}`.
* `Polynomial.resultant_sub_mem_of_coeff_sub_mem`: congruence of resultants modulo an arbitrary
  ideal.
* `Polynomial.exists_monic_map_sub_coeff_mem`: lifting a monic polynomial along a map surjective
  modulo an ideal while preserving the degree.
* `Polynomial.addVal_resultant_pow_mul_of_sub_add_C_pow_mem`: shifted-factor multiplicity slope
  formula over a discrete valuation ring.
* `Polynomial.resultantRecognition`: monic tests from a uniformizer-adically dense ring uniquely
  determine a monic polynomial over a discrete valuation ring.
-/

public section

noncomputable section

open Polynomial

namespace AdjoinRoot

/-- For monic `g : R[X]`, if every coefficient of `h` lies in an ideal `I`, then the norm of
`AdjoinRoot.mk g (1 + h)` over `R` is congruent to `1` modulo `I`. -/
theorem norm_mk_one_add_sub_one_mem {R : Type*} [CommRing R] {g h : R[X]} (hg : g.Monic)
    {I : Ideal R} (hh : ∀ i, h.coeff i ∈ I) :
    Algebra.norm R (mk g (1 + h)) - 1 ∈ I := by
  set q := Ideal.Quotient.mk I
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
  rcases subsingleton_or_nontrivial (R ⧸ I) with _ | _
  · exact Subsingleton.elim _ _
  have hmap : (1 + h).map q = 1 := by
    ext i
    simp [q, Ideal.Quotient.eq_zero_iff_mem.mpr (hh i)]
  rw [norm_mk_eq_resultant hg, ← resultant_map_map, hmap, resultant_one_right,
    ← hg.natDegree_map q, coeff_natDegree, (hg.map q).leadingCoeff, one_pow]

/-- For monic `g : R[X]`, the norm of `AdjoinRoot.mk g (C a)` over `R` is `a ^ g.natDegree`. -/
theorem norm_mk_C {R : Type*} [CommRing R] {g : R[X]} (hg : g.Monic) (a : R) :
    Algebra.norm R (mk g (C a)) = a ^ g.natDegree := by
  nontriviality R
  rw [mk_C, ← algebraMap_eq, Algebra.norm_algebraMap_of_basis (powerBasis' hg).basis]
  simp only [Fintype.card_fin]
  rfl

end AdjoinRoot

namespace Polynomial

section ArbitraryRing

variable {R : Type*} [CommRing R]

/-- **Resultant of a shifted monic factor.** For monic `g : R[X]` and an ideal `I : Ideal R`, if
`ψ = g + C a + C a * h` and all coefficients of `h` lie in `I`, then
`g.resultant ψ = a ^ g.natDegree * u` for some `u` congruent to `1` modulo `I`. -/
theorem exists_resultant_eq_pow_mul {g ψ h : R[X]} (hg : g.Monic) (a : R) {I : Ideal R}
    (hψ : ψ = g + C a + C a * h) (hh : ∀ i, h.coeff i ∈ I) :
    ∃ u : R, u - 1 ∈ I ∧ g.resultant ψ = a ^ g.natDegree * u := by
  refine ⟨Algebra.norm R (AdjoinRoot.mk g (1 + h)),
    AdjoinRoot.norm_mk_one_add_sub_one_mem hg hh, ?_⟩
  rw [← AdjoinRoot.norm_mk_C hg a, ← map_mul (Algebra.norm R), ← map_mul,
    ← AdjoinRoot.norm_mk_eq_resultant hg]
  congr 1
  have hrewrite : ψ = g + C a * (1 + h) := by rw [hψ]; ring
  rw [hrewrite, map_add, AdjoinRoot.mk_self, zero_add]

/-- **Resultant of a shifted monic factor modulo `a * b`.** If `g` is monic and every coefficient
of `ψ - (g + C a)` lies in `Ideal.span {a * b}`, then `g.resultant ψ = a ^ g.natDegree * u` for
some `u` with `u - 1 ∈ Ideal.span {b}`. -/
theorem exists_resultant_eq_pow_mul_of_coeff_mem_span_mul {g ψ : R[X]} (hg : g.Monic) (a b : R)
    (hψ : ∀ i, (ψ - (g + C a)).coeff i ∈ Ideal.span {a * b}) :
    ∃ u : R, u - 1 ∈ Ideal.span {b} ∧ g.resultant ψ = a ^ g.natDegree * u := by
  have hdvd : C (a * b) ∣ ψ - (g + C a) :=
    (C_dvd_iff_dvd_coeff _ _).mpr fun i ↦ Ideal.mem_span_singleton.mp (hψ i)
  obtain ⟨k, hk⟩ := hdvd
  have hrewrite : ψ = g + C a + C a * (C b * k) := by
    have := congrArg (· + (g + C a)) hk
    simpa [C_mul, mul_assoc, add_comm, add_left_comm, add_assoc] using this
  refine exists_resultant_eq_pow_mul hg a hrewrite fun i ↦ ?_
  rw [coeff_C_mul, Ideal.mem_span_singleton]
  exact dvd_mul_right b _

/-- **Resultant congruence modulo an arbitrary ideal.** If `ψ` and `g` have the same `natDegree`
and agree coefficientwise up to `g.natDegree` modulo `I`, then `f.resultant ψ - f.resultant g`
lies in `I` for every polynomial `f`. -/
theorem resultant_sub_mem_of_coeff_sub_mem (f : R[X]) {g ψ : R[X]} {I : Ideal R}
    (hdeg : ψ.natDegree = g.natDegree)
    (hsub : ∀ i ≤ g.natDegree, (ψ - g).coeff i ∈ I) :
    f.resultant ψ - f.resultant g ∈ I := by
  set q := Ideal.Quotient.mk I
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, ← resultant_map_map, ← hdeg,
    ← resultant_map_map]
  refine resultant_congr_of_coeff_eq (fun _ _ ↦ rfl) fun i hi ↦ ?_
  simp only [coeff_map]
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, ← coeff_sub]
  exact hsub i (hdeg ▸ hi)

/-- Multiplicativity of resultants in a product `f ^ e * g` of monic polynomials, taken at the
actual degrees. -/
theorem Monic.resultant_pow_mul_left {f g : R[X]} (hf : f.Monic) (hg : g.Monic) (e : ℕ)
    (ψ : R[X]) :
    (f ^ e * g).resultant ψ = f.resultant ψ ^ e * g.resultant ψ := by
  nontriviality R
  have hfe : (f ^ e).Monic := hf.pow e
  have hdeg : (f ^ e * g).natDegree = (f ^ e).natDegree + g.natDegree := hfe.natDegree_mul hg
  rw [hdeg, resultant_mul_left_of_natDegree_le le_rfl le_rfl le_rfl]
  congr 1
  refine resultant_pow_left _ _ _ _ ?_ le_rfl
  rw [hf.leadingCoeff, one_pow]
  exact one_ne_zero

end ArbitraryRing

section Lifting

/-- **Lifting a monic polynomial modulo an ideal.** If `φ : D →+* O` is surjective modulo an
ideal `I ≠ ⊤`, then any monic `T : O[X]` lifts to a monic `ψ : D[X]` of the same `natDegree`
such that `ψ.map φ - T` has all coefficients in `I`. -/
theorem exists_monic_map_sub_coeff_mem {D O : Type*} [CommRing D] [CommRing O] (φ : D →+* O)
    {I : Ideal O} (hI : I ≠ ⊤) (hφ : ∀ o : O, ∃ d : D, o - φ d ∈ I)
    {T : O[X]} (hT : T.Monic) :
    ∃ ψ : D[X], ψ.Monic ∧ ψ.natDegree = T.natDegree ∧
      ∀ i, (ψ.map φ - T).coeff i ∈ I := by
  let q := Ideal.Quotient.mk I
  have : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hlifts : T.map q ∈ lifts (q.comp φ) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    obtain ⟨d, hd⟩ := hφ (T.coeff i)
    refine ⟨d, ?_⟩
    rw [RingHom.comp_apply, coeff_map, eq_comm, ← sub_eq_zero, ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hd
  obtain ⟨ψ, hψ_map, hψ_deg, hψ_monic⟩ := lifts_and_natDegree_eq_and_monic hlifts (hT.map q)
  refine ⟨ψ, hψ_monic, hψ_deg.trans (hT.natDegree_map q), fun i ↦ ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, coeff_sub, map_sub, sub_eq_zero, ← coeff_map,
    ← coeff_map, map_map]
  exact congrArg (fun p : (O ⧸ I)[X] ↦ p.coeff i) hψ_map

end Lifting

section DVR

open IsDiscreteValuationRing

private theorem addVal_eq_of_lt_addVal_sub {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {x y : O} (h : addVal O x < addVal O (y - x)) :
    y ≠ 0 ∧ addVal O y = addVal O x := by
  have hy : y ≠ 0 := by
    rintro rfl
    rw [zero_sub, (addVal O).map_neg] at h
    exact lt_irrefl _ h
  refine ⟨hy, le_antisymm ?_ ?_⟩
  · by_contra! hlt
    have htri : min (addVal O y) (addVal O (y - x)) ≤ addVal O x := by
      have hx : x = y + -(y - x) := by ring
      conv_rhs => rw [hx]
      rw [← (addVal O).map_neg (y - x)]
      exact addVal_add
    exact not_le_of_gt (lt_min hlt h) htri
  · have hyeq : y = x + (y - x) := by ring
    calc
      addVal O x = min (addVal O x) (addVal O (y - x)) := (min_eq_left h.le).symm
      _ ≤ addVal O (x + (y - x)) := addVal_add
      _ = addVal O y := by rw [← hyeq]

private theorem isUnit_of_sub_one_mem_span_pow {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {π u : O} (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n)
    (hu : u - 1 ∈ Ideal.span {π ^ n}) : IsUnit u := by
  by_contra hnot
  have huM : u ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal u).mpr hnot
  have hπM : π ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal π).mpr hπ.not_isUnit
  have hspan : Ideal.span {π ^ n} ≤ IsLocalRing.maximalIdeal O :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.pow_mem_of_mem _ hπM n hn))
  have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    simpa using (IsLocalRing.maximalIdeal O).sub_mem huM (hspan hu)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

/-- For a monic polynomial `R : O[X]` over a discrete valuation ring `O` with uniformizer `π` and
`n ≥ 1`, any `ψ : O[X]` whose coefficients match `R + C (π ^ n)` modulo `π ^ (2 * n)` has
nonzero resultant with `R` of additive valuation `n * R.natDegree`. -/
theorem addVal_resultant_of_sub_add_C_pow_mem {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {π : O} (hπ : Irreducible π) {R ψ : O[X]} (hR : R.Monic)
    {n : ℕ} (hn : 1 ≤ n)
    (hψ : ∀ i, (ψ - (R + C (π ^ n))).coeff i ∈ Ideal.span {π ^ (2 * n)}) :
    R.resultant ψ ≠ 0 ∧ addVal O (R.resultant ψ) = (n * R.natDegree : ℕ) := by
  have hψ' : ∀ i, (ψ - (R + C (π ^ n))).coeff i ∈ Ideal.span {π ^ n * π ^ n} := by
    simpa [← pow_add, ← two_mul] using hψ
  obtain ⟨u, hu, hres⟩ :=
    exists_resultant_eq_pow_mul_of_coeff_mem_span_mul hR (π ^ n) (π ^ n) hψ'
  have hu_unit : IsUnit u := isUnit_of_sub_one_mem_span_pow hπ hn hu
  have hne : R.resultant ψ ≠ 0 := by
    rw [hres]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hπ.ne_zero)) hu_unit.ne_zero
  refine ⟨hne, ?_⟩
  have hval_u : addVal O u = 0 := addVal_eq_zero_iff.mpr hu_unit
  rw [hres, addVal_mul, hval_u, add_zero, ← pow_mul, hπ.addVal_pow]

/-- **Multiplicity detected by shifted factors.** Let `O` be a discrete valuation ring with
uniformizer `π`, and let `R, S : O[X]` be monic with `S.resultant R ≠ 0`. For `P = R ^ e * S`,
any `n ≥ 1` strictly larger than `addVal O (S.resultant R)`, and any monic `ψ : O[X]` of degree
`R.natDegree` congruent to `R + C (π ^ n)` modulo `π ^ (2 * n)`, we have `P.resultant ψ ≠ 0`
and `addVal O (P.resultant ψ) = (n * R.natDegree * e : ℕ) + addVal O (S.resultant R)`. -/
theorem addVal_resultant_pow_mul_of_sub_add_C_pow_mem {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {π : O} (hπ : Irreducible π) {R S ψ : O[X]} (hR : R.Monic)
    (hS : S.Monic) (e : ℕ) {n : ℕ} (hn : 1 ≤ n) (hlt : addVal O (S.resultant R) < n)
    (hdeg : ψ.natDegree = R.natDegree)
    (hψ : ∀ i, (ψ - (R + C (π ^ n))).coeff i ∈ Ideal.span {π ^ (2 * n)}) :
    (R ^ e * S).resultant ψ ≠ 0 ∧
      addVal O ((R ^ e * S).resultant ψ) =
        ((n * R.natDegree * e : ℕ) : ℕ∞) + addVal O (S.resultant R) := by
  have hR_val := addVal_resultant_of_sub_add_C_pow_mem hπ hR hn hψ
  have hsub : ∀ i ≤ R.natDegree, (ψ - R).coeff i ∈ Ideal.span {π ^ n} := by
    intro i _
    have hi : (ψ - (R + C (π ^ n))).coeff i ∈ Ideal.span {π ^ n} := by
      have hdiv : Ideal.span {π ^ (2 * n)} ≤ Ideal.span {π ^ n} :=
        Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_span_singleton.mpr
          (pow_dvd_pow π (by lia))))
      exact hdiv (hψ i)
    have hc : (C (π ^ n)).coeff i ∈ Ideal.span {π ^ n} := by
      rw [coeff_C]
      split_ifs
      · exact Ideal.subset_span rfl
      · exact Ideal.zero_mem _
    have heq : (ψ - R).coeff i = (ψ - (R + C (π ^ n))).coeff i + (C (π ^ n)).coeff i := by
      simp [sub_eq_add_neg, add_assoc]
    rw [heq]
    exact Ideal.add_mem _ hi hc
  have hS_diff : (n : ℕ∞) ≤ addVal O (S.resultant ψ - S.resultant R) := by
    have hmem := resultant_sub_mem_of_coeff_sub_mem S hdeg hsub
    rw [← hπ.addVal_pow n, addVal_le_iff_dvd]
    exact Ideal.mem_span_singleton.mp hmem
  have hS_val := addVal_eq_of_lt_addVal_sub (lt_of_lt_of_le hlt hS_diff)
  rw [hR.resultant_pow_mul_left hS e ψ]
  refine ⟨mul_ne_zero (pow_ne_zero e hR_val.1) hS_val.1, ?_⟩
  rw [addVal_mul, addVal_pow, hR_val.2, hS_val.2, nsmul_eq_mul, ← Nat.cast_mul, mul_comm e]

end DVR

section Recognition

private theorem exists_pow_mul_of_monic_irreducible_map {O K : Type*} [CommRing O]
    [IsIntegrallyClosed O] [Field K] [Algebra O K] [IsFractionRing O K] {R₀ : O[X]}
    (hR₀ : R₀.Monic) (hR₀_pos : 0 < R₀.natDegree) (F : O[X]) (hF : F.Monic) :
    ∃ e : ℕ, ∃ S : O[X], S.Monic ∧
      ¬ (R₀.map (algebraMap O K) ∣ S.map (algebraMap O K)) ∧ F = R₀ ^ e * S := by
  classical
  induction hdeg : F.natDegree using Nat.strong_induction_on generalizing F with
  | ind d ih =>
    by_cases hdvd : R₀.map (algebraMap O K) ∣ F.map (algebraMap O K)
    · obtain ⟨F₁, hF₁⟩ := hF.dvd_of_fraction_map_dvd_fraction_map hR₀ hdvd
      have hF₁_monic : F₁.Monic := Monic.of_mul_monic_left hR₀ (hF₁ ▸ hF)
      have hF₁_lt : F₁.natDegree < d := by
        have hsum : F.natDegree = R₀.natDegree + F₁.natDegree := by
          rw [hF₁, hR₀.natDegree_mul hF₁_monic]
        lia
      obtain ⟨e, S, hS_monic, hS_ndvd, hS_eq⟩ := ih F₁.natDegree hF₁_lt F₁ hF₁_monic rfl
      refine ⟨e + 1, S, hS_monic, hS_ndvd, ?_⟩
      rw [hF₁, hS_eq, pow_succ', mul_assoc]
    · exact ⟨0, F, hF, hdvd, by simp⟩

private theorem exists_factor_ne_multiplicity_aux {O K : Type*} [CommRing O]
    [IsIntegrallyClosed O] [Field K] [Algebra O K] [IsFractionRing O K]
    {X₁ X₂ : O[X]} (hX₁ : X₁.Monic) (hX₂ : X₂.Monic)
    {g A : K[X]} (hgA : X₁.map (algebraMap O K) = g * A)
    (hgcd : ∀ d : K[X],
      d ∣ X₁.map (algebraMap O K) → d ∣ X₂.map (algebraMap O K) → d ∣ g)
    (hA : ¬ IsUnit A) :
    ∃ R₀ : O[X], R₀.Monic ∧ Irreducible (R₀.map (algebraMap O K)) ∧
      ∃ e₁ e₂ : ℕ, ∃ S₁ S₂ : O[X], S₁.Monic ∧ S₂.Monic ∧
        ¬ (R₀.map (algebraMap O K) ∣ S₁.map (algebraMap O K)) ∧
        ¬ (R₀.map (algebraMap O K) ∣ S₂.map (algebraMap O K)) ∧
        X₁ = R₀ ^ e₁ * S₁ ∧ X₂ = R₀ ^ e₂ * S₂ ∧ e₁ ≠ e₂ := by
  classical
  let ι := algebraMap O K
  have hA0 : A ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hgA
    exact (hX₁.map ι).ne_zero hgA
  obtain ⟨R₁, hR₁_irr, hR₁_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hA hA0
  let R : K[X] := R₁ * C R₁.leadingCoeff⁻¹
  have hR_monic : R.Monic := monic_mul_leadingCoeff_inv hR₁_irr.ne_zero
  have hC_unit : IsUnit (C R₁.leadingCoeff⁻¹) :=
    isUnit_C.mpr (inv_ne_zero (leadingCoeff_ne_zero.mpr hR₁_irr.ne_zero)).isUnit
  have hR_assoc : Associated R₁ R := associated_mul_unit_right R₁ _ hC_unit
  have hR_irr : Irreducible R := hR_assoc.irreducible hR₁_irr
  have hR_dvd_A : R ∣ A := hR_assoc.dvd_iff_dvd_left.mp hR₁_dvd
  have hR_dvd_X₁ : R ∣ X₁.map ι := hgA ▸ hR_dvd_A.mul_left g
  obtain ⟨R₀, hR₀_map⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hX₁ hR_dvd_X₁
  rw [hR_monic.leadingCoeff, C_1, mul_one] at hR₀_map
  have hR₀_monic : R₀.Monic :=
    monic_of_injective (IsFractionRing.injective O K) (hR₀_map ▸ hR_monic)
  have hR₀_irr : Irreducible (R₀.map ι) := hR₀_map ▸ hR_irr
  have hR₀_pos : 0 < R₀.natDegree := by
    rw [← natDegree_map_eq_of_injective (IsFractionRing.injective O K)]
    exact hR₀_irr.natDegree_pos
  obtain ⟨e₁, S₁, hS₁_m, hS₁_ndvd, hX₁_eq⟩ :=
    exists_pow_mul_of_monic_irreducible_map (K := K) hR₀_monic hR₀_pos X₁ hX₁
  obtain ⟨e₂, S₂, hS₂_m, hS₂_ndvd, hX₂_eq⟩ :=
    exists_pow_mul_of_monic_irreducible_map (K := K) hR₀_monic hR₀_pos X₂ hX₂
  refine ⟨R₀, hR₀_monic, hR₀_irr, e₁, e₂, S₁, S₂,
    hS₁_m, hS₂_m, hS₁_ndvd, hS₂_ndvd, hX₁_eq, hX₂_eq, ?_⟩
  rintro rfl
  have hpow_dvd_g : R ^ e₁ ∣ g := by
    have hd1 : R ^ e₁ ∣ X₁.map ι := by
      rw [hX₁_eq, Polynomial.map_mul, Polynomial.map_pow, hR₀_map]
      exact dvd_mul_right _ _
    have hd2 : R ^ e₁ ∣ X₂.map ι := by
      rw [hX₂_eq, Polynomial.map_mul, Polynomial.map_pow, hR₀_map]
      exact dvd_mul_right _ _
    exact hgcd (R ^ e₁) hd1 hd2
  obtain ⟨g', rfl⟩ := hpow_dvd_g
  have heq : R ^ e₁ * S₁.map ι = R ^ e₁ * (g' * A) := by
    calc
      R ^ e₁ * S₁.map ι = (R₀ ^ e₁ * S₁).map ι := by
        rw [Polynomial.map_mul, Polynomial.map_pow, hR₀_map]
      _ = X₁.map ι := by rw [← hX₁_eq]
      _ = R ^ e₁ * (g' * A) := by rw [hgA, mul_assoc]
  have hS₁_eq := mul_left_cancel₀ (pow_ne_zero e₁ hR_monic.ne_zero) heq
  exact hS₁_ndvd (hR₀_map.symm ▸ hS₁_eq ▸ hR_dvd_A.mul_left g')

private theorem exists_factor_ne_multiplicity {O K : Type*} [CommRing O]
    [IsIntegrallyClosed O] [Field K] [Algebra O K] [IsFractionRing O K]
    {P Q : O[X]} (hP : P.Monic) (hQ : Q.Monic) (hne : P ≠ Q) :
    ∃ R₀ : O[X], R₀.Monic ∧ Irreducible (R₀.map (algebraMap O K)) ∧
      ∃ e₁ e₂ : ℕ, ∃ S₁ S₂ : O[X], S₁.Monic ∧ S₂.Monic ∧
        ¬ (R₀.map (algebraMap O K) ∣ S₁.map (algebraMap O K)) ∧
        ¬ (R₀.map (algebraMap O K) ∣ S₂.map (algebraMap O K)) ∧
        P = R₀ ^ e₁ * S₁ ∧ Q = R₀ ^ e₂ * S₂ ∧ e₁ ≠ e₂ := by
  classical
  let ι := algebraMap O K
  have hne_K : P.map ι ≠ Q.map ι :=
    fun h ↦ hne (map_injective ι (IsFractionRing.injective O K) h)
  let g := EuclideanDomain.gcd (P.map ι) (Q.map ι)
  obtain ⟨A, hA⟩ := EuclideanDomain.gcd_dvd_left (P.map ι) (Q.map ι)
  obtain ⟨B, hB⟩ := EuclideanDomain.gcd_dvd_right (P.map ι) (Q.map ι)
  have hnot : ¬ IsUnit A ∨ ¬ IsUnit B := by
    by_contra! h
    have h1 : Associated (P.map ι) g := hA ▸ (associated_mul_unit_right g A h.1).symm
    have h2 : Associated (Q.map ι) g := hB ▸ (associated_mul_unit_right g B h.2).symm
    exact hne_K (eq_of_monic_of_associated (hP.map ι) (hQ.map ι) (h1.trans h2.symm))
  rcases hnot with hAn | hBn
  · exact exists_factor_ne_multiplicity_aux hP hQ hA
      (fun _ h1 h2 ↦ EuclideanDomain.dvd_gcd h1 h2) hAn
  · obtain ⟨R₀, hR₀_m, hR₀_i, e₂, e₁, S₂, S₁,
        hS₂_m, hS₁_m, hS₂_nd, hS₁_nd, hQ_eq, hP_eq, hne'⟩ :=
      exists_factor_ne_multiplicity_aux hQ hP hB
        (fun _ h1 h2 ↦ EuclideanDomain.dvd_gcd h2 h1) hBn
    exact ⟨R₀, hR₀_m, hR₀_i, e₁, e₂, S₁, S₂,
      hS₁_m, hS₂_m, hS₁_nd, hS₂_nd, hP_eq, hQ_eq, hne'.symm⟩

private theorem resultant_ne_zero_of_not_dvd_fraction {O K : Type*} [CommRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] {S R₀ : O[X]}
    (hR₀_irr : Irreducible (R₀.map (algebraMap O K)))
    (hndvd : ¬ (R₀.map (algebraMap O K) ∣ S.map (algebraMap O K))) :
    S.resultant R₀ ≠ 0 := by
  let ι := algebraMap O K
  have hinj := IsFractionRing.injective O K
  have hcop : IsCoprime (S.map ι) (R₀.map ι) := (hR₀_irr.coprime_iff_not_dvd.mpr hndvd).symm
  have hres_ne : (S.map ι).resultant (R₀.map ι) ≠ 0 := resultant_ne_zero _ _ hcop
  rw [resultant_map_of_natDegree_eq ι (natDegree_map_eq_of_injective hinj _)
    (natDegree_map_eq_of_injective hinj _)] at hres_ne
  exact fun h0 ↦ hres_ne (by rw [h0, map_zero])

/-- **Resultant recognition.** Let `O` be a discrete valuation ring with uniformizer `π`,
and let `φ : D →+* O` be a ring homomorphism whose image is dense modulo every power `π ^ N`.
If monic polynomials `P, Q : O[X]` have equal additive valuations
`addVal O (P.resultant (ψ.map φ))` and `addVal O (Q.resultant (ψ.map φ))` for every monic
`ψ : D[X]` such that both resultants are nonzero, then `P = Q`. -/
theorem resultantRecognition {D O : Type*} [CommRing D] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (φ : D →+* O) (π : O) (hπ : Irreducible π)
    (hφ : ∀ N : ℕ, ∀ o : O, ∃ d : D, o - φ d ∈ Ideal.span {π ^ N})
    (P Q : Polynomial O) (hP : P.Monic) (hQ : Q.Monic)
    (h : ∀ ψ : Polynomial D, ψ.Monic →
      Polynomial.resultant P (ψ.map φ) ≠ 0 →
      Polynomial.resultant Q (ψ.map φ) ≠ 0 →
      IsDiscreteValuationRing.addVal O (Polynomial.resultant P (ψ.map φ)) =
        IsDiscreteValuationRing.addVal O (Polynomial.resultant Q (ψ.map φ))) :
    P = Q := by
  by_contra hne
  let K := FractionRing O
  obtain ⟨R₀, hR₀_m, hR₀_irr, e₁, e₂, S₁, S₂,
      hS₁_m, hS₂_m, hS₁_nd, hS₂_nd, rfl, rfl, he⟩ :=
    exists_factor_ne_multiplicity (K := K) hP hQ hne
  have hd_pos : 0 < R₀.natDegree := by
    rw [← natDegree_map_eq_of_injective (IsFractionRing.injective O K)]
    exact hR₀_irr.natDegree_pos
  have hSR₁ : S₁.resultant R₀ ≠ 0 :=
    resultant_ne_zero_of_not_dvd_fraction hR₀_irr hS₁_nd
  have hSR₂ : S₂.resultant R₀ ≠ 0 :=
    resultant_ne_zero_of_not_dvd_fraction hR₀_irr hS₂_nd
  obtain ⟨k₁, hk₁⟩ := ENat.ne_top_iff_exists.mp
    (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr hSR₁)
  obtain ⟨k₂, hk₂⟩ := ENat.ne_top_iff_exists.mp
    (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr hSR₂)
  have hslope (n : ℕ) (hn : 1 ≤ n) (hn₁ : k₁ < n) (hn₂ : k₂ < n) :
      n * R₀.natDegree * e₁ + k₁ = n * R₀.natDegree * e₂ + k₂ := by
    let T : O[X] := R₀ + C (π ^ n)
    have hCdeg : (C (π ^ n)).degree < R₀.degree :=
      (degree_C_le).trans_lt (natDegree_pos_iff_degree_pos.mp hd_pos)
    have hT_monic : T.Monic := hR₀_m.add_of_left hCdeg
    have hT_deg : T.natDegree = R₀.natDegree := natDegree_add_eq_left_of_degree_lt hCdeg
    have hI_ne : Ideal.span {π ^ (2 * n)} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]
      exact fun hunit ↦ hπ.not_isUnit (isUnit_of_dvd_one
        ((pow_one π ▸ pow_dvd_pow π (by lia : 1 ≤ 2 * n)).trans hunit.dvd))
    obtain ⟨ψ, hψ_m, hψ_deg, hψ_coeff⟩ :=
      exists_monic_map_sub_coeff_mem φ hI_ne (hφ (2 * n)) hT_monic
    have hψφ_deg : (ψ.map φ).natDegree = R₀.natDegree := by
      rw [hψ_m.natDegree_map, hψ_deg, hT_deg]
    obtain ⟨hPψ_ne, hPψ_val⟩ :=
      addVal_resultant_pow_mul_of_sub_add_C_pow_mem hπ hR₀_m hS₁_m e₁ hn
        (by rw [← hk₁]; exact Nat.cast_lt.mpr hn₁) hψφ_deg hψ_coeff
    obtain ⟨hQψ_ne, hQψ_val⟩ :=
      addVal_resultant_pow_mul_of_sub_add_C_pow_mem hπ hR₀_m hS₂_m e₂ hn
        (by rw [← hk₂]; exact Nat.cast_lt.mpr hn₂) hψφ_deg hψ_coeff
    have heq := h ψ hψ_m hPψ_ne hQψ_ne
    rw [hPψ_val, hQψ_val, ← hk₁, ← hk₂, ← Nat.cast_add, ← Nat.cast_add] at heq
    exact Nat.cast_injective heq
  let N := max k₁ k₂ + 1
  have h1 := hslope N (by lia) (by lia) (by lia)
  have h2 := hslope (N + 1) (by lia) (by lia) (by lia)
  have hmul : R₀.natDegree * e₁ = R₀.natDegree * e₂ := by nlinarith
  exact he (Nat.eq_of_mul_eq_mul_left hd_pos hmul)

end Recognition

end Polynomial
