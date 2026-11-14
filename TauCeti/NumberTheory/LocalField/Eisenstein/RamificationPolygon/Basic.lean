/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Eisenstein.RamificationPolygon.Polynomial
public import TauCeti.NumberTheory.NewtonPolygon.Slopes
import Mathlib.Algebra.Polynomial.Div
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.SplittingField.Construction
import TauCeti.Analysis.Convex.Sequence.Rationality
import TauCeti.Data.Nat.Choose.Factorization
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.NumberTheory.LocalField.Eisenstein.TotallyRamified
import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic
import TauCeti.NumberTheory.LocalField.Monogenic
import TauCeti.NumberTheory.LocalField.TotallyRamified
import TauCeti.NumberTheory.NewtonPolygon.Roots
import TauCeti.RingTheory.Polynomial.Eisenstein.Minpoly

/-!
# The ramification polygon of an Eisenstein extension

For a monic Eisenstein polynomial `φ ∈ 𝒪[K][X]` of degree `n` whose root `α` generates a
nonarchimedean local-field extension `L = K(α)`, the *ramification polygon* is the Newton polygon
`(ramificationPolynomial φ α).newtonPolygon (realAddValuation L)` of `ρ(X) = α⁻ⁿ φ(α X + α)`.
With Tau Ceti's lower-convex-envelope orientation (`Polynomial.newtonPolygon`), slopes increase
from left to right and a slope `-r` corresponds to a nonzero root `(α' - α) / α` of normalized
valuation `r`.

This file establishes the arithmetic geometry of the ramification polygon together with its
Galois-conjugate root-difference interpretation:

* `p`-power contact: every contact point of the coefficient heights with a supporting line of
  strictly negative slope has abscissa `p ^ i`, where `p = ringChar 𝓀[K]`.
* The tame segment: writing `w = padicValNat p n`, the coefficient height at `p ^ w` is `0`, every
  coefficient in `[1, p ^ w)` has valuation at least `1`, and `[p ^ w, n]` is the finite face of
  slope `0` of the ramification polygon. Consequently all finite slopes are nonpositive and `0`
  occurs with multiplicity `n - p ^ w`.
* Negative-slope segments: every finite face of strictly negative slope and positive width has
  endpoints `p ^ a` and `p ^ (a + d)` with `0 < d` and `a + d ≤ w`, and rational slope `-r` with
  `0 < r` and `r.den ∣ p ^ a * (p ^ d - 1)`. In the separable case, unit slopes are constant on
  each interval `[p ^ k, p ^ (k + 1))`.
* Conjugate root differences (`TauCeti.conjugateBreaks`): for any finite tower `M/L/K`, the
  multiset of normalized root-difference valuations `v_M(σ ξ - ξ) / e(M/L) - 1` over `K`-embeddings
  `σ ≠ incl` is independent of the choice of uniformizer `ξ` of a totally ramified extension `L/K`,
  and in the separable split case its negated real casts equal the Newton slopes of
  `ramificationPolynomial φ α`. Consequently both the Newton slopes and the ramification polygon
  depend only on the separable extension `L/K` and not on the pair `(φ, α)`.

## Main definitions

* `TauCeti.conjugateBreaks`: the multiset of rational root-difference breaks
  `(WithZero.log (normalizedValuationWithZero M (σ ξ - algebraMap L M ξ)) : ℚ) / e(M/L) - 1`
  over `K`-embeddings `σ : L →ₐ[K] M` distinct from `IsScalarTower.toAlgHom K L M`.

## Main results

* `TauCeti.exists_eq_pow_of_mem_supportingFace_of_neg`: contact points on a supporting line of
  strictly negative slope occur only at powers of `ringChar 𝓀[K]`.
* `TauCeti.isFiniteFace_zero_newtonPolygon_ramificationPolynomial` and
  `TauCeti.count_zero_newtonSlopes_ramificationPolynomial`: `[p ^ w, n]` is the horizontal face of
  slope `0`, contributing `n - p ^ w` zero slopes.
* `TauCeti.exists_pow_endpoints_of_isFiniteFace_of_neg` and
  `TauCeti.exists_rat_neg_eq_and_den_dvd_of_isFiniteFace_of_neg`: `p`-power endpoints and
  denominator divisibility on negative-slope segments.
* `TauCeti.unitSlope_newtonPolygon_ramificationPolynomial_eq_on_Ico_pow`: constancy of unit slopes
  on `[p ^ k, p ^ (k + 1))` in the separable case.
* `TauCeti.conjugateBreaks_eq_of_irreducible`: uniformizer invariance of `conjugateBreaks` for
  totally ramified extensions.
* `TauCeti.newtonSlopes_ramificationPolynomial_eq_map_conjugateBreaks` and
  `TauCeti.card_filter_conjugateBreaks_eq_zero`: Newton-slope dictionary and tame zero count.
* `TauCeti.newtonSlopes_ramificationPolynomial_eq` and
  `TauCeti.newtonPolygon_ramificationPolynomial_eq`: invariance of the Newton slopes and
  ramification polygon under changing the monic Eisenstein generator `(φ, α)`.

## References

* O. Ore, *Bemerkungen zur Theorie der Differente*, Mathematische Zeitschrift 25 (1926), 1–8.
* C. Greve and S. Pauli, *Ramification polygons, splitting fields, and Galois groups of Eisenstein
  polynomials*, International Journal of Number Theory 8 (2012), 1401–1424, §4.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §6, and Chapter IV, §§1–2.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField Polynomial
open scoped IntermediateField WithZero

namespace TauCeti

section PolygonGeometry

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- Greve–Pauli's coefficient inequality: for `p = ringChar 𝓀[K]` and `p ∤ u`, the coefficient of
`ramificationPolynomial φ α` at `p ^ r` has valuation at most that at `p ^ r * u`. -/
theorem realAddValuation_coeff_pow_le_coeff_pow_mul {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    (r : ℕ) {u : ℕ} (hu : ¬ ringChar 𝓀[K] ∣ u) :
    realAddValuation L ((ramificationPolynomial φ α).coeff ((ringChar 𝓀[K]) ^ r)) ≤
      realAddValuation L ((ramificationPolynomial φ α).coeff ((ringChar 𝓀[K]) ^ r * u)) := by
  set p := ringChar 𝓀[K]
  have hp : p.Prime := CharP.char_is_prime 𝓀[K] p
  have hu0 : 0 < u := Nat.pos_of_ne_zero fun h ↦ hu (h ▸ dvd_zero p)
  have hpr : 1 ≤ p ^ r := Nat.one_le_pow r p hp.pos
  have hpru : p ^ r ≤ p ^ r * u := Nat.le_mul_of_pos_right _ hu0
  rcases lt_or_ge φ.natDegree (p ^ r * u) with hgt | _
  · simp [coeff_ramificationPolynomial_eq_zero_of_lt hgt]
  have hf₁ := realAddValuation_coeff_ramificationPolynomial_add_natDegree
    hmonic hφ hroot hgen hpr
  have hf₂ := realAddValuation_coeff_ramificationPolynomial_add_natDegree
    hmonic hφ hroot hgen (hpr.trans hpru)
  have hinf : realAddValuation L ((ramificationPolynomial φ α).coeff (p ^ r)) +
        (φ.natDegree : WithTop ℝ) ≤
      realAddValuation L ((ramificationPolynomial φ α).coeff (p ^ r * u)) +
        (φ.natDegree : WithTop ℝ) := by
    rw [hf₁, hf₂, Finset.le_inf_iff]
    intro h hh
    obtain ⟨hh₁, hh₂⟩ := Finset.mem_Icc.mp hh
    refine (Finset.inf_le (Finset.mem_Icc.mpr ⟨hpru.trans hh₁, hh₂⟩)).trans ?_
    refine add_le_add ?_ le_rfl
    refine WithTop.monotone_map_iff.mpr (fun a b hab ↦ mul_le_mul_of_nonneg_left hab
      (Nat.cast_nonneg _)) ?_
    simp only [Subring.coe_mul, Subring.coe_natCast, (realAddValuation K).map_mul]
    refine add_le_add ?_ le_rfl
    have hc₁ : h.choose (p ^ r) ≠ 0 := (Nat.choose_pos (hpru.trans hh₁)).ne'
    have hc₂ : h.choose (p ^ r * u) ≠ 0 := (Nat.choose_pos hh₁).ne'
    rw [realAddValuation_natCast_eq_nsmul hc₁, realAddValuation_natCast_eq_nsmul hc₂]
    have hfac := Nat.factorization_choose_pow_le_choose_pow_mul hp hu hh₁
    have hvp : 0 ≤ realAddValuation K (p : K) :=
      mem_integer_iff_realAddValuation_nonneg.mp (natCast_mem 𝒪[K] p)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hfac
    rw [hk, add_nsmul]
    exact le_add_of_nonneg_right (nsmul_nonneg hvp k)
  cases hx : realAddValuation L ((ramificationPolynomial φ α).coeff (p ^ r)) with
  | top =>
    rw [hx, top_add] at hinf
    cases hy : realAddValuation L ((ramificationPolynomial φ α).coeff (p ^ r * u)) with
    | top => simp
    | coe y =>
      rw [hy, ← WithTop.coe_natCast, ← WithTop.coe_add] at hinf
      exact absurd hinf (by simp)
  | coe x =>
    cases hy : realAddValuation L ((ramificationPolynomial φ α).coeff (p ^ r * u)) with
    | top => simp
    | coe y =>
      rw [hx, hy, ← WithTop.coe_natCast, ← WithTop.coe_add, ← WithTop.coe_add,
        WithTop.coe_le_coe] at hinf
      rw [WithTop.coe_le_coe]
      linarith

/-- **`p`-power contact theorem.** Every contact point of the coefficient heights of
`ramificationPolynomial φ α` with a supporting line of strictly negative slope occurs at a power of
`ringChar 𝓀[K]`. -/
theorem exists_eq_pow_of_mem_supportingFace_of_neg {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    {σ c : ℝ} (hσ : σ < 0)
    (hc : IsSupportingLine (fun m ↦ realAddValuation L ((ramificationPolynomial φ α).coeff m)) σ c)
    {m : ℕ}
    (hm : m ∈ supportingFace
      (fun m ↦ realAddValuation L ((ramificationPolynomial φ α).coeff m)) σ c) :
    ∃ i : ℕ, m = (ringChar 𝓀[K]) ^ i := by
  set p := ringChar 𝓀[K]
  have hp : p.Prime := CharP.char_is_prime 𝓀[K] p
  have hm0 : m ≠ 0 := by
    rintro rfl
    have h0 := mem_supportingFace.mp hm
    simp [coeff_zero_ramificationPolynomial_of_isRoot hroot] at h0
  set i := m.factorization p
  set u := m / p ^ i
  have hmu : p ^ i * u = m := Nat.ordProj_mul_ordCompl_eq_self m p
  have hndvd : ¬ p ∣ u := Nat.not_dvd_ordCompl hp hm0
  refine ⟨i, ?_⟩
  by_contra hne
  have hu1 : 1 < u := by
    have hu0 : u ≠ 0 := fun h ↦ hm0 (by rw [← hmu, h, mul_zero])
    have hu_ne1 : u ≠ 1 := fun h ↦ hne (by rw [← hmu, h, mul_one])
    exact Nat.lt_of_le_of_ne (Nat.pos_of_ne_zero hu0) hu_ne1.symm
  have hlt : p ^ i < m := by
    rw [← hmu]
    exact lt_mul_of_one_lt_right (pow_pos hp.pos i) hu1
  have hline : ((c + σ * (p ^ i : ℕ) : ℝ) : WithTop ℝ) ≤
      ((c + σ * (m : ℕ) : ℝ) : WithTop ℝ) :=
    (isSupportingLine_iff_forall.mp hc (p ^ i)).trans
      ((realAddValuation_coeff_pow_le_coeff_pow_mul hmonic hφ hroot hgen i hndvd).trans_eq
        (hmu.symm ▸ mem_supportingFace.mp hm))
  rw [WithTop.coe_le_coe] at hline
  have hlt_real : ((p ^ i : ℕ) : ℝ) < (m : ℝ) := Nat.cast_lt.mpr hlt
  nlinarith

/-- At `p ^ w`, where `p = ringChar 𝓀[K]` and `w = padicValNat p φ.natDegree`, the coefficient of
`ramificationPolynomial φ α` has valuation `0` (so is a unit of `𝒪[L]`). -/
theorem realAddValuation_coeff_pow_padicValNat_ramificationPolynomial {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤) :
    realAddValuation L ((ramificationPolynomial φ α).coeff
      ((ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree)) = 0 := by
  obtain ⟨-, -, -, -, he⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hmonic hφ hroot hgen
  set p := ringChar 𝓀[K]
  have hp : p.Prime := CharP.char_is_prime 𝓀[K] p
  set n := φ.natDegree
  have hnpos : 0 < n := he ▸ ramificationIndex_pos (K := K) (L := L)
  set w := padicValNat p n
  have hfac : n.factorization p = w := (Nat.factorization_def n hp).trans Nat.padicValNat_def.symm
  have hpwn : p ^ w ≤ n := hfac ▸ Nat.le_of_dvd hnpos (Nat.ordProj_dvd n p)
  refine le_antisymm ?_
    (realAddValuation_coeff_ramificationPolynomial_nonneg hmonic hφ hroot hgen (p ^ w))
  have hformula := realAddValuation_coeff_ramificationPolynomial_add_natDegree
    hmonic hφ hroot hgen (Nat.one_le_pow w p hp.pos)
  have hndvd : ¬ p ∣ n.choose (p ^ w) := hfac ▸ Nat.not_dvd_choose_pow_factorization hp hnpos.ne'
  have hle : realAddValuation L ((ramificationPolynomial φ α).coeff (p ^ w)) +
      (n : WithTop ℝ) ≤ (n : WithTop ℝ) := by
    rw [hformula]
    refine (Finset.inf_le (Finset.mem_Icc.mpr ⟨hpwn, le_rfl⟩)).trans ?_
    have hcoeff : (((n.choose (p ^ w) : 𝒪[K]) * φ.coeff n : 𝒪[K]) : K) =
        (n.choose (p ^ w) : K) := by
      simp [n, hmonic.coeff_natDegree]
    rw [hcoeff, realAddValuation_natCast_eq_zero_iff_not_dvd.mpr hndvd]
    simp
  cases hx : realAddValuation L ((ramificationPolynomial φ α).coeff (p ^ w)) with
  | top => rw [hx, top_add] at hle; exact absurd hle (by simp)
  | coe r =>
    rw [hx, ← WithTop.coe_natCast, ← WithTop.coe_add, WithTop.coe_le_coe] at hle
    rw [← WithTop.coe_zero, WithTop.coe_le_coe]
    linarith

/-- Below the wild index `p ^ w` (`w = padicValNat p φ.natDegree`), every coefficient `ρ_i` with
`1 ≤ i < p ^ w` lies in `𝓂[L]`, i.e. has normalized valuation at least `1`. -/
theorem one_le_realAddValuation_coeff_of_lt_pow_padicValNat {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    {i : ℕ} (hi1 : 1 ≤ i)
    (hi : i < (ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree) :
    1 ≤ realAddValuation L ((ramificationPolynomial φ α).coeff i) := by
  set p := ringChar 𝓀[K]
  have hp : p.Prime := CharP.char_is_prime 𝓀[K] p
  set n := φ.natDegree
  have hfac : n.factorization p = padicValNat p n :=
    (Nat.factorization_def n hp).trans Nat.padicValNat_def.symm
  have hformula := realAddValuation_coeff_ramificationPolynomial_add_natDegree
    hmonic hφ hroot hgen hi1
  have hge : ((1 + n : ℝ) : WithTop ℝ) ≤
      realAddValuation L ((ramificationPolynomial φ α).coeff i) + (n : WithTop ℝ) := by
    rw [hformula, Finset.le_inf_iff]
    intro h hh
    obtain ⟨hih, hhn⟩ := Finset.mem_Icc.mp hh
    have h1 : 1 ≤ realAddValuation K (((h.choose i : 𝒪[K]) * φ.coeff h : 𝒪[K]) : K) := by
      rcases eq_or_lt_of_le hhn with rfl | hlt
      · have hdvd : p ∣ φ.natDegree.choose i :=
          Nat.dvd_choose_of_lt_pow_factorization hp hi1 (hfac.symm ▸ hi)
        have hcoeff : (((φ.natDegree.choose i : 𝒪[K]) * φ.coeff φ.natDegree : 𝒪[K]) : K) =
            (φ.natDegree.choose i : K) := by
          simp [hmonic.coeff_natDegree]
        rw [hcoeff]
        exact one_le_realAddValuation_natCast_iff_dvd.mpr hdvd
      · exact mem_maximalIdeal_iff_one_le_realAddValuation.mp (Ideal.mul_mem_left _ _ (hφ.mem hlt))
    cases hx : realAddValuation K (((h.choose i : 𝒪[K]) * φ.coeff h : 𝒪[K]) : K) with
    | top => simp
    | coe r =>
      rw [hx, ← WithTop.coe_one, WithTop.coe_le_coe] at h1
      simp only [WithTop.map_coe, ← WithTop.coe_natCast, ← WithTop.coe_add, WithTop.coe_le_coe]
      have : (1 : ℝ) ≤ h := by exact_mod_cast hi1.trans hih
      nlinarith
  cases hv : realAddValuation L ((ramificationPolynomial φ α).coeff i) with
  | top => simp
  | coe r =>
    rw [hv, ← WithTop.coe_natCast, ← WithTop.coe_add, WithTop.coe_le_coe] at hge
    rw [← WithTop.coe_one, WithTop.coe_le_coe]
    linarith

/-- **The tame segment.** The finite face of slope `0` of the ramification polygon runs from
`p ^ padicValNat p φ.natDegree` to `φ.natDegree`, where `p = ringChar 𝓀[K]`. -/
theorem isFiniteFace_zero_newtonPolygon_ramificationPolynomial {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤) :
    IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L)) 0
      ((ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree) φ.natDegree := by
  obtain ⟨-, -, hα0, -, he⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hmonic hφ hroot hgen
  set p := ringChar 𝓀[K]
  have hp : p.Prime := CharP.char_is_prime 𝓀[K] p
  set n := φ.natDegree
  have hnpos : 0 < n := he ▸ ramificationIndex_pos (K := K) (L := L)
  set w := padicValNat p n
  have hfac : n.factorization p = w := (Nat.factorization_def n hp).trans Nat.padicValNat_def.symm
  have hpwn : p ^ w ≤ n := hfac ▸ Nat.le_of_dvd hnpos (Nat.ordProj_dvd n p)
  set ρ := ramificationPolynomial φ α
  have henv := ρ.isLowerConvexEnvelope_newtonPolygon (realAddValuation L)
  have hca : IsSupportingLine (fun m ↦ realAddValuation L (ρ.coeff m)) 0 0 :=
    isSupportingLine_iff_forall.mpr fun m ↦ by
      simpa using realAddValuation_coeff_ramificationPolynomial_nonneg hmonic hφ hroot hgen m
  have hcN : IsSupportingLine (ρ.newtonPolygon (realAddValuation L)) 0 0 :=
    henv.isSupportingLine_iff.mpr hca
  refine isFiniteFace_iff.mpr ⟨hpwn, 0, hcN, Set.Subset.antisymm (fun m hm ↦ ?_) ?_⟩
  · refine ⟨le_of_not_gt fun hlt ↦ ?_, le_of_not_gt fun hgt ↦ ?_⟩
    · obtain ⟨k, hkm, hk⟩ := henv.exists_le_mem_supportingFace hca hm
      have hk0 : realAddValuation L (ρ.coeff k) = 0 := by simpa using mem_supportingFace.mp hk
      rcases eq_or_ne k 0 with rfl | hk_ne
      · rw [coeff_zero_ramificationPolynomial_of_isRoot hroot,
          (realAddValuation L).map_zero] at hk0
        exact WithTop.top_ne_coe hk0
      · have hk1 := one_le_realAddValuation_coeff_of_lt_pow_padicValNat hmonic hφ hroot hgen
          (Nat.one_le_iff_ne_zero.mpr hk_ne) (hkm.trans_lt hlt)
        rw [hk0] at hk1
        exact absurd hk1 (by simp)
    · have htop := ρ.newtonPolygon_eq_top_of_natDegree_lt (realAddValuation L)
        ((natDegree_ramificationPolynomial_le φ α).trans_lt hgt)
      have hm0 := mem_supportingFace.mp hm
      rw [htop] at hm0
      exact WithTop.top_ne_coe hm0
  · have hleft : p ^ w ∈ supportingFace (ρ.newtonPolygon (realAddValuation L)) 0 0 :=
      henv.supportingFace_subset hca (by
        simpa using
          realAddValuation_coeff_pow_padicValNat_ramificationPolynomial hmonic hφ hroot hgen)
    have hright : n ∈ supportingFace (ρ.newtonPolygon (realAddValuation L)) 0 0 :=
      henv.supportingFace_subset hca (by
        simpa using realAddValuation_coeff_natDegree_ramificationPolynomial hmonic hα0)
    exact ((ρ.isConvexSeq_newtonPolygon (realAddValuation L)).ordConnected_supportingFace
      hcN).out hleft hright

/-- The slope `0` occurs in `newtonSlopes` of `ramificationPolynomial φ α` with multiplicity
`φ.natDegree - p ^ padicValNat p φ.natDegree`. -/
theorem count_zero_newtonSlopes_ramificationPolynomial {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤) :
    ((ramificationPolynomial φ α).newtonSlopes (realAddValuation L)).count 0 =
      φ.natDegree - (ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree :=
  count_newtonSlopes_of_isFiniteFace
    (isFiniteFace_zero_newtonPolygon_ramificationPolynomial hmonic hφ hroot hgen)

/-- Every finite slope of `ramificationPolynomial φ α` is nonpositive. -/
theorem nonpos_of_mem_newtonSlopes_ramificationPolynomial {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    {s : ℝ} (hs : s ∈ (ramificationPolynomial φ α).newtonSlopes (realAddValuation L)) :
    s ≤ 0 := by
  obtain ⟨i, hi, rfl⟩ := (mem_newtonSlopes _ _).mp hs
  have hface := isFiniteFace_zero_newtonPolygon_ramificationPolynomial hmonic hφ hroot hgen
  have hin : i < φ.natDegree := lt_of_not_ge fun hge ↦
    (mem_finiteEdges.mp hi).2 ((ramificationPolynomial φ α).newtonPolygon_eq_top_of_natDegree_lt
      (realAddValuation L) ((natDegree_ramificationPolynomial_le φ α).trans_lt (by omega)))
  rcases lt_or_ge i ((ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree) with hlt | hge
  · exact (hface.unitSlope_lt ((ramificationPolynomial φ α).isConvexSeq_newtonPolygon _) hi hlt).le
  · exact (hface.unitSlope_eq hge hin).le

/-- **Endpoints of negative-slope faces.** Every finite face of strictly negative slope and
positive width of the ramification polygon has endpoints `p ^ a` and `p ^ (a + d)` with `0 < d`
and `a + d ≤ padicValNat p φ.natDegree`, where `p = ringChar 𝓀[K]`. -/
theorem exists_pow_endpoints_of_isFiniteFace_of_neg {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    {σ : ℝ} {l u : ℕ} (hσ : σ < 0) (hlu : l < u)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L)) σ l u) :
    ∃ a d : ℕ, 0 < d ∧ a + d ≤ padicValNat (ringChar 𝓀[K]) φ.natDegree ∧
      l = (ringChar 𝓀[K]) ^ a ∧ u = (ringChar 𝓀[K]) ^ (a + d) := by
  set p := ringChar 𝓀[K]
  have hp : p.Prime := CharP.char_is_prime 𝓀[K] p
  have henv := (ramificationPolynomial φ α).isLowerConvexEnvelope_newtonPolygon (realAddValuation L)
  obtain ⟨c, hc, ⟨hl_mem, -⟩, ⟨hu_mem, -⟩⟩ :=
    henv.exists_isSupportingLine_isLeast_isGreatest_of_isFiniteFace hface
  obtain ⟨a, ha⟩ := exists_eq_pow_of_mem_supportingFace_of_neg hmonic hφ hroot hgen hσ hc hl_mem
  obtain ⟨b, hb⟩ := exists_eq_pow_of_mem_supportingFace_of_neg hmonic hφ hroot hgen hσ hc hu_mem
  have hab : a < b := (Nat.pow_lt_pow_iff_right hp.one_lt).mp (ha ▸ hb ▸ hlu)
  have hun : u ≤ φ.natDegree := le_of_not_gt fun hgt ↦
    hface.right_ne_top ((ramificationPolynomial φ α).newtonPolygon_eq_top_of_natDegree_lt
      (realAddValuation L) ((natDegree_ramificationPolynomial_le φ α).trans_lt hgt))
  have huw : u ≤ p ^ padicValNat p φ.natDegree := by
    by_contra hgt
    have hgt' : ringChar 𝓀[K] ^ padicValNat (ringChar 𝓀[K]) φ.natDegree < u := not_le.mp hgt
    have hf0 := isFiniteFace_zero_newtonPolygon_ramificationPolynomial hmonic hφ hroot hgen
    have hsl₁ := hface.unitSlope_eq (i := u - 1) (by omega) (by omega)
    have hsl₂ := hf0.unitSlope_eq (i := u - 1) (by omega) (by omega)
    linarith
  have hbw : b ≤ padicValNat p φ.natDegree :=
    (Nat.pow_le_pow_iff_right hp.one_lt).mp (hb ▸ huw)
  exact ⟨a, b - a, Nat.sub_pos_of_lt hab, by omega, ha, by rw [hb]; congr 1; omega⟩

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension K L] in
/-- **Rationality and denominator bound on negative-slope faces.** Every finite face of strictly
negative slope and positive width of the ramification polygon has slope `-r` for a rational `0 < r`
whose reduced denominator divides the face width `u - l`. -/
theorem exists_rat_neg_eq_and_den_dvd_of_isFiniteFace_of_neg {φ : 𝒪[K][X]} {α : L}
    {σ : ℝ} {l u : ℕ} (hσ : σ < 0) (hlu : l < u)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L)) σ l u) :
    ∃ r : ℚ, 0 < r ∧ σ = -(r : ℝ) ∧ r.den ∣ u - l := by
  obtain ⟨q, hq, hdvd⟩ :=
    ((ramificationPolynomial φ α).isLowerConvexEnvelope_newtonPolygon
      (realAddValuation L)).exists_rat_eq_and_den_dvd_of_isFiniteFace
      (fun m hm ↦ exists_int_realAddValuation (mt realAddValuation_eq_top_iff.mpr hm)) hface hlu
  have hqneg : q < 0 := by exact_mod_cast hq.trans_lt hσ
  refine ⟨-q, neg_pos.mpr hqneg, ?_, ?_⟩
  · push_cast
    linarith
  · rwa [Rat.den_neg_eq_den]

/-- In an Eisenstein extension `L = K(α)` with `φ` monic, the ramification polygon ends at
`(φ.natDegree, 0)`. -/
theorem newtonPolygon_ramificationPolynomial_natDegree {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤) :
    (ramificationPolynomial φ α).newtonPolygon (realAddValuation L) φ.natDegree = 0 := by
  obtain ⟨-, -, hα0, -, -⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hmonic hφ hroot hgen
  rw [← hmonic.natDegree_ramificationPolynomial hα0, newtonPolygon_natDegree,
    (hmonic.ramificationPolynomial hα0).leadingCoeff, (realAddValuation L).map_one]

section SeparablePolygon

variable [Algebra.IsSeparable K L]

/-- In a separable Eisenstein extension `L = K(α)`, the ramification polygon starts at `(1, y_1)`
with `y_1 = d(L/K) + 1 - φ.natDegree`. -/
theorem newtonPolygon_ramificationPolynomial_one {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤) :
    (ramificationPolynomial φ α).newtonPolygon (realAddValuation L) 1 =
      (((differentExponent K L : ℝ) + 1 - φ.natDegree : ℝ) : WithTop ℝ) := by
  have htr := natTrailingDegree_ramificationPolynomial hmonic hφ hroot hgen
  rw [← htr, newtonPolygon_natTrailingDegree, trailingCoeff, htr,
    realAddValuation_coeff_one_ramificationPolynomial hmonic hφ hroot hgen]

/-- In a separable Eisenstein extension `L = K(α)`, `ramificationPolynomial φ α` has
`φ.natDegree - 1` finite Newton slopes. -/
theorem card_newtonSlopes_ramificationPolynomial {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤) :
    ((ramificationPolynomial φ α).newtonSlopes (realAddValuation L)).card = φ.natDegree - 1 := by
  obtain ⟨-, -, hα0, -, -⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hmonic hφ hroot hgen
  rw [card_newtonSlopes _ _ fun _ ↦ realAddValuation_eq_top_iff.mp,
    hmonic.natDegree_ramificationPolynomial hα0,
    natTrailingDegree_ramificationPolynomial hmonic hφ hroot hgen]

/-- In a separable Eisenstein extension, the unit slopes of the ramification polygon are constant
on every `p`-power interval `[p ^ k, p ^ (k + 1))` inside `[1, φ.natDegree)`. -/
theorem unitSlope_newtonPolygon_ramificationPolynomial_eq_on_Ico_pow {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    (k : ℕ) {i j : ℕ}
    (hi : i ∈ Set.Ico ((ringChar 𝓀[K]) ^ k) ((ringChar 𝓀[K]) ^ (k + 1)))
    (hj : j ∈ Set.Ico ((ringChar 𝓀[K]) ^ k) ((ringChar 𝓀[K]) ^ (k + 1)))
    (hin : i < φ.natDegree) (hjn : j < φ.natDegree) :
    unitSlope ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L)) i =
      unitSlope ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L)) j := by
  obtain ⟨-, -, hα0, -, -⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hmonic hφ hroot hgen
  set p := ringChar 𝓀[K]
  have hp : p.Prime := CharP.char_is_prime 𝓀[K] p
  set ρ := ramificationPolynomial φ α
  set N := ρ.newtonPolygon (realAddValuation L)
  have hi1 : 1 ≤ i := (Nat.one_le_pow k p hp.pos).trans hi.1
  have hedge : i ∈ finiteEdges N := by
    rw [ρ.finiteEdges_newtonPolygon (realAddValuation L) fun _ ↦ realAddValuation_eq_top_iff.mp,
      natTrailingDegree_ramificationPolynomial hmonic hφ hroot hgen,
      hmonic.natDegree_ramificationPolynomial hα0]
    exact ⟨hi1, hin⟩
  set σ := unitSlope N i
  obtain ⟨l, u, hface⟩ := exists_isFiniteFace_newtonPolygon
    ((hmonic.ramificationPolynomial hα0).newtonPolygon_ne_top (realAddValuation L)) σ
  have hiu : i ∈ Set.Ico l u :=
    (hface.setOf_unitSlope_eq (ρ.isConvexSeq_newtonPolygon _)).subset ⟨hedge, rfl⟩
  have hσle : σ ≤ 0 := nonpos_of_mem_newtonSlopes_ramificationPolynomial hmonic hφ hroot hgen
    ((mem_newtonSlopes _ _).mpr ⟨i, hedge, rfl⟩)
  rcases eq_or_lt_of_le hσle with hσ0 | hσneg
  · obtain ⟨rfl, rfl⟩ := (isFiniteFace_zero_newtonPolygon_ramificationPolynomial
      hmonic hφ hroot hgen).unique (hσ0 ▸ hface)
    have hwk : padicValNat p φ.natDegree ≤ k := Nat.lt_succ_iff.mp
      ((Nat.pow_lt_pow_iff_right hp.one_lt).mp (hiu.1.trans_lt hi.2))
    have hlj : p ^ padicValNat p φ.natDegree ≤ j :=
      (Nat.pow_le_pow_right hp.pos hwk).trans hj.1
    exact hσ0.trans
      ((isFiniteFace_zero_newtonPolygon_ramificationPolynomial hmonic hφ hroot hgen).unitSlope_eq
        hlj hjn).symm
  · obtain ⟨a, d, -, -, rfl, rfl⟩ := exists_pow_endpoints_of_isFiniteFace_of_neg
      hmonic hφ hroot hgen hσneg (hiu.1.trans_lt hiu.2) hface
    have hak : a ≤ k := Nat.lt_succ_iff.mp
      ((Nat.pow_lt_pow_iff_right hp.one_lt).mp (hiu.1.trans_lt hi.2))
    have hkad : k + 1 ≤ a + d := Nat.succ_le_of_lt
      ((Nat.pow_lt_pow_iff_right hp.one_lt).mp (hi.1.trans_lt hiu.2))
    exact (hface.unitSlope_eq ((Nat.pow_le_pow_right hp.pos hak).trans hj.1)
      (hj.2.trans_le (Nat.pow_le_pow_right hp.pos hkad))).symm

end SeparablePolygon

end PolygonGeometry

/-! ### Conjugate root-difference valuations and invariance of the ramification polygon -/

section ConjugateBreaks

open Classical in
/-- The multiset of rational root-difference breaks
`v_M(σ ξ - ξ) / e(M/L) - 1` of an element `ξ : L` over all `K`-embeddings `σ : L →ₐ[K] M` distinct
from the tower inclusion `IsScalarTower.toAlgHom K L M`. -/
def conjugateBreaks (K L M : Type*) [Field K] [Field L]
    [Algebra K L] [Module.Finite K L]
    [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M] (ξ : L) : Multiset ℚ :=
  ((Finset.univ : Finset (L →ₐ[K] M)).filter
      (· ≠ IsScalarTower.toAlgHom K L M)).val.map
    fun σ ↦ ((WithZero.log (normalizedValuationWithZero M (σ ξ - algebraMap L M ξ)) : ℤ) : ℚ) /
      ramificationIndex L M - 1

/-- Unfolding `conjugateBreaks` to its defining multiset map. -/
theorem conjugateBreaks_def (K L M : Type*) [Field K] [Field L]
    [Algebra K L] [Module.Finite K L]
    [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M] [DecidableEq (L →ₐ[K] M)] (ξ : L) :
    conjugateBreaks K L M ξ =
      ((Finset.univ : Finset (L →ₐ[K] M)).filter
        (· ≠ IsScalarTower.toAlgHom K L M)).val.map
      fun σ ↦ ((WithZero.log (normalizedValuationWithZero M (σ ξ - algebraMap L M ξ)) : ℤ) : ℚ) /
        ramificationIndex L M - 1 := by
  unfold conjugateBreaks
  congr

section Tower

variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [Algebra L M] [IsScalarTower K L M] [ValuativeExtension L M]

/-- If `x ∈ 𝒪[L]` generates `𝒪[L]` as an `𝒪[K]`-algebra, then for every `y ∈ 𝒪[L]` and every
`K`-embedding `σ : L →ₐ[K] M`, `realAddValuation M (σ x - x) ≤ realAddValuation M (σ y - y)`. -/
theorem realAddValuation_sub_algebraMap_le_of_adjoin_eq_top
    {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) (y : 𝒪[L]) (σ : L →ₐ[K] M) :
    realAddValuation M (σ (x : L) - algebraMap L M (x : L)) ≤
      realAddValuation M (σ (y : L) - algebraMap L M (y : L)) := by
  have : ValuativeExtension K M := ValuativeExtension.trans K L M
  obtain ⟨P, hP⟩ : y ∈ (Polynomial.aeval x : 𝒪[K][X] →ₐ[𝒪[K]] 𝒪[L]).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval, hx]
    exact Algebra.mem_top
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hP
  have hmem (τ : L →ₐ[K] M) : τ (x : L) ∈ 𝒪[M] := by
    rw [mem_integer_iff_realAddValuation_nonneg, τ.realAddValuation_apply,
      ← realAddValuation_algebraMap]
    -- `algebraMap L M (x : L)` is the coercion of `algebraMap 𝒪[L] 𝒪[M] x ∈ 𝒪[M]`.
    have hcoe : algebraMap L M (x : L) = (algebraMap 𝒪[L] 𝒪[M] x : M) := by
      change algebraMap L M (algebraMap 𝒪[L] L x) = algebraMap 𝒪[M] M (algebraMap 𝒪[L] 𝒪[M] x)
      rw [← IsScalarTower.algebraMap_apply 𝒪[L] L M, ← IsScalarTower.algebraMap_apply 𝒪[L] 𝒪[M] M]
    rw [hcoe]
    exact mem_integer_iff_realAddValuation_nonneg.mp (algebraMap 𝒪[L] 𝒪[M] x).2
  set Q : 𝒪[M][X] := P.map (algebraMap 𝒪[K] 𝒪[M])
  set c : (L →ₐ[K] M) → 𝒪[M] := fun τ ↦ ⟨τ (x : L), hmem τ⟩
  have heval (τ : L →ₐ[K] M) : algebraMap 𝒪[M] M (Q.eval (c τ)) = τ (y : L) := by
    have hhom : (algebraMap K M).comp (algebraMap 𝒪[K] K) =
        τ.toRingHom.comp ((algebraMap K L).comp (algebraMap 𝒪[K] K)) := by
      ext d
      exact (τ.commutes (algebraMap 𝒪[K] K d)).symm
    rw [← Polynomial.eval_map_apply, Polynomial.map_map, algebraMap_comp_algebraMap_integerRing,
      hhom, ← Polynomial.map_map, ← algebraMap_comp_algebraMap_integerRing, ← Polynomial.map_map,
      ← hP, Polynomial.aeval_def, ← Polynomial.eval_map]
    -- `algebraMap 𝒪[M] M (c τ)` reduces definitionally to `τ.toRingHom (algebraMap 𝒪[L] L x)`.
    change (((P.map (algebraMap 𝒪[K] 𝒪[L])).map (algebraMap 𝒪[L] L)).map τ.toRingHom).eval
        (τ.toRingHom (algebraMap 𝒪[L] L x)) =
      τ.toRingHom (algebraMap 𝒪[L] L ((P.map (algebraMap 𝒪[K] 𝒪[L])).eval x))
    rw [Polynomial.eval_map_apply, Polynomial.eval_map_apply]
  obtain ⟨q, hq⟩ := Polynomial.sub_dvd_eval_sub (c σ) (c (IsScalarTower.toAlgHom K L M)) Q
  have hsub : σ (y : L) - algebraMap L M (y : L) =
      (σ (x : L) - algebraMap L M (x : L)) * (q : M) := by
    have hval := congrArg (algebraMap 𝒪[M] M) hq
    simp only [map_sub, map_mul, heval] at hval
    exact hval
  rw [hsub, (realAddValuation M).map_mul]
  exact le_add_of_nonneg_right (mem_integer_iff_realAddValuation_nonneg.mp q.2)

/-- **Uniformizer invariance of root-difference valuations.** In a totally ramified extension
`L/K`, any two uniformizers `ξ` and `ξ'` of `𝒪[L]` have identical root-difference valuation
`realAddValuation M (σ ξ - ξ)` at every `K`-embedding `σ : L →ₐ[K] M`. -/
theorem realAddValuation_sub_algebraMap_eq_of_irreducible
    (h : IsTotallyRamified K L) {ξ ξ' : 𝒪[L]} (hξ : Irreducible ξ) (hξ' : Irreducible ξ')
    (σ : L →ₐ[K] M) :
    realAddValuation M (σ (ξ : L) - algebraMap L M (ξ : L)) =
      realAddValuation M (σ (ξ' : L) - algebraMap L M (ξ' : L)) :=
  le_antisymm
    (realAddValuation_sub_algebraMap_le_of_adjoin_eq_top
      (h.adjoin_eq_top_of_irreducible hξ) ξ' σ)
    (realAddValuation_sub_algebraMap_le_of_adjoin_eq_top
      (h.adjoin_eq_top_of_irreducible hξ') ξ σ)

/-- **Uniformizer invariance of `conjugateBreaks`.** Two uniformizers of a totally ramified
extension `L/K` yield the same multiset of rational root-difference breaks in `M`. -/
theorem conjugateBreaks_eq_of_irreducible [Module.Finite K L] (h : IsTotallyRamified K L)
    {ξ ξ' : 𝒪[L]} (hξ : Irreducible ξ) (hξ' : Irreducible ξ') :
    conjugateBreaks K L M (ξ : L) = conjugateBreaks K L M (ξ' : L) := by
  classical
  rw [conjugateBreaks_def, conjugateBreaks_def]
  refine Multiset.map_congr rfl fun σ _ ↦ ?_
  have heq := congrArg WithTop.untop₀
    (realAddValuation_sub_algebraMap_eq_of_irreducible h hξ hξ' σ)
  rw [untop₀_realAddValuation, untop₀_realAddValuation] at heq
  have hlog : (WithZero.log (normalizedValuationWithZero M (σ (ξ : L) - algebraMap L M (ξ : L))) :
      ℤ) = WithZero.log (normalizedValuationWithZero M (σ (ξ' : L) - algebraMap L M (ξ' : L))) :=
    Int.cast_injective heq
  rw [hlog]

private theorem minpoly_eq_map_of_eisenstein_isRoot {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) :
    minpoly K α = φ.map (algebraMap 𝒪[K] K) := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  have hα : α ∈ 𝒪[L] := mem_integer_of_isRoot_monic hmonic hroot
  set ξ : 𝒪[L] := ⟨α, hα⟩
  have hint : IsIntegral 𝒪[K] ξ := IsIntegral.of_finite 𝒪[K] ξ
  have heq : minpoly 𝒪[K] ξ = φ := eq_of_monic_of_associated (minpoly.monic hint) hmonic
    (hφ.associated_minpoly hφ.isUnit_leadingCoeff (isRoot_map_integerRing_of_isRoot hα hroot))
  have hminK : minpoly K (ξ : L) = (minpoly 𝒪[K] ξ).map (algebraMap 𝒪[K] K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions K L hint
  rwa [heq] at hminK

omit [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra L M]
  [IsScalarTower K L M] [ValuativeExtension L M] in
private theorem map_univ_algHom_eq_roots [Algebra.IsSeparable K L] [Module.Finite K L]
    {φ : 𝒪[K][X]} (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤) :
    (Finset.univ : Finset (L →ₐ[K] M)).val.map (fun σ ↦ σ α) =
      (φ.map ((algebraMap K M).comp (algebraMap 𝒪[K] K))).roots := by
  classical
  have hmin := minpoly_eq_map_of_eisenstein_isRoot hmonic hφ hroot
  let pb : PowerBasis K L := PowerBasis.ofAdjoinSimpleEqTop (Algebra.IsIntegral.isIntegral α) hgen
  have hpb : pb.gen = α := PowerBasis.ofAdjoinSimpleEqTop_gen _ hgen
  have hinj : Function.Injective (fun σ : L →ₐ[K] M ↦ σ α) := fun σ τ hστ ↦
    pb.algHom_ext (by simpa [hpb] using hστ)
  have hmap : φ.map ((algebraMap K M).comp (algebraMap 𝒪[K] K)) =
      (minpoly K pb.gen).map (algebraMap K M) := by
    rw [hpb, hmin, Polynomial.map_map]
  have hsep : ((minpoly K pb.gen).map (algebraMap K M)).Separable :=
    Polynomial.Separable.map (Algebra.IsSeparable.isSeparable K pb.gen)
  refine (Multiset.Nodup.ext (Finset.univ.nodup.map hinj) (hmap ▸ nodup_roots hsep)).mpr fun y ↦ ?_
  rw [hmap, Multiset.mem_map]
  constructor
  · rintro ⟨σ, -, rfl⟩
    rw [← hpb]
    exact (pb.liftEquiv' σ).2
  · intro hy
    have hy0 : aeval y (minpoly K pb.gen) = 0 := by
      rw [aeval_def, ← eval_map]
      exact (mem_roots (map_monic_ne_zero (minpoly.monic pb.isIntegral_gen))).mp hy
    exact ⟨pb.lift y hy0, Finset.mem_univ _, hpb ▸ pb.lift_gen y hy0⟩

/-- **Newton-slope dictionary.** When `L = K(α)` is separable and `φ` splits over `M`, the finite
Newton slopes of `ramificationPolynomial φ α` are the negated real casts of
`conjugateBreaks K L M α`. -/
theorem newtonSlopes_ramificationPolynomial_eq_map_conjugateBreaks
    [Algebra.IsSeparable K L] [Module.Finite K L] {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    (hsplit : (φ.map ((algebraMap K M).comp (algebraMap 𝒪[K] K))).Splits) :
    (ramificationPolynomial φ α).newtonSlopes (realAddValuation L) =
      (conjugateBreaks K L M α).map (fun q : ℚ ↦ -(q : ℝ)) := by
  classical
  have : ValuativeExtension K M := ValuativeExtension.trans K L M
  obtain ⟨-, -, hα0, hvα, -⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hmonic hφ hroot hgen
  have hepos : 0 < (ramificationIndex L M : ℝ) :=
    Nat.cast_pos.mpr (ramificationIndex_pos (K := L) (L := M))
  refine Multiset.map_injective (mul_right_injective₀ hepos.ne') ?_
  rw [← newtonSlopes_map_eq_map_mul (ramificationPolynomial φ α) (realAddValuation L)
      (algebraMap L M) hepos (fun x ↦ realAddValuation_algebraMap x),
    newtonSlopes_eq_map_roots (fun _ ↦ realAddValuation_eq_top_iff.mp)
      (splits_map_ramificationPolynomial α hsplit),
    roots_map_ramificationPolynomial φ hα0,
    ← map_univ_algHom_eq_roots hmonic hφ hroot hgen,
    Multiset.map_map, Multiset.filter_map, Multiset.map_map, conjugateBreaks_def,
    Multiset.map_map, Multiset.map_map, Finset.filter_val]
  let pb : PowerBasis K L := PowerBasis.ofAdjoinSimpleEqTop (Algebra.IsIntegral.isIntegral α) hgen
  have hpb : pb.gen = α := PowerBasis.ofAdjoinSimpleEqTop_gen _ hgen
  have haM : algebraMap L M α ≠ 0 := (map_ne_zero (algebraMap L M)).mpr hα0
  have hvaM :
      realAddValuation M (algebraMap L M α) = ((ramificationIndex L M : ℝ) : WithTop ℝ) := by
    rw [realAddValuation_algebraMap, hvα, WithTop.map_one, mul_one]
  have hfilt : (Finset.univ : Finset (L →ₐ[K] M)).val.filter
        (((· ≠ 0) ∘ fun r ↦ (r - algebraMap L M α) / algebraMap L M α) ∘ fun σ ↦ σ α) =
      (Finset.univ : Finset (L →ₐ[K] M)).val.filter (· ≠ IsScalarTower.toAlgHom K L M) := by
    refine Multiset.filter_congr fun σ _ ↦ ?_
    simp only [Function.comp_apply, ne_eq, div_eq_zero_iff, haM, or_false, sub_eq_zero]
    exact not_congr ⟨fun heq ↦ pb.algHom_ext (by simpa [hpb] using heq), fun hσ ↦ by simp [hσ]⟩
  refine Multiset.map_congr hfilt fun σ hσ ↦ ?_
  have hσ_ne : σ ≠ IsScalarTower.toAlgHom K L M := (Multiset.mem_filter.mp hσ).2
  have hsub_ne : σ α - algebraMap L M α ≠ 0 := sub_ne_zero.mpr fun heq ↦
    hσ_ne (pb.algHom_ext (by simpa [hpb] using heq))
  have hmul : (σ α - algebraMap L M α) / algebraMap L M α * algebraMap L M α =
      σ α - algebraMap L M α := div_mul_cancel₀ _ haM
  have hvprod := congrArg (realAddValuation M) hmul
  rw [(realAddValuation M).map_mul, hvaM, realAddValuation_of_ne_zero hsub_ne] at hvprod
  simp only [Function.comp_apply]
  cases hq : realAddValuation M ((σ α - algebraMap L M α) / algebraMap L M α) with
  | top =>
    rw [hq, top_add] at hvprod
    exact absurd hvprod WithTop.top_ne_coe
  | coe r =>
    rw [hq, ← WithTop.coe_add, WithTop.coe_eq_coe] at hvprod
    simp only [WithTop.untop₀_coe, Rat.cast_sub, Rat.cast_div, Rat.cast_intCast,
      Rat.cast_natCast, Rat.cast_one]
    have he0 : (ramificationIndex L M : ℝ) ≠ 0 := hepos.ne'
    field_simp [he0]
    linarith

omit [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [ValuativeExtension L M] in
private theorem minpoly_eisenstein_data [Normal K M]
    (h : IsTotallyRamified K L) {ξ : 𝒪[L]} (hξ : Irreducible ξ) :
    (minpoly 𝒪[K] ξ).Monic ∧ (minpoly 𝒪[K] ξ).IsEisensteinAt 𝓂[K] ∧
      ((minpoly 𝒪[K] ξ).map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot (ξ : L) ∧
      K⟮(ξ : L)⟯ = ⊤ ∧
      ((minpoly 𝒪[K] ξ).map ((algebraMap K M).comp (algebraMap 𝒪[K] K))).Splits := by
  have hint : IsIntegral 𝒪[K] ξ := IsIntegral.of_finite 𝒪[K] ξ
  have hmonic : (minpoly 𝒪[K] ξ).Monic := minpoly.monic hint
  have hφ : (minpoly 𝒪[K] ξ).IsEisensteinAt 𝓂[K] := h.isEisensteinAt_minpoly hξ
  have hminK : minpoly K (ξ : L) = (minpoly 𝒪[K] ξ).map (algebraMap 𝒪[K] K) := by
    simpa only [Algebra.algebraMap_ofSubsemiring_apply] using
      minpoly.isIntegrallyClosed_eq_field_fractions K L hint
  have hroot : ((minpoly 𝒪[K] ξ).map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot
      (ξ : L) := by
    rw [IsRoot, ← Polynomial.map_map, ← hminK, eval_map, ← aeval_def, minpoly.aeval]
  have hgen : K⟮(ξ : L)⟯ = ⊤ := by
    simpa only [Algebra.algebraMap_ofSubsemiring_apply] using
      IntermediateField.adjoin_eq_top_of_algebra_adjoin_eq_top
        (R := 𝒪[K]) (S := 𝒪[L]) (K := K) (L := L) (h.adjoin_eq_top_of_irreducible hξ)
  have hsplit : ((minpoly 𝒪[K] ξ).map ((algebraMap K M).comp (algebraMap 𝒪[K] K))).Splits := by
    rw [← Polynomial.map_map, ← hminK, ← minpoly.algebraMap_eq (algebraMap L M).injective (ξ : L)]
    exact (Normal.out ‹Normal K M› (algebraMap L M (ξ : L))).2
  exact ⟨hmonic, hφ, hroot, hgen, hsplit⟩

/-- In a separable totally ramified extension `L/K` inside a normal extension `M/K`, every break in
`conjugateBreaks K L M (ξ : L)` of a uniformizer `ξ` is nonnegative. -/
theorem nonneg_of_mem_conjugateBreaks [Algebra.IsSeparable K L] [Normal K M] [Module.Finite K L]
    (h : IsTotallyRamified K L) {ξ : 𝒪[L]} (hξ : Irreducible ξ) {q : ℚ}
    (hq : q ∈ conjugateBreaks K L M (ξ : L)) :
    0 ≤ q := by
  obtain ⟨hmonic, hφ, hroot, hgen, hsplit⟩ := minpoly_eisenstein_data (M := M) h hξ
  have hmem : -(q : ℝ) ∈
      (ramificationPolynomial (minpoly 𝒪[K] ξ) (ξ : L)).newtonSlopes (realAddValuation L) := by
    rw [newtonSlopes_ramificationPolynomial_eq_map_conjugateBreaks hmonic hφ hroot hgen hsplit]
    exact Multiset.mem_map_of_mem _ hq
  have hle := nonpos_of_mem_newtonSlopes_ramificationPolynomial hmonic hφ hroot hgen hmem
  exact_mod_cast neg_nonpos.mp hle

/-- **Tame zero-break count.** In a separable totally ramified extension `L/K` inside a normal
extension `M/K`, exactly `[L : K] - p ^ padicValNat p (ramificationIndex K L)` entries of
`conjugateBreaks K L M (ξ : L)` vanish. -/
theorem card_filter_conjugateBreaks_eq_zero [Algebra.IsSeparable K L] [Normal K M]
    [Module.Finite K L] (h : IsTotallyRamified K L) {ξ : 𝒪[L]} (hξ : Irreducible ξ) :
    ((conjugateBreaks K L M (ξ : L)).filter (· = 0)).card =
      Module.finrank K L -
        (ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) (ramificationIndex K L) := by
  classical
  obtain ⟨hmonic, hφ, hroot, hgen, hsplit⟩ := minpoly_eisenstein_data (M := M) h hξ
  obtain ⟨-, -, -, -, he⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hmonic hφ hroot hgen
  have htr : ramificationIndex K L = Module.finrank K L :=
    (isTotallyRamified_iff_ramificationIndex_eq_finrank K L).mp h
  have hinj : Function.Injective (fun q : ℚ ↦ -(q : ℝ)) :=
    neg_injective.comp Rat.cast_injective
  have hfilt : (conjugateBreaks K L M (ξ : L)).filter (· = 0) =
      (conjugateBreaks K L M (ξ : L)).filter (0 = ·) :=
    Multiset.filter_congr fun _ _ ↦ eq_comm
  have hzero : (0 : ℝ) = -((0 : ℚ) : ℝ) := by simp
  have hcnt : ((conjugateBreaks K L M (ξ : L)).filter (· = 0)).card =
      ((ramificationPolynomial (minpoly 𝒪[K] ξ) (ξ : L)).newtonSlopes
        (realAddValuation L)).count 0 := by
    rw [hfilt, ← Multiset.count_eq_card_filter_eq,
      newtonSlopes_ramificationPolynomial_eq_map_conjugateBreaks hmonic hφ hroot hgen hsplit,
      hzero, Multiset.count_map_eq_count' _ _ hinj]
  rw [hcnt, count_zero_newtonSlopes_ramificationPolynomial hmonic hφ hroot hgen, ← he]
  nth_rw 1 [htr]

end Tower

section GeneratorInvariance

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Algebra.IsSeparable K L]

/-- **Generator invariance of the Newton slopes.** Any two monic Eisenstein generators `(φ, α)`
and `(φ', α')` of a separable extension `L/K` have identical finite Newton slopes under
`realAddValuation L`. -/
theorem newtonSlopes_ramificationPolynomial_eq {φ φ' : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    (hmonic' : φ'.Monic) (hφ' : φ'.IsEisensteinAt 𝓂[K]) {α' : L}
    (hroot' : (φ'.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α')
    (hgen' : K⟮α'⟯ = ⊤) :
    (ramificationPolynomial φ α).newtonSlopes (realAddValuation L) =
      (ramificationPolynomial φ' α').newtonSlopes (realAddValuation L) := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  obtain ⟨hα, hξ, -, -, -⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hmonic hφ hroot hgen
  obtain ⟨hα', hξ', -, -, -⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hmonic' hφ' hroot' hgen'
  have htot : IsTotallyRamified K L :=
    isTotallyRamified_of_eisenstein_adjoin_eq_top hφ (isRoot_map_integerRing_of_isRoot hα hroot)
      hgen
  set f := φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))
  set f' := φ'.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))
  set M := (f * f').SplittingField
  let _ : ValuativeRel M := algebraicExtensionValuativeRel L M
  let _ : TopologicalSpace M := algebraicExtensionNormedFieldTopology L M
  have : IsNonarchimedeanLocalField M := finiteExtension_isNonarchimedeanLocalField L M
  have : ValuativeExtension L M := algebraicExtension_valuativeExtension L M
  have hsp : ((f * f').map (algebraMap L M)).Splits := Polynomial.SplittingField.splits (f * f')
  rw [Polynomial.map_mul] at hsp
  have hmap (g : 𝒪[K][X]) :
      (g.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).map (algebraMap L M) =
        g.map ((algebraMap K M).comp (algebraMap 𝒪[K] K)) := by
    have hhom : (algebraMap L M).comp ((algebraMap K L).comp (algebraMap 𝒪[K] K)) =
        (algebraMap K M).comp (algebraMap 𝒪[K] K) := by
      ext x
      exact (IsScalarTower.algebraMap_apply K L M (algebraMap 𝒪[K] K x)).symm
    rw [Polynomial.map_map, hhom]
  have hf0 : f.map (algebraMap L M) ≠ 0 := ((hmonic.map _).map _).ne_zero
  have hf0' : f'.map (algebraMap L M) ≠ 0 := ((hmonic'.map _).map _).ne_zero
  have hsp₁ : (φ.map ((algebraMap K M).comp (algebraMap 𝒪[K] K))).Splits :=
    hmap φ ▸ (splits_mul'.mp hsp).1.resolve_right hf0'
  have hsp₂ : (φ'.map ((algebraMap K M).comp (algebraMap 𝒪[K] K))).Splits :=
    hmap φ' ▸ (splits_mul'.mp hsp).2.resolve_right hf0
  rw [newtonSlopes_ramificationPolynomial_eq_map_conjugateBreaks (M := M) hmonic hφ hroot hgen hsp₁,
    newtonSlopes_ramificationPolynomial_eq_map_conjugateBreaks (M := M) hmonic' hφ' hroot' hgen'
      hsp₂,
    conjugateBreaks_eq_of_irreducible (M := M) htot hξ hξ']

/-- **Generator invariance of the ramification polygon.** Any two monic Eisenstein generators
`(φ, α)` and `(φ', α')` of a separable extension `L/K` have identical ramification polygon under
`realAddValuation L`. -/
theorem newtonPolygon_ramificationPolynomial_eq {φ φ' : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    (hmonic' : φ'.Monic) (hφ' : φ'.IsEisensteinAt 𝓂[K]) {α' : L}
    (hroot' : (φ'.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α')
    (hgen' : K⟮α'⟯ = ⊤) :
    (ramificationPolynomial φ α).newtonPolygon (realAddValuation L) =
      (ramificationPolynomial φ' α').newtonPolygon (realAddValuation L) := by
  obtain ⟨-, -, hα0, -, he⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hmonic hφ hroot hgen
  obtain ⟨-, -, hα0', -, he'⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hmonic' hφ' hroot' hgen'
  have hdeg : φ.natDegree = φ'.natDegree := he.symm.trans he'
  have hn1 : 1 ≤ φ.natDegree := he ▸ ramificationIndex_pos (K := K) (L := L)
  have hdom {g : 𝒪[K][X]} (hg : g.Monic) (hgeis : g.IsEisensteinAt 𝓂[K]) {β : L} (hβ0 : β ≠ 0)
      (hβr : (g.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot β) (hβg : K⟮β⟯ = ⊤)
      (hd : g.natDegree = φ.natDegree) (n : ℕ) :
      (ramificationPolynomial g β).newtonPolygon (realAddValuation L) n ≠ ⊤ ↔
        1 ≤ n ∧ n ≤ 1 + (φ.natDegree - 1) := by
    rw [newtonPolygon_ne_top_iff (realAddValuation L) (fun _ ↦ realAddValuation_eq_top_iff.mp)
        (hg.ramificationPolynomial hβ0).ne_zero,
      natTrailingDegree_ramificationPolynomial hg hgeis hβr hβg,
      hg.natDegree_ramificationPolynomial hβ0, hd, Nat.add_sub_cancel' hn1]
  let d := FiniteSlopeData.ofIsConvexSeq
    ((ramificationPolynomial φ α).isConvexSeq_newtonPolygon (realAddValuation L))
    (hdom hmonic hφ hα0 hroot hgen rfl)
  let d' := FiniteSlopeData.ofIsConvexSeq
    ((ramificationPolynomial φ' α').isConvexSeq_newtonPolygon (realAddValuation L))
    (hdom hmonic' hφ' hα0' hroot' hgen' hdeg.symm)
  have hd : d.heights = (ramificationPolynomial φ α).newtonPolygon (realAddValuation L) :=
    FiniteSlopeData.heights_ofIsConvexSeq _ _
  have hd' : d'.heights = (ramificationPolynomial φ' α').newtonPolygon (realAddValuation L) :=
    FiniteSlopeData.heights_ofIsConvexSeq _ _
  have hdeq : d = d' := FiniteSlopeData.eq_of_slopeMultiset_eq (by simp [d, d'])
    (by simp [d, d', newtonPolygon_ramificationPolynomial_one hmonic hφ hroot hgen,
      newtonPolygon_ramificationPolynomial_one hmonic' hφ' hroot' hgen', hdeg])
    (by rw [← newtonSlopes_eq_slopeMultiset hd, ← newtonSlopes_eq_slopeMultiset hd',
      newtonSlopes_ramificationPolynomial_eq hmonic hφ hroot hgen hmonic' hφ' hroot' hgen'])
  rw [← hd, ← hd', hdeq]

end GeneratorInvariance

end ConjugateBreaks

end TauCeti
