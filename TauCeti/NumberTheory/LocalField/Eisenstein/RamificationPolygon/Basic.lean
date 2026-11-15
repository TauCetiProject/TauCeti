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

For a monic Eisenstein polynomial `φ ∈ 𝒪[K][X]` of degree `n` with root `α` generating `L = K(α)`,
the *ramification polygon* is `(ramificationPolynomial φ α).newtonPolygon (realAddValuation L)`.
This file proves its `p`-power contact theorem, horizontal tame segment `[p ^ w, n]`, rational
negative-slope face structure, and conjugate root-difference invariance.

## Main definitions

* `TauCeti.conjugateBreaks`: multiset of rational breaks `v_M(σ ξ - ξ) / e(M/L) - 1` over
  `K`-embeddings `σ : L →ₐ[K] M` distinct from `IsScalarTower.toAlgHom K L M`.

## Main results

* `TauCeti.exists_eq_pow_of_mem_supportingFace_of_neg` and
  `TauCeti.isFiniteFace_zero_newtonPolygon_ramificationPolynomial`: `p`-power contact abscissae on
  negative slopes and the horizontal tame face `[p ^ w, n]`.
* `TauCeti.exists_pow_endpoints_of_isFiniteFace_of_neg`,
  `TauCeti.exists_rat_neg_eq_and_den_dvd_of_isFiniteFace_of_neg` and
  `TauCeti.unitSlope_newtonPolygon_ramificationPolynomial_eq_on_Ico_pow`: `p`-power endpoints,
  rational slopes and constancy on `[p ^ k, p ^ (k + 1))`.
* `TauCeti.conjugateBreaks_eq_of_irreducible`,
  `TauCeti.newtonSlopes_ramificationPolynomial_eq_map_conjugateBreaks` and
  `TauCeti.newtonPolygon_ramificationPolynomial_eq`: uniformizer and generator invariance.

## References

* O. Ore, *Bemerkungen zur Theorie der Differente*, Math. Z. 25 (1926), 1–8.
* C. Greve and S. Pauli, *Ramification polygons, splitting fields, and Galois groups of Eisenstein
  polynomials*, Int. J. Number Theory 8 (2012), 1401–1424, §4.
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

private theorem le_of_add_natCast_le {a b : WithTop ℝ} {n : ℕ}
    (h : a + (n : WithTop ℝ) ≤ b + (n : WithTop ℝ)) : a ≤ b := by
  cases a <;> cases b <;>
    simp_all only [top_add, le_top, le_rfl, ← WithTop.coe_natCast, ← WithTop.coe_add,
      WithTop.top_le_iff, WithTop.coe_ne_top, WithTop.coe_le_coe]
  linarith

/-- Greve–Pauli's coefficient inequality: for `p = ringChar 𝓀[K]` and `p ∤ u`, `v_L(ρ_{p^r}) ≤
v_L(ρ_{p^r u})`. -/
theorem realAddValuation_coeff_pow_le_coeff_pow_mul {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    (r : ℕ) {u : ℕ} (hu : ¬ ringChar 𝓀[K] ∣ u) :
    realAddValuation L ((ramificationPolynomial φ α).coeff ((ringChar 𝓀[K]) ^ r)) ≤
      realAddValuation L ((ramificationPolynomial φ α).coeff ((ringChar 𝓀[K]) ^ r * u)) := by
  set p := ringChar 𝓀[K]
  have hp : p.Prime := CharP.char_is_prime 𝓀[K] p
  have hpr : 1 ≤ p ^ r := Nat.one_le_pow r p hp.pos
  have hpru : p ^ r ≤ p ^ r * u :=
    Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero fun h : u = 0 ↦ hu (h ▸ dvd_zero p))
  rcases lt_or_ge φ.natDegree (p ^ r * u) with hgt | _
  · simp [coeff_ramificationPolynomial_eq_zero_of_lt hgt]
  refine le_of_add_natCast_le (n := φ.natDegree) ?_
  rw [realAddValuation_coeff_ramificationPolynomial_add_natDegree hmonic hφ hroot hgen hpr,
    realAddValuation_coeff_ramificationPolynomial_add_natDegree hmonic hφ hroot hgen
      (hpr.trans hpru), Finset.le_inf_iff]
  intro h hh
  obtain ⟨hh₁, hh₂⟩ := Finset.mem_Icc.mp hh
  refine (Finset.inf_le (Finset.mem_Icc.mpr ⟨hpru.trans hh₁, hh₂⟩)).trans (add_le_add ?_ le_rfl)
  refine WithTop.monotone_map_iff.mpr
    (fun _ _ hab ↦ mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg _)) ?_
  simp only [Subring.coe_mul, Subring.coe_natCast, (realAddValuation K).map_mul]
  refine add_le_add ?_ le_rfl
  rw [realAddValuation_natCast_eq_nsmul (Nat.choose_pos (hpru.trans hh₁)).ne',
    realAddValuation_natCast_eq_nsmul (Nat.choose_pos hh₁).ne']
  obtain ⟨k, hk⟩ :=
    Nat.exists_eq_add_of_le (Nat.factorization_choose_pow_le_choose_pow_mul hp hu hh₁)
  rw [hk, add_nsmul]
  exact le_add_of_nonneg_right
    (nsmul_nonneg (mem_integer_iff_realAddValuation_nonneg.mp (natCast_mem 𝒪[K] p)) k)

/-- **`p`-power contact theorem.** Every contact point of the coefficient heights of
`ramificationPolynomial φ α` on a negative-slope supporting line is a power of `ringChar 𝓀[K]`. -/
theorem exists_eq_pow_of_mem_supportingFace_of_neg {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    {σ c : ℝ} (hσ : σ < 0)
    (hc : IsSupportingLine (fun m ↦ realAddValuation L ((ramificationPolynomial φ α).coeff m)) σ c)
    {m : ℕ} (hm : m ∈ supportingFace
      (fun m ↦ realAddValuation L ((ramificationPolynomial φ α).coeff m)) σ c) :
    ∃ i : ℕ, m = (ringChar 𝓀[K]) ^ i := by
  set p := ringChar 𝓀[K]
  have hp : p.Prime := CharP.char_is_prime 𝓀[K] p
  have hm0 : m ≠ 0 := by
    rintro rfl
    simpa [coeff_zero_ramificationPolynomial_of_isRoot hroot] using mem_supportingFace.mp hm
  set i := m.factorization p; set u := m / p ^ i
  have hmu : p ^ i * u = m := Nat.ordProj_mul_ordCompl_eq_self m p
  refine ⟨i, by_contra fun hne ↦ ?_⟩
  have hlt : p ^ i < m := hmu ▸ lt_mul_of_one_lt_right (pow_pos hp.pos i)
    (Nat.lt_of_le_of_ne (Nat.pos_of_ne_zero fun h ↦ hm0 (by rw [← hmu, h, mul_zero]))
      (Ne.symm fun h ↦ hne (by rw [← hmu, h, mul_one])))
  have hline := (isSupportingLine_iff_forall.mp hc (p ^ i)).trans
    ((realAddValuation_coeff_pow_le_coeff_pow_mul hmonic hφ hroot hgen i
      (Nat.not_dvd_ordCompl hp hm0)).trans_eq (hmu.symm ▸ mem_supportingFace.mp hm))
  rw [hmu, WithTop.coe_le_coe] at hline
  have : ((p ^ i : ℕ) : ℝ) < m := Nat.cast_lt.mpr hlt
  nlinarith

/-- At `p ^ w` (`w = padicValNat p φ.natDegree`), `(ramificationPolynomial φ α).coeff (p ^ w)` has
valuation `0`. -/
theorem realAddValuation_coeff_pow_padicValNat_ramificationPolynomial {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤) :
    realAddValuation L ((ramificationPolynomial φ α).coeff
      ((ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree)) = 0 := by
  obtain ⟨-, -, -, -, he⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hmonic hφ hroot hgen
  set p := ringChar 𝓀[K]; set n := φ.natDegree; set w := padicValNat p n
  have hp : p.Prime := CharP.char_is_prime 𝓀[K] p
  have hnpos : 0 < n := he ▸ ramificationIndex_pos (K := K) (L := L)
  have hfac : n.factorization p = w := (Nat.factorization_def n hp).trans Nat.padicValNat_def.symm
  refine le_antisymm (le_of_add_natCast_le (n := n) ?_)
    (realAddValuation_coeff_ramificationPolynomial_nonneg hmonic hφ hroot hgen (p ^ w))
  rw [zero_add, realAddValuation_coeff_ramificationPolynomial_add_natDegree hmonic hφ hroot hgen
    (Nat.one_le_pow w p hp.pos)]
  refine (Finset.inf_le (Finset.mem_Icc.mpr
    ⟨hfac ▸ Nat.le_of_dvd hnpos (Nat.ordProj_dvd n p), le_rfl⟩)).trans ?_
  rw [show (((n.choose (p ^ w) : 𝒪[K]) * φ.coeff n : 𝒪[K]) : K) = (n.choose (p ^ w) : K) by
    simp [n, hmonic.coeff_natDegree],
    realAddValuation_natCast_eq_zero_iff_not_dvd.mpr
      (hfac ▸ Nat.not_dvd_choose_pow_factorization hp hnpos.ne')]
  simp [n]

/-- For `1 ≤ i < p ^ padicValNat p φ.natDegree`, `(ramificationPolynomial φ α).coeff i` has
valuation at least `1`. -/
theorem one_le_realAddValuation_coeff_of_lt_pow_padicValNat {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i < (ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree) :
    1 ≤ realAddValuation L ((ramificationPolynomial φ α).coeff i) := by
  set p := ringChar 𝓀[K]; set n := φ.natDegree
  have hp : p.Prime := CharP.char_is_prime 𝓀[K] p
  have hfac : n.factorization p = padicValNat p n :=
    (Nat.factorization_def n hp).trans Nat.padicValNat_def.symm
  have hmono : Monotone (WithTop.map ((n : ℝ) * ·)) :=
    WithTop.monotone_map_iff.mpr fun _ _ hab ↦ mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg _)
  refine le_of_add_natCast_le (n := n) ?_
  rw [realAddValuation_coeff_ramificationPolynomial_add_natDegree hmonic hφ hroot hgen hi1,
    Finset.le_inf_iff]
  intro h hh
  obtain ⟨hih, hhn⟩ := Finset.mem_Icc.mp hh
  have h1 : 1 ≤ realAddValuation K (((h.choose i : 𝒪[K]) * φ.coeff h : 𝒪[K]) : K) := by
    rcases eq_or_lt_of_le hhn with rfl | hlt
    · simpa [hmonic.coeff_natDegree] using one_le_realAddValuation_natCast_iff_dvd (K := K).mpr
        (Nat.dvd_choose_of_lt_pow_factorization hp hi1 (hfac.symm ▸ hi))
    · exact mem_maximalIdeal_iff_one_le_realAddValuation.mp (Ideal.mul_mem_left _ _ (hφ.mem hlt))
  refine (show (1 : WithTop ℝ) + (n : WithTop ℝ) ≤
      (1 : WithTop ℝ).map ((n : ℝ) * ·) + (h : WithTop ℝ) by
    simp only [← WithTop.coe_one, ← WithTop.coe_natCast, WithTop.map_coe, mul_one,
      ← WithTop.coe_add, WithTop.coe_le_coe]
    have : (1 : ℝ) ≤ h := by exact_mod_cast hi1.trans hih
    linarith).trans (add_le_add (hmono h1) le_rfl)

/-- **The tame segment.** The finite face of slope `0` of the ramification polygon runs from
`p ^ padicValNat p φ.natDegree` to `φ.natDegree`, where `p = ringChar 𝓀[K]`. -/
theorem isFiniteFace_zero_newtonPolygon_ramificationPolynomial {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤) :
    IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L)) 0
      ((ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree) φ.natDegree := by
  obtain ⟨-, -, hα0, -, he⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hmonic hφ hroot hgen
  set p := ringChar 𝓀[K]; set n := φ.natDegree; set w := padicValNat p n
  have hp : p.Prime := CharP.char_is_prime 𝓀[K] p
  have hnpos : 0 < n := he ▸ ramificationIndex_pos (K := K) (L := L)
  have hfac : n.factorization p = w := (Nat.factorization_def n hp).trans Nat.padicValNat_def.symm
  set ρ := ramificationPolynomial φ α
  have henv := ρ.isLowerConvexEnvelope_newtonPolygon (realAddValuation L)
  have hca : IsSupportingLine (fun m ↦ realAddValuation L (ρ.coeff m)) 0 0 :=
    isSupportingLine_iff_forall.mpr fun m ↦ by
      simpa using realAddValuation_coeff_ramificationPolynomial_nonneg hmonic hφ hroot hgen m
  have hcN : IsSupportingLine (ρ.newtonPolygon (realAddValuation L)) 0 0 :=
    henv.isSupportingLine_iff.mpr hca
  refine isFiniteFace_iff.mpr ⟨hfac ▸ Nat.le_of_dvd hnpos (Nat.ordProj_dvd n p), 0, hcN,
    Set.Subset.antisymm (fun m hm ↦ ⟨le_of_not_gt fun hlt ↦ ?_, le_of_not_gt fun hgt ↦ ?_⟩) ?_⟩
  · obtain ⟨k, hkm, hk⟩ := henv.exists_le_mem_supportingFace hca hm
    have hk0 : realAddValuation L (ρ.coeff k) = 0 := by simpa using mem_supportingFace.mp hk
    rcases eq_or_ne k 0 with rfl | hk_ne
    · rw [coeff_zero_ramificationPolynomial_of_isRoot hroot, (realAddValuation L).map_zero] at hk0
      exact WithTop.top_ne_coe hk0
    · exact absurd (hk0 ▸ one_le_realAddValuation_coeff_of_lt_pow_padicValNat hmonic hφ hroot hgen
        (Nat.one_le_iff_ne_zero.mpr hk_ne) (hkm.trans_lt hlt)) (by simp)
  · have hm0 := mem_supportingFace.mp hm
    rw [ρ.newtonPolygon_eq_top_of_natDegree_lt (realAddValuation L)
      ((natDegree_ramificationPolynomial_le φ α).trans_lt hgt)] at hm0
    exact WithTop.top_ne_coe hm0
  · exact ((ρ.isConvexSeq_newtonPolygon (realAddValuation L)).ordConnected_supportingFace hcN).out
      (henv.supportingFace_subset hca (by simpa using
        realAddValuation_coeff_pow_padicValNat_ramificationPolynomial hmonic hφ hroot hgen))
      (henv.supportingFace_subset hca (by simpa using
        realAddValuation_coeff_natDegree_ramificationPolynomial hmonic hα0))

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
    {s : ℝ} (hs : s ∈ (ramificationPolynomial φ α).newtonSlopes (realAddValuation L)) : s ≤ 0 := by
  obtain ⟨i, hi, rfl⟩ := (mem_newtonSlopes _ _).mp hs
  have hface := isFiniteFace_zero_newtonPolygon_ramificationPolynomial hmonic hφ hroot hgen
  have hin : i < φ.natDegree := lt_of_not_ge fun hge ↦
    (mem_finiteEdges.mp hi).2 ((ramificationPolynomial φ α).newtonPolygon_eq_top_of_natDegree_lt
      (realAddValuation L) ((natDegree_ramificationPolynomial_le φ α).trans_lt (by omega)))
  rcases lt_or_ge i ((ringChar 𝓀[K]) ^ padicValNat (ringChar 𝓀[K]) φ.natDegree) with hlt | hge
  · exact (hface.unitSlope_lt ((ramificationPolynomial φ α).isConvexSeq_newtonPolygon _) hi hlt).le
  · exact (hface.unitSlope_eq hge hin).le

/-- **Endpoints of negative-slope faces.** Every finite face of negative slope and positive width
has endpoints `p ^ a` and `p ^ (a + d)` with `0 < d` and `a + d ≤ padicValNat p φ.natDegree`. -/
theorem exists_pow_endpoints_of_isFiniteFace_of_neg {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    {σ : ℝ} {l u : ℕ} (hσ : σ < 0) (hlu : l < u)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L)) σ l u) :
    ∃ a d : ℕ, 0 < d ∧ a + d ≤ padicValNat (ringChar 𝓀[K]) φ.natDegree ∧
      l = (ringChar 𝓀[K]) ^ a ∧ u = (ringChar 𝓀[K]) ^ (a + d) := by
  set p := ringChar 𝓀[K]
  have hp : p.Prime := CharP.char_is_prime 𝓀[K] p
  obtain ⟨c, hc, ⟨hl_mem, -⟩, ⟨hu_mem, -⟩⟩ :=
    ((ramificationPolynomial φ α).isLowerConvexEnvelope_newtonPolygon
      (realAddValuation L)).exists_isSupportingLine_isLeast_isGreatest_of_isFiniteFace hface
  obtain ⟨a, ha⟩ := exists_eq_pow_of_mem_supportingFace_of_neg hmonic hφ hroot hgen hσ hc hl_mem
  obtain ⟨b, hb⟩ := exists_eq_pow_of_mem_supportingFace_of_neg hmonic hφ hroot hgen hσ hc hu_mem
  have hab : a < b := (Nat.pow_lt_pow_iff_right hp.one_lt).mp (ha ▸ hb ▸ hlu)
  have hun : u ≤ φ.natDegree := le_of_not_gt fun hgt ↦
    hface.right_ne_top ((ramificationPolynomial φ α).newtonPolygon_eq_top_of_natDegree_lt
      (realAddValuation L) ((natDegree_ramificationPolynomial_le φ α).trans_lt hgt))
  have huw : u ≤ p ^ padicValNat p φ.natDegree := le_of_not_gt fun hgt ↦ by
    have hgt' : ringChar 𝓀[K] ^ padicValNat (ringChar 𝓀[K]) φ.natDegree < u := hgt
    have := hface.unitSlope_eq (i := u - 1) (by omega) (by omega)
    have := (isFiniteFace_zero_newtonPolygon_ramificationPolynomial
      hmonic hφ hroot hgen).unitSlope_eq (i := u - 1) (by omega) (by omega)
    linarith
  have hbw : b ≤ padicValNat p φ.natDegree := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hb ▸ huw)
  exact ⟨a, b - a, Nat.sub_pos_of_lt hab, by omega, ha, by rw [hb]; congr 1; omega⟩

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension K L] in
/-- **Rationality and denominator bound on negative-slope faces.** Every finite face of strictly
negative slope and positive width has slope `-r` for `0 < r` in `ℚ` with `r.den ∣ u - l`. -/
theorem exists_rat_neg_eq_and_den_dvd_of_isFiniteFace_of_neg {φ : 𝒪[K][X]} {α : L}
    {σ : ℝ} {l u : ℕ} (hσ : σ < 0) (hlu : l < u)
    (hface : IsFiniteFace ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L)) σ l u) :
    ∃ r : ℚ, 0 < r ∧ σ = -(r : ℝ) ∧ r.den ∣ u - l := by
  obtain ⟨q, hq, hdvd⟩ :=
    ((ramificationPolynomial φ α).isLowerConvexEnvelope_newtonPolygon
      (realAddValuation L)).exists_rat_eq_and_den_dvd_of_isFiniteFace
      (fun _ hm ↦ exists_int_realAddValuation (mt realAddValuation_eq_top_iff.mpr hm)) hface hlu
  have hqneg : q < 0 := by exact_mod_cast hq.trans_lt hσ
  exact ⟨-q, neg_pos.mpr hqneg, by push_cast; linarith, Rat.den_neg_eq_den q ▸ hdvd⟩

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

/-- In separable `L = K(α)`, the ramification polygon starts at `(1, d(L/K) + 1 - φ.natDegree)`. -/
theorem newtonPolygon_ramificationPolynomial_one {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤) :
    (ramificationPolynomial φ α).newtonPolygon (realAddValuation L) 1 =
      (((differentExponent K L : ℝ) + 1 - φ.natDegree : ℝ) : WithTop ℝ) := by
  have htr := natTrailingDegree_ramificationPolynomial hmonic hφ hroot hgen
  rw [← htr, newtonPolygon_natTrailingDegree, trailingCoeff, htr,
    realAddValuation_coeff_one_ramificationPolynomial hmonic hφ hroot hgen]

/-- In separable `L = K(α)`, `ramificationPolynomial φ α` has `φ.natDegree - 1` Newton slopes. -/
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
    (k : ℕ) {i j : ℕ} (hi : i ∈ Set.Ico ((ringChar 𝓀[K]) ^ k) ((ringChar 𝓀[K]) ^ (k + 1)))
    (hj : j ∈ Set.Ico ((ringChar 𝓀[K]) ^ k) ((ringChar 𝓀[K]) ^ (k + 1)))
    (hin : i < φ.natDegree) (hjn : j < φ.natDegree) :
    unitSlope ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L)) i =
      unitSlope ((ramificationPolynomial φ α).newtonPolygon (realAddValuation L)) j := by
  obtain ⟨-, -, hα0, -, -⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hmonic hφ hroot hgen
  set p := ringChar 𝓀[K]; set ρ := ramificationPolynomial φ α
  set N := ρ.newtonPolygon (realAddValuation L)
  have hp : p.Prime := CharP.char_is_prime 𝓀[K] p
  have hedge : i ∈ finiteEdges N := by
    rw [ρ.finiteEdges_newtonPolygon (realAddValuation L) fun _ ↦ realAddValuation_eq_top_iff.mp,
      natTrailingDegree_ramificationPolynomial hmonic hφ hroot hgen,
      hmonic.natDegree_ramificationPolynomial hα0]
    exact ⟨(Nat.one_le_pow k p hp.pos).trans hi.1, hin⟩
  obtain ⟨l, u, hface⟩ := exists_isFiniteFace_newtonPolygon
    ((hmonic.ramificationPolynomial hα0).newtonPolygon_ne_top (realAddValuation L)) (unitSlope N i)
  have hiu : i ∈ Set.Ico l u :=
    (hface.setOf_unitSlope_eq (ρ.isConvexSeq_newtonPolygon _)).subset ⟨hedge, rfl⟩
  rcases eq_or_lt_of_le (nonpos_of_mem_newtonSlopes_ramificationPolynomial hmonic hφ hroot hgen
    ((mem_newtonSlopes _ _).mpr ⟨i, hedge, rfl⟩)) with hσ0 | hσneg
  · have hf0 := isFiniteFace_zero_newtonPolygon_ramificationPolynomial hmonic hφ hroot hgen
    obtain ⟨rfl, rfl⟩ := hf0.unique (hσ0 ▸ hface)
    have hwk := Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right hp.one_lt).mp (hiu.1.trans_lt hi.2))
    exact hσ0.trans (hf0.unitSlope_eq ((Nat.pow_le_pow_right hp.pos hwk).trans hj.1) hjn).symm
  · obtain ⟨a, d, -, -, rfl, rfl⟩ := exists_pow_endpoints_of_isFiniteFace_of_neg
      hmonic hφ hroot hgen hσneg (hiu.1.trans_lt hiu.2) hface
    have hak := Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right hp.one_lt).mp (hiu.1.trans_lt hi.2))
    have hkad := Nat.succ_le_of_lt ((Nat.pow_lt_pow_iff_right hp.one_lt).mp (hi.1.trans_lt hiu.2))
    exact (hface.unitSlope_eq ((Nat.pow_le_pow_right hp.pos hak).trans hj.1)
      (hj.2.trans_le (Nat.pow_le_pow_right hp.pos hkad))).symm

end SeparablePolygon

end PolygonGeometry

section ConjugateBreaks

open Classical in
/-- The multiset of rational root-difference breaks `v_M(σ ξ - ξ) / e(M/L) - 1` of `ξ : L` over all
`K`-embeddings `σ : L →ₐ[K] M` distinct from `IsScalarTower.toAlgHom K L M`. -/
def conjugateBreaks (K L M : Type*) [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M] (ξ : L) : Multiset ℚ :=
  ((Finset.univ : Finset (L →ₐ[K] M)).filter (· ≠ IsScalarTower.toAlgHom K L M)).val.map
    fun σ ↦ ((WithZero.log (normalizedValuationWithZero M (σ ξ - algebraMap L M ξ)) : ℤ) : ℚ) /
      ramificationIndex L M - 1

/-- Unfolding `conjugateBreaks` to its defining multiset map. -/
theorem conjugateBreaks_def (K L M : Type*) [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra K M]
    [Algebra L M] [IsScalarTower K L M] [DecidableEq (L →ₐ[K] M)] (ξ : L) :
    conjugateBreaks K L M ξ =
      ((Finset.univ : Finset (L →ₐ[K] M)).filter (· ≠ IsScalarTower.toAlgHom K L M)).val.map
      fun σ ↦ ((WithZero.log (normalizedValuationWithZero M (σ ξ - algebraMap L M ξ)) : ℤ) : ℚ) /
        ramificationIndex L M - 1 := by
  unfold conjugateBreaks; congr

section Tower

variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [Algebra L M] [IsScalarTower K L M] [ValuativeExtension L M]

/-- If `x ∈ 𝒪[L]` generates `𝒪[L]` over `𝒪[K]`, then `v_M(σ x - x) ≤ v_M(σ y - y)` for every
`y ∈ 𝒪[L]` and `σ : L →ₐ[K] M`. -/
theorem realAddValuation_sub_algebraMap_le_of_adjoin_eq_top
    {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) (y : 𝒪[L]) (σ : L →ₐ[K] M) :
    realAddValuation M (σ (x : L) - algebraMap L M (x : L)) ≤
      realAddValuation M (σ (y : L) - algebraMap L M (y : L)) := by
  have : ValuativeExtension K M := ValuativeExtension.trans K L M
  obtain ⟨P, hP⟩ : y ∈ (Polynomial.aeval x : 𝒪[K][X] →ₐ[𝒪[K]] 𝒪[L]).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval, hx]; exact Algebra.mem_top
  have hmem (τ : L →ₐ[K] M) : τ (x : L) ∈ 𝒪[M] := by
    rw [mem_integer_iff_realAddValuation_nonneg, τ.realAddValuation_apply,
      ← realAddValuation_algebraMap, show algebraMap L M (x : L) = (algebraMap 𝒪[L] 𝒪[M] x : M) by
      change algebraMap L M (algebraMap 𝒪[L] L x) = algebraMap 𝒪[M] M (algebraMap 𝒪[L] 𝒪[M] x)
      rw [← IsScalarTower.algebraMap_apply 𝒪[L] L M, ← IsScalarTower.algebraMap_apply 𝒪[L] 𝒪[M] M]]
    exact mem_integer_iff_realAddValuation_nonneg.mp (algebraMap 𝒪[L] 𝒪[M] x).2
  let c (τ : L →ₐ[K] M) : 𝒪[M] := ⟨τ (x : L), hmem τ⟩
  have heval (τ : L →ₐ[K] M) :
      algebraMap 𝒪[M] M ((P.map (algebraMap 𝒪[K] 𝒪[M])).eval (c τ)) = τ (y : L) := by
    have hhom : (algebraMap 𝒪[M] M).comp (algebraMap 𝒪[K] 𝒪[M]) =
        τ.toRingHom.comp ((algebraMap 𝒪[L] L).comp (algebraMap 𝒪[K] 𝒪[L])) := by
      rw [algebraMap_comp_algebraMap_integerRing, algebraMap_comp_algebraMap_integerRing]
      exact RingHom.ext fun d ↦ (τ.commutes (algebraMap 𝒪[K] K d)).symm
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hP
    rw [eval_map, hom_eval₂, ← hP, aeval_def]
    change P.eval₂ _ (τ (x : L)) = τ.toRingHom (algebraMap 𝒪[L] L (P.eval₂ _ x))
    rw [hom_eval₂, hom_eval₂, hhom]; rfl
  obtain ⟨q, hq⟩ := Polynomial.sub_dvd_eval_sub (c σ) (c (IsScalarTower.toAlgHom K L M))
    (P.map (algebraMap 𝒪[K] 𝒪[M]))
  have hval := congrArg (algebraMap 𝒪[M] M) hq
  simp only [map_sub, map_mul, heval] at hval
  rw [show σ (y : L) - algebraMap L M (y : L) = (σ (x : L) - algebraMap L M (x : L)) * (q : M) from
    hval, (realAddValuation M).map_mul]
  exact le_add_of_nonneg_right (mem_integer_iff_realAddValuation_nonneg.mp q.2)

/-- **Uniformizer invariance of root-difference valuations.** In a totally ramified extension
`L/K`, any two uniformizers of `𝒪[L]` have equal root-difference valuation at `σ : L →ₐ[K] M`. -/
theorem realAddValuation_sub_algebraMap_eq_of_irreducible
    (h : IsTotallyRamified K L) {ξ ξ' : 𝒪[L]} (hξ : Irreducible ξ) (hξ' : Irreducible ξ')
    (σ : L →ₐ[K] M) :
    realAddValuation M (σ (ξ : L) - algebraMap L M (ξ : L)) =
      realAddValuation M (σ (ξ' : L) - algebraMap L M (ξ' : L)) :=
  le_antisymm
    (realAddValuation_sub_algebraMap_le_of_adjoin_eq_top (h.adjoin_eq_top_of_irreducible hξ) ξ' σ)
    (realAddValuation_sub_algebraMap_le_of_adjoin_eq_top (h.adjoin_eq_top_of_irreducible hξ') ξ σ)

/-- **Uniformizer invariance of `conjugateBreaks`.** Two uniformizers of a totally ramified
extension `L/K` yield the same multiset of rational root-difference breaks in `M`. -/
theorem conjugateBreaks_eq_of_irreducible [Module.Finite K L] (h : IsTotallyRamified K L)
    {ξ ξ' : 𝒪[L]} (hξ : Irreducible ξ) (hξ' : Irreducible ξ') :
    conjugateBreaks K L M (ξ : L) = conjugateBreaks K L M (ξ' : L) := by
  classical
  rw [conjugateBreaks_def, conjugateBreaks_def]
  refine Multiset.map_congr rfl fun σ _ ↦ ?_
  have heq := congrArg WithTop.untop₀
    (realAddValuation_sub_algebraMap_eq_of_irreducible (M := M) h hξ hξ' σ)
  rw [untop₀_realAddValuation, untop₀_realAddValuation] at heq
  rw [Int.cast_injective heq]

private theorem minpoly_eq_map_of_eisenstein_isRoot {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) :
    minpoly K α = φ.map (algebraMap 𝒪[K] K) := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  have hα := mem_integer_of_isRoot_monic hmonic hroot
  have hint : IsIntegral 𝒪[K] (⟨α, hα⟩ : 𝒪[L]) := IsIntegral.of_finite 𝒪[K] _
  have heq : minpoly 𝒪[K] (⟨α, hα⟩ : 𝒪[L]) = φ :=
    eq_of_monic_of_associated (minpoly.monic hint) hmonic
      (hφ.associated_minpoly hφ.isUnit_leadingCoeff (isRoot_map_integerRing_of_isRoot hα hroot))
  exact (minpoly.isIntegrallyClosed_eq_field_fractions K L hint).trans (heq ▸ rfl)

omit [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra L M]
  [IsScalarTower K L M] [ValuativeExtension L M] in
private theorem map_univ_algHom_eq_roots [Algebra.IsSeparable K L] [Module.Finite K L]
    {φ : 𝒪[K][X]} (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤) :
    (Finset.univ : Finset (L →ₐ[K] M)).val.map (fun σ ↦ σ α) =
      (φ.map ((algebraMap K M).comp (algebraMap 𝒪[K] K))).roots := by
  classical
  let pb : PowerBasis K L := PowerBasis.ofAdjoinSimpleEqTop (Algebra.IsIntegral.isIntegral α) hgen
  have hpb : pb.gen = α := PowerBasis.ofAdjoinSimpleEqTop_gen _ hgen
  have hinj : Function.Injective (fun σ : L →ₐ[K] M ↦ σ α) := fun _ _ hστ ↦
    pb.algHom_ext (by simpa [hpb] using hστ)
  have hmap : φ.map ((algebraMap K M).comp (algebraMap 𝒪[K] K)) =
      (minpoly K pb.gen).map (algebraMap K M) := by
    rw [hpb, minpoly_eq_map_of_eisenstein_isRoot hmonic hφ hroot, Polynomial.map_map]
  refine (Multiset.Nodup.ext (Finset.univ.nodup.map hinj)
    (hmap ▸ nodup_roots (Polynomial.Separable.map (Algebra.IsSeparable.isSeparable K pb.gen)))).mpr
    fun y ↦ ?_
  rw [hmap, Multiset.mem_map]
  refine ⟨fun ⟨σ, _, hy⟩ ↦ hy ▸ hpb ▸ (pb.liftEquiv' σ).2, fun hy ↦ ?_⟩
  have hy0 : aeval y (minpoly K pb.gen) = 0 := by
    rw [aeval_def, ← eval_map]
    exact (mem_roots (map_monic_ne_zero (minpoly.monic pb.isIntegral_gen))).mp hy
  exact ⟨pb.lift y hy0, Finset.mem_univ _, hpb ▸ pb.lift_gen y hy0⟩

/-- **Newton-slope dictionary.** When `L = K(α)` is separable and `φ` splits over `M`, the finite
Newton slopes of `ramificationPolynomial φ α` are the negations of `conjugateBreaks K L M α`. -/
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
  have hepos : 0 < (ramificationIndex L M : ℝ) := Nat.cast_pos.mpr (ramificationIndex_pos (K := L))
  refine Multiset.map_injective (mul_right_injective₀ hepos.ne') ?_
  rw [← newtonSlopes_map_eq_map_mul (ramificationPolynomial φ α) (realAddValuation L)
      (algebraMap L M) hepos realAddValuation_algebraMap,
    newtonSlopes_eq_map_roots (fun _ ↦ realAddValuation_eq_top_iff.mp)
      (splits_map_ramificationPolynomial α hsplit),
    roots_map_ramificationPolynomial φ hα0, ← map_univ_algHom_eq_roots hmonic hφ hroot hgen,
    Multiset.map_map, Multiset.filter_map, Multiset.map_map, conjugateBreaks_def,
    Multiset.map_map, Multiset.map_map, Finset.filter_val]
  let pb : PowerBasis K L := PowerBasis.ofAdjoinSimpleEqTop (Algebra.IsIntegral.isIntegral α) hgen
  have hpb : pb.gen = α := PowerBasis.ofAdjoinSimpleEqTop_gen _ hgen
  have haM : algebraMap L M α ≠ 0 := (map_ne_zero (algebraMap L M)).mpr hα0
  refine Multiset.map_congr (Multiset.filter_congr fun σ _ ↦ by
    simp only [Function.comp_apply, ne_eq, div_eq_zero_iff, haM, or_false, sub_eq_zero]
    exact not_congr ⟨fun heq ↦ pb.algHom_ext (by simpa [hpb] using heq), fun hσ ↦ by simp [hσ]⟩)
    fun σ hσ ↦ ?_
  have hsub_ne : σ α - algebraMap L M α ≠ 0 := sub_ne_zero.mpr fun heq ↦
    (Multiset.mem_filter.mp hσ).2 (pb.algHom_ext (by simpa [hpb] using heq))
  have hvprod := congrArg (realAddValuation M) (div_mul_cancel₀ (σ α - algebraMap L M α) haM)
  rw [(realAddValuation M).map_mul, realAddValuation_algebraMap, hvα, WithTop.map_one, mul_one,
    realAddValuation_of_ne_zero hsub_ne] at hvprod
  simp only [Function.comp_apply]
  cases hq : realAddValuation M ((σ α - algebraMap L M α) / algebraMap L M α) with
  | top => rw [hq, top_add] at hvprod; exact absurd hvprod WithTop.top_ne_coe
  | coe r =>
    rw [hq, ← WithTop.coe_add, WithTop.coe_eq_coe] at hvprod
    simp only [WithTop.untop₀_coe, Rat.cast_sub, Rat.cast_div, Rat.cast_intCast,
      Rat.cast_natCast, Rat.cast_one]; field_simp [hepos.ne']; linarith

omit [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [ValuativeExtension L M] in
private theorem minpoly_eisenstein_data [Normal K M]
    (h : IsTotallyRamified K L) {ξ : 𝒪[L]} (hξ : Irreducible ξ) :
    (minpoly 𝒪[K] ξ).Monic ∧ (minpoly 𝒪[K] ξ).IsEisensteinAt 𝓂[K] ∧
      ((minpoly 𝒪[K] ξ).map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot (ξ : L) ∧
      K⟮(ξ : L)⟯ = ⊤ ∧
      ((minpoly 𝒪[K] ξ).map ((algebraMap K M).comp (algebraMap 𝒪[K] K))).Splits := by
  have hint : IsIntegral 𝒪[K] ξ := IsIntegral.of_finite 𝒪[K] ξ
  have hminK : minpoly K (ξ : L) = (minpoly 𝒪[K] ξ).map (algebraMap 𝒪[K] K) := by
    simpa only [Algebra.algebraMap_ofSubsemiring_apply] using
      minpoly.isIntegrallyClosed_eq_field_fractions K L hint
  refine ⟨minpoly.monic hint, h.isEisensteinAt_minpoly hξ, ?_, ?_, ?_⟩
  · rw [IsRoot, ← Polynomial.map_map, ← hminK, eval_map, ← aeval_def, minpoly.aeval]
  · simpa only [Algebra.algebraMap_ofSubsemiring_apply] using
      IntermediateField.adjoin_eq_top_of_algebra_adjoin_eq_top (K := K) (L := L)
        (h.adjoin_eq_top_of_irreducible hξ)
  · rw [← Polynomial.map_map, ← hminK, ← minpoly.algebraMap_eq (algebraMap L M).injective (ξ : L)]
    exact (Normal.out ‹Normal K M› (algebraMap L M (ξ : L))).2

/-- In separable totally ramified `L/K` in normal `M/K`, breaks in `conjugateBreaks` are `≥ 0`. -/
theorem nonneg_of_mem_conjugateBreaks [Algebra.IsSeparable K L] [Normal K M] [Module.Finite K L]
    (h : IsTotallyRamified K L) {ξ : 𝒪[L]} (hξ : Irreducible ξ) {q : ℚ}
    (hq : q ∈ conjugateBreaks K L M (ξ : L)) : 0 ≤ q := by
  obtain ⟨hmonic, hφ, hroot, hgen, hsplit⟩ := minpoly_eisenstein_data (M := M) h hξ
  have hmem : -(q : ℝ) ∈
      (ramificationPolynomial (minpoly 𝒪[K] ξ) (ξ : L)).newtonSlopes (realAddValuation L) := by
    rw [newtonSlopes_ramificationPolynomial_eq_map_conjugateBreaks hmonic hφ hroot hgen hsplit]
    exact Multiset.mem_map_of_mem _ hq
  exact_mod_cast neg_nonpos.mp
    (nonpos_of_mem_newtonSlopes_ramificationPolynomial hmonic hφ hroot hgen hmem)

/-- **Tame zero-break count.** `[L : K] - p ^ padicValNat p (ramificationIndex K L)` entries of
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
  rw [Multiset.filter_congr (fun _ _ ↦ eq_comm (b := (0 : ℚ))), ← Multiset.count_eq_card_filter_eq,
    ← Multiset.count_map_eq_count' (fun q : ℚ ↦ -(q : ℝ)) _ (neg_injective.comp Rat.cast_injective),
    ← newtonSlopes_ramificationPolynomial_eq_map_conjugateBreaks hmonic hφ hroot hgen hsplit]
  simp only [Rat.cast_zero, neg_zero,
    count_zero_newtonSlopes_ramificationPolynomial hmonic hφ hroot hgen, ← he]
  nth_rw 1 [(isTotallyRamified_iff_ramificationIndex_eq_finrank K L).mp h]

end Tower

section GeneratorInvariance

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Algebra.IsSeparable K L]

/-- **Generator invariance of the Newton slopes.** Any two monic Eisenstein generators `(φ, α)`
and `(φ', α')` of a separable extension `L/K` have identical finite Newton slopes. -/
theorem newtonSlopes_ramificationPolynomial_eq {φ φ' : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    (hmonic' : φ'.Monic) (hφ' : φ'.IsEisensteinAt 𝓂[K]) {α' : L}
    (hroot' : (φ'.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α') (hgen' : K⟮α'⟯ = ⊤) :
    (ramificationPolynomial φ α).newtonSlopes (realAddValuation L) =
      (ramificationPolynomial φ' α').newtonSlopes (realAddValuation L) := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  obtain ⟨hα, hξ, -, -, -⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hmonic hφ hroot hgen
  obtain ⟨hα', hξ', -, -, -⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hmonic' hφ' hroot' hgen'
  set f := φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))
  set f' := φ'.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))
  set M := (f * f').SplittingField
  let _ : ValuativeRel M := algebraicExtensionValuativeRel L M
  let _ : TopologicalSpace M := algebraicExtensionNormedFieldTopology L M
  have : IsNonarchimedeanLocalField M := finiteExtension_isNonarchimedeanLocalField L M
  have : ValuativeExtension L M := algebraicExtension_valuativeExtension L M
  have hsp : (f.map (algebraMap L M) * f'.map (algebraMap L M)).Splits :=
    Polynomial.map_mul (algebraMap L M) ▸ Polynomial.SplittingField.splits (f * f')
  have hmap (g : 𝒪[K][X]) :
      (g.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).map (algebraMap L M) =
        g.map ((algebraMap K M).comp (algebraMap 𝒪[K] K)) :=
    (Polynomial.map_map _ _ g).trans <| congrArg g.map <| RingHom.ext fun x ↦
      (IsScalarTower.algebraMap_apply K L M (algebraMap 𝒪[K] K x)).symm
  rw [newtonSlopes_ramificationPolynomial_eq_map_conjugateBreaks (M := M) hmonic hφ hroot hgen
      (hmap φ ▸ (splits_mul'.mp hsp).1.resolve_right ((hmonic'.map _).map _).ne_zero),
    newtonSlopes_ramificationPolynomial_eq_map_conjugateBreaks (M := M) hmonic' hφ' hroot' hgen'
      (hmap φ' ▸ (splits_mul'.mp hsp).2.resolve_right ((hmonic.map _).map _).ne_zero),
    conjugateBreaks_eq_of_irreducible (M := M)
      (isTotallyRamified_of_eisenstein_adjoin_eq_top hφ
        (isRoot_map_integerRing_of_isRoot hα hroot) hgen) hξ hξ']

/-- **Generator invariance of the ramification polygon.** Any two monic Eisenstein generators
`(φ, α)` and `(φ', α')` of a separable extension `L/K` have identical ramification polygon. -/
theorem newtonPolygon_ramificationPolynomial_eq {φ φ' : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    (hmonic' : φ'.Monic) (hφ' : φ'.IsEisensteinAt 𝓂[K]) {α' : L}
    (hroot' : (φ'.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α') (hgen' : K⟮α'⟯ = ⊤) :
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
    ((ramificationPolynomial φ α).isConvexSeq_newtonPolygon _) (hdom hmonic hφ hα0 hroot hgen rfl)
  let d' := FiniteSlopeData.ofIsConvexSeq
    ((ramificationPolynomial φ' α').isConvexSeq_newtonPolygon _)
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
