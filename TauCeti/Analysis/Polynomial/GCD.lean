/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Subresultant.FirstNonzero
public import TauCeti.Analysis.Polynomial.ContinuityOfRoots
import Mathlib.Topology.Instances.Matrix

/-!
# Continuous monic gcds of polynomial families

The monic gcd of two polynomial families has continuous coefficients wherever the degrees of
both inputs and of their gcd are locally constant. At a strict gcd index it is the subresultant
polynomial divided by its nonzero principal coefficient. At a terminal index it is the monic
normalization of the input of smaller degree. The terminal cases include nonzero constants and
one input dividing the other.

Consequently, every common root at a parameter is approximated by common roots at nearby
parameters. This supplies the common-root persistence needed to make individual root matchings
agree for several polynomials; fixed input degrees alone do not ensure persistence.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
Chapters 4 and 5 (subresultant gcd recovery and continuity of roots).
-/

public section

open Polynomial Filter Topology

namespace TauCeti

variable {B R : Type*} [TopologicalSpace B]

section Subresultant

variable [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  {F G : B → R[X]} {x₀ : B} {m n : ℕ}

/-- A fixed-bound subresultant coefficient minor depends continuously on the input coefficients.
Only coefficients up to the respective formal bounds need be continuous. -/
@[fun_prop]
theorem continuousAt_subresultantCoeff
    (hF : ∀ i ≤ m, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hG : ∀ i ≤ n, ContinuousAt (fun x => (G x).coeff i) x₀) (j k : ℕ) :
    ContinuousAt (fun x => subresultantCoeff (F x) (G x) m n j k) x₀ := by
  simp only [subresultantCoeff_def]
  apply continuous_id.matrix_det.continuousAt.comp
  apply continuousAt_pi.2
  intro i
  apply continuousAt_pi.2
  intro l
  induction l using Fin.addCases with
  | left l =>
      simp only [subresultantCoeffMatrix_castAdd]
      split_ifs <;> first | exact hG _ (by omega) | exact continuousAt_const
  | right l =>
      simp only [subresultantCoeffMatrix_natAdd]
      split_ifs <;> first | exact hF _ (by omega) | exact continuousAt_const

/-- Every coefficient of a fixed-bound subresultant polynomial is continuous in the input
coefficients, including outside the strict-index range where the polynomial is zero. -/
@[fun_prop]
theorem continuousAt_coeff_subresultant
    (hF : ∀ i ≤ m, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hG : ∀ i ≤ n, ContinuousAt (fun x => (G x).coeff i) x₀) (j k : ℕ) :
    ContinuousAt (fun x => (subresultant (F x) (G x) m n j).coeff k) x₀ := by
  simp only [coeff_subresultant]
  split_ifs
  · exact continuousAt_subresultantCoeff hF hG j k
  · exact continuousAt_const

end Subresultant

section Field

variable [Field R] [DecidableEq R] [TopologicalSpace R] [IsTopologicalDivisionRing R]
  {F G : B → R[X]} {x₀ : B} {m n j : ℕ}

/-- Monic normalization has continuous coefficients on a family of fixed finite degree. -/
@[fun_prop]
theorem continuousAt_coeff_normalize
    (hF : ∀ i ≤ m, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).degree = m) (k : ℕ) :
    ContinuousAt (fun x => (normalize (F x)).coeff k) x₀ := by
  have hcoeff : ContinuousAt (fun x => (F x).coeff k) x₀ := by
    by_cases hk : k ≤ m
    · exact hF k hk
    · have hzero : ContinuousAt (fun _ : B => (0 : R)) x₀ := continuousAt_const
      apply hzero.congr
      filter_upwards [hdeg] with x hx
      exact (coeff_eq_zero_of_natDegree_lt (by
        rw [natDegree_eq_of_degree_eq_some hx]
        omega)).symm
  apply (((hF m le_rfl).inv₀ (coeff_ne_zero_of_eq_degree hdeg.self_of_nhds)).mul hcoeff).congr
  filter_upwards [hdeg] with x hx
  have hp : F x ≠ 0 := by
    intro h
    simp [h] at hx
  simp only [Pi.mul_apply, Pi.inv_apply, normalize_apply, coe_normUnit_of_ne_zero hp,
    coeff_mul_C]
  rw [leadingCoeff, natDegree_eq_of_degree_eq_some hx, mul_comm]

/-- The monic gcd has continuous coefficients when both input degrees and the gcd degree are
locally constant. The gcd may have the full degree of either input; neither input need be monic
or squarefree. Finite input degrees exclude zero polynomials. -/
@[fun_prop]
theorem continuousAt_coeff_normalize_gcd
    (hF : ∀ i ≤ m, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hG : ∀ i ≤ n, ContinuousAt (fun x => (G x).coeff i) x₀)
    (hdegF : ∀ᶠ x in 𝓝 x₀, (F x).degree = m)
    (hdegG : ∀ᶠ x in 𝓝 x₀, (G x).degree = n)
    (hgcd : ∀ᶠ x in 𝓝 x₀, (EuclideanDomain.gcd (F x) (G x)).natDegree = j) (k : ℕ) :
    ContinuousAt (fun x => (normalize (EuclideanDomain.gcd (F x) (G x))).coeff k) x₀ := by
  have hf₀ : F x₀ ≠ 0 := by
    intro h
    simpa [h] using hdegF.self_of_nhds
  have hg₀ : G x₀ ≠ 0 := by
    intro h
    simpa [h] using hdegG.self_of_nhds
  have hmn : j ≤ min m n := by
    have h₁ := natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_left (F x₀) (G x₀)) hf₀
    have h₂ := natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right (F x₀) (G x₀)) hg₀
    rw [hgcd.self_of_nhds, natDegree_eq_of_degree_eq_some hdegF.self_of_nhds] at h₁
    rw [hgcd.self_of_nhds, natDegree_eq_of_degree_eq_some hdegG.self_of_nhds] at h₂
    exact le_min h₁ h₂
  -- At a strict index the nonzero principal coefficient normalizes the subresultant.
  by_cases hj : j < min m n
  · have hc : psc (F x₀) (G x₀) m n j ≠ 0 := by
      rw [← hgcd.self_of_nhds]
      exact psc_natDegree_gcd_ne_zero hf₀
        (natDegree_eq_of_degree_eq_some hdegF.self_of_nhds)
        (natDegree_eq_of_degree_eq_some hdegG.self_of_nhds).le
    have hcont : ContinuousAt (fun x => psc (F x) (G x) m n j) x₀ := by
      simpa only [subresultantCoeff_self] using continuousAt_subresultantCoeff hF hG j j
    apply ((hcont.inv₀ hc).mul (continuousAt_coeff_subresultant hF hG j k)).congr
    filter_upwards [hdegF, hdegG, hgcd] with x hf hg hx
    have hm := natDegree_eq_of_degree_eq_some hf
    have hn := natDegree_eq_of_degree_eq_some hg
    have hs := subresultant_natDegree_gcd hm.le hn.le (by rwa [hx])
    rw [hx] at hs
    have hc' : psc (F x) (G x) m n j ≠ 0 := by
      rw [← hx]
      apply psc_natDegree_gcd_ne_zero _ hm hn.le
      intro h
      simp [h] at hf
    simp only [Pi.mul_apply, Pi.inv_apply]
    rw [hs, coeff_C_mul, ← mul_assoc, inv_mul_cancel₀ hc', one_mul]
  -- At the terminal index the gcd is associated to an input of that degree.
  · have heq : j = m ∨ j = n := by omega
    rcases heq with rfl | rfl
    · apply (continuousAt_coeff_normalize hF hdegF k).congr
      filter_upwards [hdegF, hgcd] with x hf hx
      have ha := associated_of_dvd_of_natDegree_le
        (EuclideanDomain.gcd_dvd_left (F x) (G x))
        (degree_ne_bot.mp (by rw [hf]; exact WithBot.coe_ne_bot))
        (by rw [natDegree_eq_of_degree_eq_some hf, hx])
      rw [normalize_eq_normalize_iff_associated.mpr ha]
    · apply (continuousAt_coeff_normalize hG hdegG k).congr
      filter_upwards [hdegG, hgcd] with x hg hx
      have ha := associated_of_dvd_of_natDegree_le
        (EuclideanDomain.gcd_dvd_right (F x) (G x))
        (degree_ne_bot.mp (by rw [hg]; exact WithBot.coe_ne_bot))
        (by rw [natDegree_eq_of_degree_eq_some hg, hx])
      rw [normalize_eq_normalize_iff_associated.mpr ha]

end Field

section CommonRoots

variable [NormedField R] [DecidableEq R] [IsAlgClosed R] [ProperSpace R]
  {F G : B → R[X]} {x₀ : B} {m n j : ℕ}

/-- Common roots persist under continuous variation with locally constant input and gcd degrees:
every central common root has a common root arbitrarily close in every sufficiently nearby
fiber. This does not assume constancy of the number of distinct roots of either input. -/
theorem eventually_exists_common_root_norm_sub_lt
    (hF : ∀ i ≤ m, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hG : ∀ i ≤ n, ContinuousAt (fun x => (G x).coeff i) x₀)
    (hdegF : ∀ᶠ x in 𝓝 x₀, (F x).degree = m)
    (hdegG : ∀ᶠ x in 𝓝 x₀, (G x).degree = n)
    (hgcd : ∀ᶠ x in 𝓝 x₀, (EuclideanDomain.gcd (F x) (G x)).natDegree = j)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∀ z, (F x₀).IsRoot z → (G x₀).IsRoot z →
      ∃ w, (F x).IsRoot w ∧ (G x).IsRoot w ∧ ‖w - z‖ < ε := by
  let H := fun x => normalize (EuclideanDomain.gcd (F x) (G x))
  have hne : ∀ᶠ x in 𝓝 x₀, EuclideanDomain.gcd (F x) (G x) ≠ 0 := by
    filter_upwards [hdegF] with x hx
    intro h
    have := (EuclideanDomain.gcd_eq_zero_iff.mp h).1
    simp [this] at hx
  have hmonic : ∀ᶠ x in 𝓝 x₀, (H x).Monic := hne.mono fun x hx => monic_normalize hx
  have hHdeg : ∀ᶠ x in 𝓝 x₀, (H x).degree = j := by
    filter_upwards [hne, hgcd] with x hx hj
    rw [degree_normalize, degree_eq_natDegree hx, hj]
  have hH : ∀ i ≤ j, ContinuousAt (fun x => (H x).coeff i) x₀ := fun i _ =>
    continuousAt_coeff_normalize_gcd hF hG hdegF hdegG hgcd i
  filter_upwards [eventually_exists_C_mul_prod_X_sub_C_norm_sub_lt hH hHdeg hε,
    hmonic, hne] with x ⟨a, b, ha, hb, hab⟩ hm hx z hzF hzG
  have hroot : (H x₀).IsRoot z := by
    rw [← mem_roots (monic_normalize hne.self_of_nhds).ne_zero, roots_normalize,
      mem_roots hne.self_of_nhds, isRoot_gcd_iff_isRoot_left_right]
    exact ⟨hzF, hzG⟩
  have ha' : H x₀ = ∏ i, (X - C (a i)) := by
    simpa only [hmonic.self_of_nhds.leadingCoeff, C_1, one_mul] using ha
  have hb' : H x = ∏ i, (X - C (b i)) := by
    simpa only [hm.leadingCoeff, C_1, one_mul] using hb
  obtain ⟨i, hi⟩ : ∃ i, z = a i := by
    simpa only [IsRoot.def, ha', eval_prod, eval_sub, eval_X, eval_C,
      Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero] using hroot
  have hw : (H x).IsRoot (b i) := by
    simp only [IsRoot.def, hb', eval_prod, eval_sub, eval_X, eval_C,
      Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero]
    exact ⟨i, rfl⟩
  have hcommon : (F x).IsRoot (b i) ∧ (G x).IsRoot (b i) := by
    rw [← isRoot_gcd_iff_isRoot_left_right, ← mem_roots hx, ← roots_normalize,
      mem_roots hm.ne_zero]
    exact hw
  exact ⟨b i, hcommon.1, hcommon.2, by rw [hi, norm_sub_rev]; exact hab i⟩

end CommonRoots

end TauCeti
