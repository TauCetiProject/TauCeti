/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Coleman.Basic
import TauCeti.RingTheory.PowerSeries.GaussNorm

/-!
# Coleman's transform with entire functional input

For entire series `B` and `F`, with `B(0) = 0` and `F(0) = 1`,
`PowerSeries.colemanDEntire B F` is the limit of the finite Coleman transforms of their
polynomial truncations. The two truncation orders tend to infinity independently.
The coefficientwise Cauchy estimate constructs the limit, and a common null coefficient
majorant upgrades convergence to every positive-radius Gauss norm. Thus the construction
does not depend on a diagonal choice of truncations.

The transform is entire, normalized, and uniquely characterized by coefficient convergence.
The cases `B = 0`, `B = X`, and `F = 1` are included. The zero constant term of `B` is essential:
otherwise padding finite ranks introduces extra factors from zero eigenvalues.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A3.
-/

public section

namespace PowerSeries

open Filter Finset
open scoped Topology Polynomial

variable {R : Type*} [NormedCommRing R]

/-- The coefficientwise limit of the finite Coleman transforms of the truncations of `B` and
`F`. Its convergence and entire-series interpretation hold when `B` and `F` are entire,
`coeff 0 B = 0`, and `coeff 0 F = 1`. -/
noncomputable def colemanDEntire (B F : R⟦X⟧) : R⟦X⟧ :=
  mk fun k ↦ limUnder atTop fun p : ℕ × ℕ ↦
    (Polynomial.colemanDBounded (trunc (p.2 + 1) B) (trunc (p.1 + 1) F) p.1 p.2).coeff k

/-- The defining coefficient formula for the entire Coleman transform. The limit is taken in
the coefficient ring, with the rank and functional truncation order independent. -/
theorem coeff_colemanDEntire (B F : R⟦X⟧) (k : ℕ) :
    coeff k (colemanDEntire B F) = limUnder atTop fun p : ℕ × ℕ ↦
      (Polynomial.colemanDBounded (trunc (p.2 + 1) B) (trunc (p.1 + 1) F) p.1 p.2).coeff k :=
  coeff_mk _ _

variable {B F G : R⟦X⟧}

section Entire

variable [CompleteSpace R] [NormOneClass R] [IsUltrametricDist R]

/-- The finite transforms converge coefficientwise to the entire Coleman transform. -/
theorem tendsto_coeff_colemanDBounded_trunc (hB : B.IsEntire) (hF : F.IsEntire)
    (hB₀ : coeff 0 B = 0) (hF₀ : coeff 0 F = 1) (k : ℕ) :
    Tendsto (fun p : ℕ × ℕ ↦
      (Polynomial.colemanDBounded (trunc (p.2 + 1) B) (trunc (p.1 + 1) F) p.1 p.2).coeff k)
      atTop (𝓝 (coeff k (colemanDEntire B F))) := by
  obtain ⟨ρ, hρ₀, hρ, _, hbound⟩ := hF.exists_newtonMajorant (by simp [hF₀])
  rw [coeff_colemanDEntire]
  exact (cauchySeq_coeff_colemanDBounded_trunc (fun i ↦ (hρ₀ i).le) hρ hbound hF₀
    (fun i ↦ hB.isRestricted _) hB₀ k).tendsto_limUnder

/-- A nonnegative antitone product majorant of `F` bounds the coefficients of the transform by
products of the Coleman majorants of `B`. -/
theorem norm_coeff_colemanDEntire_le {ρ : ℕ → ℝ} (hρ₀ : ∀ i, 0 ≤ ρ i)
    (hρ : Antitone ρ) (hbound : ∀ j, ‖coeff j F‖ ≤ ∏ i ∈ range j, ρ i)
    (hB : B.IsEntire) (hF : F.IsEntire) (hB₀ : coeff 0 B = 0) (hF₀ : coeff 0 F = 1)
    (k : ℕ) : ‖coeff k (colemanDEntire B F)‖ ≤ ∏ i ∈ range k, colemanMajorant B (ρ i) := by
  exact le_of_tendsto (tendsto_coeff_colemanDBounded_trunc hB hF hB₀ hF₀ k).norm
    (Eventually.of_forall fun p ↦ norm_coeff_colemanDBounded_trunc_le hρ₀ hρ hbound
      (fun i ↦ hB.isRestricted _) hB₀ p.1 p.2 (p.2 + 1) (p.1 + 1) k)

/-- Coleman's transform of normalized entire input along a zero-constant entire function is
entire over a complete ultrametric norm-one coefficient ring. -/
theorem isEntire_colemanDEntire (hB : B.IsEntire) (hF : F.IsEntire)
    (hB₀ : coeff 0 B = 0) (hF₀ : coeff 0 F = 1) : (colemanDEntire B F).IsEntire := by
  obtain ⟨ρ, hρ₀, hρ, hlim, hbound⟩ := hF.exists_newtonMajorant (by simp [hF₀])
  exact isEntire_of_norm_coeff_le_prod
    (tendsto_colemanMajorant (hB.isRestricted 1) zero_lt_one (fun i ↦ (hρ₀ i).le) hlim)
    (norm_coeff_colemanDEntire_le (fun i ↦ (hρ₀ i).le) hρ hbound hB hF hB₀ hF₀)

/-- The finite transforms converge in every positive-radius Gauss norm, with the two
truncation orders tending to infinity independently. -/
theorem tendsto_gaussNorm_colemanDBounded_trunc_sub_colemanDEntire
    (hB : B.IsEntire) (hF : F.IsEntire) (hB₀ : coeff 0 B = 0) (hF₀ : coeff 0 F = 1)
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun p : ℕ × ℕ ↦
      ((Polynomial.colemanDBounded (trunc (p.2 + 1) B) (trunc (p.1 + 1) F) p.1 p.2 : R⟦X⟧) -
        colemanDEntire B F).gaussNorm norm r) atTop (𝓝 0) := by
  obtain ⟨ρ, hρ₀, hρ, hlim, hbound⟩ := hF.exists_newtonMajorant (by simp [hF₀])
  let β : ℕ → ℝ := fun i ↦ colemanMajorant B (ρ i)
  have hβ₀ (i) : 0 ≤ β i := colemanMajorant_nonneg _ (hρ₀ i).le
  have hβ : Tendsto β atTop (𝓝 0) :=
    tendsto_colemanMajorant (hB.isRestricted 1) zero_lt_one (fun i ↦ (hρ₀ i).le) hlim
  -- The series with coefficients equal to the common product bounds is entire too.
  have hprod : (mk fun k ↦ (∏ i ∈ range k, β i : ℝ)).IsEntire :=
    isEntire_of_norm_coeff_le_prod hβ (fun k ↦ by
      rw [coeff_mk, Real.norm_eq_abs, abs_of_nonneg (prod_nonneg fun i _ ↦ hβ₀ i)])
  refine TauCeti.PowerSeries.tendsto_gaussNorm_zero_of_coeff_bound
    (b := fun k ↦ (∏ i ∈ range k, β i) * r ^ k) ?_ ?_ ?_
  · intro k
    simpa only [map_sub, Polynomial.coeff_coe, sub_self] using
      (tendsto_coeff_colemanDBounded_trunc hB hF hB₀ hF₀ k).sub_const
        (coeff k (colemanDEntire B F))
  · intro p k
    rw [map_sub, Polynomial.coeff_coe]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr.le _)
    have hsub (x y : R) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
      simpa only [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)
    exact (hsub _ _).trans (max_le
      (norm_coeff_colemanDBounded_trunc_le (fun i ↦ (hρ₀ i).le) hρ hbound
        (fun i ↦ hB.isRestricted _) hB₀ p.1 p.2 (p.2 + 1) (p.1 + 1) k)
      (norm_coeff_colemanDEntire_le (fun i ↦ (hρ₀ i).le) hρ hbound hB hF hB₀ hF₀ k))
  · simpa only [coeff_mk, Real.norm_eq_abs,
      abs_of_nonneg (prod_nonneg fun i _ ↦ hβ₀ i)] using
      (isRestricted_iff' r _).mp (hprod.isRestricted r)

end Entire

/-- Uniqueness of the Coleman transform from its defining coefficient limits. -/
theorem colemanDEntire_eq_of_tendsto_coeff
    (hG : ∀ k, Tendsto (fun p : ℕ × ℕ ↦
      (Polynomial.colemanDBounded (trunc (p.2 + 1) B) (trunc (p.1 + 1) F) p.1 p.2).coeff k)
      atTop (𝓝 (coeff k G))) : colemanDEntire B F = G := by
  ext k
  rw [coeff_colemanDEntire]
  exact (hG k).limUnder_eq

/-- The entire Coleman transform is normalized to have constant coefficient one. -/
@[simp]
theorem coeff_zero_colemanDEntire (hF₀ : coeff 0 F = 1) :
    coeff 0 (colemanDEntire B F) = 1 := by
  rw [coeff_colemanDEntire]
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  exact Eventually.of_forall fun p ↦
    (Polynomial.coeff_zero_colemanDBounded (by simp [coeff_trunc, hF₀]) _ p.1 p.2).symm

/-- The zero functional input gives the constant series one. -/
@[simp]
theorem colemanDEntire_zero_left (hF₀ : coeff 0 F = 1) :
    colemanDEntire 0 F = 1 := by
  apply colemanDEntire_eq_of_tendsto_coeff
  intro k
  apply tendsto_const_nhds.congr'
  exact Eventually.of_forall fun p ↦ by
    have hF₀' : (trunc (p.1 + 1) F).coeff 0 = 1 := by simp [coeff_trunc, hF₀]
    simp only [map_zero, Polynomial.colemanDBounded_zero_left hF₀', coeff_one,
      Polynomial.coeff_one]

/-- The transform of the constant series one is one, regardless of the truncation rank. -/
@[simp]
theorem colemanDEntire_one_right (hB₀ : coeff 0 B = 0) :
    colemanDEntire B 1 = 1 := by
  apply colemanDEntire_eq_of_tendsto_coeff
  intro k
  have hD (p : ℕ × ℕ) :
      Polynomial.colemanDBounded (trunc (p.2 + 1) B) (trunc (p.1 + 1) (1 : R⟦X⟧)) p.1 p.2 = 1 := by
    rw [trunc_one, Polynomial.colemanDBounded_one_right
      (Nat.lt_succ_iff.mp (natDegree_trunc_lt _ _))]
    simp [coeff_trunc, hB₀]
  simpa only [hD, ← Polynomial.coeff_coe, Polynomial.coe_one] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ × ℕ ↦ coeff k (1 : R⟦X⟧)) atTop (𝓝 _))

/-- Substituting the identity function in Coleman's transform returns the original series. -/
@[simp]
theorem colemanDEntire_X_left (hF₀ : coeff 0 F = 1) :
    colemanDEntire X F = F := by
  nontriviality R
  apply colemanDEntire_eq_of_tendsto_coeff
  intro k
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (k, 1)] with p hp
  have hX : trunc (p.2 + 1) (X : R⟦X⟧) = Polynomial.X :=
    trunc_X_of (by have := hp.2; omega)
  have hdeg : (Polynomial.X : R[X]).natDegree ≤ p.2 := by
    simpa using hp.2
  have hF₀' : (trunc (p.1 + 1) F).coeff 0 = 1 := by simp [coeff_trunc, hF₀]
  rw [hX, Polynomial.colemanDBounded_of_natDegree_le hdeg hF₀',
    Polynomial.natDegree_X,
    Polynomial.colemanDBounded_X_left (Nat.lt_succ_iff.mp (natDegree_trunc_lt _ _))]
  simp [coeff_trunc, Nat.lt_succ_of_le hp.1]

end PowerSeries
