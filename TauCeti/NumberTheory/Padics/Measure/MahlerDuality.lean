/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.AmiceTransform
public import TauCeti.NumberTheory.Padics.Basic
public import TauCeti.NumberTheory.Padics.MahlerBasis
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.LinearCombination

/-!
# Mahler duality for measures on `ℤ_p`

Let `R` be a complete ultrametric normed commutative ring with a contractive `ℤ_[p]`-algebra
structure. A measure `μ ∈ D(ℤ_p, R)` is a continuous `R`-linear functional on `C(ℤ_[p], R)`, and
its Amice transform `A_μ` has the moments `b_n = μ (x ↦ x choose n)` as coefficients. Mahler's
theorem identifies `C(ℤ_[p], R)` isometrically with the null sequences `C₀(ℕ, R)`, the
coordinate vectors corresponding to the Mahler basis. Hence, dually, measures correspond to bounded
moment sequences:

* every integral is the convergent series `μ f = ∑ n, a_n(f) * b_n` in the Mahler coefficients
  `a_n(f) = Δ^n f (0)` of `f` (`AbstractMeasure.hasSum_mahlerEquiv_mul_coeff_amiceTransform`);
* a bound `‖b_n‖ ≤ C` on the moments gives `‖μ f‖ ≤ C * ‖f‖`, and conversely
  (`AbstractMeasure.norm_apply_le_of_forall_norm_coeff_le`,
  `AbstractMeasure.norm_coeff_amiceTransform_le`).

When `R` admits a multiplicative pseudo-uniformiser (`TauCeti.NormedRing.IsTate R`), every
continuous linear functional is bounded, so the moments of every measure are bounded, and the
moments give an `R`-linear equivalence `AbstractMeasure.mahlerMomentsEquiv` between `D(ℤ_p, R)`
and the bounded sequences `ℓ^∞(ℕ, R)`. The operator norm of a measure is the supremum of the norms
of its moments, and a power series is an Amice transform exactly when its coefficients are bounded.
Over a nontrivially normed field, for instance a complete extension of `ℚ_p`, this is the
statement for Mathlib's operator norm (`AbstractMeasure.norm_toCLMEquiv_eq_iSup_coeff`). Over
`ℚ_p` the bounded measures therefore do not exhaust the power series: `∑ p⁻ⁿ Tⁿ` is not an Amice
transform. The integral case `R = ℤ_[p]`, where every power series is an Amice transform, is
Mathlib's `AbstractMeasure.amiceTransformEquiv`.

No norm is installed on the measure carrier; norms are taken on its image under Mathlib's
`AbstractMeasure.toCLMEquiv`. Over ring scalars this is the operator norm of the scope
`TauCeti.RingOpNorm`.

## Main definitions

* `AbstractMeasure.mahlerMomentsEquiv`: over a ring with a multiplicative pseudo-uniformiser, the
  linear equivalence between measures on `ℤ_p` and bounded moment sequences.

## Main results

* `AbstractMeasure.mahlerMomentsEquiv_apply`, `AbstractMeasure.mahlerMomentsEquiv_symm_apply`: the
  moments of a measure, and the measure with given bounded moments.
* `AbstractMeasure.hasSum_mahlerEquiv_mul_coeff_amiceTransform`: the Mahler expansion of an
  integral.
* `AbstractMeasure.bddAbove_norm_coeff_amiceTransform`: over Tate scalars, the moments of a measure
  are bounded.
* `AbstractMeasure.ringOpNorm_toCLMEquiv_eq_iSup_coeff`: over Tate scalars, the operator norm of a
  measure is the supremum of the norms of its moments.
* `AbstractMeasure.norm_toCLMEquiv_eq_iSup_coeff`: the same over a nontrivially normed field, for
  Mathlib's operator norm.
* `AbstractMeasure.norm_toCLMEquiv_le_iff_forall_norm_coeff_le`: hence over such a field a measure
  has norm at most `C` exactly when its moments do.
* `AbstractMeasure.mem_range_amiceTransform_iff`: a power series is the Amice transform of a measure
  exactly when its coefficients are bounded.

## References

* K. Mahler, *An interpolation series for continuous functions of a p-adic variable*,
  J. reine angew. Math. 199 (1958), 23–34.
* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.3 and §II.2.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.
-/

public section

open scoped AbstractMeasure ENNReal PowerSeries ZeroAtInfty
open PadicInt ZeroAtInftyContinuousMap

variable {p : ℕ} [Fact p.Prime]

namespace AbstractMeasure

section NormedCommRing

variable {R : Type*} [NormedCommRing R] [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R]
  [IsUltrametricDist R] [CompleteSpace R]

/-- **Mahler expansion of an integral.** The integral of `f` against `μ` is the sum over `n` of
the Mahler coefficients `Δ^n f (0)` of `f` times the moments `μ (x ↦ x choose n)`, the coefficients
of the Amice transform of `μ`. -/
theorem hasSum_mahlerEquiv_mul_coeff_amiceTransform (μ : D(ℤ_[p], R)) (f : C(ℤ_[p], R)) :
    HasSum (fun n ↦ mahlerEquiv R f n * μ.amiceTransform.coeff n) (μ f) := by
  have := (hasSum_mahler f).map (toCLMEquiv μ) (toCLMEquiv μ).continuous
  simpa [Function.comp_def, mahlerTerm_eq_smul, coeff_amiceTransform, mahlerEquiv_apply] using this

/-- A bound `C` on the norms of the moments of a measure is a bound for the measure:
`‖μ f‖ ≤ C * ‖f‖`. -/
theorem norm_apply_le_of_forall_norm_coeff_le (μ : D(ℤ_[p], R)) {C : ℝ}
    (hC : ∀ n, ‖μ.amiceTransform.coeff n‖ ≤ C) (f : C(ℤ_[p], R)) : ‖μ f‖ ≤ C * ‖f‖ := by
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  let b : lp (fun _ : ℕ ↦ R) ∞ :=
    ⟨fun n ↦ μ.amiceTransform.coeff n, memℓp_infty ⟨C, by rintro _ ⟨n, rfl⟩; exact hC n⟩⟩
  rw [← (hasSum_mahlerEquiv_mul_coeff_amiceTransform μ f).tsum_eq, ← (mahlerEquiv R).norm_map f]
  exact ((mahlerEquiv R f).norm_tsum_smul_le b).trans
    (mul_le_mul_of_nonneg_right (lp.norm_le_of_forall_le hC₀ hC) (norm_nonneg _))

omit [CompleteSpace R] in
/-- A bound `‖μ f‖ ≤ C * ‖f‖` on a measure bounds its moments by `C`, since the Mahler basis
functions have norm one. -/
theorem norm_coeff_amiceTransform_le [NormOneClass R] (μ : D(ℤ_[p], R)) {C : ℝ}
    (hμ : ∀ f, ‖μ f‖ ≤ C * ‖f‖) (n : ℕ) : ‖μ.amiceTransform.coeff n‖ ≤ C := by
  have := hμ (mahlerTerm (1 : R) n)
  rwa [norm_mahlerTerm, norm_one, mul_one, mahlerTerm_eq_smul, one_smul,
    ← coeff_amiceTransform] at this

end NormedCommRing

section IsTate

open scoped TauCeti.RingOpNorm

variable {R : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R] [Algebra ℤ_[p] R]
  [IsBoundedSMul ℤ_[p] R] [IsUltrametricDist R] [CompleteSpace R]

omit [CompleteSpace R] in
/-- Over a ring with a multiplicative pseudo-uniformiser, the moments of every measure on `ℤ_p`
are bounded. -/
theorem bddAbove_norm_coeff_amiceTransform (μ : D(ℤ_[p], R)) :
    BddAbove (Set.range fun n ↦ ‖μ.amiceTransform.coeff n‖) := by
  obtain ⟨C, -, hC⟩ :=
    TauCeti.NormedRing.IsTate.bound_of_continuous (toCLMEquiv μ) (toCLMEquiv μ).continuous
  exact ⟨C, by
    rintro _ ⟨n, rfl⟩
    exact norm_coeff_amiceTransform_le μ (fun f ↦ by simpa using hC f) n⟩

variable (p R) in
/-- **Mahler duality.** Over a ring with a multiplicative pseudo-uniformiser, a measure on `ℤ_p`
is determined by its moments `μ (x ↦ x choose n)`, the coefficients of its Amice transform, and
every bounded sequence is the moment sequence of a measure. The inverse sends a bounded sequence
`b` to the measure `f ↦ ∑ n, Δ^n f (0) * b n`. -/
noncomputable def mahlerMomentsEquiv : D(ℤ_[p], R) ≃ₗ[R] lp (fun _ : ℕ ↦ R) ∞ :=
  toCLMEquiv ≪≫ₗ
    ContinuousLinearEquiv.arrowCongrEquivₛₗ
      (mahlerLinearIsometryEquiv R R).toContinuousLinearEquiv (ContinuousLinearEquiv.refl R R) ≪≫ₗ
    (linearCombinationEquiv R R).symm.toLinearEquiv

/-- The moment sequence of a measure is the coefficient sequence of its Amice transform. -/
@[simp]
theorem mahlerMomentsEquiv_apply (μ : D(ℤ_[p], R)) (n : ℕ) :
    mahlerMomentsEquiv p R μ n = μ.amiceTransform.coeff n := by
  simp [mahlerMomentsEquiv, coeff_amiceTransform, mahlerTerm_eq_smul]

/-- The measure with a given bounded moment sequence has that sequence as the coefficients of its
Amice transform. -/
@[simp]
theorem amiceTransform_mahlerMomentsEquiv_symm (b : lp (fun _ : ℕ ↦ R) ∞) :
    ((mahlerMomentsEquiv p R).symm b).amiceTransform = PowerSeries.mk b := by
  ext n
  rw [PowerSeries.coeff_mk, ← mahlerMomentsEquiv_apply, LinearEquiv.apply_symm_apply]

/-- The measure with a bounded moment sequence `b` integrates `f` to `∑ n, Δ^n f (0) * b n`. -/
theorem mahlerMomentsEquiv_symm_apply (b : lp (fun _ : ℕ ↦ R) ∞) (f : C(ℤ_[p], R)) :
    (mahlerMomentsEquiv p R).symm b f = ∑' n, mahlerEquiv R f n * b n := by
  simpa using
    (hasSum_mahlerEquiv_mul_coeff_amiceTransform ((mahlerMomentsEquiv p R).symm b) f).tsum_eq.symm

/-- Over a ring with a multiplicative pseudo-uniformiser, the operator norm of a measure on `ℤ_p`
is the supremum of the norms of its moments. -/
theorem ringOpNorm_toCLMEquiv_eq_iSup_coeff (μ : D(ℤ_[p], R)) :
    ‖toCLMEquiv μ‖ = ⨆ n, ‖μ.amiceTransform.coeff n‖ := by
  have hb := bddAbove_norm_coeff_amiceTransform μ
  refine ContinuousLinearMap.ringOpNorm_eq_of_bounds (Real.iSup_nonneg fun _ ↦ norm_nonneg _)
    (fun f ↦ by simpa using norm_apply_le_of_forall_norm_coeff_le μ (le_ciSup hb ·) f)
    fun N _ hN ↦ ciSup_le (norm_coeff_amiceTransform_le μ fun f ↦ by simpa using hN f)

/-- Mahler duality is isometric: the operator norm of a measure is the supremum norm of its
moment sequence. -/
theorem ringOpNorm_toCLMEquiv_eq_norm_mahlerMomentsEquiv (μ : D(ℤ_[p], R)) :
    ‖toCLMEquiv μ‖ = ‖mahlerMomentsEquiv p R μ‖ := by
  simp [ringOpNorm_toCLMEquiv_eq_iSup_coeff, lp.norm_eq_ciSup]

/-- **The range of the Amice transform.** Over a ring with a multiplicative pseudo-uniformiser, a
power series is the Amice transform of a measure on `ℤ_p` exactly when its coefficients are
bounded. -/
theorem mem_range_amiceTransform_iff (F : R⟦X⟧) :
    F ∈ LinearMap.range (amiceTransform (p := p) (R := R)) ↔
      BddAbove (Set.range fun n ↦ ‖F.coeff n‖) := by
  refine ⟨?_, fun hF ↦ ⟨(mahlerMomentsEquiv p R).symm ⟨fun n ↦ F.coeff n, memℓp_infty hF⟩, ?_⟩⟩
  · rintro ⟨μ, rfl⟩
    exact bddAbove_norm_coeff_amiceTransform μ
  · ext n
    simp

end IsTate

/-- **Mahler duality for field coefficients.** Over a complete ultrametric nontrivially normed
field with a contractive `ℤ_[p]`-algebra structure, such as a complete extension of `ℚ_p`, the
operator norm of a measure on `ℤ_p` is the supremum of the norms of the coefficients of its Amice
transform. -/
theorem norm_toCLMEquiv_eq_iSup_coeff {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
    [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K] (μ : D(ℤ_[p], K)) :
    ‖toCLMEquiv μ‖ = ⨆ n, ‖μ.amiceTransform.coeff n‖ :=
  (ContinuousLinearMap.ringOpNorm_eq_opNorm _).symm.trans
    (ringOpNorm_toCLMEquiv_eq_iSup_coeff μ)

/-- Over a complete ultrametric nontrivially normed field with a contractive `ℤ_[p]`-algebra
structure, a measure on `ℤ_p` has operator norm at most `C` exactly when every coefficient of its
Amice transform has norm at most `C`. -/
theorem norm_toCLMEquiv_le_iff_forall_norm_coeff_le {K : Type*} [NontriviallyNormedField K]
    [Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]
    (μ : D(ℤ_[p], K)) {C : ℝ} :
    ‖toCLMEquiv μ‖ ≤ C ↔ ∀ n, ‖μ.amiceTransform.coeff n‖ ≤ C := by
  rw [norm_toCLMEquiv_eq_iSup_coeff, ciSup_le_iff (bddAbove_norm_coeff_amiceTransform μ)]

/-- The power series `∑ p⁻ⁿ Tⁿ` over `ℚ_p` is not the Amice transform of a measure: its
coefficients `p⁻ⁿ` have norms `pⁿ`, which are unbounded. -/
example :
    PowerSeries.mk (fun n ↦ (p : ℚ_[p])⁻¹ ^ n) ∉
      LinearMap.range (amiceTransform (p := p) (R := ℚ_[p])) := by
  rw [mem_range_amiceTransform_iff]
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  refine hn.not_ge (hC ⟨n, ?_⟩)
  simp

end AbstractMeasure
