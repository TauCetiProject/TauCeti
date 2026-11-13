/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.KummerRatio
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Real
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.AlmostEverywhere
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
import Mathlib.Algebra.BigOperators.Finprod

/-!
# The product of local Kummer ratios

For an isogeny `φ : E₁ → E₂` over a fraction field `K`, its finite local Kummer ratio at `v` is
`[E₂(K_v) : φ E₁(K_v)] / #E₁(K_v)[φ]`. It is positive when the residue field is finite and the
degree is nonzero in the base Dedekind domain. With finite residue fields and degree nonzero
in `K`, the factors are one almost everywhere.

Over `ℚ`, the product including the real factor is a positive rational number,
`TauCeti.Isogeny.kummerRatioProduct`. This is the local product that enters the global Selmer
ratio formula, not the Kummer ratio on global rational points. No equality with orders of
global Selmer groups is asserted here.

The product is multiplicative under composition. This follows from the kernel–cokernel
index identity at each place; in particular it does not require choices of minimal equations,
differentials, or embeddings of separable closures. A finite set containing the nontrivial
factors computes the product exactly.

## References

* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
* E. F. Schaefer, *Class groups and Selmer groups*, J. Number Theory 56 (1996), §3.
-/

public noncomputable section

open IsDedekindDomain WeierstrassCurve ValuativeRel

namespace TauCeti.Isogeny

section Finite

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {W₁ W₂ W₃ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

/-- The Kummer ratio at a finite prime, using the canonical map to the completion. -/
def finiteKummerRatio (φ : Isogeny W₁.toAffine W₂.toAffine) (v : HeightOneSpectrum R) : ℚ :=
  (φ.map (algebraMap K (v.adicCompletion K))).kummerRatio

/-- The finite local ratio is the Kummer ratio after base change to the completion.
Any completion algebra compatible with the fraction-field tower gives the same map. -/
theorem finiteKummerRatio_def (φ : Isogeny W₁.toAffine W₂.toAffine)
    (v : HeightOneSpectrum R) [Algebra K (v.adicCompletion K)]
    [IsScalarTower R K (v.adicCompletion K)] :
    φ.finiteKummerRatio v = (φ.map (algebraMap K (v.adicCompletion K))).kummerRatio := by
  have h : algebraMap K (v.adicCompletion K) =
      @algebraMap K (v.adicCompletion K) _ _
        (HeightOneSpectrum.instAlgebraAdicCompletion R K v) := by
    apply IsFractionRing.ringHom_ext (A := R)
    intro x
    rw [← IsScalarTower.algebraMap_apply R K (v.adicCompletion K)]
    rfl
  rw [h]
  rfl

/-- Each finite local factor is positive when the residue field is finite and the degree
is nonzero in the base domain. -/
theorem finiteKummerRatio_pos (φ : Isogeny W₁.toAffine W₂.toAffine)
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] (hφ : (φ.degree : R) ≠ 0) :
    0 < φ.finiteKummerRatio v := by
  classical
  have := Hom.finiteIndex_range_pointMapHom_of_degree_ne_zero
    (A := R) (F := K) v
    (f := Hom.ofIsogeny (φ.map (algebraMap K (v.adicCompletion K)))) (by
      rwa [Hom.degree_ofIsogeny, degree_map])
  rw [finiteKummerRatio_def]
  exact kummerRatio_pos _

/-- The finite local factor is one at good reduction away from the degree. -/
theorem finiteKummerRatio_eq_one_of_isElliptic_integralModel
    (φ : Isogeny W₁.toAffine W₂.toAffine) (v : HeightOneSpectrum R)
    [Finite (R ⧸ v.asIdeal)] [Algebra K (v.adicCompletion K)]
    [IsScalarTower R K (v.adicCompletion K)]
    [hI₁ : IsIntegral 𝒪[v.adicCompletion K] (W₁.baseChange (v.adicCompletion K))]
    [hE₁ : (integralModel 𝒪[v.adicCompletion K]
      (W₁.baseChange (v.adicCompletion K))).IsElliptic]
    [hI₂ : IsIntegral 𝒪[v.adicCompletion K] (W₂.baseChange (v.adicCompletion K))]
    [hE₂ : (integralModel 𝒪[v.adicCompletion K]
      (W₂.baseChange (v.adicCompletion K))).IsElliptic]
    (hφ : (φ.degree : R) ∉ v.asIdeal) : φ.finiteKummerRatio v = 1 := by
  classical
  -- Base change is map along the algebra map, with the completion algebra quantified above.
  simp only [WeierstrassCurve.baseChange] at hI₁ hI₂ hE₁ hE₂
  have heq := Hom.index_range_eq_card_ker_of_isElliptic_integralModel
    (f := Hom.ofIsogeny (φ.map (algebraMap K (v.adicCompletion K)))) (by
      rwa [Hom.degree_ofIsogeny, degree_map])
  have := (Hom.ofIsogeny (φ.map (algebraMap K (v.adicCompletion K)))).finite_ker_pointMapHom
    (Hom.ofIsogeny_ne_zero _)
  rw [finiteKummerRatio_def, kummerRatio_def, heq,
    div_self (Nat.cast_ne_zero.mpr Nat.card_pos.ne')]

/-- With finite residue fields and degree nonzero in `K`, only finitely many finite primes
have nontrivial local Kummer factor. -/
theorem hasFiniteMulSupport_finiteKummerRatio [Ring.HasFiniteQuotients R]
    (φ : Isogeny W₁.toAffine W₂.toAffine) (hφ : (φ.degree : K) ≠ 0) :
    (φ.finiteKummerRatio (R := R)).HasFiniteMulSupport := by
  classical
  obtain ⟨T, -, hT, hdeg⟩ := exists_finset_isElliptic_integralModel_adicCompletion R W₁ hφ ∅
  apply Filter.eventually_cofinite.mp
  filter_upwards [T.eventually_cofinite_notMem,
    eventually_isElliptic_integralModel_adicCompletion R W₂] with v hv ⟨hI₂, hE₂⟩
  obtain ⟨hI₁, hE₁⟩ := hT v hv
  have : Finite (R ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  exact finiteKummerRatio_eq_one_of_isElliptic_integralModel φ v (hdeg v hv)

/-- Finite local Kummer ratios multiply under composition. -/
@[simp]
theorem finiteKummerRatio_comp (ψ : Isogeny W₂.toAffine W₃.toAffine)
    (φ : Isogeny W₁.toAffine W₂.toAffine) (v : HeightOneSpectrum R) :
    (ψ.comp φ).finiteKummerRatio v = ψ.finiteKummerRatio v * φ.finiteKummerRatio v := by
  simp only [finiteKummerRatio_def, comp_map, kummerRatio_comp]

/-- The identity isogeny has finite local Kummer ratio one. -/
@[simp]
theorem finiteKummerRatio_id (W : WeierstrassCurve K) [W.IsElliptic]
    (v : HeightOneSpectrum R) : (Isogeny.id W.toAffine).finiteKummerRatio v = 1 := by
  simp only [finiteKummerRatio_def, id_map, kummerRatio_id]

end Finite

section Rational

variable {W₁ W₂ W₃ : WeierstrassCurve ℚ} [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

/-- The real local Kummer ratio. -/
def realKummerRatio (φ : Isogeny W₁.toAffine W₂.toAffine) : ℚ :=
  (φ.map (algebraMap ℚ ℝ)).kummerRatio

/-- The real local ratio is the Kummer ratio after base change to `ℝ`. -/
theorem realKummerRatio_def (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.realKummerRatio = (φ.map (algebraMap ℚ ℝ)).kummerRatio :=
  (rfl)

/-- The real local factor is positive. -/
theorem realKummerRatio_pos (φ : Isogeny W₁.toAffine W₂.toAffine) :
    0 < φ.realKummerRatio := by
  classical
  have := (Hom.ofIsogeny (φ.map (algebraMap ℚ ℝ))).finiteIndex_range_pointMapHom_real
    (Hom.ofIsogeny_ne_zero _)
  rw [realKummerRatio_def]
  exact kummerRatio_pos _

/-- Real local Kummer ratios multiply under composition. -/
@[simp]
theorem realKummerRatio_comp (ψ : Isogeny W₂.toAffine W₃.toAffine)
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ψ.comp φ).realKummerRatio = ψ.realKummerRatio * φ.realKummerRatio := by
  simp only [realKummerRatio_def, comp_map, kummerRatio_comp]

/-- The identity isogeny has real local Kummer ratio one. -/
@[simp]
theorem realKummerRatio_id (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    (Isogeny.id W.toAffine).realKummerRatio = 1 := by
  simp only [realKummerRatio_def, id_map, kummerRatio_id]

/-- The product of local Kummer ratios, including the real place and every finite prime. -/
def kummerRatioProduct (φ : Isogeny W₁.toAffine W₂.toAffine) : ℚ :=
  φ.realKummerRatio * ∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v

/-- The defining product, including the real place. -/
theorem kummerRatioProduct_def (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.kummerRatioProduct =
      φ.realKummerRatio * ∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v :=
  (rfl)

/-- A finite exceptional set computes the product, independently of the extra primes included. -/
theorem kummerRatioProduct_eq_mul_prod (φ : Isogeny W₁.toAffine W₂.toAffine)
    (S : Finset (HeightOneSpectrum ℤ)) (hS : ∀ v ∉ S, φ.finiteKummerRatio v = 1) :
    φ.kummerRatioProduct = φ.realKummerRatio * ∏ v ∈ S, φ.finiteKummerRatio v := by
  rw [kummerRatioProduct_def, finprod_eq_prod_of_mulSupport_subset]
  exact fun v hv => by_contra fun h => hv (hS v h)

/-- The product of local Kummer ratios over `ℚ` is positive. -/
theorem kummerRatioProduct_pos (φ : Isogeny W₁.toAffine W₂.toAffine) :
    0 < φ.kummerRatioProduct := by
  classical
  rw [kummerRatioProduct_def]
  refine mul_pos φ.realKummerRatio_pos ?_
  rw [finprod_eq_prod _ (φ.hasFiniteMulSupport_finiteKummerRatio (R := ℤ)
    (Nat.cast_ne_zero.mpr φ.degree_pos.ne'))]
  exact Finset.prod_pos fun v _ => by
    have : Finite (ℤ ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    exact φ.finiteKummerRatio_pos v (Nat.cast_ne_zero.mpr φ.degree_pos.ne')

/-- The product of local Kummer ratios is multiplicative under composition. -/
@[simp]
theorem kummerRatioProduct_comp (ψ : Isogeny W₂.toAffine W₃.toAffine)
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ψ.comp φ).kummerRatioProduct = ψ.kummerRatioProduct * φ.kummerRatioProduct := by
  classical
  simp only [kummerRatioProduct_def, realKummerRatio_comp, finiteKummerRatio_comp]
  rw [finprod_mul_distrib
    (ψ.hasFiniteMulSupport_finiteKummerRatio (R := ℤ) (Nat.cast_ne_zero.mpr ψ.degree_pos.ne'))
    (φ.hasFiniteMulSupport_finiteKummerRatio (R := ℤ) (Nat.cast_ne_zero.mpr φ.degree_pos.ne'))]
  ring

/-- The identity isogeny has product of local Kummer ratios one. -/
@[simp]
theorem kummerRatioProduct_id (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    (Isogeny.id W.toAffine).kummerRatioProduct = 1 := by
  simp only [kummerRatioProduct_def, realKummerRatio_id, finiteKummerRatio_id,
    finprod_one, mul_one]

end Rational

end TauCeti.Isogeny
