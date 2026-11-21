/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Analysis.Normed.Algebra.GelfandRadius
public import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Reduced
public import TauCeti.RingTheory.Huber.Uniform
public import TauCeti.RingTheory.Localization.Reduced

import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Topology.Algebra.Algebra
import TauCeti.Algebra.Module.LocalizedModule.Lift
import TauCeti.Analysis.Normed.Algebra.MinpolyRemainder
import TauCeti.Analysis.Normed.Operator.Embedding
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basic
import TauCeti.FieldTheory.Minpoly.TorsionFree
import TauCeti.RingTheory.Huber.Normed
import TauCeti.RingTheory.Huber.StrictMorphism
import TauCeti.RingTheory.Localization.TensorProduct

/-!
# Nonarchimedean Banach function algebras and finite torsion-free extensions

A commutative Banach algebra `A` is a *Banach function algebra* (in the sense of
Bosch–Güntzer–Remmert, §3.8.3) when its norm is equivalent to its spectral / smoothing seminorm
`smoothingFun (normRingSeminorm A)` (equivalently Mathlib's `gelfandRadius`; see
`TauCeti.Analysis.Normed.Algebra.GelfandRadius`).

This file establishes **[BGR, §3.8.3, Theorem 7]** for finite torsion-free extensions over a
nontrivially normed field `K` of arbitrary characteristic. Let `B` be a Noetherian integrally
closed ultrametric Banach `K`-algebra domain admitting an isometric algebra map into an ultrametric
normed field `F`, and let `A` be an ultrametric Banach `K`-algebra that is finite and torsion-free
over `B` with continuous structure map `B → A`.
* Without weak stability of `F`, `[IsFractionRing B F]`, or reducedness of `A`, for every `a : A`
  we have `gelfandRadius a = spectralValue (minpoly B a)`.
* When `F` is a fraction field of `B` (`[IsFractionRing B F]`) and `A` is reduced, `F ⊗[B] A` is a
  finite reduced `F`-algebra and
  `smoothingFun (normRingSeminorm A) a = reducedSpectralAlgNorm F (F ⊗[B] A) (1 ⊗ₜ[B] a)`.
* When `F` is moreover weakly stable (`TauCeti.IsWeaklyStable F`), `A` is a Banach function
  algebra: there exists `C > 0` such that for all `a : A`,
  `smoothingFun (normRingSeminorm A) a ≤ ‖a‖ ≤ C * smoothingFun (normRingSeminorm A) a`,
  and `A` is uniform (`TauCeti.Huber.IsUniform A`).

## Main results

* `TauCeti.gelfandRadius_eq_spectralValue_minpoly`,
  `TauCeti.reducedSpectralAlgNorm_one_tmul_eq_spectralValue_minpoly`, and
  `TauCeti.smoothingFun_eq_reducedSpectralAlgNorm`: minimal-polynomial and base-change formulas in
  finite torsion-free extensions.
* `TauCeti.exists_pos_norm_le_mul_smoothingFun_of_isWeaklyStable`,
  `TauCeti.isUniform_of_isWeaklyStable`, and
  `AlgHom.exists_pos_norm_le_mul_smoothingFun_of_isWeaklyStable`: [BGR, §3.8.3, Theorem 7].

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §3.8.3 (Theorem 7).
-/

public section

open Filter Polynomial Topology
open scoped TensorProduct nonZeroDivisors

namespace TauCeti

/-- For a reduced finite torsion-free algebra `A` over an integrally closed normed commutative
ring `B` and a fraction field `F` of `B` extending the norm isometrically, `reducedSpectralAlgNorm`
of `1 ⊗ₜ a` in `F ⊗[B] A` equals `spectralValue (minpoly B a)`. -/
theorem reducedSpectralAlgNorm_one_tmul_eq_spectralValue_minpoly
    {B F A : Type*} [NormedCommRing B] [IsIntegrallyClosed B]
    [NormedField F] [IsUltrametricDist F] [Algebra B F] [IsFractionRing B F]
    (hBF : ∀ b : B, ‖algebraMap B F b‖ = ‖b‖)
    [CommRing A] [IsReduced A] [Algebra B A] [Module.Finite B A] [Module.IsTorsionFree B A]
    (a : A) :
    reducedSpectralAlgNorm F (F ⊗[B] A) ((1 : F) ⊗ₜ[B] a) = spectralValue (minpoly B a) := by
  let φ : A →ₐ[B] F ⊗[B] A := Algebra.TensorProduct.includeRight
  have hφ : Function.Injective φ := Algebra.TensorProduct.includeRight_injective_of_isFractionRing
  have hmin : minpoly F ((1 : F) ⊗ₜ[B] a) = (minpoly B a).map (algebraMap B F) :=
    TauCeti.minpoly.isIntegrallyClosed_eq_field_fractions_of_injective F φ hφ
      (Algebra.IsIntegral.isIntegral a)
  rw [reducedSpectralAlgNorm_def, hmin, (algebraMap B F).spectralValue_map_of_norm_eq hBF]

section Extension

variable (K : Type*) [NontriviallyNormedField K]
  {B F A : Type*} [NormedCommRing B] [IsDomain B] [IsUltrametricDist B] [CompleteSpace B]
  [NormedAlgebra K B] [IsNoetherianRing B] [IsIntegrallyClosed B]
  [NormedField F] [IsUltrametricDist F] [Algebra B F] [IsFractionRing B F]
  [NormedCommRing A] [IsUltrametricDist A] [CompleteSpace A] [NormedAlgebra K A]
  [Algebra B A] [IsScalarTower K B A] [Module.Finite B A] [Module.IsTorsionFree B A]

include K

omit [IsFractionRing B F] in
/-- **Minimal-polynomial formula for the Gelfand radius in a finite torsion-free extension.**
Over a nontrivially normed field `K`, let `B` be a Noetherian integrally closed ultrametric Banach
`K`-algebra domain admitting an isometric algebra map into an ultrametric normed field `F`, and let
`A` be an ultrametric Banach `K`-algebra that is finite and torsion-free over `B` with continuous
structure map `B → A`. Then for every `a : A`, `gelfandRadius a = spectralValue (minpoly B a)`.
Neither `[IsFractionRing B F]`, weak stability of `F`, nor reducedness of `A` is needed. -/
theorem gelfandRadius_eq_spectralValue_minpoly
    (hBF : ∀ b : B, ‖algebraMap B F b‖ = ‖b‖) (hBA : Continuous (algebraMap B A)) (a : A) :
    gelfandRadius a = spectralValue (minpoly B a) := by
  have ha_int : IsIntegral B a := Algebra.IsIntegral.isIntegral a
  rcases subsingleton_or_nontrivial A with _ | _
  · have hdvd1 : minpoly B a ∣ 1 :=
      TauCeti.minpoly.isIntegrallyClosed_dvd_of_isTorsionFree ha_int (Subsingleton.elim _ _)
    have hp1 : minpoly B a = 1 :=
      (minpoly.monic ha_int).natDegree_eq_zero.mp <| Nat.eq_zero_of_le_zero <|
        (Polynomial.natDegree_le_of_dvd hdvd1 one_ne_zero).trans_eq natDegree_one
    rw [hp1, Polynomial.spectralValue_one, Subsingleton.elim a 0, gelfandRadius_zero]
  set p := minpoly B a
  have hp_monic : p.Monic := minpoly.monic ha_int
  have hp_ne_one : p ≠ 1 := fun h1 ↦ by
    have h0 : aeval a p = 0 := minpoly.aeval B a
    rw [h1, map_one] at h0
    exact one_ne_zero h0
  refine le_antisymm ?_ ?_
  · -- Upper bound: `algebraMap B A` is continuous `K`-linear, so
    -- `gelfandRadius (algebraMap B A b) ≤ ‖b‖`.
    let gK : B →L[K] A := ⟨Algebra.linearMap B A, hBA⟩
    refine gelfandRadius_le_spectralValue_of_aeval_eq_zero (fun b ↦ ?_) hp_monic (minpoly.aeval B a)
    refine (gelfandRadius_le_of_norm_pow_le ‖gK‖ fun n ↦ ?_).trans (gelfandRadius_le_norm b)
    rw [← map_pow]
    exact gK.le_opNorm (b ^ n)
  · -- Lower bound: evaluate `X ^ n %ₘ p` at each root `x` of `p` in `AlgebraicClosure F`.
    obtain ⟨C, _, hcoeff⟩ := exists_pos_norm_coeff_modByMonic_le K hBA a
    rw [← (algebraMap B F).spectralValue_map_of_norm_eq hBF p]
    refine (hp_monic.map (algebraMap B F)).spectralValue_le_of_forall_aeval_eq_zero
      (gelfandRadius_nonneg a) fun x hxp ↦ ?_
    set f : AlgebraNorm F (AlgebraicClosure F) := spectralAlgNorm F (AlgebraicClosure F)
    rw [← spectralAlgNorm_def]
    refine le_gelfandRadius_of_bound (C := C * ∑ i : Fin p.natDegree, f (x ^ (i : ℕ))) fun n hn ↦ ?_
    let rn : B[X] := (X : B[X]) ^ n %ₘ p
    have hrnF_deg : (rn.map (algebraMap B F)).natDegree < p.natDegree :=
      natDegree_map_le.trans_lt (natDegree_modByMonic_lt (X ^ n) hp_monic hp_ne_one)
    have hx_pow : x ^ n = ∑ i : Fin p.natDegree, algebraMap B F (rn.coeff i) • x ^ (i : ℕ) := by
      have hdiv := congrArg (Polynomial.map (algebraMap B F))
        (modByMonic_add_div ((X : B[X]) ^ n) p)
      have haevalx : aeval x (rn.map (algebraMap B F)) = x ^ n := by
        have h := congrArg (aeval x) hdiv
        simpa only [rn, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
          Polynomial.map_X, map_add, map_mul, hxp, zero_mul, add_zero, map_pow, aeval_X] using h
      rw [← haevalx, aeval_eq_sum_range' hrnF_deg, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [coeff_map]
    calc
      f x ^ n = f (x ^ n) := (spectralAlgNorm_isPowMul x (Nat.pos_of_ne_zero hn)).symm
      _ = f (∑ i : Fin p.natDegree, algebraMap B F (rn.coeff i) • x ^ (i : ℕ)) := by rw [hx_pow]
      _ ≤ ∑ i : Fin p.natDegree, f (algebraMap B F (rn.coeff i) • x ^ (i : ℕ)) :=
        Finset.le_sum_of_subadditive f (map_zero f).le (map_add_le_add f) _ _
      _ = ∑ i : Fin p.natDegree, ‖rn.coeff i‖ * f (x ^ (i : ℕ)) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [map_smul_eq_mul, hBF]
      _ ≤ ∑ i : Fin p.natDegree, (C * ‖a ^ n‖) * f (x ^ (i : ℕ)) :=
        Finset.sum_le_sum fun i _ ↦
          mul_le_mul_of_nonneg_right
            (by simpa only [map_pow, aeval_X] using hcoeff ((X : B[X]) ^ n) (i : ℕ))
            (apply_nonneg f _)
      _ = (C * ∑ i : Fin p.natDegree, f (x ^ (i : ℕ))) * ‖a ^ n‖ := by
        rw [← Finset.mul_sum]
        ring

/-- **Smoothing seminorm via `reducedSpectralAlgNorm` on `F ⊗[B] A`.** Under the hypotheses of
`gelfandRadius_eq_spectralValue_minpoly` (over a nontrivially normed field `K`), when `F` is
additionally a fraction field of `B` (`[IsFractionRing B F]`) and `A` is reduced, `F ⊗[B] A` is a
finite reduced `F`-algebra and `smoothingFun (normRingSeminorm A) a` coincides with
`reducedSpectralAlgNorm F (F ⊗[B] A) (1 ⊗ₜ[B] a)` (no weak stability needed). -/
theorem smoothingFun_eq_reducedSpectralAlgNorm [IsReduced A]
    (hBF : ∀ b : B, ‖algebraMap B F b‖ = ‖b‖) (hBA : Continuous (algebraMap B A)) (a : A) :
    smoothingFun (normRingSeminorm A) a =
      reducedSpectralAlgNorm F (F ⊗[B] A) ((1 : F) ⊗ₜ[B] a) := by
  rw [smoothingFun_normRingSeminorm_eq_gelfandRadius,
    gelfandRadius_eq_spectralValue_minpoly K hBF hBA a,
    reducedSpectralAlgNorm_one_tmul_eq_spectralValue_minpoly hBF a]

/-- **Bosch–Güntzer–Remmert, §3.8.3, Theorem 7.** Over a nontrivially normed field `K`, let `B` be
a Noetherian integrally closed ultrametric Banach `K`-algebra domain whose fraction field `F`
(`[IsFractionRing B F]`) is isometric and weakly stable (`TauCeti.IsWeaklyStable F`), and let `A`
be a reduced ultrametric Banach `K`-algebra that is finite and torsion-free over `B` with continuous
structure map `B → A`. Then `A` is a Banach function algebra: there exists `C > 0` such that for
every `a : A`, `smoothingFun (normRingSeminorm A) a ≤ ‖a‖` and
`‖a‖ ≤ C * smoothingFun (normRingSeminorm A) a`. -/
theorem exists_pos_norm_le_mul_smoothingFun_of_isWeaklyStable [IsReduced A]
    (hBF : ∀ b : B, ‖algebraMap B F b‖ = ‖b‖) (hF : IsWeaklyStable F)
    (hBA : Continuous (algebraMap B A)) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : A,
      smoothingFun (normRingSeminorm A) a ≤ ‖a‖ ∧
        ‖a‖ ≤ C * smoothingFun (normRingSeminorm A) a := by
  rcases subsingleton_or_nontrivial A with _ | _
  · refine ⟨1, zero_lt_one, fun a ↦ ?_⟩
    simp [Subsingleton.elim a 0, smoothingFun_normRingSeminorm_eq_gelfandRadius]
  -- Embed `A` `B`-linearly into a finite free `B`-module `ι → B` by clearing denominators of the
  -- coordinates in an `F`-basis of `E := F ⊗[B] A`.
  let E := F ⊗[B] A
  let φ : A →ₐ[B] E := Algebra.TensorProduct.includeRight
  have hφ : Function.Injective φ := Algebra.TensorProduct.includeRight_injective_of_isFractionRing
  have : Nontrivial E := hφ.nontrivial
  let ι := Module.Free.ChooseBasisIndex F E
  let b : Module.Basis ι F E := Module.Free.chooseBasis F E
  have : Nonempty ι := b.index_nonempty
  obtain ⟨Ψ₀, d₀, hΨ₀_inj, hΨ₀_spec⟩ := Module.Finite.exists_injective_lift_finsupp_of_basis
    B⁰ (IsFractionRing.injective B F) b (f := φ.toLinearMap) hφ
  let Ψ : A →ₗ[B] (ι → B) := Finsupp.lcoeFun.comp Ψ₀
  have hΨ_inj : Function.Injective Ψ := DFunLike.coe_injective.comp hΨ₀_inj
  have hd₀_ne : (d₀ : B) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d₀.property
  have : 0 < ‖(d₀ : B)‖ := norm_pos_iff.mpr hd₀_ne
  have : Huber.IsTateRing B := Huber.IsTateRing.of_normedAlgebra K B
  have : ContinuousSMul B A := continuousSMul_of_algebraMap B A hBA
  have hΨ_strict : IsStrictMap Ψ := Ψ.isStrictMap_of_module_finite
  obtain ⟨C₁, hC₁, hΨ_bound⟩ :=
    (Ψ.restrictScalars K).exists_pos_norm_le_mul_norm_of_isStrictMap_of_injective hΨ_strict hΨ_inj
  obtain ⟨C₂, _, hC₂, _, hb_comp⟩ := hF.exists_basis_reducedSpectralAlgNorm_comparison b
  refine ⟨C₁ * ‖(d₀ : B)‖ * C₂, by positivity,
    fun a ↦ ⟨smoothingFun_le_self (normRingSeminorm A) a, ?_⟩⟩
  have hΨ_norm : ‖Ψ a‖ ≤ ‖(d₀ : B)‖ * b.norm (φ a) := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (b.norm_nonneg _))).mpr fun i ↦ ?_
    rw [← hBF (Ψ a i), show Ψ a i = Ψ₀ a i from rfl, hΨ₀_spec a i,
      AlgHom.toLinearMap_apply, norm_mul, hBF]
    exact mul_le_mul_of_nonneg_left (b.norm_repr_le_norm i) (norm_nonneg _)
  calc
    ‖a‖ ≤ C₁ * ‖Ψ a‖ := hΨ_bound a
    _ ≤ C₁ * (‖(d₀ : B)‖ * b.norm (φ a)) := mul_le_mul_of_nonneg_left hΨ_norm hC₁.le
    _ ≤ C₁ * (‖(d₀ : B)‖ * (C₂ * reducedSpectralAlgNorm F E (φ a))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hb_comp (φ a)).1 (norm_nonneg _)) hC₁.le
    _ = C₁ * ‖(d₀ : B)‖ * C₂ * smoothingFun (normRingSeminorm A) a := by
      rw [smoothingFun_eq_reducedSpectralAlgNorm K hBF hBA a]
      dsimp only [E, φ]
      rw [Algebra.TensorProduct.includeRight_apply]
      ring

/-- Under the hypotheses of `exists_pos_norm_le_mul_smoothingFun_of_isWeaklyStable`, `A` is a
uniform Huber ring (`TauCeti.Huber.IsUniform A`). -/
theorem isUniform_of_isWeaklyStable [IsReduced A]
    (hBF : ∀ b : B, ‖algebraMap B F b‖ = ‖b‖) (hF : IsWeaklyStable F)
    (hBA : Continuous (algebraMap B A)) :
    Huber.IsUniform A := by
  obtain ⟨C, _, hC⟩ := exists_pos_norm_le_mul_smoothingFun_of_isWeaklyStable K hBF hF hBA
  exact Huber.IsUniform.of_norm_le_mul_smoothingFun K ⟨C, fun a ↦ (hC a).2⟩

end Extension

end TauCeti

/-- `AlgHom` wrapper for `TauCeti.exists_pos_norm_le_mul_smoothingFun_of_isWeaklyStable` over a
nontrivially normed field `K`, taking a continuous finite `K`-algebra homomorphism `g : B →ₐ[K] A`
whose nonzero elements act without torsion on `A`. -/
theorem AlgHom.exists_pos_norm_le_mul_smoothingFun_of_isWeaklyStable
    {K B F A : Type*} [NontriviallyNormedField K]
    [NormedCommRing B] [IsDomain B] [IsUltrametricDist B] [CompleteSpace B]
    [NormedAlgebra K B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    [NormedField F] [IsUltrametricDist F] [Algebra B F] [IsFractionRing B F]
    [NormedCommRing A] [IsReduced A] [IsUltrametricDist A] [CompleteSpace A] [NormedAlgebra K A]
    (g : B →ₐ[K] A) (hg_cont : Continuous g) (hg_fin : g.Finite)
    (hg_tf : ∀ ⦃b : B⦄ ⦃a : A⦄, b ≠ 0 → g b * a = 0 → a = 0)
    (hBF : ∀ b : B, ‖algebraMap B F b‖ = ‖b‖) (hF : TauCeti.IsWeaklyStable F) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : A,
      smoothingFun (normRingSeminorm A) a ≤ ‖a‖ ∧
        ‖a‖ ≤ C * smoothingFun (normRingSeminorm A) a := by
  let _ : Algebra B A := g.toRingHom.toAlgebra
  have : IsScalarTower K B A := .of_algebraMap_eq fun c ↦ (g.commutes c).symm
  have : Module.Finite B A := hg_fin
  have : Module.IsTorsionFree B A := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun b a hba ↦ ?_
    by_cases hb : b = 0
    · exact Or.inl hb
    · exact Or.inr (hg_tf hb hba)
  exact TauCeti.exists_pos_norm_le_mul_smoothingFun_of_isWeaklyStable K hBF hF hg_cont
