/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.RingTheory.ClassGroup.Basic
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.PartialZeta
public import TauCeti.NumberTheory.LFunctions.Theta.Mellin.Pair
public import TauCeti.NumberTheory.LFunctions.Theta.Surface.Cone
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.IdealLattice
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Count.TrivialModulus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Real
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.NumberTheory.LFunctions.DedekindZeta.UnitQuotient
import TauCeti.NumberTheory.LFunctions.Theta.GammaIntegral
import TauCeti.NumberTheory.LFunctions.Theta.UnitCone
import TauCeti.NumberTheory.NumberField.Global.RayClass.Integral

/-!
# The Mellin integral of an ideal-lattice theta function

Let `I` be an invertible fractional ideal of a number field `K`, and let `𝔎` be the ideal class of
`I⁻¹` in `ClassGroup (𝓞 K)`. Over any unit fundamental domain `D` (`IsUnitFundamentalDomain K D`),
Hecke's proof of the analytic continuation and functional equation of a partial zeta function
evaluates the Mellin transform at `s / 2` of the radial theta kernel
`mellinKernel D (idealLattice K I) · - mellinConstant K` on `Re s > 1` (Neukirch, Chapter VII,
(5.3)–(5.5)). This file establishes that identity in three steps:

1. **Fundamental-cone and ideal-class series** (`hasSum_norm_cpow_fundamentalCone`,
   `LSeries_rayClassCoeff_one_eq_tsum_mk0`): scaling `I` by the positive integer norm
   `n = N((den I))` clears denominators by a rational integer, which preserves Mathlib's
   `NumberField.mixedEmbedding.fundamentalCone K` and extends `hasSum_norm_cpow_idealSet` from
   integral ideals to invertible fractional ideals. Under `oneEquivClassGroup`, the sum over
   nonzero integral ideals in a given ideal class matches the `Modulus.one K` ray-class `LSeries`.
2. **Unfolding the lattice sum over `unitCone D`** (`summable_integral_unitCone`,
   `integrableOn_archNorm_cpow_mul_latticeTheta_sub_one`,
   `integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one`): nonzero points of
   `idealLattice K I` decompose uniquely as `(a, [u])` with `a` in `fundamentalCone K` and
   `[u] ∈ (𝓞 K)ˣ ⧸ torsion K`. Moving `u⁻¹` to the archimedean parameter via
   `archGaussian_unit_smul` tiles the open positive orthant by the pairwise disjoint measurable
   translates `unitScale u ⁻¹' unitCone D`, collapsing each unit orbit modulo torsion to a single
   full gamma integral `integral_archGaussian_mul_archNorm_cpow`.
3. **Covolume and complex-place normalization**
   (`hasMellin_mellinKernel_idealLattice_sub_mellinConstant`): combining the cone integral with
   `covolume_idealLattice` (`V_I = N(I) · 2 ^ (-r₂) · √|d_K|`) and
   `2 · 2 ^ (-s) · Γ_ℝ(2 s) = Γ_ℂ(s)` cancels `torsionOrder K`, `N(I) ^ s`, and the factors of `2`
   at the complex places, identifying the Mellin transform at `s / 2` with
   `|d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ∑_{[𝔟] = [I]⁻¹} N(𝔟) ^ (-s)`.

## Main results

* `TauCeti.LFunctions.hasSum_norm_cpow_fundamentalCone`: the sum of `|N(x)| ^ (-s)` over the points
  of `idealLattice K I` in `fundamentalCone K` on `Re s > 1`.
* `TauCeti.LFunctions.LSeries_rayClassCoeff_one_eq_tsum_mk0`: the `Modulus.one K` ray-class
  `LSeries` of a class `c` as the sum of `N(𝔟) ^ (-s)` over integral ideals in the corresponding
  `ClassGroup (𝓞 K)` class.
* `TauCeti.LFunctions.summable_integral_unitCone`: absolute summability of the lattice-point gamma
  integrals over `unitCone D` for `σ > 1`.
* `TauCeti.LFunctions.integrableOn_archNorm_cpow_mul_latticeTheta_sub_one`,
  `TauCeti.LFunctions.integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one`: integrability and
  evaluation of the cone integral of `N(y) ^ (s / 2) * (θ_{σ(I)}(y) - 1)` on `Re s > 1`.
* `TauCeti.LFunctions.hasMellin_mellinKernel_idealLattice_sub_mellinConstant`: Neukirch VII (5.5) as
  a `HasMellin` identity on `Re s > 1` for every unit fundamental domain `D`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.3)–(5.5).
* `NumberField.mixedEmbedding.fundamentalCone`
  (`Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone`, X. Roblot).
-/

public section

noncomputable section

open Complex Filter MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone NumberField.Units Set TauCeti.GlobalNumberFields
  TauCeti.NumberField.mixedEmbedding TauCeti.NumberField.Units
open scoped ENNReal Pointwise nonZeroDivisors

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### Fundamental-cone and ideal-class series -/

/-- Every invertible fractional ideal `I` of `K` becomes a nonzero integral ideal `J` after
multiplication by a positive natural number `n`, namely the absolute norm of the ideal generated by
`I.1.den`. Using a rational integer rather than an arbitrary algebraic integer ensures that the
induced scaling `x ↦ (n : ℝ) • x` on `mixedSpace K` preserves `fundamentalCone K`. -/
private theorem exists_nat_pos_spanSingleton_mul_eq_coeIdeal
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ (n : ℕ) (J : (Ideal (𝓞 K))⁰), 0 < n ∧
      ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (n : K) * (I : FractionalIdeal (𝓞 K)⁰ K) := by
  let d : 𝓞 K := I.1.den
  have hd0 : d ≠ 0 := nonZeroDivisors.coe_ne_zero I.1.den
  have hspan : Ideal.span {d} ≠ (⊥ : Ideal (𝓞 K)) := Ideal.span_singleton_eq_bot.not.mpr hd0
  let n : ℕ := Ideal.absNorm (Ideal.span {d})
  have hn0 : n ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hspan
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp (Ideal.absNorm_mem (Ideal.span {d}))
  let J₀ : Ideal (𝓞 K) := Ideal.span {k} * I.1.num
  have hJ₀_eq : (J₀ : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (n : K) * (I : FractionalIdeal (𝓞 K)⁰ K) := by
    calc (J₀ : FractionalIdeal (𝓞 K)⁰ K)
        = (Ideal.span {k} : FractionalIdeal (𝓞 K)⁰ K) *
            (I.1.num : FractionalIdeal (𝓞 K)⁰ K) := FractionalIdeal.coeIdeal_mul _ _
      _ = FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K k) *
            (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K d) * I.1) := by
          rw [FractionalIdeal.coeIdeal_span_singleton, ← I.1.den_mul_self_eq_num']
      _ = (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K d) *
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K k)) * I.1 := by ring
      _ = FractionalIdeal.spanSingleton (𝓞 K)⁰ (n : K) * I.1 := by
          rw [← map_mul, ← map_mul, ← hk, map_natCast]
  have hJ₀_ne : J₀ ≠ ⊥ := by
    rw [ne_eq, ← FractionalIdeal.coeIdeal_eq_zero (K := K), hJ₀_eq]
    exact mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Nat.cast_ne_zero.mpr hn0))
      I.ne_zero
  exact ⟨n, ⟨J₀, mem_nonZeroDivisors_iff_ne_zero.mpr hJ₀_ne⟩, Nat.pos_of_ne_zero hn0, hJ₀_eq⟩

/-- If `J = (n) * I` with `0 < n`, then `J` and `I` have the same ideal class in `ClassGroup (𝓞 K)`,
and `N(J) = n ^ [K : ℚ] * N(I)`. -/
private theorem mk0_and_absNorm_of_spanSingleton_mul {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {n : ℕ} {J : (Ideal (𝓞 K))⁰} (hn : 0 < n)
    (hJ : ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (n : K) * (I : FractionalIdeal (𝓞 K)⁰ K)) :
    ClassGroup.mk0 J = ClassGroup.mk K I ∧
      (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) =
        (n : ℝ) ^ Module.finrank ℚ K *
          (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hunit : FractionalIdeal.mk0 K J = toPrincipalIdeal (𝓞 K) K (Units.mk0 (n : K) hnK) * I :=
    Units.ext (by simpa [coe_toPrincipalIdeal] using hJ)
  have hprin : ClassGroup.mk K (toPrincipalIdeal (𝓞 K) K (Units.mk0 (n : K) hnK)) = 1 :=
    ClassGroup.mk_eq_one_iff.mpr
      ⟨(n : K), by simp [coe_toPrincipalIdeal, FractionalIdeal.coeToSubmodule_spanSingleton]⟩
  refine ⟨?_, ?_⟩
  · rw [← ClassGroup.mk_mk0 K J, hunit, map_mul, hprin, one_mul]
  · have hnorm : (Ideal.absNorm (J : Ideal (𝓞 K)) : ℚ) =
        (n : ℚ) ^ Module.finrank ℚ K *
          FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) := by
      have h := congrArg FractionalIdeal.absNorm hJ
      rw [FractionalIdeal.coeIdeal_absNorm, map_mul, FractionalIdeal.absNorm_span_singleton,
        show (n : K) = algebraMap ℚ K (n : ℚ) by simp, Algebra.norm_algebraMap,
        abs_of_nonneg (pow_nonneg (Nat.cast_nonneg n) _)] at h
      exact h
    exact_mod_cast hnorm

/-- Scaling by `n > 0` identifies the points of `idealLattice K I` in `fundamentalCone K` with
`idealSet K J` when `J = (n) * I`. -/
private def coneLatticeEquivIdealSet {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {n : ℕ}
    {J : (Ideal (𝓞 K))⁰} (hn : 0 < n)
    (hJ : ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (n : K) * (I : FractionalIdeal (𝓞 K)⁰ K)) :
    {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K} ≃ idealSet K J := by
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hsmul (z : mixedSpace K) : (n : ℝ) • z = (n : mixedSpace K) * z := by
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  have hI_eq : (I : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (n : K)⁻¹ *
        ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hJ, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hnK, map_one, one_mul]
  refine
    { toFun := fun x ↦ ⟨(n : ℝ) • (x.1 : mixedSpace K), ?_, ?_⟩
      invFun := fun y ↦ ⟨⟨(n : ℝ)⁻¹ • (y : mixedSpace K), ?_⟩,
        (fundamentalCone.smul_mem_iff_mem (inv_ne_zero hnR)).mpr y.2.1⟩
      left_inv := fun x ↦ Subtype.ext (Subtype.ext (inv_smul_smul₀ hnR _))
      right_inv := fun y ↦ Subtype.ext (smul_inv_smul₀ hnR _) }
  · exact (fundamentalCone.smul_mem_iff_mem hnR).mpr x.2
  · obtain ⟨a, ha, ha_eq⟩ := (mem_idealLattice K I).mp x.1.2
    refine (mem_idealLattice K (FractionalIdeal.mk0 K J)).mpr ⟨(n : K) * a, ?_, ?_⟩
    · change (n : K) * a ∈ ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      rw [hJ]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ (n : K)) ha
    · rw [map_mul, map_natCast, ha_eq, ← hsmul]
  · obtain ⟨b, hb, hb_eq⟩ := (mem_idealLattice K (FractionalIdeal.mk0 K J)).mp y.2.2
    refine (mem_idealLattice K I).mpr ⟨(n : K)⁻¹ * b, ?_, ?_⟩
    · rw [SetLike.mem_coe, hI_eq]
      exact FractionalIdeal.mul_mem_mul
        (FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ (n : K)⁻¹) hb
    · have hmul : (n : ℝ) • mixedEmbedding K ((n : K)⁻¹ * b) = (y : mixedSpace K) := by
        calc (n : ℝ) • mixedEmbedding K ((n : K)⁻¹ * b)
            = (n : mixedSpace K) * mixedEmbedding K ((n : K)⁻¹ * b) := hsmul _
          _ = mixedEmbedding K ((n : K) * ((n : K)⁻¹ * b)) := by
              rw [map_mul (mixedEmbedding K) (n : K), map_natCast]
          _ = mixedEmbedding K b := by rw [← mul_assoc, mul_inv_cancel₀ hnK, one_mul]
          _ = (y : mixedSpace K) := hb_eq
      rw [← hmul, inv_smul_smul₀ hnR]

/-- If `J` is a nonzero integral ideal in the class `𝔎⁻¹`, then a nonzero integral ideal `𝔟` lies
in `𝔎` if and only if `𝔟 * J` is principal. -/
private theorem mk0_eq_iff_isPrincipal {𝔎 : ClassGroup (𝓞 K)} {J : (Ideal (𝓞 K))⁰}
    (hJ : ClassGroup.mk0 J = 𝔎⁻¹) (𝔟 : (Ideal (𝓞 K))⁰) :
    ClassGroup.mk0 𝔟 = 𝔎 ↔
      Submodule.IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K))) := by
  have hJ' : 𝔎 = (ClassGroup.mk0 J)⁻¹ := by rw [hJ, inv_inv]
  rw [hJ', eq_inv_iff_mul_eq_one, ← map_mul, ClassGroup.mk0_eq_one_iff (𝔟 * J).2,
    Submonoid.coe_mul]

/-- **The sum over the points of `idealLattice K I` in the fundamental cone**, extending
`hasSum_norm_cpow_idealSet` from integral ideals to invertible fractional ideals: for `Re s > 1`,
`∑_{x ∈ σ(I) ∩ cone} |N(x)| ^ (-s) = w · N(I) ^ (-s) · ∑_{[𝔟] = [I]⁻¹} N(𝔟) ^ (-s)`. -/
theorem hasSum_norm_cpow_fundamentalCone (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    HasSum
      (fun x : {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K} ↦
        (mixedEmbedding.norm (x.1 : mixedSpace K) : ℂ) ^ (-s))
      ((torsionOrder K : ℂ) * ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s) *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by
  obtain ⟨n, J, hn, hJ⟩ := exists_nat_pos_spanSingleton_mul_eq_coeIdeal I
  obtain ⟨hJ_mk, hJ_norm⟩ := mk0_and_absNorm_of_spanSingleton_mul hn hJ
  have hJ_inv : ClassGroup.mk0 J = ((ClassGroup.mk K I)⁻¹)⁻¹ := by rw [inv_inv, hJ_mk]
  have hn_pow_pos : (0 : ℝ) < (n : ℝ) ^ Module.finrank ℚ K := by positivity
  have hn_cpow_ne : (((n : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    exact fun h ↦ (ofReal_ne_zero.mpr hn_pow_pos.ne') h.1
  have hJ_cpow : (Ideal.absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s) =
      (((n : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s) *
        ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s) := by
    have hcast : (Ideal.absNorm (J : Ideal (𝓞 K)) : ℂ) =
        (((n : ℝ) ^ Module.finrank ℚ K * (FractionalIdeal.absNorm I.1 : ℝ) : ℝ) : ℂ) := by
      exact_mod_cast hJ_norm
    rw [hcast, ofReal_mul, TauCeti.ofReal_mul_cpow hn_pow_pos.le, ofReal_ratCast]
  have htsum :
      (∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ //
          Submodule.IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)))},
        (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) =
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
        (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) :=
    (Equiv.subtypeEquivRight fun 𝔟 ↦ (mk0_eq_iff_isPrincipal hJ_inv 𝔟).symm).tsum_eq
      (fun 𝔟 ↦ (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-s))
  have hsumJ := (coneLatticeEquivIdealSet hn hJ).hasSum_iff.mpr (hasSum_norm_cpow_idealSet J hs)
  have hterm (x : {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K}) :
      ((mixedEmbedding.norm ((coneLatticeEquivIdealSet hn hJ x : idealSet K J) :
          mixedSpace K) : ℝ) : ℂ) ^ (-s) =
        (((n : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s) *
          (mixedEmbedding.norm (x.1 : mixedSpace K) : ℂ) ^ (-s) := by
    change ((mixedEmbedding.norm ((n : ℝ) • (x.1 : mixedSpace K)) : ℝ) : ℂ) ^ (-s) = _
    rw [mixedEmbedding.norm_smul, abs_of_nonneg (Nat.cast_nonneg n), ofReal_mul,
      TauCeti.ofReal_mul_cpow hn_pow_pos.le]
  have hscaled := (hsumJ.congr_fun fun x ↦ (hterm x).symm).mul_left
    ((((n : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s))⁻¹
  have hsum_eq :
      ((((n : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s))⁻¹ *
        ((torsionOrder K : ℂ) * (Ideal.absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s) *
          ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ //
              Submodule.IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)))},
            (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) =
      (torsionOrder K : ℂ) * ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s) *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
    rw [hJ_cpow, htsum]
    calc ((((n : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s))⁻¹ *
          ((torsionOrder K : ℂ) * ((((n : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s) *
            ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s)) *
            ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
              (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s))
        = ((((n : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s) *
            ((((n : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s))⁻¹) *
          ((torsionOrder K : ℂ) * ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s) *
            ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
              (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hn_cpow_ne, one_mul]
  rw [← hsum_eq]
  exact hscaled.congr_fun fun x ↦ (inv_mul_cancel_left₀ hn_cpow_ne _).symm

/-- **The `Modulus.one K` ray-class `LSeries` as a sum over an ideal class.** Under
`oneEquivClassGroup`, for `Re s > 1`, the Dirichlet series of a class `c` of the trivial modulus is
the sum of `N(𝔟) ^ (-s)` over the nonzero integral ideals `𝔟` with `ClassGroup.mk0 𝔟 = 𝔎`. -/
theorem LSeries_rayClassCoeff_one_eq_tsum_mk0 {c : RayClassGroup (Modulus.one K)}
    {𝔎 : ClassGroup (𝓞 K)} (hc : oneEquivClassGroup c = 𝔎) {s : ℂ} (hs : 1 < s.re) :
    LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s =
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = 𝔎},
        (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  obtain ⟨J, hJ_mk⟩ := ClassGroup.mk0_surjective 𝔎⁻¹
  have hJ_ray : idealClass (Modulus.one K) (integralIdealsPrimeToOneEquiv.symm J) = c⁻¹ := by
    apply oneEquivClassGroup.injective
    rw [map_inv, hc, idealClass_apply, oneEquivClassGroup_rayClassMk]
    have hunit : ((NumberFieldArithmetic.integralIdealsAwayHom K (Modulus.one K).support
          (integralIdealsPrimeToOneEquiv.symm J) : idealsPrimeTo (Modulus.one K)) :
          (FractionalIdeal (𝓞 K)⁰ K)ˣ) = FractionalIdeal.mk0 K J :=
      Units.ext (by simp [NumberFieldArithmetic.coe_integralIdealsAwayHom])
    rw [hunit, ClassGroup.mk_mk0, hJ_mk]
  rw [LSeries_rayClassCoeff_one_eq_tsum J hJ_ray hs]
  exact (Equiv.subtypeEquivRight fun 𝔟 ↦ (mk0_eq_iff_isPrincipal hJ_mk 𝔟).symm).tsum_eq
    (fun 𝔟 ↦ (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-s))

/-! ### Unfolding the lattice sum over the unit cone -/

private theorem norm_ne_zero_of_idealLattice_ne_zero {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {x : idealLattice K I} (hx : x ≠ 0) :
    mixedEmbedding.norm (x : mixedSpace K) ≠ 0 := by
  obtain ⟨a, -, ha⟩ := (mem_idealLattice K I).mp x.2
  exact (mixedEmbedding.norm_eq_zero_iff' ⟨a, ha⟩).not.mpr fun h ↦ hx (Submodule.coe_eq_zero.mp h)

/-- Every nonzero point `x` of `idealLattice K I` decomposes uniquely as `u⁻¹ • a` with `a` in
`fundamentalCone K` and `[u] ∈ (𝓞 K)ˣ ⧸ torsion K`. Using `u⁻¹` matches the parameter substitution
`archGaussian y (u⁻¹ • a) = archGaussian (unitScale u⁻¹ y) a`. -/
private def orbitEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    {a : idealLattice K I // (a : mixedSpace K) ∈ fundamentalCone K} × ((𝓞 K)ˣ ⧸ torsion K) ≃
      {x : idealLattice K I // x ≠ 0} := by
  refine Equiv.ofBijective
    (fun p ↦ ⟨(Quotient.out p.2)⁻¹.unitSMulIdealLatticeEquiv I p.1.1, ?_⟩) ⟨?_, ?_⟩
  · intro h0
    have hn : mixedEmbedding.norm
        (((Quotient.out p.2)⁻¹.unitSMulIdealLatticeEquiv I p.1.1 : idealLattice K I) :
          mixedSpace K) = 0 := by
      rw [h0, Submodule.coe_zero, map_zero]
    rw [Units.unitSMulIdealLatticeEquiv_apply, norm_unit_smul] at hn
    exact (fundamentalCone.norm_pos_of_mem p.1.2).ne' hn
  · rintro ⟨a₁, q₁⟩ ⟨a₂, q₂⟩ h
    have hsmul : (Quotient.out q₁)⁻¹ • (a₁.1 : mixedSpace K) =
        (Quotient.out q₂)⁻¹ • (a₂.1 : mixedSpace K) := by
      simpa only [Function.comp_apply, Units.unitSMulIdealLatticeEquiv_apply] using
        congrArg (Subtype.val ∘ Subtype.val) h
    have hu : Quotient.out q₂ * (Quotient.out q₁)⁻¹ ∈ torsion K := by
      rw [← fundamentalCone.unit_smul_mem_iff_mem_torsion a₁.2, mul_smul, hsmul, smul_inv_smul]
      exact a₂.2
    have hq : q₁ = q₂ := by
      have hmk : QuotientGroup.mk (s := torsion K) (Quotient.out q₂ * (Quotient.out q₁)⁻¹) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hu
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq', QuotientGroup.out_eq',
        mul_inv_eq_one] at hmk
      exact hmk.symm
    subst hq
    exact Prod.ext (Subtype.ext
      (((Quotient.out q₁)⁻¹.unitSMulIdealLatticeEquiv I).injective (congrArg Subtype.val h))) rfl
  · rintro ⟨x, hx0⟩
    obtain ⟨u, hu⟩ :=
      fundamentalCone.exists_unit_smul_mem (norm_ne_zero_of_idealLattice_ne_zero hx0)
    let q : (𝓞 K)ˣ ⧸ torsion K := QuotientGroup.mk u
    have hquot : QuotientGroup.mk (s := torsion K) (Quotient.out q * u⁻¹) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq', mul_inv_cancel]
    have htors : Quotient.out q * u⁻¹ ∈ torsion K := (QuotientGroup.eq_one_iff _).mp hquot
    let a : idealLattice K I := (Quotient.out q).unitSMulIdealLatticeEquiv I x
    have ha_cone : (a : mixedSpace K) ∈ fundamentalCone K := by
      have hrewrite : (a : mixedSpace K) =
          (Quotient.out q * u⁻¹) • (u • (x : mixedSpace K)) := by
        rw [Units.unitSMulIdealLatticeEquiv_apply, mul_smul, inv_smul_smul]
      rw [hrewrite]
      exact fundamentalCone.torsion_smul_mem_of_mem hu htors
    refine ⟨(⟨a, ha_cone⟩, q), Subtype.ext (Subtype.ext ?_)⟩
    simp only [a, Units.unitSMulIdealLatticeEquiv_apply, inv_smul_smul]

@[simp]
private theorem coe_orbitEquiv_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : {a : idealLattice K I // (a : mixedSpace K) ∈ fundamentalCone K} ×
      ((𝓞 K)ˣ ⧸ torsion K)) :
    (((orbitEquiv I p : {x : idealLattice K I // x ≠ 0}) : idealLattice K I) : mixedSpace K) =
      (Quotient.out p.2)⁻¹ • (p.1.1 : mixedSpace K) :=
  Units.unitSMulIdealLatticeEquiv_apply (Quotient.out p.2)⁻¹ I p.1.1

omit [NumberField K] in
/-- `unitScale u` as a homeomorphism of `realSpace K`. -/
private def unitScaleHomeomorph (u : (𝓞 K)ˣ) : realSpace K ≃ₜ realSpace K where
  toFun := unitScale u
  invFun := unitScale u⁻¹
  left_inv y := by rw [unitScale_unitScale, inv_mul_cancel, unitScale_one]
  right_inv y := by rw [unitScale_unitScale, mul_inv_cancel, unitScale_one]
  continuous_toFun := continuous_pi fun w ↦ by
    rw [show (fun y ↦ unitScale u y w) = fun y : realSpace K ↦ w (u : K) ^ 2 * y w by
      ext y; exact unitScale_apply u y w]
    fun_prop
  continuous_invFun := continuous_pi fun w ↦ by
    rw [show (fun y ↦ unitScale u⁻¹ y w) = fun y : realSpace K ↦ w ((u⁻¹ : (𝓞 K)ˣ) : K) ^ 2 * y w by
      ext y; exact unitScale_apply u⁻¹ y w]
    fun_prop

omit [NumberField K] in
@[simp]
private theorem coe_unitScaleHomeomorph (u : (𝓞 K)ˣ) :
    ⇑(unitScaleHomeomorph u) = unitScale u :=
  rfl

/-- `unitScale u` preserves the multiplicative Haar measure `archHaar K`. -/
private theorem measurePreserving_unitScale (u : (𝓞 K)ˣ) :
    MeasurePreserving (unitScale u) (archHaar K) (archHaar K) where
  measurable := coe_unitScaleHomeomorph u ▸ (unitScaleHomeomorph u).continuous.measurable
  map_eq := by
    have heq : unitScale u = ((fun w : InfinitePlace K ↦ w (u : K) ^ 2) * ·) := by
      ext y w
      simp [unitScale_apply]
    rw [heq]
    exact map_archHaar_mul_left fun w ↦ pow_pos (pos_iff.mpr (by simp)) 2

/-- The tile of the positive orthant indexed by a unit class `q ∈ (𝓞 K)ˣ ⧸ torsion K`. -/
private def conePiece (D : Set (realSpace K)) (q : (𝓞 K)ˣ ⧸ torsion K) : Set (realSpace K) :=
  unitScale (Quotient.out q) ⁻¹' unitCone D

private theorem measurableSet_conePiece {D : Set (realSpace K)} (hDm : MeasurableSet D)
    (q : (𝓞 K)ˣ ⧸ torsion K) : MeasurableSet (conePiece D q) :=
  (measurableSet_unitCone hDm).preimage
    (coe_unitScaleHomeomorph (Quotient.out q) ▸
      (unitScaleHomeomorph (Quotient.out q)).continuous.measurable)

private theorem pairwise_disjoint_conePiece {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) :
    Pairwise fun q₁ q₂ ↦ Disjoint (conePiece D q₁) (conePiece D q₂) := by
  intro q₁ q₂ hne
  refine Set.disjoint_left.mpr fun y hy₁ hy₂ ↦ hne ?_
  rw [conePiece, mem_preimage, mem_unitCone] at hy₁ hy₂
  have hs₁ : surfacePart y ∈ unitScale (Quotient.out q₁) ⁻¹' D := by
    simpa only [mem_preimage, surfacePart_unitScale] using hy₁.2
  have hs₂ : surfacePart y ∈ unitScale (Quotient.out q₂) ⁻¹' D := by
    simpa only [mem_preimage, surfacePart_unitScale] using hy₂.2
  have hmem : unitScale (Quotient.out q₂ * (Quotient.out q₁)⁻¹)
      (unitScale (Quotient.out q₁) (surfacePart y)) ∈ D := by
    rwa [← unitScale_unitScale, unitScale_unitScale (Quotient.out q₁)⁻¹, inv_mul_cancel,
      unitScale_one]
  have htors : Quotient.out q₂ * (Quotient.out q₁)⁻¹ ∈ torsion K :=
    (hD.unitScale_mem_iff _ hs₁ _).mp hmem
  have hmk : QuotientGroup.mk (s := torsion K) (Quotient.out q₂ * (Quotient.out q₁)⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr htors
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq', QuotientGroup.out_eq',
    mul_inv_eq_one] at hmk
  exact hmk.symm

private theorem iUnion_conePiece {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D) :
    ⋃ q : (𝓞 K)ˣ ⧸ torsion K, conePiece D q = {y : realSpace K | ∀ w, 0 < y w} := by
  ext y
  simp only [mem_iUnion, conePiece, mem_preimage, mem_unitCone, mem_ofPred_eq]
  refine ⟨fun ⟨q, hy⟩ w ↦ ?_, fun hy ↦ ?_⟩
  · have h := unitScale_pos (hy.1 w) (Quotient.out q)⁻¹
    rwa [unitScale_unitScale, inv_mul_cancel, unitScale_one] at h
  · obtain ⟨u, hu⟩ := hD.exists_unitScale_mem _ (surfacePart_mem_normOneSurface hy)
    let q : (𝓞 K)ˣ ⧸ torsion K := QuotientGroup.mk u
    refine ⟨q, fun w ↦ unitScale_pos (hy w) _, ?_⟩
    have hquot : QuotientGroup.mk (s := torsion K) (Quotient.out q * u⁻¹) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq', mul_inv_cancel]
    have htors : Quotient.out q * u⁻¹ ∈ torsion K := (QuotientGroup.eq_one_iff _).mp hquot
    rw [surfacePart_unitScale]
    have hmem := (hD.unitScale_mem_iff _ hu (Quotient.out q * u⁻¹)).mpr htors
    rwa [← unitScale_unitScale, unitScale_unitScale u⁻¹, inv_mul_cancel, unitScale_one] at hmem

/-- Summing the integral of `g ∘ unitScale (Quotient.out q)⁻¹` over `unitCone D` across all
`q ∈ (𝓞 K)ˣ ⧸ torsion K` recovers the integral of `g` over the whole parameter space
`archHaar K`. -/
private theorem hasSum_integral_unitCone_comp_unitScale {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    {g : realSpace K → E} (hg : Integrable g (archHaar K)) :
    HasSum (fun q : (𝓞 K)ˣ ⧸ torsion K ↦
        ∫ y in unitCone D, g (unitScale (Quotient.out q)⁻¹ y) ∂archHaar K)
      (∫ y, g y ∂archHaar K) := by
  let : Countable (𝓞 K) := Countable.of_moduleFinite (R := ℤ)
  let : Countable (𝓞 K)ˣ := Units.val_injective.countable
  let : Countable ((𝓞 K)ˣ ⧸ torsion K) := (QuotientGroup.mk'_surjective (torsion K)).countable
  have hpiece (q : (𝓞 K)ˣ ⧸ torsion K) :
      ∫ y in unitCone D, g (unitScale (Quotient.out q)⁻¹ y) ∂archHaar K =
        ∫ y in conePiece D q, g y ∂archHaar K := by
    have hpre : unitScale (Quotient.out q)⁻¹ ⁻¹' conePiece D q = unitCone D := by
      ext y
      simp only [conePiece, mem_preimage, unitScale_unitScale, mul_inv_cancel, unitScale_one]
    conv_lhs => rw [← hpre]
    exact (measurePreserving_unitScale (Quotient.out q)⁻¹).setIntegral_preimage_emb
      (coe_unitScaleHomeomorph (Quotient.out q)⁻¹ ▸
        (unitScaleHomeomorph (Quotient.out q)⁻¹).measurableEmbedding)
      g (conePiece D q)
  simp_rw [hpiece]
  have hunion : IntegrableOn g (⋃ q, conePiece D q) (archHaar K) := hg.integrableOn
  have hsum := hasSum_integral_iUnion (measurableSet_conePiece hD.measurableSet)
    (pairwise_disjoint_conePiece hD) hunion
  rwa [iUnion_conePiece hD, Measure.restrict_eq_self_of_ae_mem ae_archHaar_pos] at hsum

/-- On the open positive orthant, the norm of `archGaussian y x * (archNorm y : ℂ) ^ (s / 2)` is
`(archGaussian y x).re * archNorm y ^ (s.re / 2)`. -/
private theorem norm_archGaussian_mul_archNorm_cpow {y : realSpace K} (hy : ∀ w, 0 < y w)
    (x : mixedSpace K) (s : ℂ) :
    ‖archGaussian y x * (archNorm y : ℂ) ^ (s / 2)‖ =
      (archGaussian y x).re * archNorm y ^ (s.re / 2) := by
  have hgauss : ‖archGaussian y x‖ = (archGaussian y x).re := by
    rw [archGaussian_apply, norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), ofReal_re]
  rw [norm_mul, hgauss, norm_cpow_eq_rpow_re_of_pos (archNorm_pos hy), div_ofNat_re]

/-- **Absolute summability of the lattice-point gamma integrals over `unitCone D`.** For `σ > 1`,
the real integrals `∫_{unitCone D} N(y) ^ (σ / 2) exp(-π ∑ y_w |x_w|²) dy / y` are summable over
the nonzero points `x` of `idealLattice K I`. -/
theorem summable_integral_unitCone {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun x : {x : idealLattice K I // x ≠ 0} ↦
      ∫ y in unitCone D, archNorm y ^ (σ / 2) * (archGaussian y (x : mixedSpace K)).re
        ∂archHaar K := by
  have hσ0 : 0 < (σ : ℂ).re := by
    rw [ofReal_re]
    exact zero_lt_one.trans hσ
  have hσ1 : 1 < (σ : ℂ).re := by rwa [ofReal_re]
  set G : {x : idealLattice K I // x ≠ 0} → ℝ := fun x ↦
    ∫ y in unitCone D, archNorm y ^ (σ / 2) * (archGaussian y (x : mixedSpace K)).re ∂archHaar K
  refine (orbitEquiv I).summable_iff.mp ?_
  have hnonneg (p : {a : idealLattice K I // (a : mixedSpace K) ∈ fundamentalCone K} ×
      ((𝓞 K)ˣ ⧸ torsion K)) : 0 ≤ G (orbitEquiv I p) := by
    refine integral_nonneg_of_ae (ae_restrict_of_ae (ae_archHaar_pos.mono fun y hy ↦ ?_))
    exact mul_nonneg (Real.rpow_nonneg (archNorm_pos hy).le _) (archGaussian_re_pos y _).le
  have hrow (a : {a : idealLattice K I // (a : mixedSpace K) ∈ fundamentalCone K}) :
      HasSum (fun q : (𝓞 K)ˣ ⧸ torsion K ↦ G (orbitEquiv I (a, q)))
        ((Gammaℝ σ ^ nrRealPlaces K * Gammaℝ (2 * σ) ^ nrComplexPlaces K *
            (mixedEmbedding.norm (a.1 : mixedSpace K) : ℂ) ^ (-(σ : ℂ))).re) := by
    set g : realSpace K → ℝ :=
      fun y ↦ archNorm y ^ (σ / 2) * (archGaussian y (a.1 : mixedSpace K)).re
    have ha_norm : mixedEmbedding.norm (a.1 : mixedSpace K) ≠ 0 :=
      (fundamentalCone.norm_pos_of_mem a.2).ne'
    have hg_eq : g =ᵐ[archHaar K] fun y ↦
        (archGaussian y (a.1 : mixedSpace K) * (archNorm y : ℂ) ^ ((σ : ℂ) / 2)).re := by
      filter_upwards [ae_archHaar_pos] with y hy
      have hpow : (archNorm y : ℂ) ^ ((σ : ℂ) / 2) = ((archNorm y ^ (σ / 2) : ℝ) : ℂ) := by
        rw [show (σ : ℂ) / 2 = ((σ / 2 : ℝ) : ℂ) by push_cast; rfl,
          ← ofReal_cpow (archNorm_pos hy).le]
      simp only [g, archGaussian_apply, hpow, ← ofReal_mul, ofReal_re, mul_comm]
    have hg_int : Integrable g (archHaar K) :=
      (Complex.reCLM.integrable_comp
        (integrable_archGaussian_mul_archNorm_cpow ha_norm hσ0)).congr hg_eq.symm
    have hsum := hasSum_integral_unitCone_comp_unitScale hD hg_int
    have hterm (q : (𝓞 K)ˣ ⧸ torsion K) :
        G (orbitEquiv I (a, q)) =
          ∫ y in unitCone D, g (unitScale (Quotient.out q)⁻¹ y) ∂archHaar K := by
      refine setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y _ ↦ ?_
      simp only [g, coe_orbitEquiv_apply, archNorm_unitScale, archGaussian_unit_smul]
    have hint_val : ∫ y, g y ∂archHaar K =
        (Gammaℝ σ ^ nrRealPlaces K * Gammaℝ (2 * σ) ^ nrComplexPlaces K *
          (mixedEmbedding.norm (a.1 : mixedSpace K) : ℂ) ^ (-(σ : ℂ))).re := by
      have hint := Complex.reCLM.integral_comp_comm
        (integrable_archGaussian_mul_archNorm_cpow ha_norm hσ0)
      simp only [reCLM_apply] at hint
      rw [integral_congr_ae hg_eq, hint, integral_archGaussian_mul_archNorm_cpow ha_norm hσ0]
    rw [← hint_val]
    exact hsum.congr_fun hterm
  refine (summable_prod_of_nonneg hnonneg).mpr ⟨fun a ↦ (hrow a).summable, ?_⟩
  have hcone_summable := (hasSum_norm_cpow_fundamentalCone I hσ1).summable
  have hmul_summable : Summable fun a :
      {a : idealLattice K I // (a : mixedSpace K) ∈ fundamentalCone K} ↦
        Gammaℝ σ ^ nrRealPlaces K * Gammaℝ (2 * σ) ^ nrComplexPlaces K *
          (mixedEmbedding.norm (a.1 : mixedSpace K) : ℂ) ^ (-(σ : ℂ)) :=
    hcone_summable.mul_left _
  exact (Complex.reCLM.summable hmul_summable).congr fun a ↦ (hrow a).tsum_eq.symm

/-- If a countable family of integrable functions has summable `L¹` norms, then its pointwise `tsum`
is integrable. -/
private theorem integrable_tsum_of_summable_integral_norm {α ι : Type*} [Countable ι]
    [MeasurableSpace α] {μ : Measure α} {F : ι → α → ℂ} (hF_int : ∀ i, Integrable (F i) μ)
    (hF_sum : Summable fun i ↦ ∫ a, ‖F i a‖ ∂μ) :
    Integrable (fun a ↦ ∑' i, F i a) μ := by
  refine ⟨AEStronglyMeasurable.tsum fun i ↦ (hF_int i).1, ?_⟩
  rw [hasFiniteIntegral_iff_eNorm]
  have hterm (i : ι) : ∫⁻ a, ‖F i a‖ₑ ∂μ = ‖∫ a, ‖F i a‖ ∂μ‖ₑ := by
    dsimp [eNorm]
    rw [lintegral_coe_eq_integral _ (hF_int i).norm, ENNReal.coe_nnreal_eq, coe_nnNorm,
      Real.norm_of_nonneg (integral_nonneg fun a ↦ norm_nonneg (F i a))]
    simp only [coe_nnNorm]
  refine lt_of_le_of_lt (lintegral_mono fun a ↦ eNorm_tsum_le_tsum_eNorm) ?_
  rw [lintegral_tsum fun i ↦ (hF_int i).1.aemeasurable.eNorm, funext hterm]
  exact (ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 hF_sum.abs).lt_top

private theorem integrable_and_summable_norm_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    (∀ x : {x : idealLattice K I // x ≠ 0},
      Integrable (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K))
        ((archHaar K).restrict (unitCone D))) ∧
    Summable fun x : {x : idealLattice K I // x ≠ 0} ↦
      ∫ y in unitCone D,
        ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K)‖ ∂archHaar K := by
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  refine ⟨fun x ↦ ?_, (summable_integral_unitCone hD I hs).congr fun x ↦ ?_⟩
  · simpa only [IntegrableOn, mul_comm] using
      (integrable_archGaussian_mul_archNorm_cpow
        (norm_ne_zero_of_idealLattice_ne_zero x.2) hs0).integrableOn
  · refine (integral_congr_ae (ae_restrict_of_ae (ae_archHaar_pos.mono fun y hy ↦ ?_))).symm
    simpa only [mul_comm] using norm_archGaussian_mul_archNorm_cpow hy (x : mixedSpace K) s

/-- **Absolute integrability of the norm-weighted theta series minus `1` over `unitCone D`.** For
`Re s > 1`, `y ↦ N(y) ^ (s / 2) * (θ_{σ(I)}(y) - 1)` is integrable on `unitCone D` against
`archHaar K`. -/
theorem integrableOn_archNorm_cpow_mul_latticeTheta_sub_one {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    IntegrableOn (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1))
      (unitCone D) (archHaar K) := by
  let : Countable (idealLattice K I) := Countable.of_moduleFinite (R := ℤ)
  obtain ⟨hF_int, hF_sum⟩ := integrable_and_summable_norm_unitCone hD I hs
  refine (integrable_tsum_of_summable_integral_norm hF_int hF_sum).congr ?_
  filter_upwards [ae_restrict_of_ae ae_archHaar_pos] with y hy
  rw [latticeTheta_eq_one_add _ y hy, add_sub_cancel_left, ← tsum_mul_left]

/-- **Unfolding the cone integral of `θ_{σ(I)} - 1`.** For `Re s > 1`, integrating
`N(y) ^ (s / 2) * (θ_{σ(I)}(y) - 1)` over `unitCone D` yields `w · N(I) ^ (-s) · Γ_ℝ(s) ^ r₁ ·
Γ_ℝ(2 s) ^ r₂` times the partial zeta series of `(ClassGroup.mk K I)⁻¹`. -/
theorem integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    ∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1)
        ∂archHaar K =
      (torsionOrder K : ℂ) * ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s) *
        Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  let : Countable (idealLattice K I) := Countable.of_moduleFinite (R := ℤ)
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  set μ := (archHaar K).restrict (unitCone D)
  set F : {x : idealLattice K I // x ≠ 0} → realSpace K → ℂ :=
    fun x y ↦ (archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K)
  obtain ⟨hF_int, hF_sum⟩ := integrable_and_summable_norm_unitCone hD I hs
  have hswap : ∫ y in unitCone D,
      (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1) ∂archHaar K =
        ∑' x : {x : idealLattice K I // x ≠ 0}, ∫ y, F x y ∂μ := by
    calc ∫ y in unitCone D,
          (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1) ∂archHaar K
        = ∫ y, (∑' x, F x y) ∂μ := by
            refine integral_congr_ae (ae_restrict_of_ae (ae_archHaar_pos.mono fun y hy ↦ ?_))
            dsimp only
            rw [latticeTheta_eq_one_add _ y hy, add_sub_cancel_left, ← tsum_mul_left]
      _ = ∑' x, ∫ y, F x y ∂μ := (integral_tsum_of_summable_integral_norm hF_int hF_sum).symm
  have hnorm_sum : Summable fun x ↦ ‖∫ y, F x y ∂μ‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun x ↦ norm_integral_le_integral_norm _)
      hF_sum
  have hprod_sum : Summable fun p :
      {a : idealLattice K I // (a : mixedSpace K) ∈ fundamentalCone K} × ((𝓞 K)ˣ ⧸ torsion K) ↦
        ∫ y, F (orbitEquiv I p) y ∂μ :=
    summable_norm_iff.mp ((orbitEquiv I).summable_iff.mpr hnorm_sum)
  have hrow (a : {a : idealLattice K I // (a : mixedSpace K) ∈ fundamentalCone K}) :
      (∑' q : (𝓞 K)ˣ ⧸ torsion K, ∫ y, F (orbitEquiv I (a, q)) y ∂μ) =
        Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
          (mixedEmbedding.norm (a.1 : mixedSpace K) : ℂ) ^ (-s) := by
    have ha_norm : mixedEmbedding.norm (a.1 : mixedSpace K) ≠ 0 :=
      (fundamentalCone.norm_pos_of_mem a.2).ne'
    have hg : Integrable (fun y ↦ archGaussian y (a.1 : mixedSpace K) * (archNorm y : ℂ) ^ (s / 2))
        (archHaar K) := integrable_archGaussian_mul_archNorm_cpow ha_norm hs0
    have hsum := hasSum_integral_unitCone_comp_unitScale hD hg
    have hterm (q : (𝓞 K)ˣ ⧸ torsion K) :
        (∫ y, F (orbitEquiv I (a, q)) y ∂μ) =
          ∫ y in unitCone D, archGaussian (unitScale (Quotient.out q)⁻¹ y) (a.1 : mixedSpace K) *
            (archNorm (unitScale (Quotient.out q)⁻¹ y) : ℂ) ^ (s / 2) ∂archHaar K := by
      refine setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y _ ↦ ?_
      simp only [F, coe_orbitEquiv_apply, archNorm_unitScale, archGaussian_unit_smul, mul_comm]
    rw [(hsum.congr_fun hterm).tsum_eq, integral_archGaussian_mul_archNorm_cpow ha_norm hs0]
  rw [hswap, ← (orbitEquiv I).tsum_eq, hprod_sum.tsum_prod' fun a ↦ hprod_sum.prod_factor a]
  simp_rw [hrow, tsum_mul_left, (hasSum_norm_cpow_fundamentalCone I hs).tsum_eq]
  ring

/-! ### Covolume and complex-place normalization -/

/-- Each complex place contributes `2 · 2 ^ (-s) · Γ_ℝ(2 s) = Γ_ℂ(s)`. -/
private theorem two_mul_two_cpow_neg_mul_Gammaℝ_two_mul (s : ℂ) :
    2 * (2 : ℂ) ^ (-s) * Gammaℝ (2 * s) = Gammaℂ s := by
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * (Real.pi : ℂ) ^ (-s) := by
    rw [ofReal_mul, TauCeti.ofReal_mul_cpow zero_le_two, ofReal_ofNat]
  rw [Gammaℂ_def, Gammaℝ_def, show -(2 * s) / 2 = -s by ring, show 2 * s / 2 = s by ring,
    show (2 : ℂ) * ↑Real.pi = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl, hpi]
  ring

open scoped Classical in
/-- The covolume factor `(V_I ^ 2) ^ (s / 2)` splits into `N(I) ^ s · (2 ^ (-s)) ^ r₂ ·
|d_K| ^ (s / 2)`. -/
private theorem covolume_idealLattice_sq_cpow (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) =
      ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ s *
        ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K *
        ((|discr K| : ℤ) : ℂ) ^ (s / 2) := by
  have hN : (0 : ℝ) ≤ (FractionalIdeal.absNorm I.1 : ℚ) :=
    Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg I.1)
  have h2_nonneg : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ nrComplexPlaces K :=
    pow_nonneg (inv_nonneg.mpr zero_le_two) _
  have hV : 0 ≤ ZLattice.covolume (idealLattice K I) := by
    rw [NumberField.mixedEmbedding.covolume_idealLattice]
    exact mul_nonneg (mul_nonneg hN h2_nonneg) (Real.sqrt_nonneg _)
  have h1 : (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) =
      (ZLattice.covolume (idealLattice K I) : ℂ) ^ s := by
    rw [TauCeti.ofReal_pow_cpow hV]
    congr 1
    ring
  have h2pow : (((2 : ℝ)⁻¹ ^ nrComplexPlaces K : ℝ) : ℂ) ^ s =
      ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K := by
    have hinv : (((2 : ℝ)⁻¹ : ℝ) : ℂ) ^ s = (2 : ℂ) ^ (-s) := by
      rw [ofReal_inv, inv_cpow_ofReal_nonneg zero_le_two, ofReal_ofNat, cpow_neg]
    have hprod : ((2 : ℝ)⁻¹ ^ nrComplexPlaces K : ℝ) =
        ∏ _ ∈ Finset.range (nrComplexPlaces K), (2 : ℝ)⁻¹ := by
      rw [Finset.prod_const, Finset.card_range]
    rw [hprod, TauCeti.ofReal_prod_cpow _ fun _ _ ↦ inv_nonneg.mpr zero_le_two,
      Finset.prod_const, Finset.card_range, hinv]
  have hsqrt : ((Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) ^ s = ((|discr K| : ℤ) : ℂ) ^ (s / 2) := by
    have hsq : ((|discr K| : ℤ) : ℝ) = Real.sqrt |(discr K : ℝ)| ^ 2 := by
      rw [Int.cast_abs, Real.sq_sqrt (abs_nonneg _)]
    have hcast : ((|discr K| : ℤ) : ℂ) = ((Real.sqrt |(discr K : ℝ)| ^ 2 : ℝ) : ℂ) := by
      rw [← ofReal_intCast, hsq]
    rw [hcast, ofReal_pow, TauCeti.ofReal_pow_cpow (Real.sqrt_nonneg _)]
    congr 1
    ring
  rw [h1, NumberField.mixedEmbedding.covolume_idealLattice, mul_assoc, ofReal_mul,
    TauCeti.ofReal_mul_cpow hN, ofReal_ratCast, ofReal_mul, TauCeti.ofReal_mul_cpow h2_nonneg,
    h2pow, hsqrt]
  ring

/-- **Neukirch VII (5.5): the Mellin transform of the ideal-lattice kernel.** Over any unit
fundamental domain `D` and for `Re s > 1`, the Mellin transform at `s / 2` of
`u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K` is the completed partial zeta series
of `(ClassGroup.mk K I)⁻¹`. -/
theorem hasMellin_mellinKernel_idealLattice_sub_mellinConstant {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    HasMellin (fun u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K) (s / 2)
      (((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by
  classical
  have hm := hasMellin_mellinKernel_sub hD.measurableSet hD.isBounded (idealLattice K I) s
    (integrableOn_archNorm_cpow_mul_latticeTheta_sub_one hD I hs)
  have hc : (mellinConstant K : ℂ) = (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
      ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ) := by
    rw [mellinConstant_eq_mul_surfaceHaar_real hD]
    push_cast
    rfl
  rw [← hc] at hm
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  have hN_ne : ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ≠ 0 :=
    Rat.cast_ne_zero.mpr (FractionalIdeal.absNorm_eq_zero_iff.not.mpr I.ne_zero)
  have hN_cancel : ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ s *
      ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s) = 1 := by
    rw [← cpow_add _ _ hN_ne, add_neg_cancel, cpow_zero]
  have hGammaC : (2 : ℂ) ^ nrComplexPlaces K * ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K *
      Gammaℝ (2 * s) ^ nrComplexPlaces K = Gammaℂ s ^ nrComplexPlaces K := by
    rw [← mul_pow, ← mul_pow, two_mul_two_cpow_neg_mul_Gammaℝ_two_mul]
  have hval :
      (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
        (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) *
        (∫ y in unitCone D,
          (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1) ∂archHaar K) =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
    rw [covolume_idealLattice_sq_cpow,
      integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one hD I hs]
    calc (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
          (((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ s * ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K *
            ((|discr K| : ℤ) : ℂ) ^ (s / 2)) *
          ((torsionOrder K : ℂ) * ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s) *
            Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
            ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
              (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s))
        = ((torsionOrder K : ℂ) / (torsionOrder K : ℂ)) *
          (((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ s *
            ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s)) *
          (((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
            ((2 : ℂ) ^ nrComplexPlaces K * ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K *
              Gammaℝ (2 * s) ^ nrComplexPlaces K) *
            ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
              (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by ring
      _ = _ := by rw [div_self hw, hN_cancel, hGammaC, one_mul, one_mul]
  rwa [hval] at hm

end TauCeti.LFunctions
