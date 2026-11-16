/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.UnitQuotient
public import TauCeti.NumberTheory.LFunctions.Theta.GammaIntegral
public import TauCeti.NumberTheory.LFunctions.Theta.Mellin.Pair
public import TauCeti.NumberTheory.LFunctions.Theta.UnitCone
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Topology.Compactness.Lindelof
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Unfolding the theta integral of an ideal lattice

Let `I` be a nonzero fractional ideal of a number field `K`, and let `D` be a fundamental domain
for the unit action `unitScale` on the norm-one hypersurface `S`. On the cone `unitCone D` of
positive archimedean parameters above `D`, the nonzero points of the ideal lattice `σ(I)` break
into orbits under the quotient `(𝓞 K)ˣ ⧸ torsion K` of the units modulo torsion, each orbit
having a unique representative in `σ(I) ∩ fundamentalCone K`. Moving the unit from the lattice
point to the parameter tiles the positive orthant with disjoint measurable translates of
`unitCone D`, so each orbit assembles into a full archimedean gamma integral
`Γ_ℝ(s)^r₁ Γ_ℝ(2s)^r₂ |N(x₀)|^(-s)`.

Summing over the representatives in the fundamental cone converges absolutely for `Re s > 1`, by
scaling `I` by a positive integer to an integral ideal and invoking
`hasSum_norm_cpow_idealSet` (Neukirch VII (5.3)–(5.4)). Tonelli's theorem therefore justifies
exchanging the lattice sum with the cone integral (`summable_integral_unitCone` and
`integrableOn_archNorm_cpow_mul_latticeTheta_sub_one`) and evaluates the cone integral
(`integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one`). Feeding this integrability into
`hasMellin_mellinKernel_sub` and matching the covolume `V_I = N(I) 2^(-r₂) √|d_K|` against
`Γ_ℝ(2s) = 2^(s - 1) Γ_ℂ(s)` identifies `(mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` on
`Re s > 1` with `|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ(𝔎, s)` for the class `𝔎 = [I⁻¹]`
(`mellinKernelFEPair_idealLattice_Λ_div_two`, Neukirch VII (5.5)).

## Main results

* `TauCeti.LFunctions.hasSum_norm_cpow_idealLattice_fundamentalCone`: the fractional-ideal form
  of Neukirch (5.3)–(5.4).
* `TauCeti.LFunctions.LSeries_rayClassCoeff_one_eq_tsum_idealLattice`: the Dirichlet series of the
  class `[I⁻¹]` as a sum over `σ(I) ∩ fundamentalCone K`.
* `TauCeti.LFunctions.summable_integral_unitCone`: absolute convergence justifying the
  sum–integral interchange over `unitCone D`.
* `TauCeti.LFunctions.integrableOn_archNorm_cpow_mul_latticeTheta_sub_one`: integrability of the
  weighted theta series `N(y)^(s/2) (θ_{σ(I)}(y) - 1)` on `unitCone D` for `Re s > 1`.
* `TauCeti.LFunctions.integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one`: evaluation of the
  cone integral in terms of the fundamental-cone sum.
* `TauCeti.LFunctions.mellinKernelFEPair_idealLattice_Λ_div_two`: identification of the completed
  function `Λ(s / 2)` of the Mellin pair of `σ(I)` with the completed partial zeta series on
  `Re s > 1`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.3)–(5.5).
-/

public section
noncomputable section

open Complex MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone NumberField.Units Set
  TauCeti.GlobalNumberFields TauCeti.NumberField.mixedEmbedding
open scoped ENNReal Real nonZeroDivisors

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### The fractional-ideal cone sum -/

/-- At the trivial modulus, `oneEquivClassGroup` sends the ray class of a nonzero integral ideal
to its class in `ClassGroup (𝓞 K)`. -/
private theorem oneEquivClassGroup_idealClass (J : (Ideal (𝓞 K))⁰) :
    oneEquivClassGroup (idealClass (Modulus.one K) (integralIdealsPrimeToOneEquiv.symm J)) =
      ClassGroup.mk0 J := by
  rw [idealClass_apply, oneEquivClassGroup_rayClassMk]
  have h : (NumberFieldArithmetic.integralIdealsAwayHom K (Modulus.one K).support
      (integralIdealsPrimeToOneEquiv.symm J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      FractionalIdeal.mk0 K J := by
    apply Units.ext
    rw [NumberFieldArithmetic.coe_integralIdealsAwayHom,
      integralIdealsPrimeToOneEquiv_symm_apply_coe, FractionalIdeal.coe_mk0]
  rw [h, ClassGroup.mk_mk0]

/-- Scaling any nonzero fractional ideal `I` by a suitable positive rational integer `m` produces
a nonzero integral ideal `J` in the same class `[J] = [I]`. -/
private theorem exists_nat_mul_eq_coeIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ (m : ℕ) (J : (Ideal (𝓞 K))⁰), 0 < m ∧
      ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (m : K) * (I : FractionalIdeal (𝓞 K)⁰ K) ∧
      ClassGroup.mk0 J = ClassGroup.mk K I := by
  set d : (𝓞 K)⁰ := I.1.den
  have hd0 : (d : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  set m : ℕ := Ideal.absNorm (Ideal.span {(d : 𝓞 K)})
  have hm_pos : 0 < m := Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
    (mem_nonZeroDivisors_iff_ne_zero.mpr (mt Ideal.span_singleton_eq_bot.mp hd0))
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (Ideal.absNorm_mem (Ideal.span {(d : 𝓞 K)}))
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hc
    exact hm_pos.ne' (Nat.cast_eq_zero.mp hc)
  have hnum_ne : I.1.num ≠ ⊥ := FractionalIdeal.num_eq_zero_iff.not.mpr I.ne_zero
  set J : (Ideal (𝓞 K))⁰ := ⟨Ideal.span {c} * I.1.num, mem_nonZeroDivisors_iff_ne_zero.mpr
    (mul_ne_zero (mt Ideal.span_singleton_eq_bot.mp hc0) hnum_ne)⟩
  have hJ_eq : ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (m : K) * (I : FractionalIdeal (𝓞 K)⁰ K) := by
    have hmd : (m : K) = (c : K) * ((d : 𝓞 K) : K) := by
      have := congrArg (algebraMap (𝓞 K) K) hc
      simpa only [map_natCast, map_mul, mul_comm] using this
    rw [show (J : Ideal (𝓞 K)) = Ideal.span {c} * I.1.num from rfl, FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.coeIdeal_span_singleton, hmd, map_mul,
      mul_assoc, ← FractionalIdeal.den_mul_self_eq_num']
  have hJ_class : ClassGroup.mk0 J = ClassGroup.mk K I := by
    rw [← ClassGroup.mk_mk0 K J, ← div_eq_one, ← map_div, ClassGroup.mk_eq_one_iff]
    refine ⟨⟨(m : K), ?_⟩⟩
    have hdiv : ((FractionalIdeal.mk0 K J / I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ (m : K) := by
      rw [div_eq_mul_inv, Units.val_mul, FractionalIdeal.coe_mk0, hJ_eq, mul_assoc,
        Units.mul_inv, mul_one]
    rw [hdiv, FractionalIdeal.coeToSubmodule_spanSingleton]
  exact ⟨m, J, hm_pos, hJ_eq, hJ_class⟩

/-- **The fractional-ideal version of Neukirch (5.3)–(5.4).** For any nonzero fractional ideal `I`
and `Re s > 1`, the sum of `|N(x)|^(-s)` over the nonzero points of `σ(I)` in Mathlib's fundamental
cone is `w · N(I)^(-s)` times the sum of `N(𝔟)^(-s)` over the nonzero integral ideals `𝔟` of the
class `[I]⁻¹`. -/
theorem hasSum_norm_cpow_idealLattice_fundamentalCone (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum
      (fun x : {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K} ↦
        ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-s))
      (torsionOrder K *
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s) *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by
  obtain ⟨m, J, hm_pos, hJ_eq, hJ_class⟩ := exists_nat_mul_eq_coeIdeal I
  have hm_real_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
  -- Multiplication by the positive real `m` identifies `σ(I) ∩ cone` with `idealSet K J`.
  have hmem_J (x : K) : x ∈ (I : FractionalIdeal (𝓞 K)⁰ K) ↔
      ∃ a : 𝓞 K, a ∈ (J : Ideal (𝓞 K)) ∧ (a : K) = (m : K) * x := by
    constructor
    · intro hx
      have hmx : (m : K) * x ∈ ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
        rw [hJ_eq]
        exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hx
      obtain ⟨a, haJ, ha⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hmx
      exact ⟨a, haJ, ha⟩
    · rintro ⟨a, haJ, ha⟩
      have hmx : (m : K) * x ∈ FractionalIdeal.spanSingleton (𝓞 K)⁰ (m : K) *
          (I : FractionalIdeal (𝓞 K)⁰ K) := by
        rw [← hJ_eq, ← ha]
        exact (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mpr ⟨a, haJ, rfl⟩
      have hinv : (m : K)⁻¹ * ((m : K) * x) ∈ FractionalIdeal.spanSingleton (𝓞 K)⁰ (m : K)⁻¹ *
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ (m : K) * (I : FractionalIdeal (𝓞 K)⁰ K)) :=
        FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hmx
      rw [← mul_assoc, ← map_mul,
        inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hm_pos.ne'), map_one,
        one_mul, inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr hm_pos.ne')] at hinv
      exact hinv
  have hsmul_emb (a : K) : (m : ℝ) • mixedEmbedding K a = mixedEmbedding K ((m : K) * a) := by
    rw [map_mul, map_natCast]
    ext w <;> simp [Algebra.smul_def]
  let e : {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K} ≃
      idealSet K J :=
    { toFun := fun x ↦ ⟨(m : ℝ) • (x : mixedSpace K), by
        obtain ⟨a, haI, ha⟩ := (mem_idealLattice K I).mp x.1.2
        obtain ⟨b, hbJ, hb⟩ := (hmem_J a).mp haI
        refine mem_idealSet.mpr ⟨(fundamentalCone.smul_mem_iff_mem hm_real_pos.ne').mpr
          x.2.2, ⟨b, hbJ, ?_⟩⟩
        rw [← ha, hsmul_emb, hb]⟩
      invFun := fun y ↦ ⟨⟨(m : ℝ)⁻¹ • (y : mixedSpace K), by
        obtain ⟨b, hbJ, hb⟩ := (mem_idealSet.mp y.2).2
        refine (mem_idealLattice K I).mpr ⟨(m : K)⁻¹ * (b : K), (hmem_J _).mpr ⟨b, hbJ, ?_⟩, ?_⟩
        · rw [mul_inv_cancel_left₀ (Nat.cast_ne_zero.mpr hm_pos.ne')]
        · have h1 : (m : ℝ) • mixedEmbedding K ((m : K)⁻¹ * (b : K)) =
              mixedEmbedding K (b : K) := by
            rw [hsmul_emb, mul_inv_cancel_left₀ (Nat.cast_ne_zero.mpr hm_pos.ne')]
          rw [← hb, ← h1, inv_smul_smul₀ hm_real_pos.ne']⟩,
        by
          intro h0
          have hy0 : (y : mixedSpace K) = 0 := by
            have := congrArg (fun z : idealLattice K I ↦ (m : ℝ) • (z : mixedSpace K)) h0
            simpa [smul_smul, mul_inv_cancel₀ hm_real_pos.ne'] using this
          exact (fundamentalCone.norm_pos_of_mem (mem_idealSet.mp y.2).1).ne'
            (by rw [hy0, map_zero]),
        (fundamentalCone.smul_mem_iff_mem (inv_ne_zero hm_real_pos.ne')).mpr
          (mem_idealSet.mp y.2).1⟩
      left_inv := fun x ↦ Subtype.ext (Subtype.ext (by
        simp [smul_smul, inv_mul_cancel₀ hm_real_pos.ne']))
      right_inv := fun y ↦ Subtype.ext (by
        simp [smul_smul, mul_inv_cancel₀ hm_real_pos.ne']) }
  -- Compare norms: `N(J) = m^n N(I)` and `|N(m • x)| = m^n |N(x)|`.
  have hnorm_J : (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) =
      (m : ℝ) ^ Module.finrank ℚ K *
        (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
    have hq : (Ideal.absNorm (J : Ideal (𝓞 K)) : ℚ) =
        (m : ℚ) ^ Module.finrank ℚ K * FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [← FractionalIdeal.coeIdeal_absNorm (K := K), hJ_eq, map_mul,
        FractionalIdeal.absNorm_span_singleton (𝓞 K),
        show (m : K) = algebraMap ℚ K (m : ℚ) by simp, Algebra.norm_algebraMap,
        abs_of_nonneg (pow_nonneg (Nat.cast_nonneg m) _)]
    exact_mod_cast hq
  have hmn_pos : (0 : ℝ) < (m : ℝ) ^ Module.finrank ℚ K := pow_pos hm_real_pos _
  have hNI_pos : (0 : ℝ) < FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) := by
    have hne : FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      (FractionalIdeal.absNorm_eq_zero_iff).not.mpr I.ne_zero
    exact_mod_cast (FractionalIdeal.absNorm_nonneg I.1).lt_of_ne' hne
  have hcpow_J : (Ideal.absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s) =
      (((m : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s) *
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s) := by
    have h1 : (Ideal.absNorm (J : Ideal (𝓞 K)) : ℂ) =
        (((m : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) *
          ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) := by
      exact_mod_cast hnorm_J
    rw [h1, ← Complex.ofReal_ratCast, Complex.mul_cpow_ofReal_nonneg hmn_pos.le hNI_pos.le]
  -- Match the ideal-sum subtype `{𝔟 // IsPrincipal (𝔟 * J)}` with `{𝔟 // [𝔟] = [I]⁻¹}`.
  have htsum_eq :
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // Submodule.IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)))},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) =
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
    refine (Equiv.subtypeEquivRight fun 𝔟 : (Ideal (𝓞 K))⁰ ↦ ?_).tsum_eq
      (fun 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹} ↦
        (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s))
    rw [← Submonoid.coe_mul, ← ClassGroup.mk0_eq_one_iff (𝔟 * J).2, Subtype.coe_eta, map_mul,
      mul_eq_one_iff_eq_inv, hJ_class]
  -- Transport `hasSum_norm_cpow_idealSet J hs` along `e` and cancel `((m : ℝ)^n : ℂ)^(-s)`.
  have hsumJ := (e.hasSum_iff).mpr (hasSum_norm_cpow_idealSet J hs)
  have hmul := hsumJ.mul_left ((((m : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ s)
  have hcancel : (((m : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ s *
      (((m : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s) = 1 := by
    rw [← Complex.cpow_add _ _ (by exact_mod_cast hmn_pos.ne'), add_neg_cancel, Complex.cpow_zero]
  have hval : (((m : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ s *
        (torsionOrder K * (Ideal.absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s) *
          ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ //
              Submodule.IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)))},
            (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) =
      torsionOrder K *
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s) *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
    rw [hcpow_J, htsum_eq]
    calc (((m : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ s *
          (torsionOrder K * ((((m : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s) *
            ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s)) *
          ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
            (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s))
        = ((((m : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ s *
            (((m : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s)) *
          (torsionOrder K *
            ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s) *
          ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
            (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by ring
      _ = _ := by rw [hcancel, one_mul]
  rw [← hval]
  refine hmul.congr_fun fun x ↦ ?_
  simp only [Function.comp_apply, e, Equiv.coe_fn_mk, mixedEmbedding.norm_smul,
    abs_of_pos hm_real_pos, Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg hmn_pos.le (mixedEmbedding.norm_nonneg _),
    ← mul_assoc, hcancel, one_mul]

/-- The Dirichlet series of the class `[I⁻¹]` at the trivial modulus equals the sum of
`N(𝔟)^(-s)` over the nonzero integral ideals `𝔟` of that class. -/
theorem LSeries_rayClassCoeff_one_eq_tsum_classGroup (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (normCoeff K (rayClassCoeff (Modulus.one K)
        (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹))) s =
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
        (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective (R := 𝓞 K) (ClassGroup.mk K I)
  have hJray : idealClass (Modulus.one K) (integralIdealsPrimeToOneEquiv.symm J) =
      (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹)⁻¹ := by
    apply oneEquivClassGroup.injective
    simp [oneEquivClassGroup_idealClass, hJ]
  rw [LSeries_rayClassCoeff_one_eq_tsum J hJray hs]
  refine (Equiv.subtypeEquivRight fun 𝔟 : (Ideal (𝓞 K))⁰ ↦ ?_).tsum_eq
    (fun 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹} ↦
      (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s))
  rw [← Submonoid.coe_mul, ← ClassGroup.mk0_eq_one_iff (𝔟 * J).2, Subtype.coe_eta, map_mul,
    mul_eq_one_iff_eq_inv, hJ]

/-- **Neukirch (5.3)–(5.4) for a fractional ideal**: the partial zeta function of the class `[I⁻¹]`
is `N(I)^s / w` times the sum of `|N(x)|^(-s)` over the nonzero points of `σ(I)` in the fundamental
cone. -/
theorem LSeries_rayClassCoeff_one_eq_tsum_idealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (normCoeff K (rayClassCoeff (Modulus.one K)
        (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹))) s =
      ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s / torsionOrder K *
        ∑' x : {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K},
          ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-s) := by
  have hI0 : ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ≠ 0 :=
    Rat.cast_ne_zero.mpr ((FractionalIdeal.absNorm_eq_zero_iff).not.mpr I.ne_zero)
  have hIs : ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h ↦ hI0 h.1
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  rw [(hasSum_norm_cpow_idealLattice_fundamentalCone I hs).tsum_eq,
    LSeries_rayClassCoeff_one_eq_tsum_classGroup I hs, Complex.cpow_neg]
  field_simp

/-- The real-norm series `∑_{x ∈ σ(I) ∩ cone} |N(x)|^(-σ)` converges for `1 < σ`. -/
theorem summable_norm_rpow_idealLattice_fundamentalCone (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {σ : ℝ} (hσ : 1 < σ) :
    Summable fun x : {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K} ↦
      mixedEmbedding.norm (x : mixedSpace K) ^ (-σ) := by
  have hC := (hasSum_norm_cpow_idealLattice_fundamentalCone I (s := (σ : ℂ)) (by simpa)).summable
  refine (Complex.reCLM.summable hC).congr fun x ↦ ?_
  have hpos : 0 < mixedEmbedding.norm (x : mixedSpace K) := fundamentalCone.norm_pos_of_mem x.2.2
  rw [Complex.reCLM_apply, ← Complex.ofReal_neg, ← Complex.ofReal_cpow hpos.le, Complex.ofReal_re]

/-! ### Unfolding over a unit cone -/

omit [NumberField K] in
/-- Unit scaling on the archimedean parameters as a measurable equivalence. -/
private def unitScaleMeasurableEquiv (u : (𝓞 K)ˣ) : realSpace K ≃ᵐ realSpace K where
  toFun := unitScale u
  invFun := unitScale u⁻¹
  left_inv y := by rw [unitScale_unitScale, inv_mul_cancel, unitScale_one]
  right_inv y := by rw [unitScale_unitScale, mul_inv_cancel, unitScale_one]
  measurable_toFun := Measurable.of_eval fun w ↦ by
    have h : (fun y : realSpace K ↦ unitScale u y w) = fun y ↦ w (u : K) ^ 2 * y w :=
      funext fun y ↦ unitScale_apply u y w
    simpa only [Equiv.coe_fn_mk, h] using
      (measurable_pi_apply w : Measurable fun y : realSpace K ↦ y w).const_mul _
  measurable_invFun := Measurable.of_eval fun w ↦ by
    have h : (fun y : realSpace K ↦ unitScale u⁻¹ y w) =
        fun y ↦ w ((u⁻¹ : (𝓞 K)ˣ) : K) ^ 2 * y w :=
      funext fun y ↦ unitScale_apply u⁻¹ y w
    simpa only [Equiv.coe_fn_symm_mk, h] using
      (measurable_pi_apply w : Measurable fun y : realSpace K ↦ y w).const_mul _

/-- Unit scaling preserves the multiplicative Haar measure `dy / y`. -/
private theorem measurePreserving_unitScale (u : (𝓞 K)ˣ) :
    MeasurePreserving (unitScale u) (archHaar K) (archHaar K) := by
  refine ⟨(unitScaleMeasurableEquiv u).measurable, ?_⟩
  have hfn : unitScale u = ((fun w : InfinitePlace K ↦ w (u : K) ^ 2) * ·) :=
    funext fun y ↦ funext fun w ↦ unitScale_apply u y w
  rw [hfn]
  exact map_archHaar_mul_left fun w ↦ pow_pos (InfinitePlace.pos_iff.mpr (by simp)) 2

private theorem countable_units_quotient_torsion (K : Type*) [Field K] [NumberField K] :
    Countable ((𝓞 K)ˣ ⧸ torsion K) := by
  have : Countable (𝓞 K) := (NumberField.RingOfIntegers.basis K).repr.injective.countable
  have : Countable (𝓞 K)ˣ := Units.val_injective.countable
  exact Quotient.countable

/-- Translates of `unitCone D` by coset representatives of `(𝓞 K)ˣ ⧸ torsion K` partition the
positive orthant into pairwise disjoint measurable sets. -/
private theorem iUnion_unitScale_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) :
    ⋃ g : (𝓞 K)ˣ ⧸ torsion K, unitScale (Quotient.out g) '' unitCone D =
      {y : realSpace K | ∀ w, 0 < y w} := by
  ext y
  simp only [mem_iUnion, mem_image, mem_unitCone, mem_ofPred_eq]
  constructor
  · rintro ⟨g, z, ⟨hz, _⟩, rfl⟩ w
    exact unitScale_pos (hz w) _
  · intro hy
    obtain ⟨u, hu⟩ := hD.exists_unitScale_mem (surfacePart y) (surfacePart_mem_normOneSurface hy)
    set g : (𝓞 K)ˣ ⧸ torsion K := QuotientGroup.mk u⁻¹
    have htor : u * Quotient.out g ∈ torsion K := by
      have hmk : QuotientGroup.mk (Quotient.out g) = QuotientGroup.mk u⁻¹ := Quotient.out_eq g
      have hrel : (Quotient.out g)⁻¹ * u⁻¹ ∈ torsion K := QuotientGroup.eq.mp hmk
      simpa [mul_inv_rev] using (torsion K).inv_mem hrel
    refine ⟨g, unitScale (Quotient.out g)⁻¹ y, ⟨fun w ↦ unitScale_pos (hy w) _, ?_⟩, ?_⟩
    · have hEq : surfacePart (unitScale (Quotient.out g)⁻¹ y) =
          unitScale (u * Quotient.out g)⁻¹ (unitScale u (surfacePart y)) := by
        rw [surfacePart_unitScale, unitScale_unitScale, mul_inv_rev, mul_assoc, inv_mul_cancel,
          mul_one]
      rw [hEq]
      exact (hD.unitScale_mem_iff _ hu _).mpr ((torsion K).inv_mem htor)
    · rw [unitScale_unitScale, mul_inv_cancel, unitScale_one]

/-- Distinct coset representatives of `(𝓞 K)ˣ ⧸ torsion K` give disjoint translates of
`unitCone D`. -/
private theorem pairwiseDisjoint_unitScale_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) :
    Pairwise (Function.onFun Disjoint fun g : (𝓞 K)ˣ ⧸ torsion K ↦
      unitScale (Quotient.out g) '' unitCone D) := by
  intro g₁ g₂ hne
  refine Set.disjoint_left.mpr fun y hy₁ hy₂ ↦ hne ?_
  obtain ⟨z₁, hz₁, rfl⟩ := hy₁
  obtain ⟨z₂, hz₂, hzEq⟩ := hy₂
  have hz₂' : unitScale ((Quotient.out g₂)⁻¹ * Quotient.out g₁) (surfacePart z₁) ∈ D := by
    have h1 : unitScale ((Quotient.out g₂)⁻¹ * Quotient.out g₁) z₁ = z₂ := by
      rw [← unitScale_unitScale, ← hzEq, unitScale_unitScale, inv_mul_cancel, unitScale_one]
    rw [← surfacePart_unitScale, h1]
    exact (mem_unitCone.mp hz₂).2
  have htor : (Quotient.out g₂)⁻¹ * Quotient.out g₁ ∈ torsion K :=
    (hD.unitScale_mem_iff _ (mem_unitCone.mp hz₁).2 _).mp hz₂'
  rw [← Quotient.out_eq g₁, ← Quotient.out_eq g₂]
  exact (QuotientGroup.eq.mpr htor).symm

/-- Every nonzero point of an ideal lattice has nonzero norm in the mixed space. -/
private theorem norm_ne_zero_of_mem_idealLattice {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {x : idealLattice K I} (hx : x ≠ 0) : mixedEmbedding.norm (x : mixedSpace K) ≠ 0 := by
  obtain ⟨a, _, ha⟩ := (mem_idealLattice K I).mp x.2
  have ha0 : a ≠ 0 := fun h0 ↦ hx (Subtype.ext (by simp [← ha, h0]))
  rw [← ha, mixedEmbedding.norm_eq_norm]
  exact Rat.cast_ne_zero (α := ℝ).mpr (abs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr ha0))

omit [NumberField K] in
/-- Acting by a unit sends nonzero mixed-space points to nonzero points. -/
private theorem unit_smul_ne_zero (u : (𝓞 K)ˣ) {x : mixedSpace K} (hx : x ≠ 0) :
    u • x ≠ 0 := by
  intro h0
  apply hx
  have := congrArg (u⁻¹ • ·) h0
  rw [inv_smul_smul, smul_zero] at this
  exact this

/-- Bijection between `((𝓞 K)ˣ ⧸ torsion K) × (σ(I) ∩ fundamentalCone K)` and the nonzero points
of `σ(I)`, sending `(g, x₀)` to `Quotient.out g • x₀`. -/
private def idealLatticeUnitOrbitEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((𝓞 K)ˣ ⧸ torsion K) ×
      {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K} ≃
      {x : idealLattice K I // x ≠ 0} where
  toFun p := ⟨⟨Quotient.out p.1 • (p.2.1 : mixedSpace K),
      (Quotient.out p.1).unitSMul_mem_idealLattice_iff I _ |>.mpr p.2.1.2⟩,
    fun h0 ↦ unit_smul_ne_zero (Quotient.out p.1) (fun h ↦ p.2.2.1 (Subtype.ext h))
      (congrArg Subtype.val h0)⟩
  invFun x := by
    have hx_norm := norm_ne_zero_of_mem_idealLattice x.2
    let u := (fundamentalCone.exists_unit_smul_mem hx_norm).choose
    have hu : u • (x : mixedSpace K) ∈ fundamentalCone K :=
      (fundamentalCone.exists_unit_smul_mem hx_norm).choose_spec
    let g : (𝓞 K)ˣ ⧸ torsion K := QuotientGroup.mk u⁻¹
    have htor : (Quotient.out g)⁻¹ * u⁻¹ ∈ torsion K :=
      QuotientGroup.eq.mp (Quotient.out_eq g)
    refine (g, ⟨⟨(Quotient.out g)⁻¹ • (x : mixedSpace K),
      (Quotient.out g)⁻¹.unitSMul_mem_idealLattice_iff I _ |>.mpr x.1.2⟩,
      fun h0 ↦ unit_smul_ne_zero (Quotient.out g)⁻¹ (fun h ↦ x.2 (Subtype.ext h))
        (congrArg Subtype.val h0), ?_⟩)
    dsimp only
    have hEq : (Quotient.out g)⁻¹ • (x : mixedSpace K) =
        ((Quotient.out g)⁻¹ * u⁻¹) • (u • (x : mixedSpace K)) := by
      rw [mul_smul, inv_smul_smul]
    rw [hEq]
    exact fundamentalCone.torsion_smul_mem_of_mem hu htor
  left_inv p := by
    have hy_norm : mixedEmbedding.norm (Quotient.out p.1 • (p.2.1 : mixedSpace K)) ≠ 0 :=
      norm_ne_zero_of_mem_idealLattice (I := I)
        (x := ⟨Quotient.out p.1 • (p.2.1 : mixedSpace K),
          (Quotient.out p.1).unitSMul_mem_idealLattice_iff I _ |>.mpr p.2.1.2⟩)
        (fun h0 ↦ unit_smul_ne_zero (Quotient.out p.1) (fun h ↦ p.2.2.1 (Subtype.ext h))
          (congrArg Subtype.val h0))
    set u := (fundamentalCone.exists_unit_smul_mem hy_norm).choose
    have hu : u • (Quotient.out p.1 • (p.2.1 : mixedSpace K)) ∈ fundamentalCone K :=
      (fundamentalCone.exists_unit_smul_mem hy_norm).choose_spec
    have htor : u * Quotient.out p.1 ∈ torsion K :=
      (fundamentalCone.unit_smul_mem_iff_mem_torsion p.2.2.2 _).mp
        (by simpa only [mul_smul] using hu)
    have hg : (QuotientGroup.mk u⁻¹ : (𝓞 K)ˣ ⧸ torsion K) = p.1 := by
      rw [← Quotient.out_eq p.1]
      exact QuotientGroup.eq.mpr (by simpa using htor)
    apply Prod.ext
    · exact hg
    · apply Subtype.ext
      apply Subtype.ext
      dsimp only
      rw [hg, inv_smul_smul]
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [smul_inv_smul]

/-- The nonnegative `lintegral` over `unitCone D` of the orbit of a representative `x₀` in
`σ(I) ∩ fundamentalCone K` assembles into the full gamma integral over `realSpace K`. -/
private theorem tsum_lintegral_unitCone_orbit {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {σ : ℝ} (hσ : 0 < σ)
    (x₀ : {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K}) :
    ∑' g : (𝓞 K)ˣ ⧸ torsion K,
        ∫⁻ y in unitCone D,
          ENNReal.ofReal (‖archGaussian y (Quotient.out g • (x₀ : mixedSpace K))‖ *
            archNorm y ^ (σ / 2)) ∂archHaar K =
      ENNReal.ofReal (Gammaℝ (σ : ℂ) ^ nrRealPlaces K *
          Gammaℝ (2 * (σ : ℂ)) ^ nrComplexPlaces K).re *
        ENNReal.ofReal (mixedEmbedding.norm (x₀ : mixedSpace K) ^ (-σ)) := by
  have : Countable ((𝓞 K)ˣ ⧸ torsion K) := countable_units_quotient_torsion K
  set f : realSpace K → ℝ≥0∞ := fun z ↦
    ENNReal.ofReal (‖archGaussian z (x₀ : mixedSpace K)‖ * archNorm z ^ (σ / 2))
  have hstep (g : (𝓞 K)ˣ ⧸ torsion K) :
      ∫⁻ y in unitCone D,
        ENNReal.ofReal (‖archGaussian y (Quotient.out g • (x₀ : mixedSpace K))‖ *
          archNorm y ^ (σ / 2)) ∂archHaar K =
        ∫⁻ z in unitScale (Quotient.out g) '' unitCone D, f z ∂archHaar K := by
    have heq : ∀ y, ENNReal.ofReal (‖archGaussian y (Quotient.out g • (x₀ : mixedSpace K))‖ *
        archNorm y ^ (σ / 2)) = f (unitScale (Quotient.out g) y) := fun y ↦ by
      simp only [f, archGaussian_unit_smul, archNorm_unitScale]
    simp_rw [heq]
    exact (measurePreserving_unitScale (Quotient.out g)).setLIntegral_comp_emb
      (unitScaleMeasurableEquiv (Quotient.out g)).measurableEmbedding f (unitCone D)
  simp_rw [hstep]
  have hmeas (g : (𝓞 K)ˣ ⧸ torsion K) :
      MeasurableSet (unitScale (Quotient.out g) '' unitCone D) :=
    (unitScaleMeasurableEquiv (Quotient.out g)).measurableEmbedding.measurableSet_image.mpr
      (measurableSet_unitCone hD.measurableSet)
  rw [← lintegral_iUnion hmeas (pairwiseDisjoint_unitScale_unitCone hD),
    iUnion_unitScale_unitCone hD, Measure.restrict_eq_self_of_ae_mem ae_archHaar_pos]
  have hx₀_pos : 0 < mixedEmbedding.norm (x₀ : mixedSpace K) :=
    fundamentalCone.norm_pos_of_mem x₀.2.2
  have hintC := integrable_archGaussian_mul_archNorm_cpow (s := (σ : ℂ)) hx₀_pos.ne'
    (by simpa using hσ)
  have hevalC := integral_archGaussian_mul_archNorm_cpow (s := (σ : ℂ)) hx₀_pos.ne'
    (by simpa using hσ)
  have hre_eq : ∀ᵐ z ∂archHaar K,
      ‖archGaussian z (x₀ : mixedSpace K)‖ * archNorm z ^ (σ / 2) =
        (archGaussian z (x₀ : mixedSpace K) * (archNorm z : ℂ) ^ ((σ : ℂ) / 2)).re := by
    filter_upwards [ae_archHaar_pos] with z hz
    have hN : 0 < archNorm z := archNorm_pos hz
    have hpow : (archNorm z : ℂ) ^ ((σ : ℂ) / 2) = ((archNorm z ^ (σ / 2) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_ofNat, ← Complex.ofReal_div, Complex.ofReal_cpow hN.le]
    rw [archGaussian_apply, hpow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have hnonneg : 0 ≤ᵐ[archHaar K] fun z ↦
      ‖archGaussian z (x₀ : mixedSpace K)‖ * archNorm z ^ (σ / 2) := by
    filter_upwards [ae_archHaar_pos] with z hz
    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (archNorm_pos hz).le _)
  have hintR : Integrable (fun z ↦ ‖archGaussian z (x₀ : mixedSpace K)‖ * archNorm z ^ (σ / 2))
      (archHaar K) := (Complex.reCLM.integrable_comp hintC).congr (hre_eq.mono fun _ h ↦ h.symm)
  rw [← ofReal_integral_eq_lintegral_ofReal hintR hnonneg, integral_congr_ae hre_eq]
  have hint_re :
      ∫ z, (archGaussian z (x₀ : mixedSpace K) * (archNorm z : ℂ) ^ ((σ : ℂ) / 2)).re
          ∂archHaar K =
        (∫ z, archGaussian z (x₀ : mixedSpace K) * (archNorm z : ℂ) ^ ((σ : ℂ) / 2)
          ∂archHaar K).re :=
    Complex.reCLM.integral_comp_comm hintC
  rw [hint_re, hevalC]
  have hnorm_cpow : (mixedEmbedding.norm (x₀ : mixedSpace K) : ℂ) ^ (-(σ : ℂ)) =
      ((mixedEmbedding.norm (x₀ : mixedSpace K) ^ (-σ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg, Complex.ofReal_cpow hx₀_pos.le]
  rw [hnorm_cpow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    ENNReal.ofReal_mul' (Real.rpow_nonneg hx₀_pos.le _)]

/-- On the cone `unitCone D`, the pointwise enorm of each term of the theta series agrees with
the real-part norm expression `ENNReal.ofReal (‖archGaussian y x‖ * archNorm y ^ (s.re / 2))`. -/
private theorem enorm_archNorm_cpow_mul_archGaussian {y : realSpace K} (hy : ∀ w, 0 < y w)
    (x : mixedSpace K) (s : ℂ) :
    ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y x‖ₑ =
      ENNReal.ofReal (‖archGaussian y x‖ * archNorm y ^ (s.re / 2)) := by
  rw [← ofReal_norm, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (archNorm_pos hy) (s / 2), mul_comm]
  simp

/-- Tonelli finiteness for the unfolded theta sum over `unitCone D` when `1 < Re s`. -/
private theorem tsum_lintegral_unitCone_ne_top {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    ∑' x : {x : idealLattice K I // x ≠ 0},
        ∫⁻ y in unitCone D,
          ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K)‖ₑ ∂archHaar K ≠ ⊤ := by
  have hcongr (x : {x : idealLattice K I // x ≠ 0}) :
      ∫⁻ y in unitCone D,
        ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K)‖ₑ ∂archHaar K =
      ∫⁻ y in unitCone D,
        ENNReal.ofReal (‖archGaussian y (x : mixedSpace K)‖ * archNorm y ^ (s.re / 2))
          ∂archHaar K := by
    refine setLIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y hy ↦ ?_
    exact enorm_archNorm_cpow_mul_archGaussian (mem_unitCone.mp hy).1 _ s
  simp_rw [hcongr]
  rw [← (idealLatticeUnitOrbitEquiv I).tsum_eq, tsum_prod', tsum_comm]
  simp_rw [idealLatticeUnitOrbitEquiv, Equiv.coe_fn_mk,
    tsum_lintegral_unitCone_orbit hD I (zero_lt_one.trans hs), ENNReal.tsum_mul_left]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun x₀ ↦ Real.rpow_nonneg (fundamentalCone.norm_pos_of_mem x₀.2.2).le _)
    (summable_norm_rpow_idealLattice_fundamentalCone I hs)]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- **Absolute convergence for the sum–integral interchange** over `unitCone D`: for `Re s > 1`,
the integrals over `unitCone D` of the norms of the nonzero terms of `σ(I)` are summable. -/
theorem summable_integral_unitCone {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    Summable fun x : {x : idealLattice K I // x ≠ 0} ↦
      ∫ y in unitCone D,
        ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K)‖ ∂archHaar K := by
  have hfin := tsum_lintegral_unitCone_ne_top hD I hs
  have hint (x : {x : idealLattice K I // x ≠ 0}) :
      IntegrableOn (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K))
        (unitCone D) (archHaar K) := by
    have h := (integrable_archGaussian_mul_archNorm_cpow (s := s)
      (norm_ne_zero_of_mem_idealLattice x.2) (zero_lt_one.trans hs)).integrableOn
        (s := unitCone D)
    simpa only [mul_comm] using h
  have hterm (x : {x : idealLattice K I // x ≠ 0}) :
      ((∫ y in unitCone D,
          ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K)‖ ∂archHaar K).toNNReal :
          ℝ≥0∞) =
        ∫⁻ y in unitCone D,
          ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K)‖ₑ ∂archHaar K := by
    rw [← ENNReal.ofReal_coe_nnreal,
      Real.coe_toNNReal _ (integral_nonneg fun _ ↦ norm_nonneg _),
      ofReal_integral_eq_lintegral_ofReal (hint x).norm
        (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)]
    simp_rw [ofReal_norm]
  have hnn : Summable fun x : {x : idealLattice K I // x ≠ 0} ↦
      (∫ y in unitCone D,
        ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K)‖ ∂archHaar K).toNNReal :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp (by simpa only [hterm] using hfin)
  refine (NNReal.summable_coe.mpr hnn).congr fun x ↦ ?_
  exact Real.coe_toNNReal _ (integral_nonneg fun _ ↦ norm_nonneg _)

/-- **Integrability of the weighted theta series on a unit cone** for `Re s > 1`. This is the
integrability hypothesis consumed by `hasMellin_mellinKernel_sub`. -/
theorem integrableOn_archNorm_cpow_mul_latticeTheta_sub_one {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn
      (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1))
      (unitCone D) (archHaar K) := by
  have : Countable (idealLattice K I) :=
    countable_univ_iff.mp isLindelof_univ.countable_of_discrete
  have : Countable {x : idealLattice K I // x ≠ 0} := Subtype.countable
  refine ⟨?_, ?_⟩
  · refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_unitCone hD.measurableSet)
    intro y hy
    have hpos : ∀ w, 0 < y w := (mem_unitCone.mp hy).1
    have hN : 0 < archNorm y := archNorm_pos hpos
    have harch : ContinuousAt (fun z : realSpace K ↦ (archNorm z : ℂ) ^ (s / 2)) y := by
      have h1 : ContinuousAt (fun z : realSpace K ↦ (archNorm z : ℂ)) y :=
        Complex.continuous_ofReal.continuousAt.comp continuous_archNorm.continuousAt
      exact (continuousAt_cpow_const (Or.inl (by simpa using hN))).comp h1
    have hθ : ContinuousAt (fun z : realSpace K ↦ latticeTheta (idealLattice K I) z - 1) y :=
      (continuousAt_latticeTheta (idealLattice K I) hpos).sub continuousAt_const
    exact (harch.mul hθ).continuousWithinAt
  · rw [hasFiniteIntegral_iff_eNorm]
    have hle : ∫⁻ y in unitCone D,
          ‖(archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1)‖ₑ ∂archHaar K ≤
        ∫⁻ y in unitCone D,
          ∑' x : {x : idealLattice K I // x ≠ 0},
            ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K)‖ₑ ∂archHaar K := by
      refine setLIntegral_mono_ae' (measurableSet_unitCone hD.measurableSet)
        (Filter.Eventually.of_forall fun y hy ↦ ?_)
      have hpos : ∀ w, 0 < y w := (mem_unitCone.mp hy).1
      rw [latticeTheta_eq_one_add (idealLattice K I) y hpos, add_sub_cancel_left, ← tsum_mul_left]
      exact eNorm_tsum_le_tsum_eNorm
    have hmeas (x : {x : idealLattice K I // x ≠ 0}) :
        AEMeasurable (fun y ↦ ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K)‖ₑ)
          ((archHaar K).restrict (unitCone D)) := by
      have h := (integrable_archGaussian_mul_archNorm_cpow (s := s)
        (norm_ne_zero_of_mem_idealLattice x.2) (zero_lt_one.trans hs)).integrableOn
          (s := unitCone D)
      simpa only [mul_comm] using h.aestronglyMeasurable.eNorm
    rw [lintegral_tsum hmeas] at hle
    exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr (tsum_lintegral_unitCone_ne_top hD I hs))

/-- **Unfolding the cone integral of an ideal lattice** (Neukirch VII (5.5)): for `Re s > 1`,
integrating `N(y)^(s/2) (θ_{σ(I)}(y) - 1)` over `unitCone D` breaks into unit orbits that assemble
into the full archimedean gamma integral times the fundamental-cone sum. -/
theorem integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    ∫ y in unitCone D,
        (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1) ∂archHaar K =
      Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
        ∑' x : {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K},
          ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-s) := by
  have : Countable (idealLattice K I) :=
    countable_univ_iff.mp isLindelof_univ.countable_of_discrete
  have : Countable {x : idealLattice K I // x ≠ 0} := Subtype.countable
  have : Countable ((𝓞 K)ˣ ⧸ torsion K) := countable_units_quotient_torsion K
  have hint (x : {x : idealLattice K I // x ≠ 0}) :
      IntegrableOn (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K))
        (unitCone D) (archHaar K) := by
    have h := (integrable_archGaussian_mul_archNorm_cpow (s := s)
      (norm_ne_zero_of_mem_idealLattice x.2) (zero_lt_one.trans hs)).integrableOn
        (s := unitCone D)
    simpa only [mul_comm] using h
  -- Rewrite the integrand as the sum over nonzero lattice points and swap sum with integral.
  have hcongr :
      ∫ y in unitCone D,
          (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1) ∂archHaar K =
        ∫ y in unitCone D,
          ∑' x : {x : idealLattice K I // x ≠ 0},
            (archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K) ∂archHaar K := by
    refine setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y hy ↦ ?_
    rw [latticeTheta_eq_one_add (idealLattice K I) y (mem_unitCone.mp hy).1, add_sub_cancel_left,
      ← tsum_mul_left]
  rw [hcongr, integral_tsum (fun x ↦ (hint x).aestronglyMeasurable)
    (tsum_lintegral_unitCone_ne_top hD I hs)]
  -- Reindex into unit orbits with the cone representative outside and the unit coset inside.
  have hsumm : Summable fun x : {x : idealLattice K I // x ≠ 0} ↦
      ∫ y in unitCone D,
        (archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K) ∂archHaar K :=
    (summable_integral_unitCone hD I hs).of_norm_bounded fun x ↦ norm_integral_le_integral_norm _
  have hsumm_prod : Summable (fun p :
      {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K} ×
        ((𝓞 K)ˣ ⧸ torsion K) ↦
      ∫ y in unitCone D,
        (archNorm y : ℂ) ^ (s / 2) * archGaussian y (Quotient.out p.2 • (p.1.1 : mixedSpace K))
          ∂archHaar K) :=
    ((Equiv.prodComm _ _).trans (idealLatticeUnitOrbitEquiv I)).summable_iff.mpr hsumm
  rw [← ((Equiv.prodComm _ _).trans (idealLatticeUnitOrbitEquiv I)).tsum_eq]
  simp only [Equiv.trans_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap,
    idealLatticeUnitOrbitEquiv, Equiv.coe_fn_mk]
  rw [hsumm_prod.tsum_prod' (fun x₀ ↦ hsumm_prod.comp_injective fun _ _ h ↦ (Prod.mk.inj h).2)]
  -- Evaluate each orbit sum by tiling the positive orthant with translates of `unitCone D`.
  have horbit (x₀ : {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K}) :
      ∑' g : (𝓞 K)ˣ ⧸ torsion K,
          ∫ y in unitCone D,
            (archNorm y : ℂ) ^ (s / 2) *
              archGaussian y (Quotient.out g • (x₀ : mixedSpace K)) ∂archHaar K =
        Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
          ((mixedEmbedding.norm (x₀ : mixedSpace K) : ℝ) : ℂ) ^ (-s) := by
    set F : realSpace K → ℂ := fun z ↦
      (archNorm z : ℂ) ^ (s / 2) * archGaussian z (x₀ : mixedSpace K)
    have hstep (g : (𝓞 K)ˣ ⧸ torsion K) :
        ∫ y in unitCone D,
            (archNorm y : ℂ) ^ (s / 2) *
              archGaussian y (Quotient.out g • (x₀ : mixedSpace K)) ∂archHaar K =
          ∫ z in unitScale (Quotient.out g) '' unitCone D, F z ∂archHaar K := by
      have heq : ∀ y, (archNorm y : ℂ) ^ (s / 2) *
          archGaussian y (Quotient.out g • (x₀ : mixedSpace K)) =
          F (unitScale (Quotient.out g) y) := fun y ↦ by
        simp only [F, archGaussian_unit_smul, archNorm_unitScale]
      simp_rw [heq]
      exact ((measurePreserving_unitScale (Quotient.out g)).setIntegral_image_emb
        (unitScaleMeasurableEquiv (Quotient.out g)).measurableEmbedding F (unitCone D)).symm
    simp_rw [hstep]
    have hmeas (g : (𝓞 K)ˣ ⧸ torsion K) :
        MeasurableSet (unitScale (Quotient.out g) '' unitCone D) :=
      (unitScaleMeasurableEquiv (Quotient.out g)).measurableEmbedding.measurableSet_image.mpr
        (measurableSet_unitCone hD.measurableSet)
    have hFint : Integrable F (archHaar K) := by
      have h := integrable_archGaussian_mul_archNorm_cpow (s := s)
        (norm_ne_zero_of_mem_idealLattice x₀.2.1) (zero_lt_one.trans hs)
      simpa only [F, mul_comm] using h
    rw [← integral_iUnion hmeas (pairwiseDisjoint_unitScale_unitCone hD) hFint.integrableOn,
      iUnion_unitScale_unitCone hD, Measure.restrict_eq_self_of_ae_mem ae_archHaar_pos]
    simpa only [F, mul_comm] using integral_archGaussian_mul_archNorm_cpow (s := s)
      (norm_ne_zero_of_mem_idealLattice x₀.2.1) (zero_lt_one.trans hs)
  simp_rw [horbit, tsum_mul_left]

open scoped Classical in
/-- **Hecke's integral identity for an ideal lattice**, Neukirch VII (5.5): on `Re s > 1`, the
completed function `Λ` of `mellinKernelFEPair hD (idealLattice K I)` evaluated at `s / 2` equals
`|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂` times the partial zeta Dirichlet series of the ideal class
`[I⁻¹]`. -/
theorem mellinKernelFEPair_idealLattice_Λ_div_two {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) *
        Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
        LSeries (normCoeff K (rayClassCoeff (Modulus.one K)
          (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹))) s := by
  have hs_half : 1 / 2 < (s / 2).re := by
    simp only [Complex.div_ofNat_re]
    linarith
  have hm1 := hasMellin_mellinKernel_sub_mellinConstant hD (idealLattice K I) hs_half
  have hm2 := hasMellin_mellinKernel_sub hD.measurableSet hD.isBounded (idealLattice K I) s
    (integrableOn_archNorm_cpow_mul_latticeTheta_sub_one hD I hs)
  have hconst : (mellinConstant K : ℂ) =
      (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
        ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ) := by
    rw [mellinConstant_eq_mul_surfaceHaar_real hD]
    push_cast
    rfl
  rw [hconst] at hm1
  have hΛ : (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) =
      (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
        ((ZLattice.covolume (idealLattice K I) : ℂ) ^ 2) ^ (s / 2) *
        ∫ y in unitCone D,
          (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1) ∂archHaar K :=
    hm1.2.symm.trans hm2.2
  -- Expand the covolume `V_I = N(I) 2^(-r₂) √|d_K|` into the powers of `N(I)`, `2`, and `|d_K|`.
  have hNI_nonneg : (0 : ℝ) ≤ FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) := by
    exact_mod_cast FractionalIdeal.absNorm_nonneg I.1
  have hdiscr_nonneg : (0 : ℝ) ≤ |(discr K : ℝ)| := abs_nonneg _
  have hV_sq : (ZLattice.covolume (idealLattice K I) : ℝ) ^ 2 =
      ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ 2 *
        ((2⁻¹ : ℝ) ^ nrComplexPlaces K) ^ 2) * |(discr K : ℝ)| := by
    rw [covolume_idealLattice, mul_pow, mul_pow, Real.sq_sqrt hdiscr_nonneg]
  have hpow_cov : ((ZLattice.covolume (idealLattice K I) : ℂ) ^ 2) ^ (s / 2) =
      ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s *
        ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K *
        ((|discr K| : ℤ) : ℂ) ^ (s / 2) := by
    have h1 : ((ZLattice.covolume (idealLattice K I) : ℂ) ^ 2) =
        (((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ 2 *
          ((2⁻¹ : ℝ) ^ nrComplexPlaces K) ^ 2 : ℝ) : ℂ) *
          ((|(discr K : ℝ)| : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, hV_sq, Complex.ofReal_mul]
    have h2 : (((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ 2 : ℝ) : ℂ) ^
        (s / 2) = ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s := by
      rw [Complex.ofReal_pow, TauCeti.ofReal_pow_cpow hNI_nonneg, Complex.ofReal_ratCast]
      congr 1
      ring
    have h3 : ((((2⁻¹ : ℝ) ^ nrComplexPlaces K) ^ 2 : ℝ) : ℂ) ^ (s / 2) =
        ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K := by
      have harg2 : (2 : ℂ).arg ≠ Real.pi := by
        rw [← Complex.ofReal_ofNat, Complex.arg_ofReal_of_nonneg zero_le_two]
        exact Real.pi_ne_zero.symm
      rw [← pow_mul, mul_comm (nrComplexPlaces K) 2, pow_mul, Complex.ofReal_pow,
        TauCeti.ofReal_pow_cpow (sq_nonneg _), Complex.ofReal_pow,
        TauCeti.ofReal_pow_cpow (by positivity), Complex.ofReal_inv, Complex.ofReal_ofNat,
        Complex.inv_cpow (2 : ℂ) _ harg2, ← Complex.cpow_neg, ← Complex.cpow_nat_mul]
      congr 1
      ring
    have h4 : ((|(discr K : ℝ)| : ℝ) : ℂ) = ((|discr K| : ℤ) : ℂ) := by
      rw [← Int.cast_abs, Complex.ofReal_intCast]
    rw [h1, Complex.mul_cpow_ofReal_nonneg (by positivity) hdiscr_nonneg,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (sq_nonneg _) (sq_nonneg _),
      h2, h3, h4]
  -- Absorb `2^r₂ * (2^(-s))^r₂` into `Gammaℝ (2 * s) ^ r₂` using `2 * 2^(-s) * Γ_ℝ(2s) = Γ_ℂ(s)`.
  have hGammaℂ : (2 : ℂ) * (2 : ℂ) ^ (-s) * Gammaℝ (2 * s) = Gammaℂ s := by
    have h2pi : (2 * (Real.pi : ℂ)) ^ (-s) = (2 : ℂ) ^ (-s) * (Real.pi : ℂ) ^ (-s) := by
      rw [← Complex.ofReal_ofNat, Complex.mul_cpow_ofReal_nonneg zero_le_two Real.pi_pos.le,
        Complex.ofReal_ofNat]
    rw [Gammaℝ_def, Gammaℂ_def, h2pi]
    have h1 : -(2 * s) / 2 = -s := by ring
    have h2 : 2 * s / 2 = s := by ring
    rw [h1, h2]
    ring
  rw [hΛ, integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one hD I hs,
    LSeries_rayClassCoeff_one_eq_tsum_idealLattice I hs, hpow_cov]
  calc (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
        (((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s *
          ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K * ((|discr K| : ℤ) : ℂ) ^ (s / 2)) *
        (Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
          ∑' x : {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K},
            ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-s))
      = ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
          ((2 : ℂ) * (2 : ℂ) ^ (-s) * Gammaℝ (2 * s)) ^ nrComplexPlaces K *
          (((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s /
            (torsionOrder K : ℂ) *
            ∑' x : {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K},
              ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-s)) := by
        rw [mul_pow, mul_pow]
        ring
    _ = _ := by rw [hGammaℂ]

end TauCeti.LFunctions
