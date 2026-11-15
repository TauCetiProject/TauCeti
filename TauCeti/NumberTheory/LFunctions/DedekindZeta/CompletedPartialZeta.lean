/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import TauCeti.Analysis.Meromorphic.Continuation
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.PartialZeta
public import TauCeti.NumberTheory.LFunctions.Theta.Mellin.Pair
public import TauCeti.NumberTheory.LFunctions.Theta.Surface.Cone
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.NumberTheory.LFunctions.DedekindZeta.UnitQuotient
import TauCeti.NumberTheory.LFunctions.Theta.GammaIntegral
import TauCeti.NumberTheory.LFunctions.Theta.UnitCone
import TauCeti.NumberTheory.NumberField.Units.Dirichlet

/-!
# The completed partial zeta function of a fractional ideal

Let `K` be a number field of signature `(r₁, r₂)` and discriminant `d_K`, and let `I` be an
invertible fractional ideal of `K`. The integral ideals `𝔟` of the class `𝔎 = [I⁻¹]` are the
nonzero integral ideals of `𝓞 K` for which `𝔟 I` is a principal fractional ideal. Following
Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.3)–(5.9), the completed partial zeta
function attached to `I` is

`Z(𝔎, s) = |d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ∑_{𝔟 ∈ 𝔎} N(𝔟) ^ (-s)`

on `Re s > 1`, continued meromorphically to `ℂ` in canonical normal form
(`TauCeti.meromorphicContinuation`).

Hecke's proof of meromorphic continuation and the functional equation unfolds the integral of the
multi-parameter theta series `θ_{σ(I)}(y) - 1` over the cone `unitCone D` above any unit
fundamental domain `D` on the norm-one hypersurface:

1. Clearing the denominator of `I` by a positive natural number scales `σ(I) ∩ fundamentalCone K`
   onto Mathlib's `fundamentalCone.idealSet K J` for a nonzero integral ideal `J`, lifting the
   cone-sum identity of `UnitQuotient` from integral ideals to arbitrary invertible fractional
   ideals (`hasSum_norm_cpow_fundamentalCone` and
   `LSeries_rayClassCoeff_one_eq_tsum_fractionalIdeal`).
2. Dirichlet's unit theorem splits `(𝓞 K)ˣ` into its finite torsion subgroup of order `w` and a
   free abelian group `(Fin (Units.rank K) → ℤ)`. On the positive orthant `unitCone D` is a
   fundamental domain for that free part, while each nonzero `((𝓞 K)ˣ / μ(K))`-orbit of `σ(I)`
   meets `fundamentalCone K` in a single point. Unfolding the lattice sum against `archHaar K`
   therefore turns the cone integral into the sum of full archimedean gamma integrals over
   `σ(I) ∩ fundamentalCone K` (`summable_integral_unitCone` and
   `integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one`).
3. Combining the radial Mellin substitution `hasMellin_mellinKernel_sub` with
   `covolume_idealLattice` and `2 * 2 ^ (-s) * Γ_ℝ(2s) = Γ_ℂ(s)` identifies the completed series
   on `Re s > 1` with the Mellin transform `(mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`
   (`completedPartialZeta_eq_mellin` and `completedPartialZeta_eq_toMeromorphicNFOn`). The same
   fundamental-domain argument on `normOneSurface K` shows that `mellinKernel D (idealLattice K I)`
   is independent of the unit fundamental domain `D` (`mellinKernel_idealLattice_eq`).
4. Reading the properties of `mellinKernelFEPair` through `s ↦ s / 2` gives meromorphic
   continuation across `ℂ` with simple poles at `s = 0` and `s = 1` of residues `-2 a₀` and `2 a₀`,
   `a₀ = mellinConstant K = 2 ^ (r - 1) R / w`, and the functional equation
   `completedPartialZeta I (1 - s) = completedPartialZeta J s` against the trace dual
   `J = FractionalIdeal.dual ℤ ℚ I = (I 𝔡)⁻¹` (`completedPartialZeta_one_sub`). Because
   `meromorphicContinuation` normalizes poles to `0` and `s ↦ 1 - s` swaps the two poles `0` and
   `1`, the functional equation holds pointwise at every `s : ℂ` as well as on punctured germs.

## Main definitions

* `TauCeti.LFunctions.completedPartialZeta`: the canonical meromorphic continuation from `Re s > 1`
  of `|d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ∑_{𝔟 I principal} N(𝔟) ^ (-s)`.

## Main results

* `TauCeti.LFunctions.hasSum_norm_cpow_fundamentalCone`: Neukirch VII (5.3)–(5.4) for any
  invertible fractional ideal `I`.
* `TauCeti.LFunctions.mellinKernel_idealLattice_eq`: `mellinKernel D (idealLattice K I)` is
  independent of the unit fundamental domain `D`.
* `TauCeti.LFunctions.summable_integral_unitCone`,
  `TauCeti.LFunctions.integrableOn_archNorm_cpow_mul_latticeTheta_sub_one`: absolute convergence of
  Hecke's cone integral on `Re s > 1`.
* `TauCeti.LFunctions.completedPartialZeta_eq_tsum`,
  `TauCeti.LFunctions.completedPartialZeta_eq_tsum_fundamentalCone`,
  `TauCeti.LFunctions.completedPartialZeta_eq_LSeries_rayClassCoeff`,
  `TauCeti.LFunctions.completedPartialZeta_eq_integral_unitCone`,
  `TauCeti.LFunctions.completedPartialZeta_eq_mellin`: series, cone-integral, and Mellin
  representations on `Re s > 1`.
* `TauCeti.LFunctions.analyticAt_completedPartialZeta_iff`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedPartialZeta_zero`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedPartialZeta_one`,
  `TauCeti.LFunctions.tendsto_mul_completedPartialZeta_zero`,
  `TauCeti.LFunctions.tendsto_sub_one_mul_completedPartialZeta`: regularity off `{0, 1}` and
  simple poles with residues `∓ 2 * mellinConstant K`.
* `TauCeti.LFunctions.completedPartialZeta_one_sub`,
  `TauCeti.LFunctions.completedPartialZeta_one_sub_eventuallyEq`: Neukirch VII (5.9), the
  functional equation against `FractionalIdeal.dual ℤ ℚ I`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.3)–(5.9).
-/

public section

noncomputable section

open Complex Filter MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone NumberField.Units Set
  TauCeti.GlobalNumberFields TauCeti.NumberField.mixedEmbedding
open scoped Pointwise Topology nonZeroDivisors ENNReal

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### Clearing fractional denominators and summing over the fundamental cone -/

section FundamentalConeSum

/-- Every invertible fractional ideal can be scaled into a nonzero integral ideal by a positive
natural number: the absolute norm of the principal ideal generated by its denominator is a positive
integer multiple of that denominator in `𝓞 K`. -/
private theorem exists_pos_nat_spanSingleton_mul_eq_coeIdeal
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ (m : ℕ) (J : (Ideal (𝓞 K))⁰), 0 < m ∧
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (m : K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
        ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  let A : Ideal (𝓞 K) := Ideal.span {(I.1.den : 𝓞 K)}
  have hA : A ≠ ⊥ := by simp [A, nonZeroDivisors.coe_ne_zero I.1.den]
  let A_nz : (Ideal (𝓞 K))⁰ := ⟨A, mem_nonZeroDivisors_iff_ne_zero.mpr hA⟩
  let m : ℕ := Ideal.absNorm A
  have hm : 0 < m := Ideal.absNorm_pos_of_nonZeroDivisors A_nz
  obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton.mp (Ideal.absNorm_mem A)
  let J₀ : Ideal (𝓞 K) := Ideal.span {β} * (I : FractionalIdeal (𝓞 K)⁰ K).num
  have hmul : FractionalIdeal.spanSingleton (𝓞 K)⁰ (m : K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
      (J₀ : FractionalIdeal (𝓞 K)⁰ K) := by
    have hmK : (m : K) = algebraMap (𝓞 K) K β * algebraMap (𝓞 K) K I.1.den := by
      have h1 : algebraMap (𝓞 K) K (m : 𝓞 K) = (m : K) := map_natCast (algebraMap (𝓞 K) K) m
      rw [← h1, hβ, map_mul, mul_comm]
    rw [hmK, map_mul (FractionalIdeal.spanSingleton (𝓞 K)⁰), mul_assoc,
      FractionalIdeal.den_mul_self_eq_num', ← FractionalIdeal.coeIdeal_span_singleton,
      ← FractionalIdeal.coeIdeal_mul]
  have hm0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (m : K) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Nat.cast_ne_zero.mpr hm.ne')
  have hJ₀ : J₀ ≠ ⊥ := by
    rw [← FractionalIdeal.coeIdeal_ne_zero (K := K), ← hmul]
    exact mul_ne_zero hm0 I.ne_zero
  exact ⟨m, ⟨J₀, mem_nonZeroDivisors_iff_ne_zero.mpr hJ₀⟩, hm, hmul⟩

/-- A nonzero integral ideal is principal in `𝓞 K` if and only if its coercion to fractional ideals
is generated by an element of `Kˣ`. -/
private theorem isPrincipal_iff_exists_coeIdeal_eq_spanSingleton {A : Ideal (𝓞 K)} (hA : A ≠ ⊥) :
    Submodule.IsPrincipal A ↔
      ∃ y : Kˣ, (A : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (y : K) := by
  constructor
  · rintro ⟨⟨a, rfl⟩⟩
    have ha : a ≠ 0 := by
      rintro rfl
      exact hA Ideal.span_singleton_zero
    have haK : algebraMap (𝓞 K) K a ≠ 0 :=
      (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha
    exact ⟨Units.mk0 _ haK, by simp [FractionalIdeal.coeIdeal_span_singleton]⟩
  · rintro ⟨y, hy⟩
    have hyA : (y : K) ∈ (A : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [hy]
      exact FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ (y : K)
    obtain ⟨a, _, ha⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hyA
    refine ⟨⟨a, FractionalIdeal.coeIdeal_injective (K := K) ?_⟩⟩
    dsimp only
    rw [hy, ← ha, FractionalIdeal.coeIdeal_span_singleton]

/-- Scaling by a positive natural number `m` with `(m) * I = J` carries the fractional-principal
condition on `𝔟 * I` to principality of the integral product `𝔟 * J`. -/
private theorem exists_mul_eq_spanSingleton_iff_isPrincipal {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {m : ℕ} {J : (Ideal (𝓞 K))⁰} (hm : 0 < m)
    (hmI : FractionalIdeal.spanSingleton (𝓞 K)⁰ (m : K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
      ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
    (𝔟 : (Ideal (𝓞 K))⁰) :
    (∃ x : Kˣ, ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
        (I : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) ↔
      Submodule.IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K))) := by
  have hbJ : (𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)) ≠ ⊥ :=
    mul_ne_zero (mem_nonZeroDivisors_iff_ne_zero.mp 𝔟.2) (mem_nonZeroDivisors_iff_ne_zero.mp J.2)
  rw [isPrincipal_iff_exists_coeIdeal_eq_spanSingleton hbJ, FractionalIdeal.coeIdeal_mul, ← hmI]
  let mU : Kˣ := Units.mk0 (m : K) (Nat.cast_ne_zero.mpr hm.ne')
  have hmU : FractionalIdeal.spanSingleton (𝓞 K)⁰ (m : K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (mU : K) := rfl
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨mU * x, ?_⟩
    rw [mul_left_comm ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K), hx, hmU,
      ← map_mul, Units.val_mul]
  · rintro ⟨y, hy⟩
    refine ⟨mU⁻¹ * y, ?_⟩
    have hmul := congrArg (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((mU⁻¹ : Kˣ) : K) * ·) hy
    simpa only [hmU, mul_left_comm ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K), ← mul_assoc,
      ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, one_mul] using hmul

/-- The absolute norm of the principal fractional ideal generated by `m : ℕ` is `m ^ [K : ℚ]`. -/
private theorem absNorm_spanSingleton_natCast (m : ℕ) :
    FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ (m : K)) =
      (m : ℚ) ^ Module.finrank ℚ K := by
  have hcoe : FractionalIdeal.spanSingleton (𝓞 K)⁰ (m : K) =
      ((Ideal.span {(m : 𝓞 K)} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, map_natCast (algebraMap (𝓞 K) K) m]
  rw [hcoe, FractionalIdeal.coeIdeal_absNorm, Ideal.absNorm_span_singleton]
  have hnorm : Algebra.norm ℤ (m : 𝓞 K) = (m : ℤ) ^ Module.finrank ℚ K := by
    have hm : (m : 𝓞 K) = algebraMap ℤ (𝓞 K) (m : ℤ) := (map_natCast (algebraMap ℤ (𝓞 K)) m).symm
    rw [hm, Algebra.norm_algebraMap, RingOfIntegers.rank]
  rw [hnorm, Int.natAbs_pow, Int.natAbs_natCast, Nat.cast_pow]

/-- Scaling by `m > 0` with `(m) * I = J` maps `σ(I) ∩ fundamentalCone K` bijectively onto
`idealSet K J`. -/
private def coneIdealLatticeEquivIdealSet {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {m : ℕ}
    {J : (Ideal (𝓞 K))⁰} (hm : 0 < m)
    (hmI : FractionalIdeal.spanSingleton (𝓞 K)⁰ (m : K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
      ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) :
    {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K} ≃ idealSet K J where
  toFun x := ⟨(m : ℝ) • (x : mixedSpace K), by
    have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    refine (Set.mem_inter_iff _ _ _).mpr ⟨(smul_mem_iff_mem hmR).mpr x.2, ?_⟩
    obtain ⟨a, ha, ha_eq⟩ := (mem_idealLattice K I).mp x.1.2
    have hma : (m : K) * a ∈ ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [← hmI]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ (m : K)) ha
    obtain ⟨b, hbJ, hb⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hma
    refine (mem_idealLattice K (FractionalIdeal.mk0 K J)).mpr ⟨algebraMap (𝓞 K) K b, ?_, ?_⟩
    · rw [FractionalIdeal.coe_mk0]
      exact (FractionalIdeal.mem_coeIdeal (P := K) (𝓞 K)⁰).mpr ⟨b, hbJ, rfl⟩
    · have hsmul : mixedEmbedding K ((m : K) * a) = (m : ℝ) • mixedEmbedding K a := by
        ext w <;> simp
      rw [hb, hsmul, ha_eq]⟩
  invFun y := ⟨⟨(m : ℝ)⁻¹ • (y : mixedSpace K), by
    obtain ⟨_, b, hbJ, hb_eq⟩ := mem_idealSet.mp y.2
    have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    have hb_mem : algebraMap (𝓞 K) K b ∈
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (m : K) * (I : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [hmI]
      exact (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mpr ⟨b, hbJ, rfl⟩
    have hinv_mem : (m : K)⁻¹ * algebraMap (𝓞 K) K b ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := by
      have h1 := FractionalIdeal.mul_mem_mul
        (FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ (m : K)⁻¹) hb_mem
      rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hmK, map_one, one_mul] at h1
    refine (mem_idealLattice K I).mpr ⟨(m : K)⁻¹ * algebraMap (𝓞 K) K b, hinv_mem, ?_⟩
    have hsmul : mixedEmbedding K ((m : K)⁻¹ * algebraMap (𝓞 K) K b) =
        (m : ℝ)⁻¹ • mixedEmbedding K (algebraMap (𝓞 K) K b) := by
      ext w <;> simp
    rw [hsmul, hb_eq]⟩, by
    have hmR : (m : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr hm.ne')
    exact (smul_mem_iff_mem hmR).mpr (mem_idealSet.mp y.2).1⟩
  left_inv x := by
    ext1
    ext1
    exact inv_smul_smul₀ (Nat.cast_ne_zero.mpr hm.ne') _
  right_inv y := by
    ext1
    exact smul_inv_smul₀ (Nat.cast_ne_zero.mpr hm.ne') _

/-- **The sum over the points of a fractional ideal in the fundamental cone**, Neukirch VII
(5.3)–(5.4). For an invertible fractional ideal `I` and `Re s > 1`, the sum of `|N(x)| ^ (-s)`
over the points `x` of `σ(I)` lying in `fundamentalCone K` is `w N(I) ^ (-s)` times the sum of
`N(𝔟) ^ (-s)` over the nonzero integral ideals `𝔟` with `𝔟 I` principal, where `w = torsionOrder K`.
Every point in `σ(I) ∩ fundamentalCone K` is automatically nonzero because `0 ∉ fundamentalCone K`.
-/
theorem hasSum_norm_cpow_fundamentalCone (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun x : {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K} ↦
        ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-s))
      (torsionOrder K * ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s) *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
            ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
              (I : FractionalIdeal (𝓞 K)⁰ K) =
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by
  obtain ⟨m, J, hm, hmI⟩ := exists_pos_nat_spanSingleton_mul_eq_coeIdeal I
  let e := coneIdealLatticeEquivIdealSet hm hmI
  have hmR_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hm_pow_pos : (0 : ℝ) < (m : ℝ) ^ Module.finrank ℚ K := pow_pos hmR_pos _
  have hnormJ : (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) =
      (m : ℝ) ^ Module.finrank ℚ K *
        (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
    have hq := congrArg FractionalIdeal.absNorm hmI
    rw [map_mul, absNorm_spanSingleton_natCast, FractionalIdeal.coeIdeal_absNorm] at hq
    exact_mod_cast hq.symm
  have hJsum := hasSum_norm_cpow_idealSet J hs
  let eIdx : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
        ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
          (I : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)} ≃
      {𝔟 : (Ideal (𝓞 K))⁰ // Submodule.IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)))} :=
    Equiv.subtypeEquivRight (exists_mul_eq_spanSingleton_iff_isPrincipal hm hmI)
  rw [← eIdx.tsum_eq fun 𝔟 ↦ (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)] at hJsum
  have hscale_ne : (((m : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    exact fun h ↦ hm_pow_pos.ne' (ofReal_eq_zero.mp h.1)
  have hJ_cpow : (Ideal.absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s) =
      (((m : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s) *
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s) := by
    have h1 : (Ideal.absNorm (J : Ideal (𝓞 K)) : ℂ) =
        (((m : ℝ) ^ Module.finrank ℚ K *
          (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℝ) : ℂ) := by
      rw [← hnormJ, ofReal_natCast]
    rw [h1, ofReal_mul, ofReal_mul_cpow hm_pow_pos.le, ofReal_ratCast]
  have hscaled := (e.hasSum_iff.mpr hJsum).mul_left
    ((((m : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s))⁻¹
  have htarget : ((((m : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s))⁻¹ *
      (torsionOrder K * (Ideal.absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s) *
        ∑' c : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
            ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
              (I : FractionalIdeal (𝓞 K)⁰ K) =
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
          (Ideal.absNorm ((eIdx c : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℂ) ^ (-s)) =
      torsionOrder K * ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s) *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
            ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
              (I : FractionalIdeal (𝓞 K)⁰ K) =
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
    simp only [eIdx, Equiv.subtypeEquivRight_apply, Subtype.coe_mk, hJ_cpow]
    calc ((((m : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s))⁻¹ *
          (torsionOrder K * ((((m : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s) *
            ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s)) *
            ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
                ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
                  (I : FractionalIdeal (𝓞 K)⁰ K) =
                  FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
              (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s))
        = ((((m : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s))⁻¹ *
            ((((m : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s) *
              (torsionOrder K *
                ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s) *
                ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
                    ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
                      (I : FractionalIdeal (𝓞 K)⁰ K) =
                      FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
                  (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s))) := by ring
      _ = _ := inv_mul_cancel_left₀ hscale_ne _
  rw [← htarget]
  refine hscaled.congr_fun fun x ↦ ?_
  -- `e x` scales `x` by `(m : ℝ)`, multiplying its mixed norm by `m ^ [K : ℚ]`.
  have he : mixedEmbedding.norm ((e x : idealSet K J) : mixedSpace K) =
      (m : ℝ) ^ Module.finrank ℚ K * mixedEmbedding.norm (x : mixedSpace K) := by
    simpa only [e, coneIdealLatticeEquivIdealSet, Equiv.coe_fn_mk,
      abs_of_pos hmR_pos] using mixedEmbedding.norm_smul (m : ℝ) (x : mixedSpace K)
  simp only [Function.comp_apply]
  rw [he, ofReal_mul, ofReal_mul_cpow hm_pow_pos.le, inv_mul_cancel_left₀ hscale_ne]

/-- **The Dirichlet series of an ideal class for a fractional ideal representative.** For an
invertible fractional ideal `I`, the ray class `c` of the trivial modulus corresponding to
`[I]⁻¹`, and `Re s > 1`, `ζ(c, s)` is the sum of `N(𝔟) ^ (-s)` over the nonzero integral ideals `𝔟`
with `𝔟 I` principal. -/
theorem LSeries_rayClassCoeff_one_eq_tsum_fractionalIdeal
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {c : RayClassGroup (Modulus.one K)}
    (hc : oneEquivClassGroup c = (ClassGroup.mk K I)⁻¹) {s : ℂ} (hs : 1 < s.re) :
    LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s =
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
          ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
            (I : FractionalIdeal (𝓞 K)⁰ K) =
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
        (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  obtain ⟨m, J, hm, hmI⟩ := exists_pos_nat_spanSingleton_mul_eq_coeIdeal I
  let mU : Kˣ := Units.mk0 (m : K) (Nat.cast_ne_zero.mpr hm.ne')
  have hmJI : FractionalIdeal.mk0 K J = toPrincipalIdeal (𝓞 K) K mU * I := by
    ext1
    simpa [FractionalIdeal.coe_mk0, coe_toPrincipalIdeal, mU] using hmI.symm
  have hmk_prin : ClassGroup.mk K (toPrincipalIdeal (𝓞 K) K mU) = 1 :=
    ClassGroup.mk_eq_one_iff.mpr
      ⟨⟨(mU : K), by rw [coe_toPrincipalIdeal, FractionalIdeal.coeToSubmodule_spanSingleton]⟩⟩
  have hclassJ : ClassGroup.mk K (FractionalIdeal.mk0 K J) = ClassGroup.mk K I := by
    rw [hmJI, map_mul, hmk_prin, one_mul]
  have hJ : idealClass (Modulus.one K) (integralIdealsPrimeToOneEquiv.symm J) = c⁻¹ := by
    apply oneEquivClassGroup.injective
    rw [map_inv, hc, inv_inv, ← hclassJ, idealClass_apply, oneEquivClassGroup_rayClassMk]
    congr 1
    ext1
    simp [NumberFieldArithmetic.coe_integralIdealsAwayHom, FractionalIdeal.coe_mk0]
  rw [LSeries_rayClassCoeff_one_eq_tsum J hJ hs]
  let eIdx : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
        ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
          (I : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)} ≃
      {𝔟 : (Ideal (𝓞 K))⁰ // Submodule.IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)))} :=
    Equiv.subtypeEquivRight (exists_mul_eq_spanSingleton_iff_isPrincipal hm hmI)
  exact (eIdx.tsum_eq fun 𝔟 ↦ (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)).symm

end FundamentalConeSum

/-! ### Unfolding the unit action on the cone and the norm-one surface -/

section UnitUnfolding

/-- The free part of the unit group `(𝓞 K)ˣ` given by a fundamental system of units. Kept private
so no ad-hoc group action leaks into the public interface. -/
private def freeUnit : Multiplicative (Fin (rank K) → ℤ) →* (𝓞 K)ˣ where
  toFun e := ∏ i, fundSystem K i ^ Multiplicative.toAdd e i
  map_one' := by simp
  map_mul' a b := by simp [toAdd_mul, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

private theorem freeUnit_mem_torsion_iff {e : Multiplicative (Fin (rank K) → ℤ)} :
    freeUnit e ∈ torsion K ↔ e = 1 := by
  rw [freeUnit, MonoidHom.coe_mk, OneHom.coe_mk, prod_fundSystem_zpow_mem_torsion_iff,
    ← toAdd_one, Multiplicative.toAdd.injective.eq_iff]

private instance : Countable (Multiplicative (Fin (rank K) → ℤ)) :=
  let : Countable (Fin (rank K) → ℤ) := Countable.of_moduleFinite (R := ℤ)
  Countable.of_equiv (Fin (rank K) → ℤ) Multiplicative.ofAdd

/-- Every unit orbit on `normOneSurface K` meets a unit fundamental domain `D` in a unique
`freeUnit`-translate: torsion acts trivially on `realSpace K`, and Dirichlet's theorem splits
`(𝓞 K)ˣ` into torsion times `freeUnit`. -/
private theorem existsUnique_freeUnit_unitScale_mem {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) {x : realSpace K} (hx : x ∈ normOneSurface K) :
    ∃! e : Multiplicative (Fin (rank K) → ℤ), unitScale (freeUnit e) x ∈ D := by
  obtain ⟨u, hu⟩ := hD.exists_unitScale_mem x hx
  obtain ⟨p, huv, -⟩ := exist_unique_eq_mul_prod K u
  rcases p with ⟨ζ, v⟩
  dsimp only at huv
  have hζ_fix (z : realSpace K) : unitScale (ζ : (𝓞 K)ˣ) z = z := by
    ext w
    rw [unitScale_apply, (NumberField.Units.mem_torsion K).mp ζ.2 w, one_pow, one_mul]
  have hv : unitScale (freeUnit (Multiplicative.ofAdd v)) x ∈ D := by
    have : unitScale u x = unitScale (freeUnit (Multiplicative.ofAdd v)) x := by
      rw [huv, ← unitScale_unitScale, hζ_fix]
      rfl
    rwa [← this]
  refine ⟨Multiplicative.ofAdd v, hv, fun e he ↦ ?_⟩
  have hmem : unitScale (freeUnit (e * (Multiplicative.ofAdd v)⁻¹))
      (unitScale (freeUnit (Multiplicative.ofAdd v)) x) ∈ D := by
    rwa [unitScale_unitScale, ← map_mul, inv_mul_cancel_right]
  have htor := (hD.unitScale_mem_iff _ hv _).mp hmem
  exact mul_inv_eq_one.mp (freeUnit_mem_torsion_iff.mp htor)

private instance : SMul (Multiplicative (Fin (rank K) → ℤ)) (normOneSurface K) where
  smul e x := ⟨unitScale (freeUnit e) x, (unitScale_mem_normOneSurface _).mpr x.2⟩

private theorem coe_smul_normOneSurface (e : Multiplicative (Fin (rank K) → ℤ))
    (x : normOneSurface K) :
    ((e • x : normOneSurface K) : realSpace K) = unitScale (freeUnit e) x := rfl

private instance : MulAction (Multiplicative (Fin (rank K) → ℤ)) (normOneSurface K) where
  one_smul x := Subtype.ext (by rw [coe_smul_normOneSurface, map_one, unitScale_one])
  mul_smul a b x := Subtype.ext (by
    rw [coe_smul_normOneSurface, coe_smul_normOneSurface, coe_smul_normOneSurface, map_mul,
      ← unitScale_unitScale])

private instance : ContinuousConstSMul (Multiplicative (Fin (rank K) → ℤ)) (normOneSurface K) where
  continuous_const_smul e := by
    have hcont : Continuous fun x : realSpace K ↦ unitScale (freeUnit e) x :=
      continuous_pi fun w ↦ by
        simp_rw [unitScale_apply]
        fun_prop
    exact (hcont.comp continuous_subtype_val).subtype_mk fun x ↦
      (unitScale_mem_normOneSurface _).mpr x.2

private instance : SMulInvariantMeasure (Multiplicative (Fin (rank K) → ℤ)) (normOneSurface K)
    (surfaceHaar K) where
  measure_preimage_smul e s hs := by
    let c : normOneSurface K := ⟨unitScale (freeUnit e) 1,
      (unitScale_mem_normOneSurface _).mpr (mem_normOneSurface.mpr ⟨fun _ ↦ one_pos, map_one _⟩)⟩
    have heq : (e • · : normOneSurface K → normOneSurface K) = surfaceMul c := by
      ext x w
      simp [coe_smul_normOneSurface, c]
    rw [heq]
    exact (measurePreserving_surfaceMul c).measure_preimage hs.nullMeasurableSet

/-- On `normOneSurface K`, the preimage of any unit fundamental domain `D` is a measure-theoretic
fundamental domain for the free part of the unit group. -/
private theorem isFundamentalDomain_preimage_surface {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) :
    IsFundamentalDomain (Multiplicative (Fin (rank K) → ℤ))
      (Subtype.val ⁻¹' D) (surfaceHaar K) :=
  IsFundamentalDomain.mk' (measurable_subtype_coe hD.measurableSet).nullMeasurableSet
    fun x ↦ existsUnique_freeUnit_unitScale_mem hD x.2

/-- **The Mellin kernel of an ideal lattice does not depend on the unit fundamental domain.** For
an invertible fractional ideal `I`, the theta series `latticeTheta (idealLattice K I)` is invariant
under `unitScale`, and `unitScale` preserves `surfaceHaar K`, so any two unit fundamental domains
give the same kernel at every `u : ℝ`. -/
theorem mellinKernel_idealLattice_eq {D₁ D₂ : Set (realSpace K)}
    (hD₁ : IsUnitFundamentalDomain K D₁) (hD₂ : IsUnitFundamentalDomain K D₂)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : ℝ) :
    mellinKernel D₁ (idealLattice K I) u = mellinKernel D₂ (idealLattice K I) u := by
  classical
  rw [mellinKernel_def, mellinKernel_def]
  congr 1
  refine (isFundamentalDomain_preimage_surface hD₁).setIntegral_eq
    (isFundamentalDomain_preimage_surface hD₂) fun e x ↦ ?_
  simpa only [coe_smul_normOneSurface, surfaceScale_unitScale] using
    latticeTheta_unitScale I (freeUnit e)
      (surfaceScale (x : realSpace K) (u / ZLattice.covolume (idealLattice K I) ^ 2))

private instance : SMul (Multiplicative (Fin (rank K) → ℤ)) (realSpace K) where
  smul e y := unitScale (freeUnit e) y

private theorem smul_realSpace_def (e : Multiplicative (Fin (rank K) → ℤ)) (y : realSpace K) :
    e • y = unitScale (freeUnit e) y := rfl

private instance : MulAction (Multiplicative (Fin (rank K) → ℤ)) (realSpace K) where
  one_smul y := by rw [smul_realSpace_def, map_one, unitScale_one]
  mul_smul a b y := by
    rw [smul_realSpace_def, smul_realSpace_def, smul_realSpace_def, map_mul, ← unitScale_unitScale]

private instance : ContinuousConstSMul (Multiplicative (Fin (rank K) → ℤ)) (realSpace K) where
  continuous_const_smul e := by
    simp_rw [smul_realSpace_def]
    exact continuous_pi fun w ↦ by
      simp_rw [unitScale_apply]
      fun_prop

private instance : SMulInvariantMeasure (Multiplicative (Fin (rank K) → ℤ)) (realSpace K)
    (archHaar K) where
  measure_preimage_smul e s hs := by
    have hc : ∀ w : InfinitePlace K, 0 < (unitScale (freeUnit e) 1) w :=
      fun w ↦ unitScale_pos one_pos (freeUnit e)
    have heq : (e • · : realSpace K → realSpace K) = (unitScale (freeUnit e) 1 * ·) := by
      ext y w
      simp [smul_realSpace_def]
    rw [heq, ← Measure.map_apply (measurable_const_mul _) hs, map_archHaar_mul_left hc]

/-- `unitCone D` is a measure-theoretic fundamental domain for the free part of `(𝓞 K)ˣ` acting on
`realSpace K` with `archHaar K`. -/
private theorem isFundamentalDomain_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) :
    IsFundamentalDomain (Multiplicative (Fin (rank K) → ℤ)) (unitCone D) (archHaar K) := by
  refine IsFundamentalDomain.mk'' (measurableSet_unitCone hD.measurableSet).nullMeasurableSet ?_
    (fun e he ↦ Disjoint.aedisjoint (Set.disjoint_left.mpr fun y hye hy ↦ ?_))
    (fun e ↦ (measurePreserving_smul e (archHaar K)).quasiMeasurePreserving)
  · filter_upwards [ae_archHaar_pos] with y hy
    obtain ⟨e, he, -⟩ := existsUnique_freeUnit_unitScale_mem hD (surfacePart_mem_normOneSurface hy)
    refine ⟨e, mem_unitCone.mpr ⟨fun w ↦ unitScale_pos (hy w) _, ?_⟩⟩
    simpa only [smul_realSpace_def, surfacePart_unitScale] using he
  · rw [Set.mem_smul_set_iff_inv_smul_mem] at hye
    rcases mem_unitCone.mp hy with ⟨hypos, hyD⟩
    rcases mem_unitCone.mp hye with ⟨_, hyeD⟩
    have hyS : surfacePart y ∈ normOneSurface K := surfacePart_mem_normOneSurface hypos
    have h1 : unitScale (freeUnit e⁻¹) (surfacePart y) ∈ D := by
      simpa only [smul_realSpace_def, surfacePart_unitScale] using hyeD
    have h2 : unitScale (freeUnit 1) (surfacePart y) ∈ D := by
      simpa using hyD
    have heq := (existsUnique_freeUnit_unitScale_mem hD hyS).unique h1 h2
    exact he (inv_eq_one.mp heq)

private def toNonzeroIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : Multiplicative (Fin (rank K) → ℤ) ×
      {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K}) :
    {x : idealLattice K I // x ≠ 0} :=
  ⟨(freeUnit p.1).unitSMulIdealLatticeEquiv I p.2.1, fun h0 ↦ by
    have hx0 : ((p.2.1 : idealLattice K I) : mixedSpace K) ≠ 0 := by
      intro h
      exact (norm_pos_of_mem p.2.2).ne' (h ▸ mixedEmbedding.norm.map_zero')
    have hsmul : freeUnit p.1 • ((p.2.1 : idealLattice K I) : mixedSpace K) = 0 := by
      simpa only [Units.unitSMulIdealLatticeEquiv_apply, Submodule.coe_zero] using
        congrArg Subtype.val h0
    exact hx0 ((unit_smul_eq_zero (freeUnit p.1) _).mp hsmul)⟩

private theorem injective_toNonzeroIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Function.Injective (toNonzeroIdealLattice I) := by
  rintro ⟨e₁, x₁⟩ ⟨e₂, x₂⟩ h
  have hval : freeUnit e₁ • (x₁.1 : mixedSpace K) = freeUnit e₂ • (x₂.1 : mixedSpace K) := by
    simpa only [toNonzeroIdealLattice, Units.unitSMulIdealLatticeEquiv_apply] using
      congrArg (fun z : {x : idealLattice K I // x ≠ 0} ↦ (z.1 : mixedSpace K)) h
  have hmem : freeUnit (e₂⁻¹ * e₁) • (x₁.1 : mixedSpace K) ∈ fundamentalCone K := by
    have : freeUnit (e₂⁻¹ * e₁) • (x₁.1 : mixedSpace K) = (x₂.1 : mixedSpace K) := by
      rw [map_mul, map_inv, mul_smul, hval, inv_smul_smul]
    rw [this]
    exact x₂.2
  have htor : freeUnit (e₂⁻¹ * e₁) ∈ torsion K :=
    (unit_smul_mem_iff_mem_torsion x₁.2 _).mp hmem
  have he : e₁ = e₂ := (inv_mul_eq_one.mp (freeUnit_mem_torsion_iff.mp htor)).symm
  subst he
  have hx : (x₁.1 : mixedSpace K) = (x₂.1 : mixedSpace K) :=
    MulAction.injective (freeUnit e₁) hval
  exact Prod.ext rfl (Subtype.ext (Subtype.ext hx))

private theorem surjective_toNonzeroIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Function.Surjective (toNonzeroIdealLattice I) := by
  rintro ⟨x, hx⟩
  have hx_mem : (x : mixedSpace K) ∈ Set.range (mixedEmbedding K) := by
    obtain ⟨a, -, ha⟩ := (mem_idealLattice K I).mp x.2
    exact ⟨a, ha⟩
  have hx_norm : mixedEmbedding.norm (x : mixedSpace K) ≠ 0 :=
    (mixedEmbedding.norm_eq_zero_iff' hx_mem).not.mpr (by simpa using hx)
  obtain ⟨u, hu⟩ := exists_unit_smul_mem hx_norm
  obtain ⟨p, huv, -⟩ := exist_unique_eq_mul_prod K u⁻¹
  rcases p with ⟨ζ, v⟩
  dsimp only at huv
  let e := Multiplicative.ofAdd v
  let x₀_val : idealLattice K I := u.unitSMulIdealLatticeEquiv I x
  have hζx₀ : ((ζ : (𝓞 K)ˣ).unitSMulIdealLatticeEquiv I x₀_val : mixedSpace K) ∈
      fundamentalCone K := by
    rw [Units.unitSMulIdealLatticeEquiv_apply]
    have hx₀_eq : (x₀_val : mixedSpace K) = u • (x : mixedSpace K) :=
      u.unitSMulIdealLatticeEquiv_apply I x
    rw [hx₀_eq]
    exact torsion_smul_mem_of_mem hu ζ.2
  refine ⟨(e, ⟨(ζ : (𝓞 K)ˣ).unitSMulIdealLatticeEquiv I x₀_val, hζx₀⟩), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  simp only [toNonzeroIdealLattice, Units.unitSMulIdealLatticeEquiv_apply, x₀_val]
  have hcomm : freeUnit e * (ζ : (𝓞 K)ˣ) = u⁻¹ := by
    rw [mul_comm, huv]
    rfl
  rw [← mul_smul, hcomm, inv_smul_smul]

/-- Every nonzero point of `idealLattice K I` decomposes uniquely as `freeUnit e • x₀` with `x₀` in
`fundamentalCone K`: Dirichlet's theorem splits `(𝓞 K)ˣ` into torsion times `freeUnit`, and
torsion stabilizes `fundamentalCone K`. Ordered with the cone factor first so product summation
sums along unit orbits first. -/
private def nonzeroIdealLatticeEquivConeProdFree (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K} ×
      Multiplicative (Fin (rank K) → ℤ) ≃
      {x : idealLattice K I // x ≠ 0} :=
  (Equiv.prodComm _ _).trans
    (Equiv.ofBijective (toNonzeroIdealLattice I)
      ⟨injective_toNonzeroIdealLattice I, surjective_toNonzeroIdealLattice I⟩)

/-- For a nonzero point `x₀` in `fundamentalCone K`, the sum over `freeUnit` translates of its
weighted Gaussian integral on `unitCone D` equals its full archimedean gamma integral. -/
private theorem hasSum_setIntegral_unitCone_freeUnit {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) {x₀ : mixedSpace K} (hx₀ : mixedEmbedding.norm x₀ ≠ 0)
    {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun e : Multiplicative (Fin (rank K) → ℤ) ↦
        ∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) * archGaussian y (freeUnit e • x₀)
          ∂archHaar K)
      (Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
        (mixedEmbedding.norm x₀ : ℂ) ^ (-s)) := by
  set F : realSpace K → ℂ := fun y ↦ archGaussian y x₀ * (archNorm y : ℂ) ^ (s / 2)
  have hint : Integrable F (archHaar K) := integrable_archGaussian_mul_archNorm_cpow hx₀ hs
  have hint_norm : Integrable (fun y ↦ ‖F y‖) (archHaar K) := hint.norm
  have hfd := isFundamentalDomain_unitCone hD
  have hsum_norm : Summable fun e : Multiplicative (Fin (rank K) → ℤ) ↦
      ∫ y in unitCone D, ‖F (e • y)‖ ∂archHaar K := by
    refine summable_of_sum_le (c := ∫ y, ‖F y‖ ∂archHaar K)
      (fun e ↦ integral_nonneg fun _ ↦ norm_nonneg _) fun s₀ ↦ ?_
    have hdisj : PairwiseDisjoint (s₀ : Set (Multiplicative (Fin (rank K) → ℤ)))
        (fun e ↦ e • unitCone D) := fun e₁ _ e₂ _ hne ↦ by
      refine Set.disjoint_left.mpr fun y hy₁ hy₂ ↦ hne ?_
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hy₁ hy₂
      rcases mem_unitCone.mp hy₁ with ⟨hy₁_pos, hy₁D⟩
      rcases mem_unitCone.mp hy₂ with ⟨_, hy₂D⟩
      have hypos : ∀ w, 0 < y w := fun w ↦ by
        have h := hy₁_pos w
        simp only [smul_realSpace_def, unitScale_apply] at h
        exact (mul_pos_iff_of_pos_left (pow_pos (pos_at_place _ w) 2)).mp h
      have hyS := surfacePart_mem_normOneSurface hypos
      have hm₁ : unitScale (freeUnit e₁⁻¹) (surfacePart y) ∈ D := by
        simpa only [smul_realSpace_def, surfacePart_unitScale] using hy₁D
      have hm₂ : unitScale (freeUnit e₂⁻¹) (surfacePart y) ∈ D := by
        simpa only [smul_realSpace_def, surfacePart_unitScale] using hy₂D
      exact inv_injective ((existsUnique_freeUnit_unitScale_mem hD hyS).unique hm₁ hm₂)
    have hmeas (e : Multiplicative (Fin (rank K) → ℤ)) : MeasurableSet (e • unitCone D) :=
      (measurableEmbedding_const_smul e).measurableSet_image.mpr
        (measurableSet_unitCone hD.measurableSet)
    calc ∑ e ∈ s₀, ∫ y in unitCone D, ‖F (e • y)‖ ∂archHaar K
        = ∑ e ∈ s₀, ∫ y in e • unitCone D, ‖F y‖ ∂archHaar K := by
          refine Finset.sum_congr rfl fun e _ ↦ ?_
          exact ((measurePreserving_smul e (archHaar K)).setIntegral_image_emb
            (measurableEmbedding_const_smul e) (fun y ↦ ‖F y‖) (unitCone D)).symm
      _ = ∫ y in ⋃ e ∈ s₀, e • unitCone D, ‖F y‖ ∂archHaar K :=
          (integral_biUnion_finset s₀ (fun e _ ↦ hmeas e) hdisj
            fun _ _ ↦ hint_norm.integrableOn).symm
      _ ≤ ∫ y, ‖F y‖ ∂archHaar K :=
          setIntegral_le_integral hint_norm (Eventually.of_forall fun _ ↦ norm_nonneg _)
  have hsum : Summable fun e : Multiplicative (Fin (rank K) → ℤ) ↦
      ∫ y in unitCone D, F (e • y) ∂archHaar K :=
    Summable.of_norm_bounded hsum_norm fun e ↦ norm_integral_le_integral_norm _
  have htot : ∑' e : Multiplicative (Fin (rank K) → ℤ),
      ∫ y in unitCone D, F (e • y) ∂archHaar K =
        Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
          (mixedEmbedding.norm x₀ : ℂ) ^ (-s) := by
    rw [← hfd.integral_eq_tsum'' F hint]
    exact integral_archGaussian_mul_archNorm_cpow hx₀ hs
  rw [← htot]
  refine hsum.hasSum.congr_fun fun e ↦ setIntegral_congr_fun
    (measurableSet_unitCone hD.measurableSet) fun y _ ↦ ?_
  simpa only [F, smul_realSpace_def, ← archGaussian_unit_smul, archNorm_unitScale] using
    mul_comm ((archNorm y : ℂ) ^ (s / 2)) (archGaussian y (freeUnit e • x₀))

/-- **Absolute convergence of the lattice-point gamma integrals over a unit cone**, Neukirch VII
(5.5). Over `unitCone D`, the norm-weighted Gaussian integrals of the nonzero points of `σ(I)` are
summable for every `σ > 1`: grouping along unit orbits modulo torsion reduces the sum to the
convergent Dirichlet series over `σ(I) ∩ fundamentalCone K`. -/
theorem summable_integral_unitCone {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun x : {x : idealLattice K I // x ≠ 0} ↦
        ∫ y in unitCone D,
          ‖archGaussian y (x : mixedSpace K)‖ * archNorm y ^ (σ / 2) ∂archHaar K := by
  have hσ0 : 0 < ((σ : ℂ)).re := by simpa using zero_lt_one.trans hσ
  have hσ1 : 1 < ((σ : ℂ)).re := by simpa using hσ
  let e := nonzeroIdealLatticeEquivConeProdFree I
  rw [← e.summable_iff]
  have hterm (p : {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K} ×
      Multiplicative (Fin (rank K) → ℤ)) :
      (∫ y in unitCone D,
          ‖archGaussian y ((e p).1 : mixedSpace K)‖ * archNorm y ^ (σ / 2) ∂archHaar K : ℝ) =
        (∫ y in unitCone D, (archNorm y : ℂ) ^ ((σ : ℂ) / 2) *
          archGaussian y (freeUnit p.2 • (p.1.1 : mixedSpace K)) ∂archHaar K).re := by
    have he_coe : ((e p).1 : mixedSpace K) = freeUnit p.2 • (p.1.1 : mixedSpace K) :=
      (freeUnit p.2).unitSMulIdealLatticeEquiv_apply I p.1.1
    have hcongr : (fun y ↦ ‖archGaussian y ((e p).1 : mixedSpace K)‖ * archNorm y ^ (σ / 2)) =ᵐ[
        (archHaar K).restrict (unitCone D)]
        fun y ↦ ((archNorm y : ℂ) ^ ((σ : ℂ) / 2) *
          archGaussian y (freeUnit p.2 • (p.1.1 : mixedSpace K))).re := by
      filter_upwards [ae_restrict_mem (measurableSet_unitCone hD.measurableSet)] with y hy
      have hy_nn : 0 ≤ archNorm y := (archNorm_pos (mem_unitCone.mp hy).1).le
      have hcpow : (archNorm y : ℂ) ^ ((σ : ℂ) / 2) = ((archNorm y ^ (σ / 2) : ℝ) : ℂ) := by
        rw [ofReal_cpow hy_nn]
        congr 1
        push_cast
        rfl
      rw [he_coe, hcpow, archGaussian_apply, ← ofReal_mul, ofReal_re, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
    rw [integral_congr_ae hcongr]
    have hx₀ : mixedEmbedding.norm (freeUnit p.2 • (p.1.1 : mixedSpace K)) ≠ 0 := by
      rw [norm_unit_smul]
      exact (norm_pos_of_mem p.1.2).ne'
    exact Complex.reCLM.integral_comp_comm
      ((integrable_archGaussian_mul_archNorm_cpow hx₀ hσ0).integrableOn.congr_fun
        (fun y _ ↦ mul_comm _ _) (measurableSet_unitCone hD.measurableSet))
  have hnonneg (p : {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K} ×
      Multiplicative (Fin (rank K) → ℤ)) :
      0 ≤ ∫ y in unitCone D,
        ‖archGaussian y ((e p).1 : mixedSpace K)‖ * archNorm y ^ (σ / 2) ∂archHaar K :=
    setIntegral_nonneg (measurableSet_unitCone hD.measurableSet) fun y hy ↦
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (archNorm_pos (mem_unitCone.mp hy).1).le _)
  rw [Function.comp_def, summable_prod_of_nonneg hnonneg]
  have hrow (x₀ : {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K}) :
      HasSum (fun a : Multiplicative (Fin (rank K) → ℤ) ↦
          ∫ y in unitCone D,
            ‖archGaussian y ((e (x₀, a)).1 : mixedSpace K)‖ * archNorm y ^ (σ / 2) ∂archHaar K)
        ((Gammaℝ σ ^ nrRealPlaces K * Gammaℝ (2 * σ) ^ nrComplexPlaces K *
          (mixedEmbedding.norm (x₀.1 : mixedSpace K) : ℂ) ^ (-(σ : ℂ))).re) := by
    have hC := Complex.reCLM.hasSum
      (hasSum_setIntegral_unitCone_freeUnit hD (norm_pos_of_mem x₀.2).ne' hσ0)
    exact hC.congr_fun fun a ↦ hterm (x₀, a)
  refine ⟨fun x₀ ↦ (hrow x₀).summable, ?_⟩
  have hcone_sum := ((hasSum_norm_cpow_fundamentalCone I hσ1).summable).mul_left
    (Gammaℝ σ ^ nrRealPlaces K * Gammaℝ (2 * σ) ^ nrComplexPlaces K)
  exact (Complex.reCLM.summable hcone_sum).congr fun x₀ ↦ ((hrow x₀).tsum_eq).symm

/-- Nonzero points of an ideal lattice have nonzero mixed norm. -/
private theorem norm_ne_zero_of_mem_idealLattice_ne_zero {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (x : {x : idealLattice K I // x ≠ 0}) :
    mixedEmbedding.norm (x.1 : mixedSpace K) ≠ 0 := by
  have hx_mem : (x.1 : mixedSpace K) ∈ Set.range (mixedEmbedding K) := by
    obtain ⟨a, -, ha⟩ := (mem_idealLattice K I).mp x.1.2
    exact ⟨a, ha⟩
  exact (mixedEmbedding.norm_eq_zero_iff' hx_mem).not.mpr (by simpa using x.2)

/-- **Absolute integrability of the theta integral over a unit cone**, discharging the hypothesis
of `hasMellin_mellinKernel_sub` for `idealLattice K I` when `Re s > 1`. -/
theorem integrableOn_archNorm_cpow_mul_latticeTheta_sub_one {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1))
      (unitCone D) (archHaar K) := by
  let : Countable {x : idealLattice K I // x ≠ 0} :=
    have : Countable (idealLattice K I) := Countable.of_moduleFinite (R := ℤ)
    Subtype.countable
  set μ := (archHaar K).restrict (unitCone D)
  set G : realSpace K → ℂ :=
    fun y ↦ (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1)
  set F : {x : idealLattice K I // x ≠ 0} → realSpace K → ℂ :=
    fun x y ↦ (archNorm y : ℂ) ^ (s / 2) * archGaussian y (x.1 : mixedSpace K)
  have hF_int (x : {x : idealLattice K I // x ≠ 0}) : Integrable (F x) μ :=
    ((integrable_archGaussian_mul_archNorm_cpow (norm_ne_zero_of_mem_idealLattice_ne_zero x)
      (zero_lt_one.trans hs)).integrableOn).congr_fun (fun _ _ ↦ mul_comm _ _)
      (measurableSet_unitCone hD.measurableSet)
  have hF_sum : Summable fun x ↦ ∫ y, ‖F x y‖ ∂μ := by
    refine (summable_integral_unitCone hD I hs).congr fun x ↦ ?_
    refine setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y hy ↦ ?_
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (archNorm_pos (mem_unitCone.mp hy).1),
      div_ofNat_re, mul_comm]
  have hG_cont : ContinuousOn G (unitCone D) := fun y hy ↦ by
    have hy_pos := (mem_unitCone.mp hy).1
    have h1 : ContinuousAt (fun z : realSpace K ↦ (archNorm z : ℂ) ^ (s / 2)) y :=
      (Complex.continuous_ofReal.continuousAt.comp continuous_archNorm.continuousAt).cpow
        continuousAt_const (Or.inl (by simpa using archNorm_pos hy_pos))
    have h2 : ContinuousAt (fun z : realSpace K ↦ latticeTheta (idealLattice K I) z - 1) y :=
      (continuousAt_latticeTheta (idealLattice K I) hy_pos).sub continuousAt_const
    exact (h1.mul h2).continuousWithinAt
  refine ⟨hG_cont.aestronglyMeasurable (measurableSet_unitCone hD.measurableSet), ?_⟩
  rw [HasFiniteIntegral]
  have hae : (fun y ↦ ‖G y‖ₑ) =ᵐ[μ] fun y ↦ ‖∑' x, F x y‖ₑ := by
    filter_upwards [ae_restrict_mem (measurableSet_unitCone hD.measurableSet)] with y hy
    simp only [G, F, latticeTheta_eq_one_add (idealLattice K I) y (mem_unitCone.mp hy).1,
      add_sub_cancel_left, tsum_mul_left]
  rw [lintegral_congr_ae hae]
  have hle : (∫⁻ y, ‖∑' x, F x y‖ₑ ∂μ) ≤ ∑' x, ∫⁻ y, ‖F x y‖ₑ ∂μ := by
    rw [← lintegral_tsum fun x ↦ (hF_int x).aestronglyMeasurable.eNorm]
    refine lintegral_mono fun y ↦ ?_
    by_cases hy : Summable fun x ↦ ‖F x y‖
    · calc ‖∑' x, F x y‖ₑ
          = ENNReal.ofReal ‖∑' x, F x y‖ := (ofReal_norm _).symm
        _ ≤ ENNReal.ofReal (∑' x, ‖F x y‖) := ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm hy)
        _ = ∑' x, ENNReal.ofReal ‖F x y‖ :=
            ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ norm_nonneg _) hy
        _ = ∑' x, ‖F x y‖ₑ := tsum_congr fun _ ↦ ofReal_norm _
    · simp [tsum_eq_zero_of_not_summable (mt summable_norm_iff.mpr hy)]
  refine hle.trans_lt ?_
  have hterm_eq (x : {x : idealLattice K I // x ≠ 0}) :
      ∫⁻ y, ‖F x y‖ₑ ∂μ = ENNReal.ofReal (∫ y, ‖F x y‖ ∂μ) :=
    (ofReal_integral_norm_eq_lintegral_eNorm (hF_int x)).symm
  simp_rw [hterm_eq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun x ↦ integral_nonneg fun _ ↦ norm_nonneg _) hF_sum]
  exact ENNReal.ofReal_lt_top

/-- **Unfolding the cone integral to a sum over `fundamentalCone K`.** For `Re s > 1` and any unit
fundamental domain `D`, the integral of `N(y) ^ (s / 2) (θ_{σ(I)}(y) - 1)` over `unitCone D`
unfolds to `Γ_ℝ(s) ^ r₁ Γ_ℝ(2s) ^ r₂` times the sum of `|N(x)| ^ (-s)` over
`σ(I) ∩ fundamentalCone K`. -/
theorem integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    ∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1)
        ∂archHaar K =
      Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
        ∑' x : {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K},
          ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-s) := by
  let : Countable {x : idealLattice K I // x ≠ 0} :=
    have : Countable (idealLattice K I) := Countable.of_moduleFinite (R := ℤ)
    Subtype.countable
  set μ := (archHaar K).restrict (unitCone D)
  set F : {x : idealLattice K I // x ≠ 0} → realSpace K → ℂ :=
    fun x y ↦ (archNorm y : ℂ) ^ (s / 2) * archGaussian y (x.1 : mixedSpace K)
  have hF_int (x : {x : idealLattice K I // x ≠ 0}) : Integrable (F x) μ :=
    ((integrable_archGaussian_mul_archNorm_cpow (norm_ne_zero_of_mem_idealLattice_ne_zero x)
      (zero_lt_one.trans hs)).integrableOn).congr_fun (fun _ _ ↦ mul_comm _ _)
      (measurableSet_unitCone hD.measurableSet)
  have hF_sum : Summable fun x ↦ ∫ y, ‖F x y‖ ∂μ := by
    refine (summable_integral_unitCone hD I hs).congr fun x ↦ ?_
    refine setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y hy ↦ ?_
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (archNorm_pos (mem_unitCone.mp hy).1),
      div_ofNat_re, mul_comm]
  have hpointwise : (∫ y, (archNorm y : ℂ) ^ (s / 2) *
      (latticeTheta (idealLattice K I) y - 1) ∂μ) = ∫ y, (∑' x, F x y) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem (measurableSet_unitCone hD.measurableSet)] with y hy
    rw [latticeTheta_eq_one_add (idealLattice K I) y (mem_unitCone.mp hy).1,
      add_sub_cancel_left, tsum_mul_left]
  rw [hpointwise, ← integral_tsum_of_summable_integral_norm hF_int hF_sum]
  let e := nonzeroIdealLatticeEquivConeProdFree I
  have hF_int_sum : Summable fun x ↦ ∫ y, F x y ∂μ :=
    hF_sum.of_norm_bounded fun x ↦ norm_integral_le_integral_norm (F x)
  have hcomp_sum : Summable fun p :
      {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K} ×
        Multiplicative (Fin (rank K) → ℤ) ↦ ∫ y, F (e p) y ∂μ :=
    e.summable_iff.mpr hF_int_sum
  have hrow (x₀ : {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K}) :
      HasSum (fun a : Multiplicative (Fin (rank K) → ℤ) ↦ ∫ y, F (e (x₀, a)) y ∂μ)
        (Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
          ((mixedEmbedding.norm (x₀.1 : mixedSpace K) : ℝ) : ℂ) ^ (-s)) := by
    refine (hasSum_setIntegral_unitCone_freeUnit hD (norm_pos_of_mem x₀.2).ne'
      (zero_lt_one.trans hs)).congr_fun fun a ↦ ?_
    have he_coe : ((e (x₀, a)).1 : mixedSpace K) = freeUnit a • (x₀.1 : mixedSpace K) :=
      (freeUnit a).unitSMulIdealLatticeEquiv_apply I x₀.1
    simp only [F, μ, he_coe]
  rw [← e.tsum_eq, hcomp_sum.tsum_prod' fun x₀ ↦ (hrow x₀).summable, ← tsum_mul_left]
  exact tsum_congr fun x₀ ↦ (hrow x₀).tsum_eq

end UnitUnfolding

/-! ### The completed partial zeta function and Hecke's Mellin representation -/

/-- Deligne's complex gamma factor `Γ_ℂ(s) = 2 (2π) ^ (-s) Γ(s)` in terms of
`Γ_ℝ(2s) = π ^ (-s) Γ(s)`. In Hecke's integral `2` comes from `mellinKernel`, `2 ^ (-s)` from the
covolume `2 ^ (-r₂)` of `idealLattice`, and `Γ_ℝ(2s)` from the complex-place Gaussian integral. -/
private theorem two_mul_two_cpow_neg_mul_Gammaℝ_two_mul (s : ℂ) :
    2 * (2 : ℂ) ^ (-s) * Gammaℝ (2 * s) = Gammaℂ s := by
  have hpi : (2 * (Real.pi : ℂ)) ^ (-s) = (2 : ℂ) ^ (-s) * (Real.pi : ℂ) ^ (-s) := by
    simpa using ofReal_mul_cpow (r := 2) zero_le_two (Real.pi : ℂ) (-s)
  have hexp1 : -(2 * s) / 2 = -s := by ring
  have hexp2 : 2 * s / 2 = s := mul_div_cancel_left₀ s two_ne_zero
  rw [Gammaℂ_def, Gammaℝ_def, hexp1, hexp2, hpi]
  ring

/-- **The completed partial zeta function** of an invertible fractional ideal `I`, Neukirch VII
(5.4) and (5.9): the canonical meromorphic continuation (`TauCeti.meromorphicContinuation`) from
`Re s > 1` of

`|d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ∑_{𝔟} N(𝔟) ^ (-s)`,

summed over the nonzero integral ideals `𝔟` of `𝓞 K` for which `𝔟 I` is a principal fractional
ideal (the integral ideals in the class of `I⁻¹`). -/
def completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℂ → ℂ :=
  meromorphicContinuation 1 fun s ↦
    ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
          ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
            (I : FractionalIdeal (𝓞 K)⁰ K) =
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
        (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)

/-- The defining equation of `completedPartialZeta`, exposing `meromorphicContinuation`. -/
theorem completedPartialZeta_def (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I = meromorphicContinuation 1 fun s ↦
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
            ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
              (I : FractionalIdeal (𝓞 K)⁰ K) =
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := (rfl)

/-- `completedPartialZeta I` depends only on the ideal class of `I` in `ClassGroup (𝓞 K)`. -/
theorem completedPartialZeta_eq_of_mk_eq {I I' : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : ClassGroup.mk K I = ClassGroup.mk K I') :
    completedPartialZeta I = completedPartialZeta I' := by
  have hmk1 : ClassGroup.mk K (I⁻¹ * I') = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨⟨a, ha⟩⟩ := ClassGroup.mk_eq_one_iff.mp hmk1
  have ha_span : ((I⁻¹ * I' : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ a := by
    apply Subtype.coe_injective
    simpa [FractionalIdeal.coeToSubmodule_spanSingleton] using ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact (I⁻¹ * I').ne_zero (ha_span.trans (map_zero _))
  let u : Kˣ := Units.mk0 a ha0
  have hII' : (I' : FractionalIdeal (𝓞 K)⁰ K) =
      (I : FractionalIdeal (𝓞 K)⁰ K) * FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K) := by
    have hmul := congrArg ((I : FractionalIdeal (𝓞 K)⁰ K) * ·) ha_span
    simpa only [Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul, u, Units.val_mk0] using hmul
  let e : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
        ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
          (I : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)} ≃
      {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
        ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
          (I' : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)} :=
    Equiv.subtypeEquivRight fun 𝔟 ↦ by
      rw [hII', ← mul_assoc]
      refine ⟨fun ⟨x, hx⟩ ↦ ⟨x * u, by rw [hx, ← map_mul, Units.val_mul]⟩,
        fun ⟨y, hy⟩ ↦ ⟨y * u⁻¹, ?_⟩⟩
      have hmul := congrArg (· * FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u⁻¹ : Kˣ) : K)) hy
      simpa only [mul_assoc, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one,
        mul_one] using hmul
  rw [completedPartialZeta_def, completedPartialZeta_def]
  refine meromorphicContinuation_congr fun s _ ↦ ?_
  rw [← e.tsum_eq fun 𝔟 ↦ (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)]
  rfl

/-- `completedPartialZeta I` is in canonical meromorphic normal form on `ℂ`. -/
theorem meromorphicNFOn_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    MeromorphicNFOn (completedPartialZeta I) univ :=
  meromorphicNFOn_meromorphicContinuation _ _

/-- `completedPartialZeta I` is meromorphic on `ℂ`. -/
theorem meromorphic_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Meromorphic (completedPartialZeta I) :=
  meromorphicOn_univ.mp (meromorphicNFOn_completedPartialZeta I).meromorphicOn

/-- On `Re s > 1`, `(mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` agrees with the defining
completed series of `completedPartialZeta I`: covolume algebra combines `(2 ^ r₂ / w) V_I ^ s`,
`Γ_ℝ(s) ^ r₁ Γ_ℝ(2s) ^ r₂`, and `w N(I) ^ (-s)` into `|d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂`. -/
private theorem mellinKernelFEPair_Λ_div_two_eq_series {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
            ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
              (I : FractionalIdeal (𝓞 K)⁰ K) =
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  classical
  have hs2 : (1 / 2 : ℝ) < (s / 2).re := by
    rw [div_ofNat_re]
    linarith
  have hm1 := hasMellin_mellinKernel_sub_mellinConstant hD (idealLattice K I) hs2
  have hm2 := hasMellin_mellinKernel_sub hD.measurableSet hD.isBounded (idealLattice K I) s
    (integrableOn_archNorm_cpow_mul_latticeTheta_sub_one hD I hs)
  have hconst : (mellinConstant K : ℂ) =
      (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
        ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ) := by
    rw [mellinConstant_eq_mul_surfaceHaar_real hD]
    push_cast
    rfl
  rw [← hconst] at hm2
  rw [← hm1.2, hm2.2, integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one hD I hs,
    (hasSum_norm_cpow_fundamentalCone I hs).tsum_eq]
  -- Evaluate `(V_I ^ 2) ^ (s / 2)` from `covolume_idealLattice`.
  have hNI_pos : 0 < (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
    exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _)
      (Ne.symm (FractionalIdeal.absNorm_eq_zero_iff.not.mpr I.ne_zero))
  have hV_sq : ZLattice.covolume (idealLattice K I) ^ 2 =
      ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * 2⁻¹ ^ nrComplexPlaces K) ^ 2 *
        ((|discr K| : ℤ) : ℝ) := by
    rw [covolume_idealLattice, mul_pow, Int.cast_abs, Real.sq_sqrt (abs_nonneg _)]
  have ha_pos : 0 < (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
      2⁻¹ ^ nrComplexPlaces K := by positivity
  have h2 : (((2⁻¹ ^ nrComplexPlaces K : ℝ) : ℂ)) ^ s = ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K := by
    have hprod : (2⁻¹ ^ nrComplexPlaces K : ℝ) =
        ∏ _ ∈ Finset.range (nrComplexPlaces K), (2⁻¹ : ℝ) := by
      simp
    rw [hprod, ofReal_prod_cpow _ (fun _ _ ↦ by positivity), Finset.prod_const, Finset.card_range]
    congr 1
    rw [ofReal_inv, inv_cpow_ofReal_nonneg zero_le_two, ofReal_ofNat, ← cpow_neg]
  have hV_cpow : ((ZLattice.covolume (idealLattice K I) ^ 2 : ℝ) : ℂ) ^ (s / 2) =
      ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s *
        ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K * ((|discr K| : ℤ) : ℂ) ^ (s / 2) := by
    rw [hV_sq, ofReal_mul, ofReal_mul_cpow (sq_nonneg _), ofReal_pow,
      ofReal_pow_cpow ha_pos.le, show ((2 : ℕ) : ℂ) * (s / 2) = s by push_cast; ring,
      ofReal_mul, ofReal_mul_cpow hNI_pos.le, ofReal_ratCast, ofReal_intCast, h2]
  have hNI_cancel : ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s *
      ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s) = 1 := by
    rw [cpow_neg, mul_inv_cancel₀]
    rw [Ne, cpow_eq_zero_iff]
    exact fun h ↦ (Rat.cast_ne_zero.mpr (FractionalIdeal.absNorm_eq_zero_iff.not.mpr I.ne_zero)) h.1
  have hw_ne : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  have hgammaC : (2 : ℂ) ^ nrComplexPlaces K * ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K *
      Gammaℝ (2 * s) ^ nrComplexPlaces K = Gammaℂ s ^ nrComplexPlaces K := by
    rw [← mul_pow, ← mul_pow, two_mul_two_cpow_neg_mul_Gammaℝ_two_mul]
  rw [← ofReal_pow, hV_cpow]
  calc (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
        (((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s *
          ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K * ((|discr K| : ℤ) : ℂ) ^ (s / 2)) *
        (Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
          ((torsionOrder K : ℂ) *
            ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s) *
            ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
                ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
                  (I : FractionalIdeal (𝓞 K)⁰ K) =
                  FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
              (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)))
      = ((torsionOrder K : ℂ)⁻¹ * (torsionOrder K : ℂ)) *
          (((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s *
            ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s)) *
          ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
          ((2 : ℂ) ^ nrComplexPlaces K * ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K *
            Gammaℝ (2 * s) ^ nrComplexPlaces K) *
          ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
              ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
                (I : FractionalIdeal (𝓞 K)⁰ K) =
                FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
            (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
          rw [div_eq_mul_inv]
          ring
    _ = _ := by rw [inv_mul_cancel₀ hw_ne, hNI_cancel, hgammaC]; ring

private theorem analyticAt_div_two (z : ℂ) : AnalyticAt ℂ (fun w : ℂ ↦ w / 2) z :=
  (analyticAt_id (𝕜 := ℂ)).div analyticAt_const two_ne_zero

private theorem tendsto_div_two_nhdsNE (z : ℂ) :
    Tendsto (fun w : ℂ ↦ w / 2) (𝓝[≠] z) (𝓝[≠] (z / 2)) := by
  refine tendsto_nhdsWithin_iff.mpr
    ⟨(((continuous_id' : Continuous fun w : ℂ ↦ w).div_const (2 : ℂ)).tendsto z).mono_left
      nhdsWithin_le_nhds, ?_⟩
  refine eventually_nhdsWithin_of_forall fun w (hw : w ≠ z) ↦ Set.mem_compl_singleton_iff.mpr ?_
  exact fun h ↦ hw ((div_eq_div_iff two_ne_zero two_ne_zero).mp h |> mul_right_cancel₀ two_ne_zero)

/-- `z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2)` is meromorphic on `ℂ`. -/
private theorem meromorphic_mellinKernelFEPair_div_two {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Meromorphic fun z : ℂ ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2) := fun z ↦ by
  let g : ℂ → ℂ := fun w ↦ w / 2
  exact ((mellinKernelFEPair hD (idealLattice K I)).meromorphic_Λ (g z)).comp_analyticAt
    (analyticAt_div_two z)

/-- `z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2)` is analytic at `z` if and only if
`z ≠ 0` and `z ≠ 1`. -/
private theorem analyticAt_mellinKernelFEPair_div_two_iff {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (z : ℂ) :
    AnalyticAt ℂ (fun w ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (w / 2)) z ↔
      z ≠ 0 ∧ z ≠ 1 := by
  have hc : (mellinConstant K : ℂ) ≠ 0 := ofReal_ne_zero.mpr (mellinConstant_ne_zero K)
  constructor
  · intro hz
    have hmul : AnalyticAt ℂ (fun u : ℂ ↦ 2 * u) (z / 2) :=
      analyticAt_const.mul (analyticAt_id (𝕜 := ℂ))
    have hcomp : AnalyticAt ℂ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2) := by
      have heq : ((fun w ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (w / 2)) ∘
          fun u : ℂ ↦ 2 * u) = (mellinKernelFEPair hD (idealLattice K I)).Λ := by
        ext u
        simp
      have hcomp' := hz.comp_of_eq hmul (mul_div_cancel₀ z two_ne_zero)
      rwa [heq] at hcomp'
    rw [(mellinKernelFEPair hD (idealLattice K I)).analyticAt_Λ_iff] at hcomp
    simp only [mellinKernelFEPair_f₀, mellinKernelFEPair_k, mellinKernelFEPair_g₀, hc, or_false,
      ofReal_div, ofReal_one, ofReal_ofNat] at hcomp
    exact ⟨fun h0 ↦ hcomp.1 (by simp [h0]), fun h1 ↦ hcomp.2 (by simp [h1])⟩
  · rintro ⟨hz0, hz1⟩
    have hΛ : AnalyticAt ℂ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2) := by
      rw [(mellinKernelFEPair hD (idealLattice K I)).analyticAt_Λ_iff]
      simp only [mellinKernelFEPair_f₀, mellinKernelFEPair_k, mellinKernelFEPair_g₀,
        ofReal_div, ofReal_one, ofReal_ofNat]
      refine ⟨.inl (div_ne_zero hz0 two_ne_zero), .inl fun h ↦ hz1 ?_⟩
      exact (div_eq_div_iff two_ne_zero two_ne_zero).mp h |> mul_right_cancel₀ two_ne_zero
    exact hΛ.comp_of_eq (analyticAt_div_two z) rfl

/-- **Identification of `completedPartialZeta` with the normal form of Hecke's Mellin pair.** For
any unit fundamental domain `D`, `completedPartialZeta I` is the meromorphic normal form on `ℂ` of
`z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2)`. -/
theorem completedPartialZeta_eq_toMeromorphicNFOn {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I =
      toMeromorphicNFOn (fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2)) univ := by
  rw [completedPartialZeta_def]
  refine meromorphicContinuation_eq_toMeromorphicNFOn
    (meromorphic_mellinKernelFEPair_div_two hD I) (fun z hz ↦ ?_)
    (fun z hz ↦ mellinKernelFEPair_Λ_div_two_eq_series hD I hz)
  refine (analyticAt_mellinKernelFEPair_div_two_iff hD I z).mpr ⟨?_, ?_⟩
  · rintro rfl; norm_num at hz
  · rintro rfl; norm_num at hz

/-- `completedPartialZeta I` has the punctured germ of
`z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2)` at every complex point `s`. -/
theorem completedPartialZeta_eventuallyEq_mellinKernelFEPair {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    completedPartialZeta I =ᶠ[𝓝[≠] s]
      fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2) := by
  rw [completedPartialZeta_eq_toMeromorphicNFOn hD I]
  have hm : MeromorphicOn (fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2)) univ :=
    (meromorphic_mellinKernelFEPair_div_two hD I).meromorphicOn
  exact hm.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s)

/-- Off the poles `0` and `1`, `completedPartialZeta I s` equals
`(mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`. -/
theorem completedPartialZeta_eq_mellinKernelFEPair {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedPartialZeta I s = (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) := by
  rw [completedPartialZeta_eq_toMeromorphicNFOn hD I,
    toMeromorphicNFOn_apply_of_analyticAt (meromorphic_mellinKernelFEPair_div_two hD I)
      ((analyticAt_mellinKernelFEPair_div_two_iff hD I s).mpr ⟨h0, h1⟩)]

/-! ### Series, cone-integral, and Mellin representations on `Re s > 1` -/

/-- **Series representation of `completedPartialZeta` on `Re s > 1`**, Neukirch VII (5.4). -/
theorem completedPartialZeta_eq_tsum (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
            ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
              (I : FractionalIdeal (𝓞 K)⁰ K) =
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  rw [completedPartialZeta_eq_mellinKernelFEPair hD I h0 h1,
    mellinKernelFEPair_Λ_div_two_eq_series hD I hs]

/-- **Fundamental-cone representation of `completedPartialZeta` on `Re s > 1`**, Neukirch VII
(5.3)–(5.4): the completed partial zeta function as a sum over `σ(I) ∩ fundamentalCone K`. -/
theorem completedPartialZeta_eq_tsum_fundamentalCone (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s /
          (torsionOrder K : ℂ) *
        ∑' x : {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K},
          ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-s) := by
  have hNI_ne : (((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ)) ^ s ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    exact fun h ↦ (Rat.cast_ne_zero.mpr (FractionalIdeal.absNorm_eq_zero_iff.not.mpr I.ne_zero)) h.1
  have hw_ne : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  rw [completedPartialZeta_eq_tsum I hs, (hasSum_norm_cpow_fundamentalCone I hs).tsum_eq,
    cpow_neg]
  field_simp

/-- **Ray-class `LSeries` representation of `completedPartialZeta` on `Re s > 1`.** For the ray
class `c` of the trivial modulus corresponding to `[I]⁻¹`, `completedPartialZeta I s` is the
archimedean completion of `LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s`. -/
theorem completedPartialZeta_eq_LSeries_rayClassCoeff (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {c : RayClassGroup (Modulus.one K)} (hc : oneEquivClassGroup c = (ClassGroup.mk K I)⁻¹)
    {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
        LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s := by
  rw [completedPartialZeta_eq_tsum I hs, LSeries_rayClassCoeff_one_eq_tsum_fractionalIdeal I hc hs]

open scoped Classical in
/-- **Cone-integral representation of `completedPartialZeta` on `Re s > 1`**, Neukirch VII (5.5)
before the radial Mellin substitution: over `unitCone D` for any unit fundamental domain `D`,
`completedPartialZeta I s` is `(2 ^ r₂ / w) V_I ^ s` times the `N(y) ^ (s / 2)`-weighted integral
of `θ_{σ(I)}(y) - 1`. -/
theorem completedPartialZeta_eq_integral_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta I s =
      (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
        (ZLattice.covolume (idealLattice K I) : ℂ) ^ s *
          ∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) *
            (latticeTheta (idealLattice K I) y - 1) ∂archHaar K := by
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hs2 : (1 / 2 : ℝ) < (s / 2).re := by rw [div_ofNat_re]; linarith
  have hm1 := hasMellin_mellinKernel_sub_mellinConstant hD (idealLattice K I) hs2
  have hm2 := hasMellin_mellinKernel_sub hD.measurableSet hD.isBounded (idealLattice K I) s
    (integrableOn_archNorm_cpow_mul_latticeTheta_sub_one hD I hs)
  have hconst : (mellinConstant K : ℂ) =
      (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
        ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ) := by
    rw [mellinConstant_eq_mul_surfaceHaar_real hD]
    push_cast
    rfl
  have hV : ((ZLattice.covolume (idealLattice K I) : ℂ) ^ 2) ^ (s / 2) =
      (ZLattice.covolume (idealLattice K I) : ℂ) ^ s := by
    rw [ofReal_pow_cpow (ZLattice.covolume_pos (idealLattice K I) volume).le]
    congr 1
    push_cast
    ring
  rw [← hconst] at hm2
  rw [completedPartialZeta_eq_mellinKernelFEPair hD I h0 h1, ← hm1.2, hm2.2, hV]

/-- **Hecke's Mellin representation as `HasMellin`**, Neukirch VII (5.5): on `Re s > 1` and for
every unit fundamental domain `D`, `mellinKernel D (idealLattice K I) - mellinConstant K` has
convergent Mellin transform `completedPartialZeta I s` at `s / 2`. -/
theorem hasMellin_mellinKernel_sub_completedPartialZeta {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K) (s / 2)
      (completedPartialZeta I s) := by
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hs2 : (1 / 2 : ℝ) < (s / 2).re := by rw [div_ofNat_re]; linarith
  rw [completedPartialZeta_eq_mellinKernelFEPair hD I h0 h1]
  exact hasMellin_mellinKernel_sub_mellinConstant hD (idealLattice K I) hs2

/-- **Hecke's Mellin representation**, Neukirch VII (5.5): on `Re s > 1` and for every unit
fundamental domain `D`, `completedPartialZeta I s` is the Mellin transform of
`mellinKernel D (idealLattice K I) - mellinConstant K` evaluated at `s / 2`. -/
theorem completedPartialZeta_eq_mellin {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta I s =
      mellin (fun u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K) (s / 2) :=
  (hasMellin_mellinKernel_sub_completedPartialZeta hD I hs).2.symm

/-! ### Regularity, poles, residues, and the functional equation -/

/-- `completedPartialZeta I` has a simple pole at `s = 0`. -/
@[simp]
theorem meromorphicOrderAt_completedPartialZeta_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    meromorphicOrderAt (completedPartialZeta I) 0 = (-1 : ℤ) := by
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  rw [meromorphicOrderAt_congr (completedPartialZeta_eventuallyEq_mellinKernelFEPair hD I 0),
    meromorphicOrderAt_eq_int_iff (meromorphic_mellinKernelFEPair_div_two hD I 0)]
  have hpole := (mellinKernelFEPair hD (idealLattice K I)).meromorphicOrderAt_Λ_zero
    (by simp [ofReal_ne_zero.mpr (mellinConstant_ne_zero K)])
  obtain ⟨g, hga, hg0, hgev⟩ := (meromorphicOrderAt_eq_int_iff
    ((mellinKernelFEPair hD (idealLattice K I)).meromorphic_Λ 0)).mp hpole
  have hmap : Tendsto (fun z : ℂ ↦ z / 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
    simpa only [zero_div] using tendsto_div_two_nhdsNE 0
  refine ⟨fun z ↦ 2 * g (z / 2), analyticAt_const.mul
    (hga.comp_of_eq (analyticAt_div_two 0) (by simp)),
    mul_ne_zero two_ne_zero (by simpa using hg0), ?_⟩
  filter_upwards [hmap.eventually hgev] with z hz
  simp only [sub_zero, zpow_neg_one, smul_eq_mul] at hz ⊢
  rw [hz]
  ring

/-- `completedPartialZeta I` has a simple pole at `s = 1`. -/
@[simp]
theorem meromorphicOrderAt_completedPartialZeta_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    meromorphicOrderAt (completedPartialZeta I) 1 = (-1 : ℤ) := by
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  rw [meromorphicOrderAt_congr (completedPartialZeta_eventuallyEq_mellinKernelFEPair hD I 1),
    meromorphicOrderAt_eq_int_iff (meromorphic_mellinKernelFEPair_div_two hD I 1)]
  have hpole := (mellinKernelFEPair hD (idealLattice K I)).meromorphicOrderAt_Λ_k
    (by simp [ofReal_ne_zero.mpr (mellinConstant_ne_zero K)])
  simp only [mellinKernelFEPair_k, ofReal_div, ofReal_one, ofReal_ofNat] at hpole
  obtain ⟨g, hga, hg0, hgev⟩ := (meromorphicOrderAt_eq_int_iff
    ((mellinKernelFEPair hD (idealLattice K I)).meromorphic_Λ (1 / 2))).mp hpole
  have hmap := tendsto_div_two_nhdsNE 1
  refine ⟨fun z ↦ 2 * g (z / 2), analyticAt_const.mul (hga.comp_of_eq (analyticAt_div_two 1) rfl),
    mul_ne_zero two_ne_zero hg0, ?_⟩
  filter_upwards [hmap.eventually hgev] with z hz
  simp only [zpow_neg_one, smul_eq_mul] at hz ⊢
  rw [hz]
  have hdiv : (z / 2 - 1 / 2)⁻¹ = (z - 1)⁻¹ * 2 := by
    have : z / 2 - 1 / 2 = (z - 1) / 2 := by ring
    rw [this, inv_div, div_eq_inv_mul, mul_comm]
  rw [hdiv]
  ring

/-- **Exact regularity of `completedPartialZeta`**: it is analytic everywhere except at `0` and `1`
(Neukirch VII (5.9)). -/
@[simp]
theorem analyticAt_completedPartialZeta_iff (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    AnalyticAt ℂ (completedPartialZeta I) s ↔ s ≠ 0 ∧ s ≠ 1 := by
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  constructor
  · intro hs
    refine ⟨?_, ?_⟩
    · rintro rfl
      have h := hs.meromorphicOrderAt_nonneg
      rw [meromorphicOrderAt_completedPartialZeta_zero] at h
      exact absurd h (by decide)
    · rintro rfl
      have h := hs.meromorphicOrderAt_nonneg
      rw [meromorphicOrderAt_completedPartialZeta_one] at h
      exact absurd h (by decide)
  · rintro ⟨h0, h1⟩
    have ha := (analyticAt_mellinKernelFEPair_div_two_iff hD I s).mpr ⟨h0, h1⟩
    rw [completedPartialZeta_eq_toMeromorphicNFOn hD I]
    have hev := toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds
      (meromorphic_mellinKernelFEPair_div_two hD I).meromorphicOn (mem_univ s)
    rw [toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt] at hev
    exact (analyticAt_congr hev).mpr ha

/-- `completedPartialZeta I` is analytic at every complex point off `0` and `1`. -/
theorem analyticAt_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) : AnalyticAt ℂ (completedPartialZeta I) s :=
  (analyticAt_completedPartialZeta_iff I s).mpr ⟨h0, h1⟩

/-- **Residue of `completedPartialZeta` at `s = 1`**, Neukirch VII (5.9): the residue is
`2 * mellinConstant K = 2 ^ (r₁ + r₂) R / w`, independent of the ideal class. -/
theorem tendsto_sub_one_mul_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun s : ℂ ↦ (s - 1) * completedPartialZeta I s) (𝓝[≠] 1)
      (𝓝 (2 * mellinConstant K : ℂ)) := by
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  have hres := (mellinKernelFEPair hD (idealLattice K I)).Λ_residue_k
  simp only [mellinKernelFEPair_k, mellinKernelFEPair_ε, mellinKernelFEPair_N,
    mellinKernelFEPair_g₀, ofReal_div, ofReal_one, ofReal_ofNat, one_cpow, mul_one, one_mul,
    smul_eq_mul] at hres
  have h2 := (hres.comp (tendsto_div_two_nhdsNE 1)).const_mul (2 : ℂ)
  refine h2.congr' ?_
  filter_upwards [completedPartialZeta_eventuallyEq_mellinKernelFEPair hD I 1] with s hs
  simp only [Function.comp_apply, hs]
  ring

/-- **Residue of `completedPartialZeta` at `s = 0`**, Neukirch VII (5.9): the residue is
`-(2 * mellinConstant K) = -2 ^ (r₁ + r₂) R / w`, independent of the ideal class. -/
theorem tendsto_mul_completedPartialZeta_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun s : ℂ ↦ s * completedPartialZeta I s) (𝓝[≠] 0)
      (𝓝 (-(2 * mellinConstant K : ℂ))) := by
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  have hres := (mellinKernelFEPair hD (idealLattice K I)).Λ_residue_zero
  simp only [mellinKernelFEPair_f₀, smul_eq_mul] at hres
  have hmap : Tendsto (fun z : ℂ ↦ z / 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
    simpa only [zero_div] using tendsto_div_two_nhdsNE 0
  have h2 : Tendsto (fun s : ℂ ↦ (2 : ℂ) * ((s / 2) *
      (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2))) (𝓝[≠] 0)
      (𝓝 ((2 : ℂ) * -(mellinConstant K : ℂ))) := (hres.comp hmap).const_mul 2
  rw [show (2 : ℂ) * -(mellinConstant K : ℂ) = -(2 * mellinConstant K : ℂ) by ring] at h2
  refine h2.congr' ?_
  filter_upwards [completedPartialZeta_eventuallyEq_mellinKernelFEPair hD I 0] with s hs
  simp only [hs]
  ring

/-- **The functional equation of `completedPartialZeta` on punctured germs**, Neukirch VII (5.9):
for `J = FractionalIdeal.dual ℤ ℚ I` (for instance `Units.mk0 (FractionalIdeal.dual ℤ ℚ I)
(FractionalIdeal.dual_ne_zero ℤ ℚ I.ne_zero)`), `z ↦ completedPartialZeta I (1 - z)` and
`completedPartialZeta J` have the same punctured germ at every `s : ℂ`. -/
theorem completedPartialZeta_one_sub_eventuallyEq {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)) (s : ℂ) :
    (fun z ↦ completedPartialZeta I (1 - z)) =ᶠ[𝓝[≠] s] completedPartialZeta J := by
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  -- Identify the dual Mellin pair's `Λ` with `(mellinKernelFEPair hD (idealLattice K J)).Λ`.
  have hΛ_dual : (mellinKernelFEPair hD.inv (mixedDual K (idealLattice K I))).Λ =
      (mellinKernelFEPair hD (idealLattice K J)).Λ := by
    rw [← FEPairWithLevel.toWeakFEPair_Λ, ← FEPairWithLevel.toWeakFEPair_Λ]
    refine WeakFEPair.Λ_congr (fun u (hu : 0 < u) ↦ ?_) (by simp) (by simp) (by simp) (by simp)
    simp only [FEPairWithLevel.toWeakFEPair_f, mellinKernelFEPair_f,
      indicator_of_mem (mem_Ioi.mpr hu)]
    rw [mellinKernel_mixedDual_idealLattice hJ,
      mellinKernel_idealLattice_eq (hD.inv.mul traceShift_mem_normOneSurface) hD J u]
  have hmap1 : Tendsto (fun z : ℂ ↦ (1 : ℂ) - z) (𝓝[≠] s) (𝓝[≠] ((1 : ℂ) - s)) := by
    refine tendsto_nhdsWithin_iff.mpr
      ⟨((continuous_const.sub (continuous_id' : Continuous fun z : ℂ ↦ z)).tendsto s).mono_left
        nhdsWithin_le_nhds, ?_⟩
    refine eventually_nhdsWithin_of_forall fun z (hz : z ≠ s) ↦ Set.mem_compl_singleton_iff.mpr ?_
    exact fun h ↦ hz (sub_right_injective h)
  have hmap2 : Tendsto (fun z : ℂ ↦ ((1 : ℂ) - z) / 2) (𝓝[≠] s) (𝓝[≠] (((1 : ℂ) - s) / 2)) :=
    (tendsto_div_two_nhdsNE ((1 : ℂ) - s)).comp hmap1
  have hevI := hmap1.eventually (completedPartialZeta_eventuallyEq_mellinKernelFEPair hD I (1 - s))
  have hevFE := hmap2.eventually
    (mellinKernelFEPair_Λ_eventuallyEq hD (idealLattice K I) ((1 - s) / 2))
  have hevJ := completedPartialZeta_eventuallyEq_mellinKernelFEPair hD J s
  filter_upwards [hevI, hevFE, hevJ] with z hzI hzFE hzJ
  have harg : (1 : ℂ) / 2 - (1 - z) / 2 = z / 2 := by ring
  rw [hzI, hzFE, harg, hΛ_dual, hzJ]

/-- **The functional equation of `completedPartialZeta`**, Neukirch VII (5.9): for
`J = FractionalIdeal.dual ℤ ℚ I = (I 𝔡)⁻¹`,
`completedPartialZeta I (1 - s) = completedPartialZeta J s` for every `s : ℂ`. Off the poles `0`
and `1` both sides are analytic and agree by continuity; at `0` and `1` both sides take the
canonical normal-form value `0` because `s ↦ 1 - s` swaps the two simple poles. -/
theorem completedPartialZeta_one_sub {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)) (s : ℂ) :
    completedPartialZeta I (1 - s) = completedPartialZeta J s := by
  have hpole_zero {I₀ : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {w : ℂ}
      (hw : ¬ AnalyticAt ℂ (completedPartialZeta I₀) w) :
      completedPartialZeta I₀ w = 0 := by
    have hnf := meromorphicNFOn_completedPartialZeta I₀ (mem_univ w)
    rcases meromorphicNFAt_iff_analyticAt_or.mp hnf with ha | ⟨-, -, h0⟩
    · exact absurd ha hw
    · exact h0
  by_cases hs0 : s = 0
  · subst hs0
    have hI1 : ¬ AnalyticAt ℂ (completedPartialZeta I) 1 := by simp
    have hJ0 : ¬ AnalyticAt ℂ (completedPartialZeta J) 0 := by simp
    rw [sub_zero, hpole_zero hI1, hpole_zero hJ0]
  · by_cases hs1 : s = 1
    · subst hs1
      have hI0 : ¬ AnalyticAt ℂ (completedPartialZeta I) 0 := by simp
      have hJ1 : ¬ AnalyticAt ℂ (completedPartialZeta J) 1 := by simp
      rw [sub_self, hpole_zero hI0, hpole_zero hJ1]
    · have haL : AnalyticAt ℂ (fun z ↦ completedPartialZeta I (1 - z)) s :=
        (analyticAt_completedPartialZeta I (sub_ne_zero.mpr (Ne.symm hs1))
          (fun h ↦ hs0 (sub_eq_self.mp h))).comp_of_eq
          (analyticAt_const.sub (analyticAt_id (𝕜 := ℂ))) rfl
      have haR : AnalyticAt ℂ (completedPartialZeta J) s :=
        analyticAt_completedPartialZeta J hs0 hs1
      exact ((haL.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE haR.continuousAt).mp
        (completedPartialZeta_one_sub_eventuallyEq hJ s)).eq_of_nhds

end TauCeti.LFunctions
