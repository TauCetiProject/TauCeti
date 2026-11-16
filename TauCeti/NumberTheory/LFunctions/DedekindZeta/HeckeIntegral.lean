/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import TauCeti.Analysis.Meromorphic.Continuation
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.UnitQuotient
public import TauCeti.NumberTheory.LFunctions.Theta.Mellin.Pair
public import TauCeti.NumberTheory.LFunctions.Theta.UnitCone
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import TauCeti.Analysis.Meromorphic.Order
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.NumberTheory.LFunctions.Theta.GammaIntegral
import TauCeti.NumberTheory.NumberField.Global.RayClass.Basic

/-!
# Hecke's integral representation and completed partial zeta functions

For an invertible fractional ideal `I` of a number field `K`, the lattice `σ(I)` in the mixed
space is invariant under multiplication by units of `𝓞 K`. Integrating its theta series minus `1`
against `N(y)^(s/2) dy / y` over the cone `unitCone D` above a unit fundamental domain `D` unfolds
the sum over nonzero lattice points: the unit translates modulo torsion of `unitCone D` partition
the positive orthant, while the points of `σ(I)` in Mathlib's fundamental cone represent the unit
orbits modulo torsion. Each orbit contributes a single full archimedean gamma integral
`Γ_ℝ(s)^r₁ Γ_ℝ(2s)^r₂ |N(x)|^(-s)`.

Scaling `I` by a positive integer denominator reduces the sum over the fundamental cone to the
integral-ideal identity `hasSum_norm_cpow_idealSet`, identifying the cone integral with the
partial zeta function of the ideal class of `I⁻¹`. Together with `hasMellin_mellinKernel_sub` and
the covolume formula `covolume_idealLattice`, this identifies the Mellin transform of
`mellinKernel D (idealLattice K I) - mellinConstant K` at `s / 2` with the completed partial zeta
function

`Z(I, s) = |d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ∑_{𝔟 ∈ [I]⁻¹} N(𝔟)^(-s)`

on `Re s > 1`. The Mellin principle (`mellinKernelFEPair`) then supplies the meromorphic
continuation to `ℂ`, simple poles at `0` and `1` with residues `-(2 a₀)` and `2 a₀` (where
`a₀ = mellinConstant K = 2^(r₁+r₂-1) R / w`), and Hecke's functional equation
`Z(I, 1 - s) = Z(I^∨, s)` against the trace dual `I^∨ = FractionalIdeal.dual ℤ ℚ I`.

## Main definitions

* `TauCeti.LFunctions.completedPartialZeta`: the completed partial zeta function of the ideal class
  of `I⁻¹`, in meromorphic normal form on `ℂ`.

## Main results

* `TauCeti.LFunctions.summable_integral_unitCone`: absolute convergence justifying the interchange
  of summation over nonzero lattice points and integration over `unitCone D`.
* `TauCeti.LFunctions.integrableOn_archNorm_cpow_mul_latticeTheta_sub_one_unitCone`: integrability
  of the norm-weighted theta series minus `1` on `unitCone D` for `Re s > 1`.
* `TauCeti.LFunctions.integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one`: the unfolded
  unit-cone integral as a sum over the fundamental cone.
* `TauCeti.LFunctions.completedPartialZeta_eq_tsum`,
  `TauCeti.LFunctions.completedPartialZeta_eq_tsum_fundamentalCone`,
  `TauCeti.LFunctions.completedPartialZeta_eq_LSeries_rayClassCoeff`: Dirichlet-series and
  fundamental-cone representations on `Re s > 1`.
* `TauCeti.LFunctions.completedPartialZeta_eq_integral_unitCone`,
  `TauCeti.LFunctions.hasMellin_mellinKernel_sub_completedPartialZeta`,
  `TauCeti.LFunctions.completedPartialZeta_eq_mellin`: Hecke's unit-cone and Mellin representations
  on `Re s > 1`.
* `TauCeti.LFunctions.analyticAt_completedPartialZeta`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedPartialZeta_zero`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedPartialZeta_one`,
  `TauCeti.LFunctions.tendsto_mul_completedPartialZeta_zero`,
  `TauCeti.LFunctions.tendsto_sub_one_mul_completedPartialZeta`: regularity, simple poles and
  residues.
* `TauCeti.LFunctions.completedPartialZeta_one_sub`,
  `TauCeti.LFunctions.completedPartialZeta_one_sub_eventuallyEq`: the functional equation against
  the trace dual.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.3)–(5.9).
-/

public section
noncomputable section

open Complex Filter MeasureTheory NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone NumberField.Units Set
  TauCeti.GlobalNumberFields TauCeti.NumberField.mixedEmbedding
open scoped ENNReal nonZeroDivisors Pointwise Real Topology

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### Auxiliary lemmas on fractional ideals and the fundamental cone -/

/-- The quotient of the unit group by the roots of unity is countable. -/
private theorem countable_units_quotient_torsion :
    Countable ((𝓞 K)ˣ ⧸ torsion K) := by
  have : Countable (𝓞 K) := Countable.of_moduleFinite (R := ℤ)
  have : Countable (𝓞 K)ˣ := Units.val_injective.countable
  exact Quotient.countable

/-- Every nonzero point of an ideal lattice has nonzero mixed norm. -/
private theorem norm_ne_zero_of_mem_idealLattice {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {x : idealLattice K I} (hx : x ≠ 0) :
    mixedEmbedding.norm (x : mixedSpace K) ≠ 0 := by
  obtain ⟨a, _, ha⟩ := (mem_idealLattice K I).mp x.2
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hx
    exact Subtype.ext (by rw [← ha, map_zero]; rfl)
  rw [← ha, mixedEmbedding.norm_eq_norm]
  exact Rat.cast_ne_zero.mpr (abs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr ha0))

/-- Every invertible fractional ideal can be cleared to a nonzero integral ideal by multiplying by
a positive integer. -/
private theorem exists_nat_pos_mul_eq_coeIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ (d : ℕ) (J : (Ideal (𝓞 K))⁰), 0 < d ∧
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (d : K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
        (J : Ideal (𝓞 K)) := by
  obtain ⟨a, ha0, ha⟩ := I.1.2
  have ha_ne : a ≠ 0 := nonZeroDivisors.ne_zero ha0
  set d := Ideal.absNorm (Ideal.span {a})
  have hd : 0 < d := Ideal.absNorm_pos_of_nonZeroDivisors
    ⟨Ideal.span {a}, mem_nonZeroDivisors_of_ne_zero (Ideal.span_singleton_eq_bot.not.mpr ha_ne)⟩
  have hda : (d : 𝓞 K) ∈ Ideal.span {a} := Ideal.absNorm_mem _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hda
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ (d : K) * (I : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 := by
    intro y hy
    rw [FractionalIdeal.mem_singleton_mul] at hy
    obtain ⟨x, hxI, rfl⟩ := hy
    obtain ⟨b, hb⟩ := ha x hxI
    refine (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mpr ⟨c * b, ?_⟩
    have hcK : (d : K) = (a : K) * (c : K) := by
      exact_mod_cast hc
    have hbK : (a : K) * x = (b : K) := hb.symm
    calc algebraMap (𝓞 K) K (c * b) = (c : K) * (b : K) := map_mul _ _ _
      _ = (c : K) * ((a : K) * x) := by rw [hbK]
      _ = ((a : K) * (c : K)) * x := by ring
      _ = (d : K) * x := by rw [← hcK]
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hJ0 : J ≠ ⊥ := by
    intro hbot
    have hmul0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (d : K) *
        (I : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
      rw [← hJ, hbot, FractionalIdeal.coeIdeal_bot]
    rcases mul_eq_zero.mp hmul0 with h1 | h2
    · exact Nat.cast_ne_zero.mpr hd.ne' (FractionalIdeal.spanSingleton_eq_zero_iff.mp h1)
    · exact I.ne_zero h2
  exact ⟨d, ⟨J, mem_nonZeroDivisors_of_ne_zero hJ0⟩, hd, hJ.symm⟩

/-- Scaling a nonzero fractional ideal by a positive integer scales its absolute norm by
`d^[K:ℚ]`. -/
private theorem absNorm_coeIdeal_eq_pow_mul {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {d : ℕ} (hd : 0 < d)
    {J : (Ideal (𝓞 K))⁰}
    (hJ : FractionalIdeal.spanSingleton (𝓞 K)⁰ (d : K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
      (J : Ideal (𝓞 K))) :
    (Ideal.absNorm (J : Ideal (𝓞 K)) : ℚ) =
      (d : ℚ) ^ Module.finrank ℚ K * FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) := by
  have h := congrArg (FractionalIdeal.absNorm (R := 𝓞 K) (K := K)) hJ
  have hd_cast : algebraMap ℚ K (d : ℚ) = (d : K) := by simp
  rw [map_mul, FractionalIdeal.coeIdeal_absNorm, FractionalIdeal.absNorm_span_singleton,
    ← hd_cast, Algebra.norm_algebraMap] at h
  have hpos : (0 : ℚ) ≤ (d : ℚ) ^ Module.finrank ℚ K := by positivity
  rw [abs_of_nonneg hpos] at h
  exact h.symm

/-- For `J = d * I` with `d > 0`, multiplying by `d` gives a bijection between the nonzero points
of `σ(I)` in the fundamental cone and `idealSet K J`. -/
private def conePtsEquivIdealSet {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {d : ℕ} (hd : 0 < d)
    {J : (Ideal (𝓞 K))⁰}
    (hJ : FractionalIdeal.spanSingleton (𝓞 K)⁰ (d : K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
      (J : Ideal (𝓞 K))) :
    {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K} ≃ idealSet K J := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hsmul (a : K) : (d : ℝ) • mixedEmbedding K a = mixedEmbedding K ((d : K) * a) := by
    rw [map_mul, map_natCast]
    exact Prod.ext (funext fun w ↦ by simp) (funext fun w ↦ by simp)
  have hmem (z : mixedSpace K) :
      z ∈ idealLattice K I ↔ (d : ℝ) • z ∈ idealLattice K (FractionalIdeal.mk0 K J) := by
    rw [mem_idealLattice, mem_idealLattice]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨(d : K) * a, ?_, (hsmul a).symm⟩
      rw [SetLike.mem_coe, FractionalIdeal.coe_mk0, ← hJ]
      exact FractionalIdeal.mem_singleton_mul.mpr ⟨a, ha, rfl⟩
    · rintro ⟨b, hb, hbz⟩
      rw [SetLike.mem_coe, FractionalIdeal.coe_mk0, ← hJ,
        FractionalIdeal.mem_singleton_mul] at hb
      obtain ⟨a, ha, rfl⟩ := hb
      refine ⟨a, ha, ?_⟩
      exact smul_right_injective (mixedSpace K) hdR (by dsimp only; rw [hsmul, hbz])
  refine
    { toFun := fun x ↦ ⟨(d : ℝ) • (x : mixedSpace K),
        ⟨fundamentalCone.smul_mem_of_mem x.2.2 hdR, (hmem x.1.1).mp x.1.2⟩⟩
      invFun := fun y ↦
        ⟨⟨(d : ℝ)⁻¹ • (y : mixedSpace K), (hmem _).mpr (by simpa [hdR] using y.2.2)⟩,
          ⟨fun h0 ↦ by
            have hy0 : (y : mixedSpace K) = 0 := by
              have h1 : (d : ℝ)⁻¹ • (y : mixedSpace K) = 0 := congrArg Subtype.val h0
              simpa [hdR] using congrArg ((d : ℝ) • ·) h1
            exact fundamentalCone.norm_pos_of_mem y.2.1 |>.ne' (by simp [hy0]),
          fundamentalCone.smul_mem_of_mem y.2.1 (inv_ne_zero hdR)⟩⟩
      left_inv := fun x ↦ Subtype.ext (Subtype.ext (by simp [hdR]))
      right_inv := fun y ↦ Subtype.ext (by simp [hdR]) }

/-- The bijection `conePtsEquivIdealSet` scales norms by `d ^ [K : ℚ]`. -/
private theorem norm_conePtsEquivIdealSet {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {d : ℕ} (hd : 0 < d)
    {J : (Ideal (𝓞 K))⁰}
    (hJ : FractionalIdeal.spanSingleton (𝓞 K)⁰ (d : K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
      (J : Ideal (𝓞 K)))
    (x : {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K}) :
    mixedEmbedding.norm ((conePtsEquivIdealSet hd hJ x : idealSet K J) : mixedSpace K) =
      (d : ℝ) ^ Module.finrank ℚ K * mixedEmbedding.norm (x : mixedSpace K) := by
  simp only [conePtsEquivIdealSet, Equiv.coe_fn_mk]
  rw [mixedEmbedding.norm_smul, abs_of_pos (Nat.cast_pos.mpr hd)]

/-- If `J = d * I` with `d > 0`, then `J` and `I` have the same class in `ClassGroup (𝓞 K)`. -/
private theorem classGroup_mk0_eq_mk_of_mul {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {d : ℕ} (hd : 0 < d)
    {J : (Ideal (𝓞 K))⁰}
    (hJ : FractionalIdeal.spanSingleton (𝓞 K)⁰ (d : K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
      (J : Ideal (𝓞 K))) :
    ClassGroup.mk0 J = ClassGroup.mk K I := by
  have hdK : (d : K) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  let u : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
    Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ (d : K))
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hdK)
  have huJ : u * I = FractionalIdeal.mk0 K J := Units.ext (by
    simpa [u, FractionalIdeal.coe_mk0] using hJ)
  have hu1 : ClassGroup.mk K u = 1 := ClassGroup.mk_eq_one_iff.mpr
    ⟨(d : K), by simp [u, FractionalIdeal.coeToSubmodule_spanSingleton]⟩
  rw [← ClassGroup.mk_mk0 K J, ← huJ, map_mul, hu1, one_mul]

/-- A nonzero integral ideal `𝔟` satisfies `ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹` if and only
if `𝔟 * J` is principal, where `J = d * I` with `d > 0`. -/
private theorem classGroup_mk0_eq_inv_iff_isPrincipal_mul {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {d : ℕ} (hd : 0 < d) {J : (Ideal (𝓞 K))⁰}
    (hJ : FractionalIdeal.spanSingleton (𝓞 K)⁰ (d : K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
      (J : Ideal (𝓞 K)))
    (𝔟 : (Ideal (𝓞 K))⁰) :
    ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹ ↔
      ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K))).IsPrincipal := by
  rw [← classGroup_mk0_eq_mk_of_mul hd hJ, eq_inv_iff_mul_eq_one, ← map_mul,
    ClassGroup.mk0_eq_one_iff]
  rfl

/-- **Sum over the fundamental cone for an arbitrary fractional ideal.** For `Re s > 1`, the sum of
`|N(x)|^(-s)` over the nonzero points of `σ(I)` in Mathlib's fundamental cone equals
`w · N(I)^(-s)` times the sum of `N(𝔟)^(-s)` over the nonzero integral ideals `𝔟` in the class of
`I⁻¹`. -/
theorem hasSum_norm_cpow_idealLattice_fundamentalCone (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum
      (fun x : {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K} ↦
        ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-s))
      ((torsionOrder K : ℂ) *
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s) *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by
  obtain ⟨d, J, hd, hJ⟩ := exists_nat_pos_mul_eq_coeIdeal I
  have hdpos : (0 : ℝ) < (d : ℝ) ^ Module.finrank ℚ K := by positivity
  have hdC : (((d : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h ↦ hdpos.ne' (Complex.ofReal_eq_zero.mp h.1)
  have hnormJ : (Ideal.absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s) =
      (((d : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s) *
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s) := by
    have hq : ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) : ℂ) =
        ((((d : ℝ) ^ Module.finrank ℚ K) *
          (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℝ) : ℂ) := by
      have h := absNorm_coeIdeal_eq_pow_mul hd hJ
      exact_mod_cast h
    rw [← Complex.ofReal_natCast, hq, Complex.ofReal_mul,
      TauCeti.ofReal_mul_cpow hdpos.le, Complex.ofReal_ratCast]
  have hsumJ := (conePtsEquivIdealSet hd hJ).hasSum_iff.mpr (hasSum_norm_cpow_idealSet J hs)
  let hsubEquiv :
      {𝔟 : (Ideal (𝓞 K))⁰ // ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K))).IsPrincipal} ≃
        {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹} :=
    Equiv.subtypeEquivRight fun 𝔟 ↦ (classGroup_mk0_eq_inv_iff_isPrincipal_mul hd hJ 𝔟).symm
  have htsum_eq :
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K))).IsPrincipal},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) =
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
    simpa [hsubEquiv] using
      hsubEquiv.tsum_eq fun 𝔟 ↦ (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)
  have hmul := hsumJ.mul_left ((((d : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s))⁻¹
  refine (hmul.congr_fun fun x ↦ ?_).trans_eq ?_
  · simp only [Function.comp_apply, norm_conePtsEquivIdealSet hd hJ x, Complex.ofReal_mul,
      TauCeti.ofReal_mul_cpow hdpos.le, inv_mul_cancel_left₀ hdC]
  · rw [hnormJ, htsum_eq]
    field_simp [hdC]

/-! ### Orbit decomposition and unit-cone unfolding -/

/-- A fixed section of the quotient `(𝓞 K)ˣ → (𝓞 K)ˣ ⧸ torsion K`. -/
private def unitSection (g : (𝓞 K)ˣ ⧸ torsion K) : (𝓞 K)ˣ :=
  Function.surjInv QuotientGroup.mk_surjective g

omit [NumberField K] in
private theorem mk_unitSection (g : (𝓞 K)ˣ ⧸ torsion K) :
    (unitSection g : (𝓞 K)ˣ ⧸ torsion K) = g :=
  Function.surjInv_eq QuotientGroup.mk_surjective g

omit [NumberField K] in
private theorem unitSMulIdealLatticeEquiv_ne_zero (u : (𝓞 K)ˣ)
    {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x : idealLattice K I} (hx : x ≠ 0) :
    u.unitSMulIdealLatticeEquiv I x ≠ 0 := fun h0 ↦ hx <| by
  have h1 : u • (x : mixedSpace K) = 0 :=
    (Units.unitSMulIdealLatticeEquiv_apply _ _ _).symm.trans (congrArg Subtype.val h0)
  have h2 := congrArg (u⁻¹ • ·) h1
  rw [inv_smul_smul, smul_zero] at h2
  exact Subtype.ext h2

/-- Nonzero points of an ideal lattice split as unit-modulo-torsion translates of its points in
the fundamental cone. -/
private def idealLatticeOrbitEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((𝓞 K)ˣ ⧸ torsion K) ×
      {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K} ≃
      {x : idealLattice K I // x ≠ 0} := by
  refine Equiv.ofBijective
    (fun p ↦ ⟨(unitSection p.1).unitSMulIdealLatticeEquiv I p.2.1,
      unitSMulIdealLatticeEquiv_ne_zero _ p.2.2.1⟩)
    ⟨?_, ?_⟩
  · rintro ⟨g₁, x₁⟩ ⟨g₂, x₂⟩ h
    have hval :
        unitSection g₁ • (x₁.1 : mixedSpace K) = unitSection g₂ • (x₂.1 : mixedSpace K) := by
      have h' := congrArg (fun z : {x : idealLattice K I // x ≠ 0} ↦ (z.1 : mixedSpace K)) h
      simpa only [Units.unitSMulIdealLatticeEquiv_apply] using h'
    have hmem : ((unitSection g₂)⁻¹ * unitSection g₁) • (x₁.1 : mixedSpace K) ∈
        fundamentalCone K := by
      rw [mul_smul, hval, inv_smul_smul]
      exact x₂.2.2
    have htor : (unitSection g₂)⁻¹ * unitSection g₁ ∈ torsion K :=
      (fundamentalCone.unit_smul_mem_iff_mem_torsion x₁.2.2 _).mp hmem
    have hg : g₁ = g₂ := by
      rw [← mk_unitSection g₁, ← mk_unitSection g₂]
      exact (QuotientGroup.eq.mpr htor).symm
    subst hg
    have hx : (x₁.1 : mixedSpace K) = (x₂.1 : mixedSpace K) := by
      have h' := congrArg ((unitSection g₁)⁻¹ • ·) hval
      rw [inv_smul_smul, inv_smul_smul] at h'
      exact h'
    exact Prod.ext rfl (Subtype.ext (Subtype.ext hx))
  · intro z
    obtain ⟨u, hu⟩ := fundamentalCone.exists_unit_smul_mem (norm_ne_zero_of_mem_idealLattice z.2)
    set g : (𝓞 K)ˣ ⧸ torsion K := QuotientGroup.mk u⁻¹
    have htor : u * unitSection g ∈ torsion K := by
      have hmk : (u⁻¹ : (𝓞 K)ˣ ⧸ torsion K) = (unitSection g : (𝓞 K)ˣ ⧸ torsion K) :=
        (mk_unitSection g).symm
      simpa using QuotientGroup.eq.mp hmk
    have htor' : (u * unitSection g)⁻¹ ∈ torsion K := (torsion K).inv_mem htor
    set x : idealLattice K I := (unitSection g)⁻¹.unitSMulIdealLatticeEquiv I z.1
    have hx_cone : (x : mixedSpace K) ∈ fundamentalCone K := by
      have heq : (x : mixedSpace K) = (u * unitSection g)⁻¹ • (u • (z.1 : mixedSpace K)) := by
        rw [Units.unitSMulIdealLatticeEquiv_apply, mul_inv_rev, mul_smul, inv_smul_smul]
      rw [heq]
      exact fundamentalCone.torsion_smul_mem_of_mem hu htor'
    refine ⟨(g, ⟨x, unitSMulIdealLatticeEquiv_ne_zero _ z.2, hx_cone⟩),
      Subtype.ext (Subtype.ext ?_)⟩
    rw [Units.unitSMulIdealLatticeEquiv_apply]
    dsimp only
    rw [Units.unitSMulIdealLatticeEquiv_apply, smul_inv_smul]

private theorem idealLatticeOrbitEquiv_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (g : (𝓞 K)ˣ ⧸ torsion K)
    (x : {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K}) :
    (((idealLatticeOrbitEquiv I (g, x)).1 : idealLattice K I) : mixedSpace K) =
      unitSection g • (x.1 : mixedSpace K) :=
  Units.unitSMulIdealLatticeEquiv_apply _ _ _

omit [NumberField K] in
/-- `unitScale u` is continuous on `realSpace K`. -/
private theorem continuous_unitScale (u : (𝓞 K)ˣ) : Continuous (unitScale u) :=
  continuous_pi fun w ↦ by
    simp_rw [unitScale_apply]
    exact Continuous.mul (f := fun _ : realSpace K ↦ w (algebraMap (𝓞 K) K u) ^ 2)
      (g := fun y : realSpace K ↦ y w) continuous_const (continuous_apply w)

/-- `unitScale u` is a measurable embedding of `realSpace K`. -/
private theorem measurableEmbedding_unitScale (u : (𝓞 K)ˣ) :
    MeasurableEmbedding (unitScale u) :=
  ⟨fun _ _ h ↦ by
      have h' := congrArg (unitScale u⁻¹) h
      simpa [unitScale_unitScale] using h',
    (continuous_unitScale u).measurable,
    fun s hs ↦ by
      have himg : unitScale u '' s = unitScale u⁻¹ ⁻¹' s := by
        ext y
        exact ⟨by rintro ⟨x, hx, rfl⟩; simpa [unitScale_unitScale] using hx,
          fun hy ↦ ⟨unitScale u⁻¹ y, hy, by simp [unitScale_unitScale]⟩⟩
      rw [himg]
      exact hs.preimage (continuous_unitScale u⁻¹).measurable⟩

/-- `unitScale u` preserves `archHaar K`. -/
private theorem measurePreserving_unitScale (u : (𝓞 K)ˣ) :
    MeasurePreserving (unitScale u) (archHaar K) (archHaar K) := by
  refine ⟨(continuous_unitScale u).measurable, ?_⟩
  let c : realSpace K := fun w ↦ w (algebraMap (𝓞 K) K u) ^ 2
  have hfun : unitScale u = (c * ·) := by
    ext y w
    exact unitScale_apply u y w
  rw [hfun]
  exact map_archHaar_mul_left (c := c) fun w ↦
    pow_pos (InfinitePlace.pos_iff.mpr (by simp [Units.ne_zero])) 2

/-- The unit-modulo-torsion translates of `unitCone D` are pairwise disjoint measurable sets
covering the positive orthant. -/
private theorem pairwise_disjoint_unitScale_preimage_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) :
    Pairwise fun g₁ g₂ : (𝓞 K)ˣ ⧸ torsion K ↦
      Disjoint (unitScale (unitSection g₁)⁻¹ ⁻¹' unitCone D)
        (unitScale (unitSection g₂)⁻¹ ⁻¹' unitCone D) := by
  intro g₁ g₂ hne
  rw [Set.disjoint_left]
  intro y hy₁ hy₂
  apply hne
  have h1 : surfacePart (unitScale (unitSection g₁)⁻¹ y) ∈ D := (mem_unitCone.mp hy₁).2
  have h2 : surfacePart (unitScale (unitSection g₂)⁻¹ y) ∈ D := (mem_unitCone.mp hy₂).2
  have hrel : unitScale ((unitSection g₂)⁻¹ * unitSection g₁)
      (surfacePart (unitScale (unitSection g₁)⁻¹ y)) ∈ D := by
    rwa [surfacePart_unitScale, unitScale_unitScale, mul_assoc, mul_inv_cancel, mul_one,
      ← surfacePart_unitScale]
  have htor := (hD.unitScale_mem_iff _ h1 _).mp hrel
  rw [← mk_unitSection g₁, ← mk_unitSection g₂]
  exact (QuotientGroup.eq.mpr htor).symm

private theorem iUnion_unitScale_preimage_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) :
    ⋃ g : (𝓞 K)ˣ ⧸ torsion K, unitScale (unitSection g)⁻¹ ⁻¹' unitCone D =
      {y : realSpace K | ∀ w, 0 < y w} := by
  ext y
  simp only [mem_iUnion, mem_preimage, mem_unitCone, mem_ofPred_eq]
  constructor
  · rintro ⟨g, hpos, _⟩ w
    have h := unitScale_pos (hpos w) (unitSection g)
    rwa [unitScale_unitScale, mul_inv_cancel, unitScale_one] at h
  · intro hy
    obtain ⟨u, hu⟩ := hD.exists_unitScale_mem _ (surfacePart_mem_normOneSurface hy)
    set g : (𝓞 K)ˣ ⧸ torsion K := QuotientGroup.mk u⁻¹
    have htor : u * unitSection g ∈ torsion K := by
      have hmk : (u⁻¹ : (𝓞 K)ˣ ⧸ torsion K) = (unitSection g : (𝓞 K)ˣ ⧸ torsion K) :=
        (mk_unitSection g).symm
      simpa using QuotientGroup.eq.mp hmk
    have htor' : (unitSection g)⁻¹ * u⁻¹ ∈ torsion K := by
      simpa [mul_inv_rev] using (torsion K).inv_mem htor
    refine ⟨g, fun w ↦ unitScale_pos (hy w) _, ?_⟩
    rw [surfacePart_unitScale]
    have hrel : unitScale (unitSection g)⁻¹ (surfacePart y) =
        unitScale ((unitSection g)⁻¹ * u⁻¹) (unitScale u (surfacePart y)) := by
      rw [unitScale_unitScale, mul_assoc, inv_mul_cancel, mul_one]
    rw [hrel]
    exact (hD.unitScale_mem_iff _ hu _).mpr htor'

private theorem iUnion_unitScale_preimage_unitCone_ae_univ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) :
    (⋃ g : (𝓞 K)ˣ ⧸ torsion K, unitScale (unitSection g)⁻¹ ⁻¹' unitCone D) =ᵐ[archHaar K]
      (univ : Set (realSpace K)) := by
  rw [iUnion_unitScale_preimage_unitCone hD]
  exact Filter.eventuallyEqSet_iff.mpr (ae_archHaar_pos.mono fun _ hy ↦ iff_of_true hy trivial)

/-- A nonnegative real family whose `ENNReal.ofReal` sum is finite is summable. -/
private theorem summable_of_tsum_ofReal_lt_top {α : Type*} {f : α → ℝ}
    (hf : ∀ a, 0 ≤ f a) (hlt : (∑' a, ENNReal.ofReal (f a)) < ⊤) : Summable f := by
  let g : α → NNReal := fun a ↦ ⟨f a, hf a⟩
  have hne : (∑' a, (g a : ℝ≥0∞)) ≠ ⊤ := by
    have heq : (fun a ↦ (g a : ℝ≥0∞)) = fun a ↦ ENNReal.ofReal (f a) :=
      funext fun a ↦ (ENNReal.ofReal_coe_nnreal (p := g a)).symm
    rw [heq]
    exact hlt.ne
  exact ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hne

/-- Unfolding a single unit orbit for the `ℝ≥0∞`-integral against `enorm`. -/
private theorem tsum_lintegral_unitCone_enorm {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (x : mixedSpace K) (s : ℂ) :
    ∑' g : (𝓞 K)ˣ ⧸ torsion K,
        ∫⁻ y in unitCone D,
          ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y (unitSection g • x)‖ₑ ∂archHaar K =
      ∫⁻ z, ‖(archNorm z : ℂ) ^ (s / 2) * archGaussian z x‖ₑ ∂archHaar K := by
  have : Countable ((𝓞 K)ˣ ⧸ torsion K) := countable_units_quotient_torsion
  have hterm (g : (𝓞 K)ˣ ⧸ torsion K) :
      ∫⁻ y in unitCone D,
          ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y (unitSection g • x)‖ₑ ∂archHaar K =
        ∫⁻ z in unitScale (unitSection g)⁻¹ ⁻¹' unitCone D,
          ‖(archNorm z : ℂ) ^ (s / 2) * archGaussian z x‖ₑ ∂archHaar K := by
    have hpre : unitScale (unitSection g) ⁻¹' (unitScale (unitSection g)⁻¹ ⁻¹' unitCone D) =
        unitCone D := by
      ext y
      simp [unitScale_unitScale]
    have hmp := measurePreserving_unitScale (unitSection g)
    have hemb := measurableEmbedding_unitScale (unitSection g)
    rw [← hmp.setLIntegral_comp_preimage_emb hemb _ (unitScale (unitSection g)⁻¹ ⁻¹' unitCone D),
      hpre]
    refine setLIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y _ ↦ ?_
    rw [archGaussian_unit_smul, archNorm_unitScale]
  simp_rw [hterm]
  rw [← lintegral_iUnion (fun g ↦ (measurableSet_unitCone hD.measurableSet).preimage
      (continuous_unitScale (unitSection g)⁻¹).measurable)
      (pairwise_disjoint_unitScale_preimage_unitCone hD),
    Measure.restrict_congr_set (iUnion_unitScale_preimage_unitCone_ae_univ hD),
    Measure.restrict_univ]

/-- Unfolding a single unit orbit for the complex Bochner integral. -/
private theorem tsum_integral_unitCone_orbit {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0)
    {s : ℂ} (hs : 0 < s.re) :
    ∑' g : (𝓞 K)ˣ ⧸ torsion K,
        ∫ y in unitCone D,
          (archNorm y : ℂ) ^ (s / 2) * archGaussian y (unitSection g • x) ∂archHaar K =
      Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
        (mixedEmbedding.norm x : ℂ) ^ (-s) := by
  have : Countable ((𝓞 K)ˣ ⧸ torsion K) := countable_units_quotient_torsion
  have hint : Integrable (fun z ↦ (archNorm z : ℂ) ^ (s / 2) * archGaussian z x) (archHaar K) := by
    simpa only [mul_comm] using integrable_archGaussian_mul_archNorm_cpow hx hs
  have hterm (g : (𝓞 K)ˣ ⧸ torsion K) :
      ∫ y in unitCone D,
          (archNorm y : ℂ) ^ (s / 2) * archGaussian y (unitSection g • x) ∂archHaar K =
        ∫ z in unitScale (unitSection g)⁻¹ ⁻¹' unitCone D,
          (archNorm z : ℂ) ^ (s / 2) * archGaussian z x ∂archHaar K := by
    have hpre : unitScale (unitSection g) ⁻¹' (unitScale (unitSection g)⁻¹ ⁻¹' unitCone D) =
        unitCone D := by
      ext y
      simp [unitScale_unitScale]
    have hmp := measurePreserving_unitScale (unitSection g)
    have hemb := measurableEmbedding_unitScale (unitSection g)
    rw [← hmp.setIntegral_preimage_emb hemb _ (unitScale (unitSection g)⁻¹ ⁻¹' unitCone D), hpre]
    refine setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y _ ↦ ?_
    rw [archGaussian_unit_smul, archNorm_unitScale]
  simp_rw [hterm]
  rw [← integral_iUnion (fun g ↦ (measurableSet_unitCone hD.measurableSet).preimage
        (continuous_unitScale (unitSection g)⁻¹).measurable)
      (pairwise_disjoint_unitScale_preimage_unitCone hD) hint.integrableOn,
    Measure.restrict_congr_set (iUnion_unitScale_preimage_unitCone_ae_univ hD),
    Measure.restrict_univ]
  simpa only [mul_comm] using integral_archGaussian_mul_archNorm_cpow hx hs

/-- On the positive orthant, the norm of `(archNorm y : ℂ) ^ (s / 2) * archGaussian y x` equals
the positive real value `((archNorm y : ℂ) ^ ((s.re : ℂ) / 2) * archGaussian y x).re`. -/
private theorem lintegral_enorm_eq_ofReal_integral {x : mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    ∫⁻ z, ‖(archNorm z : ℂ) ^ (s / 2) * archGaussian z x‖ₑ ∂archHaar K =
      ENNReal.ofReal
        ((Gammaℝ (s.re : ℂ) ^ nrRealPlaces K * Gammaℝ (2 * (s.re : ℂ)) ^ nrComplexPlaces K *
          (mixedEmbedding.norm x : ℂ) ^ (-(s.re : ℂ))).re) := by
  have hreal : ∀ᵐ z ∂archHaar K,
      ‖(archNorm z : ℂ) ^ (s / 2) * archGaussian z x‖ =
        ((archNorm z : ℂ) ^ ((s.re : ℂ) / 2) * archGaussian z x).re := by
    filter_upwards [ae_archHaar_pos] with z hz
    have hN : 0 < archNorm z := archNorm_pos hz
    have hpow : (archNorm z : ℂ) ^ ((s.re : ℂ) / 2) =
        ((archNorm z ^ (s.re / 2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hN.le]
      push_cast
      rfl
    have hnorm : ‖(archNorm z : ℂ) ^ (s / 2)‖ = archNorm z ^ (s.re / 2) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hN]
      simp
    rw [norm_mul, hnorm, hpow, archGaussian_apply, ← Complex.ofReal_mul, Complex.ofReal_re,
      Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
  have hint_re : Integrable (fun z ↦ (archNorm z : ℂ) ^ ((s.re : ℂ) / 2) * archGaussian z x)
      (archHaar K) := by
    simpa only [mul_comm] using
      integrable_archGaussian_mul_archNorm_cpow hx (by simpa using hs)
  have hre : ∫ z, ((archNorm z : ℂ) ^ ((s.re : ℂ) / 2) * archGaussian z x).re ∂archHaar K =
      (∫ z, (archNorm z : ℂ) ^ ((s.re : ℂ) / 2) * archGaussian z x ∂archHaar K).re := by
    simpa only [Complex.reCLM_apply] using Complex.reCLM.integral_comp_comm hint_re
  rw [← ofReal_integral_norm_eq_lintegral_eNorm
      (by simpa only [mul_comm] using integrable_archGaussian_mul_archNorm_cpow hx hs),
    integral_congr_ae hreal, hre]
  have hval := integral_archGaussian_mul_archNorm_cpow hx (s := (s.re : ℂ)) (by simpa using hs)
  simpa only [mul_comm] using congrArg (fun z : ℂ ↦ ENNReal.ofReal z.re) hval

/-- The total `ℝ≥0∞`-sum over nonzero points of `σ(I)` of the cone `enorm`-integrals is finite
for `Re s > 1`. This single finiteness estimate licenses both absolute summability and the
sum–integral interchange over `unitCone D`. -/
private theorem tsum_lintegral_unitCone_lt_top {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    (∑' x : {x : idealLattice K I // x ≠ 0},
        ∫⁻ y in unitCone D,
          ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K)‖ₑ ∂archHaar K) < ⊤ := by
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  rw [← (idealLatticeOrbitEquiv I).tsum_eq, tsum_prod', tsum_comm]
  simp_rw [idealLatticeOrbitEquiv_apply, tsum_lintegral_unitCone_enorm hD]
  have hconv : ∀ x : {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K},
      ∫⁻ z, ‖(archNorm z : ℂ) ^ (s / 2) * archGaussian z (x : mixedSpace K)‖ₑ ∂archHaar K =
        ENNReal.ofReal
          ((Gammaℝ (s.re : ℂ) ^ nrRealPlaces K * Gammaℝ (2 * (s.re : ℂ)) ^ nrComplexPlaces K *
            ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-(s.re : ℂ))).re) := fun x ↦
    lintegral_enorm_eq_ofReal_integral (norm_ne_zero_of_mem_idealLattice x.2.1) hs0
  simp_rw [hconv]
  have hsum : Summable fun x : {x : idealLattice K I // x ≠ 0 ∧
      (x : mixedSpace K) ∈ fundamentalCone K} ↦
      ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-(s.re : ℂ)) :=
    (hasSum_norm_cpow_idealLattice_fundamentalCone I (s := (s.re : ℂ)) (by simpa using hs)).summable
  have hsum_re : Summable fun x : {x : idealLattice K I // x ≠ 0 ∧
      (x : mixedSpace K) ∈ fundamentalCone K} ↦
      (Gammaℝ (s.re : ℂ) ^ nrRealPlaces K * Gammaℝ (2 * (s.re : ℂ)) ^ nrComplexPlaces K *
        ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-(s.re : ℂ))).re :=
    Complex.reCLM.summable (hsum.mul_left _)
  have hle : ∀ x : {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K},
      ENNReal.ofReal
        ((Gammaℝ (s.re : ℂ) ^ nrRealPlaces K * Gammaℝ (2 * (s.re : ℂ)) ^ nrComplexPlaces K *
          ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-(s.re : ℂ))).re) ≤
        ENNReal.ofReal
          ‖(Gammaℝ (s.re : ℂ) ^ nrRealPlaces K * Gammaℝ (2 * (s.re : ℂ)) ^ nrComplexPlaces K *
            ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-(s.re : ℂ))).re‖ :=
    fun x ↦ ENNReal.ofReal_le_ofReal (le_abs_self _)
  refine (tsum_le_tsum hle).trans_lt ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ norm_nonneg _) hsum_re.abs]
  exact ENNReal.ofReal_lt_top

private theorem integrableOn_archNorm_cpow_mul_archGaussian_unitCone {D : Set (realSpace K)}
    {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} (x : {x : idealLattice K I // x ≠ 0})
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K))
      (unitCone D) (archHaar K) := by
  have h := integrable_archGaussian_mul_archNorm_cpow (norm_ne_zero_of_mem_idealLattice x.2) hs
  exact (by simpa only [mul_comm] using h : Integrable _ (archHaar K)).integrableOn

/-- **Absolute convergence of the unfolded cone integral.** Over the cone above a unit fundamental
domain, the norm-weighted Gaussian integrals of the nonzero points of an ideal lattice form a
summable family for `σ > 1`. -/
theorem summable_integral_unitCone {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun x : {x : idealLattice K I // x ≠ 0} ↦
      ∫ y in unitCone D,
        ‖archGaussian y (x : mixedSpace K)‖ * archNorm y ^ (σ / 2) ∂archHaar K := by
  have hlt := tsum_lintegral_unitCone_lt_top hD I (s := (σ : ℂ)) (by simpa using hσ)
  have hterm (x : {x : idealLattice K I // x ≠ 0}) :
      ENNReal.ofReal (∫ y in unitCone D,
          ‖archGaussian y (x : mixedSpace K)‖ * archNorm y ^ (σ / 2) ∂archHaar K) =
        ∫⁻ y in unitCone D,
          ‖(archNorm y : ℂ) ^ ((σ : ℂ) / 2) * archGaussian y (x : mixedSpace K)‖ₑ ∂archHaar K := by
    have hint := integrableOn_archNorm_cpow_mul_archGaussian_unitCone (D := D) x
      (s := (σ : ℂ)) (by simpa using zero_lt_one.trans hσ)
    rw [← ofReal_integral_norm_eq_lintegral_eNorm hint]
    congr 1
    refine setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y hy ↦ ?_
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (archNorm_pos (mem_unitCone.mp hy).1),
      mul_comm]
    simp
  refine summable_of_tsum_ofReal_lt_top
    (fun x ↦ setIntegral_nonneg (measurableSet_unitCone hD.measurableSet) fun y hy ↦
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (archNorm_pos (mem_unitCone.mp hy).1).le _)) ?_
  simp_rw [hterm]
  exact hlt

/-- **Integrability of the norm-weighted theta series minus `1` on the unit cone.** For `Re s > 1`
and any unit fundamental domain `D`, `(archNorm y)^(s/2) * (θ_{σ(I)}(y) - 1)` is integrable on
`unitCone D` with respect to `archHaar K`. -/
theorem integrableOn_archNorm_cpow_mul_latticeTheta_sub_one_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn
      (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1))
      (unitCone D) (archHaar K) := by
  classical
  have hmeas : AEStronglyMeasurable
      (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1))
      ((archHaar K).restrict (unitCone D)) := by
    have hcont : ContinuousOn
        (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1))
        {y : realSpace K | ∀ w, 0 < y w} := fun y hy ↦ by
      have h1 : ContinuousAt (fun z : realSpace K ↦ (archNorm z : ℂ) ^ (s / 2)) y :=
        (continuousAt_cpow_const
          (Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using archNorm_pos hy)))).comp
          (Complex.continuous_ofReal.comp continuous_archNorm).continuousAt
      exact (h1.mul ((continuousAt_latticeTheta (idealLattice K I) hy).sub
        continuousAt_const)).continuousWithinAt
    have hP : MeasurableSet {y : realSpace K | ∀ w, 0 < y w} := by
      simpa only [Set.ofPred_forall] using MeasurableSet.iInter fun w : InfinitePlace K ↦
        measurableSet_lt (measurable_const (a := (0 : ℝ))) (measurable_pi_apply w)
    exact (hcont.aestronglyMeasurable hP).mono_measure
      (Measure.restrict_mono (fun _ hy ↦ (mem_unitCone.mp hy).1) le_rfl)
  refine ⟨hmeas, ?_⟩
  rw [HasFiniteIntegral]
  have hpt : ∀ᵐ y ∂(archHaar K).restrict (unitCone D),
      ‖(archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1)‖ₑ ≤
        ∑' x : {x : idealLattice K I // x ≠ 0},
          ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K)‖ₑ := by
    filter_upwards [ae_restrict_mem (measurableSet_unitCone hD.measurableSet)] with y hy
    rw [latticeTheta_eq_one_add (idealLattice K I) y (mem_unitCone.mp hy).1,
      add_sub_cancel_left, ← tsum_mul_left]
    exact eNorm_tsum_le_tsum_eNorm
  have hm (x : {x : idealLattice K I // x ≠ 0}) :=
    (integrableOn_archNorm_cpow_mul_archGaussian_unitCone (D := D) x
      (zero_lt_one.trans hs)).aestronglyMeasurable.eNorm
  exact (lintegral_mono_ae hpt).trans_lt
    ((lintegral_tsum hm).trans_lt (tsum_lintegral_unitCone_lt_top hD I hs))

private theorem summable_integral_unitCone_orbit {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : ((𝓞 K)ˣ ⧸ torsion K) ×
        {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K} ↦
      ∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) *
        archGaussian y (((idealLatticeOrbitEquiv I p).1 : idealLattice K I) : mixedSpace K)
      ∂archHaar K := by
  refine Summable.of_norm (summable_of_tsum_ofReal_lt_top (fun _ ↦ norm_nonneg _) ?_)
  have hle : ∀ p : ((𝓞 K)ˣ ⧸ torsion K) ×
      {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K},
      ENNReal.ofReal
        ‖∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) *
          archGaussian y (((idealLatticeOrbitEquiv I p).1 : idealLattice K I) : mixedSpace K)
          ∂archHaar K‖ ≤
        ∫⁻ y in unitCone D,
          ‖(archNorm y : ℂ) ^ (s / 2) *
            archGaussian y (((idealLatticeOrbitEquiv I p).1 : idealLattice K I) : mixedSpace K)‖ₑ
          ∂archHaar K := fun p ↦ by
    rw [ofReal_norm]
    exact eNorm_integral_le_lintegral_eNorm _
  refine (tsum_le_tsum hle).trans_lt ?_
  rw [(idealLatticeOrbitEquiv I).tsum_eq fun x : {x : idealLattice K I // x ≠ 0} ↦
    ∫⁻ y in unitCone D,
      ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K)‖ₑ ∂archHaar K]
  exact tsum_lintegral_unitCone_lt_top hD I hs

/-- **Hecke's unfolding on the unit cone.** For `Re s > 1` and any unit fundamental domain `D`,
the integral of `N(y)^(s/2) (θ_{σ(I)}(y) - 1)` over `unitCone D` equals
`Γ_ℝ(s)^r₁ Γ_ℝ(2s)^r₂ ∑_{x ∈ σ(I) ∩ cone} |N(x)|^(-s)`. -/
theorem integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    ∫ y in unitCone D,
        (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1) ∂archHaar K =
      Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
        ∑' x : {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K},
          ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-s) := by
  classical
  have : Countable ((𝓞 K)ˣ ⧸ torsion K) := countable_units_quotient_torsion
  have hmeas (x : {x : idealLattice K I // x ≠ 0}) :=
    (integrableOn_archNorm_cpow_mul_archGaussian_unitCone (D := D) x
      (zero_lt_one.trans hs)).aestronglyMeasurable
  have hcongr :
      ∫ y in unitCone D,
          (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1) ∂archHaar K =
        ∫ y in unitCone D,
          ∑' x : {x : idealLattice K I // x ≠ 0},
            (archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K) ∂archHaar K := by
    refine setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y hy ↦ ?_
    rw [latticeTheta_eq_one_add (idealLattice K I) y (mem_unitCone.mp hy).1,
      add_sub_cancel_left, ← tsum_mul_left]
  rw [hcongr, integral_tsum hmeas (tsum_lintegral_unitCone_lt_top hD I hs).ne,
    ← (idealLatticeOrbitEquiv I).tsum_eq]
  have hswap : Summable fun c :
      {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K} ×
        ((𝓞 K)ˣ ⧸ torsion K) ↦
      ∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) *
        archGaussian y
          (((idealLatticeOrbitEquiv I (Equiv.prodComm _ _ c)).1 : idealLattice K I) : mixedSpace K)
        ∂archHaar K :=
    (summable_integral_unitCone_orbit hD I hs).comp_injective (Equiv.prodComm _ _).injective
  rw [← (Equiv.prodComm _ _).tsum_eq,
    hswap.tsum_prod' fun x ↦ hswap.comp_injective (Prod.mk_right_injective x)]
  simp_rw [Equiv.prodComm_apply, Prod.swap, idealLatticeOrbitEquiv_apply]
  rw [← tsum_mul_left]
  refine tsum_congr fun x ↦ ?_
  exact tsum_integral_unitCone_orbit hD (norm_ne_zero_of_mem_idealLattice x.2.1)
    (zero_lt_one.trans hs)

/-! ### Identification of the Mellin pair of an ideal lattice -/

/-- The relation `2 * 2^(-s) * Γ_ℝ(2s) = Γ_ℂ(s)` between Deligne's real and complex gamma
factors. -/
private theorem two_mul_two_cpow_neg_mul_Gammaℝ_two_mul (s : ℂ) :
    (2 : ℂ) * (2 : ℂ) ^ (-s) * Gammaℝ (2 * s) = Gammaℂ s := by
  rw [Gammaℝ_def, Gammaℂ_def, show -(2 * s) / 2 = -s by ring, show 2 * s / 2 = s by ring,
    show (2 : ℂ) * (π : ℂ) = (((2 : ℝ) * π : ℝ) : ℂ) by push_cast; rfl,
    Complex.ofReal_mul, TauCeti.ofReal_mul_cpow (by norm_num : (0 : ℝ) ≤ 2)]
  push_cast
  ring

open scoped Classical in
/-- The covolume power `(V_I²)^(s/2)` of an ideal lattice splits into the discriminant, the
complex-place factor `2^(-r₂ s)`, and the ideal norm `N(I)^s`. -/
private theorem covolume_idealLattice_sq_cpow (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    ((ZLattice.covolume (idealLattice K I) : ℂ) ^ 2) ^ (s / 2) =
      ((discr K).natAbs : ℂ) ^ (s / 2) *
        ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K *
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s := by
  have hI0 : (0 : ℝ) ≤ (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) :=
    Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg I.1)
  have hdiscr : (Real.sqrt |(discr K : ℝ)|) ^ 2 = ((discr K).natAbs : ℝ) := by
    rw [Real.sq_sqrt (abs_nonneg _), ← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  have hsq_real : ZLattice.covolume (idealLattice K I) ^ 2 =
      ((discr K).natAbs : ℝ) * (((2⁻¹ : ℝ) ^ 2) ^ nrComplexPlaces K *
        (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ 2) := by
    rw [covolume_idealLattice, mul_pow, mul_pow, hdiscr, ← pow_mul, mul_comm (nrComplexPlaces K) 2,
      pow_mul]
    ring
  have hsq : ((ZLattice.covolume (idealLattice K I) : ℂ) ^ 2) =
      ((ZLattice.covolume (idealLattice K I) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  have h2inv : (((2⁻¹ : ℝ) ^ 2 : ℝ) : ℂ) ^ (s / 2) = (2 : ℂ) ^ (-s) := by
    rw [Complex.ofReal_pow, TauCeti.ofReal_pow_cpow (by norm_num : (0 : ℝ) ≤ 2⁻¹),
      Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      Complex.ofReal_ofNat, Nat.cast_ofNat, show (2 : ℂ) * (s / 2) = s by ring, Complex.cpow_neg]
  have hIpow : (((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ 2 : ℝ) : ℂ) ^
      (s / 2) = ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s := by
    rw [Complex.ofReal_pow, TauCeti.ofReal_pow_cpow hI0, Complex.ofReal_ratCast,
      Nat.cast_ofNat, show (2 : ℂ) * (s / 2) = s by ring]
  rw [hsq, hsq_real, Complex.ofReal_mul, TauCeti.ofReal_mul_cpow (Nat.cast_nonneg _),
    Complex.ofReal_mul, TauCeti.ofReal_mul_cpow (by positivity),
    Complex.ofReal_pow, TauCeti.ofReal_pow_cpow (by positivity), Complex.cpow_nat_mul,
    h2inv, hIpow, Complex.ofReal_natCast, mul_assoc]

open scoped Classical in
/-- **Hecke's Mellin identification for an ideal lattice.** On `Re s > 1`, the completed function
of `mellinKernelFEPair hD (idealLattice K I)` evaluated at `s / 2` is the completed partial zeta
series of the ideal class of `I⁻¹`. -/
theorem mellinKernelFEPair_idealLattice_Λ_eq {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) =
      ((discr K).natAbs : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  have hm1 := hasMellin_mellinKernel_sub hD.measurableSet hD.isBounded (idealLattice K I) s
    (integrableOn_archNorm_cpow_mul_latticeTheta_sub_one_unitCone hD I hs)
  have hconst : (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
      ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ) = (mellinConstant K : ℂ) := by
    rw [mellinConstant_eq_mul_surfaceHaar_real hD]
    push_cast
    rfl
  simp_rw [hconst] at hm1
  have hm2 := hasMellin_mellinKernel_sub_mellinConstant hD (idealLattice K I)
    (s := s / 2) (by rw [Complex.div_ofNat_re]; linarith)
  rw [← hm2.2, hm1.2, integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one hD I hs,
    (hasSum_norm_cpow_idealLattice_fundamentalCone I hs).tsum_eq,
    covolume_idealLattice_sq_cpow I s]
  set N : ℂ := ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ)
  set S : ℂ := ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
    (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  have hN0 : N ≠ 0 :=
    Rat.cast_ne_zero.mpr (FractionalIdeal.absNorm_eq_zero_iff.not.mpr I.ne_zero)
  have hNcancel : N ^ s * N ^ (-s) = 1 := by
    rw [← Complex.cpow_add _ _ hN0, add_neg_cancel, Complex.cpow_zero]
  have hΓC : (2 : ℂ) ^ nrComplexPlaces K * ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K *
      Gammaℝ (2 * s) ^ nrComplexPlaces K = Gammaℂ s ^ nrComplexPlaces K := by
    rw [← mul_pow, ← mul_pow, two_mul_two_cpow_neg_mul_Gammaℝ_two_mul]
  calc (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
        (((discr K).natAbs : ℂ) ^ (s / 2) * ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K * N ^ s) *
        (Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
          ((torsionOrder K : ℂ) * N ^ (-s) * S))
      = ((discr K).natAbs : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
          ((2 : ℂ) ^ nrComplexPlaces K * ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K *
            Gammaℝ (2 * s) ^ nrComplexPlaces K) *
          (N ^ s * N ^ (-s)) * ((torsionOrder K : ℂ) / (torsionOrder K : ℂ)) * S := by ring
    _ = _ := by rw [hΓC, hNcancel, div_self hw, mul_one, mul_one]

/-! ### The completed partial zeta function -/

/-- **The completed partial zeta function** of the ideal class of `I⁻¹`, Neukirch VII (5.4) and
(5.9): the canonical meromorphic continuation from `Re s > 1` of
`|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ∑_{𝔟 ∈ [I]⁻¹} N(𝔟)^(-s)`. It depends only on the ideal class of
`I` (`completedPartialZeta_eq_of_class_eq`). -/
def completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℂ → ℂ :=
  meromorphicContinuation 1 fun s ↦
    ((discr K).natAbs : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
      Gammaℂ s ^ nrComplexPlaces K *
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
        (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)

/-- Defining equation of `completedPartialZeta`. -/
theorem completedPartialZeta_def (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I =
      meromorphicContinuation 1 fun s ↦
        ((discr K).natAbs : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
          Gammaℂ s ^ nrComplexPlaces K *
          ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
            (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := (rfl)

/-- The completed partial zeta function is in meromorphic normal form on the plane. -/
theorem meromorphicNFOn_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    MeromorphicNFOn (completedPartialZeta I) univ :=
  meromorphicNFOn_meromorphicContinuation _ _

/-- The completed partial zeta function is meromorphic on the plane. -/
theorem meromorphic_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Meromorphic (completedPartialZeta I) :=
  meromorphicOn_univ.mp (meromorphicNFOn_completedPartialZeta I).meromorphicOn

/-- The completed partial zeta function depends only on the ideal class of `I`. -/
theorem completedPartialZeta_eq_of_class_eq {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : ClassGroup.mk K I = ClassGroup.mk K J) :
    completedPartialZeta I = completedPartialZeta J := by
  rw [completedPartialZeta_def, completedPartialZeta_def, h]

open scoped Classical in
private theorem meromorphic_mellinKernelFEPair_div_two {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    Meromorphic (fun s : ℂ ↦ (mellinKernelFEPair hD L).Λ (s / 2)) := fun s ↦ by
  have hdiv : AnalyticAt ℂ (fun z : ℂ ↦ z / 2) s :=
    analyticAt_id.div analyticAt_const (two_ne_zero : (2 : ℂ) ≠ 0)
  exact MeromorphicAt.comp_analyticAt (f := (mellinKernelFEPair hD L).Λ)
    (g := fun z : ℂ ↦ z / 2) ((mellinKernelFEPair hD L).meromorphic_Λ (s / 2)) hdiv

open scoped Classical in
private theorem analyticAt_mellinKernelFEPair_div_two {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ ↦ (mellinKernelFEPair hD L).Λ (z / 2)) s := by
  have ha : AnalyticAt ℂ (mellinKernelFEPair hD L).Λ (s / 2) := by
    rw [FEPairWithLevel.analyticAt_Λ_iff]
    refine ⟨Or.inl (div_ne_zero h0 two_ne_zero), Or.inl ?_⟩
    simp only [mellinKernelFEPair_k, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    exact fun h ↦ h1 (by linear_combination 2 * h)
  have hdiv : AnalyticAt ℂ (fun z : ℂ ↦ z / 2) s :=
    analyticAt_id.div analyticAt_const (two_ne_zero : (2 : ℂ) ≠ 0)
  exact ha.comp (f := fun z : ℂ ↦ z / 2) hdiv

open scoped Classical in
private theorem analyticOnNhd_mellinKernelFEPair_div_two {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ (mellinKernelFEPair hD L).Λ (z / 2)) {s | 1 < s.re} := by
  intro s hs
  refine analyticAt_mellinKernelFEPair_div_two hD L ?_ ?_
  · rintro rfl; norm_num at hs
  · rintro rfl; norm_num at hs

open scoped Classical in
/-- As punctured germs at any point of the plane, `completedPartialZeta I` agrees with the
completed function of Hecke's Mellin pair evaluated at `s / 2`. -/
theorem completedPartialZeta_eventuallyEq_mellinKernelFEPair {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (z : ℂ) :
    completedPartialZeta I =ᶠ[𝓝[≠] z]
      fun s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) :=
  meromorphicContinuation_eventuallyEq
    (meromorphic_mellinKernelFEPair_div_two hD (idealLattice K I))
    (analyticOnNhd_mellinKernelFEPair_div_two hD (idealLattice K I))
    (fun _ hs ↦ mellinKernelFEPair_idealLattice_Λ_eq hD I hs) z

open scoped Classical in
/-- Away from the poles `0` and `1`, `completedPartialZeta I s` is the completed function of
Hecke's Mellin pair at `s / 2`, independently of the unit fundamental domain `D`. -/
theorem completedPartialZeta_eq_mellinKernelFEPair {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedPartialZeta I s = (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) :=
  meromorphicContinuation_apply
    (meromorphic_mellinKernelFEPair_div_two hD (idealLattice K I))
    (analyticOnNhd_mellinKernelFEPair_div_two hD (idealLattice K I))
    (fun _ hs ↦ mellinKernelFEPair_idealLattice_Λ_eq hD I hs)
    (analyticAt_mellinKernelFEPair_div_two hD (idealLattice K I) h0 h1)

/-- On `Re s > 1`, the completed partial zeta function is the completed sum over the nonzero
integral ideals in the class of `I⁻¹`. -/
theorem completedPartialZeta_eq_tsum (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((discr K).natAbs : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  rw [completedPartialZeta_eq_mellinKernelFEPair hD I h0 h1,
    mellinKernelFEPair_idealLattice_Λ_eq hD I hs]

/-- **Fundamental-cone representation** (Neukirch VII (5.3)–(5.4)): on `Re s > 1`, the completed
partial zeta function is written through the sum of `|N(x)|^(-s)` over the points of `σ(I)` in
Mathlib's fundamental cone. -/
theorem completedPartialZeta_eq_tsum_fundamentalCone (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((discr K).natAbs : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s /
        (torsionOrder K : ℂ) *
        ∑' x : {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K},
          ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-s) := by
  set N : ℂ := ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ)
  set S : ℂ := ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
    (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  have hN0 : N ≠ 0 :=
    Rat.cast_ne_zero.mpr (FractionalIdeal.absNorm_eq_zero_iff.not.mpr I.ne_zero)
  have hNcancel : N ^ s * N ^ (-s) = 1 := by
    rw [← Complex.cpow_add _ _ hN0, add_neg_cancel, Complex.cpow_zero]
  rw [completedPartialZeta_eq_tsum I hs,
    (hasSum_norm_cpow_idealLattice_fundamentalCone I hs).tsum_eq]
  calc ((discr K).natAbs : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K * S
      = ((discr K).natAbs : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
          Gammaℂ s ^ nrComplexPlaces K * (N ^ s * N ^ (-s)) *
          ((torsionOrder K : ℂ) / (torsionOrder K : ℂ)) * S := by
        rw [hNcancel, div_self hw, mul_one, mul_one]
    _ = _ := by ring

/-- **Agreement with the ray-class Dirichlet series at the trivial modulus.** On `Re s > 1`,
`completedPartialZeta I s` is the completed `LSeries` of `rayClassCoeff (Modulus.one K) c`, where
`c` corresponds to the ideal class of `I⁻¹`. -/
theorem completedPartialZeta_eq_LSeries_rayClassCoeff (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : RayClassGroup (Modulus.one K))
    (hc : oneEquivClassGroup c = (ClassGroup.mk K I)⁻¹) {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((discr K).natAbs : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s := by
  obtain ⟨d, J, hd, hJ⟩ := exists_nat_pos_mul_eq_coeIdeal I
  have hclassJ : ClassGroup.mk0 J = ClassGroup.mk K I := classGroup_mk0_eq_mk_of_mul hd hJ
  have hJray : idealClass (Modulus.one K) (integralIdealsPrimeToOneEquiv.symm J) = c⁻¹ := by
    apply oneEquivClassGroup.injective
    rw [map_inv, hc, inv_inv, ← hclassJ, idealClass_apply, oneEquivClassGroup_rayClassMk,
      ← ClassGroup.mk_mk0 K J]
    congr 1
    exact Units.ext (by
      simp [NumberFieldArithmetic.coe_integralIdealsAwayHom, FractionalIdeal.coe_mk0])
  rw [completedPartialZeta_eq_tsum I hs, LSeries_rayClassCoeff_one_eq_tsum J hJray hs]
  congr 1
  let e : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹} ≃
      {𝔟 : (Ideal (𝓞 K))⁰ // ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K))).IsPrincipal} :=
    Equiv.subtypeEquivRight fun 𝔟 ↦ classGroup_mk0_eq_inv_iff_isPrincipal_mul hd hJ 𝔟
  simpa [e] using e.tsum_eq fun 𝔟 ↦ (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)

/-- **Hecke's Mellin representation** (Neukirch VII (5.5)): on `Re s > 1`, for every unit
fundamental domain `D`, the completed partial zeta function at `s` is the Mellin transform of
`mellinKernel D (idealLattice K I) - mellinConstant K` at `s / 2`. -/
theorem hasMellin_mellinKernel_sub_completedPartialZeta {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun u ↦ mellinKernel D (idealLattice K I) u - (mellinConstant K : ℂ)) (s / 2)
      (completedPartialZeta I s) := by
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  rw [completedPartialZeta_eq_mellinKernelFEPair hD I h0 h1]
  exact hasMellin_mellinKernel_sub_mellinConstant hD (idealLattice K I)
    (by rw [Complex.div_ofNat_re]; linarith)

/-- On `Re s > 1`, `completedPartialZeta I s` equals the `mellin` transform of
`mellinKernel D (idealLattice K I) - mellinConstant K` at `s / 2`. -/
theorem completedPartialZeta_eq_mellin {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta I s =
      mellin (fun u ↦ mellinKernel D (idealLattice K I) u - (mellinConstant K : ℂ)) (s / 2) :=
  (hasMellin_mellinKernel_sub_completedPartialZeta hD I hs).2.symm

open scoped Classical in
/-- **Hecke's unit-cone representation** (Neukirch VII (5.5), before the Mellin substitution):
on `Re s > 1`, for every unit fundamental domain `D`, the completed partial zeta function is
`(2^r₂ / w) (V_I²)^(s/2)` times the integral of `N(y)^(s/2) (θ_{σ(I)}(y) - 1)` over `unitCone D`. -/
theorem completedPartialZeta_eq_integral_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta I s =
      (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
        ((ZLattice.covolume (idealLattice K I) : ℂ) ^ 2) ^ (s / 2) *
        ∫ y in unitCone D,
          (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1) ∂archHaar K := by
  have hm := hasMellin_mellinKernel_sub hD.measurableSet hD.isBounded (idealLattice K I) s
    (integrableOn_archNorm_cpow_mul_latticeTheta_sub_one_unitCone hD I hs)
  have hconst : (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
      ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ) = (mellinConstant K : ℂ) := by
    rw [mellinConstant_eq_mul_surfaceHaar_real hD]
    push_cast
    rfl
  simp_rw [hconst] at hm
  rw [completedPartialZeta_eq_mellin hD I hs, hm.2]

/-! ### Regularity, poles, residues and functional equation -/

/-- The completed partial zeta function is analytic away from `0` and `1`. -/
theorem analyticAt_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (completedPartialZeta I) s := by
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  have hg := analyticAt_mellinKernelFEPair_div_two hD (idealLattice K I) h0 h1
  rw [← (meromorphicNFOn_completedPartialZeta I
        (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt,
    meromorphicOrderAt_congr (completedPartialZeta_eventuallyEq_mellinKernelFEPair hD I s)]
  exact hg.meromorphicOrderAt_nonneg

/-- **Residue at `s = 0`**: `s * completedPartialZeta I s → -(2 * mellinConstant K)` as `s → 0`. -/
theorem tendsto_mul_completedPartialZeta_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun s : ℂ ↦ s * completedPartialZeta I s) (𝓝[≠] 0)
      (𝓝 (-(2 * (mellinConstant K : ℂ)))) := by
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  have hcont : Continuous (fun s : ℂ ↦ s / 2) := continuous_id.div_const 2
  have hdiv : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [zero_div] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    · exact eventually_of_mem self_mem_nhdsWithin fun s hs ↦
        div_ne_zero (mem_compl_singleton_iff.mp hs) two_ne_zero
  have hres := ((mellinKernelFEPair hD (idealLattice K I)).Λ_residue_zero.comp hdiv).const_mul 2
  simp only [mellinKernelFEPair_f₀, smul_eq_mul, Function.comp_def, mul_neg] at hres
  refine hres.congr' ?_
  filter_upwards [completedPartialZeta_eventuallyEq_mellinKernelFEPair hD I 0] with s hs
  rw [hs]
  ring

/-- **Residue at `s = 1`**: `(s - 1) * completedPartialZeta I s → 2 * mellinConstant K` as
`s → 1`. -/
theorem tendsto_sub_one_mul_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun s : ℂ ↦ (s - 1) * completedPartialZeta I s) (𝓝[≠] 1)
      (𝓝 (2 * (mellinConstant K : ℂ))) := by
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  have hcont : Continuous (fun s : ℂ ↦ s / 2) := continuous_id.div_const 2
  have hdiv : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 1)
      (𝓝[≠] ((mellinKernelFEPair hD (idealLattice K I)).k : ℂ)) := by
    rw [mellinKernelFEPair_k]
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h12 : (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
      rw [← h12]
      exact (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
    · refine eventually_of_mem self_mem_nhdsWithin fun s hs hEq ↦
        mem_compl_singleton_iff.mp hs ?_
      have hEq' : s / 2 = 1 / 2 := by simpa using hEq
      linear_combination 2 * hEq'
  have hres := ((mellinKernelFEPair hD (idealLattice K I)).Λ_residue_k.comp hdiv).const_mul 2
  simp only [mellinKernelFEPair_k, mellinKernelFEPair_ε, mellinKernelFEPair_N,
    mellinKernelFEPair_g₀, Complex.ofReal_one, Complex.one_cpow, mul_one, one_mul,
    smul_eq_mul, Function.comp_def] at hres
  refine hres.congr' ?_
  filter_upwards [completedPartialZeta_eventuallyEq_mellinKernelFEPair hD I 1] with s hs
  rw [hs, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

/-- The completed partial zeta function has a simple pole at `s = 0`. -/
theorem meromorphicOrderAt_completedPartialZeta_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    meromorphicOrderAt (completedPartialZeta I) 0 = (-1 : ℤ) := by
  have hne : -(2 * (mellinConstant K : ℂ)) ≠ 0 :=
    neg_ne_zero.mpr
      (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr (mellinConstant_ne_zero K)))
  refine (meromorphic_completedPartialZeta I 0).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    hne ?_
  simpa only [sub_zero, smul_eq_mul] using tendsto_mul_completedPartialZeta_zero I

/-- The completed partial zeta function has a simple pole at `s = 1`. -/
theorem meromorphicOrderAt_completedPartialZeta_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    meromorphicOrderAt (completedPartialZeta I) 1 = (-1 : ℤ) := by
  have hne : (2 * (mellinConstant K : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr (mellinConstant_ne_zero K))
  refine (meromorphic_completedPartialZeta I 1).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    hne ?_
  simpa only [smul_eq_mul] using tendsto_sub_one_mul_completedPartialZeta I

open scoped Classical in
/-- The Mellin pair of the Euclidean dual of `σ(I)` over `D⁻¹` has the same completed function as
the Mellin pair of `σ(J)` over `traceShift K * D⁻¹`, where `J = I^∨` is the trace dual. -/
private theorem mellinKernelFEPair_mixedDual_idealLattice_Λ_eq
    {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    (mellinKernelFEPair hD.inv (mixedDual K (idealLattice K I))).Λ =
      (mellinKernelFEPair (hD.inv.mul traceShift_mem_normOneSurface) (idealLattice K J)).Λ := by
  rw [← FEPairWithLevel.toWeakFEPair_Λ, ← FEPairWithLevel.toWeakFEPair_Λ]
  refine WeakFEPair.Λ_congr (fun u hu ↦ ?_) (by simp) (by simp) (by simp) (by simp)
  simp only [FEPairWithLevel.toWeakFEPair_f, mellinKernelFEPair_f, indicator_of_mem hu]
  exact mellinKernel_mixedDual_idealLattice hJ D⁻¹ u

/-- **Functional equation of the completed partial zeta function**, Neukirch VII (5.9):
`Z(I, 1 - s) = Z(J, s)` off `0` and `1`, where `J = I^∨ = FractionalIdeal.dual ℤ ℚ I` is the trace
dual of `I`. -/
theorem completedPartialZeta_one_sub {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedPartialZeta I (1 - s) = completedPartialZeta J s := by
  have hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  have hD' := hD.inv.mul (traceShift_mem_normOneSurface (K := K))
  have hs0' : 1 - s ≠ 0 := sub_ne_zero.mpr h1.symm
  have hs1' : 1 - s ≠ 1 := fun h ↦ h0 (by linear_combination -h)
  have h12 : (1 - s) / 2 ≠ 0 := div_ne_zero hs0' two_ne_zero
  have h12' : (1 - s) / 2 ≠ 1 / 2 := fun h ↦ h0 (by linear_combination -2 * h)
  rw [completedPartialZeta_eq_mellinKernelFEPair hD I hs0' hs1',
    mellinKernelFEPair_Λ_eq hD (idealLattice K I) h12 h12',
    mellinKernelFEPair_mixedDual_idealLattice_Λ_eq hD hJ,
    show (1 / 2 : ℂ) - (1 - s) / 2 = s / 2 by ring,
    completedPartialZeta_eq_mellinKernelFEPair hD' J h0 h1]

/-- **Functional equation of the completed partial zeta function, as punctured germs** at every
point of the plane, including the poles `0` and `1`. -/
theorem completedPartialZeta_one_sub_eventuallyEq {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)) (s : ℂ) :
    (fun z ↦ completedPartialZeta I (1 - z)) =ᶠ[𝓝[≠] s] completedPartialZeta J := by
  have hfin : ({0, 1} : Set ℂ).Finite := (Set.finite_singleton 1).insert 0
  filter_upwards [nhdsNE_of_nhdsNE_sdiff_finite univ_mem hfin.to_subtype] with z hz
  simp only [Set.mem_sdiff, mem_univ, mem_insert_iff, mem_singleton_iff, true_and, not_or] at hz
  exact completedPartialZeta_one_sub hJ hz.1 hz.2

end TauCeti.LFunctions
