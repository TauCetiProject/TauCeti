/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Continuation
public import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.UnitQuotient
public import TauCeti.NumberTheory.LFunctions.Theta.Mellin.Pair
public import TauCeti.NumberTheory.LFunctions.Theta.UnitCone
public import TauCeti.RingTheory.DedekindDomain.Different.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.Meromorphic.Order
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
import TauCeti.NumberTheory.LFunctions.Theta.GammaIntegral
import TauCeti.NumberTheory.NumberField.Global.RayClass.Integral
import TauCeti.RingTheory.ClassGroup.Basic

/-!
# Completed partial zeta functions of ideal classes

For an invertible fractional ideal `I` of a number field `K`, let `𝔎` be the ideal class of `I⁻¹`.
On `Re s > 1`, the completed partial zeta function attached to `I` is

`Z(I, s) = |d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ∑_{𝔟 ∈ 𝔎} N(𝔟) ^ (-s)`,

where the sum runs over the nonzero integral ideals `𝔟` of `𝓞 K` in the class of `I⁻¹` — that is,
the nonzero integral ideals `𝔟` such that `𝔟 I` is principal. We define
`TauCeti.LFunctions.completedPartialZeta I` globally on `ℂ` as the canonical meromorphic normal-form
continuation (`TauCeti.meromorphicContinuation 1`) from `Re s > 1`.

Following Hecke (Neukirch, Chapter VII, §5), we unfold the integral of the norm-weighted reduced
theta series `N(y) ^ (s / 2) (θ_{σ(I)}(y) - 1)` over the cone `unitCone D` above any unit
fundamental domain `D ⊆ S`. Grouping the nonzero points of the ideal lattice `σ(I)` into orbits
under `(𝓞 K)ˣ` matches the orbits with the integral ideals `𝔟` of class `[I]⁻¹`; each orbit sums
over `(𝓞 K)ˣ` (with torsion multiplicity `w = #μ(K)`) to a full archimedean Gaussian integral over
`realSpace K`, evaluated by `integral_archGaussian_mul_archNorm_cpow`. Rescaling by the covolume
`V_{σ(I)} = N(I) 2 ^ (-r₂) √|d_K|` identifies `completedPartialZeta I` on `Re s > 1` with the
Mellin transform at `s / 2` of `mellinKernel D (idealLattice K I) - mellinConstant K`, and hence
globally with the normal form of `s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`.

From `mellinKernelFEPair` and the trace-dual kernel identity `mellinKernel_mixedDual_idealLattice`
we deduce meromorphic continuation to `ℂ`, analyticity away from simple poles at `s = 0` and
`s = 1` with residues `-2 a₀` and `2 a₀` (`a₀ = mellinConstant K = 2 ^ (r - 1) R / w`), and
Hecke's functional equation `Z(I, 1 - s) = Z(I^∨, s)` against the trace dual
`FractionalIdeal.dualEquiv ℤ ℚ I`.

## Main definitions

* `TauCeti.LFunctions.completedPartialZeta`: the completed partial zeta function of `I` in
  meromorphic normal form on `ℂ`.

## Main results

* `TauCeti.LFunctions.summable_integral_unitCone`: absolute convergence of the lattice-point
  Gaussian integrals over `unitCone D` for `σ > 1`.
* `TauCeti.LFunctions.completedPartialZeta_eq_toMeromorphicNFOn`: identification of
  `completedPartialZeta I` with the normal form of
  `s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`.
* `TauCeti.LFunctions.completedPartialZeta_eq_tsum`,
  `TauCeti.LFunctions.completedPartialZeta_eq_tsum_spanSingleton`,
  `TauCeti.LFunctions.completedPartialZeta_eq_tsum_fundamentalCone`,
  `TauCeti.LFunctions.completedPartialZeta_eq_mul_LSeries_rayClassCoeff_one`: representations on
  `Re s > 1` over ideals in `[I]⁻¹`, principal products, fundamental-cone lattice points, and the
  trivial-modulus ray-class Dirichlet series.
* `TauCeti.LFunctions.completedPartialZeta_eq_integral_unitCone`,
  `TauCeti.LFunctions.hasMellin_completedPartialZeta`,
  `TauCeti.LFunctions.completedPartialZeta_eq_mellin`: cone-integral and Mellin-transform
  representations on `Re s > 1` (Neukirch VII (5.5)).
* `TauCeti.LFunctions.analyticAt_completedPartialZeta_iff`,
  `TauCeti.LFunctions.tendsto_sub_one_mul_completedPartialZeta`,
  `TauCeti.LFunctions.tendsto_mul_completedPartialZeta_zero`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedPartialZeta_one`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedPartialZeta_zero`: regularity, simple poles at
  `0` and `1`, and their residues.
* `TauCeti.LFunctions.completedPartialZeta_one_sub`: Hecke's functional equation
  `completedPartialZeta I (1 - s) = completedPartialZeta (FractionalIdeal.dualEquiv ℤ ℚ I) s`
  (Neukirch VII (5.9)).

## References

* E. Hecke, *Über die Zetafunktion beliebiger algebraischer Zahlkörper*, Nachr. Ges. Wiss.
  Göttingen (1917), 77–89.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.3)–(5.9).
-/

public section
noncomputable section

open Complex Filter MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  Set Submodule TauCeti.GlobalNumberFields TauCeti.NumberField.mixedEmbedding
open scoped ENNReal nonZeroDivisors Pointwise Topology

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### Definition and class invariance -/

/-- **The completed partial zeta function** attached to an invertible fractional ideal `I` of `K`,
Neukirch VII (5.4) and (5.9): the canonical whole-plane meromorphic normal-form continuation from
`Re s > 1` of `|d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ∑_{𝔟 ∈ [I]⁻¹} N(𝔟) ^ (-s)`. -/
def completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℂ → ℂ :=
  meromorphicContinuation 1 fun s ↦
    ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
      Gammaℂ s ^ nrComplexPlaces K *
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
        (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)

/-- Defining equation of `TauCeti.LFunctions.completedPartialZeta`. -/
theorem completedPartialZeta_def (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I = meromorphicContinuation 1 fun s ↦
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) :=
  (rfl)

/-- `completedPartialZeta I` is in meromorphic normal form on `ℂ`. -/
theorem meromorphicNFOn_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    MeromorphicNFOn (completedPartialZeta I) univ :=
  meromorphicNFOn_meromorphicContinuation _ _

/-- `completedPartialZeta I` is meromorphic on `ℂ`. -/
theorem meromorphic_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Meromorphic (completedPartialZeta I) :=
  meromorphicOn_univ.mp (meromorphicNFOn_completedPartialZeta I).meromorphicOn

/-- `completedPartialZeta I` depends on `I` only through its ideal class in `ClassGroup (𝓞 K)`. -/
theorem completedPartialZeta_congr_class {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : ClassGroup.mk K I = ClassGroup.mk K J) :
    completedPartialZeta I = completedPartialZeta J :=
  congrArg (fun c ↦ meromorphicContinuation 1 fun s ↦
    ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
      Gammaℂ s ^ nrComplexPlaces K *
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = c⁻¹},
        (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) h

/-! ### Unit-orbit parametrization of an ideal lattice -/

section OrbitParametrization

private abbrev InvClassIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Type _ :=
  {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹}

/-- Every ideal `𝔟` in `[I]⁻¹` admits a nonzero generator of `𝔟 I` whose mixed embedding lies in
`fundamentalCone K`. -/
private theorem exists_coneGen (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (𝔟 : InvClassIdeal I) :
    ∃ a : K, a ≠ 0 ∧ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K) ∧
      (𝔟.1.1 : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ a ∧
      mixedEmbedding K a ∈ fundamentalCone K := by
  obtain ⟨x, hx⟩ := (ClassGroup.mk0_eq_inv_mk_iff I 𝔟.1).mp 𝔟.2
  have hx_norm : mixedEmbedding.norm (mixedEmbedding K (x : K)) ≠ 0 := by
    rw [norm_eq_norm, ne_eq, Rat.cast_eq_zero, abs_eq_zero, Algebra.norm_eq_zero_iff]
    exact x.ne_zero
  obtain ⟨u, hu⟩ := fundamentalCone.exists_unit_smul_mem hx_norm
  refine ⟨(u : K) * (x : K), mul_ne_zero (Units.coe_ne_zero u) x.ne_zero, ?_, ?_, ?_⟩
  · have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u : K) * (x : K)) =
        (𝔟.1.1 : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [hx, FractionalIdeal.spanSingleton_eq_spanSingleton]
      refine ⟨u⁻¹, ?_⟩
      rw [Units.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, Units.inv_mul, map_one,
        one_mul]
    have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u : K) * (x : K)) ≤ I.1 := by
      rw [hspan]
      exact mul_le_of_le_one_left' FractionalIdeal.coeIdeal_le_one
    exact hle (FractionalIdeal.mem_spanSingleton_self _ _)
  · rw [hx, FractionalIdeal.spanSingleton_eq_spanSingleton]
    exact ⟨u, by rw [Units.smul_def, Algebra.smul_def]⟩
  · simpa only [unitSMul_smul, map_mul] using hu

private def coneGen (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (𝔟 : InvClassIdeal I) : K :=
  (exists_coneGen I 𝔟).choose

private theorem coneGen_ne_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (𝔟 : InvClassIdeal I) :
    coneGen I 𝔟 ≠ 0 :=
  (exists_coneGen I 𝔟).choose_spec.1

private theorem coneGen_mem (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (𝔟 : InvClassIdeal I) :
    coneGen I 𝔟 ∈ (I : FractionalIdeal (𝓞 K)⁰ K) :=
  (exists_coneGen I 𝔟).choose_spec.2.1

private theorem mul_eq_spanSingleton_coneGen (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (𝔟 : InvClassIdeal I) :
    (𝔟.1.1 : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (coneGen I 𝔟) :=
  (exists_coneGen I 𝔟).choose_spec.2.2.1

private theorem mixedEmbedding_coneGen_mem_fundamentalCone (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (𝔟 : InvClassIdeal I) :
    mixedEmbedding K (coneGen I 𝔟) ∈ fundamentalCone K :=
  (exists_coneGen I 𝔟).choose_spec.2.2.2

private theorem norm_mixedEmbedding_coneGen (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (𝔟 : InvClassIdeal I) :
    mixedEmbedding.norm (mixedEmbedding K (coneGen I 𝔟)) =
      (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℝ) *
        (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
  have hq : |Algebra.norm ℚ (coneGen I 𝔟)| =
      FractionalIdeal.absNorm ((𝔟.1.1 : FractionalIdeal (𝓞 K)⁰ K) * I.1) := by
    rw [mul_eq_spanSingleton_coneGen, FractionalIdeal.absNorm_span_singleton]
  rw [norm_eq_norm, hq, map_mul, FractionalIdeal.coeIdeal_absNorm, Rat.cast_mul, Rat.cast_natCast]

/-- Every nonzero element `a ∈ I` factors `spanSingleton a` as `𝔟 * I` for a unique `𝔟 ∈ [I]⁻¹`. -/
private theorem exists_invClassIdeal_of_mem (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {a : K}
    (ha : a ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) (ha0 : a ≠ 0) :
    ∃ 𝔟 : InvClassIdeal I, ∃ u : (𝓞 K)ˣ, (u : K) * coneGen I 𝔟 = a := by
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ a * ↑I⁻¹ ≤ 1 := by
    calc FractionalIdeal.spanSingleton (𝓞 K)⁰ a * ↑I⁻¹
        ≤ I.1 * ↑I⁻¹ := mul_left_mono (FractionalIdeal.spanSingleton_le_iff_mem.mpr ha)
      _ = 1 := Units.mul_inv I
  obtain ⟨𝔟₀, h𝔟₀⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hmul : (𝔟₀ : FractionalIdeal (𝓞 K)⁰ K) * I.1 =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ a := by
    rw [h𝔟₀, mul_assoc, Units.inv_mul, mul_one]
  have h𝔟₀_ne : 𝔟₀ ≠ ⊥ := by
    rintro rfl
    simp at hmul
    exact ha0 (FractionalIdeal.spanSingleton_eq_zero_iff.mp hmul.symm)
  let 𝔟 : InvClassIdeal I := ⟨⟨𝔟₀, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔟₀_ne⟩,
    (ClassGroup.mk0_eq_inv_mk_iff I _).mpr ⟨Units.mk0 a ha0, hmul⟩⟩
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ (coneGen I 𝔟) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ a := by
    rw [← mul_eq_spanSingleton_coneGen, ← hmul]
  obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hspan
  refine ⟨𝔟, u, ?_⟩
  rwa [Units.smul_def, Algebra.smul_def] at hu

/-- Bijection between `InvClassIdeal I × (𝓞 K)ˣ` and the nonzero points of `idealLattice K I`. -/
private def idealLatticeNeZeroEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    InvClassIdeal I × (𝓞 K)ˣ ≃ {x : idealLattice K I // x ≠ 0} := by
  refine Equiv.ofBijective (fun p ↦ ⟨⟨p.2 • mixedEmbedding K (coneGen I p.1),
      (p.2.unitSMul_mem_idealLattice_iff I _).mpr
        ((mem_idealLattice K I).mpr ⟨coneGen I p.1, coneGen_mem I p.1, rfl⟩)⟩, ?_⟩) ⟨?_, ?_⟩
  · intro h0
    have h1 : p.2 • mixedEmbedding K (coneGen I p.1) = 0 := congrArg Subtype.val h0
    rw [unitSMul_smul, ← map_mul, map_eq_zero_iff _ (mixedEmbedding_injective K)] at h1
    exact mul_ne_zero (Units.coe_ne_zero p.2) (coneGen_ne_zero I p.1) h1
  · rintro ⟨𝔟₁, u₁⟩ ⟨𝔟₂, u₂⟩ h
    have heq : (u₁ : K) * coneGen I 𝔟₁ = (u₂ : K) * coneGen I 𝔟₂ := by
      apply mixedEmbedding_injective K
      simpa only [Subtype.ext_iff, unitSMul_smul, map_mul] using h
    have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ (coneGen I 𝔟₁) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (coneGen I 𝔟₂) := by
      rw [FractionalIdeal.spanSingleton_eq_spanSingleton]
      refine ⟨u₂⁻¹ * u₁, ?_⟩
      rw [Units.smul_def, Units.val_mul, Algebra.smul_def, map_mul, mul_assoc, heq, ← mul_assoc,
        ← map_mul, Units.inv_mul, map_one, one_mul]
    have h𝔟 : 𝔟₁ = 𝔟₂ := by
      apply Subtype.ext
      apply Subtype.ext
      apply FractionalIdeal.coeIdeal_injective (K := K)
      exact mul_right_cancel₀ I.ne_zero
        ((mul_eq_spanSingleton_coneGen I 𝔟₁).trans
          (hspan.trans (mul_eq_spanSingleton_coneGen I 𝔟₂).symm))
    subst h𝔟
    have hu : (u₁ : K) = (u₂ : K) := mul_right_cancel₀ (coneGen_ne_zero I 𝔟₁) heq
    exact Prod.ext rfl (Units.ext (RingOfIntegers.ext hu))
  · rintro ⟨⟨x, hx⟩, hx0⟩
    obtain ⟨a, ha, rfl⟩ := (mem_idealLattice K I).mp hx
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hx0 (Subtype.ext (map_zero _))
    obtain ⟨𝔟, u, hu⟩ := exists_invClassIdeal_of_mem I ha ha0
    refine ⟨(𝔟, u), Subtype.ext (Subtype.ext ?_)⟩
    simp [unitSMul_smul, ← map_mul, hu]

@[simp]
private theorem coe_idealLatticeNeZeroEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : InvClassIdeal I × (𝓞 K)ˣ) :
    ((idealLatticeNeZeroEquiv I p).1 : mixedSpace K) =
      p.2 • mixedEmbedding K (coneGen I p.1) :=
  (rfl)

/-- Bijection between `InvClassIdeal I × Units.torsion K` and the points of `idealLattice K I`
lying in `fundamentalCone K`. -/
private def idealLatticeFundamentalConeEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    InvClassIdeal I × Units.torsion K ≃
      {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K} :=
  calc InvClassIdeal I × Units.torsion K
      ≃ Units.torsion K × InvClassIdeal I := Equiv.prodComm _ _
    _ ≃ {p : (𝓞 K)ˣ × InvClassIdeal I // p.1 ∈ Units.torsion K} :=
        (Equiv.prodSubtypeFstEquivSubtypeProd (p := (· ∈ Units.torsion K))).symm
    _ ≃ {p : InvClassIdeal I × (𝓞 K)ˣ // p.2 ∈ Units.torsion K} :=
        Equiv.subtypeEquiv (Equiv.prodComm _ _) fun _ ↦ Iff.rfl
    _ ≃ {x : {x : idealLattice K I // x ≠ 0} // ((x.1 : mixedSpace K) ∈ fundamentalCone K)} :=
        Equiv.subtypeEquiv (idealLatticeNeZeroEquiv I) fun p ↦
          (fundamentalCone.unit_smul_mem_iff_mem_torsion
            (mixedEmbedding_coneGen_mem_fundamentalCone I p.1) p.2).symm
    _ ≃ {x : idealLattice K I // x ≠ 0 ∧ (x : mixedSpace K) ∈ fundamentalCone K} :=
        Equiv.subtypeSubtypeEquivSubtypeInter (fun x : idealLattice K I ↦ x ≠ 0)
          (fun x : idealLattice K I ↦ (x : mixedSpace K) ∈ fundamentalCone K)
    _ ≃ {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K} :=
        Equiv.subtypeEquivRight fun _ ↦ and_iff_right_of_imp fun hx h0 ↦ by
          have := fundamentalCone.norm_pos_of_mem hx
          rw [h0, Submodule.coe_zero, map_zero] at this
          exact lt_irrefl 0 this

@[simp]
private theorem coe_idealLatticeFundamentalConeEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : InvClassIdeal I × Units.torsion K) :
    ((idealLatticeFundamentalConeEquiv I p : idealLattice K I) : mixedSpace K) =
      (p.2 : (𝓞 K)ˣ) • mixedEmbedding K (coneGen I p.1) := by
  simp [idealLatticeFundamentalConeEquiv, Equiv.prodSubtypeFstEquivSubtypeProd, Equiv.subtypeEquiv]

/-- **Sum of `|N(x)| ^ (-s)` over the points of an ideal lattice in `fundamentalCone K`.** For
`Re s > 1`, the fundamental-cone lattice sum of an invertible fractional ideal `I` is
`w N(I) ^ (-s)` times the ideal sum over `[I]⁻¹`. -/
theorem hasSum_norm_cpow_idealLattice_fundamentalCone (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun x : {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K} ↦
        ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-s))
      ((Units.torsionOrder K : ℂ) *
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s) *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by
  have hI_nonneg : 0 ≤ (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) :=
    Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg I.1)
  set F : InvClassIdeal I → ℂ :=
    fun 𝔟 ↦ ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s) *
      (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-s)
  have hFn : Summable fun 𝔟 : InvClassIdeal I ↦ ‖F 𝔟‖ := by
    have hsum : Summable fun 𝔟 : InvClassIdeal I ↦
        (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℝ) ^ (-s.re) :=
      ((TauCeti.summable_absNorm_rpow_ideal_iff (K := K)).mpr hs).subtype _
    refine (hsum.mul_left ‖((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s)‖).congr fun 𝔟 ↦ ?_
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (Ideal.absNorm_pos_of_nonZeroDivisors 𝔟.1),
      neg_re]
  have h1 : Summable fun _ : Units.torsion K ↦ ‖(1 : ℂ)‖ := Summable.of_finite
  have hprod : HasSum (fun p : InvClassIdeal I × Units.torsion K ↦ F p.1 * 1)
      ((∑' 𝔟, F 𝔟) * ∑' _ : Units.torsion K, (1 : ℂ)) := by
    rw [tsum_mul_tsum_of_summable_norm hFn h1]
    exact (summable_mul_of_summable_norm hFn h1).hasSum
  have hval : (Units.torsionOrder K : ℂ) * ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s) *
      (∑' 𝔟 : InvClassIdeal I, (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-s)) =
        (∑' 𝔟, F 𝔟) * ∑' _ : Units.torsion K, (1 : ℂ) := by
    rw [tsum_const, Units.torsionOrder, nsmul_eq_mul, mul_one, tsum_mul_left]
    ring
  rw [hval]
  refine (idealLatticeFundamentalConeEquiv I).hasSum_iff.mp (hprod.congr_fun fun p ↦ ?_)
  rw [Function.comp_apply, coe_idealLatticeFundamentalConeEquiv, unitSMul_smul, map_mul,
    norm_unit, one_mul, norm_mixedEmbedding_coneGen, ofReal_mul,
    mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) hI_nonneg, ofReal_natCast, ofReal_ratCast, mul_one]
  simp only [F, mul_comm]

/-! ### Unfolding over the unit cone -/

/-- Norm of the weighted archimedean Gaussian at a positive parameter `y`. -/
private theorem norm_archNorm_cpow_mul_archGaussian {y : realSpace K} (hy : ∀ w, 0 < y w)
    (x : mixedSpace K) (s : ℂ) :
    ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y x‖ =
      ‖archGaussian y x‖ * archNorm y ^ (s.re / 2) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (archNorm_pos hy), div_ofNat_re, mul_comm]

/-- Nonzero points of `idealLattice K I` have nonzero mixed norm. -/
private theorem norm_ne_zero_of_idealLatticeNeZero {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (x : {x : idealLattice K I // x ≠ 0}) :
    mixedEmbedding.norm (x : mixedSpace K) ≠ 0 := by
  obtain ⟨a, _, ha⟩ := (mem_idealLattice K I).mp x.1.2
  rw [← ha, ne_eq, norm_eq_zero_iff' ⟨a, rfl⟩, ha]
  exact Subtype.coe_ne_coe.mpr x.2

/-- Evaluation of the real `archHaar` integral of `‖archGaussian y x‖ * archNorm y ^ (σ / 2)` for
`σ > 0` and `N(x) ≠ 0`. -/
private theorem integral_norm_archGaussian_mul_archNorm_rpow {x : mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) {σ : ℝ} (hσ : 0 < σ) :
    (∫ y, ‖archGaussian y x‖ * archNorm y ^ (σ / 2) ∂archHaar K) =
      ‖Gammaℝ σ ^ nrRealPlaces K * Gammaℝ (2 * σ) ^ nrComplexPlaces K‖ *
        mixedEmbedding.norm x ^ (-σ) := by
  have hσ0 : (0 : ℝ) < (σ : ℂ).re := by simpa using hσ
  have hae : (fun y ↦ ((‖archGaussian y x‖ * archNorm y ^ (σ / 2) : ℝ) : ℂ)) =ᵐ[archHaar K]
      fun y ↦ archGaussian y x * (archNorm y : ℂ) ^ ((σ : ℂ) / 2) := by
    filter_upwards [ae_archHaar_pos] with y hy
    have hpow : (archNorm y : ℂ) ^ ((σ : ℂ) / 2) = ((archNorm y ^ (σ / 2) : ℝ) : ℂ) := by
      rw [← ofReal_ofNat, ← ofReal_div, ofReal_cpow (archNorm_pos hy).le]
    rw [hpow, archGaussian_apply, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, ofReal_mul]
  have hint_eq : ((∫ y, ‖archGaussian y x‖ * archNorm y ^ (σ / 2) ∂archHaar K : ℝ) : ℂ) =
      ∫ y, archGaussian y x * (archNorm y : ℂ) ^ ((σ : ℂ) / 2) ∂archHaar K :=
    integral_ofReal.symm.trans (integral_congr_ae hae)
  have hnonneg : 0 ≤ ∫ y, ‖archGaussian y x‖ * archNorm y ^ (σ / 2) ∂archHaar K := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_archHaar_pos] with y hy
    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (archNorm_pos hy).le _)
  have hnorm := congrArg Norm.norm hint_eq
  rw [norm_real, Real.norm_of_nonneg hnonneg, integral_archGaussian_mul_archNorm_cpow hx hσ0,
    norm_mul, norm_cpow_eq_rpow_re_of_pos (lt_of_le_of_ne (mixedEmbedding.norm_nonneg _) hx.symm),
    neg_re, ofReal_re] at hnorm
  exact hnorm

/-- Sum over `(𝓞 K)ˣ` of the norm-weighted real Gaussian cone integrals along one ideal orbit. -/
private theorem tsum_unit_setIntegral_norm_archGaussian {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (𝔟 : InvClassIdeal I) {σ : ℝ} (hσ_pos : 0 < σ) :
    (∑' u : (𝓞 K)ˣ, ∫ y in unitCone D,
        ‖archGaussian y (idealLatticeNeZeroEquiv I (𝔟, u) : mixedSpace K)‖ *
          archNorm y ^ (σ / 2) ∂archHaar K) =
      ((Units.torsionOrder K : ℝ) *
        ‖Gammaℝ σ ^ nrRealPlaces K * Gammaℝ (2 * σ) ^ nrComplexPlaces K‖ *
        (FractionalIdeal.absNorm I.1 : ℝ) ^ (-σ)) *
        (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℝ) ^ (-σ) := by
  have hσ0 : (0 : ℝ) < (σ : ℂ).re := by simpa using hσ_pos
  have hI_nonneg : 0 ≤ (FractionalIdeal.absNorm I.1 : ℝ) :=
    Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg I.1)
  set x₀ := mixedEmbedding K (coneGen I 𝔟)
  have hx₀ : mixedEmbedding.norm x₀ ≠ 0 :=
    (fundamentalCone.norm_pos_of_mem (mixedEmbedding_coneGen_mem_fundamentalCone I 𝔟)).ne'
  have hint : Integrable (fun y ↦ ‖archGaussian y x₀‖ * archNorm y ^ (σ / 2)) (archHaar K) := by
    refine (integrable_archGaussian_mul_archNorm_cpow hx₀ hσ0).norm.congr ?_
    filter_upwards [ae_archHaar_pos] with y hy
    simpa only [mul_comm (archGaussian y x₀), ofReal_re] using
      norm_archNorm_cpow_mul_archGaussian hy x₀ σ
  have hterm (u : (𝓞 K)ˣ) :
      (∫ y in unitCone D,
          ‖archGaussian y (idealLatticeNeZeroEquiv I (𝔟, u) : mixedSpace K)‖ *
            archNorm y ^ (σ / 2) ∂archHaar K) =
        ∫ y in unitCone D, ‖archGaussian (unitScale u y) x₀‖ *
          archNorm (unitScale u y) ^ (σ / 2) ∂archHaar K :=
    setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y _ ↦ by
      simp only [x₀, coe_idealLatticeNeZeroEquiv, archGaussian_unit_smul, archNorm_unitScale]
  simp_rw [hterm]
  rw [← integral_archHaar_eq_tsum_unitCone hD hint, nsmul_eq_mul,
    integral_norm_archGaussian_mul_archNorm_rpow hx₀ hσ_pos, norm_mixedEmbedding_coneGen,
    Real.mul_rpow (Nat.cast_nonneg _) hI_nonneg]
  ring

/-- **Absolute convergence of the lattice-point Gaussian integrals over `unitCone D`.** For `σ > 1`
and any unit fundamental domain `D`, the integrals over `unitCone D` of
`‖archGaussian y x‖ * archNorm y ^ (σ / 2)` are summable over all nonzero `x ∈ σ(I)`. -/
theorem summable_integral_unitCone {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun x : {x : idealLattice K I // x ≠ 0} ↦
      ∫ y in unitCone D, ‖archGaussian y (x : mixedSpace K)‖ * archNorm y ^ (σ / 2)
        ∂archHaar K := by
  have hσ_pos : 0 < σ := zero_lt_one.trans hσ
  have hσ0 : (0 : ℝ) < (σ : ℂ).re := by simpa using hσ_pos
  rw [← (idealLatticeNeZeroEquiv I).summable_iff]
  refine (summable_prod_of_nonneg fun p ↦ setIntegral_nonneg
    (measurableSet_unitCone hD.measurableSet) fun y hy ↦
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (archNorm_pos (mem_unitCone.mp hy).1).le _)).mpr
    ⟨fun 𝔟 ↦ ?_, ?_⟩
  · have hx : mixedEmbedding.norm (mixedEmbedding K (coneGen I 𝔟)) ≠ 0 :=
      (fundamentalCone.norm_pos_of_mem (mixedEmbedding_coneGen_mem_fundamentalCone I 𝔟)).ne'
    refine (summable_setIntegral_norm_unitCone hD
      (integrable_archGaussian_mul_archNorm_cpow hx hσ0)).congr fun u ↦ ?_
    refine setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y hy ↦ ?_
    rw [coe_idealLatticeNeZeroEquiv, archGaussian_unit_smul, ← archNorm_unitScale u y]
    simpa only [mul_comm (archGaussian (unitScale u y) _), ofReal_re] using
      norm_archNorm_cpow_mul_archGaussian (fun w ↦ unitScale_pos ((mem_unitCone.mp hy).1 w) u) _ σ
  · refine (((TauCeti.summable_absNorm_rpow_ideal_iff (K := K)).mpr hσ).subtype _
      |>.mul_left _).congr fun 𝔟 ↦ (tsum_unit_setIntegral_norm_archGaussian hD I 𝔟 hσ_pos).symm

/-- Each nonzero lattice point gives an integrable weighted Gaussian on `unitCone D` for
`Re s > 0`. -/
private theorem integrableOn_unitCone_archNorm_cpow_mul_archGaussian (D : Set (realSpace K))
    {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * archGaussian y x)
      (unitCone D) (archHaar K) := by
  simpa only [mul_comm] using
    (integrable_archGaussian_mul_archNorm_cpow hx hs).integrableOn

/-- Summability of the cone integrals of `‖(archNorm y) ^ (s / 2) * archGaussian y x‖` over
nonzero `x ∈ σ(I)` for `Re s > 1`. -/
private theorem summable_setIntegral_norm_archNorm_cpow_mul_archGaussian {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    Summable fun x : {x : idealLattice K I // x ≠ 0} ↦
      ∫ y in unitCone D, ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K)‖
        ∂archHaar K :=
  (summable_integral_unitCone hD I hs).congr fun _ ↦
    setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun _ hy ↦
      (norm_archNorm_cpow_mul_archGaussian (mem_unitCone.mp hy).1 _ s).symm

/-- **Integrability of the norm-weighted reduced theta series on `unitCone D`** for `Re s > 1`. -/
theorem integrableOn_archNorm_cpow_mul_latticeTheta_sub_one {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    IntegrableOn (fun y ↦ (archNorm y : ℂ) ^ (s / 2) *
        (latticeTheta (idealLattice K I) y - 1)) (unitCone D) (archHaar K) := by
  classical
  let μ := (archHaar K).restrict (unitCone D)
  let F : {x : idealLattice K I // x ≠ 0} → realSpace K → ℂ :=
    fun x y ↦ (archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K)
  have hF_int (x : {x : idealLattice K I // x ≠ 0}) : Integrable (F x) μ :=
    integrableOn_unitCone_archNorm_cpow_mul_archGaussian D (norm_ne_zero_of_idealLatticeNeZero x)
      (zero_lt_one.trans hs)
  have hsum : Summable fun x ↦ ∫ y, ‖F x y‖ ∂μ :=
    summable_setIntegral_norm_archNorm_cpow_mul_archGaussian hD I hs
  have hcont : ContinuousOn (fun y ↦ (archNorm y : ℂ) ^ (s / 2) *
      (latticeTheta (idealLattice K I) y - 1)) (unitCone D) := by
    refine ContinuousOn.mul ?_ (ContinuousOn.sub (fun y hy ↦
      (continuousAt_latticeTheta _ (mem_unitCone.mp hy).1).continuousWithinAt) continuousOn_const)
    refine ContinuousOn.cpow (ofRealCLM.continuous.comp continuous_archNorm).continuousOn
      continuousOn_const fun y hy ↦ Or.inl ?_
    simpa using archNorm_pos (mem_unitCone.mp hy).1
  refine ⟨hcont.aestronglyMeasurable (measurableSet_unitCone hD.measurableSet), ?_⟩
  have hle : ∫⁻ y, ‖(archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1)‖ₑ ∂μ ≤
      ∑' x, ∫⁻ y, ‖F x y‖ₑ ∂μ := by
    rw [← lintegral_tsum fun x ↦ (hF_int x).1.eNorm]
    refine setLIntegral_mono' (measurableSet_unitCone hD.measurableSet) fun y hy ↦ ?_
    rw [latticeTheta_eq_one_add _ y (mem_unitCone.mp hy).1, add_sub_cancel_left, ← tsum_mul_left]
    exact eNorm_tsum_le_tsum_eNorm
  refine lt_of_le_of_lt hle ?_
  have heq (x : {x : idealLattice K I // x ≠ 0}) : ∫⁻ y, ‖F x y‖ₑ ∂μ = ‖∫ y, ‖F x y‖ ∂μ‖ₑ := by
    dsimp [eNorm]
    rw [lintegral_coe_eq_integral _ (hF_int x).norm, ENNReal.coe_nnreal_eq, coe_nnNorm,
      Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    simp only [coe_nnNorm]
  simp_rw [heq]
  exact lt_top_iff_ne_top.mpr
    (ENNReal.tsum_coe_ne_top_iff_summable.mpr (NNReal.summable_coe.mp hsum.abs))

open scoped Classical in
/-- Complex power `(V_{σ(I)} ^ 2) ^ (s / 2)` expanded in terms of `N(I)`, `2 ^ (-r₂)`, and
`|d_K|`. -/
private theorem covolume_sq_idealLattice_cpow (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) =
      ((FractionalIdeal.absNorm I.1 : ℝ) : ℂ) ^ s *
        (((2⁻¹ : ℝ) : ℂ) ^ s) ^ nrComplexPlaces K *
        (((|discr K| : ℤ) : ℂ)) ^ (s / 2) := by
  set N_I : ℝ := (FractionalIdeal.absNorm I.1 : ℝ)
  set D_K : ℝ := ((|discr K| : ℤ) : ℝ)
  have hNI_pos : 0 < N_I := Rat.cast_pos.mpr
    ((FractionalIdeal.absNorm_nonneg I.1).lt_of_ne'
      (FractionalIdeal.absNorm_eq_zero_iff.not.mpr I.ne_zero))
  have hDK_pos : 0 < D_K := Int.cast_pos.mpr (abs_pos.mpr (discr_ne_zero K))
  have hV_pos : 0 < ZLattice.covolume (idealLattice K I) := ZLattice.covolume_pos (idealLattice K I)
  have h1 : (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) =
      (ZLattice.covolume (idealLattice K I) : ℂ) ^ s := by
    rw [TauCeti.ofReal_pow_cpow hV_pos.le 2 (s / 2), Nat.cast_ofNat,
      mul_div_cancel₀ _ two_ne_zero]
  have hcov : ZLattice.covolume (idealLattice K I) = N_I * 2⁻¹ ^ nrComplexPlaces K * √D_K := by
    rw [covolume_idealLattice]
    simp [N_I, D_K]
  rw [h1, hcov, ofReal_mul,
    mul_cpow_ofReal_nonneg (mul_nonneg hNI_pos.le (by positivity)) (Real.sqrt_nonneg _),
    ofReal_mul, mul_cpow_ofReal_nonneg hNI_pos.le (by positivity), ofReal_pow,
    TauCeti.ofReal_pow_cpow (by positivity) (nrComplexPlaces K) s, cpow_nat_mul,
    Real.sqrt_eq_rpow, ← cpow_mul_ofReal_nonneg hDK_pos.le, ofReal_intCast |discr K|]
  congr 2
  push_cast
  ring

open scoped Classical in
/-- Covolume-rescaled normalization algebra converting the unfolded Gaussian sum into the
archimedean factor times the ideal sum. -/
private theorem covolume_gamma_mul_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) *
        ((Units.torsionOrder K : ℂ) *
          (Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K) *
          ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s)) =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K := by
  set r₁ := nrRealPlaces K
  set r₂ := nrComplexPlaces K
  set N_I : ℝ := (FractionalIdeal.absNorm I.1 : ℝ)
  have hNI_pos : 0 < N_I := Rat.cast_pos.mpr
    ((FractionalIdeal.absNorm_nonneg I.1).lt_of_ne'
      (FractionalIdeal.absNorm_eq_zero_iff.not.mpr I.ne_zero))
  have hw : (Units.torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Units.torsionOrder_ne_zero K)
  have h2gamma : (2 : ℂ) ^ r₂ * Gammaℝ (2 * s) ^ r₂ = ((2 : ℂ) ^ s) ^ r₂ * Gammaℂ s ^ r₂ := by
    rw [← mul_pow, two_mul_Gammaℝ_two_mul, mul_pow]
  have h2cancel : (((2⁻¹ : ℝ) : ℂ) ^ s) ^ r₂ * ((2 : ℂ) ^ s) ^ r₂ = 1 := by
    rw [← ofReal_ofNat, ← mul_pow, ← mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
    norm_num
  have hNI_cancel : (N_I : ℂ) ^ s * ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s) = 1 := by
    rw [← ofReal_ratCast, ← cpow_add _ _ (ofReal_ne_zero.mpr hNI_pos.ne'), add_neg_cancel,
      cpow_zero]
  rw [covolume_sq_idealLattice_cpow]
  calc (2 : ℂ) ^ r₂ / (Units.torsionOrder K : ℂ) *
          ((N_I : ℂ) ^ s * (((2⁻¹ : ℝ) : ℂ) ^ s) ^ r₂ * ((|discr K| : ℤ) : ℂ) ^ (s / 2)) *
          ((Units.torsionOrder K : ℂ) * (Gammaℝ s ^ r₁ * Gammaℝ (2 * s) ^ r₂) *
            ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s))
      = (((Units.torsionOrder K : ℂ) / (Units.torsionOrder K : ℂ)) *
          ((N_I : ℂ) ^ s * ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s)) *
          ((((2⁻¹ : ℝ) : ℂ) ^ s) ^ r₂ * ((2 : ℂ) ^ r₂ * Gammaℝ (2 * s) ^ r₂)) *
          (((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ r₁)) := by ring
    _ = ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ r₁ * Gammaℂ s ^ r₂ := by
        rw [div_self hw, hNI_cancel, h2gamma]
        linear_combination
          (((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ r₁ * Gammaℂ s ^ r₂) * h2cancel

/-- Sum over `(𝓞 K)ˣ` of the complex weighted Gaussian cone integrals along one ideal orbit. -/
private theorem tsum_unit_setIntegral_archGaussian {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (𝔟 : InvClassIdeal I) {s : ℂ} (hs0 : 0 < s.re) :
    (∑' u : (𝓞 K)ˣ, ∫ y in unitCone D,
        (archNorm y : ℂ) ^ (s / 2) *
          archGaussian y (idealLatticeNeZeroEquiv I (𝔟, u) : mixedSpace K) ∂archHaar K) =
      ((Units.torsionOrder K : ℂ) *
        (Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K) *
        ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s)) *
        (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  have hI_nonneg : 0 ≤ (FractionalIdeal.absNorm I.1 : ℝ) :=
    Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg I.1)
  set x₀ := mixedEmbedding K (coneGen I 𝔟)
  have hx₀ : mixedEmbedding.norm x₀ ≠ 0 :=
    (fundamentalCone.norm_pos_of_mem (mixedEmbedding_coneGen_mem_fundamentalCone I 𝔟)).ne'
  have hint₀ := integrable_archGaussian_mul_archNorm_cpow hx₀ hs0
  have hu_eq (u : (𝓞 K)ˣ) :
      (∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) *
          archGaussian y (idealLatticeNeZeroEquiv I (𝔟, u) : mixedSpace K) ∂archHaar K) =
        ∫ y in unitCone D, archGaussian (unitScale u y) x₀ *
          (archNorm (unitScale u y) : ℂ) ^ (s / 2) ∂archHaar K :=
    setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y _ ↦ by
      simp only [x₀, coe_idealLatticeNeZeroEquiv, archGaussian_unit_smul, archNorm_unitScale,
        mul_comm]
  simp_rw [hu_eq]
  rw [← integral_archHaar_eq_tsum_unitCone hD hint₀, nsmul_eq_mul,
    integral_archGaussian_mul_archNorm_cpow hx₀ hs0, norm_mixedEmbedding_coneGen, ofReal_mul,
    mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) hI_nonneg, ofReal_natCast, ofReal_ratCast]
  ring

open scoped Classical in
/-- **Evaluation of Hecke's cone integral on `Re s > 1`.** Over any unit fundamental domain `D`,
the covolume-rescaled cone integral of `(archNorm y) ^ (s / 2) * (θ_{σ(I)}(y) - 1)` equals the
completed partial zeta series. -/
private theorem unitCone_integral_eq_tsum {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) *
        (∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) *
          (latticeTheta (idealLattice K I) y - 1) ∂archHaar K) =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  let μ := (archHaar K).restrict (unitCone D)
  let F : {x : idealLattice K I // x ≠ 0} → realSpace K → ℂ :=
    fun x y ↦ (archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K)
  have hF_int (x : {x : idealLattice K I // x ≠ 0}) : Integrable (F x) μ :=
    integrableOn_unitCone_archNorm_cpow_mul_archGaussian D (norm_ne_zero_of_idealLatticeNeZero x)
      hs0
  have hF_sum : Summable fun x ↦ ∫ y, ‖F x y‖ ∂μ :=
    summable_setIntegral_norm_archNorm_cpow_mul_archGaussian hD I hs
  have hint_eq : (∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) *
        (latticeTheta (idealLattice K I) y - 1) ∂archHaar K) =
      ∑' x, ∫ y, F x y ∂μ := by
    refine (setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y hy ↦ ?_).trans
      (integral_tsum_of_summable_integral_norm hF_int hF_sum).symm
    rw [latticeTheta_eq_one_add _ y (mem_unitCone.mp hy).1, add_sub_cancel_left, ← tsum_mul_left]
  have hint_sum : Summable fun x ↦ ∫ y, F x y ∂μ :=
    hF_sum.of_norm_bounded fun x ↦ norm_integral_le_integral_norm (F x)
  have hprod_sum : Summable fun p : InvClassIdeal I × (𝓞 K)ˣ ↦
      ∫ y, F (idealLatticeNeZeroEquiv I p) y ∂μ :=
    (idealLatticeNeZeroEquiv I).summable_iff.mpr hint_sum
  rw [hint_eq, ← (idealLatticeNeZeroEquiv I).tsum_eq, hprod_sum.tsum_prod'
    fun 𝔟 ↦ hprod_sum.comp_injective (Prod.mk_right_injective 𝔟)]
  simp_rw [F, μ, tsum_unit_setIntegral_archGaussian hD I _ hs0, tsum_mul_left]
  rw [← mul_assoc _ _ (∑' 𝔟 : InvClassIdeal I, _), covolume_gamma_mul_eq]

end OrbitParametrization

/-! ### Identification with the Mellin functional-equation pair -/

/-- On `Re s > 1`, `(mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` equals the completed
partial zeta series of `I`. -/
theorem mellinKernelFEPair_Λ_div_two_eq_tsum {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  have hs2 : 1 / 2 < (s / 2).re := by
    rw [div_ofNat_re]
    linarith
  have hm1 := hasMellin_mellinKernel_sub_mellinConstant hD (idealLattice K I) hs2
  have hm2 := hasMellin_mellinKernel_sub hD.measurableSet hD.isBounded (idealLattice K I) s
    (integrableOn_archNorm_cpow_mul_latticeTheta_sub_one hD I hs)
  have hconst : (mellinConstant K : ℂ) = (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
      ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ) := by
    rw [mellinConstant_eq_mul_surfaceHaar_real hD]
    push_cast
    rfl
  rw [← hconst, unitCone_integral_eq_tsum hD I hs] at hm2
  exact hm1.2.symm.trans hm2.2

/-- `s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` is meromorphic on `ℂ`. -/
private theorem meromorphic_mellinKernelFEPair_Λ_div_two {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Meromorphic (fun s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)) :=
  fun z ↦ ((mellinKernelFEPair hD (idealLattice K I)).meromorphic_Λ (z / 2)).comp_analyticAt
    (g := fun w : ℂ ↦ w / 2) (analyticAt_id.div_const (c := (2 : ℂ)))

/-- Away from `0` and `1`, `s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` is analytic
at `s`. -/
private theorem analyticAt_mellinKernelFEPair_Λ_div_two {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2)) s := by
  have h0' : s / 2 ≠ 0 := div_ne_zero h0 two_ne_zero
  have h1' : s / 2 ≠ ((mellinKernelFEPair hD (idealLattice K I)).k : ℂ) := by
    simp only [mellinKernelFEPair_k, ofReal_div, ofReal_one, ofReal_ofNat]
    exact fun h ↦ h1 (by linear_combination 2 * h)
  have han : AnalyticAt ℂ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) :=
    ((mellinKernelFEPair hD (idealLattice K I)).analyticAt_Λ_iff (s / 2)).mpr ⟨.inl h0', .inl h1'⟩
  exact han.comp (f := fun w : ℂ ↦ w / 2) (analyticAt_id.div_const (c := (2 : ℂ)))

/-- **Global identification with Hecke's Mellin pair.** Over any unit fundamental domain `D`,
`completedPartialZeta I` is the whole-plane meromorphic normal form of
`s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`. -/
theorem completedPartialZeta_eq_toMeromorphicNFOn {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I =
      toMeromorphicNFOn (fun s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)) univ := by
  refine meromorphicContinuation_eq_toMeromorphicNFOn
    (meromorphic_mellinKernelFEPair_Λ_div_two hD I) (fun s (hs : 1 < s.re) ↦ ?_)
    (fun s (hs : 1 < s.re) ↦ mellinKernelFEPair_Λ_div_two_eq_tsum hD I hs)
  refine analyticAt_mellinKernelFEPair_Λ_div_two hD I ?_ ?_
  · intro h
    rw [h, zero_re] at hs
    linarith
  · intro h
    rw [h, one_re] at hs
    linarith

/-- At every point `s : ℂ` (poles included), `completedPartialZeta I` has the same punctured germ
as `z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2)`. -/
theorem completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    completedPartialZeta I =ᶠ[𝓝[≠] s]
      fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2) := by
  rw [completedPartialZeta_eq_toMeromorphicNFOn hD I]
  exact (meromorphic_mellinKernelFEPair_Λ_div_two hD I).meromorphicOn
    |>.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s)

/-- Off the poles `0` and `1`, `completedPartialZeta I s` agrees pointwise with
`(mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`. -/
theorem completedPartialZeta_eq_mellinKernelFEPair_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedPartialZeta I s = (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) := by
  rw [completedPartialZeta_eq_toMeromorphicNFOn hD I]
  exact toMeromorphicNFOn_apply_of_analyticAt (meromorphic_mellinKernelFEPair_Λ_div_two hD I)
    (analyticAt_mellinKernelFEPair_Λ_div_two hD I h0 h1)

/-! ### Half-plane and integral representations -/

/-- **Ideal-sum representation on `Re s > 1`**, Neukirch VII (5.4). -/
theorem completedPartialZeta_eq_tsum (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  have h0 : s ≠ 0 := fun h ↦ by linarith [h ▸ hs, zero_re]
  have h1 : s ≠ 1 := fun h ↦ by linarith [h ▸ hs, one_re]
  rw [completedPartialZeta_eq_mellinKernelFEPair_Λ isUnitFundamentalDomain_unitFundamentalDomain
      I h0 h1,
    mellinKernelFEPair_Λ_div_two_eq_tsum isUnitFundamentalDomain_unitFundamentalDomain I hs]

/-- **Principal-product ideal-sum representation on `Re s > 1`**: the sum runs over nonzero
integral ideals `𝔟` such that `𝔟 I = (x)` for some `x : Kˣ`. -/
theorem completedPartialZeta_eq_tsum_spanSingleton (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : Ideal (𝓞 K) // 𝔟 ≠ ⊥ ∧ ∃ x : Kˣ,
            (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  rw [completedPartialZeta_eq_tsum I hs]
  congr 1
  let e : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹} ≃
      {𝔟 : Ideal (𝓞 K) // 𝔟 ≠ ⊥ ∧ ∃ x : Kˣ,
        (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)} :=
    (Equiv.subtypeEquivRight fun 𝔟 ↦ ClassGroup.mk0_eq_inv_mk_iff I 𝔟).trans <|
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun 𝔟 : Ideal (𝓞 K) ↦ 𝔟 ∈ (Ideal (𝓞 K))⁰)
        (fun 𝔟 : Ideal (𝓞 K) ↦ ∃ x : Kˣ,
          (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K))).trans <|
        Equiv.subtypeEquivRight fun 𝔟 ↦ and_congr_left' (mem_nonZeroDivisors_iff_ne_zero (x := 𝔟))
  rw [← e.tsum_eq fun 𝔟 ↦ (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)]
  rfl

/-- **Fundamental-cone lattice-sum representation on `Re s > 1`**, Neukirch VII (5.3)–(5.4):
each ideal of class `[I]⁻¹` contributes `w = #μ(K)` generators in `fundamentalCone K`. -/
theorem completedPartialZeta_eq_tsum_fundamentalCone (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s /
        (Units.torsionOrder K : ℂ) *
        ∑' x : {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K},
          ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-s) := by
  have hI0 : ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ≠ 0 :=
    Rat.cast_ne_zero.mpr (FractionalIdeal.absNorm_eq_zero_iff.not.mpr I.ne_zero)
  have hIs : ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ s ≠ 0 := by
    rw [ne_eq, cpow_eq_zero_iff]
    exact fun h ↦ hI0 h.1
  have hw : (Units.torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Units.torsionOrder_ne_zero K)
  rw [(hasSum_norm_cpow_idealLattice_fundamentalCone I hs).tsum_eq,
    completedPartialZeta_eq_tsum I hs, cpow_neg]
  field_simp

/-- **Relation to the ray-class Dirichlet series at the trivial modulus**: for a ray class `c` of
`Modulus.one K` corresponding to `[I]⁻¹`, `completedPartialZeta I s` on `Re s > 1` is the
archimedean factor times `LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s`. -/
theorem completedPartialZeta_eq_mul_LSeries_rayClassCoeff_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {c : RayClassGroup (Modulus.one K)}
    (hc : ∀ 𝔟 : (Ideal (𝓞 K))⁰,
      idealClass (Modulus.one K) (integralIdealsPrimeToOneEquiv.symm 𝔟) = c ↔
        ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹)
    {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s := by
  classical
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective (ClassGroup.mk K I)
  have hJc : idealClass (Modulus.one K) (integralIdealsPrimeToOneEquiv.symm J) = c⁻¹ := by
    obtain ⟨𝔟₀, h𝔟₀⟩ := ClassGroup.mk0_surjective (ClassGroup.mk K I)⁻¹
    have h1 : idealClass (Modulus.one K) (integralIdealsPrimeToOneEquiv.symm 𝔟₀) = c :=
      (hc 𝔟₀).mpr h𝔟₀
    have hprod : IsPrincipal ((𝔟₀ : Ideal (𝓞 K)) * (J : Ideal (𝓞 K))) := by
      rw [← Submonoid.coe_mul, ← ClassGroup.mk0_eq_one_iff (𝔟₀ * J).2, Subtype.coe_eta, map_mul,
        h𝔟₀, hJ, inv_mul_cancel]
    have hmul1 : idealClass (Modulus.one K)
        (integralIdealsPrimeToOneEquiv.symm 𝔟₀ * integralIdealsPrimeToOneEquiv.symm J) = 1 := by
      rw [idealClass_one_eq_one_iff_isPrincipal, Submonoid.coe_mul,
        integralIdealsPrimeToOneEquiv_symm_apply_coe, integralIdealsPrimeToOneEquiv_symm_apply_coe]
      exact hprod
    rw [idealClass_mul, h1] at hmul1
    exact (inv_eq_of_mul_eq_one_right hmul1).symm
  rw [completedPartialZeta_eq_tsum I hs, LSeries_rayClassCoeff_one_eq_tsum J hJc hs]
  congr 1
  have hiff (𝔟 : (Ideal (𝓞 K))⁰) :
      ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹ ↔
        IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K))) := by
    rw [← Submonoid.coe_mul, ← ClassGroup.mk0_eq_one_iff (𝔟 * J).2, Subtype.coe_eta, map_mul, hJ,
      mul_eq_one_iff_eq_inv]
  exact (Equiv.subtypeEquivRight hiff).tsum_eq
    fun 𝔟 ↦ (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-s)

open scoped Classical in
/-- **Cone-integral representation on `Re s > 1`**, Neukirch VII (5.5): over any unit fundamental
domain `D`, `completedPartialZeta I s` is `(2 ^ r₂ / w) V_{σ(I)} ^ s` times the cone integral of
`N(y) ^ (s / 2) (θ_{σ(I)}(y) - 1)`. -/
theorem completedPartialZeta_eq_integral_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) *
        ∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) *
          (latticeTheta (idealLattice K I) y - 1) ∂archHaar K := by
  rw [completedPartialZeta_eq_tsum I hs, unitCone_integral_eq_tsum hD I hs]

/-- **Mellin-transform representation on `Re s > 1` (`HasMellin` form)**, Neukirch VII (5.5):
`completedPartialZeta I s` is the Mellin transform at `s / 2` of
`mellinKernel D (idealLattice K I) - mellinConstant K`. -/
theorem hasMellin_completedPartialZeta {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    HasMellin (fun u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K) (s / 2)
      (completedPartialZeta I s) := by
  have hs2 : 1 / 2 < (s / 2).re := by
    rw [div_ofNat_re]
    linarith
  have h0 : s ≠ 0 := fun h ↦ by linarith [h ▸ hs, zero_re]
  have h1 : s ≠ 1 := fun h ↦ by linarith [h ▸ hs, one_re]
  rw [completedPartialZeta_eq_mellinKernelFEPair_Λ hD I h0 h1]
  exact hasMellin_mellinKernel_sub_mellinConstant hD (idealLattice K I) hs2

/-- **Mellin-transform representation on `Re s > 1` (`mellin` form)**, Neukirch VII (5.5). -/
theorem completedPartialZeta_eq_mellin {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      mellin (fun u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K) (s / 2) :=
  (hasMellin_completedPartialZeta hD I hs).2.symm

/-! ### Regularity, poles, and residues -/

/-- `completedPartialZeta I` is analytic away from `s = 0` and `s = 1`. -/
theorem analyticAt_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (completedPartialZeta I) s := by
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  have hopen : IsOpen ({0, 1}ᶜ : Set ℂ) :=
    ((Set.finite_singleton (1 : ℂ)).insert 0).isClosed.isOpen_compl
  have hs : s ∈ ({0, 1}ᶜ : Set ℂ) := by simp [h0, h1]
  refine (analyticAt_mellinKernelFEPair_Λ_div_two hD I h0 h1).congr ?_
  filter_upwards [hopen.mem_nhds hs] with z hz
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
  exact (completedPartialZeta_eq_mellinKernelFEPair_Λ hD I hz.1 hz.2).symm

/-- Punctured-neighborhood convergence of `s ↦ s / 2` at any `z : ℂ`. -/
private theorem tendsto_div_two_nhdsWithin_ne (z : ℂ) :
    Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] z) (𝓝[≠] (z / 2)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (((continuous_id'.div_const (2 : ℂ)).continuousAt (x := z)).tendsto.mono_left
      nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs h
  exact hs ((div_left_inj₀ two_ne_zero).mp h)

/-- **Residue of `completedPartialZeta I` at `s = 1`**, Neukirch VII (5.9):
`lim_{s → 1} (s - 1) Z(I, s) = 2 a₀ = 2 ^ r R / w`. -/
theorem tendsto_sub_one_mul_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun s : ℂ ↦ (s - 1) * completedPartialZeta I s) (𝓝[≠] 1)
      (𝓝 (2 * mellinConstant K : ℂ)) := by
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  let P := mellinKernelFEPair hD (idealLattice K I)
  have hhalf : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 1) (𝓝[≠] ((1 / 2 : ℝ) : ℂ)) := by
    simpa only [ofReal_div, ofReal_one, ofReal_ofNat] using tendsto_div_two_nhdsWithin_ne 1
  have hres := P.Λ_residue_k
  simp only [P, mellinKernelFEPair_k, mellinKernelFEPair_ε, mellinKernelFEPair_N,
    mellinKernelFEPair_g₀, ofReal_one, one_cpow, mul_one, smul_eq_mul, one_mul] at hres
  refine ((hres.comp hhalf).const_mul 2).congr' ?_
  filter_upwards [completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ hD I 1] with s hs
  rw [Function.comp_apply, hs]
  push_cast
  ring

/-- **Residue of `completedPartialZeta I` at `s = 0`**, Neukirch VII (5.9):
`lim_{s → 0} s Z(I, s) = -2 a₀ = -2 ^ r R / w`. -/
theorem tendsto_mul_completedPartialZeta_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun s : ℂ ↦ s * completedPartialZeta I s) (𝓝[≠] 0)
      (𝓝 (-(2 * mellinConstant K : ℂ))) := by
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  let P := mellinKernelFEPair hD (idealLattice K I)
  have hhalf : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
    simpa only [zero_div] using tendsto_div_two_nhdsWithin_ne 0
  have hres := P.Λ_residue_zero
  simp only [P, mellinKernelFEPair_f₀, smul_eq_mul] at hres
  have hmul := (hres.comp hhalf).const_mul 2
  rw [mul_neg] at hmul
  refine hmul.congr' ?_
  filter_upwards [completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ hD I 0] with s hs
  rw [Function.comp_apply, hs]
  ring

/-- `completedPartialZeta I` has a simple pole at `s = 1`. -/
theorem meromorphicOrderAt_completedPartialZeta_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    meromorphicOrderAt (completedPartialZeta I) 1 = (-1 : ℤ) := by
  have ha : (2 * mellinConstant K : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr (mellinConstant_ne_zero K))
  exact (meromorphic_completedPartialZeta I 1).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul ha
    (tendsto_sub_one_mul_completedPartialZeta I)

/-- `completedPartialZeta I` has a simple pole at `s = 0`. -/
theorem meromorphicOrderAt_completedPartialZeta_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    meromorphicOrderAt (completedPartialZeta I) 0 = (-1 : ℤ) := by
  have ha : -(2 * mellinConstant K : ℂ) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr (mellinConstant_ne_zero K)))
  refine (meromorphic_completedPartialZeta I 0).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul ha
    ?_
  simpa only [sub_zero, smul_eq_mul] using tendsto_mul_completedPartialZeta_zero I

/-- `completedPartialZeta I` is analytic at `s` if and only if `s ≠ 0` and `s ≠ 1`. -/
@[simp]
theorem analyticAt_completedPartialZeta_iff (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} :
    AnalyticAt ℂ (completedPartialZeta I) s ↔ s ≠ 0 ∧ s ≠ 1 := by
  refine ⟨fun han ↦ ⟨?_, ?_⟩, fun ⟨h0, h1⟩ ↦ analyticAt_completedPartialZeta I h0 h1⟩
  · rintro rfl
    have hnonneg := han.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_completedPartialZeta_zero] at hnonneg
    exact absurd hnonneg (by decide)
  · rintro rfl
    have hnonneg := han.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_completedPartialZeta_one] at hnonneg
    exact absurd hnonneg (by decide)

/-- As a meromorphic normal form, `completedPartialZeta I` takes the canonical value `0` at its
pole `s = 0`. -/
@[simp]
theorem completedPartialZeta_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I 0 = 0 := by
  have hnf := meromorphicNFOn_completedPartialZeta I (mem_univ (0 : ℂ))
  rw [meromorphicNFAt_iff_analyticAt_or] at hnf
  rcases hnf with han | ⟨_, _, h0⟩
  · exact absurd han (by simp)
  · exact h0

/-- As a meromorphic normal form, `completedPartialZeta I` takes the canonical value `0` at its
pole `s = 1`. -/
@[simp]
theorem completedPartialZeta_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I 1 = 0 := by
  have hnf := meromorphicNFOn_completedPartialZeta I (mem_univ (1 : ℂ))
  rw [meromorphicNFAt_iff_analyticAt_or] at hnf
  rcases hnf with han | ⟨_, _, h1⟩
  · exact absurd han (by simp)
  · exact h1

/-! ### Functional equation -/

/-- **Hecke's functional equation for completed partial zeta functions**, Neukirch VII (5.9):
`Z(I, 1 - s) = Z(I^∨, s)` for every `s : ℂ` (at the poles `0` and `1` both sides take the
normal-form value `0`). -/
theorem completedPartialZeta_one_sub (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    completedPartialZeta I (1 - s) =
      completedPartialZeta (FractionalIdeal.dualEquiv ℤ ℚ I) s := by
  by_cases h0 : s = 0
  · subst h0
    simp
  by_cases h1 : s = 1
  · subst h1
    simp
  have h1s0 : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h1s1 : 1 - s ≠ 1 := fun h ↦ h0 (sub_eq_self.mp h)
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  let hD' := hD.inv.mul (traceShift_mem_normOneSurface (K := K))
  rw [completedPartialZeta_eq_mellinKernelFEPair_Λ hD I h1s0 h1s1,
    completedPartialZeta_eq_mellinKernelFEPair_Λ hD' (FractionalIdeal.dualEquiv ℤ ℚ I) h0 h1]
  have hs0 : (1 - s) / 2 ≠ 0 := div_ne_zero h1s0 two_ne_zero
  have hs1 : (1 - s) / 2 ≠ 1 / 2 := fun h ↦ h0 (by linear_combination -2 * h)
  have hsub : (1 / 2 : ℂ) - (1 - s) / 2 = s / 2 := by ring
  rw [mellinKernelFEPair_Λ_eq hD (idealLattice K I) hs0 hs1, hsub]
  have hcongr : (mellinKernelFEPair hD.inv (mixedDual K (idealLattice K I))).Λ =
      (mellinKernelFEPair hD' (idealLattice K (FractionalIdeal.dualEquiv ℤ ℚ I))).Λ := by
    rw [← FEPairWithLevel.toWeakFEPair_Λ, ← FEPairWithLevel.toWeakFEPair_Λ]
    refine WeakFEPair.Λ_congr (fun u (hu : 0 < u) ↦ ?_) (by simp) (by simp) (by simp) (by simp)
    simp only [FEPairWithLevel.toWeakFEPair_f, mellinKernelFEPair_f,
      indicator_of_mem (mem_Ioi.mpr hu)]
    exact mellinKernel_mixedDual_idealLattice (FractionalIdeal.coe_dualEquiv ℤ ℚ I) _ u
  exact congrFun hcongr (s / 2)

/-- Punctured-germ form of Hecke's functional equation at every `s : ℂ`. -/
theorem completedPartialZeta_one_sub_eventuallyEq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    (fun z ↦ completedPartialZeta I (1 - z)) =ᶠ[𝓝[≠] s]
      completedPartialZeta (FractionalIdeal.dualEquiv ℤ ℚ I) :=
  Eventually.of_forall (completedPartialZeta_one_sub I)

end TauCeti.LFunctions
