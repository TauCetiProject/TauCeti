/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.RingTheory.DedekindDomain.Different
public import TauCeti.Analysis.Meromorphic.Continuation
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.UnitQuotient
public import TauCeti.NumberTheory.LFunctions.Theta.Mellin.Pair
public import TauCeti.NumberTheory.LFunctions.Theta.UnitCone
import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.MeasureTheory.Group.FundamentalDomain
import TauCeti.MeasureTheory.Integral.DominatedConvergence
import TauCeti.NumberTheory.LFunctions.Theta.GammaIntegral
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.IdealLattice
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.TraceDual
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.UnitAction

/-!
# Completed partial zeta functions and their functional equation

Let `K` be a number field of discriminant `d_K`, with `r₁` real places, `r₂` complex places,
regulator `R`, and `w = #μ(K)` roots of unity, and let `I` be an invertible fractional ideal of `K`.
Writing `𝔎` for the ideal class `[I]⁻¹` and `ζ(𝔎, s) = ∑_{𝔟 ∈ 𝔎} N(𝔟)^(-s)` for its partial zeta
series on `Re s > 1`, Neukirch's completed partial zeta function of `I` (Chapter VII, §5) is the
meromorphic continuation of

`Z(I, s) = |d_K|^(s / 2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ([I]⁻¹, s)`.

This file defines `TauCeti.LFunctions.completedPartialZeta I` as the canonical meromorphic normal
form (`TauCeti.meromorphicContinuation 1`) of that right half-plane expression and establishes
Hecke's integral representation, meromorphic continuation, pole structure, residues, and functional
equation:

* **Unfolding on the unit cone** (`summable_integral_norm_unitCone`,
  `integrableOn_archNorm_cpow_mul_latticeTheta_sub_one`,
  `integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one`): for any unit fundamental domain `D`
  on the norm-one hypersurface, `unitCone D` is a measure-theoretic fundamental domain for the
  action of `(𝓞 K)ˣ ⧸ torsion K` on `realSpace K` with respect to `archHaar K`. Quotienting the
  nonzero points of `idealLattice K I` by `(𝓞 K)ˣ ⧸ torsion K` unfolds the norm-weighted integral of
  `latticeTheta (idealLattice K I) y - 1` over `unitCone D` into `archHaar K` Gaussian gamma
  integrals indexed by `fundamentalCone K ∩ idealLattice K I`.
* **Identification with Hecke's Mellin pair** (`mellinKernelFEPair_Λ_div_two_eq_of_one_lt_re`,
  `completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ`,
  `completedPartialZeta_eq_mellinKernelFEPair_Λ`, `completedPartialZeta_eq_mellin`,
  `completedPartialZeta_eq_integral_unitCone`): combining the cone integral with the covolume
  formula `covolume_idealLattice` and the fundamental-cone identity
  `LSeries_rayClassCoeff_one_eq_tsum_fundamentalCone` identifies `completedPartialZeta I s` with
  `(mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` on `Re s > 1`, hence as punctured
  meromorphic germs everywhere and as values away from `{0, 1}` — independently of `D`.
* **Analyticity, poles, and residues** (`analyticAt_completedPartialZeta_iff`,
  `meromorphicOrderAt_completedPartialZeta_zero`, `meromorphicOrderAt_completedPartialZeta_one`,
  `tendsto_mul_completedPartialZeta`, `tendsto_sub_one_mul_completedPartialZeta`):
  `completedPartialZeta I` is analytic away from `0` and `1`, where it has simple poles with
  residues `-2 a₀` and `2 a₀`, with `a₀ = mellinConstant K = 2^(r₁ + r₂ - 1) R / w` (so
  `2 a₀ = 2^(r₁ + r₂) R / w`).
* **Functional equation** (`completedPartialZeta_one_sub`,
  `completedPartialZeta_one_sub_eventuallyEq`): if `J` is the trace dual
  `FractionalIdeal.dual ℤ ℚ I`, then `completedPartialZeta I (1 - s) = completedPartialZeta J s` for
  all `s : ℂ` (including the canonical normal-form zero values at the poles `0` and `1`), obtained
  from `mellinKernelFEPair_Λ_eq` and `mellinKernel_mixedDual_idealLattice`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.3)–(5.9).
-/

public section

noncomputable section

open Complex Filter MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone NumberField.Units Set
  TauCeti.GlobalNumberFields TauCeti.NumberField.mixedEmbedding
open scoped Pointwise Topology nonZeroDivisors Real

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### Definition and invariance on ideal classes -/

/-- **The completed partial zeta function** attached to an invertible fractional ideal `I` of a
number field `K`, Neukirch VII (5.5): the canonical meromorphic normal-form continuation from
`Re s > 1` of `|d_K|^(s / 2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ([I]⁻¹, s)`, where `ζ([I]⁻¹, s)` is the Dirichlet
series of the ideal class `[I]⁻¹` at the trivial modulus. It depends on `I` only through its ideal
class (`completedPartialZeta_congr`). -/
def completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℂ → ℂ :=
  meromorphicContinuation 1 fun s ↦
    ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
      LSeries (normCoeff K (rayClassCoeff (Modulus.one K)
        (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹))) s

/-- Defining equation of `TauCeti.LFunctions.completedPartialZeta`. -/
theorem completedPartialZeta_def (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I = meromorphicContinuation 1 fun s ↦
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
        LSeries (normCoeff K (rayClassCoeff (Modulus.one K)
          (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹))) s :=
  (rfl)

/-- The completed partial zeta function depends on `I` only through its class in `ClassGroup`. -/
theorem completedPartialZeta_congr {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : ClassGroup.mk K I = ClassGroup.mk K J) :
    completedPartialZeta I = completedPartialZeta J := by
  simp only [completedPartialZeta_def, h]

/-- `completedPartialZeta I` is in meromorphic normal form on `ℂ`. -/
theorem meromorphicNFOn_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    MeromorphicNFOn (completedPartialZeta I) univ :=
  meromorphicNFOn_meromorphicContinuation _ _

/-- `completedPartialZeta I` is meromorphic on `ℂ`. -/
theorem meromorphic_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Meromorphic (completedPartialZeta I) :=
  meromorphicOn_univ.mp (meromorphicNFOn_completedPartialZeta I).meromorphicOn

/-! ### Unfolding the theta integral over the unit cone -/

section Unfolding

/-- The action of `(𝓞 K)ˣ ⧸ torsion K` on `realSpace K` induced by `unitScale`. Roots of unity have
absolute value `1` at every infinite place, so `unitScale` factors through the torsion quotient. -/
local instance : MulAction ((𝓞 K)ˣ ⧸ torsion K) (realSpace K) where
  smul g y := Quotient.liftOn' g (fun u ↦ unitScale u y) fun u v huv ↦ by
    have hmem : u⁻¹ * v ∈ torsion K := QuotientGroup.leftRel_apply.mp huv
    have hv : v = u * (u⁻¹ * v) := (mul_inv_cancel_left u v).symm
    ext w
    rw [unitScale_apply, unitScale_apply, hv, Units.val_mul, map_mul, map_mul,
      (mem_torsion K).mp hmem w, mul_one]
  one_smul := unitScale_one
  mul_smul g₁ g₂ y := Quotient.inductionOn₂' g₁ g₂ fun u v ↦ (unitScale_unitScale u v y).symm

@[simp]
private theorem mk_smul_realSpace (u : (𝓞 K)ˣ) (y : realSpace K) :
    (QuotientGroup.mk u : (𝓞 K)ˣ ⧸ torsion K) • y = unitScale u y :=
  (rfl)

@[simp]
private theorem archNorm_smul_realSpace (g : (𝓞 K)ˣ ⧸ torsion K) (y : realSpace K) :
    archNorm (g • y) = archNorm y :=
  Quotient.inductionOn' g fun u ↦ archNorm_unitScale u y

local instance : ContinuousConstSMul ((𝓞 K)ˣ ⧸ torsion K) (realSpace K) :=
  ⟨fun g ↦ QuotientGroup.induction_on g fun u ↦ continuous_pi fun w ↦ by
    simp only [mk_smul_realSpace, unitScale_apply]
    exact continuous_const.mul (continuous_apply w)⟩

local instance : Countable ((𝓞 K)ˣ ⧸ torsion K) := by
  have : Countable (𝓞 K) := Countable.of_moduleFinite (R := ℤ)
  have : Countable (𝓞 K)ˣ := Units.val_injective.countable
  infer_instance

local instance : SMulInvariantMeasure ((𝓞 K)ˣ ⧸ torsion K) (realSpace K) (archHaar K) :=
  ⟨fun g s hs ↦ QuotientGroup.induction_on g fun u ↦ by
    set c : realSpace K := fun w ↦ w (u : K) ^ 2
    have hmap := map_archHaar_mul_left (c := c) fun w ↦ pow_pos (pos_iff.mpr (by simp)) 2
    have heq : ((QuotientGroup.mk u : (𝓞 K)ˣ ⧸ torsion K) • ·) = (c * ·) := by
      ext y w
      simp [c, unitScale_apply]
    rw [← Measure.map_apply (measurable_const_smul _) hs, heq, hmap]⟩

/-- For any unit fundamental domain `D` on the norm-one hypersurface, the cone `unitCone D` is a
measure-theoretic fundamental domain for `(𝓞 K)ˣ ⧸ torsion K` on `realSpace K` with respect to
`archHaar K`. -/
private theorem isFundamentalDomain_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) :
    IsFundamentalDomain ((𝓞 K)ˣ ⧸ torsion K) (unitCone D) (archHaar K) := by
  refine IsFundamentalDomain.mk'' (measurableSet_unitCone hD.measurableSet).nullMeasurableSet
    ?_ ?_ fun g ↦ (measurePreserving_smul g (archHaar K)).quasiMeasurePreserving
  · filter_upwards [ae_archHaar_pos] with y hy
    obtain ⟨u, hu⟩ := hD.exists_unitScale_mem _ (surfacePart_mem_normOneSurface hy)
    exact ⟨QuotientGroup.mk u, mem_unitCone.mpr
      ⟨fun w ↦ by rw [mk_smul_realSpace]; exact unitScale_pos (hy w) u,
        by rwa [mk_smul_realSpace, surfacePart_unitScale]⟩⟩
  · intro g hg
    refine Disjoint.aedisjoint (Set.disjoint_left.mpr ?_)
    rintro y ⟨z, hz, rfl⟩ hy
    induction g using QuotientGroup.induction_on with
    | H u =>
      dsimp only at hy
      rw [mk_smul_realSpace, mem_unitCone] at hy
      have hut : u ∈ torsion K :=
        (hD.unitScale_mem_iff _ (mem_unitCone.mp hz).2 u).mp
          (by rw [← surfacePart_unitScale]; exact hy.2)
      exact hg ((QuotientGroup.eq_one_iff u).mpr hut)

/-- Choosing coset representatives `Quotient.out g` identifies
`(fundamentalCone K ∩ idealLattice K I) × ((𝓞 K)ˣ ⧸ torsion K)` bijectively with the nonzero points
of `idealLattice K I`. -/
private def coneOrbitEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (fundamentalCone K ∩ idealLattice K I : Set (mixedSpace K)) × ((𝓞 K)ˣ ⧸ torsion K) ≃
      {x : idealLattice K I // x ≠ 0} := by
  refine Equiv.ofBijective
    (fun p ↦ ⟨(Quotient.out p.2).unitSMulIdealLatticeEquiv I ⟨p.1.1, p.1.2.2⟩, fun h ↦ ?_⟩)
    ⟨?_, ?_⟩
  · have hnorm : mixedEmbedding.norm ((Quotient.out p.2 : (𝓞 K)ˣ) • (p.1 : mixedSpace K)) = 0 := by
      simpa using congrArg (fun z : idealLattice K I ↦ mixedEmbedding.norm (z : mixedSpace K)) h
    rw [norm_unit_smul] at hnorm
    exact (norm_pos_of_mem p.1.2.1).ne' hnorm
  · rintro ⟨a₁, g₁⟩ ⟨a₂, g₂⟩ h
    have hsmul : (Quotient.out g₁ : (𝓞 K)ˣ) • (a₁ : mixedSpace K) =
        (Quotient.out g₂ : (𝓞 K)ˣ) • (a₂ : mixedSpace K) := by
      simpa using congrArg (fun z : {x : idealLattice K I // x ≠ 0} ↦ (z.1 : mixedSpace K)) h
    have ha₁ : (a₁ : mixedSpace K) =
        ((Quotient.out g₁)⁻¹ * Quotient.out g₂) • (a₂ : mixedSpace K) := by
      rw [mul_smul, ← hsmul, inv_smul_smul]
    have htor : (Quotient.out g₁)⁻¹ * Quotient.out g₂ ∈ torsion K :=
      (unit_smul_mem_iff_mem_torsion a₂.2.1 _).mp (ha₁ ▸ a₁.2.1)
    have hg : g₁ = g₂ := by
      rw [← Quotient.out_eq g₁, ← Quotient.out_eq g₂]
      exact QuotientGroup.eq.mpr htor
    subst hg
    exact Prod.ext (Subtype.ext (MulAction.injective (Quotient.out g₁) hsmul)) rfl
  · rintro ⟨⟨x, hxI⟩, hx0⟩
    have hx0' : x ≠ 0 := fun h ↦ hx0 (Subtype.ext h)
    obtain ⟨v, hv⟩ := exists_unit_smul_mem ((norm_eq_zero_iff_of_mem_idealLattice hxI).not.mpr hx0')
    set g : (𝓞 K)ˣ ⧸ torsion K := QuotientGroup.mk v⁻¹
    set u : (𝓞 K)ˣ := Quotient.out g
    have htor : (v⁻¹)⁻¹ * u ∈ torsion K :=
      QuotientGroup.eq.mp (Quotient.out_eq g).symm
    have htor' : u⁻¹ * v⁻¹ ∈ torsion K := by
      simpa [mul_inv_rev] using Subgroup.inv_mem (torsion K) htor
    have ha_cone : u⁻¹ • x ∈ fundamentalCone K := by
      have heq : u⁻¹ • x = (u⁻¹ * v⁻¹) • (v • x) := by rw [mul_smul, inv_smul_smul]
      rw [heq]
      exact (unit_smul_mem_iff_mem_torsion hv _).mpr htor'
    have haI : u⁻¹ • x ∈ idealLattice K I := (u⁻¹.unitSMul_mem_idealLattice_iff I x).mpr hxI
    refine ⟨(⟨u⁻¹ • x, ha_cone, haI⟩, g), Subtype.ext (Subtype.ext ?_)⟩
    rw [Units.unitSMulIdealLatticeEquiv_apply]
    exact smul_inv_smul u x

@[simp]
private theorem coneOrbitEquiv_apply_coe (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a : (fundamentalCone K ∩ idealLattice K I : Set (mixedSpace K))) (g : (𝓞 K)ˣ ⧸ torsion K) :
    ((coneOrbitEquiv I (a, g) : {x : idealLattice K I // x ≠ 0}) : mixedSpace K) =
      (Quotient.out g : (𝓞 K)ˣ) • (a : mixedSpace K) :=
  Units.unitSMulIdealLatticeEquiv_apply _ _ _

/-- Under `coneOrbitEquiv`, the Gaussian at `y` and `coneOrbitEquiv I (a, g)` is the Gaussian at
`g • y` and `a`. -/
private theorem archGaussian_coneOrbitEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a : (fundamentalCone K ∩ idealLattice K I : Set (mixedSpace K)))
    (g : (𝓞 K)ˣ ⧸ torsion K) (y : realSpace K) :
    archGaussian y (coneOrbitEquiv I (a, g) : mixedSpace K) =
      archGaussian (g • y) (a : mixedSpace K) := by
  conv_rhs => rw [← Quotient.out_eq g]
  rw [coneOrbitEquiv_apply_coe, mk_smul_realSpace, archGaussian_unit_smul]

/-- On the positive orthant, the norm of `N(y)^(s / 2) * archGaussian y x`, cast to `ℂ`, is the
integrand at the real exponent `s.re`. -/
private theorem ofReal_norm_archNorm_cpow_mul_archGaussian {y : realSpace K} (hy : ∀ w, 0 < y w)
    (x : mixedSpace K) (s : ℂ) :
    ((‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y x‖ : ℝ) : ℂ) =
      archGaussian y x * (archNorm y : ℂ) ^ ((s.re : ℂ) / 2) := by
  have hN : 0 < archNorm y := archNorm_pos hy
  have hexp : ‖archGaussian y x‖ = Real.exp (-π * ∑ w, y w * normAtPlace w x ^ 2) := by
    rw [archGaussian_apply, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hre : (s / 2).re = s.re / 2 := by simp
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hN, hre, hexp, ofReal_mul, ofReal_cpow hN.le,
    ofReal_div, ofReal_ofNat, archGaussian_apply, mul_comm]

/-- For `Re s > 0` and `N(x) ≠ 0`, `y ↦ ‖N(y)^(s / 2) * archGaussian y x‖` is integrable on
`realSpace K` with respect to `archHaar K`. -/
private theorem integrable_norm_archNorm_cpow_mul_archGaussian {x : mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun y ↦ ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y x‖) (archHaar K) := by
  have hs0 : 0 < (s.re : ℂ).re := by simpa using hs
  have hintC := integrable_archGaussian_mul_archNorm_cpow hx hs0
  refine (Complex.reCLM.integrable_comp hintC).congr ?_
  filter_upwards [ae_archHaar_pos] with y hy
  have h := congrArg Complex.re (ofReal_norm_archNorm_cpow_mul_archGaussian hy x s)
  simpa only [ofReal_re, Complex.reCLM_apply] using h.symm

/-- Evaluation of the whole-orthant `L¹` norm of `N(y)^(s / 2) * archGaussian y x` at a cone point
`a` with `N(a) > 0`. -/
private theorem integral_norm_archNorm_cpow_mul_archGaussian {x : mixedSpace K}
    (hx : 0 < mixedEmbedding.norm x) {s : ℂ} (hs : 0 < s.re) :
    ∫ y, ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y x‖ ∂archHaar K =
      (Gammaℝ s.re ^ nrRealPlaces K * Gammaℝ (2 * s.re) ^ nrComplexPlaces K).re *
        mixedEmbedding.norm x ^ (-s.re) := by
  have hs0 : 0 < (s.re : ℂ).re := by simpa using hs
  have hintC := integrable_archGaussian_mul_archNorm_cpow hx.ne' hs0
  have hae : (fun y ↦ ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y x‖) =ᵐ[archHaar K]
      fun y ↦ Complex.reCLM (archGaussian y x * (archNorm y : ℂ) ^ ((s.re : ℂ) / 2)) := by
    filter_upwards [ae_archHaar_pos] with y hy
    simpa only [ofReal_re, Complex.reCLM_apply] using
      congrArg Complex.re (ofReal_norm_archNorm_cpow_mul_archGaussian hy x s)
  rw [integral_congr_ae hae, Complex.reCLM.integral_comp_comm hintC, Complex.reCLM_apply,
    integral_archGaussian_mul_archNorm_cpow hx.ne' hs0, ← ofReal_neg, ← ofReal_cpow hx.le]
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]

/-- For `Re s > 1` and a unit fundamental domain `D`, the `L¹` norms on `unitCone D` of the
archimedean Gaussians at nonzero points of `idealLattice K I` are summable. -/
theorem summable_integral_norm_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    Summable fun x : {x : idealLattice K I // x ≠ 0} ↦
      ∫ y in unitCone D, ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K)‖
        ∂archHaar K := by
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  refine (coneOrbitEquiv I).summable_iff.mp ((summable_prod_of_nonneg
    fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _).mpr ⟨fun a ↦ ?_, ?_⟩)
  · have hintR := integrable_norm_archNorm_cpow_mul_archGaussian (norm_pos_of_mem a.2.1).ne' hs0
    refine ((isFundamentalDomain_unitCone hD).hasSum_setIntegral_smul hintR).summable.congr
      fun g ↦ setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y _ ↦ ?_
    rw [archNorm_smul_realSpace, archGaussian_coneOrbitEquiv]
  · set c : ℝ := (Gammaℝ s.re ^ nrRealPlaces K * Gammaℝ (2 * s.re) ^ nrComplexPlaces K).re
    have hcone : Summable fun a : (fundamentalCone K ∩ idealLattice K I : Set (mixedSpace K)) ↦
        c * mixedEmbedding.norm (a : mixedSpace K) ^ (-s.re) := by
      refine ((hasSum_norm_cpow_fundamentalCone I (s := (s.re : ℂ))
        (by simpa using hs)).summable.norm.mul_left c).congr fun a ↦ ?_
      rw [norm_cpow_eq_rpow_re_of_pos (norm_pos_of_mem a.2.1), neg_re, ofReal_re]
    refine hcone.congr fun a ↦ ?_
    have hintR := integrable_norm_archNorm_cpow_mul_archGaussian (norm_pos_of_mem a.2.1).ne' hs0
    have hsum_g : (∑' g : (𝓞 K)ˣ ⧸ torsion K, ∫ y in unitCone D,
        ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y (coneOrbitEquiv I (a, g) : mixedSpace K)‖
          ∂archHaar K) =
        ∫ y, ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y (a : mixedSpace K)‖ ∂archHaar K := by
      refine (((isFundamentalDomain_unitCone hD).hasSum_setIntegral_smul hintR).congr_fun fun g ↦
        setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y _ ↦ ?_).tsum_eq
      rw [archNorm_smul_realSpace, archGaussian_coneOrbitEquiv]
    rw [hsum_g, integral_norm_archNorm_cpow_mul_archGaussian (norm_pos_of_mem a.2.1) hs0]

/-- **Absolute integrability of Hecke's cone integral.** For `Re s > 1` and a unit fundamental
domain `D`, the norm-weighted theta series `N(y)^(s / 2) * (θ_{σ(I)}(y) - 1)` of an ideal lattice is
integrable on `unitCone D` with respect to `archHaar K`. -/
theorem integrableOn_archNorm_cpow_mul_latticeTheta_sub_one {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1))
      (unitCone D) (archHaar K) := by
  have : Countable (idealLattice K I) := Countable.of_moduleFinite (R := ℤ)
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  set F : {x : idealLattice K I // x ≠ 0} → realSpace K → ℂ :=
    fun x y ↦ (archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K)
  have hF_int (x : {x : idealLattice K I // x ≠ 0}) :
      Integrable (F x) ((archHaar K).restrict (unitCone D)) := by
    have hx0 : (x : mixedSpace K) ≠ 0 := fun h ↦ x.2 (Subtype.ext h)
    have hint := (integrable_archGaussian_mul_archNorm_cpow
      ((norm_eq_zero_iff_of_mem_idealLattice x.1.2).not.mpr hx0) hs0).restrict (s := unitCone D)
    exact hint.congr (Filter.Eventually.of_forall fun _ ↦ mul_comm _ _)
  have htsum := TauCeti.integrable_tsum_of_summable_integral_norm hF_int
    (summable_integral_norm_unitCone hD I hs)
  refine htsum.congr ?_
  filter_upwards [ae_restrict_mem (measurableSet_unitCone hD.measurableSet)] with y hy
  simp only [F]
  rw [tsum_mul_left, latticeTheta_eq_one_add (idealLattice K I) y (mem_unitCone.mp hy).1,
    add_sub_cancel_left]

/-- **Hecke's unfolding on the unit cone.** For `Re s > 1` and any unit fundamental domain `D`, the
integral of `N(y)^(s / 2) * (θ_{σ(I)}(y) - 1)` over `unitCone D` unfolds to `Γ_ℝ(s)^r₁ Γ_ℝ(2s)^r₂`
times the fundamental-cone sum `∑_{x ∈ σ(I) ∩ cone} |N(x)|^(-s)`. -/
theorem integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    ∫ y in unitCone D,
        (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1) ∂archHaar K =
      Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
        ∑' a : (fundamentalCone K ∩ idealLattice K I : Set (mixedSpace K)),
          ((mixedEmbedding.norm (a : mixedSpace K) : ℝ) : ℂ) ^ (-s) := by
  have : Countable (idealLattice K I) := Countable.of_moduleFinite (R := ℤ)
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  set F : {x : idealLattice K I // x ≠ 0} → realSpace K → ℂ :=
    fun x y ↦ (archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K)
  have hF_int (x : {x : idealLattice K I // x ≠ 0}) :
      Integrable (F x) ((archHaar K).restrict (unitCone D)) := by
    have hx0 : (x : mixedSpace K) ≠ 0 := fun h ↦ x.2 (Subtype.ext h)
    exact ((integrable_archGaussian_mul_archNorm_cpow
      ((norm_eq_zero_iff_of_mem_idealLattice x.1.2).not.mpr hx0) hs0).restrict
        (s := unitCone D)).congr (Filter.Eventually.of_forall fun _ ↦ mul_comm _ _)
  have hcongr : ∫ y in unitCone D, (∑' x, F x y) ∂archHaar K =
      ∫ y in unitCone D,
        (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1) ∂archHaar K := by
    refine setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y hy ↦ ?_
    simp only [F]
    rw [tsum_mul_left, latticeTheta_eq_one_add (idealLattice K I) y (mem_unitCone.mp hy).1,
      add_sub_cancel_left]
  have hsum_x : HasSum (fun x ↦ ∫ y in unitCone D, F x y ∂archHaar K)
      (∫ y in unitCone D,
        (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1) ∂archHaar K) :=
    hcongr ▸ hasSum_integral_of_summable_integral_norm hF_int
      (summable_integral_norm_unitCone hD I hs)
  have hsum_p := (coneOrbitEquiv I).hasSum_iff.mpr hsum_x
  have hfib (a : (fundamentalCone K ∩ idealLattice K I : Set (mixedSpace K))) :
      HasSum (fun g : (𝓞 K)ˣ ⧸ torsion K ↦
          ∫ y in unitCone D, F (coneOrbitEquiv I (a, g)) y ∂archHaar K)
        (Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
          ((mixedEmbedding.norm (a : mixedSpace K) : ℝ) : ℂ) ^ (-s)) := by
    have hint_a : Integrable (fun y ↦ (archNorm y : ℂ) ^ (s / 2) *
        archGaussian y (a : mixedSpace K)) (archHaar K) :=
      (integrable_archGaussian_mul_archNorm_cpow (norm_pos_of_mem a.2.1).ne' hs0).congr
        (Filter.Eventually.of_forall fun _ ↦ mul_comm _ _)
    have hval_a : ∫ y, (archNorm y : ℂ) ^ (s / 2) * archGaussian y (a : mixedSpace K) ∂archHaar K =
        Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
          ((mixedEmbedding.norm (a : mixedSpace K) : ℝ) : ℂ) ^ (-s) := by
      rw [← integral_archGaussian_mul_archNorm_cpow (norm_pos_of_mem a.2.1).ne' hs0]
      exact integral_congr_ae (Filter.Eventually.of_forall fun _ ↦ mul_comm _ _)
    rw [← hval_a]
    refine ((isFundamentalDomain_unitCone hD).hasSum_setIntegral_smul hint_a).congr_fun fun g ↦
      setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y _ ↦ ?_
    simp only [F, archNorm_smul_realSpace, archGaussian_coneOrbitEquiv]
  rw [← tsum_mul_left]
  exact (hsum_p.prod_fiberwise hfib).tsum_eq.symm

open scoped Classical in
/-- Covolume factor in Hecke's integral:
`(covolume σ(I)²)^(s / 2) = N(I)^s (2⁻¹)^(r₂ s) |d_K|^(s / 2)`. -/
private theorem covolume_idealLattice_sq_cpow_div_two (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) =
      (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℂ) ^ s *
        (((2⁻¹ : ℝ) : ℂ) ^ s) ^ nrComplexPlaces K * ((|discr K| : ℤ) : ℂ) ^ (s / 2) := by
  set nI : ℝ := (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
  have hnI : 0 ≤ nI := Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)
  have h2r : 0 ≤ ((2⁻¹ : ℝ) ^ nrComplexPlaces K) := by positivity
  have hsq : ZLattice.covolume (idealLattice K I) ^ 2 =
      nI ^ 2 * ((2⁻¹ : ℝ) ^ nrComplexPlaces K) ^ 2 * ((|discr K| : ℤ) : ℝ) := by
    rw [covolume_idealLattice]
    have hsqrt : (√|(discr K : ℝ)|) ^ 2 = ((|discr K| : ℤ) : ℝ) := by
      rw [Real.sq_sqrt (abs_nonneg _), ← Int.cast_abs]
    calc (nI * (2⁻¹ : ℝ) ^ nrComplexPlaces K * √|(discr K : ℝ)|) ^ 2
        = nI ^ 2 * ((2⁻¹ : ℝ) ^ nrComplexPlaces K) ^ 2 * (√|(discr K : ℝ)|) ^ 2 := by ring
      _ = _ := by rw [hsqrt]
  have h2s : (2 : ℕ) * (s / 2) = s := by push_cast; ring
  have hpow2 : (((2⁻¹ : ℝ) ^ nrComplexPlaces K : ℝ) : ℂ) ^ s =
      (((2⁻¹ : ℝ) : ℂ) ^ s) ^ nrComplexPlaces K := by
    rw [ofReal_pow, TauCeti.ofReal_pow_cpow (by positivity), mul_comm, cpow_mul_nat]
  rw [← ofReal_pow, hsq, ofReal_mul,
    TauCeti.ofReal_mul_cpow (mul_nonneg (sq_nonneg _) (sq_nonneg _)), ofReal_mul,
    TauCeti.ofReal_mul_cpow (sq_nonneg _), ofReal_pow, TauCeti.ofReal_pow_cpow hnI,
    ofReal_pow ((2⁻¹ : ℝ) ^ nrComplexPlaces K), TauCeti.ofReal_pow_cpow h2r, h2s, hpow2,
    ofReal_intCast]
  simp only [nI, ofReal_ratCast]

open scoped Classical in
/-- **Hecke's Mellin formula on `Re s > 1`** (Neukirch VII (5.5)): for any unit fundamental domain
`D`, `(mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` equals
`|d_K|^(s / 2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ([I]⁻¹, s)` on `Re s > 1`. -/
theorem mellinKernelFEPair_Λ_div_two_eq_of_one_lt_re {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
        LSeries (normCoeff K (rayClassCoeff (Modulus.one K)
          (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹))) s := by
  have hs2 : 1 / 2 < (s / 2).re := by
    have : (s / 2).re = s.re / 2 := by simp
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
  have hΛ : (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) =
      (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
        (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) *
          ∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) *
            (latticeTheta (idealLattice K I) y - 1) ∂archHaar K :=
    hm1.2.symm.trans hm2.2
  have hGammaC : (2 : ℂ) ^ nrComplexPlaces K * (((2⁻¹ : ℝ) : ℂ) ^ s) ^ nrComplexPlaces K *
      Gammaℝ (2 * s) ^ nrComplexPlaces K = Gammaℂ s ^ nrComplexPlaces K := by
    rw [← mul_pow, ← mul_pow, two_mul_inv_two_cpow_mul_Gammaℝ_two_mul]
  rw [hΛ, integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one hD I hs,
    covolume_idealLattice_sq_cpow_div_two,
    LSeries_rayClassCoeff_one_eq_tsum_fundamentalCone I (oneEquivClassGroup.apply_symm_apply _) hs,
    ← hGammaC]
  set S : ℂ := ∑' a : (fundamentalCone K ∩ idealLattice K I : Set (mixedSpace K)),
    ((mixedEmbedding.norm (a : mixedSpace K) : ℝ) : ℂ) ^ (-s)
  ring

end Unfolding

/-! ### Meromorphic continuation and right half-plane formulas -/

open scoped Classical in
private theorem analyticAt_mellinKernelFEPair_Λ_div_two {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2)) s := by
  have hopen : IsOpen ({(0 : ℂ), 1} : Set ℂ)ᶜ :=
    ((Set.finite_singleton (1 : ℂ)).insert 0).isClosed.isOpen_compl
  refine (DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hopen) s (by simp [h0, h1])
  obtain ⟨hz0', hz1'⟩ : z ≠ 0 ∧ z ≠ 1 := by simpa [not_or] using hz
  have hz0 : z / 2 ≠ 0 := div_ne_zero hz0' two_ne_zero
  have hz1 : z / 2 ≠ ((mellinKernelFEPair hD (idealLattice K I)).k : ℂ) := by
    rw [mellinKernelFEPair_k]
    push_cast
    exact fun h ↦ hz1' (by linear_combination 2 * h)
  exact (((mellinKernelFEPair hD (idealLattice K I)).differentiableAt_Λ
    (.inl hz0) (.inl hz1)).comp z (differentiableAt_id.div_const 2)).differentiableWithinAt

open scoped Classical in
private theorem meromorphic_mellinKernelFEPair_Λ_div_two {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Meromorphic fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2) := fun z ↦ by
  have hg : AnalyticAt ℂ (fun w : ℂ ↦ w / 2) z := analyticAt_id.div analyticAt_const two_ne_zero
  exact MeromorphicAt.comp_analyticAt
    (f := (mellinKernelFEPair hD (idealLattice K I)).Λ) (g := fun w : ℂ ↦ w / 2)
    ((mellinKernelFEPair hD (idealLattice K I)).meromorphic_Λ (z / 2)) hg

open scoped Classical in
/-- **Identification of `completedPartialZeta` with Hecke's Mellin pair, as germs.** For any unit
fundamental domain `D` and every `s : ℂ` (the poles `0` and `1` included), `completedPartialZeta I`
has the punctured germ of `z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2)`. -/
theorem completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    completedPartialZeta I =ᶠ[𝓝[≠] s]
      fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2) := by
  rw [completedPartialZeta_def]
  exact meromorphicContinuation_eventuallyEq (meromorphic_mellinKernelFEPair_Λ_div_two hD I)
    (fun _ hz ↦ analyticAt_mellinKernelFEPair_Λ_div_two hD I
      (ne_zero_of_re_pos (zero_lt_one.trans hz)) (ne_of_apply_ne re (by simpa using hz.ne')))
    (fun _ hz ↦ mellinKernelFEPair_Λ_div_two_eq_of_one_lt_re hD I hz) s

open scoped Classical in
/-- **Identification of `completedPartialZeta` with Hecke's Mellin pair off the poles.** For any
unit fundamental domain `D` and `s ≠ 0, 1`,
`completedPartialZeta I s = (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`. -/
theorem completedPartialZeta_eq_mellinKernelFEPair_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedPartialZeta I s = (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) := by
  rw [completedPartialZeta_def]
  exact meromorphicContinuation_apply (meromorphic_mellinKernelFEPair_Λ_div_two hD I)
    (fun _ hz ↦ analyticAt_mellinKernelFEPair_Λ_div_two hD I
      (ne_zero_of_re_pos (zero_lt_one.trans hz)) (ne_of_apply_ne re (by simpa using hz.ne')))
    (fun _ hz ↦ mellinKernelFEPair_Λ_div_two_eq_of_one_lt_re hD I hz)
    (analyticAt_mellinKernelFEPair_Λ_div_two hD I h0 h1)

/-- On `Re s > 1`, `completedPartialZeta I s` agrees with the completed Dirichlet series
`|d_K|^(s / 2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ([I]⁻¹, s)`. -/
theorem completedPartialZeta_eq_LSeries (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
        LSeries (normCoeff K (rayClassCoeff (Modulus.one K)
          (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹))) s := by
  rw [completedPartialZeta_eq_mellinKernelFEPair_Λ isUnitFundamentalDomain_unitFundamentalDomain I
    (ne_zero_of_re_pos (zero_lt_one.trans hs)) (ne_of_apply_ne re (by simpa using hs.ne')),
    mellinKernelFEPair_Λ_div_two_eq_of_one_lt_re isUnitFundamentalDomain_unitFundamentalDomain I hs]

/-- On `Re s > 1`, `completedPartialZeta I s` is `|d_K|^(s / 2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂` times the sum
of `N(𝔟)^(-s)` over the nonzero integral ideals `𝔟` whose product `𝔟 I` is principal. -/
theorem completedPartialZeta_eq_tsum (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ //
            Submodule.IsPrincipal (((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
              (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  rw [completedPartialZeta_eq_LSeries I hs,
    LSeries_rayClassCoeff_one_eq_tsum_fractionalIdeal I
      (oneEquivClassGroup.apply_symm_apply _) hs]

/-- On `Re s > 1`, `completedPartialZeta I s` is written directly as a sum over the points of
`idealLattice K I` in Mathlib's fundamental cone (Neukirch VII (5.3)–(5.4)). -/
theorem completedPartialZeta_eq_tsum_fundamentalCone (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K *
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℂ) ^ s / torsionOrder K *
          ∑' a : (fundamentalCone K ∩ idealLattice K I : Set (mixedSpace K)),
            ((mixedEmbedding.norm (a : mixedSpace K) : ℝ) : ℂ) ^ (-s)) := by
  rw [completedPartialZeta_eq_LSeries I hs,
    LSeries_rayClassCoeff_one_eq_tsum_fundamentalCone I
      (oneEquivClassGroup.apply_symm_apply _) hs]

open scoped Classical in
/-- **Mellin integral representation of `completedPartialZeta`** (Neukirch VII (5.5)): on
`Re s > 1`, for any unit fundamental domain `D`, `completedPartialZeta I s` is the Mellin transform
at `s / 2` of `mellinKernel D (idealLattice K I) - mellinConstant K`. -/
theorem hasMellin_completedPartialZeta {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K) (s / 2)
      (completedPartialZeta I s) := by
  have hs2 : 1 / 2 < (s / 2).re := by
    have : (s / 2).re = s.re / 2 := by simp
    linarith
  rw [completedPartialZeta_eq_mellinKernelFEPair_Λ hD I
    (ne_zero_of_re_pos (zero_lt_one.trans hs)) (ne_of_apply_ne re (by simpa using hs.ne'))]
  exact hasMellin_mellinKernel_sub_mellinConstant hD (idealLattice K I) hs2

open scoped Classical in
/-- **Mellin formula for `completedPartialZeta`** (Neukirch VII (5.5)): on `Re s > 1`, for any unit
fundamental domain `D`, `completedPartialZeta I s` equals
`mellin (fun u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K) (s / 2)`. -/
theorem completedPartialZeta_eq_mellin {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta I s =
      mellin (fun u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K) (s / 2) :=
  (hasMellin_completedPartialZeta hD I hs).2.symm

open scoped Classical in
/-- **Cone integral representation of `completedPartialZeta`**: on `Re s > 1`, for any unit
fundamental domain `D`, `completedPartialZeta I s` is `(2^r₂ / w) V_{σ(I)}^s` times the integral of
`N(y)^(s / 2) * (θ_{σ(I)}(y) - 1)` over `unitCone D`. -/
theorem completedPartialZeta_eq_integral_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta I s =
      (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
        (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) *
          ∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) *
            (latticeTheta (idealLattice K I) y - 1) ∂archHaar K := by
  have hm1 := hasMellin_completedPartialZeta hD I hs
  have hm2 := hasMellin_mellinKernel_sub hD.measurableSet hD.isBounded (idealLattice K I) s
    (integrableOn_archNorm_cpow_mul_latticeTheta_sub_one hD I hs)
  have hconst : (mellinConstant K : ℂ) =
      (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
        ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ) := by
    rw [mellinConstant_eq_mul_surfaceHaar_real hD]
    push_cast
    rfl
  rw [← hconst] at hm2
  exact hm1.2.symm.trans hm2.2

/-! ### Analyticity, simple poles, and residues at `s = 0` and `s = 1` -/

/-- `completedPartialZeta I` has a simple pole at `s = 0`. -/
theorem meromorphicOrderAt_completedPartialZeta_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    meromorphicOrderAt (completedPartialZeta I) 0 = (-1 : ℤ) := by
  classical
  set P := mellinKernelFEPair (isUnitFundamentalDomain_unitFundamentalDomain (K := K))
    (idealLattice K I)
  have hderiv : deriv (fun z : ℂ ↦ z / 2) 0 ≠ 0 := by
    rw [((hasDerivAt_id' (0 : ℂ)).div_const 2).deriv]
    norm_num
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero (f := P.Λ) (g := fun z : ℂ ↦ z / 2)
    (x := 0) (analyticAt_id.div analyticAt_const two_ne_zero) hderiv
  have hf₀ : P.f₀ ≠ 0 := by simp [P]
  rw [meromorphicOrderAt_congr (completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ
    isUnitFundamentalDomain_unitFundamentalDomain I 0), ← Function.comp_def, hcomp, zero_div,
    P.meromorphicOrderAt_Λ_zero hf₀]

/-- `completedPartialZeta I` has a simple pole at `s = 1`. -/
theorem meromorphicOrderAt_completedPartialZeta_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    meromorphicOrderAt (completedPartialZeta I) 1 = (-1 : ℤ) := by
  classical
  set P := mellinKernelFEPair (isUnitFundamentalDomain_unitFundamentalDomain (K := K))
    (idealLattice K I)
  have hderiv : deriv (fun z : ℂ ↦ z / 2) 1 ≠ 0 := by
    rw [((hasDerivAt_id' (1 : ℂ)).div_const 2).deriv]
    norm_num
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero (f := P.Λ) (g := fun z : ℂ ↦ z / 2)
    (x := 1) (analyticAt_id.div analyticAt_const two_ne_zero) hderiv
  have hg₀ : P.g₀ ≠ 0 := by simp [P]
  have hk : ((1 : ℂ) / 2) = (P.k : ℂ) := by simp [P]
  rw [meromorphicOrderAt_congr (completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ
    isUnitFundamentalDomain_unitFundamentalDomain I 1), ← Function.comp_def, hcomp, hk,
    P.meromorphicOrderAt_Λ_k hg₀]

/-- `completedPartialZeta I` is analytic away from `0` and `1`. -/
theorem analyticAt_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (completedPartialZeta I) s := by
  classical
  have hnf := (meromorphicNFOn_completedPartialZeta I) (mem_univ s)
  have h := analyticAt_mellinKernelFEPair_Λ_div_two
    (isUnitFundamentalDomain_unitFundamentalDomain (K := K)) I h0 h1
  rw [← hnf.meromorphicOrderAt_nonneg_iff_analyticAt,
    meromorphicOrderAt_congr (completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ
      isUnitFundamentalDomain_unitFundamentalDomain I s)]
  exact h.meromorphicOrderAt_nonneg

/-- `completedPartialZeta I` is analytic at `s` if and only if `s ≠ 0` and `s ≠ 1`. -/
@[simp]
theorem analyticAt_completedPartialZeta_iff (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} :
    AnalyticAt ℂ (completedPartialZeta I) s ↔ s ≠ 0 ∧ s ≠ 1 := by
  refine ⟨fun ha ↦ ⟨?_, ?_⟩, fun ⟨h0, h1⟩ ↦ analyticAt_completedPartialZeta I h0 h1⟩
  · rintro rfl
    have h := ha.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_completedPartialZeta_zero] at h
    exact absurd h (by decide)
  · rintro rfl
    have h := ha.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_completedPartialZeta_one] at h
    exact absurd h (by decide)

variable (K) in
/-- Twice Neukirch's constant term `a₀ = mellinConstant K` is `2^(r₁ + r₂) R / w`. -/
theorem two_mul_mellinConstant :
    2 * mellinConstant K =
      2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K / torsionOrder K := by
  have hcard : 0 < nrRealPlaces K + nrComplexPlaces K := by
    rw [← card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hcard.ne'
  rw [mellinConstant_def, hm, Nat.succ_sub_one, pow_succ']
  ring

/-- **Residue of `completedPartialZeta` at `s = 0`** (Neukirch VII (5.9)): as `s → 0` with `s ≠ 0`,
`s * completedPartialZeta I s` tends to `-2 * mellinConstant K = -2^(r₁ + r₂) R / w`. -/
theorem tendsto_mul_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun s : ℂ ↦ s * completedPartialZeta I s) (𝓝[≠] 0)
      (𝓝 (-2 * (mellinConstant K : ℂ))) := by
  classical
  set P := mellinKernelFEPair (isUnitFundamentalDomain_unitFundamentalDomain (K := K))
    (idealLattice K I)
  have hdiv0 : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 0) (𝓝 0) := by
    simpa using ((continuous_id.div_const (2 : ℂ)).tendsto 0).mono_left nhdsWithin_le_nhds
  have hdiv : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hdiv0,
      eventually_nhdsWithin_of_forall fun s hs ↦ div_ne_zero hs two_ne_zero⟩
  have hres := (P.Λ_residue_zero.comp hdiv).const_mul (2 : ℂ)
  simp only [P, mellinKernelFEPair_f₀, smul_eq_mul, mul_neg, Function.comp_apply] at hres
  have hlim : -(2 * (mellinConstant K : ℂ)) = -2 * (mellinConstant K : ℂ) := by ring
  rw [hlim] at hres
  refine hres.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    eventually_ne_nhdsWithin (zero_ne_one (α := ℂ))] with s hs0 hs1
  rw [completedPartialZeta_eq_mellinKernelFEPair_Λ
    isUnitFundamentalDomain_unitFundamentalDomain I hs0 hs1]
  ring

/-- **Residue of `completedPartialZeta` at `s = 1`** (Neukirch VII (5.9)): as `s → 1` with `s ≠ 1`,
`(s - 1) * completedPartialZeta I s` tends to `2 * mellinConstant K = 2^(r₁ + r₂) R / w`. -/
theorem tendsto_sub_one_mul_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun s : ℂ ↦ (s - 1) * completedPartialZeta I s) (𝓝[≠] 1)
      (𝓝 (2 * (mellinConstant K : ℂ))) := by
  classical
  set P := mellinKernelFEPair (isUnitFundamentalDomain_unitFundamentalDomain (K := K))
    (idealLattice K I)
  have hk : (P.k : ℂ) = 1 / 2 := by simp [P]
  have hdiv1 : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 1) (𝓝 (1 / 2)) :=
    ((continuous_id.div_const (2 : ℂ)).tendsto 1).mono_left nhdsWithin_le_nhds
  have hdiv : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 1) (𝓝[≠] (P.k : ℂ)) := by
    rw [hk]
    exact tendsto_nhdsWithin_iff.mpr ⟨hdiv1, eventually_nhdsWithin_of_forall
      fun s (hs : s ≠ 1) (h : s / 2 = 1 / 2) ↦ hs (by linear_combination 2 * h)⟩
  have hres := (P.Λ_residue_k.comp hdiv).const_mul (2 : ℂ)
  simp only [P, mellinKernelFEPair_ε, mellinKernelFEPair_N, mellinKernelFEPair_g₀,
    mellinKernelFEPair_k, ofReal_one, one_cpow, mul_one, one_mul, smul_eq_mul,
    Function.comp_apply] at hres
  refine hres.congr' ?_
  filter_upwards [eventually_ne_nhdsWithin (one_ne_zero (α := ℂ)),
    self_mem_nhdsWithin] with s hs0 hs1
  rw [completedPartialZeta_eq_mellinKernelFEPair_Λ
    isUnitFundamentalDomain_unitFundamentalDomain I hs0 hs1]
  push_cast
  ring

/-! ### The functional equation against the trace dual -/

/-- **The functional equation of `completedPartialZeta`** (Neukirch VII (5.9)): if `J` is the trace
dual `FractionalIdeal.dual ℤ ℚ I` of an invertible fractional ideal `I`, then
`completedPartialZeta I (1 - s) = completedPartialZeta J s` for all `s : ℂ` (including the canonical
normal-form values `0` at the poles `0` and `1`). -/
theorem completedPartialZeta_one_sub {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    (s : ℂ) :
    completedPartialZeta I (1 - s) = completedPartialZeta J s := by
  classical
  have hnf_sub : MeromorphicNFOn (fun z ↦ completedPartialZeta I (1 - z)) univ := fun z _ ↦ by
    have hderiv : deriv (fun w : ℂ ↦ 1 - w) z ≠ 0 := by
      rw [deriv_const_sub_id (1 : ℂ)]
      norm_num
    exact (meromorphicNFAt_comp_iff_of_deriv_ne_zero (f := completedPartialZeta I)
      (g := fun w : ℂ ↦ 1 - w) (by fun_prop) hderiv).mpr
      (meromorphicNFOn_completedPartialZeta I (mem_univ (1 - z)))
  refine congrFun (eq_of_meromorphicNFOn_of_eqOn_halfPlane (σ := 1) hnf_sub
    (meromorphicNFOn_completedPartialZeta J) fun z (hz : 1 < z.re) ↦ ?_) s
  set D := unitFundamentalDomain K
  have hD : IsUnitFundamentalDomain K D := isUnitFundamentalDomain_unitFundamentalDomain
  have hD' : IsUnitFundamentalDomain K ((traceShift K * ·) '' D⁻¹) :=
    hD.inv.mul traceShift_mem_normOneSurface
  have hΛ : (mellinKernelFEPair hD.inv (mixedDual K (idealLattice K I))).Λ =
      (mellinKernelFEPair hD' (idealLattice K J)).Λ := by
    rw [← FEPairWithLevel.toWeakFEPair_Λ, ← FEPairWithLevel.toWeakFEPair_Λ]
    refine WeakFEPair.Λ_congr (fun u hu ↦ ?_) (by simp) (by simp) (by simp) (by simp)
    simp [indicator_of_mem hu, mellinKernel_mixedDual_idealLattice hJ D⁻¹ u]
  have hz0 : z ≠ 0 := ne_zero_of_re_pos (zero_lt_one.trans hz)
  have hz1 : z ≠ 1 := ne_of_apply_ne re (by simpa using hz.ne')
  have h1z0 : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  have h1z1 : 1 - z ≠ 1 := fun h ↦ hz0 (by linear_combination -h)
  have hd0 : (1 - z) / 2 ≠ 0 := div_ne_zero h1z0 two_ne_zero
  have hd1 : (1 - z) / 2 ≠ 1 / 2 := fun h ↦ hz0 (by linear_combination -2 * h)
  have hsub : 1 / 2 - (1 - z) / 2 = z / 2 := by ring
  rw [completedPartialZeta_eq_mellinKernelFEPair_Λ hD I h1z0 h1z1,
    mellinKernelFEPair_Λ_eq hD (idealLattice K I) hd0 hd1, hsub, hΛ,
    completedPartialZeta_eq_mellinKernelFEPair_Λ hD' J hz0 hz1]

/-- **The functional equation of `completedPartialZeta`, as punctured germs.** At every `s : ℂ`,
`z ↦ completedPartialZeta I (1 - z)` and `completedPartialZeta J` have the same punctured germ when
`J` is the trace dual of `I`. -/
theorem completedPartialZeta_one_sub_eventuallyEq {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    (s : ℂ) :
    (fun z ↦ completedPartialZeta I (1 - z)) =ᶠ[𝓝[≠] s] completedPartialZeta J :=
  Filter.Eventually.of_forall (completedPartialZeta_one_sub hJ)

end TauCeti.LFunctions
