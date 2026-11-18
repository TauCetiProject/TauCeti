/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.UnitQuotient
public import TauCeti.NumberTheory.LFunctions.Theta.Mellin.Pair
public import TauCeti.NumberTheory.LFunctions.Theta.UnitCone
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.IdealLattice

/-!
# Hecke's unfolding of the theta integral over a unit cone

Let `I` be an invertible fractional ideal of a number field `K`, `σ(I)` its lattice in the mixed
space, and `D` a fundamental domain for the units on the norm-one hypersurface. Hecke's integral
representation of the partial zeta function of the class of `I⁻¹` integrates the theta series of
`σ(I)` minus its constant term over the cone above `D` (Neukirch VII (5.5), before the Mellin
substitution):

`∫_{cone D} N(y)^(s/2) (θ_{σ(I)}(y) - 1) dy / y = Γ_ℝ(s)^r₁ Γ_ℝ(2s)^r₂ ∑_a |N(a)|^(-s)`

for `Re s > 1`, where the sum runs over the points `a` of `σ(I)` in Mathlib's fundamental cone
`fundamentalCone K` (`TauCeti.LFunctions.integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one`).
For a nonzero integral ideal `J` these are the points of Mathlib's `idealSet K J`. Fractional
ideals occur on the dual side of the functional equation, through the lattice of the trace dual of
`I` (`TauCeti.LFunctions.mellinKernel_mixedDual_idealLattice`).

The proof unfolds the units twice. On the side of the parameters, the translates of the cone above
`D` by the units cover the positive orthant `w = #μ(K)` times
(`TauCeti.LFunctions.IsUnitFundamentalDomain.hasSum_integral_unitCone_unitScale`), so the cone
integrals of the Gaussians of the unit multiples `u a` of one lattice point `a` add up to `w` times
its full gamma integral `Γ_ℝ(s)^r₁ Γ_ℝ(2s)^r₂ |N(a)|^(-s)`
(`TauCeti.LFunctions.hasSum_integral_unitCone_archGaussian_unit_smul`). On the side of the
lattice, the map `(a, u) ↦ u a` from the points of `σ(I)` in the fundamental cone and the units
onto the nonzero points of `σ(I)` has fibres of `w` points, the torsion orbits
(`NumberField.mixedEmbedding.fundamentalCone.natCard_unitSMul_eq_torsionOrder`). For `Re s > 1`
the cone integrals `∫_{cone D} ‖archGaussian y z N(y)^(s/2)‖ dy / y` of the pointwise norms are
summable over the nonzero points `z` of `σ(I)` (`TauCeti.LFunctions.summable_integral_unitCone`),
which licenses the exchange of the lattice sum with the integral.

The unfolding needs the cone above a fundamental domain for the units; over the whole positive
orthant the sum of the gamma integrals of the nonzero lattice points diverges in positive unit
rank (`NumberField.Units.not_summable_absNorm_of_rank_pos`).

## Main results

* `TauCeti.LFunctions.hasSum_integral_unitCone_archGaussian`: the cone integrals of the Gaussians
  of the nonzero points of `σ(I)` against `N(y)^(s/2)` sum to
  `Γ_ℝ(s)^r₁ Γ_ℝ(2s)^r₂ ∑_a |N(a)|^(-s)`, over the points `a` of `σ(I)` in the fundamental cone.
* `TauCeti.LFunctions.summable_integral_unitCone`: the cone integrals of the pointwise norms
  `∫_{cone D} ‖…‖` of these integrands are summable over the nonzero points of `σ(I)`.
* `TauCeti.LFunctions.integrableOn_unitCone_archNorm_cpow_mul_latticeTheta_sub_one` and
  `TauCeti.LFunctions.integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one`: the theta integral
  over the cone converges and equals that sum.
* `TauCeti.LFunctions.hasMellin_mellinKernel_idealLattice_sub_mellinConstant`: Neukirch's (5.5),
  the Mellin transform at `s/2` of the kernel of `σ(I)` minus its constant term, expressed through
  the Dirichlet series of the ideal class of `I⁻¹`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.3)–(5.5).
-/

public section

noncomputable section

open Complex MeasureTheory Set NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone NumberField.Units TauCeti.GlobalNumberFields
open scoped nonZeroDivisors

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K] {D : Set (realSpace K)} {s : ℂ}

/-! ### The unfolding over an ideal lattice -/

variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- A nonzero point of the lattice of `I` has nonzero norm. -/
private theorem norm_ne_zero_of_ne_zero (z : {z : idealLattice K I // z ≠ 0}) :
    mixedEmbedding.norm (z : mixedSpace K) ≠ 0 :=
  norm_ne_zero_of_mem_idealLattice z.1.2 fun h ↦ z.2 (Submodule.coe_eq_zero.mp h)

/-- A unit multiple of a point of the fundamental cone has nonzero norm. -/
private theorem norm_unit_smul_ne_zero {a : mixedSpace K} (ha : a ∈ fundamentalCone K)
    (u : (𝓞 K)ˣ) : mixedEmbedding.norm (u • a) ≠ 0 := by
  rw [norm_unit_smul]
  exact (norm_pos_of_mem ha).ne'

/-- The Gaussian of a nonzero point of `σ(I)` against `N(y)^(s/2)` is integrable on the cone
for `0 < Re s`. -/
private theorem integrableOn_unitCone_archGaussian_mul_archNorm_cpow
    (z : {z : idealLattice K I // z ≠ 0}) (hs : 0 < s.re) :
    IntegrableOn (fun y ↦ archGaussian y (z : mixedSpace K) * (archNorm y : ℂ) ^ (s / 2))
      (unitCone D) (archHaar K) :=
  (integrable_archGaussian_mul_archNorm_cpow (norm_ne_zero_of_ne_zero I z) hs).integrableOn

/-- The unfolded double sum over the points `a` of `σ(I)` in the fundamental cone and the units
`u`: for `Re s > 1`, the cone integrals of the Gaussians of `u a` sum absolutely to `w` times
`Γ_ℝ(s)^r₁ Γ_ℝ(2s)^r₂ ∑_a |N(a)|^(-s)`. -/
private theorem hasSum_integral_unitCone_archGaussian_prod
    (hD : IsUnitFundamentalDomain K D) (hs : 1 < s.re) :
    HasSum (fun p : ↥(fundamentalCone K ∩ (idealLattice K I : Set (mixedSpace K))) × (𝓞 K)ˣ ↦
        ∫ y in unitCone D,
          archGaussian y (p.2 • (p.1 : mixedSpace K)) * (archNorm y : ℂ) ^ (s / 2) ∂archHaar K)
      (torsionOrder K * (Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
        ∑' a : ↥(fundamentalCone K ∩ (idealLattice K I : Set (mixedSpace K))),
          (mixedEmbedding.norm (a : mixedSpace K) : ℂ) ^ (-s))) := by
  set A := fundamentalCone K ∩ (idealLattice K I : Set (mixedSpace K))
  set Γ : ℂ → ℂ := fun r ↦ Gammaℝ r ^ nrRealPlaces K * Gammaℝ (2 * r) ^ nrComplexPlaces K
  set φ : ℂ → mixedSpace K → ℂ := fun r z ↦
    ∫ y in unitCone D, archGaussian y z * (archNorm y : ℂ) ^ (r / 2) ∂archHaar K
  have hσ : 1 < (s.re : ℂ).re := by simpa using hs
  -- the sum over the units, for each point in the cone
  have hfib (r : ℂ) (hr : 1 < r.re) (a : A) : HasSum (fun u : (𝓞 K)ˣ ↦
      φ r (u • (a : mixedSpace K))) (torsionOrder K * (Γ r *
        (mixedEmbedding.norm (a : mixedSpace K) : ℂ) ^ (-r))) := by
    simpa [φ, Γ, mul_assoc] using hasSum_integral_unitCone_archGaussian_unit_smul hD
      (by simpa using norm_unit_smul_ne_zero a.2.1 1) (zero_lt_one.trans hr)
  -- the sum over the points in the cone of the sums over the units
  have hcone (r : ℂ) (hr : 1 < r.re) : HasSum (fun a : A ↦
      (torsionOrder K : ℂ) * (Γ r * (mixedEmbedding.norm (a : mixedSpace K) : ℂ) ^ (-r)))
      (torsionOrder K * (Γ r * ∑' a : A, (mixedEmbedding.norm (a : mixedSpace K) : ℂ) ^ (-r))) :=
    (((hasSum_norm_cpow_fundamentalCone_inter_idealLattice I (inv_inv _).symm
      hr).summable.hasSum.mul_left (Γ r))).mul_left _
  -- absolute convergence, dominating the norms by the same sum at the real point `Re s`
  have hbound (p : A × (𝓞 K)ˣ) :
      ‖φ s (p.2 • (p.1 : mixedSpace K))‖ ≤ (φ s.re (p.2 • (p.1 : mixedSpace K))).re :=
    (norm_integral_le_integral_norm _).trans_eq
      (setIntegral_norm_archGaussian_mul_archNorm_cpow _)
  have hsummable : Summable fun p : A × (𝓞 K)ˣ ↦ φ s (p.2 • (p.1 : mixedSpace K)) := by
    refine Summable.of_norm_bounded ((summable_prod_of_nonneg fun p ↦
      (norm_nonneg _).trans (hbound p)).mpr ⟨fun a ↦ (hasSum_re (hfib _ hσ a)).summable, ?_⟩)
      hbound
    exact (hasSum_re (hcone _ hσ)).summable.congr fun a ↦ (hasSum_re (hfib _ hσ a)).tsum_eq.symm
  rw [← (hsummable.hasSum.prod_fiberwise (hfib s hs)).unique (hcone s hs)]
  exact hsummable.hasSum

/-- **Hecke's unfolding of the lattice sum.** For `Re s > 1`, the cone integrals of the Gaussians
of the nonzero points `z` of the lattice `σ(I)` against `N(y)^(s/2) dy / y`, over the cone above a
unit fundamental domain, sum to `Γ_ℝ(s)^r₁ Γ_ℝ(2s)^r₂ ∑_{a} |N(a)|^(-s)`, the sum running over the
points `a` of `σ(I)` in the fundamental cone. -/
theorem hasSum_integral_unitCone_archGaussian (hD : IsUnitFundamentalDomain K D)
    (hs : 1 < s.re) :
    HasSum (fun z : {z : idealLattice K I // z ≠ 0} ↦
        ∫ y in unitCone D, archGaussian y (z : mixedSpace K) * (archNorm y : ℂ) ^ (s / 2)
          ∂archHaar K)
      (Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
        ∑' a : ↥(fundamentalCone K ∩ (idealLattice K I : Set (mixedSpace K))),
          (mixedEmbedding.norm (a : mixedSpace K) : ℂ) ^ (-s)) := by
  set A := fundamentalCone K ∩ (idealLattice K I : Set (mixedSpace K))
  set φ : mixedSpace K → ℂ := fun z ↦
    ∫ y in unitCone D, archGaussian y z * (archNorm y : ℂ) ^ (s / 2) ∂archHaar K
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  -- regroup the double sum along `(a, u) ↦ u a`, whose fibres have `w` points
  let Φ : A × (𝓞 K)ˣ → {z : idealLattice K I // z ≠ 0} := fun p ↦
    ⟨⟨p.2 • (p.1 : mixedSpace K), (Units.unitSMul_mem_idealLattice_iff _ _ _).mpr p.1.2.2⟩,
      fun h ↦ norm_unit_smul_ne_zero p.1.2.1 p.2
        ((congrArg mixedEmbedding.norm (Submodule.coe_eq_zero.mpr h)).trans (map_zero _))⟩
  have hfiber (z : {z : idealLattice K I // z ≠ 0}) :
      ∑' p : Φ ⁻¹' {z}, φ ((p : A × (𝓞 K)ˣ).2 • (p.1.1 : mixedSpace K)) =
        torsionOrder K * φ (z : mixedSpace K) := by
    have hΦ (p : A × (𝓞 K)ˣ) :
        p ∈ Φ ⁻¹' {z} ↔ p.2 • (p.1 : mixedSpace K) = (z : mixedSpace K) := by
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff, Φ]
    -- a pair `(a, u)` with `u a = z` has `a = u⁻¹ z` in `σ(I)` already
    let e : {p : A × (𝓞 K)ˣ // p.2 • (p.1 : mixedSpace K) = z} ≃
        {p : fundamentalCone K × (𝓞 K)ˣ // p.2 • (p.1 : mixedSpace K) = z} :=
      { toFun p := ⟨(⟨p.1.1, p.1.1.2.1⟩, p.1.2), p.2⟩
        invFun p := ⟨(⟨p.1.1, p.1.1.2, (Units.unitSMul_mem_idealLattice_iff p.1.2 _ _).mp
          (by rw [p.2]; exact z.1.2)⟩, p.1.2), p.2⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    rw [tsum_congr fun p : Φ ⁻¹' {z} ↦ congrArg φ ((hΦ p).mp p.prop), tsum_const,
      Nat.card_congr ((Equiv.subtypeEquivRight hΦ).trans e),
      natCard_unitSMul_eq_torsionOrder (norm_ne_zero_of_ne_zero I z), nsmul_eq_mul]
  have h := ((hasSum_integral_unitCone_archGaussian_prod I hD hs).tsum_fiberwise
    Φ).congr_fun fun z ↦ (hfiber z).symm
  simpa only [φ, inv_mul_cancel_left₀ hw] using h.mul_left ((torsionOrder K : ℂ)⁻¹)

/-- **Absolute convergence of the unfolded sum.** For `Re s > 1`, the cone integrals of the norms
of the Gaussians of the nonzero points of `σ(I)` against `N(y)^(s/2)` are summable; this licenses
the exchange of the lattice sum with the integral over the cone. -/
theorem summable_integral_unitCone (hD : IsUnitFundamentalDomain K D) (hs : 1 < s.re) :
    Summable fun z : {z : idealLattice K I // z ≠ 0} ↦
      ∫ y in unitCone D, ‖archGaussian y (z : mixedSpace K) * (archNorm y : ℂ) ^ (s / 2)‖
        ∂archHaar K := by
  refine (hasSum_re (hasSum_integral_unitCone_archGaussian I hD (s := s.re)
    (by simpa using hs))).summable.congr fun z ↦ ?_
  exact (setIntegral_norm_archGaussian_mul_archNorm_cpow _).symm

/-! ### The theta integral over the cone -/

/-- On the cone, `N(y)^(s/2) (θ_{σ(I)}(y) - 1)` is the sum over the nonzero lattice points of
their Gaussians against `N(y)^(s/2)`. -/
private theorem archNorm_cpow_mul_latticeTheta_sub_one_eq_tsum {y : realSpace K}
    (hy : ∀ w, 0 < y w) :
    (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1) =
      ∑' z : {z : idealLattice K I // z ≠ 0},
        archGaussian y (z : mixedSpace K) * (archNorm y : ℂ) ^ (s / 2) := by
  rw [latticeTheta_eq_one_add _ y hy, add_sub_cancel_left, tsum_mul_right, mul_comm]

/-- **The theta integral over the cone converges** for `Re s > 1`: `N(y)^(s/2) (θ_{σ(I)}(y) - 1)`
is integrable for `dy / y` on the cone above a unit fundamental domain. -/
theorem integrableOn_unitCone_archNorm_cpow_mul_latticeTheta_sub_one
    (hD : IsUnitFundamentalDomain K D) (hs : 1 < s.re) :
    IntegrableOn (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1))
      (unitCone D) (archHaar K) := by
  set L := idealLattice K I
  have : Countable L := Countable.of_moduleFinite (R := ℤ)
  have hcone := measurableSet_unitCone hD.measurableSet
  have hint (z : {z : L // z ≠ 0}) :=
    integrableOn_unitCone_archGaussian_mul_archNorm_cpow I (D := D) z (zero_lt_one.trans hs)
  have hcont : ContinuousOn (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * (latticeTheta L y - 1))
      (unitCone D) := fun y hy ↦ ContinuousAt.continuousWithinAt <|
    ((continuousAt_ofReal_cpow_const _ _ (Or.inr (archNorm_pos (mem_unitCone.mp hy).1).ne')).comp
      continuous_archNorm.continuousAt).mul
      ((continuousAt_latticeTheta L (mem_unitCone.mp hy).1).sub continuousAt_const)
  refine ⟨hcont.aestronglyMeasurable hcone, ?_⟩
  -- the norm of the sum is at most the sum of the norms, whose integrals are summable
  calc ∫⁻ y in unitCone D, ‖(archNorm y : ℂ) ^ (s / 2) * (latticeTheta L y - 1)‖ₑ ∂archHaar K
      ≤ ∫⁻ y in unitCone D, ∑' z : {z : L // z ≠ 0},
          ‖archGaussian y (z : mixedSpace K) * (archNorm y : ℂ) ^ (s / 2)‖ₑ ∂archHaar K := by
        refine setLIntegral_mono' hcone fun y hy ↦ ?_
        rw [archNorm_cpow_mul_latticeTheta_sub_one_eq_tsum I (mem_unitCone.mp hy).1]
        exact eNorm_tsum_le_tsum_eNorm
    _ = ∑' z : {z : L // z ≠ 0}, ENNReal.ofReal (∫ y in unitCone D,
          ‖archGaussian y (z : mixedSpace K) * (archNorm y : ℂ) ^ (s / 2)‖ ∂archHaar K) := by
        rw [lintegral_tsum fun z ↦ (hint z).aestronglyMeasurable.eNorm]
        exact tsum_congr fun z ↦ (ofReal_integral_norm_eq_lintegral_eNorm (hint z)).symm
    _ = ENNReal.ofReal (∑' z : {z : L // z ≠ 0}, ∫ y in unitCone D,
          ‖archGaussian y (z : mixedSpace K) * (archNorm y : ℂ) ^ (s / 2)‖ ∂archHaar K) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _)
          (summable_integral_unitCone I hD hs)).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- **Hecke's unfolding of the theta integral**, Neukirch VII (5.5) before the Mellin
substitution. For `Re s > 1` and a unit fundamental domain `D`,

`∫_{cone D} N(y)^(s/2) (θ_{σ(I)}(y) - 1) dy / y = Γ_ℝ(s)^r₁ Γ_ℝ(2s)^r₂ ∑_{a} |N(a)|^(-s)`,

the sum running over the points `a` of `σ(I)` in the fundamental cone. -/
theorem integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one
    (hD : IsUnitFundamentalDomain K D) (hs : 1 < s.re) :
    ∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1)
        ∂archHaar K =
      Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
        ∑' a : ↥(fundamentalCone K ∩ (idealLattice K I : Set (mixedSpace K))),
          (mixedEmbedding.norm (a : mixedSpace K) : ℂ) ^ (-s) := by
  have : Countable (idealLattice K I) := Countable.of_moduleFinite (R := ℤ)
  have hint (z : {z : idealLattice K I // z ≠ 0}) :=
    integrableOn_unitCone_archGaussian_mul_archNorm_cpow I (D := D) z (zero_lt_one.trans hs)
  rw [← (hasSum_integral_of_summable_integral_norm hint
    (summable_integral_unitCone I hD hs)).unique (hasSum_integral_unitCone_archGaussian I hD hs)]
  exact setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y hy ↦
    archNorm_cpow_mul_latticeTheta_sub_one_eq_tsum I (mem_unitCone.mp hy).1

open scoped Classical in
/-- **The Mellin representation of a partial zeta function**, Neukirch VII (5.5). Let `c` be the
ideal class of `I⁻¹`, `V` the covolume of `σ(I)` and `D` a unit fundamental domain. For
`Re s > 1`, the Mellin transform at `s/2` of the kernel `f_D(σ(I), ·)` minus its constant term
`a₀ = 2^(r-1) R / w` is

`2^r₂ (V²)^(s/2) N(I)^(-s) Γ_ℝ(s)^r₁ Γ_ℝ(2s)^r₂ ζ(c, s)`,

where `ζ(c, s)` is the Dirichlet series of the indicator of `c`. -/
theorem hasMellin_mellinKernel_idealLattice_sub_mellinConstant
    (hD : IsUnitFundamentalDomain K D) {c : RayClassGroup (Modulus.one K)}
    (hI : rayClassMk (Modulus.one K) ((idealsPrimeToEquiv Modulus.support_one).symm I) = c⁻¹)
    (hs : 1 < s.re) :
    HasMellin (fun u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K) (s / 2)
      (2 ^ nrComplexPlaces K * (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) *
        (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℂ) ^ (-s) *
        (Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K) *
          LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s) := by
  have h := hasMellin_mellinKernel_sub hD.measurableSet hD.isBounded _ s
    (integrableOn_unitCone_archNorm_cpow_mul_latticeTheta_sub_one I hD hs)
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  rw [integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one I hD hs,
    (hasSum_norm_cpow_fundamentalCone_inter_idealLattice I hI hs).tsum_eq] at h
  rw [mellinConstant_eq_mul_surfaceHaar_real hD]
  convert h using 1
  · simp only [ofReal_mul, ofReal_div, ofReal_pow, ofReal_ofNat, ofReal_natCast]
  · field_simp

end TauCeti.LFunctions
