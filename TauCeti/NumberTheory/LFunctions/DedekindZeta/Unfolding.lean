/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.UnitQuotient
public import TauCeti.NumberTheory.LFunctions.Theta.GammaIntegral
public import TauCeti.NumberTheory.LFunctions.Theta.Surface.Cone
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Real
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Hecke's unfolding of the theta integral over a unit cone

Let `I` be an invertible fractional ideal of a number field `K` and let `D` be a unit fundamental
domain on the norm-one hypersurface (`IsUnitFundamentalDomain K D`). Subtracting the zero lattice
point from the theta series of `σ(I)` leaves the sum of `archGaussian y x` over the nonzero points
`x` of `σ(I)`. Two mechanisms meet when this sum is integrated against `N(y)^(s/2) dy / y` over the
cone `unitCone D`:

1. On the parameter space `realSpace K`, the torsion `μ(K)` acts trivially under `unitScale`, so the
   quotient `(𝓞 K)ˣ ⧸ torsion K` acts by positive coordinatewise dilations preserving `archHaar K`,
   with fundamental domain `unitCone D`.
2. On the lattice `σ(I)`, the full unit group `(𝓞 K)ˣ` acts faithfully away from `0`, while
   Mathlib's `fundamentalCone K` is invariant under `μ(K)` and meets every nonzero `(𝓞 K)ˣ`-orbit in
   a single `μ(K)`-coset. Choosing one unit representative per coset of `(𝓞 K)ˣ ⧸ torsion K`
   therefore identifies `↑(fundamentalCone K ∩ σ(I)) × ((𝓞 K)ˣ ⧸ torsion K)` bijectively with the
   nonzero points of `σ(I)`, compatibly with `archGaussian_unit_smul`.

For `Re s > 1`, summing the `L¹` norms over a coset folds the cone integrals of an orbit into a
single whole-orthant gamma integral (`integral_archGaussian_mul_archNorm_cpow`), and the remaining
sum over `fundamentalCone K ∩ σ(I)` converges by
`hasSum_norm_cpow_fundamentalCone_inter_idealLattice`. Tonelli and Fubini
(`hasSum_integral_of_summable_integral_norm`) then give both absolute integrability of
`N(y)^(s/2) (θ_{σ(I)}(y) - 1)` on `unitCone D` — the analytic input required by
`hasMellin_mellinKernel_sub` — and Hecke's unfolded formula (Neukirch VII (5.5)):

`∫_{unitCone D} N(y)^(s/2) (θ_{σ(I)}(y) - 1) dy / y`
`  = Γ_ℝ(s)^r₁ Γ_ℝ(2s)^r₂ · ∑_{z ∈ fundamentalCone K ∩ σ(I)} |N(z)|^(-s)`.

## Main results

* `TauCeti.LFunctions.summable_integral_unitCone_norm_archNorm_cpow_mul_archGaussian`: for
  `Re s > 1`, the `L¹` norms of `N(y)^(s/2) archGaussian y x` on `unitCone D` are summable over the
  nonzero points `x` of `σ(I)`.
* `TauCeti.LFunctions.integrableOn_archNorm_cpow_mul_latticeTheta_sub_one`: for `Re s > 1`,
  `N(y)^(s/2) (θ_{σ(I)}(y) - 1)` is integrable on `unitCone D` with respect to `archHaar K`.
* `TauCeti.LFunctions.hasSum_gamma_mul_norm_cpow_fundamentalCone`: Hecke's unfolded cone integral
  as a `HasSum` over `fundamentalCone K ∩ σ(I)`, Neukirch VII (5.5).

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.5).
-/

public section

noncomputable section

open Complex MeasureTheory Set NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone NumberField.Units
open scoped Pointwise nonZeroDivisors

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### The quotient action of units modulo torsion on the parameter space -/

/-- The quotient `(𝓞 K)ˣ ⧸ torsion K` through which the unit action on `realSpace K` factors. -/
private abbrev UnitQuot (K : Type*) [Field K] := (𝓞 K)ˣ ⧸ torsion K

private instance : Countable (UnitQuot K) := by
  have : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  have : Countable (𝓞 K) := Subtype.coe_injective.countable
  have : Countable (𝓞 K)ˣ := Units.val_injective.countable
  exact Quotient.countable

/-- Roots of unity have absolute value `1` at every infinite place, so they act trivially on all
parameters in `realSpace K`. -/
private theorem unitScale_of_mem_torsion {u : (𝓞 K)ˣ} (hu : u ∈ torsion K) (y : realSpace K) :
    unitScale u y = y := by
  rw [mem_torsion] at hu
  ext w
  rw [unitScale_apply, hu w, one_pow, one_mul]

/-- Coset representatives modulo `torsion K` induce the same parameter scaling `unitScale`. -/
private theorem unitScale_congr {u v : (𝓞 K)ˣ} (h : QuotientGroup.leftRel (torsion K) u v)
    (y : realSpace K) : unitScale u y = unitScale v y := by
  have huv : u = v * (u⁻¹ * v)⁻¹ := by group
  rw [huv, ← unitScale_unitScale,
    unitScale_of_mem_torsion (inv_mem (QuotientGroup.leftRel_apply.mp h))]

private instance : MulAction (UnitQuot K) (realSpace K) where
  smul g y := Quotient.liftOn' g (fun u ↦ unitScale u y) fun _ _ h ↦ unitScale_congr h y
  one_smul := unitScale_one
  mul_smul g₁ g₂ y := Quotient.inductionOn₂' g₁ g₂ fun u v ↦ (unitScale_unitScale u v y).symm

private theorem unitQuot_mk_smul (u : (𝓞 K)ˣ) (y : realSpace K) :
    (QuotientGroup.mk u : UnitQuot K) • y = unitScale u y := rfl

@[simp]
private theorem archNorm_unitQuot_smul (g : UnitQuot K) (y : realSpace K) :
    archNorm (g • y) = archNorm y :=
  Quotient.inductionOn' g fun u ↦ archNorm_unitScale u y

omit [NumberField K] in
private theorem unitScale_eq_mul (u : (𝓞 K)ˣ) :
    (unitScale u : realSpace K → realSpace K) = ((fun w ↦ w (u : K) ^ 2) * ·) := by
  ext y w
  exact unitScale_apply u y w

private instance : MeasurableConstSMul (UnitQuot K) (realSpace K) where
  measurable_const_smul g := Quotient.inductionOn' g fun u ↦ by
    change Measurable (unitScale u)
    rw [unitScale_eq_mul]
    exact measurable_const_mul _

private instance : SMulInvariantMeasure (UnitQuot K) (realSpace K) (archHaar K) where
  measure_preimage_smul g s hs := Quotient.inductionOn' g fun u ↦ by
    have hc : ∀ w : InfinitePlace K, 0 < w (u : K) ^ 2 :=
      fun w ↦ pow_pos (pos_iff.mpr (by simp)) 2
    change (archHaar K) (unitScale u ⁻¹' s) = (archHaar K) s
    rw [unitScale_eq_mul, ← Measure.map_apply (measurable_const_mul _) hs, map_archHaar_mul_left hc]

/-- For any unit fundamental domain `D` on the norm-one hypersurface, `unitCone D` is a
measure-theoretic fundamental domain for `(𝓞 K)ˣ ⧸ torsion K` on `(realSpace K, archHaar K)`. -/
private theorem isFundamentalDomain_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) :
    IsFundamentalDomain (UnitQuot K) (unitCone D) (archHaar K) where
  nullMeasurableSet := (measurableSet_unitCone hD.measurableSet).nullMeasurableSet
  ae_covers := by
    filter_upwards [ae_archHaar_pos] with y hy
    obtain ⟨u, hu⟩ := hD.exists_unitScale_mem (surfacePart y) (surfacePart_mem_normOneSurface hy)
    refine ⟨QuotientGroup.mk u, mem_unitCone.mpr ⟨fun w ↦ unitScale_pos (hy w) u, ?_⟩⟩
    simpa only [unitQuot_mk_smul, surfacePart_unitScale] using hu
  aedisjoint g₁ g₂ hne := Disjoint.aedisjoint <| Set.disjoint_left.mpr <| by
    induction g₁ using Quotient.inductionOn' with | h u₁ =>
    induction g₂ using Quotient.inductionOn' with | h u₂ =>
    rintro _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, heq⟩
    apply hne
    change QuotientGroup.mk u₁ = QuotientGroup.mk u₂
    rw [QuotientGroup.eq]
    have hy₁_cone := mem_unitCone.mp hy₁
    have hy₂_cone := mem_unitCone.mp hy₂
    have hsurf : unitScale (u₂⁻¹ * u₁) (surfacePart y₁) = surfacePart y₂ := by
      have h1 := congrArg surfacePart heq
      simp only [unitQuot_mk_smul, surfacePart_unitScale] at h1
      calc unitScale (u₂⁻¹ * u₁) (surfacePart y₁)
          = unitScale u₂⁻¹ (unitScale u₁ (surfacePart y₁)) := (unitScale_unitScale _ _ _).symm
        _ = unitScale u₂⁻¹ (unitScale u₂ (surfacePart y₂)) := by rw [← h1]
        _ = surfacePart y₂ := by rw [unitScale_unitScale, inv_mul_cancel, unitScale_one]
    have hmem : u₂⁻¹ * u₁ ∈ torsion K :=
      (hD.unitScale_mem_iff _ hy₁_cone.2 _).mp (hsurf.symm ▸ hy₂_cone.2)
    simpa using inv_mem hmem

/-- Integrating an `archHaar`-integrable function over `realSpace K` unfolds into the `HasSum` of
its integrals over `unitCone D` along `(𝓞 K)ˣ ⧸ torsion K`. -/
private theorem hasSum_setIntegral_unitCone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D) {f : realSpace K → E}
    (hf : Integrable f (archHaar K)) :
    HasSum (fun g : UnitQuot K ↦ ∫ y in unitCone D, f (g • y) ∂archHaar K)
      (∫ y, f y ∂archHaar K) := by
  have hsum : Integrable f
      (Measure.sum fun g : UnitQuot K ↦ (archHaar K).restrict (g • unitCone D)) :=
    by rwa [(isFundamentalDomain_unitCone hD).sum_restrict]
  have h := hasSum_integral_measure hsum
  rw [(isFundamentalDomain_unitCone hD).sum_restrict] at h
  refine h.congr_fun fun g ↦ ?_
  rw [← Set.image_smul]
  exact ((measurePreserving_smul g (archHaar K)).setIntegral_image_emb
    (measurableEmbedding_const_smul g) f (unitCone D)).symm

/-! ### Orbit decomposition of nonzero ideal-lattice points -/

/-- The points of the fractional-ideal lattice `σ(I)` lying in Mathlib's fundamental cone. -/
private abbrev ConePoints (K : Type*) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  ↑(fundamentalCone K ∩ (idealLattice K I : Set (mixedSpace K)))

private instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Countable (idealLattice K I) :=
  TopologicalSpace.separableSpace_iff_countable.mp inferInstance

/-- Every nonzero point of an ideal lattice has nonzero mixed norm, as it is the image of a nonzero
field element under `mixedEmbedding K`. -/
private theorem norm_ne_zero_of_idealLattice_ne_zero {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (x : {x : idealLattice K I // x ≠ 0}) :
    mixedEmbedding.norm ((x : idealLattice K I) : mixedSpace K) ≠ 0 := by
  obtain ⟨a, _, hax⟩ := (mem_idealLattice K I).mp x.1.2
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply x.2
    exact Subtype.ext (by simpa using hax.symm)
  rw [← hax, norm_eq_norm]
  exact Rat.cast_ne_zero.mpr (abs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr ha0))

private theorem unitQuot_out_smul_ne_zero {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (p : ConePoints K I × UnitQuot K) :
    (⟨Quotient.out p.2 • (p.1 : mixedSpace K),
        ((Quotient.out p.2).unitSMul_mem_idealLattice_iff I _).mpr p.1.2.2⟩ :
      idealLattice K I) ≠ 0 := by
  intro h0
  refine (fundamentalCone.norm_pos_of_mem p.1.2.1).ne' ?_
  have hz : (p.1 : mixedSpace K) = 0 :=
    (MulAction.toPerm (Quotient.out p.2)).injective (by simpa using congrArg Subtype.val h0)
  simp [hz]

private def unitOrbitFun (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ConePoints K I × UnitQuot K) : {x : idealLattice K I // x ≠ 0} :=
  ⟨⟨Quotient.out p.2 • (p.1 : mixedSpace K),
      ((Quotient.out p.2).unitSMul_mem_idealLattice_iff I _).mpr p.1.2.2⟩,
    unitQuot_out_smul_ne_zero p⟩

private theorem bijective_unitOrbitFun (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Function.Bijective (unitOrbitFun I) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨z₁, g₁⟩ ⟨z₂, g₂⟩ h
    have hval : Quotient.out g₁ • (z₁ : mixedSpace K) = Quotient.out g₂ • (z₂ : mixedSpace K) :=
      congrArg (Subtype.val ∘ Subtype.val) h
    have hsmul : ((Quotient.out g₂)⁻¹ * Quotient.out g₁) • (z₁ : mixedSpace K) = z₂ := by
      rw [mul_smul, hval, inv_smul_smul]
    have htor : (Quotient.out g₂)⁻¹ * Quotient.out g₁ ∈ torsion K :=
      (unit_smul_mem_iff_mem_torsion z₁.2.1 _).mp (hsmul ▸ z₂.2.1)
    have hg : g₁ = g₂ := by
      rw [← Quotient.out_eq g₁, ← Quotient.out_eq g₂]
      exact (QuotientGroup.eq.mpr htor).symm
    subst hg
    exact Prod.ext (Subtype.ext (by simpa using hsmul)) rfl
  · intro x
    obtain ⟨v, hv⟩ := exists_unit_smul_mem (norm_ne_zero_of_idealLattice_ne_zero x)
    set g : UnitQuot K := QuotientGroup.mk v⁻¹
    have hout : QuotientGroup.mk (Quotient.out g) = QuotientGroup.mk v⁻¹ := Quotient.out_eq g
    have htor : (Quotient.out g)⁻¹ * v⁻¹ ∈ torsion K := QuotientGroup.eq.mp hout
    set z : mixedSpace K := (Quotient.out g)⁻¹ • ((x : idealLattice K I) : mixedSpace K)
    have hz_cone : z ∈ fundamentalCone K := by
      have hz_eq : z = ((Quotient.out g)⁻¹ * v⁻¹) •
          (v • ((x : idealLattice K I) : mixedSpace K)) := by
        rw [mul_smul, inv_smul_smul]
      rw [hz_eq]
      exact torsion_smul_mem_of_mem hv htor
    have hz_lat : z ∈ idealLattice K I :=
      ((Quotient.out g)⁻¹.unitSMul_mem_idealLattice_iff I _).mpr x.1.2
    refine ⟨⟨⟨z, hz_cone, hz_lat⟩, g⟩, Subtype.ext (Subtype.ext ?_)⟩
    exact smul_inv_smul (Quotient.out g) _

/-- Choosing `Quotient.out g` on each coset of `(𝓞 K)ˣ ⧸ torsion K` identifies
`(fundamentalCone K ∩ σ(I)) × UnitQuot K` bijectively with the nonzero points of `σ(I)`. -/
private def unitOrbitEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ConePoints K I × UnitQuot K ≃ {x : idealLattice K I // x ≠ 0} :=
  Equiv.ofBijective (unitOrbitFun I) (bijective_unitOrbitFun I)

private theorem archGaussian_unitOrbitEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ConePoints K I × UnitQuot K) (y : realSpace K) :
    archGaussian y ((unitOrbitEquiv I p : idealLattice K I) : mixedSpace K) =
      archGaussian (p.2 • y) (p.1 : mixedSpace K) := by
  have hout : (QuotientGroup.mk (Quotient.out p.2) : UnitQuot K) = p.2 := Quotient.out_eq p.2
  change archGaussian y (Quotient.out p.2 • (p.1 : mixedSpace K)) = _
  rw [archGaussian_unit_smul, ← unitQuot_mk_smul, hout]

/-! ### Norm integrals, integrability, and Hecke's unfolding -/

/-- On the positive orthant, the norm of `N(y)^(s/2) archGaussian y x`, cast to `ℂ`, is the
integrand of the gamma integral at the real argument `s.re`. -/
private theorem ofReal_norm_archNorm_cpow_mul_archGaussian {y : realSpace K} (hy : ∀ w, 0 < y w)
    (x : mixedSpace K) (s : ℂ) :
    ((‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y x‖ : ℝ) : ℂ) =
      archGaussian y x * (archNorm y : ℂ) ^ ((s.re : ℂ) / 2) := by
  have hN : 0 < archNorm y := archNorm_pos hy
  have hre : (s / 2).re = s.re / 2 := by simp
  have hexp : ‖archGaussian y x‖ = Real.exp (-Real.pi * ∑ w, y w * normAtPlace w x ^ 2) := by
    rw [archGaussian_apply, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN, hre, hexp, ofReal_mul,
    ofReal_cpow hN.le, ofReal_div, ofReal_ofNat, ← archGaussian_apply, mul_comm]

/-- Whole-orthant `L¹` norm integral of `N(y)^(s/2) archGaussian y x`, read in `ℂ` via
`integral_archGaussian_mul_archNorm_cpow` at `s.re`. -/
private theorem ofReal_integral_norm_archNorm_cpow_mul_archGaussian {x : mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    ((∫ y, ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y x‖ ∂archHaar K : ℝ) : ℂ) =
      Gammaℝ s.re ^ nrRealPlaces K * Gammaℝ (2 * (s.re : ℂ)) ^ nrComplexPlaces K *
        (mixedEmbedding.norm x : ℂ) ^ (-(s.re : ℂ)) := by
  rw [← integral_complex_ofReal]
  have hcongr : (fun y ↦ ((‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y x‖ : ℝ) : ℂ)) =ᵐ[archHaar K]
      fun y ↦ archGaussian y x * (archNorm y : ℂ) ^ ((s.re : ℂ) / 2) := by
    filter_upwards [ae_archHaar_pos] with y hy
    exact ofReal_norm_archNorm_cpow_mul_archGaussian hy x s
  rw [integral_congr_ae hcongr]
  exact integral_archGaussian_mul_archNorm_cpow hx (by simpa using hs)

/-- **Summability of the `L¹` norms over the nonzero lattice points.** For an invertible fractional
ideal `I`, a unit fundamental domain `D`, and `Re s > 1`, the `L¹` norms of
`N(y)^(s/2) archGaussian y x` over `unitCone D` are summable over the nonzero points `x` of
`σ(I)`. -/
theorem summable_integral_unitCone_norm_archNorm_cpow_mul_archGaussian
    {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    Summable fun x : {x : idealLattice K I // x ≠ 0} ↦
      ∫ y in unitCone D,
        ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y ((x : idealLattice K I) : mixedSpace K)‖
        ∂archHaar K := by
  rw [← (unitOrbitEquiv I).summable_iff]
  have hcomp : (fun x : {x : idealLattice K I // x ≠ 0} ↦
      ∫ y in unitCone D,
        ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y ((x : idealLattice K I) : mixedSpace K)‖
        ∂archHaar K) ∘ unitOrbitEquiv I = fun p : ConePoints K I × UnitQuot K ↦
      ∫ y in unitCone D,
        ‖(archNorm (p.2 • y) : ℂ) ^ (s / 2) * archGaussian (p.2 • y) (p.1 : mixedSpace K)‖
        ∂archHaar K := by
    ext ⟨z, g⟩
    simp [Function.comp_apply, archGaussian_unitOrbitEquiv]
  rw [hcomp]
  have hrow (z : ConePoints K I) :
      HasSum (fun g : UnitQuot K ↦ ∫ y in unitCone D,
          ‖(archNorm (g • y) : ℂ) ^ (s / 2) * archGaussian (g • y) (z : mixedSpace K)‖
          ∂archHaar K)
        (∫ y, ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y (z : mixedSpace K)‖ ∂archHaar K) := by
    have hint := (integrable_archGaussian_mul_archNorm_cpow
      (s := s) (fundamentalCone.norm_pos_of_mem z.2.1).ne' (zero_lt_one.trans hs)).norm
    simpa only [mul_comm (archGaussian _ _)] using hasSum_setIntegral_unitCone hD hint
  have hcol : Summable fun z : ConePoints K I ↦
      ∫ y, ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y (z : mixedSpace K)‖ ∂archHaar K := by
    rw [← Complex.summable_ofReal]
    have hcone := (hasSum_norm_cpow_fundamentalCone_inter_idealLattice I
      (s := (s.re : ℂ)) (by simpa using hs)).summable.mul_left
      (Gammaℝ s.re ^ nrRealPlaces K * Gammaℝ (2 * (s.re : ℂ)) ^ nrComplexPlaces K)
    refine hcone.congr fun z ↦ (ofReal_integral_norm_archNorm_cpow_mul_archGaussian
      (fundamentalCone.norm_pos_of_mem z.2.1).ne' (zero_lt_one.trans hs)).symm
  exact (summable_prod_of_nonneg fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _).mpr
    ⟨fun z ↦ (hrow z).summable, by simpa only [fun z ↦ (hrow z).tsum_eq] using hcol⟩

/-- Each nonzero lattice point contributes an integrable Gaussian term on `unitCone D` for
`0 < Re s`. -/
private theorem integrableOn_unitCone_archNorm_cpow_mul_archGaussian
    (D : Set (realSpace K)) {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (x : {x : idealLattice K I // x ≠ 0}) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * archGaussian y ((x : idealLattice K I) : mixedSpace K))
      (unitCone D) (archHaar K) := by
  have hint := integrable_archGaussian_mul_archNorm_cpow
    (norm_ne_zero_of_idealLattice_ne_zero x) hs
  simpa only [mul_comm (archGaussian _ _)] using hint.integrableOn

/-- **Integrability of the norm-weighted theta series minus its constant term over a unit cone.**
For an invertible fractional ideal `I`, a unit fundamental domain `D`, and `Re s > 1`, the
integrand `N(y)^(s/2) (θ_{σ(I)}(y) - 1)` is integrable on `unitCone D` with respect to
`archHaar K`. This discharges the analytic hypothesis of `hasMellin_mellinKernel_sub`. -/
theorem integrableOn_archNorm_cpow_mul_latticeTheta_sub_one
    {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1))
      (unitCone D) (archHaar K) := by
  set μ := (archHaar K).restrict (unitCone D)
  set G : {x : idealLattice K I // x ≠ 0} → realSpace K → ℂ :=
    fun x y ↦ (archNorm y : ℂ) ^ (s / 2) * archGaussian y ((x : idealLattice K I) : mixedSpace K)
  have hG_int (x) : Integrable (G x) μ :=
    integrableOn_unitCone_archNorm_cpow_mul_archGaussian D x (zero_lt_one.trans hs)
  have hG_sum : Summable fun x ↦ ∫ y, ‖G x y‖ ∂μ :=
    summable_integral_unitCone_norm_archNorm_cpow_mul_archGaussian hD I hs
  have hmeas : AEStronglyMeasurable
      (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1)) μ := by
    refine ContinuousOn.aestronglyMeasurable (fun y hy ↦ ContinuousAt.continuousWithinAt ?_)
      (measurableSet_unitCone hD.measurableSet)
    have hy_pos := (mem_unitCone.mp hy).1
    exact (((continuous_ofReal.comp continuous_archNorm).continuousAt.cpow
      continuousAt_const (Or.inl (by simpa using archNorm_pos hy_pos))).mul
      ((continuousAt_latticeTheta _ hy_pos).sub continuousAt_const))
  refine ⟨hmeas, hasFiniteIntegral_iff_eNorm.mpr ?_⟩
  have hae : ∀ᵐ y ∂μ,
      ‖(archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1)‖ₑ ≤
        ∑' x, ‖G x y‖ₑ := by
    filter_upwards [ae_restrict_mem (measurableSet_unitCone hD.measurableSet)] with y hy
    rw [latticeTheta_eq_one_add _ y (mem_unitCone.mp hy).1, add_sub_cancel_left, ← tsum_mul_left]
    exact eNorm_tsum_le_tsum_eNorm
  calc ∫⁻ y, ‖(archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1)‖ₑ ∂μ
      ≤ ∫⁻ y, ∑' x, ‖G x y‖ₑ ∂μ := lintegral_mono_ae hae
    _ = ∑' x, ∫⁻ y, ‖G x y‖ₑ ∂μ := lintegral_tsum fun x ↦ (hG_int x).1.eNorm
    _ < ⊤ := by
      have hterm (x) : ∫⁻ y, ‖G x y‖ₑ ∂μ = ENNReal.ofReal (∫ y, ‖G x y‖ ∂μ) :=
        (ofReal_integral_norm_eq_lintegral_eNorm (hG_int x)).symm
      simp_rw [hterm]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) hG_sum]
      exact ENNReal.ofReal_lt_top

/-- **Hecke's unfolded cone integral**, Neukirch VII (5.5). For an invertible fractional ideal `I`,
a unit fundamental domain `D`, and `Re s > 1`, integrating `N(y)^(s/2) (θ_{σ(I)}(y) - 1)` over
`unitCone D` against `archHaar K` unfolds the `(𝓞 K)ˣ ⧸ torsion K`-orbits of nonzero lattice points
into the `HasSum` of whole-orthant gamma integrals `Γ_ℝ(s)^r₁ Γ_ℝ(2s)^r₂ |N(z)|^(-s)` over
`fundamentalCone K ∩ σ(I)`. -/
theorem hasSum_gamma_mul_norm_cpow_fundamentalCone
    {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    HasSum
      (fun z : ↑(fundamentalCone K ∩ (idealLattice K I : Set (mixedSpace K))) ↦
        Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
          ((mixedEmbedding.norm (z : mixedSpace K) : ℝ) : ℂ) ^ (-s))
      (∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1)
        ∂archHaar K) := by
  have hsum := ((hasSum_norm_cpow_fundamentalCone_inter_idealLattice I hs).summable.mul_left
    (Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K))
  refine hsum.hasSum_iff.mpr ?_
  set μ := (archHaar K).restrict (unitCone D)
  set G : {x : idealLattice K I // x ≠ 0} → realSpace K → ℂ :=
    fun x y ↦ (archNorm y : ℂ) ^ (s / 2) * archGaussian y ((x : idealLattice K I) : mixedSpace K)
  have hG_int (x) : Integrable (G x) μ :=
    integrableOn_unitCone_archNorm_cpow_mul_archGaussian D x (zero_lt_one.trans hs)
  have hG_sum : Summable fun x ↦ ∫ y, ‖G x y‖ ∂μ :=
    summable_integral_unitCone_norm_archNorm_cpow_mul_archGaussian hD I hs
  have hcongr : (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1))
      =ᵐ[μ] fun y ↦ ∑' x, G x y := by
    filter_upwards [ae_restrict_mem (measurableSet_unitCone hD.measurableSet)] with y hy
    rw [latticeTheta_eq_one_add _ y (mem_unitCone.mp hy).1, add_sub_cancel_left, ← tsum_mul_left]
  rw [integral_congr_ae hcongr, ← integral_tsum_of_summable_integral_norm hG_int hG_sum,
    ← (unitOrbitEquiv I).tsum_eq]
  have hprod : Summable fun p : ConePoints K I × UnitQuot K ↦ ∫ y, G (unitOrbitEquiv I p) y ∂μ :=
    ((unitOrbitEquiv I).summable_iff (f := fun x ↦ ∫ y, G x y ∂μ)).mpr
      (hG_sum.of_norm_bounded fun x ↦ norm_integral_le_integral_norm (G x))
  rw [hprod.tsum_prod]
  refine (tsum_congr fun z ↦ ?_).symm
  have horb (g : UnitQuot K) : ∫ y, G (unitOrbitEquiv I (z, g)) y ∂μ =
      ∫ y in unitCone D,
        (archNorm (g • y) : ℂ) ^ (s / 2) * archGaussian (g • y) (z : mixedSpace K) ∂archHaar K := by
    simp [G, μ, archGaussian_unitOrbitEquiv]
  simp_rw [horb]
  have hint := integrable_archGaussian_mul_archNorm_cpow
    (s := s) (fundamentalCone.norm_pos_of_mem z.2.1).ne' (zero_lt_one.trans hs)
  have hrow := hasSum_setIntegral_unitCone hD
    (by simpa only [mul_comm (archGaussian _ _)] using hint)
  rw [hrow.tsum_eq]
  simpa only [mul_comm (archGaussian _ _)] using
    integral_archGaussian_mul_archNorm_cpow (fundamentalCone.norm_pos_of_mem z.2.1).ne'
      (zero_lt_one.trans hs)

end TauCeti.LFunctions
