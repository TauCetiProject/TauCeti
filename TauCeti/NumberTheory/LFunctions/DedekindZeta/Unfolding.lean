/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import TauCeti.NumberTheory.LFunctions.Theta.Mellin.Pair
public import TauCeti.NumberTheory.LFunctions.Theta.UnitCone
public import TauCeti.NumberTheory.LFunctions.Theta.GammaIntegral
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.RingTheory.FractionalIdeal.Norm
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence

/-!
# Hecke's unfolding of the theta integral over a unit cone

For a fractional ideal `I` of a number field `K` and a fundamental domain `D` for the action of the
units modulo torsion on the norm-one hypersurface, the translates of the cone `unitCone D` under
`(𝓞 K)ˣ ⧸ torsion K` partition the positive orthant `{(y_w)_w | ∀ w, 0 < y_w}` into pairwise
disjoint measurable sets, and each unit acts measure-preservingly on `archHaar K`.

On the other hand, the nonzero points of the ideal lattice `σ(I)` break into free `(𝓞 K)ˣ`-orbits
indexed by the nonzero integral ideals `𝔟` such that `𝔟 * I` is principal, i.e., the integral ideals
in the ideal class of `I⁻¹`. Unfolding the integral of `(archNorm y)^(s/2) * (θ_{σ(I)}(y) - 1)` over
`unitCone D` against the unit orbits reduces it to `w = #μ(K)` copies of the archimedean gamma
integral over the full positive orthant for each ideal `𝔟`:

`∫_{unitCone D} N(y)^(s/2) (θ_{σ(I)}(y) - 1) dy/y = w Γ_ℝ(s)^r₁ Γ_ℝ(2s)^r₂ N(I)^(-s) ∑_𝔟 N(𝔟)^(-s)`.

Combining this unfolding with the radial Mellin substitution `hasMellin_mellinKernel_sub`, the
covolume formula `ZLattice.covolume (idealLattice K I) = N(I) 2^(-r₂) √|d_K|`, and the identity
`2 * 2^(-s) * Γ_ℝ(2s) = Γ_ℂ(s)` identifies the completed function
`(mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` on `Re s > 1` with the completed partial zeta
series `|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ∑_𝔟 N(𝔟)^(-s)` (Neukirch VII, §5, (5.3)–(5.5)).

## Main results

* `TauCeti.LFunctions.measurePreserving_unitScale`: the unit action preserves `archHaar K`.
* `TauCeti.LFunctions.summable_integral_unitCone`: absolute convergence justifying the sum-integral
  interchange on `unitCone D` for `1 < σ`.
* `TauCeti.LFunctions.integrableOn_archNorm_cpow_mul_latticeTheta_sub_one`: integrability of the
  weighted theta integrand on `unitCone D` for `1 < Re s`.
* `TauCeti.LFunctions.integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one`: Hecke's unfolding
  identity over `unitCone D`.
* `TauCeti.LFunctions.hasMellin_mellinKernel_idealLattice`: the Mellin transform of
  `mellinKernel D (idealLattice K I) - mellinConstant K` at `s / 2` is the completed partial zeta
  series on `Re s > 1`.
* `TauCeti.LFunctions.mellinKernelFEPair_Λ_idealLattice_eq`: the completed function of
  `mellinKernelFEPair hD (idealLattice K I)` at `s / 2` equals the completed partial zeta series
  on `Re s > 1`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.3)–(5.5).
-/

public section

noncomputable section

open Complex MeasureTheory Set NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.Units
open scoped ENNReal nonZeroDivisors Pointwise Real

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### Countability and measure-preserving unit action -/

private theorem countable_field : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

private theorem countable_units : Countable (𝓞 K)ˣ := by
  have : Countable K := countable_field
  have hinj : Function.Injective fun u : (𝓞 K)ˣ ↦ (u : K) := fun u v h ↦
    Units.ext (IsFractionRing.injective (𝓞 K) K h)
  exact hinj.countable

private theorem countable_units_quot_torsion : Countable ((𝓞 K)ˣ ⧸ torsion K) := by
  have : Countable (𝓞 K)ˣ := countable_units
  exact Quotient.countable

private theorem countable_idealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Countable (idealLattice K I) := by
  have : Countable K := countable_field
  have hsurj : Function.Surjective fun a : (I : Set K) ↦
      (⟨mixedEmbedding K a.1, (mem_idealLattice K I).mpr ⟨a.1, a.2, rfl⟩⟩ : idealLattice K I) := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, rfl⟩ := (mem_idealLattice K I).mp hx
    exact ⟨⟨a, ha⟩, rfl⟩
  exact hsurj.countable

omit [NumberField K] in
private theorem unitScale_eq_mul_left (u : (𝓞 K)ˣ) :
    unitScale u = ((fun w : InfinitePlace K ↦ w (u : K) ^ 2) * ·) :=
  funext fun y ↦ funext fun w ↦ unitScale_apply u y w

/-- The unit action `unitScale u` as a homeomorphism of `realSpace K`. -/
private def unitScaleHomeomorph (u : (𝓞 K)ˣ) : realSpace K ≃ₜ realSpace K where
  toFun := unitScale u
  invFun := unitScale u⁻¹
  left_inv y := by simp [unitScale_unitScale]
  right_inv y := by simp [unitScale_unitScale]
  continuous_toFun := by
    rw [unitScale_eq_mul_left]
    exact continuous_const.mul continuous_id
  continuous_invFun := by
    rw [unitScale_eq_mul_left]
    exact continuous_const.mul continuous_id

/-- The action `unitScale u` of a unit preserves the multiplicative Haar measure `archHaar K`. -/
theorem measurePreserving_unitScale (u : (𝓞 K)ˣ) :
    MeasurePreserving (unitScale u) (archHaar K) (archHaar K) := by
  refine ⟨(unitScaleHomeomorph u).continuous.measurable, ?_⟩
  have hc : ∀ w : InfinitePlace K, 0 < w (u : K) ^ 2 := fun w ↦
    pow_pos (pos_iff.mpr (by simp)) 2
  rw [unitScale_eq_mul_left]
  exact map_archHaar_mul_left hc

private theorem unitScale_of_mem_torsion {t : (𝓞 K)ˣ} (ht : t ∈ torsion K) (y : realSpace K) :
    unitScale t y = y := by
  ext w
  rw [unitScale_apply, (mem_torsion K).mp ht w, one_pow, one_mul]

/-- The unit action `unitScale` descends to the quotient `(𝓞 K)ˣ ⧸ torsion K`. -/
private def quotUnitScale (q : (𝓞 K)ˣ ⧸ torsion K) (y : realSpace K) : realSpace K :=
  Quotient.liftOn' q (fun u ↦ unitScale u y) fun u v huv ↦ by
    have hmem : u⁻¹ * v ∈ torsion K := QuotientGroup.leftRel_apply.mp huv
    calc unitScale u y = unitScale u (unitScale (u⁻¹ * v) y) := by
          rw [unitScale_of_mem_torsion hmem]
      _ = unitScale v y := by rw [unitScale_unitScale, mul_inv_cancel_left]

private theorem quotUnitScale_mk (u : (𝓞 K)ˣ) (y : realSpace K) :
    quotUnitScale (QuotientGroup.mk u) y = unitScale u y := rfl

private def unitsEquivQuotProdTorsion :
    ((𝓞 K)ˣ ⧸ torsion K) × torsion K ≃ (𝓞 K)ˣ where
  toFun p := Quotient.out p.1 * (p.2 : (𝓞 K)ˣ)
  invFun u :=
    ⟨QuotientGroup.mk u,
      ⟨(Quotient.out (QuotientGroup.mk u))⁻¹ * u, by
        rw [← QuotientGroup.eq]
        exact Quotient.out_eq (QuotientGroup.mk u)⟩⟩
  left_inv p := by
    obtain ⟨q, t⟩ := p
    have hmk : QuotientGroup.mk (s := torsion K) (Quotient.out q * (t : (𝓞 K)ˣ)) = q := by
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      rw [QuotientGroup.eq, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      exact (torsion K).inv_mem t.2
    refine Prod.ext hmk ?_
    ext : 1
    simp [hmk]
  right_inv u := by simp

private theorem unitScale_unitsEquivQuotProdTorsion
    (p : ((𝓞 K)ˣ ⧸ torsion K) × torsion K) (y : realSpace K) :
    unitScale (unitsEquivQuotProdTorsion p) y = quotUnitScale p.1 y := by
  rw [unitsEquivQuotProdTorsion, Equiv.coe_fn_mk, ← unitScale_unitScale,
    unitScale_of_mem_torsion p.2.2]
  conv_rhs => rw [← QuotientGroup.out_eq' p.1, quotUnitScale_mk]

/-! ### Tiling the positive orthant by translates of `unitCone D` -/

omit [NumberField K] in
private theorem unitScale_image_eq_preimage (u : (𝓞 K)ˣ) (s : Set (realSpace K)) :
    unitScale u '' s = unitScale u⁻¹ ⁻¹' s :=
  congrFun (image_eq_preimage_of_inverse (fun y ↦ by simp [unitScale_unitScale])
    (fun y ↦ by simp [unitScale_unitScale])) s

omit [NumberField K] in
private theorem unitScale_preimage_image (u : (𝓞 K)ˣ) (s : Set (realSpace K)) :
    unitScale u ⁻¹' (unitScale u '' s) = s := by
  ext y
  simp [unitScale_image_eq_preimage, unitScale_unitScale]

private theorem measurableSet_unitScale_image_unitCone {D : Set (realSpace K)}
    (hD : MeasurableSet D) (u : (𝓞 K)ˣ) :
    MeasurableSet (unitScale u '' unitCone D) := by
  rw [unitScale_image_eq_preimage]
  exact (measurableSet_unitCone hD).preimage (unitScaleHomeomorph u⁻¹).continuous.measurable

private theorem pairwise_disjoint_quotUnitScale_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) :
    Pairwise fun q₁ q₂ : (𝓞 K)ˣ ⧸ torsion K ↦
      Disjoint (quotUnitScale q₁ '' unitCone D) (quotUnitScale q₂ '' unitCone D) := by
  intro q₁ q₂ hne
  refine disjoint_left.mpr fun y hy₁ hy₂ ↦ hne ?_
  induction q₁ using QuotientGroup.induction_on with | H u₁ =>
  induction q₂ using QuotientGroup.induction_on with | H u₂ =>
  obtain ⟨z₁, hz₁, rfl⟩ := hy₁
  obtain ⟨z₂, hz₂, heq⟩ := hy₂
  have hz₁' := mem_unitCone.mp hz₁
  have hz₂' := mem_unitCone.mp hz₂
  have hrel : unitScale (u₂⁻¹ * u₁) z₁ = z₂ := by
    rw [← unitScale_unitScale]
    have h' : unitScale u₂ z₂ = unitScale u₁ z₁ := heq
    rw [← h', unitScale_unitScale, inv_mul_cancel, unitScale_one]
  have hs : unitScale (u₂⁻¹ * u₁) (surfacePart z₁) ∈ D := by
    rw [← surfacePart_unitScale, hrel]
    exact hz₂'.2
  have hmem : u₂⁻¹ * u₁ ∈ torsion K := (hD.unitScale_mem_iff _ hz₁'.2 _).mp hs
  rw [QuotientGroup.eq]
  simpa only [mul_inv_rev, inv_inv] using (torsion K).inv_mem hmem

private theorem iUnion_quotUnitScale_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) :
    ⋃ q : (𝓞 K)ˣ ⧸ torsion K, quotUnitScale q '' unitCone D =
      {y : realSpace K | ∀ w, 0 < y w} := by
  ext y
  simp only [mem_iUnion, mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨q, z, hz, rfl⟩ w
    induction q using QuotientGroup.induction_on with | H u =>
    exact unitScale_pos ((mem_unitCone.mp hz).1 w) u
  · intro hy
    obtain ⟨u, hu⟩ := hD.exists_unitScale_mem (surfacePart y) (surfacePart_mem_normOneSurface hy)
    refine ⟨QuotientGroup.mk u⁻¹, unitScale u y, mem_unitCone.mpr ?_, ?_⟩
    · exact ⟨fun w ↦ unitScale_pos (hy w) u, by rwa [surfacePart_unitScale]⟩
    · rw [quotUnitScale_mk, unitScale_unitScale, inv_mul_cancel, unitScale_one]

omit [NumberField K] in
private theorem coe_unitScaleHomeomorph (u : (𝓞 K)ˣ) :
    (unitScaleHomeomorph u : realSpace K → realSpace K) = unitScale u := rfl

private theorem lintegral_unitScale_image_unitCone {D : Set (realSpace K)}
    (u : (𝓞 K)ˣ) (f : realSpace K → ℝ≥0∞) :
    ∫⁻ y in unitScale u '' unitCone D, f y ∂archHaar K =
      ∫⁻ y in unitCone D, f (unitScale u y) ∂archHaar K := by
  have hmp : MeasurePreserving (unitScaleHomeomorph u) (archHaar K) (archHaar K) :=
    measurePreserving_unitScale u
  have h := (hmp.setLIntegral_comp_preimage_emb (unitScaleHomeomorph u).measurableEmbedding
    f (unitScale u '' unitCone D)).symm
  rw [coe_unitScaleHomeomorph, unitScale_preimage_image] at h
  exact h

private theorem tsum_lintegral_unitCone_eq {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (f : realSpace K → ℝ≥0∞) :
    ∑' u : (𝓞 K)ˣ, ∫⁻ y in unitCone D, f (unitScale u y) ∂archHaar K =
      (torsionOrder K : ℝ≥0∞) * ∫⁻ y, f y ∂archHaar K := by
  have : Countable ((𝓞 K)ˣ ⧸ torsion K) := countable_units_quot_torsion
  have hmeas : ∀ q : (𝓞 K)ˣ ⧸ torsion K, MeasurableSet (quotUnitScale q '' unitCone D) := by
    intro q
    induction q using QuotientGroup.induction_on with | H u =>
    exact measurableSet_unitScale_image_unitCone hD.measurableSet u
  have hsupp : (archHaar K).restrict {y : realSpace K | ∀ w, 0 < y w} = archHaar K :=
    Measure.restrict_eq_self_of_ae_mem ae_archHaar_pos
  have hsum_q : ∑' q : (𝓞 K)ˣ ⧸ torsion K,
      ∫⁻ y in unitCone D, f (quotUnitScale q y) ∂archHaar K = ∫⁻ y, f y ∂archHaar K := by
    calc ∑' q : (𝓞 K)ˣ ⧸ torsion K, ∫⁻ y in unitCone D, f (quotUnitScale q y) ∂archHaar K
        = ∑' q : (𝓞 K)ˣ ⧸ torsion K, ∫⁻ y in quotUnitScale q '' unitCone D, f y ∂archHaar K := by
          refine tsum_congr fun q ↦ ?_
          induction q using QuotientGroup.induction_on with | H u =>
          exact (lintegral_unitScale_image_unitCone u f).symm
      _ = ∫⁻ y in ⋃ q : (𝓞 K)ˣ ⧸ torsion K, quotUnitScale q '' unitCone D, f y ∂archHaar K :=
          (lintegral_iUnion hmeas (pairwise_disjoint_quotUnitScale_unitCone hD) f).symm
      _ = ∫⁻ y in {y : realSpace K | ∀ w, 0 < y w}, f y ∂archHaar K := by
          rw [iUnion_quotUnitScale_unitCone hD]
      _ = ∫⁻ y, f y ∂archHaar K := by rw [hsupp]
  have hconst (c : ℝ≥0∞) : ∑' _ : torsion K, c = (torsionOrder K : ℝ≥0∞) * c := by
    have : Fintype (torsion K) := Fintype.ofFinite _
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
    rfl
  rw [← unitsEquivQuotProdTorsion.tsum_eq, tsum_prod', ← hsum_q]
  simp_rw [unitScale_unitsEquivQuotProdTorsion, hconst, ENNReal.tsum_mul_left]

private theorem setIntegral_unitScale_image_unitCone {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {D : Set (realSpace K)} (u : (𝓞 K)ˣ) (f : realSpace K → E) :
    ∫ y in unitScale u '' unitCone D, f y ∂archHaar K =
      ∫ y in unitCone D, f (unitScale u y) ∂archHaar K := by
  have hmp : MeasurePreserving (unitScaleHomeomorph u) (archHaar K) (archHaar K) :=
    measurePreserving_unitScale u
  have h := (hmp.setIntegral_preimage_emb (unitScaleHomeomorph u).measurableEmbedding
    f (unitScale u '' unitCone D)).symm
  rw [coe_unitScaleHomeomorph, unitScale_preimage_image] at h
  exact h

private theorem tsum_integral_unitCone_eq {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) {f : realSpace K → ℂ} (hf : Integrable f (archHaar K)) :
    ∑' u : (𝓞 K)ˣ, ∫ y in unitCone D, f (unitScale u y) ∂archHaar K =
      (torsionOrder K : ℂ) * ∫ y, f y ∂archHaar K := by
  have : Countable ((𝓞 K)ˣ ⧸ torsion K) := countable_units_quot_torsion
  have hmeas : ∀ q : (𝓞 K)ˣ ⧸ torsion K, MeasurableSet (quotUnitScale q '' unitCone D) := by
    intro q
    induction q using QuotientGroup.induction_on with | H u =>
    exact measurableSet_unitScale_image_unitCone hD.measurableSet u
  have hsupp : (archHaar K).restrict {y : realSpace K | ∀ w, 0 < y w} = archHaar K :=
    Measure.restrict_eq_self_of_ae_mem ae_archHaar_pos
  have hsum_q : HasSum
      (fun q : (𝓞 K)ˣ ⧸ torsion K ↦ ∫ y in unitCone D, f (quotUnitScale q y) ∂archHaar K)
      (∫ y, f y ∂archHaar K) := by
    have hU := hasSum_integral_iUnion hmeas (pairwise_disjoint_quotUnitScale_unitCone hD)
      hf.integrableOn
    rw [iUnion_quotUnitScale_unitCone hD, hsupp] at hU
    refine hU.congr_fun fun q ↦ ?_
    induction q using QuotientGroup.induction_on with | H u =>
    exact (setIntegral_unitScale_image_unitCone u f).symm
  have hnorm : Summable fun q : (𝓞 K)ˣ ⧸ torsion K ↦
      ‖∫ y in unitCone D, f (quotUnitScale q y) ∂archHaar K‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun q ↦ norm_integral_le_integral_norm _) ?_
    have hU := hasSum_integral_iUnion hmeas (pairwise_disjoint_quotUnitScale_unitCone hD)
      hf.norm.integrableOn
    rw [iUnion_quotUnitScale_unitCone hD, hsupp] at hU
    exact (hU.congr_fun fun q ↦ by
      induction q using QuotientGroup.induction_on with | H u =>
      exact (setIntegral_unitScale_image_unitCone u (fun y ↦ ‖f y‖)).symm).summable
  have h1 : Summable fun _ : torsion K ↦ ‖(1 : ℂ)‖ := Summable.of_finite
  have hprod : HasSum
      (fun p : ((𝓞 K)ˣ ⧸ torsion K) × torsion K ↦
        (∫ y in unitCone D, f (quotUnitScale p.1 y) ∂archHaar K) * (1 : ℂ))
      ((∫ y, f y ∂archHaar K) * (torsionOrder K : ℂ)) := by
    have hs := (summable_mul_of_summable_norm hnorm h1).hasSum
    rw [← tsum_mul_tsum_of_summable_norm hnorm h1, hsum_q.tsum_eq, tsum_const, nsmul_eq_mul,
      mul_one] at hs
    exact hs
  rw [← unitsEquivQuotProdTorsion.tsum_eq, mul_comm]
  refine (hprod.congr_fun fun p ↦ ?_).tsum_eq
  simp only [mul_one, unitScale_unitsEquivQuotProdTorsion]

/-! ### Unit orbits of nonzero points of an ideal lattice -/

private theorem spanSingleton_le_iff_exists_coeIdeal {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {a : K}
    (ha : a ≠ 0) :
    a ∈ (I : FractionalIdeal (𝓞 K)⁰ K) ↔
      ∃ 𝔟 : (Ideal (𝓞 K))⁰,
        ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ a := by
  constructor
  · intro haI
    have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ a ≤ (I : FractionalIdeal (𝓞 K)⁰ K) :=
      FractionalIdeal.spanSingleton_le_iff_mem.mpr haI
    have hle1 : FractionalIdeal.spanSingleton (𝓞 K)⁰ a * ((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) ≤ 1 := by
      have hmul : FractionalIdeal.spanSingleton (𝓞 K)⁰ a * (I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ≤
          (I : FractionalIdeal (𝓞 K)⁰ K) * (I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := by
        gcongr
      have hinv : (I : FractionalIdeal (𝓞 K)⁰ K) * (I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      exact hmul.trans_eq hinv
    obtain ⟨𝔟, h𝔟⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle1
    have h𝔟_ne : 𝔟 ≠ ⊥ := by
      intro hbot
      rw [hbot, FractionalIdeal.coeIdeal_bot] at h𝔟
      have h0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ a = 0 := by
        calc FractionalIdeal.spanSingleton (𝓞 K)⁰ a
            = FractionalIdeal.spanSingleton (𝓞 K)⁰ a *
                ((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) *
                (I : FractionalIdeal (𝓞 K)⁰ K) := by
              rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
          _ = 0 * (I : FractionalIdeal (𝓞 K)⁰ K) := by rw [← h𝔟]
          _ = 0 := zero_mul _
      exact ha (FractionalIdeal.spanSingleton_eq_zero_iff.mp h0)
    refine ⟨⟨𝔟, mem_nonZeroDivisors_of_ne_zero h𝔟_ne⟩, ?_⟩
    dsimp only
    rw [h𝔟, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  · rintro ⟨𝔟, h𝔟⟩
    apply FractionalIdeal.spanSingleton_le_iff_mem.mp
    rw [← h𝔟]
    exact mul_le_of_le_one_left' FractionalIdeal.coeIdeal_le_one

private def idealClassGen (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
      ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)}) : Kˣ :=
  𝔟.2.choose

private theorem idealClassGen_spec (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
      ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)}) :
    ((𝔟.1 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (idealClassGen I 𝔟 : K) :=
  𝔟.2.choose_spec

private theorem norm_mixedEmbedding_idealClassGen (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
      ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)}) :
    mixedEmbedding.norm (mixedEmbedding K (idealClassGen I 𝔟 : K)) =
      (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℝ) *
        (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
  have hrat : |Algebra.norm ℚ (idealClassGen I 𝔟 : K)| =
      (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℚ) *
        FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← FractionalIdeal.absNorm_span_singleton (𝓞 K), ← idealClassGen_spec I 𝔟, map_mul,
      FractionalIdeal.coeIdeal_absNorm]
  rw [mixedEmbedding.norm_eq_norm]
  exact_mod_cast hrat

private theorem norm_mixedEmbedding_idealClassGen_pos (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
      ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)}) :
    0 < mixedEmbedding.norm (mixedEmbedding K (idealClassGen I 𝔟 : K)) := by
  rw [norm_mixedEmbedding_idealClassGen]
  exact mul_pos (Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors 𝔟.1))
    (Rat.cast_pos.mpr ((FractionalIdeal.absNorm_nonneg _).lt_of_ne'
      (FractionalIdeal.absNorm_eq_zero_iff.not.mpr I.ne_zero)))

/-- Decomposition of the nonzero points of the ideal lattice `σ(I)` into free `(𝓞 K)ˣ`-orbits,
indexed by the nonzero integral ideals `𝔟` with `𝔟 * I` principal. -/
private def idealLatticeOrbitEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
      ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)} × (𝓞 K)ˣ ≃
      {x : idealLattice K I // x ≠ 0} := by
  refine Equiv.ofBijective
    (fun p ↦ ⟨⟨p.2 • mixedEmbedding K (idealClassGen I p.1 : K),
      (p.2.unitSMul_mem_idealLattice_iff I _).mpr
        ((mem_idealLattice K I).mpr ⟨_, (spanSingleton_le_iff_exists_coeIdeal
          (idealClassGen I p.1).ne_zero).mpr ⟨p.1.1, idealClassGen_spec I p.1⟩, rfl⟩)⟩, ?_⟩)
    ⟨?_, ?_⟩
  · intro h0
    have hval : p.2 • mixedEmbedding K (idealClassGen I p.1 : K) = 0 := congrArg Subtype.val h0
    rw [unitSMul_smul, ← map_mul] at hval
    have hu0 : (algebraMap (𝓞 K) K) (p.2 : 𝓞 K) ≠ 0 := fun h ↦
      p.2.ne_zero (IsFractionRing.injective (𝓞 K) K (h.trans (map_zero _).symm))
    exact mul_ne_zero hu0 (idealClassGen I p.1).ne_zero
      (mixedEmbedding_injective K (by simpa using hval))
  · rintro ⟨𝔟₁, u₁⟩ ⟨𝔟₂, u₂⟩ h
    have hval : u₁ • mixedEmbedding K (idealClassGen I 𝔟₁ : K) =
        u₂ • mixedEmbedding K (idealClassGen I 𝔟₂ : K) :=
      congrArg (fun z : {x : idealLattice K I // x ≠ 0} ↦ (z.1 : mixedSpace K)) h
    rw [unitSMul_smul, unitSMul_smul, ← map_mul, ← map_mul] at hval
    have hK : (u₁ : K) * (idealClassGen I 𝔟₁ : K) = (u₂ : K) * (idealClassGen I 𝔟₂ : K) :=
      mixedEmbedding_injective K hval
    have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ (idealClassGen I 𝔟₁ : K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (idealClassGen I 𝔟₂ : K) := by
      have hu : (u₂⁻¹ * u₁ : (𝓞 K)ˣ) • (idealClassGen I 𝔟₁ : K) = (idealClassGen I 𝔟₂ : K) := by
        have : ((u₂ : K)⁻¹ * (u₁ : K)) * (idealClassGen I 𝔟₁ : K) = (idealClassGen I 𝔟₂ : K) := by
          rw [mul_assoc, hK, inv_mul_cancel_left₀ (by simp)]
        simpa [Units.smul_def, Algebra.smul_def] using this
      exact FractionalIdeal.spanSingleton_eq_spanSingleton.mpr ⟨u₂⁻¹ * u₁, hu⟩
    have h𝔟_eq : 𝔟₁ = 𝔟₂ := by
      ext1; ext1
      apply FractionalIdeal.coeIdeal_injective (K := K)
      have hmul : ((𝔟₁.1 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
          (I : FractionalIdeal (𝓞 K)⁰ K) =
          ((𝔟₂.1 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
            (I : FractionalIdeal (𝓞 K)⁰ K) := by
        rw [idealClassGen_spec I 𝔟₁, idealClassGen_spec I 𝔟₂, hspan]
      simpa using mul_right_cancel₀ I.ne_zero hmul
    subst h𝔟_eq
    exact Prod.ext rfl (Units.ext (IsFractionRing.injective (𝓞 K) K
      (mul_right_cancel₀ (idealClassGen I 𝔟₁).ne_zero hK)))
  · rintro ⟨⟨x, hxI⟩, hx0⟩
    obtain ⟨a, haI, rfl⟩ := (mem_idealLattice K I).mp hxI
    have ha0 : a ≠ 0 := by intro h; apply hx0; ext1; simp [h]
    obtain ⟨𝔟, h𝔟⟩ := (spanSingleton_le_iff_exists_coeIdeal ha0).mp haI
    let 𝔟' : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
        ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)} := ⟨𝔟, Units.mk0 a ha0, h𝔟⟩
    have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ (idealClassGen I 𝔟' : K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ a := by
      rw [← idealClassGen_spec I 𝔟', h𝔟]
    obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hspan
    refine ⟨⟨𝔟', u⟩, ?_⟩
    ext1; ext1
    -- Express the unit action via multiplication in `K` to match `hu`.
    change u • mixedEmbedding K (idealClassGen I 𝔟' : K) = mixedEmbedding K a
    rw [unitSMul_smul, ← map_mul]
    exact congrArg (mixedEmbedding K) (by simpa [Units.smul_def, Algebra.smul_def] using hu)

private theorem idealLatticeOrbitEquiv_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
      ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)} × (𝓞 K)ˣ) :
    ((idealLatticeOrbitEquiv I p).1 : mixedSpace K) =
      p.2 • mixedEmbedding K (idealClassGen I p.1 : K) := rfl

/-! ### Absolute convergence and unfolding over `unitCone D` -/

private theorem integrable_norm_archGaussian_mul_archNorm_rpow {x : mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun y ↦ ‖archGaussian y x‖ * archNorm y ^ (σ / 2)) (archHaar K) := by
  have hint := (integrable_archGaussian_mul_archNorm_cpow hx (s := (σ : ℂ)) (by simpa)).norm
  refine hint.congr ?_
  filter_upwards [ae_archHaar_pos] with y hy
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (archNorm_pos hy)]
  simp

private theorem integral_norm_archGaussian_mul_archNorm_rpow {x : mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) {σ : ℝ} (hσ : 0 < σ) :
    ∫ y, ‖archGaussian y x‖ * archNorm y ^ (σ / 2) ∂archHaar K =
      ‖Gammaℝ (σ : ℂ) ^ nrRealPlaces K * Gammaℝ (2 * (σ : ℂ)) ^ nrComplexPlaces K‖ *
        mixedEmbedding.norm x ^ (-σ) := by
  have hval := integral_archGaussian_mul_archNorm_cpow hx (s := (σ : ℂ)) (by simpa)
  have hae : (fun y ↦ archGaussian y x * (archNorm y : ℂ) ^ ((σ : ℂ) / 2)) =ᵐ[archHaar K]
      fun y ↦ ((‖archGaussian y x‖ * archNorm y ^ (σ / 2) : ℝ) : ℂ) := by
    filter_upwards [ae_archHaar_pos] with y hy
    have hcp : (archNorm y : ℂ) ^ ((σ : ℂ) / 2) = ((archNorm y ^ (σ / 2) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_ofNat, ← Complex.ofReal_div, Complex.ofReal_cpow (archNorm_pos hy).le]
    rw [hcp, archGaussian_apply, Complex.norm_real, Real.norm_eq_abs,
      Real.abs_exp, Complex.ofReal_mul]
  have heq : ((∫ y, ‖archGaussian y x‖ * archNorm y ^ (σ / 2) ∂archHaar K : ℝ) : ℂ) =
      Gammaℝ (σ : ℂ) ^ nrRealPlaces K * Gammaℝ (2 * (σ : ℂ)) ^ nrComplexPlaces K *
        (mixedEmbedding.norm x : ℂ) ^ (-(σ : ℂ)) := by
    calc ((∫ y, ‖archGaussian y x‖ * archNorm y ^ (σ / 2) ∂archHaar K : ℝ) : ℂ)
        = Complex.ofRealCLM (∫ y, ‖archGaussian y x‖ * archNorm y ^ (σ / 2) ∂archHaar K) := rfl
      _ = ∫ y, Complex.ofRealCLM (‖archGaussian y x‖ * archNorm y ^ (σ / 2)) ∂archHaar K :=
          (Complex.ofRealCLM.integral_comp_comm
            (integrable_norm_archGaussian_mul_archNorm_rpow hx hσ)).symm
      _ = ∫ y, archGaussian y x * (archNorm y : ℂ) ^ ((σ : ℂ) / 2) ∂archHaar K :=
          (integral_congr_ae hae).symm
      _ = _ := hval
  have hnonneg : 0 ≤ ∫ y, ‖archGaussian y x‖ * archNorm y ^ (σ / 2) ∂archHaar K := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_archHaar_pos] with y hy
    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (archNorm_pos hy).le _)
  have hnorm_pos : 0 < mixedEmbedding.norm x := (mixedEmbedding.norm_nonneg x).lt_of_ne' hx
  have hnorm_eq := congrArg (fun z : ℂ ↦ ‖z‖) heq
  rw [Complex.norm_real, Real.norm_of_nonneg hnonneg, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hnorm_pos] at hnorm_eq
  simpa using hnorm_eq

private theorem lintegral_norm_archGaussian_mul_archNorm_rpow {x : mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) {σ : ℝ} (hσ : 0 < σ) :
    ∫⁻ y, ENNReal.ofReal (‖archGaussian y x‖ * archNorm y ^ (σ / 2)) ∂archHaar K =
      ENNReal.ofReal (‖Gammaℝ (σ : ℂ) ^ nrRealPlaces K *
        Gammaℝ (2 * (σ : ℂ)) ^ nrComplexPlaces K‖ * mixedEmbedding.norm x ^ (-σ)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_norm_archGaussian_mul_archNorm_rpow hx hσ),
    integral_norm_archGaussian_mul_archNorm_rpow hx hσ]
  filter_upwards [ae_archHaar_pos] with y hy
  exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (archNorm_pos hy).le _)

private theorem norm_ne_zero_of_idealLattice_ne_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : {x : idealLattice K I // x ≠ 0}) :
    mixedEmbedding.norm (x.1 : mixedSpace K) ≠ 0 := by
  obtain ⟨a, -, ha⟩ := (mem_idealLattice K I).mp x.1.2
  have ha0 : a ≠ 0 := by intro h; apply x.2; ext1; simp [← ha, h]
  rw [← ha, mixedEmbedding.norm_eq_norm]
  exact Rat.cast_ne_zero.mpr (abs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr ha0))

private theorem lintegral_unitCone_tsum_lt_top {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {σ : ℝ} (hσ : 1 < σ) :
    ∑' x : {x : idealLattice K I // x ≠ 0},
      ∫⁻ y in unitCone D,
        ENNReal.ofReal (‖archGaussian y (x.1 : mixedSpace K)‖ * archNorm y ^ (σ / 2))
          ∂archHaar K < ⊤ := by
  have hσ0 : 0 < σ := zero_lt_one.trans hσ
  set C : ℝ := ‖Gammaℝ (σ : ℂ) ^ nrRealPlaces K * Gammaℝ (2 * (σ : ℂ)) ^ nrComplexPlaces K‖
  have hI_pos : 0 < (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) :=
    Rat.cast_pos.mpr ((FractionalIdeal.absNorm_nonneg _).lt_of_ne'
      (FractionalIdeal.absNorm_eq_zero_iff.not.mpr I.ne_zero))
  rw [← (idealLatticeOrbitEquiv I).tsum_eq, tsum_prod']
  have hinner : ∀ 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
      ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
      ∑' u : (𝓞 K)ˣ, ∫⁻ y in unitCone D,
        ENNReal.ofReal (‖archGaussian y ((idealLatticeOrbitEquiv I (𝔟, u)).1 : mixedSpace K)‖ *
          archNorm y ^ (σ / 2)) ∂archHaar K =
        ENNReal.ofReal ((torsionOrder K : ℝ) * C *
          (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ (-σ) *
          (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℝ) ^ (-σ)) := by
    intro 𝔟
    let g : realSpace K → ℝ≥0∞ := fun y ↦
      ENNReal.ofReal (‖archGaussian y (mixedEmbedding K (idealClassGen I 𝔟 : K))‖ *
        archNorm y ^ (σ / 2))
    have hcongr : ∀ u : (𝓞 K)ˣ, ∫⁻ y in unitCone D,
        ENNReal.ofReal (‖archGaussian y ((idealLatticeOrbitEquiv I (𝔟, u)).1 : mixedSpace K)‖ *
          archNorm y ^ (σ / 2)) ∂archHaar K =
        ∫⁻ y in unitCone D, g (unitScale u y) ∂archHaar K := fun u ↦ by
      simp_rw [g, idealLatticeOrbitEquiv_apply, archGaussian_unit_smul, archNorm_unitScale]
    simp_rw [hcongr]
    rw [tsum_lintegral_unitCone_eq hD g,
      lintegral_norm_archGaussian_mul_archNorm_rpow
        (norm_mixedEmbedding_idealClassGen_pos I 𝔟).ne' hσ0,
      norm_mixedEmbedding_idealClassGen I 𝔟,
      Real.mul_rpow (Nat.cast_nonneg _) hI_pos.le,
      ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  simp_rw [hinner]
  have hsum_ideal : Summable fun 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
      ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)} ↦
      (torsionOrder K : ℝ) * C *
        (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ (-σ) *
        (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℝ) ^ (-σ) :=
    ((summable_absNorm_rpow_ideal_iff (K := K)).mpr hσ).subtype _ |>.mul_left _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun 𝔟 ↦ by positivity) hsum_ideal]
  exact ENNReal.ofReal_lt_top

/-- **Absolute convergence of the unfolded cone integral.** For `1 < σ`, the integrals over
`unitCone D` of `‖archGaussian y x‖ * archNorm y ^ (σ / 2)` over all nonzero points `x` of the
ideal lattice `σ(I)` form a summable family of real numbers. -/
theorem summable_integral_unitCone {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun x : {x : idealLattice K I // x ≠ 0} ↦
      ∫ y in unitCone D, ‖archGaussian y (x.1 : mixedSpace K)‖ * archNorm y ^ (σ / 2)
        ∂archHaar K := by
  have hσ0 : 0 < σ := zero_lt_one.trans hσ
  have hnn : ∀ x : {x : idealLattice K I // x ≠ 0},
      0 ≤ ∫ y in unitCone D,
        ‖archGaussian y (x.1 : mixedSpace K)‖ * archNorm y ^ (σ / 2) ∂archHaar K := fun x ↦ by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_of_ae ae_archHaar_pos] with y hy
    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (archNorm_pos hy).le _)
  let g : {x : idealLattice K I // x ≠ 0} → NNReal := fun x ↦
    Real.toNNReal (∫ y in unitCone D,
      ‖archGaussian y (x.1 : mixedSpace K)‖ * archNorm y ^ (σ / 2) ∂archHaar K)
  have hterm : ∀ x : {x : idealLattice K I // x ≠ 0},
      (g x : ℝ≥0∞) = ∫⁻ y in unitCone D,
        ENNReal.ofReal (‖archGaussian y (x.1 : mixedSpace K)‖ * archNorm y ^ (σ / 2))
          ∂archHaar K := fun x ↦ by
    -- By definition, `ENNReal.ofReal r` is the coercion of `Real.toNNReal r`.
    change ENNReal.ofReal _ = _
    refine ofReal_integral_eq_lintegral_ofReal
      (integrable_norm_archGaussian_mul_archNorm_rpow (norm_ne_zero_of_idealLattice_ne_zero I x)
        hσ0).integrableOn ?_
    filter_upwards [ae_restrict_of_ae ae_archHaar_pos] with y hy
    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (archNorm_pos hy).le _)
  have hne : ∑' x : {x : idealLattice K I // x ≠ 0}, (g x : ℝ≥0∞) ≠ ⊤ := by
    simp_rw [hterm]
    exact (lintegral_unitCone_tsum_lt_top hD I hσ).ne
  exact (NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp hne)).congr fun x ↦
    Real.coe_toNNReal _ (hnn x)

/-- **Integrability of the weighted theta kernel on `unitCone D`.** For `1 < Re s`, the function
`y ↦ N(y)^(s/2) * (θ_{σ(I)}(y) - 1)` is integrable on `unitCone D` against `archHaar K`. -/
theorem integrableOn_archNorm_cpow_mul_latticeTheta_sub_one {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn
      (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1))
      (unitCone D) (archHaar K) := by
  have : Countable (idealLattice K I) := countable_idealLattice I
  have hcont : ContinuousOn
      (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1))
      {y : realSpace K | ∀ w, 0 < y w} := by
    intro y hy
    have h1 : ContinuousAt (fun z : realSpace K ↦ (archNorm z : ℂ) ^ (s / 2)) y := by
      refine ContinuousAt.cpow (Complex.continuous_ofReal.continuousAt.comp
        continuous_archNorm.continuousAt) continuousAt_const ?_
      exact Or.inl (by simpa using archNorm_pos hy)
    have h2 : ContinuousAt (fun z : realSpace K ↦ latticeTheta (idealLattice K I) z - 1) y :=
      (continuousAt_latticeTheta (idealLattice K I) hy).sub continuousAt_const
    exact (h1.mul h2).continuousWithinAt
  have haesm : AEStronglyMeasurable
      (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1))
      ((archHaar K).restrict (unitCone D)) :=
    (hcont.mono fun y hy ↦ (mem_unitCone.mp hy).1).aestronglyMeasurable
      (measurableSet_unitCone hD.measurableSet)
  refine ⟨haesm, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hbound : ∫⁻ y in unitCone D,
      ENNReal.ofReal ‖(archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1)‖
        ∂archHaar K ≤
      ∑' x : {x : idealLattice K I // x ≠ 0}, ∫⁻ y in unitCone D,
        ENNReal.ofReal (‖archGaussian y (x.1 : mixedSpace K)‖ * archNorm y ^ (s.re / 2))
          ∂archHaar K := by
    calc ∫⁻ y in unitCone D,
          ENNReal.ofReal ‖(archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1)‖
            ∂archHaar K
        ≤ ∫⁻ y in unitCone D,
            ∑' x : {x : idealLattice K I // x ≠ 0},
              ENNReal.ofReal (‖archGaussian y (x.1 : mixedSpace K)‖ * archNorm y ^ (s.re / 2))
            ∂archHaar K := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem (measurableSet_unitCone hD.measurableSet)] with y hy
          have hypos : ∀ w, 0 < y w := (mem_unitCone.mp hy).1
          have hsub : latticeTheta (idealLattice K I) y - 1 =
              ∑' x : {x : idealLattice K I // x ≠ 0}, archGaussian y (x.1 : mixedSpace K) := by
            rw [latticeTheta_eq_one_add _ y hypos, add_sub_cancel_left]
          have hsum_norm : Summable fun x : {x : idealLattice K I // x ≠ 0} ↦
              ‖archGaussian y (x.1 : mixedSpace K)‖ :=
            (summable_norm_archGaussian (idealLattice K I) y hypos).subtype _
          have hle : ‖(archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1)‖ ≤
              ∑' x : {x : idealLattice K I // x ≠ 0},
                ‖archGaussian y (x.1 : mixedSpace K)‖ * archNorm y ^ (s.re / 2) := by
            rw [hsub, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (archNorm_pos hypos),
              Complex.div_ofNat_re, mul_comm, tsum_mul_right]
            exact mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hsum_norm)
              (Real.rpow_nonneg (archNorm_pos hypos).le _)
          calc ENNReal.ofReal
                ‖(archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1)‖
              ≤ ENNReal.ofReal (∑' x : {x : idealLattice K I // x ≠ 0},
                  ‖archGaussian y (x.1 : mixedSpace K)‖ * archNorm y ^ (s.re / 2)) :=
                ENNReal.ofReal_le_ofReal hle
            _ = ∑' x : {x : idealLattice K I // x ≠ 0},
                  ENNReal.ofReal (‖archGaussian y (x.1 : mixedSpace K)‖ *
                    archNorm y ^ (s.re / 2)) :=
                ENNReal.ofReal_tsum_of_nonneg
                  (fun _ ↦ mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (archNorm_pos hypos).le _))
                  (hsum_norm.mul_right _)
      _ = ∑' x : {x : idealLattice K I // x ≠ 0}, ∫⁻ y in unitCone D,
            ENNReal.ofReal (‖archGaussian y (x.1 : mixedSpace K)‖ * archNorm y ^ (s.re / 2))
            ∂archHaar K :=
          lintegral_tsum fun x ↦
            (((continuous_archGaussian _).norm.mul
              (continuous_archNorm.rpow_const fun _ ↦ Or.inr (by positivity))
              ).measurable.ennreal_ofReal).aemeasurable
  exact hbound.trans_lt (lintegral_unitCone_tsum_lt_top hD I hs)

/-- **Hecke's unfolding of the theta integral over `unitCone D`.** For `1 < Re s`, the weighted
theta integral over `unitCone D` unfolds into `w` copies of the archimedean gamma integral summed
over the nonzero integral ideals `𝔟` with `𝔟 * I` principal. -/
theorem integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    ∫ y in unitCone D,
        (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1) ∂archHaar K =
      (torsionOrder K : ℂ) * Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s) *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
            ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
          (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  have : Countable (idealLattice K I) := countable_idealLattice I
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  let F : {x : idealLattice K I // x ≠ 0} → realSpace K → ℂ :=
    fun x y ↦ (archNorm y : ℂ) ^ (s / 2) * archGaussian y (x.1 : mixedSpace K)
  have hF_eq : (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1))
      =ᵐ[(archHaar K).restrict (unitCone D)] fun y ↦ ∑' x, F x y := by
    filter_upwards [ae_restrict_mem (measurableSet_unitCone hD.measurableSet)] with y hy
    have hsub : latticeTheta (idealLattice K I) y - 1 =
        ∑' x : {x : idealLattice K I // x ≠ 0}, archGaussian y (x.1 : mixedSpace K) := by
      rw [latticeTheta_eq_one_add _ y (mem_unitCone.mp hy).1, add_sub_cancel_left]
    rw [hsub, ← tsum_mul_left]
  have hF_int : ∀ x : {x : idealLattice K I // x ≠ 0},
      IntegrableOn (F x) (unitCone D) (archHaar K) := fun x ↦ by
    have h := integrable_archGaussian_mul_archNorm_cpow
      (norm_ne_zero_of_idealLattice_ne_zero I x) hs0
    simpa only [F, mul_comm] using h.integrableOn
  have hF_sum : Summable fun x : {x : idealLattice K I // x ≠ 0} ↦
      ∫ y in unitCone D, ‖F x y‖ ∂archHaar K := by
    refine (summable_integral_unitCone hD I hs).congr fun x ↦ ?_
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae ae_archHaar_pos] with y hy
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (archNorm_pos hy), Complex.div_ofNat_re,
      mul_comm]
  have hsum_F : Summable fun x : {x : idealLattice K I // x ≠ 0} ↦
      ∫ y in unitCone D, F x y ∂archHaar K :=
    Summable.of_norm_bounded hF_sum fun x ↦ norm_integral_le_integral_norm _
  have hnorm_sum_pair : Summable fun p : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
      ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)} × (𝓞 K)ˣ ↦
      ∫ y in unitCone D, F (idealLatticeOrbitEquiv I p) y ∂archHaar K :=
    ((idealLatticeOrbitEquiv I).summable_iff).mpr hsum_F
  rw [integral_congr_ae hF_eq, ← integral_tsum_of_summable_integral_norm hF_int hF_sum,
    ← (idealLatticeOrbitEquiv I).tsum_eq,
    hnorm_sum_pair.tsum_prod' (fun 𝔟 ↦ hnorm_sum_pair.comp_injective
      (fun _ _ h ↦ (Prod.mk.inj h).2))]
  have hinner : ∀ 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
      ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
      ∑' u : (𝓞 K)ˣ, ∫ y in unitCone D, F (idealLatticeOrbitEquiv I (𝔟, u)) y ∂archHaar K =
        (torsionOrder K : ℂ) * Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
          ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s) *
          (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
    intro 𝔟
    set x₀ := mixedEmbedding K (idealClassGen I 𝔟 : K)
    have hx₀ : mixedEmbedding.norm x₀ ≠ 0 := (norm_mixedEmbedding_idealClassGen_pos I 𝔟).ne'
    have hstep : ∀ u : (𝓞 K)ˣ,
        ∫ y in unitCone D, F (idealLatticeOrbitEquiv I (𝔟, u)) y ∂archHaar K =
          ∫ y in unitCone D, archGaussian (unitScale u y) x₀ *
            (archNorm (unitScale u y) : ℂ) ^ (s / 2) ∂archHaar K := fun u ↦ by
      simp_rw [F, idealLatticeOrbitEquiv_apply, archGaussian_unit_smul, archNorm_unitScale,
        mul_comm]
      rfl
    simp_rw [hstep]
    rw [tsum_integral_unitCone_eq hD (integrable_archGaussian_mul_archNorm_cpow hx₀ hs0),
      integral_archGaussian_mul_archNorm_cpow hx₀ hs0,
      norm_mixedEmbedding_idealClassGen I 𝔟]
    have hI_nn : 0 ≤ (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) :=
      Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) hI_nn,
      Complex.ofReal_natCast, Complex.ofReal_ratCast]
    ring
  simp_rw [hinner, tsum_mul_left]

/-! ### Constant assembly and identification of `mellinKernelFEPair` -/

private theorem two_mul_two_cpow_neg_mul_Gammaℝ_two_mul (s : ℂ) :
    2 * (2 : ℂ) ^ (-s) * Gammaℝ (2 * s) = Gammaℂ s := by
  have h1 : -(2 * s) / 2 = -s := by ring
  have h2 : (2 * s) / 2 = s := by ring
  rw [Gammaℝ_def, Gammaℂ_def, h1, h2]
  have hmul : (2 : ℂ) ^ (-s) * (π : ℂ) ^ (-s) = (2 * π : ℂ) ^ (-s) := by
    simpa using (Complex.mul_cpow_ofReal_nonneg (a := (2 : ℝ)) (b := π)
      (by positivity) Real.pi_pos.le (-s)).symm
  calc 2 * (2 : ℂ) ^ (-s) * ((π : ℂ) ^ (-s) * Gamma s)
      = 2 * ((2 : ℂ) ^ (-s) * (π : ℂ) ^ (-s)) * Gamma s := by ring
    _ = 2 * (2 * π : ℂ) ^ (-s) * Gamma s := by rw [hmul]

open scoped Classical in
private theorem covolume_sq_cpow_idealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    ((ZLattice.covolume (idealLattice K I) volume : ℝ) ^ 2 : ℂ) ^ (s / 2) =
      ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s *
        ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K *
        ((|discr K| : ℤ) : ℂ) ^ (s / 2) := by
  have hI_nn : 0 ≤ (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) :=
    Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)
  have hV_nn : 0 ≤ ZLattice.covolume (idealLattice K I) volume :=
    (ZLattice.covolume_pos (idealLattice K I) volume).le
  have hsq : ((ZLattice.covolume (idealLattice K I) volume : ℂ) ^ 2) ^ (s / 2) =
      (ZLattice.covolume (idealLattice K I) volume : ℂ) ^ s := by
    rw [TauCeti.ofReal_pow_cpow hV_nn]
    congr 1
    push_cast
    ring
  have h2inv : ((2 : ℂ)⁻¹) ^ s = (2 : ℂ) ^ (-s) := by
    rw [Complex.inv_cpow _ _ (by
      simpa using (Complex.arg_ofReal_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).symm ▸
        Real.pi_pos.ne),
      Complex.cpow_neg]
  have h2pow : ∀ n : ℕ, (((2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) ^ s = ((2 : ℂ) ^ (-s)) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Complex.ofReal_mul, TauCeti.ofReal_mul_cpow (by positivity), ih, pow_succ,
        Complex.ofReal_inv, Complex.ofReal_ofNat, h2inv]
  have hsqrt : (Real.sqrt |(discr K : ℝ)| : ℂ) ^ s = ((|discr K| : ℤ) : ℂ) ^ (s / 2) := by
    set x : ℝ := |(discr K : ℝ)|
    have hx : 0 ≤ x := abs_nonneg _
    have hlog_im : (Complex.log (x : ℂ)).im = 0 := by
      rw [Complex.log_im, Complex.arg_ofReal_of_nonneg hx]
    have hcast : (x : ℂ) = ((|discr K| : ℤ) : ℂ) := by
      simp only [x, ← Int.cast_abs, Complex.ofReal_intCast]
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx, ← Complex.cpow_mul]
    · rw [hcast]
      simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
      congr 1
      ring
    · rw [Complex.mul_im, hlog_im]
      simp [Real.pi_pos]
    · rw [Complex.mul_im, hlog_im]
      simp [Real.pi_pos.le]
  rw [hsq, covolume_idealLattice, mul_assoc, Complex.ofReal_mul,
    TauCeti.ofReal_mul_cpow hI_nn, Complex.ofReal_mul,
    TauCeti.ofReal_mul_cpow (by positivity), h2pow, hsqrt, Complex.ofReal_ratCast, ← mul_assoc]

/-- **The Mellin transform of the theta kernel of an ideal lattice.** For `1 < Re s` and any unit
fundamental domain `D`, the Mellin transform at `s / 2` of `mellinKernel D (idealLattice K I) - a₀`
is `|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ∑_𝔟 N(𝔟)^(-s)` (Neukirch VII, §5, (5.5)). -/
theorem hasMellin_mellinKernel_idealLattice {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun u ↦ mellinKernel D (idealLattice K I) u - (mellinConstant K : ℂ)) (s / 2)
      (((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
            ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
          (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by
  classical
  have hm := hasMellin_mellinKernel_sub hD.measurableSet hD.isBounded (idealLattice K I) s
    (integrableOn_archNorm_cpow_mul_latticeTheta_sub_one hD I hs)
  have hmc : (mellinConstant K : ℂ) =
      (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
        ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ) := by
    rw [mellinConstant_eq_mul_surfaceHaar_real hD]
    push_cast
    rfl
  rw [← hmc, integral_unitCone_archNorm_cpow_mul_latticeTheta_sub_one hD I hs,
    covolume_sq_cpow_idealLattice I s] at hm
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  have hI0 : ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ≠ 0 := by
    exact_mod_cast FractionalIdeal.absNorm_eq_zero_iff.not.mpr I.ne_zero
  have hIcancel : ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s *
      ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s) = 1 := by
    rw [← Complex.cpow_add _ _ hI0, add_neg_cancel, Complex.cpow_zero]
  have hgamma : (2 : ℂ) ^ nrComplexPlaces K * ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K *
      Gammaℝ (2 * s) ^ nrComplexPlaces K = Gammaℂ s ^ nrComplexPlaces K := by
    rw [← mul_pow, ← mul_pow, two_mul_two_cpow_neg_mul_Gammaℝ_two_mul]
  have hval : (2 : ℂ) ^ nrComplexPlaces K / (torsionOrder K : ℂ) *
      (((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s *
        ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K * ((|discr K| : ℤ) : ℂ) ^ (s / 2)) *
      ((torsionOrder K : ℂ) * Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s) *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
            ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
          (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-s)) =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
            ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
          (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
    calc _ = ((torsionOrder K : ℂ) / (torsionOrder K : ℂ)) *
          (((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s *
            ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s)) *
          ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
          ((2 : ℂ) ^ nrComplexPlaces K * ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K *
            Gammaℝ (2 * s) ^ nrComplexPlaces K) *
          ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
              ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
                FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
            (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by ring
      _ = _ := by rw [div_self hw, hIcancel, hgamma, one_mul, one_mul]
  rwa [hval] at hm

/-- **Identification of `mellinKernelFEPair` for an ideal lattice.** For `1 < Re s` and any unit
fundamental domain `D`, the completed function `(mellinKernelFEPair hD (idealLattice K I)).Λ` at
`s / 2` equals the completed partial zeta series of the class of `I⁻¹`. -/
theorem mellinKernelFEPair_Λ_idealLattice_eq {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
            ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
          (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  have hre : (1 / 2 : ℝ) < (s / 2).re := by
    rw [Complex.div_ofNat_re]
    linarith
  have h1 := hasMellin_mellinKernel_sub_mellinConstant hD (idealLattice K I) hre
  have h2 := hasMellin_mellinKernel_idealLattice hD I hs
  exact h1.2.symm.trans h2.2

end TauCeti.LFunctions
