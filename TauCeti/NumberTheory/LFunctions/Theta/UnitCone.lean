/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Theta.Mellin.Kernel
public import TauCeti.NumberTheory.LFunctions.Theta.Surface.Cone
import Mathlib.Logic.Encodable.Pi
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import TauCeti.NumberTheory.NumberField.Units.Dirichlet

/-!
# Unit-orbit unfolding and the Mellin transform over a unit cone

Let `D` be a fundamental domain (`IsUnitFundamentalDomain K D`) for the action `unitScale` of
`(𝓞 K)ˣ` on the norm-one hypersurface `S` of a number field `K`. Its positive cone `unitCone D` is a
fundamental domain for the free part of `(𝓞 K)ˣ` acting on `(realSpace K, archHaar K)`, while the
finite torsion subgroup `Units.torsion K` of order `w = Units.torsionOrder K` acts trivially on all
parameters. Summing over all units `u : (𝓞 K)ˣ` therefore unfolds an integral over `archHaar K` with
multiplicity `w`:

* `lintegral_archHaar_eq_tsum_unitCone`:
  `w * ∫⁻ y, f y ∂archHaar K = ∑' u : (𝓞 K)ˣ, ∫⁻ y in unitCone D, f (unitScale u y) ∂archHaar K`.
* `summable_setIntegral_norm_unitCone`, `hasSum_setIntegral_unitCone`, and
  `integral_archHaar_eq_tsum_unitCone`: the corresponding absolute summability and Bochner integral
  unfolding for any `archHaar`-integrable function.
* `setLIntegral_unitCone_eq` and `setIntegral_unitCone_eq`: integrals of `unitScale`-invariant
  functions over `unitCone D` do not depend on the choice of unit fundamental domain `D`.
* `hasMellin_mellinKernel_sub`: the radial Mellin substitution identifying the Mellin transform of
  `mellinKernel D L` minus its constant term with the norm-weighted integral of `latticeTheta L - 1`
  over `unitCone D`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.5).
-/

public section
noncomputable section

open MeasureTheory Set NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped ENNReal

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### Unfolding `archHaar` over unit translates of a cone -/

section FreeUnitAction

private local instance : Countable (Multiplicative (Fin (Units.rank K) → ℤ)) :=
  Multiplicative.toAdd.injective.countable

private theorem countable_units : Countable (𝓞 K)ˣ :=
  (unitsMulEquivTorsionProdMultiplicative K).injective.countable

private def freeUnitHom : Multiplicative (Fin (Units.rank K) → ℤ) →* (𝓞 K)ˣ :=
  (unitsMulEquivTorsionProdMultiplicative K).symm.toMonoidHom.comp (MonoidHom.inr _ _)

private theorem freeUnitHom_apply (g : Multiplicative (Fin (Units.rank K) → ℤ)) :
    freeUnitHom (K := K) g = ∏ i, Units.fundSystem K i ^ Multiplicative.toAdd g i := by
  rw [freeUnitHom, MonoidHom.comp_apply, MonoidHom.inr_apply, MulEquiv.coe_toMonoidHom,
    unitsMulEquivTorsionProdMultiplicative_symm_apply, Subgroup.coe_one, one_mul]

private local instance : SMul (Multiplicative (Fin (Units.rank K) → ℤ)) (realSpace K) where
  smul g y := unitScale (freeUnitHom g) y

private theorem freeUnits_smul_def (g : Multiplicative (Fin (Units.rank K) → ℤ))
    (y : realSpace K) : g • y = unitScale (freeUnitHom g) y := (rfl)

private local instance : MulAction (Multiplicative (Fin (Units.rank K) → ℤ)) (realSpace K) where
  one_smul y := by rw [freeUnits_smul_def, map_one, unitScale_one]
  mul_smul g₁ g₂ y := by simp only [freeUnits_smul_def, map_mul, unitScale_unitScale]

private local instance :
    ContinuousConstSMul (Multiplicative (Fin (Units.rank K) → ℤ)) (realSpace K) where
  continuous_const_smul g := continuous_unitScale (freeUnitHom g)

private local instance :
    SMulInvariantMeasure (Multiplicative (Fin (Units.rank K) → ℤ)) (realSpace K) (archHaar K) where
  measure_preimage_smul g _ hs :=
    (measurePreserving_unitScale (freeUnitHom g)).measure_preimage hs.nullMeasurableSet

private theorem unitScale_symm_torsionProd (ζ : Units.torsion K)
    (g : Multiplicative (Fin (Units.rank K) → ℤ)) (y : realSpace K) :
    unitScale ((unitsMulEquivTorsionProdMultiplicative K).symm (ζ, g)) y = g • y := by
  have hpair : (ζ, g) = (ζ, 1) * (1, g) := by simp
  have hmul : (unitsMulEquivTorsionProdMultiplicative K).symm (ζ, g) =
      (ζ : (𝓞 K)ˣ) * freeUnitHom g := by
    rw [hpair, map_mul]
    congr 1
    rw [unitsMulEquivTorsionProdMultiplicative_symm_apply]
    simp
  rw [hmul, ← unitScale_unitScale, unitScale_of_mem_torsion ζ.2, freeUnits_smul_def]

/-- The cone over a unit fundamental domain is a fundamental domain for the free part of `(𝓞 K)ˣ`
with respect to `archHaar K`. -/
private theorem isFundamentalDomain_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) :
    IsFundamentalDomain (Multiplicative (Fin (Units.rank K) → ℤ)) (unitCone D) (archHaar K) := by
  refine IsFundamentalDomain.mk'' (measurableSet_unitCone hD.measurableSet).nullMeasurableSet
    ?_ ?_ fun g ↦ (measurePreserving_smul g (archHaar K)).quasiMeasurePreserving
  · filter_upwards [ae_archHaar_pos] with y hy
    obtain ⟨u, hu⟩ := hD.exists_unitScale_mem (surfacePart y) (surfacePart_mem_normOneSurface hy)
    set p := unitsMulEquivTorsionProdMultiplicative K u
    have hu_eq : u = (unitsMulEquivTorsionProdMultiplicative K).symm (p.1, p.2) := by
      simp [p]
    refine ⟨p.2, mem_unitCone.mpr ⟨fun w ↦ unitScale_pos (hy w) _, ?_⟩⟩
    rw [freeUnits_smul_def, surfacePart_unitScale, ← freeUnits_smul_def,
      ← unitScale_symm_torsionProd p.1 p.2, ← hu_eq]
    exact hu
  · intro g hg
    refine Disjoint.aedisjoint (disjoint_left.mpr ?_)
    rintro _ ⟨y, hy, rfl⟩ hgy
    obtain ⟨-, hsurf⟩ := mem_unitCone.mp hgy
    dsimp only at hsurf
    rw [freeUnits_smul_def, surfacePart_unitScale] at hsurf
    have htor : freeUnitHom g ∈ Units.torsion K :=
      (hD.unitScale_mem_iff (surfacePart y) (mem_unitCone.mp hy).2 (freeUnitHom g)).mp hsurf
    rw [freeUnitHom_apply, Units.prod_fundSystem_zpow_mem_torsion_iff] at htor
    exact hg (Multiplicative.toAdd.injective htor)

/-- **Unit-orbit unfolding of `archHaar` for nonnegative extended-real integrands.** Summing a
cone integral over all units `u : (𝓞 K)ˣ` unfolds to `w = Units.torsionOrder K` copies of the
integral over `realSpace K`. -/
theorem lintegral_archHaar_eq_tsum_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (f : realSpace K → ℝ≥0∞) :
    (Units.torsionOrder K : ℝ≥0∞) * ∫⁻ y, f y ∂archHaar K =
      ∑' u : (𝓞 K)ˣ, ∫⁻ y in unitCone D, f (unitScale u y) ∂archHaar K := by
  have := Fintype.ofFinite (Units.torsion K)
  rw [← (unitsMulEquivTorsionProdMultiplicative K).symm.toEquiv.tsum_eq, tsum_prod']
  simp_rw [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, unitScale_symm_torsionProd]
  rw [← (isFundamentalDomain_unitCone hD).lintegral_eq_tsum'' f, tsum_fintype, Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, ← Units.torsionOrder, nsmul_eq_mul]

/-- As measures on `realSpace K`, the images under `unitScale u` (`u : (𝓞 K)ˣ`) of `archHaar K`
restricted to `unitCone D` sum to `w • archHaar K`. -/
theorem sum_map_unitScale_restrict_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) :
    (Measure.sum fun u : (𝓞 K)ˣ ↦ ((archHaar K).restrict (unitCone D)).map (unitScale u)) =
      (Units.torsionOrder K : ℝ≥0∞) • archHaar K := by
  have := countable_units (K := K)
  ext s hs
  rw [Measure.sum_apply _ hs, _root_.smul_apply, smul_eq_mul,
    ← lintegral_indicator_one hs, lintegral_archHaar_eq_tsum_unitCone hD]
  refine tsum_congr fun u ↦ ?_
  rw [Measure.map_apply (continuous_unitScale u).measurable hs,
    ← lintegral_indicator_one ((continuous_unitScale u).measurable hs)]
  rfl

/-- If `f` is `archHaar`-integrable, the norms of its integrals over the unit translates of
`unitCone D` are summable over `(𝓞 K)ˣ`. -/
theorem summable_setIntegral_norm_unitCone {E : Type*} [NormedAddCommGroup E]
    {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D) {f : realSpace K → E}
    (hf : Integrable f (archHaar K)) :
    Summable fun u : (𝓞 K)ˣ ↦ ∫ y in unitCone D, ‖f (unitScale u y)‖ ∂archHaar K := by
  have := countable_units (K := K)
  let μ : (𝓞 K)ˣ → Measure (realSpace K) :=
    fun u ↦ ((archHaar K).restrict (unitCone D)).map (unitScale u)
  have hfμ : Integrable f (Measure.sum μ) := by
    rw [sum_map_unitScale_restrict_unitCone hD]
    exact hf.smul_measure (ENNReal.natCast_ne_top (Units.torsionOrder K))
  refine hfμ.summable_integral.congr fun u ↦ ?_
  have hfu : Integrable f (μ u) := hfμ.mono_measure (Measure.le_sum _ u)
  exact integral_map (continuous_unitScale u).measurable.aemeasurable hfu.norm.aestronglyMeasurable

/-- **Unit-orbit unfolding of `archHaar` (`HasSum` form).** For any `archHaar`-integrable `f`, the
integrals of `y ↦ f (unitScale u y)` over `unitCone D` sum over `u : (𝓞 K)ˣ` to
`w • ∫ y, f y ∂archHaar K`. -/
theorem hasSum_setIntegral_unitCone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D) {f : realSpace K → E}
    (hf : Integrable f (archHaar K)) :
    HasSum (fun u : (𝓞 K)ˣ ↦ ∫ y in unitCone D, f (unitScale u y) ∂archHaar K)
      (Units.torsionOrder K • ∫ y, f y ∂archHaar K) := by
  let μ : (𝓞 K)ˣ → Measure (realSpace K) :=
    fun u ↦ ((archHaar K).restrict (unitCone D)).map (unitScale u)
  have hfμ : Integrable f (Measure.sum μ) := by
    rw [sum_map_unitScale_restrict_unitCone hD]
    exact hf.smul_measure (ENNReal.natCast_ne_top (Units.torsionOrder K))
  have hsum := hasSum_integral_measure hfμ
  rw [sum_map_unitScale_restrict_unitCone hD, integral_smul_measure, ENNReal.toReal_natCast,
    Nat.cast_smul_eq_nsmul] at hsum
  refine hsum.congr_fun fun u ↦ ?_
  have hfu : Integrable f (μ u) := hfμ.mono_measure (Measure.le_sum _ u)
  exact (integral_map (continuous_unitScale u).measurable.aemeasurable
    hfu.aestronglyMeasurable).symm

/-- **Unit-orbit unfolding of `archHaar` (`tsum` form).** -/
theorem integral_archHaar_eq_tsum_unitCone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D) {f : realSpace K → E}
    (hf : Integrable f (archHaar K)) :
    Units.torsionOrder K • ∫ y, f y ∂archHaar K =
      ∑' u : (𝓞 K)ˣ, ∫ y in unitCone D, f (unitScale u y) ∂archHaar K :=
  (hasSum_setIntegral_unitCone hD hf).tsum_eq.symm

/-- Lebesgue integrals of `unitScale`-invariant functions over `unitCone D` are independent of the
unit fundamental domain `D`. -/
theorem setLIntegral_unitCone_eq {D₁ D₂ : Set (realSpace K)}
    (hD₁ : IsUnitFundamentalDomain K D₁) (hD₂ : IsUnitFundamentalDomain K D₂)
    (f : realSpace K → ℝ≥0∞) (hf : ∀ u : (𝓞 K)ˣ, ∀ y, f (unitScale u y) = f y) :
    ∫⁻ y in unitCone D₁, f y ∂archHaar K = ∫⁻ y in unitCone D₂, f y ∂archHaar K :=
  (isFundamentalDomain_unitCone hD₁).setLIntegral_eq (isFundamentalDomain_unitCone hD₂) f
    fun g y ↦ hf (freeUnitHom g) y

/-- Bochner integrals of `unitScale`-invariant functions over `unitCone D` are independent of the
unit fundamental domain `D`. -/
theorem setIntegral_unitCone_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D₁ D₂ : Set (realSpace K)} (hD₁ : IsUnitFundamentalDomain K D₁)
    (hD₂ : IsUnitFundamentalDomain K D₂) {f : realSpace K → E}
    (hf : ∀ u : (𝓞 K)ˣ, ∀ y, f (unitScale u y) = f y) :
    ∫ y in unitCone D₁, f y ∂archHaar K = ∫ y in unitCone D₂, f y ∂archHaar K :=
  (isFundamentalDomain_unitCone hD₁).setIntegral_eq (isFundamentalDomain_unitCone hD₂)
    fun g y ↦ hf (freeUnitHom g) y

end FreeUnitAction

/-! ### Radial Mellin transform over a cone -/

open scoped Classical in
/-- **The radial Mellin substitution in Hecke's integral.** If the norm-weighted theta series
minus its constant term is absolutely integrable over the cone, then the Mellin transform of
its kernel is that cone integral times `(2^r₂ / w) V_L^s`. The power of the covolume comes from
the substitution `u = V_L² t`, not from a Jacobian factor in `dt / t`. -/
theorem hasMellin_mellinKernel_sub {D : Set (realSpace K)} (hDm : MeasurableSet D)
    (hD : Bornology.IsBounded D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] (s : ℂ)
    (h : IntegrableOn (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * (latticeTheta L y - 1))
      (unitCone D) (archHaar K)) :
    HasMellin (fun u ↦ mellinKernel D L u -
        (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
          (surfaceHaar K).real (Subtype.val ⁻¹' D)) (s / 2)
      ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        (ZLattice.covolume L ^ 2 : ℂ) ^ (s / 2) *
          ∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) * (latticeTheta L y - 1)
            ∂archHaar K) := by
  let F : ℝ → ℂ := fun t ↦ ∫ x in Subtype.val ⁻¹' D,
    (latticeTheta L (surfaceScale (x : realSpace K) t) - 1) ∂surfaceHaar K
  let c : ℂ := (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ)
  have hV : 0 < ZLattice.covolume L := ZLattice.covolume_pos L
  have hF : HasMellin F (s / 2)
      (∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) * (latticeTheta L y - 1) ∂archHaar K) :=
    hasMellin_integral_surfaceScale hDm (s / 2) h
  have hscaled := hF.comp_mul_right (a := (ZLattice.covolume L ^ 2)⁻¹) (by positivity)
  have havg (u : ℝ) (hu : 0 < u) : mellinKernel D L u -
      c * (surfaceHaar K).real (Subtype.val ⁻¹' D) =
        c • F (u * (ZLattice.covolume L ^ 2)⁻¹) := by
    rw [mellinKernel_sub_eq_integral_sub_one hDm hD L hu]
    simp only [F, c, smul_eq_mul, div_eq_mul_inv]
  have hc := (hasMellin_congr (fun u hu ↦ (havg u hu).symm)).mp
    (hasMellin_const_smul hscaled.1 c)
  rw [hscaled.2, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (sq_nonneg _),
    Complex.cpow_neg, inv_inv] at hc
  simpa only [c, smul_eq_mul, Complex.ofReal_pow, mul_assoc] using hc

end TauCeti.LFunctions
