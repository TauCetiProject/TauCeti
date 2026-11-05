/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import TauCeti.NumberTheory.LFunctions.Theta.Surface.Haar
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.ExpMapBasis
public import TauCeti.NumberTheory.NumberField.Units.Dirichlet

/-!
# The volume of a unit fundamental domain

Let `K` be a number field with `r₁` real and `r₂` complex places, `r = r₁ + r₂`, regulator `R`
and degree `n = [K : ℚ]`. This file proves Neukirch's (5.6): every fundamental domain `D` for the
action `y ↦ |u|² y` of the units on the norm-one hypersurface `S` of the archimedean parameters
has volume

`d*x (D) = 2^(r - 1) R / 2^r₂`

for the measure `surfaceHaar K` (`surfaceHaar_of_isUnitFundamentalDomain`). Neukirch's value
`2^(r - 1) R` is for his canonical measure, which is `2^r₂` times `surfaceHaar K`. The `2^(r - 1)`
is the index of the lattice `2 log |𝓞ˣ|` of the action by squares in the logarithmic unit
lattice. Up to the factor `2^r₂ / w`, `w` the number of roots of unity, this volume is the
constant term of the Mellin kernel of a partial zeta function, which gives its residue at `s = 1`.

The computation takes place in the coordinates of Mathlib's
`NumberField.mixedEmbedding.fundamentalCone.expMapBasis`, which parametrizes the positive orthant
by `z ↦ e^(z_{w₀}) ∏_i |η_i|^(z_i)` for a fundamental system of units `η_i`:

* the norm of `expMapBasis z` is `e^(n z_{w₀})` (`archNorm_expMapBasis`) and its surface part is
  `expMapBasis` of `z` with the `w₀`-coordinate replaced by `0` (`surfacePart_expMapBasis`);
* `dy / y` is `2^(-r₂) R n` times Lebesgue measure (`archHaar_image_expMapBasis`), by Mathlib's
  change of variables `setLIntegral_expMapBasis_image`;
* the unit `∏_i η_i ^ c_i` acts by the translation by `2 c` (`unitScale_expMapBasis`).

So a unit fundamental domain becomes, in these coordinates and after thickening it by the
interval `[0, 1/n]` in the `w₀`-direction, a fundamental domain for the translations by the
lattice `(2ℤ)^(r - 1)`, and all such domains have the same Lebesgue measure
(`MeasureTheory.IsAddFundamentalDomain.measure_set_eq`). For the domain
`unitFundamentalDomain K` cut out by Mathlib's fundamental cone, the thickened domain is the box
`[0, 1/n] × [0, 2)^(r - 1)`, of measure `2^(r - 1) / n`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.6).
* The coordinates are those through which Mathlib computes the volume of
  `NumberField.mixedEmbedding.fundamentalCone.normLeOne K`: `expMapBasis` and its change of
  variables `setLIntegral_expMapBasis_image` (X. Roblot).
-/

public section
noncomputable section

open MeasureTheory Measure Set NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped ENNReal

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### The archimedean parameters in the coordinates of `expMapBasis` -/

/-- The norm of `expMapBasis z` is `e^(n z_{w₀})`, `n = [K : ℚ]`. -/
@[simp]
theorem archNorm_expMapBasis (z : realSpace K) :
    archNorm (expMapBasis z) = Real.exp (z w₀) ^ Module.finrank ℚ K := by
  rw [archNorm_apply]
  exact prod_expMapBasis_pow z

open scoped Classical in
/-- The surface part of `expMapBasis z` forgets the `w₀`-coordinate of `z`. -/
@[simp]
theorem surfacePart_expMapBasis (z : realSpace K) :
    surfacePart (expMapBasis z) = expMapBasis fun w ↦ if w = w₀ then 0 else z w := by
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hN : archNorm (expMapBasis z) ^ (1 / (Module.finrank ℚ K : ℝ)) = Real.exp (z w₀) := by
    rw [archNorm_expMapBasis, ← Real.rpow_natCast, ← Real.rpow_mul (Real.exp_nonneg _),
      mul_one_div_cancel hn, Real.rpow_one]
  ext w
  rw [surfacePart_apply _ (archNorm_pos (expMapBasis_pos z)).le, hN, expMapBasis_apply'' z,
    Pi.smul_apply, smul_eq_mul, mul_div_cancel_left₀ _ (Real.exp_ne_zero _)]

open scoped Classical in
/-- In the coordinates of `expMapBasis`, the unit `∏_i η_i ^ c_i` acts on the archimedean
parameters by the translation by `2 c`. -/
theorem unitScale_expMapBasis (c : {w : InfinitePlace K // w ≠ w₀} → ℤ) (z : realSpace K) :
    unitScale (∏ i, fundSystem K (equivFinRank.symm i) ^ c i) (expMapBasis z) =
      expMapBasis (2 • intCoord c + z) := by
  ext w
  rw [unitScale_apply, two_smul, expMapBasis_add, expMapBasis_add, expMapBasis_intCoord]
  simp only [Pi.mul_apply, sq]

open scoped Classical in
/-- The density of `dy / y` against `dy` at `y = expMapBasis z`, multiplied by the Jacobian of
`expMapBasis` at `z` without its constant factor, is `1`. -/
private theorem expMapBasis_jacobian_mul_density (z : realSpace K) :
    ENNReal.ofReal (Real.exp (z w₀ * Module.finrank ℚ K)) *
        (∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (expMapBasis z w.1))⁻¹ *
      ENNReal.ofReal (∏ w, (expMapBasis z w)⁻¹) = 1 := by
  have he : ∀ w, 0 < expMapBasis z w := expMapBasis_pos z
  have hprod : Real.exp (z w₀ * Module.finrank ℚ K) * ∏ w, (expMapBasis z w)⁻¹ =
      ∏ w : {w : InfinitePlace K // IsComplex w}, expMapBasis z w.1 := by
    rw [mul_comm, Real.exp_mul, Real.rpow_natCast, ← prod_expMapBasis_pow,
      ← Finset.prod_mul_distrib, prod_eq_prod_mul_prod]
    simp_rw [mult_isReal, mult_isComplex, pow_one, pow_two, ← mul_assoc,
      inv_mul_cancel₀ (he _).ne', one_mul, Finset.prod_const_one, one_mul]
  rw [← ENNReal.ofReal_prod_of_nonneg fun w _ ↦ (he w.1).le, mul_right_comm,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), hprod, ENNReal.mul_inv_cancel
      (ENNReal.ofReal_pos.mpr (Finset.prod_pos fun w _ ↦ he w.1)).ne' ENNReal.ofReal_ne_top]

/-- **`dy / y` in the coordinates of `expMapBasis`**: it is Lebesgue measure times
`2^(-r₂) R [K : ℚ]`, where `R` is the regulator. -/
theorem archHaar_image_expMapBasis {s : Set (realSpace K)} (hs : MeasurableSet s) :
    archHaar K (expMapBasis '' s) =
      2⁻¹ ^ nrComplexPlaces K * ENNReal.ofReal (regulator K) * Module.finrank ℚ K * volume s := by
  have himage : MeasurableSet (expMapBasis '' s) :=
    hs.image_of_continuousOn_injOn (continuous_expMapBasis K).continuousOn
      (injective_expMapBasis K).injOn
  have hpos : expMapBasis '' s ⊆ {y : realSpace K | ∀ w, 0 < y w} := by
    rintro _ ⟨z, -, rfl⟩
    exact expMapBasis_pos z
  rw [archHaar_eq_withDensity, withDensity_apply _ himage, Measure.restrict_restrict himage,
    inter_eq_left.mpr hpos, setLIntegral_expMapBasis_image hs (by fun_prop), ← setLIntegral_one]
  congr 1
  exact setLIntegral_congr_fun hs fun z _ ↦ expMapBasis_jacobian_mul_density z

/-! ### Thickened fundamental domains -/

variable (K) in
open scoped Classical in
/-- The slab `0 ≤ z_{w₀} ≤ 1/n` of coordinates of parameters with norm in `[1, e]`. -/
private def normSlab : Set (realSpace K) :=
  {z | z w₀ ∈ Icc 0 (Module.finrank ℚ K : ℝ)⁻¹}

open scoped Classical in
/-- The coordinates whose point, with its `w₀`-coordinate replaced by `0`, lies in `A`. -/
private def coordCylinder (A : Set (realSpace K)) : Set (realSpace K) :=
  (fun z ↦ expMapBasis fun w ↦ if w = w₀ then 0 else z w) ⁻¹' A

private theorem measurableSet_normSlab : MeasurableSet (normSlab K) :=
  measurableSet_Icc.preimage (measurable_pi_apply w₀)

private theorem measurableSet_coordCylinder {A : Set (realSpace K)} (hA : MeasurableSet A) :
    MeasurableSet (coordCylinder A) := by
  classical
  refine hA.preimage ((continuous_expMapBasis K).measurable.comp ?_)
  exact Measurable.of_eval fun w ↦ by
    split_ifs
    · exact measurable_const
    · exact measurable_pi_apply w

private theorem expMapBasis_preimage_shell (A : Set (realSpace K)) :
    expMapBasis ⁻¹' (surfacePart ⁻¹' A ∩ archNorm ⁻¹' Icc 1 (Real.exp 1)) =
      normSlab K ∩ coordCylinder A := by
  have hn : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.mpr Module.finrank_pos
  ext z
  simp only [mem_preimage, mem_inter_iff, surfacePart_expMapBasis, archNorm_expMapBasis, mem_Icc,
    normSlab, coordCylinder, mem_ofPred_eq]
  rw [← Real.exp_nat_mul, Real.one_le_exp_iff, Real.exp_le_exp, mul_comm, ← le_div_iff₀ hn,
    mul_nonneg_iff_of_pos_right hn, one_div, and_comm]

/-- The parameters with surface part in a subset of `S` and norm in `[1, e]` are positive, so they
are values of `expMapBasis`. -/
private theorem shell_subset_range {A : Set (realSpace K)} (hA : A ⊆ normOneSurface K) :
    surfacePart ⁻¹' A ∩ archNorm ⁻¹' Icc 1 (Real.exp 1) ⊆ range expMapBasis := by
  rintro y ⟨hy, h1, -⟩
  have hpos : ∀ w, 0 < y w := fun w ↦ by
    have := (mem_normOneSurface.mp (hA hy)).1 w
    rw [surfacePart_apply y (zero_le_one.trans h1)] at this
    exact (div_pos_iff_of_pos_right (Real.rpow_pos_of_pos (one_pos.trans_le h1) _)).mp this
  exact ⟨_, expMapBasis.right_inv (mem_univ_pi.mpr hpos)⟩

/-- The `d*x`-mass of a measurable `A ⊆ S` is `2^(-r₂) R n` times the Lebesgue measure of its
thickened coordinate cylinder. -/
private theorem surfaceHaar_preimage_eq_volume {A : Set (realSpace K)}
    (hA : A ⊆ normOneSurface K) (hAm : MeasurableSet A) :
    surfaceHaar K (Subtype.val ⁻¹' A) =
      2⁻¹ ^ nrComplexPlaces K * ENNReal.ofReal (regulator K) * Module.finrank ℚ K *
        volume (normSlab K ∩ coordCylinder A) := by
  rw [surfaceHaar_apply (measurable_subtype_coe hAm), Subtype.image_preimage_coe,
    inter_eq_right.mpr hA, ← image_preimage_eq_of_subset (shell_subset_range hA),
    expMapBasis_preimage_shell, archHaar_image_expMapBasis
      (measurableSet_normSlab.inter (measurableSet_coordCylinder hAm))]

open scoped Classical in
/-- A point `expMapBasis z` with `z_{w₀} = 0` lies in `unitFundamentalDomain K` exactly when its
other coordinates `z_w` lie in `[0, 2)`: membership in Mathlib's fundamental cone reads `z / 2`
in the box `[0, 1)`, as the domain is defined through square roots. -/
private theorem expMapBasis_mem_unitFundamentalDomain_iff {z : realSpace K} (hz : z w₀ = 0) :
    expMapBasis z ∈ unitFundamentalDomain K ↔ ∀ w, w ≠ w₀ → z w ∈ Ico 0 2 := by
  have hS : expMapBasis z ∈ normOneSurface K := mem_normOneSurface.mpr
    ⟨expMapBasis_pos z, by rw [archNorm_expMapBasis, hz, Real.exp_zero, one_pow]⟩
  have hsqrt : (fun w ↦ √(expMapBasis z w)) = expMapBasis ((2⁻¹ : ℝ) • z) := by
    ext w
    rw [expMapBasis_smul, Pi.pow_apply, Real.sqrt_eq_rpow, one_div]
  rw [mem_unitFundamentalDomain, hsqrt, fundamentalCone, mem_sdiff, mem_preimage,
    logMap_expMapBasis]
  simp only [hS, norm_expMapBasis_ne_zero, mem_ofPred_eq, not_false_eq_true, and_true, true_and,
    Pi.smul_apply, smul_eq_mul, mem_Ico]
  refine forall₂_congr fun w _ ↦ ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

open scoped Classical in
/-- The thickened coordinate cylinder of `unitFundamentalDomain K` is the box
`[0, 1/n] × [0, 2)^(r - 1)`. -/
private theorem normSlab_inter_coordCylinder_unitFundamentalDomain :
    normSlab K ∩ coordCylinder (unitFundamentalDomain K) =
      univ.pi fun w ↦ if w = w₀ then Icc 0 (Module.finrank ℚ K : ℝ)⁻¹ else Ico 0 2 := by
  ext z
  simp only [normSlab, coordCylinder, mem_inter_iff, mem_ofPred_eq, mem_preimage,
    expMapBasis_mem_unitFundamentalDomain_iff (z := fun w ↦ if w = w₀ then 0 else z w) (by simp),
    mem_univ_pi]
  constructor
  · rintro ⟨h0, h⟩ w
    split_ifs with hw
    · exact hw ▸ h0
    · simpa [hw] using h w hw
  · intro h
    exact ⟨by simpa using h w₀, fun w hw ↦ by simpa [hw] using h w⟩

private theorem volume_normSlab_inter_coordCylinder_unitFundamentalDomain :
    volume (normSlab K ∩ coordCylinder (unitFundamentalDomain K)) =
      (Module.finrank ℚ K : ℝ≥0∞)⁻¹ * 2 ^ (nrRealPlaces K + nrComplexPlaces K - 1) := by
  classical
  have hn : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.mpr Module.finrank_pos
  rw [normSlab_inter_coordCylinder_unitFundamentalDomain, volume_pi_pi,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ w₀), ite_eq_left rfl,
    Finset.prod_congr rfl fun w hw ↦ by rw [ite_eq_right (Finset.ne_of_mem_erase hw)],
    Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    card_eq_nrRealPlaces_add_nrComplexPlaces, Real.volume_Icc, Real.volume_Ico, sub_zero, sub_zero,
    ENNReal.ofReal_ofNat, ENNReal.ofReal_inv_of_pos hn, ENNReal.ofReal_natCast]

/-- The translations of the coordinates of `expMapBasis` by the lattice `2 c`, `c` integral with
`c_{w₀} = 0`, through which the units act on the archimedean parameters
(`unitScale_expMapBasis`). -/
private abbrev unitTranslations : AddSubgroup (realSpace K) :=
  (2 • intCoord (K := K)).range

/-- The translation by `2 c`, `c` integral with `c_{w₀} = 0`. -/
private def unitTranslation (c : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    unitTranslations (K := K) :=
  ⟨_, AddMonoidHom.mem_range.mpr ⟨c, rfl⟩⟩

open scoped Classical in
/-- **A unit fundamental domain gives a fundamental domain for the unit translations** of the
coordinates of `expMapBasis`: the units act on the point with its `w₀`-coordinate replaced by
`0` by the translations of `unitTranslations` (`unitScale_expMapBasis`), the roots of unity
acting trivially. -/
private theorem isAddFundamentalDomain_coordCylinder {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) :
    IsAddFundamentalDomain (unitTranslations (K := K)) (coordCylinder D) := by
  refine .mk' (measurableSet_coordCylinder hD.measurableSet).nullMeasurableSet fun z ↦ ?_
  set p : realSpace K := fun w ↦ if w = w₀ then 0 else z w
  set y := expMapBasis p
  have hy : y ∈ normOneSurface K := mem_normOneSurface.mpr
    ⟨expMapBasis_pos p, by simp [y, p, archNorm_expMapBasis]⟩
  -- translating by a lattice point is acting by the corresponding unit
  have htrans (c : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
      unitTranslation c +ᵥ z ∈ coordCylinder D ↔
        unitScale (∏ i, fundSystem K (equivFinRank.symm i) ^ c i) y ∈ D := by
    rw [unitScale_expMapBasis, coordCylinder, mem_preimage, AddSubgroup.vadd_def, vadd_eq_add,
      unitTranslation]
    congr! 2
    ext w
    by_cases hw : w = w₀ <;> simp [p, hw]
  obtain ⟨u, hu⟩ := hD.exists_unitScale_mem y hy
  obtain ⟨⟨ζ, e⟩, rfl, -⟩ := exist_unique_eq_mul_prod K u
  set c₀ : {w : InfinitePlace K // w ≠ w₀} → ℤ := fun i ↦ e (equivFinRank.symm i)
  have hc₀ : unitScale (∏ i, fundSystem K (equivFinRank.symm i) ^ c₀ i) y ∈ D := by
    rw [mul_comm, ← unitScale_unitScale,
      (unitScale_eq_self_iff (fun w ↦ ((mem_normOneSurface.mp hy).1 w).ne') _).mpr ζ.2] at hu
    convert hu using 2
    exact Fintype.prod_equiv equivFinRank.symm _ _ fun _ ↦ rfl
  refine ⟨unitTranslation c₀, (htrans c₀).mpr hc₀, ?_⟩
  rintro ⟨_, c, rfl⟩ hc
  have hc' := (htrans c).mp hc
  rw [← inv_mul_cancel_right (∏ i, fundSystem K (equivFinRank.symm i) ^ c i)
    (∏ i, fundSystem K (equivFinRank.symm i) ^ c₀ i), ← unitScale_unitScale,
    hD.unitScale_mem_iff _ hc₀, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib] at hc'
  simp_rw [← zpow_neg, ← zpow_add, ← sub_eq_add_neg] at hc'
  have h0 : (fun j ↦ c (equivFinRank j) - c₀ (equivFinRank j)) = 0 := by
    refine prod_fundSystem_zpow_mem_torsion_iff.mp ?_
    convert hc' using 1
    exact (Fintype.prod_equiv equivFinRank.symm _ _ fun _ ↦ by simp).symm
  have hcc : c = c₀ := funext fun i ↦ by
    simpa [sub_eq_zero] using congrFun h0 (equivFinRank.symm i)
  subst hcc
  rfl

/-! ### The volume -/

/-- **The volume of a unit fundamental domain** (Neukirch VII (5.6)): every fundamental domain `D`
for the action of the units on the norm-one hypersurface has `d*x`-mass `2^(r - 1) R / 2^r₂`,
where `r = r₁ + r₂` is the number of infinite places and `R` the regulator. Neukirch's value
`2^(r - 1) R` is for his canonical measure, which is `2^r₂` times `surfaceHaar K`. -/
theorem surfaceHaar_of_isUnitFundamentalDomain {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) :
    surfaceHaar K (Subtype.val ⁻¹' D) =
      ENNReal.ofReal (2 ^ (nrRealPlaces K + nrComplexPlaces K - 1) * regulator K /
        2 ^ nrComplexPlaces K) := by
  have : Countable (unitTranslations (K := K)) :=
    (2 • intCoord (K := K)).rangeRestrict_surjective.countable
  have hslab (g : unitTranslations (K := K)) : (g +ᵥ ·) ⁻¹' normSlab K = normSlab K := by
    obtain ⟨_, c, rfl⟩ := g
    ext z
    simp [normSlab, AddSubgroup.vadd_def]
  have hn : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.mpr Module.finrank_pos
  rw [surfaceHaar_preimage_eq_volume hD.subset hD.measurableSet,
    (isAddFundamentalDomain_coordCylinder hD).measure_set_eq
      (isAddFundamentalDomain_coordCylinder isUnitFundamentalDomain_unitFundamentalDomain)
      measurableSet_normSlab hslab,
    volume_normSlab_inter_coordCylinder_unitFundamentalDomain,
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat,
    div_eq_mul_inv, ← ENNReal.inv_pow, mul_assoc _ (Module.finrank ℚ K : ℝ≥0∞), ← mul_assoc _ _⁻¹,
    ENNReal.mul_inv_cancel (by simpa using hn.ne') (ENNReal.natCast_ne_top _), one_mul]
  ring

end TauCeti.LFunctions
