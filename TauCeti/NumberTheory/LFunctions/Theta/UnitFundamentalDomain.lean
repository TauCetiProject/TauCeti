/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne

/-!
# The unit action on the archimedean parameters

Hecke's proof of the functional equation of a partial zeta function integrates a theta series
with one positive parameter `y_w` per infinite place `w` of a number field `K`. Those parameters
are the points of Mathlib's `NumberField.mixedEmbedding.realSpace K` with positive coordinates.
A unit `u` acts on them by `y_w ↦ |u|_w² y_w`: this is the substitution that carries the Gaussian
`exp (-π ∑_w y_w |(u • x)_w|²)` back to the point `x`, and it is the only place where the unit
group enters the theta series of an ideal lattice. Integrating over a fundamental domain for this
action on the norm-one hypersurface cuts the sum over lattice points down to a sum over ideals.

This file sets up that action and its fundamental domains:

* `archNorm y = ∏_w y_w ^ mult w` is the norm of a parameter, so that a complex place counts
  twice. It is the determinant of the quadratic form `x ↦ ∑_w y_w |x_w|²` on the mixed space.
* `unitScale u y` is the action `y_w ↦ |u|_w² y_w` of a unit. It preserves the norm
  (`archNorm_unitScale`), and its kernel on parameters with nonzero coordinates is the torsion
  (`unitScale_eq_self_iff`).
* `normOneSurface K` is the hypersurface `S = {y > 0 | N(y) = 1}` on which the units act.
* `IsUnitFundamentalDomain K D` says that `D` is a bounded measurable subset of `S` meeting every
  unit orbit, and meeting the orbit of each of its points exactly in the torsion translates.
* `unitFundamentalDomain K` is the set of points of `S` whose coordinatewise square root lies in
  Mathlib's `NumberField.mixedEmbedding.fundamentalCone K`. It is a unit fundamental domain
  (`isUnitFundamentalDomain_unitFundamentalDomain`), bounded because Mathlib's
  `NumberField.mixedEmbedding.fundamentalCone.isBounded_normLeOne` is.
* Inversion and translation by a point of `S` carry unit fundamental domains to unit fundamental
  domains (`IsUnitFundamentalDomain.inv`, `IsUnitFundamentalDomain.mul`).

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

public section

open Bornology Finset NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.Units
open scoped Pointwise

namespace TauCeti.LFunctions

variable {K : Type*} [Field K]

/-! ### The action of the units -/

/-- The action `y_w ↦ |u|_w² y_w` of a unit `u` on the archimedean parameters, Neukirch's
`|ε|² y`. It is the square of the action `x ↦ u • x` on the mixed space read on absolute values
(`unitScale_sq_normAtPlace`), squared because a Gaussian is quadratic in `x`. -/
noncomputable def unitScale (u : (𝓞 K)ˣ) (y : realSpace K) : realSpace K :=
  fun w ↦ w (u : K) ^ 2 * y w

@[simp]
theorem unitScale_apply (u : (𝓞 K)ˣ) (y : realSpace K) (w : InfinitePlace K) :
    unitScale u y w = w (u : K) ^ 2 * y w := (rfl)

@[simp]
theorem unitScale_one (y : realSpace K) : unitScale 1 y = y := by
  ext w
  simp

theorem unitScale_unitScale (u v : (𝓞 K)ˣ) (y : realSpace K) :
    unitScale u (unitScale v y) = unitScale (u * v) y := by
  ext w
  simp only [unitScale_apply, Units.val_mul, map_mul]
  ring

/-- The unit action commutes with the coordinatewise multiplication of parameters. -/
theorem unitScale_mul (u : (𝓞 K)ˣ) (c y : realSpace K) :
    unitScale u (c * y) = c * unitScale u y := by
  ext w
  simp only [unitScale_apply, Pi.mul_apply]
  ring

/-- The unit action on inverted parameters is the action of the inverse unit, inverted. -/
theorem unitScale_inv (u : (𝓞 K)ˣ) (y : realSpace K) :
    unitScale u y⁻¹ = (unitScale u⁻¹ y)⁻¹ := by
  ext w
  have hu : w ((u⁻¹ : (𝓞 K)ˣ) : K) = (w (u : K))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, map_one]
  rw [Pi.inv_apply, unitScale_apply, unitScale_apply, Pi.inv_apply, hu, mul_inv, inv_pow, inv_inv]

/-- On absolute values, the unit action on parameters is the square of the action of `u` on the
mixed space. -/
theorem unitScale_sq_normAtPlace (u : (𝓞 K)ˣ) (x : mixedSpace K) :
    unitScale u (fun w ↦ normAtPlace w x ^ 2) = fun w ↦ normAtPlace w (u • x) ^ 2 := by
  ext w
  rw [unitScale_apply, unitSMul_smul, map_mul, normAtPlace_apply, mul_pow]

theorem unitScale_pos {y : realSpace K} {w : InfinitePlace K} (hy : 0 < y w) (u : (𝓞 K)ˣ) :
    0 < unitScale u y w :=
  mul_pos (pow_pos (pos_iff.mpr (by simp)) 2) hy

variable [NumberField K]

/-! ### The norm of a parameter -/

/-- The norm `N(y) = ∏_w y_w ^ mult w` of an archimedean parameter, a complex place counting
twice. For a positive parameter it is the determinant of the quadratic form
`x ↦ ∑_w y_w |x_w|²` on the mixed space, a complex coordinate being two real ones. -/
noncomputable def archNorm : realSpace K →*₀ ℝ where
  toFun y := ∏ w, y w ^ mult w
  map_zero' := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
    exact prod_eq_zero (mem_univ w) (zero_pow mult_ne_zero)
  map_one' := by simp
  map_mul' y z := by simp [mul_pow, prod_mul_distrib]

theorem archNorm_apply (y : realSpace K) : archNorm y = ∏ w, y w ^ mult w := (rfl)

/-- The norm of the coordinatewise absolute values of a point of the mixed space is Mathlib's
`mixedEmbedding.norm` of that point. -/
@[simp]
theorem archNorm_normAtAllPlaces (x : mixedSpace K) :
    archNorm (normAtAllPlaces x) = mixedEmbedding.norm x := (rfl)

theorem archNorm_pos {y : realSpace K} (hy : ∀ w, 0 < y w) : 0 < archNorm y :=
  prod_pos fun w _ ↦ pow_pos (hy w) _

theorem archNorm_inv (y : realSpace K) : archNorm y⁻¹ = (archNorm y)⁻¹ := by
  simp [archNorm_apply, inv_pow, prod_inv_distrib]

@[fun_prop]
theorem continuous_archNorm : Continuous (archNorm : realSpace K → ℝ) :=
  (continuous_finsetProd univ fun w _ ↦ (continuous_apply w).pow (mult w)).congr
    fun y ↦ (archNorm_apply y).symm

/-- A unit has norm `±1`, so its action preserves the norm of a parameter. -/
@[simp]
theorem archNorm_unitScale (u : (𝓞 K)ˣ) (y : realSpace K) :
    archNorm (unitScale u y) = archNorm y := by
  have hu : ∏ w : InfinitePlace K, (w (u : K) ^ 2) ^ mult w = 1 := by
    simp_rw [← pow_mul, mul_comm 2, pow_mul, prod_pow, prod_eq_abs_norm, Units.norm, Rat.cast_one,
      one_pow]
  simp only [archNorm_apply, unitScale_apply, mul_pow, prod_mul_distrib, hu, one_mul]

/-- The kernel of the unit action on parameters with nonzero coordinates, positive ones in
particular, is the torsion: a unit fixes such a parameter exactly when all its absolute values
are `1`. -/
theorem unitScale_eq_self_iff {y : realSpace K} (hy : ∀ w, y w ≠ 0) (u : (𝓞 K)ˣ) :
    unitScale u y = y ↔ u ∈ torsion K := by
  rw [mem_torsion, funext_iff]
  refine forall_congr' fun w ↦ ?_
  rw [unitScale_apply, mul_eq_right₀ (hy w),
    pow_eq_one_iff_of_nonneg (apply_nonneg _ _) two_ne_zero]

/-! ### The norm-one hypersurface -/

variable (K) in
/-- The norm-one hypersurface `S = {y | ∀ w, 0 < y w, N(y) = 1}` of the positive archimedean
parameters, on which the unit group acts through `unitScale` (`unitScale_mem_normOneSurface`). -/
def normOneSurface : Set (realSpace K) :=
  {y | (∀ w, 0 < y w) ∧ archNorm y = 1}

theorem mem_normOneSurface {y : realSpace K} :
    y ∈ normOneSurface K ↔ (∀ w, 0 < y w) ∧ archNorm y = 1 := Iff.rfl

variable (K) in
theorem measurableSet_normOneSurface : MeasurableSet (normOneSurface K) := by
  have hpos : MeasurableSet {y : realSpace K | ∀ w, 0 < y w} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun w ↦ measurableSet_lt measurable_const (measurable_pi_apply w)
  exact hpos.inter (measurableSet_eq_fun (continuous_archNorm (K := K)).measurable
    measurable_const)

@[simp]
theorem unitScale_mem_normOneSurface {y : realSpace K} (u : (𝓞 K)ˣ) :
    unitScale u y ∈ normOneSurface K ↔ y ∈ normOneSurface K := by
  simp only [mem_normOneSurface, archNorm_unitScale, unitScale_apply]
  exact and_congr_left fun _ ↦ forall_congr' fun w ↦
    mul_pos_iff_of_pos_left (pow_pos (pos_iff.mpr (by simp)) 2)

theorem inv_mem_normOneSurface {y : realSpace K} (hy : y ∈ normOneSurface K) :
    y⁻¹ ∈ normOneSurface K :=
  ⟨fun w ↦ inv_pos.mpr (hy.1 w), by rw [archNorm_inv, hy.2, inv_one]⟩

theorem mul_mem_normOneSurface {y z : realSpace K} (hy : y ∈ normOneSurface K)
    (hz : z ∈ normOneSurface K) : y * z ∈ normOneSurface K :=
  ⟨fun w ↦ mul_pos (hy.1 w) (hz.1 w), by rw [map_mul, hy.2, hz.2, one_mul]⟩

/-- A point of the norm-one hypersurface with coordinates at most `C` has inverse coordinates at
most `C ^ [K : ℚ]`: the other coordinates cannot make up for a small one. -/
theorem inv_le_pow_finrank_of_mem_normOneSurface {y : realSpace K} (hy : y ∈ normOneSurface K)
    {C : ℝ} (hC : 1 ≤ C) (hyC : ∀ w, y w ≤ C) (w : InfinitePlace K) :
    (y w)⁻¹ ≤ C ^ Module.finrank ℚ K := by
  classical
  have h1 : 1 ≤ C ^ Module.finrank ℚ K := one_le_pow₀ hC
  have hmul := mul_prod_erase univ (fun v ↦ y v ^ mult v) (mem_univ w)
  rw [← archNorm_apply, hy.2] at hmul
  have hpow : (y w)⁻¹ ^ mult w ≤ C ^ Module.finrank ℚ K := by
    rw [inv_pow, inv_eq_of_mul_eq_one_right hmul, ← sum_mult_eq, ← prod_pow_eq_pow_sum]
    calc ∏ v ∈ univ.erase w, y v ^ mult v
        ≤ ∏ v ∈ univ.erase w, C ^ mult v :=
          prod_le_prod₀ (fun v _ ↦ pow_nonneg (hy.1 v).le _)
            fun v _ ↦ pow_le_pow_left₀ (hy.1 v).le (hyC v) _
      _ ≤ C ^ mult w * ∏ v ∈ univ.erase w, C ^ mult v :=
          le_mul_of_one_le_left (prod_nonneg fun v _ ↦ by positivity) (one_le_pow₀ hC)
      _ = ∏ v, C ^ mult v := mul_prod_erase univ (fun v ↦ C ^ mult v) (mem_univ w)
  rcases le_or_gt (y w)⁻¹ 1 with h | h
  · exact h.trans h1
  · exact (le_self_pow₀ h.le mult_ne_zero).trans hpow

/-! ### Unit fundamental domains -/

variable (K) in
/-- A fundamental domain for the unit action on the norm-one hypersurface: a bounded measurable
subset `D` of `S` meeting every orbit of `unitScale`, such that a unit carries a point of `D`
back into `D` exactly when it is a root of unity. Boundedness, which Neukirch's fundamental domain
has, gives `D` compact closure in the open positive orthant. -/
structure IsUnitFundamentalDomain (D : Set (realSpace K)) : Prop where
  subset : D ⊆ normOneSurface K
  measurableSet : MeasurableSet D
  isBounded : IsBounded D
  exists_unitScale_mem : ∀ y ∈ normOneSurface K, ∃ u : (𝓞 K)ˣ, unitScale u y ∈ D
  unitScale_mem_iff : ∀ y ∈ D, ∀ u : (𝓞 K)ˣ, unitScale u y ∈ D ↔ u ∈ torsion K

variable (K) in
/-- The unit fundamental domain taken from Mathlib: the points of `S` whose coordinatewise square
root, read as a point of the mixed space, lies in `NumberField.mixedEmbedding.fundamentalCone K`.
Since the cone depends only on the absolute values of the coordinates and `unitScale u` is
`x ↦ u • x` read on `|x|²`, it is a fundamental domain for the unit action
(`isUnitFundamentalDomain_unitFundamentalDomain`). -/
def unitFundamentalDomain : Set (realSpace K) :=
  {y ∈ normOneSurface K | mixedSpaceOfRealSpace (fun w ↦ √(y w)) ∈ fundamentalCone K}

theorem mem_unitFundamentalDomain {y : realSpace K} :
    y ∈ unitFundamentalDomain K ↔
      y ∈ normOneSurface K ∧ mixedSpaceOfRealSpace (fun w ↦ √(y w)) ∈ fundamentalCone K :=
  Iff.rfl

omit [NumberField K] in
/-- The square root of `unitScale u y` is the square root of `y` moved by `u` in the mixed
space, up to the coordinatewise absolute values that the fundamental cone ignores. -/
private theorem normAtPlace_sqrt_unitScale (u : (𝓞 K)ˣ) (y : realSpace K) (w : InfinitePlace K) :
    normAtPlace w (mixedSpaceOfRealSpace (fun v ↦ √(unitScale u y v))) =
      normAtPlace w (u • mixedSpaceOfRealSpace (fun v ↦ √(y v))) := by
  rw [normAtPlace_mixedSpaceOfRealSpace (Real.sqrt_nonneg _), unitScale_apply, unitSMul_smul,
    map_mul, normAtPlace_apply, normAtPlace_mixedSpaceOfRealSpace (Real.sqrt_nonneg _),
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (apply_nonneg _ _)]

private theorem unitScale_mem_fundamentalCone_iff (u : (𝓞 K)ˣ) (y : realSpace K) :
    mixedSpaceOfRealSpace (fun v ↦ √(unitScale u y v)) ∈ fundamentalCone K ↔
      u • mixedSpaceOfRealSpace (fun v ↦ √(y v)) ∈ fundamentalCone K :=
  ⟨fun h ↦ fundamentalCone.mem_of_normAtPlace_eq h fun w ↦ (normAtPlace_sqrt_unitScale u y w).symm,
    fun h ↦ fundamentalCone.mem_of_normAtPlace_eq h (normAtPlace_sqrt_unitScale u y)⟩

/-- The square root of a point of `S`, read in the mixed space, has norm `1`. -/
private theorem norm_sqrt_of_mem_normOneSurface {y : realSpace K} (hy : y ∈ normOneSurface K) :
    mixedEmbedding.norm (mixedSpaceOfRealSpace (fun v ↦ √(y v))) = 1 := by
  have hsq : archNorm (fun v ↦ √(y v)) ^ 2 = 1 := by
    rw [← map_pow, ← hy.2]
    congr 1
    ext v
    exact Real.sq_sqrt (hy.1 v).le
  rw [← archNorm_normAtAllPlaces, normAtAllPlaces_mixedSpaceOfRealSpace fun _ ↦ Real.sqrt_nonneg _]
  exact (pow_eq_one_iff_of_nonneg (archNorm_pos fun v ↦ Real.sqrt_pos.mpr (hy.1 v)).le
    two_ne_zero).mp hsq

private theorem measurableSet_unitFundamentalDomain :
    MeasurableSet (unitFundamentalDomain K) :=
  (measurableSet_normOneSurface K).inter <| measurableSet_fundamentalCone K |>.preimage <|
    mixedSpaceOfRealSpace.continuous.measurable.comp <|
      Measurable.of_eval fun w ↦ (measurable_pi_apply w).sqrt

private theorem isBounded_unitFundamentalDomain : IsBounded (unitFundamentalDomain K) := by
  classical
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (fundamentalCone.isBounded_normLeOne K)
  refine isBounded_iff_forall_norm_le.mpr ⟨C ^ 2, fun y hy ↦ ?_⟩
  have hx := hC _
    (fundamentalCone.mem_normLeOne.mpr ⟨hy.2, (norm_sqrt_of_mem_normOneSurface hy.1).le⟩)
  refine (pi_norm_le_iff_of_nonneg (sq_nonneg C)).mpr fun w ↦ ?_
  have hw : normAtPlace w (mixedSpaceOfRealSpace (fun v ↦ √(y v))) ≤ C := by
    refine le_trans ?_ hx
    rw [norm_eq_sup'_normAtPlace]
    exact le_sup' (fun v ↦ normAtPlace v _) (mem_univ w)
  rw [normAtPlace_mixedSpaceOfRealSpace (Real.sqrt_nonneg _)] at hw
  rw [Real.norm_of_nonneg (hy.1.1 w).le, ← Real.sq_sqrt (hy.1.1 w).le]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hw 2

/-- **Mathlib's fundamental cone gives a unit fundamental domain.** -/
theorem isUnitFundamentalDomain_unitFundamentalDomain :
    IsUnitFundamentalDomain K (unitFundamentalDomain K) where
  subset _ hy := hy.1
  measurableSet := measurableSet_unitFundamentalDomain
  isBounded := isBounded_unitFundamentalDomain
  exists_unitScale_mem y hy := by
    obtain ⟨u, hu⟩ := fundamentalCone.exists_unit_smul_mem
      (by rw [norm_sqrt_of_mem_normOneSurface hy]; exact one_ne_zero)
    exact ⟨u, (unitScale_mem_normOneSurface u).mpr hy,
      (unitScale_mem_fundamentalCone_iff u y).mpr hu⟩
  unitScale_mem_iff y hy u := by
    rw [← fundamentalCone.unit_smul_mem_iff_mem_torsion hy.2 u,
      ← unitScale_mem_fundamentalCone_iff]
    exact and_iff_right ((unitScale_mem_normOneSurface u).mpr hy.1)

namespace IsUnitFundamentalDomain

variable {D : Set (realSpace K)}

/-- Inversion of `S` carries unit fundamental domains to unit fundamental domains. -/
theorem inv (hD : IsUnitFundamentalDomain K D) : IsUnitFundamentalDomain K D⁻¹ where
  subset y hy := by simpa using inv_mem_normOneSurface (hD.subset hy)
  measurableSet := hD.measurableSet.preimage <|
    Measurable.of_eval fun w ↦ (measurable_pi_apply w).inv
  isBounded := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hD.isBounded
    set C' := max C 1
    refine isBounded_iff_forall_norm_le.mpr ⟨C' ^ Module.finrank ℚ K, fun y hy ↦ ?_⟩
    have hy' : y⁻¹ ∈ normOneSurface K := hD.subset hy
    have hpos : ∀ w, 0 < y w := fun w ↦ inv_pos.mp (hy'.1 w)
    refine (pi_norm_le_iff_of_nonneg (pow_nonneg (by positivity) _)).mpr fun w ↦ ?_
    rw [Real.norm_of_nonneg (hpos w).le, ← inv_inv (y w)]
    refine inv_le_pow_finrank_of_mem_normOneSurface hy' (le_max_right _ _) (fun v ↦ ?_) w
    exact (Real.le_norm_self _).trans ((norm_le_pi_norm y⁻¹ v).trans
      ((hC _ hy).trans (le_max_left _ _)))
  exists_unitScale_mem y hy := by
    obtain ⟨u, hu⟩ := hD.exists_unitScale_mem _ (inv_mem_normOneSurface hy)
    refine ⟨u⁻¹, ?_⟩
    rwa [Set.mem_inv, ← inv_inv u, ← unitScale_inv, inv_inv]
  unitScale_mem_iff y hy u := by
    have h := hD.unitScale_mem_iff _ (Set.mem_inv.mp hy) u⁻¹
    rw [Set.mem_inv]
    rwa [inv_mem_iff, ← inv_inv (unitScale u⁻¹ y⁻¹), ← unitScale_inv, inv_inv] at h

/-- Translation by a point `c` of `S` carries unit fundamental domains to unit fundamental
domains. -/
theorem mul (hD : IsUnitFundamentalDomain K D) {c : realSpace K} (hc : c ∈ normOneSurface K) :
    IsUnitFundamentalDomain K ((c * ·) '' D) := by
  have hcc : c * c⁻¹ = 1 := funext fun w ↦ mul_inv_cancel₀ (hc.1 w).ne'
  have himage : (c * ·) '' D = (c⁻¹ * ·) ⁻¹' D :=
    congrFun (Set.image_eq_preimage_of_inverse (f := (c * ·)) (g := (c⁻¹ * ·))
      (fun y ↦ by simp only [← mul_assoc, mul_comm c⁻¹ c, hcc, one_mul])
      (fun y ↦ by simp only [← mul_assoc, hcc, one_mul])) D
  have hmem : ∀ y, y ∈ (c * ·) '' D ↔ c⁻¹ * y ∈ D := fun y ↦ by rw [himage]; rfl
  refine
    { subset := fun y hy ↦ ?_
      measurableSet := ?_
      isBounded := ?_
      exists_unitScale_mem := fun y hy ↦ ?_
      unitScale_mem_iff := fun y hy u ↦ ?_ }
  · obtain ⟨z, hz, rfl⟩ := hy
    exact mul_mem_normOneSurface hc (hD.subset hz)
  · rw [himage]
    exact hD.measurableSet.preimage (measurable_const.mul measurable_id)
  · obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hD.isBounded
    refine isBounded_iff_forall_norm_le.mpr ⟨‖c‖ * C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact (norm_mul_le c z).trans (mul_le_mul_of_nonneg_left (hC z hz) (norm_nonneg c))
  · obtain ⟨u, hu⟩ := hD.exists_unitScale_mem _
      (mul_mem_normOneSurface (inv_mem_normOneSurface hc) hy)
    exact ⟨u, (hmem _).mpr (by rwa [unitScale_mul] at hu)⟩
  · rw [hmem, ← unitScale_mul]
    exact hD.unitScale_mem_iff _ ((hmem y).mp hy) u

end IsUnitFundamentalDomain

end TauCeti.LFunctions
