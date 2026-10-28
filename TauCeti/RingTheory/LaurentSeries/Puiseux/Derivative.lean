/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.HahnSeries.EulerDerivation
public import TauCeti.RingTheory.LaurentSeries.Derivative
public import TauCeti.RingTheory.LaurentSeries.Primitive
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Valuation

/-!
# The derivative of Puiseux series

Over a field `K` of characteristic zero, the Puiseux field carries the derivation `D_t` determined
by the coefficient rule `D_t (t ^ q) = q t ^ (q - 1)` for every rational exponent `q`: the
coefficient of `t ^ q` in `D_t x` is `(q + 1)` times the coefficient of `t ^ (q + 1)` in `x`. On
rational Hahn series it is `t⁻¹ θ`, where `θ = t d/dt` is the Euler derivation multiplying the
coefficient of `t ^ q` by `q` (`HahnSeries.eulerDerivation`); `θ` does not enlarge supports, so
`D_t` keeps every Puiseux series at its level.

On the level-`n` copy of `K⸨X⸩`, embedded by `X ↦ u = t ^ (1 / n)`, the derivative with respect
to `t` is computed from the derivative with respect to `u` by the chain rule for `t = u ^ n`:
`D_t (ι_n f) = (1 / n) u ^ (1 - n) ι_n (D_u f)`. At level one this says that `D_t` extends the
derivative of Laurent series. The derivative lowers the order by at most one, and by exactly one
when the order is nonzero, so it is continuous for the valuation topology. Its kernel is `K`, and
its image consists of the Puiseux series with vanishing coefficient of `t⁻¹`: a residue-zero series
at level `n` has a primitive at the same level, obtained from a primitive of a Laurent series.

## Main definitions

* `TauCeti.puiseuxField.derivation K`: the derivation `D_t` of the Puiseux field over `K`.

## Main results

* `TauCeti.puiseuxField.coeff_derivation`: the coefficient rule for `D_t`.
* `TauCeti.puiseuxField.derivation_single`: `D_t (a t ^ q) = q a t ^ (q - 1)`.
* `TauCeti.puiseuxField.derivation_levelEmbedding`: the chain rule
  `D_t (ι_n f) = (1 / n) u ^ (1 - n) ι_n (D_u f)` for the level-`n` embedding.
* `TauCeti.puiseuxField.derivation_algebraMap_laurentSeries`: `D_t` extends the derivative of
  Laurent series.
* `TauCeti.puiseuxField.addVal_derivation`: if `x` has nonzero order `q`, then `D_t x` has order
  `q - 1`.
* `TauCeti.puiseuxField.continuous_derivation`: `D_t` is continuous for the valuation topology.
* `TauCeti.puiseuxField.derivation_eq_zero_iff`: the kernel of `D_t` consists of the constants.
* `TauCeti.puiseuxField.mem_range_derivation_iff`: a Puiseux series is a derivative exactly when
  its coefficient of `t⁻¹` vanishes.
-/

public section

open HahnSeries LaurentSeries Filter Topology
open scoped LaurentSeries

namespace TauCeti.puiseuxField

variable (K : Type*) [Field K]

/-- The constant `c` of the Puiseux field is the Hahn series `c t ^ 0`. -/
private theorem coe_algebraMap (c : K) :
    ((algebraMap K (puiseuxField K) c : puiseuxField K) : HahnSeries ℚ K) =
      HahnSeries.single 0 c := by
  simp [HahnSeries.algebraMap_apply']

/-- The scalar action of `K` on the Puiseux field is multiplication by the monomial `c t ^ 0`. -/
private theorem coe_smul_eq_single_zero_mul (c : K) (x : puiseuxField K) :
    ((c • x : puiseuxField K) : HahnSeries ℚ K) = HahnSeries.single 0 c * (x : HahnSeries ℚ K) := by
  rw [Algebra.smul_def, IntermediateField.coe_mul, coe_algebraMap]

variable [CharZero K]

/-- The derivative `t⁻¹ θ` of rational Hahn series, where `θ` multiplies the coefficient of
`t ^ q` by `q`. -/
private noncomputable def hahnDeriv (x : HahnSeries ℚ K) : HahnSeries ℚ K :=
  HahnSeries.single (-1) 1 * eulerDerivation (Rat.castHom K : ℚ →+ K) x

private theorem coeff_hahnDeriv (x : HahnSeries ℚ K) (q : ℚ) :
    (hahnDeriv K x).coeff q = ((q : K) + 1) * x.coeff (q + 1) := by
  rw [hahnDeriv, coeff_single_mul, one_mul, coeff_eulerDerivation, sub_neg_eq_add]
  simp

private theorem hahnDeriv_mem {x : HahnSeries ℚ K} (hx : x ∈ puiseuxField K) :
    hahnDeriv K x ∈ puiseuxField K := by
  refine mul_mem (single_mem_puiseuxField _ _) ?_
  obtain ⟨n, hn⟩ := mem_puiseuxField_iff_exists_den_dvd.mp hx
  exact mem_puiseuxField_iff_exists_den_dvd.mpr
    ⟨n, fun q hq ↦ hn q (support_eulerDerivation_subset _ _ hq)⟩

/-- The **derivative of Puiseux series** with respect to `t`, as a `K`-derivation of the Puiseux
field: `D_t (t ^ q) = q t ^ (q - 1)` for every rational exponent `q`. -/
noncomputable def derivation : Derivation K (puiseuxField K) (puiseuxField K) where
  toFun x := ⟨hahnDeriv K x, hahnDeriv_mem K x.2⟩
  map_add' x y := Subtype.ext <| by
    simp only [IntermediateField.coe_add, hahnDeriv, map_add, mul_add]
  map_smul' c x := Subtype.ext <| by
    -- The scalar action of `K` on the Puiseux field is multiplication by the constant `c`, which
    -- the Euler derivation kills.
    simp only [hahnDeriv, RingHom.id_apply, coe_smul_eq_single_zero_mul, Derivation.leibniz,
      eulerDerivation_single, map_zero, zero_mul, smul_eq_mul]
    ring
  map_one_eq_zero' := Subtype.ext <| by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, IntermediateField.coe_one, hahnDeriv,
      Derivation.map_one_eq_zero, mul_zero, IntermediateField.coe_zero]
  leibniz' x y := Subtype.ext <| by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, IntermediateField.coe_mul, hahnDeriv,
      Derivation.leibniz, smul_eq_mul, IntermediateField.coe_add]
    ring

variable {K}

/-- **The coefficient rule** for the derivative of Puiseux series: the coefficient of `t ^ q` in
`D_t x` is `q + 1` times the coefficient of `t ^ (q + 1)` in `x`. -/
@[simp]
theorem coeff_derivation (x : puiseuxField K) (q : ℚ) :
    (derivation K x : HahnSeries ℚ K).coeff q =
      ((q : K) + 1) * (x : HahnSeries ℚ K).coeff (q + 1) :=
  coeff_hahnDeriv K x q

/-- The coefficient of `t ^ (q - 1)` in `D_t x` is `q` times the coefficient of `t ^ q` in `x`. -/
theorem coeff_derivation_sub_one (x : puiseuxField K) (q : ℚ) :
    (derivation K x : HahnSeries ℚ K).coeff (q - 1) = q * (x : HahnSeries ℚ K).coeff q := by
  simp

/-- The derivative of the monomial `a t ^ q` is `q a t ^ (q - 1)`. -/
@[simp]
theorem derivation_single (q : ℚ) (a : K) :
    derivation K (single K q a) = single K (q - 1) (q * a) := by
  ext r
  rw [coeff_derivation, coe_single, coe_single, coeff_single, coeff_single]
  split_ifs with h₁ h₂ h₂
  · rw [h₂, ← h₁, add_sub_cancel_right]
    push_cast
    ring
  · exact absurd (by rw [← h₁, add_sub_cancel_right]) h₂
  · exact absurd (by rw [h₂, sub_add_cancel]) h₁
  · rw [mul_zero]

/-- **The chain rule for the level-`n` embedding** `X ↦ u = t ^ (1 / n)`: since `t = u ^ n`,
`D_t (ι_n f) = (1 / n) u ^ (1 - n) ι_n (D_u f)`. In particular `D_t` maps every level to itself. -/
theorem derivation_levelEmbedding (n : ℕ+) (f : K⸨X⸩) :
    derivation K (levelEmbedding K n f) =
      levelEmbedding K n (HahnSeries.single (1 - n : ℤ) ((n : K)⁻¹) * derivative K f) := by
  have hn : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  ext q
  rw [coeff_derivation, coe_levelEmbedding, coe_levelEmbedding]
  by_cases hq : q.den ∣ n
  · obtain ⟨k, rfl⟩ := (Rat.den_dvd_iff_exists_eq_intCast_div n.ne_zero).mp hq
    have hk : (k : ℚ) / n + 1 = ((k + n : ℤ) : ℚ) / n := by
      push_cast
      field_simp
    rw [hk, coeff_ramifiedEmbedding_intCast_div, coeff_ramifiedEmbedding_intCast_div,
      coeff_single_mul, coeff_derivative, zsmul_eq_mul, show k - (1 - n) + 1 = k + n by ring]
    push_cast
    field_simp
  · have hq' : ¬ (q + 1).den ∣ n := by
      rwa [show q + 1 = q + ((1 : ℤ) : ℚ) by simp, Rat.add_intCast_den]
    rw [coeff_ramifiedEmbedding_of_not_den_dvd n f hq',
      coeff_ramifiedEmbedding_of_not_den_dvd n _ hq, mul_zero]

/-- The derivative of Puiseux series extends the derivative of Laurent series along the
`K⸨X⸩`-algebra map `X ↦ t`. -/
@[simp]
theorem derivation_algebraMap_laurentSeries (f : K⸨X⸩) :
    derivation K (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (derivative K f) := by
  rw [algebraMap_laurentSeries_apply, derivation_levelEmbedding, algebraMap_laurentSeries_apply]
  simp

/-- The derivative of Puiseux series maps level `n` to itself. -/
theorem derivation_mem_range_levelEmbedding {n : ℕ+} {x : puiseuxField K}
    (hx : x ∈ (levelEmbedding K n).range) : derivation K x ∈ (levelEmbedding K n).range := by
  obtain ⟨f, rfl⟩ := (AlgHom.mem_range _).mp hx
  exact ⟨_, (derivation_levelEmbedding n f).symm⟩

/-! ### Order and continuity -/

/-- The derivative lowers the order by at most one: if `x` has order at least `q + 1`, then
`D_t x` has order at least `q`. -/
theorem le_addVal_derivation {q : ℚ} {x : puiseuxField K}
    (hx : ((q + 1 : ℚ) : WithTop ℚ) ≤ addVal K x) :
    (q : WithTop ℚ) ≤ addVal K (derivation K x) := by
  rw [addVal_apply, le_orderTop_iff_forall] at hx ⊢
  intro r hr
  rw [coeff_derivation, hx (r + 1)
    (by exact_mod_cast (add_lt_add_iff_right 1).mpr (WithTop.coe_lt_coe.mp hr)), mul_zero]

/-- If `x` has nonzero order `q`, then `D_t x` has order exactly `q - 1`, with leading coefficient
`q` times that of `x`. -/
theorem addVal_derivation {q : ℚ} (hq : q ≠ 0) {x : puiseuxField K} (hx : addVal K x = q) :
    addVal K (derivation K x) = ((q - 1 : ℚ) : WithTop ℚ) := by
  refine le_antisymm ?_ (le_addVal_derivation (by rw [sub_add_cancel, hx]))
  rw [addVal_apply] at hx ⊢
  refine orderTop_le_of_coeff_ne_zero ?_
  rw [coeff_derivation_sub_one]
  exact mul_ne_zero (Rat.cast_ne_zero.mpr hq) (coeff_orderTop_ne hx)

/-- The derivative of Puiseux series is continuous for the valuation topology. -/
theorem continuous_derivation : Continuous (derivation K) := by
  refine continuous_of_continuousAt_zero (derivation K) ?_
  rw [ContinuousAt, map_zero, hasBasis_nhds_zero.tendsto_right_iff]
  intro q _
  filter_upwards [hasBasis_nhds_zero.mem_of_mem (i := q + 1) trivial] with x hx
  exact le_addVal_derivation hx

/-! ### Kernel and image -/

/-- In characteristic zero, the kernel of the derivative of Puiseux series consists of the
constants. -/
theorem derivation_eq_zero_iff {x : puiseuxField K} :
    derivation K x = 0 ↔ ∃ c : K, algebraMap K (puiseuxField K) c = x := by
  refine ⟨fun h ↦ ⟨(x : HahnSeries ℚ K).coeff 0, Subtype.ext ?_⟩, ?_⟩
  · ext r
    rw [coe_algebraMap, coeff_single]
    split_ifs with hr
    · rw [hr]
    · have := coeff_derivation_sub_one x r
      rw [h, IntermediateField.coe_zero, coeff_zero] at this
      exact ((mul_eq_zero.mp this.symm).resolve_left (Rat.cast_ne_zero.mpr hr)).symm
  · rintro ⟨c, rfl⟩
    exact Derivation.map_algebraMap _ c

/-- **The residue-zero primitive criterion**: a Puiseux series is the derivative of a Puiseux
series exactly when its coefficient of `t⁻¹` vanishes. A residue-zero series at level `n` has a
primitive at level `n`. -/
theorem mem_range_derivation_iff (x : puiseuxField K) :
    x ∈ LinearMap.range (derivation K : puiseuxField K →ₗ[K] puiseuxField K) ↔
      (x : HahnSeries ℚ K).coeff (-1) = 0 := by
  simp only [LinearMap.mem_range, Derivation.coeFn_coe]
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨y, rfl⟩
    simp
  obtain ⟨n, hxn⟩ := exists_mem_range_levelEmbedding x
  obtain ⟨f, rfl⟩ := (AlgHom.mem_range _).mp hxn
  have hn : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  -- The level-`n` coefficient of `t⁻¹` is the coefficient of `X ^ (-n)` in `f`.
  have hf : f.coeff (-n) = 0 := by
    rwa [coe_levelEmbedding, show (-1 : ℚ) = ((-n : ℤ) : ℚ) / n by push_cast; field_simp,
      coeff_ramifiedEmbedding_intCast_div] at hx
  -- Integrate `n X ^ (n - 1) f`, whose residue is `n` times the coefficient of `X ^ (-n)` in `f`.
  obtain ⟨g, hg⟩ :=
    (mem_range_laurentSeries_derivative_iff K (HahnSeries.single (n - 1 : ℤ) (n : K) * f)).mpr
    (by rw [coeff_single_mul, show -1 - (n - 1 : ℤ) = -n by ring, hf, mul_zero])
  refine ⟨levelEmbedding K n g, ?_⟩
  rw [derivation_levelEmbedding, hg, ← mul_assoc, single_mul_single, inv_mul_cancel₀ hn,
    show (1 - n : ℤ) + (n - 1) = 0 by ring, ← C_apply, C_one, one_mul]

end TauCeti.puiseuxField
