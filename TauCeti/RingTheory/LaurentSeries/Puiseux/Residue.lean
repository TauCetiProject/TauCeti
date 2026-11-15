/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.HahnSeries.Primitive
public import TauCeti.RingTheory.LaurentSeries.Primitive
public import TauCeti.RingTheory.LaurentSeries.Puiseux.ContinuousDerivation

/-!
# Residues and primitives of Puiseux series

The residue of a Puiseux form `x dt` is the coefficient of `t ^ (-1)` in `x`, a rational-exponent
coefficient: `TauCeti.puiseuxField.residue K`. It is `K`-linear and, through the level-one
embedding, extends the residue of Laurent series.

On the level `K⸨t ^ (1 / n)⸩`, written in the variable `u = t ^ (1 / n)`, the form `dt` is
`d(u ^ n) = n u ^ (n - 1) du`, so the residue in `u` of a form is `n` times its residue in `t`:
`Res_u (f dt) = n Res_t (f dt)`. More generally, for `x = f (t ^ (1 / n))` and
`y = g (t ^ (1 / n))`, the residue in `u` of `f dg` is `n` times the residue in `t` of `x dy`.

In characteristic zero, termwise integration restricts to a `K`-linear operator
`TauCeti.puiseuxField.primitive K` on the Puiseux field. A Puiseux series is a derivative `dy/dt`
exactly when its residue vanishes, and then `y` is its primitive up to a constant; the form
`t⁻¹ dt` is not exact. On level `n` integration in `t` is integration in `u` of `n u ^ (n - 1) f`,
the substitution `t = u ^ n`.

The residue of the logarithmic derivative `x⁻¹ dx` is the rational order of `x`. Together with
the primitive criterion and the chain rule this gives the finite-map formula: for a continuous
`K`-algebra endomorphism `ρ` of the Puiseux field, with `e` the rational order of `ρ t`,
`Res (ρ (x) d(ρ t)) = e Res (x dt)`. Writing `x = a t⁻¹ + dy/dt`, the exact part stays exact and
`a t⁻¹ dt` becomes `a (ρ t)⁻¹ d(ρ t)`. In particular a change of parameter `t ↦ ρ t` of order one
preserves residues, as for Laurent series.

## Main definitions

* `TauCeti.puiseuxField.residue K`: the residue of Puiseux forms, the coefficient of `t ^ (-1)`.
* `TauCeti.puiseuxField.primitive K`: termwise integration of Puiseux series.

## Main results

* `TauCeti.puiseuxField.residue_algebraMap_laurentSeries`: the residue extends that of `K⸨X⸩`.
* `TauCeti.puiseuxField.coeff_neg_one_mul_derivative_single_eq_nsmul_residue`:
  `Res_u (f dt) = n Res_t (f dt)` on level `n`, in every characteristic.
* `TauCeti.puiseuxField.coeff_neg_one_mul_derivative_eq_nsmul_residue`: the residue in `u` of
  `f dg` is `n` times the residue in `t` of the corresponding Puiseux form.
* `TauCeti.puiseuxField.range_derivation`: the derivatives are exactly the residue-zero Puiseux
  series.
* `TauCeti.puiseuxField.derivation_eq_iff_eq_primitive_add_algebraMap`: primitives are unique up
  to a constant.
* `TauCeti.puiseuxField.residue_derivation_mul_inv`: the residue of `x⁻¹ dx` is the order of `x`.
* `TauCeti.puiseuxField.residue_map_mul_derivation_eq_mul` and
  `TauCeti.puiseuxField.residue_map_mul_derivation`: the residue of `ρ (x) d(ρ t)` is the order of
  `ρ t` times the residue of `x dt`, and equals it when `ρ t` has order one.
* `TauCeti.puiseuxField.primitive_levelEmbedding`: integration on level `n` by substitution;
  on level one, `TauCeti.puiseuxField.primitive_algebraMap_laurentSeries`, it extends termwise
  integration of `K⸨X⸩`.
-/

public section

open HahnSeries LaurentSeries
open scoped LaurentSeries

namespace TauCeti

namespace puiseuxField

section Residue

variable {K : Type*} [Field K]

variable (K) in
/-- The **residue** of the Puiseux form `x dt`: the coefficient of `t ^ (-1)` in `x`. -/
noncomputable def residue : puiseuxField K →ₗ[K] K where
  toFun x := (x : HahnSeries ℚ K).coeff (-1)
  map_add' x y := by
    rw [IntermediateField.coe_add, coeff_add]
  map_smul' c x := by
    -- The scalar action of `K` is multiplication by the image of `K`, which acts coefficientwise.
    simp [Algebra.smul_def, algebraMap_apply']

/-- The residue of `x dt` is the coefficient of `t ^ (-1)` in `x`. -/
theorem residue_apply (x : puiseuxField K) : residue K x = (x : HahnSeries ℚ K).coeff (-1) :=
  (rfl)

/-- The residue of `a t⁻¹ dt` is `a`. -/
@[simp]
theorem residue_single_neg_one (a : K) : residue K (single K (-1) a) = a := by
  rw [residue_apply, coe_single, coeff_single_same]

/-- The residue of `a t ^ q dt` vanishes for `q ≠ -1`. -/
theorem residue_single_of_ne {q : ℚ} (hq : q ≠ -1) (a : K) : residue K (single K q a) = 0 := by
  rw [residue_apply, coe_single, coeff_single_of_ne hq.symm]

/-- The residue of a series on level `n`, with `u = t ^ (1 / n)`, is its coefficient of
`u ^ (-n)`. -/
@[simp]
theorem residue_levelEmbedding (n : ℕ+) (f : K⸨X⸩) :
    residue K (levelEmbedding K n f) = f.coeff (-n) := by
  rw [residue_apply, coe_levelEmbedding, ← coeff_ramifiedEmbedding_intCast_div n f (-n)]
  congr 1
  push_cast
  rw [neg_div, div_self (by exact_mod_cast n.ne_zero)]

/-- The residue of Puiseux forms extends the residue of Laurent series: on level one it is the
coefficient of `X⁻¹`. -/
@[simp]
theorem residue_algebraMap_laurentSeries (f : K⸨X⸩) :
    residue K (algebraMap K⸨X⸩ (puiseuxField K) f) = f.coeff (-1) := by
  rw [algebraMap_laurentSeries_apply, residue_levelEmbedding, PNat.one_coe, Nat.cast_one]

/-- **Residues on a ramified level**: on level `n`, with `u = t ^ (1 / n)` and `t = u ^ n`, the
form `dt` is `d(u ^ n)`, and the residue in `u` of `f dt` is `n` times its residue in `t`:
`Res_u (f dt) = n Res_t (f dt)`. -/
theorem coeff_neg_one_mul_derivative_single_eq_nsmul_residue (n : ℕ+) (f : K⸨X⸩) :
    (f * derivative K (HahnSeries.single (n : ℤ) (1 : K))).coeff (-1) =
      (n : ℕ) • residue K (levelEmbedding K n f) := by
  rw [derivative_apply, hasseDeriv_single, Ring.choose_one_right, coeff_mul_single,
    residue_levelEmbedding, Nat.cast_one, show (-1 : ℤ) - (n - 1) = -n by ring, nsmul_eq_mul,
    zsmul_eq_mul, mul_one, Int.cast_natCast, mul_comm]

end Residue

end puiseuxField

variable {K : Type*} [Field K] [CharZero K]

/-- The primitive of a Puiseux series is a Puiseux series. -/
theorem ratHahnSeriesPrimitive_mem_puiseuxField {x : HahnSeries ℚ K} (hx : x ∈ puiseuxField K) :
    ratHahnSeriesPrimitive K x ∈ puiseuxField K := by
  obtain ⟨n, hn⟩ := mem_puiseuxField_iff_exists_den_dvd.mp hx
  refine mem_puiseuxField_iff_exists_den_dvd.mpr ⟨n, fun q hq ↦ ?_⟩
  obtain ⟨p, hp, rfl⟩ := support_ratHahnSeriesPrimitive_subset x hq
  rw [← Int.cast_one, Rat.add_intCast_den]
  exact hn p hp

namespace puiseuxField

/-- **Residues of forms on a ramified level**: for `x = f (t ^ (1 / n))` and `y = g (t ^ (1 / n))`,
the residue in `u = t ^ (1 / n)` of `f dg` is `n` times the residue in `t` of `x dy`. -/
theorem coeff_neg_one_mul_derivative_eq_nsmul_residue (n : ℕ+) (f g : K⸨X⸩) :
    (f * derivative K g).coeff (-1) =
      (n : ℕ) • residue K (levelEmbedding K n f * derivation K (levelEmbedding K n g)) := by
  rw [derivation_levelEmbedding, ← map_mul, residue_levelEmbedding, mul_left_comm, mul_comm,
    coeff_single_mul, show -(n : ℤ) - (1 - n) = -1 by ring, nsmul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (by exact_mod_cast n.ne_zero), one_mul]

/-- The residue of a derivative is zero: exact forms have no residue. -/
@[simp]
theorem residue_derivation (x : puiseuxField K) : residue K (derivation K x) = 0 := by
  rw [residue_apply, coe_derivation, coeff_ratHahnSeriesDerivation, neg_add_cancel, zero_smul]

variable (K) in
/-- **Termwise integration of Puiseux series**, `t ^ q ↦ t ^ (q + 1) / (q + 1)`, discarding the
residue term `t⁻¹`: the restriction of `TauCeti.ratHahnSeriesPrimitive K`. -/
noncomputable def primitive : puiseuxField K →ₗ[K] puiseuxField K where
  toFun x := ⟨ratHahnSeriesPrimitive K x, ratHahnSeriesPrimitive_mem_puiseuxField x.2⟩
  map_add' x y := Subtype.ext ((ratHahnSeriesPrimitive K).map_add x y)
  map_smul' c x := Subtype.ext <| by
    -- The scalar action of `K` on the Puiseux field is multiplication by the image of `K`, which
    -- agrees with the coefficientwise action for which `ratHahnSeriesPrimitive K` is linear.
    simp [Algebra.smul_def, algebraMap_apply']

/-- As a Hahn series, the primitive of a Puiseux series is its termwise integral. -/
@[simp]
theorem coe_primitive (x : puiseuxField K) :
    (primitive K x : HahnSeries ℚ K) = ratHahnSeriesPrimitive K x :=
  (rfl)

/-- Integration of a monomial: `a t ^ q` integrates to `(q + 1)⁻¹ a t ^ (q + 1)`, which is zero for
`q = -1`. -/
@[simp]
theorem primitive_single (q : ℚ) (a : K) :
    primitive K (single K q a) = single K (q + 1) ((q + 1)⁻¹ • a) :=
  Subtype.ext <| by rw [coe_primitive, coe_single, coe_single, ratHahnSeriesPrimitive_single]

/-- Differentiating the primitive removes exactly the residue term. -/
theorem derivation_primitive (x : puiseuxField K) :
    derivation K (primitive K x) = x - single K (-1) (residue K x) :=
  Subtype.ext <| by
    rw [coe_derivation, coe_primitive, ratHahnSeriesDerivation_ratHahnSeriesPrimitive,
      AddSubgroupClass.coe_sub, coe_single, residue_apply]

/-- Integrating a derivative removes exactly the constant term. -/
theorem primitive_derivation (x : puiseuxField K) :
    primitive K (derivation K x) = x - single K 0 ((x : HahnSeries ℚ K).coeff 0) :=
  Subtype.ext <| by
    rw [coe_primitive, coe_derivation, ratHahnSeriesPrimitive_ratHahnSeriesDerivation,
      AddSubgroupClass.coe_sub, coe_single]

/-- A residue-zero Puiseux series is the derivative of its primitive. -/
theorem derivation_primitive_of_residue_eq_zero {x : puiseuxField K} (hx : residue K x = 0) :
    derivation K (primitive K x) = x := by
  rw [derivation_primitive, hx, single_eq_zero_iff.mpr rfl, sub_zero]

/-- **Primitive criterion**: a Puiseux series is a derivative `dy/dt` exactly when its residue
vanishes. -/
theorem mem_range_derivation_iff {x : puiseuxField K} :
    x ∈ LinearMap.range (derivation K : puiseuxField K →ₗ[K] puiseuxField K) ↔ residue K x = 0 :=
  ⟨fun ⟨y, hy⟩ ↦ hy ▸ residue_derivation y,
    fun hx ↦ ⟨primitive K x, derivation_primitive_of_residue_eq_zero hx⟩⟩

/-- The exact Puiseux forms are the kernel of the residue. -/
theorem range_derivation :
    LinearMap.range (derivation K : puiseuxField K →ₗ[K] puiseuxField K) =
      LinearMap.ker (residue K) := by
  ext x
  rw [mem_range_derivation_iff, LinearMap.mem_ker]

/-- The form `t⁻¹ dt` is not exact. -/
theorem single_neg_one_notMem_range_derivation {a : K} (ha : a ≠ 0) :
    single K (-1) a ∉ LinearMap.range (derivation K : puiseuxField K →ₗ[K] puiseuxField K) := by
  rwa [mem_range_derivation_iff, residue_single_neg_one]

/-- The primitives of a residue-zero Puiseux series are its normalized primitive plus a
constant. -/
theorem derivation_eq_iff_eq_primitive_add_algebraMap {x y : puiseuxField K}
    (hx : residue K x = 0) :
    derivation K y = x ↔ ∃ c : K, y = primitive K x + algebraMap K (puiseuxField K) c := by
  refine ⟨fun h ↦ ⟨(y : HahnSeries ℚ K).coeff 0, ?_⟩, ?_⟩
  · rw [← h, primitive_derivation, sub_add_eq_add_sub, eq_sub_iff_add_eq, add_right_inj]
    exact Subtype.ext <| by simp [algebraMap_apply']
  · rintro ⟨c, rfl⟩
    rw [map_add, derivation_primitive_of_residue_eq_zero hx, Derivation.map_algebraMap, add_zero]

/-- **Integration by substitution on a ramified level**: with `u = t ^ (1 / n)` and `t = u ^ n`,
integration in `t` on level `n` is integration in `u` of `n u ^ (n - 1) f`. -/
theorem primitive_levelEmbedding (n : ℕ+) (f : K⸨X⸩) :
    primitive K (levelEmbedding K n f) =
      levelEmbedding K n
        (laurentSeriesPrimitive K (HahnSeries.single ((n : ℤ) - 1) (n : K) * f)) := by
  refine Subtype.ext ?_
  rw [coe_primitive, coe_levelEmbedding, coe_levelEmbedding]
  ext q
  by_cases hq : q.den ∣ n
  · obtain ⟨k, rfl⟩ := (Rat.den_dvd_iff_exists_eq_intCast_div n.ne_zero).mp hq
    have hn : (n : ℚ) ≠ 0 := by exact_mod_cast n.ne_zero
    have hk : (k : ℚ) / n - 1 = ((k - n : ℤ) : ℚ) / n := by
      push_cast
      field_simp
    rw [coeff_ratHahnSeriesPrimitive, hk, coeff_ramifiedEmbedding_intCast_div,
      coeff_ramifiedEmbedding_intCast_div, coeff_laurentSeriesPrimitive, coeff_single_mul,
      show k - 1 - ((n : ℤ) - 1) = k - n by ring, Rat.smul_def, inv_div]
    push_cast
    ring
  · rw [coeff_ramifiedEmbedding_of_not_den_dvd n _ hq, coeff_ratHahnSeriesPrimitive,
      coeff_ramifiedEmbedding_of_not_den_dvd n f (by rwa [← Int.cast_one, Rat.sub_intCast_den]),
      smul_zero]

/-- Termwise integration of Puiseux series extends that of `K⸨X⸩`. -/
@[simp]
theorem primitive_algebraMap_laurentSeries (f : K⸨X⸩) :
    primitive K (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (laurentSeriesPrimitive K f) := by
  rw [algebraMap_laurentSeries_apply, algebraMap_laurentSeries_apply, primitive_levelEmbedding]
  simp

/-- **The residue of a logarithmic derivative is the order.** The residue of `x⁻¹ dx` is the
rational order of the Puiseux series `x`. -/
theorem residue_derivation_mul_inv (x : puiseuxField K) :
    residue K (derivation K x * x⁻¹) = ((x : HahnSeries ℚ K).order : K) := by
  -- On level `n`, with `u = t ^ (1 / n)`, `x⁻¹ dx/dt` is `(1 / n) u ^ (1 - n) f⁻¹ df/du`.
  obtain ⟨n, hn⟩ := exists_mem_range_levelEmbedding x
  obtain ⟨f, rfl⟩ := (AlgHom.mem_range _).mp hn
  rw [derivation_levelEmbedding, ← map_inv₀, ← map_mul, residue_levelEmbedding,
    coe_levelEmbedding, order_ramifiedEmbedding]
  simp [-derivative_apply, mul_assoc, coeff_single_mul, show -(n : ℤ) - (1 - n) = -1 by ring,
    LaurentSeries.coeff_neg_one_derivative_mul_inv, div_eq_inv_mul]

/-- **The residue under a continuous endomorphism.** Let `ρ` be a continuous `K`-algebra
endomorphism of the Puiseux field, and let `e` be the rational order of `ρ t`. Then the residue of
`ρ (x) d(ρ t)` is `e` times the residue of `x dt`. -/
theorem residue_map_mul_derivation_eq_mul (ρ : puiseuxField K →ₐ[K] puiseuxField K)
    (hρ : Continuous ρ) (x : puiseuxField K) :
    residue K (ρ x * derivation K (ρ (single K 1 1))) =
      ((ρ (single K 1 1) : HahnSeries ℚ K).order : K) * residue K x := by
  set a := residue K x
  set s := ρ (single K 1 1)
  -- Split `x = a t⁻¹ + dy/dt` with `a` the residue of `x`.
  have hx : x = algebraMap K (puiseuxField K) a * (single K 1 1)⁻¹ +
      derivation K (primitive K x) := by
    rw [derivation_primitive, inv_single, inv_one, algebraMap_mul_single, mul_one, add_sub_cancel]
  -- By the chain rule the exact part `dy/dt` becomes the exact form `d(ρ y)`, of residue zero.
  have hexact : residue K (ρ (derivation K (primitive K x)) * derivation K s) = 0 := by
    rw [← derivation_algHom_apply ρ hρ, residue_derivation]
  -- The part `a t⁻¹` becomes `a (ρ t)⁻¹ d(ρ t)`, whose residue is `a` times the order of `ρ t`.
  have hlog : residue K (ρ (algebraMap K _ a * (single K 1 1)⁻¹) * derivation K s) =
      a * ((s : HahnSeries ℚ K).order : K) := by
    rw [map_mul ρ, map_inv₀ ρ, AlgHom.commutes, mul_assoc, ← Algebra.smul_def, map_smul,
      mul_comm _ (derivation K s), residue_derivation_mul_inv, smul_eq_mul]
  rw [hx, map_add, add_mul, map_add, hlog, hexact, add_zero, mul_comm]

/-- **Residues are invariant under a change of parameter of order one.** If a continuous
`K`-algebra endomorphism `ρ` of the Puiseux field sends `t` to a series of order one, then the
residue of `ρ (x) d(ρ t)` is the residue of `x dt`. -/
theorem residue_map_mul_derivation (ρ : puiseuxField K →ₐ[K] puiseuxField K) (hρ : Continuous ρ)
    (h : (ρ (single K 1 1) : HahnSeries ℚ K).order = 1) (x : puiseuxField K) :
    residue K (ρ x * derivation K (ρ (single K 1 1))) = residue K x := by
  rw [residue_map_mul_derivation_eq_mul ρ hρ, h, Rat.cast_one, one_mul]

end puiseuxField

end TauCeti
