/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.Algebra.Group.Units.Basic
public import TauCeti.NumberTheory.LocalField.FractionalIdeal
public import TauCeti.NumberTheory.LocalField.NatCastValuation
public import TauCeti.RingTheory.Valuation.ValuativeRel.Basic

import TauCeti.NumberTheory.LocalField.Squares

/-!
# The quadratic defect

Let `K` be a nonarchimedean local field with ring of integers `𝒪[K]`. The quadratic defect of
`a : Kˣ` is O'Meara's fractional ideal

`𝔡(a) = ⋂_{ξ ∈ K} (a - ξ²) 𝒪[K]`,

which measures how well `a` can be approximated by squares of `K`. Its exponent is
`δ(a) = sup_{ξ ∈ K} v_K(a - ξ²) ∈ ℤ ∪ {⊤}` for the normalized valuation `v_K`.

`FractionalIdeal` is a lattice without infima of infinite families, so the defect is defined as
the greatest lower bound of the principal fractional ideals `(a - ξ²) 𝒪[K]`, and
`TauCeti.isGLB_quadraticDefect` records that property. The infimum is attained: the approximation
orders `v_K(a - ξ²)` of a nonsquare are bounded, because a sequence of better and better
approximations would have a common point in the compact closed ball of radius
`max 1 (valuation K a)`, giving a square root of `a`.
Consequently the defect of a nonsquare is the principal fractional ideal `𝓂[K] ^ δ(a)`, while the
defect of a square is `0` and its exponent is `⊤`.

The results here are the calculus of the defect used to compute Hilbert symbols over `K`: the
defect vanishes exactly on squares, it scales by `c²` when `a` is multiplied by `c²`, the defect of
an integral element is integral, and the defect of an element of odd valuation `v_K(a)` is
`a 𝒪[K]`. None of that needs a hypothesis on the residue characteristic.

The classification below additionally assumes `(2 : K) ≠ 0`. For `e = v_K(2)` and a unit `u`,
`𝔡(u)` runs through the list `0`, `4 𝒪[K] = 𝓂[K]^{2e}`, and `𝓂[K]^{2k+1}` for `0 ≤ k < e`, with
the value `0` occurring exactly when `u` is a square. If `u` is not a square, `δ(u)` is `2e` or an
odd number below `2e`. The upper bound is the sharp local square theorem, and the parity is an
approximation argument: below depth `2e` the cross term `2 ξ π^k s` is negligible, so an
approximation of even order can always be improved using that the residue field is perfect of
characteristic two. Every listed value is
attained: sharpness supplies the value `2e`, and `1 + π^(2k+1)` has defect exponent `2k+1`.

## Main definitions

* `TauCeti.quadraticDefect`: the quadratic defect `𝔡(a)`, a fractional ideal of `𝒪[K]`.
* `TauCeti.defectExponent`: its exponent `δ(a) : WithTop ℤ`.

## Main results

* `TauCeti.isGLB_quadraticDefect`: `𝔡(a)` is the greatest lower bound of the ideals
  `(a - ξ²) 𝒪[K]`, and `TauCeti.exists_quadraticDefect_eq_spanSingleton`: it is one of them.
* `TauCeti.quadraticDefect_eq_zero_iff` and `TauCeti.defectExponent_eq_top_iff`: the defect
  detects squares.
* `TauCeti.quadraticDefect_eq_maximalIdeal_zpow`: `𝔡(a) = 𝓂[K] ^ δ(a)` for a nonsquare `a`.
* `TauCeti.quadraticDefect_mul_sq` and `TauCeti.defectExponent_mul_sq`: behaviour under
  multiplication by a square.
* `TauCeti.quadraticDefect_of_odd` and `TauCeti.defectExponent_of_odd`: the defect of
  an element of odd valuation.
* `TauCeti.defectExponent_le_two_mul_natCastValuation`: the defect exponent of a nonsquare unit
  is at most `2 v_K(2)`.
* `TauCeti.defectExponent_eq_two_mul_natCastValuation_or_odd` and
  `TauCeti.quadraticDefect_eq_maximalIdeal_zpow_or_odd`: the possible defects of a unit.
* `TauCeti.exists_unit_defectExponent_eq_two_mul_natCastValuation` and
  `TauCeti.defectExponent_one_add_pow_odd`: every entry in that list is attained, with an explicit
  representative for each odd exponent.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A, in particular 63:1 and 63:2.
-/

public section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The set of `ξ` whose square approximates `a` to within the valuation of `y`, restricted to
`ξ` with `v(ξ²) ≤ v(a)`, is closed. -/
private theorem isClosed_approx (a y : K) :
    IsClosed {ξ : K | valuation K (ξ ^ 2) ≤ valuation K a ∧
      valuation K (a - ξ ^ 2) ≤ valuation K y} := by
  have hclosed : ∀ f : K → K, Continuous f → ∀ z : K,
      IsClosed {ξ : K | valuation K (f ξ) ≤ valuation K z} := fun f hf z => by
    have h := Valuation.isClosed_closedBall (v := valuation K) ((valuation K).restrict z)
    simp_rw [Valuation.restrict_le_iff] at h
    exact h.preimage hf
  exact (hclosed _ (by fun_prop) a).inter (hclosed _ (by fun_prop) y)

/-- The set of `ξ` whose square approximates `a` to within the valuation of `y`, restricted to
`ξ` with `v(ξ²) ≤ v(a)`, is compact. -/
private theorem isCompact_approx (a y : K) :
    IsCompact {ξ : K | valuation K (ξ ^ 2) ≤ valuation K a ∧
      valuation K (a - ξ ^ 2) ≤ valuation K y} := by
  refine (isCompact_closedBall K (max 1 (valuation K a))).of_isClosed_subset
    (isClosed_approx a y) ?_
  rintro ξ ⟨hξ, -⟩
  rw [Set.mem_ofPred_eq, le_max_iff, or_iff_not_imp_left, not_le]
  intro h1
  rw [map_pow] at hξ
  exact le_trans (by simpa using pow_le_pow_right₀ h1.le one_le_two) hξ

/-- The approximation orders of a nonsquare by squares are bounded: there is a nonzero `y`
whose valuation bounds every `v(a - ξ²)` from below. -/
private theorem exists_forall_valuation_le_valuation_sub_sq {a : K} (ha : ¬IsSquare a) :
    ∃ y : Kˣ, ∀ ξ : K, valuation K (y : K) ≤ valuation K (a - ξ ^ 2) := by
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by simp⟩
  by_contra! H
  -- `t y` is the set of approximations of `a` to within `v(y)`, of the size of `√a`.
  let t : Kˣ → Set K := fun y => {ξ : K | valuation K (ξ ^ 2) ≤ valuation K a ∧
      valuation K (a - ξ ^ 2) ≤ valuation K (y : K)}
  have hmono : ∀ y z : Kˣ, valuation K (y : K) ≤ valuation K (z : K) → t y ⊆ t z :=
    fun y z hyz ξ hξ => ⟨hξ.1, hξ.2.trans hyz⟩
  have hdir : Directed (· ⊇ ·) t := fun y z => by
    rcases le_total (valuation K (y : K)) (valuation K (z : K)) with h | h
    · exact ⟨y, subset_rfl, hmono y z h⟩
    · exact ⟨z, hmono z y h, subset_rfl⟩
  have hne : ∀ y, (t y).Nonempty := fun y => by
    -- Approximate to within the smaller of `v(y)` and `v(a)`.
    obtain ⟨z, hz⟩ : ∃ z : Kˣ, valuation K (z : K) ≤ valuation K (y : K) ∧
        valuation K (z : K) ≤ valuation K a := by
      rcases le_total (valuation K (y : K)) (valuation K a) with h | h
      · exact ⟨y, le_rfl, h⟩
      · exact ⟨Units.mk0 a ha0, h, le_rfl⟩
    obtain ⟨ξ, hξ⟩ := H z
    refine ⟨ξ, ?_, hξ.le.trans hz.1⟩
    calc valuation K (ξ ^ 2) = valuation K (a - (a - ξ ^ 2)) := by rw [sub_sub_cancel]
      _ ≤ max (valuation K a) (valuation K (a - ξ ^ 2)) := (valuation K).map_sub _ _
      _ = valuation K a := max_eq_left (hξ.le.trans hz.2)
  obtain ⟨ξ, hξ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hne
    (fun y => isCompact_approx a y) (fun y => isClosed_approx a y)
  rw [Set.mem_iInter] at hξ
  -- The common approximation `ξ` is a square root of `a`.
  apply ha
  refine ⟨ξ, ?_⟩
  by_contra hsub
  rw [← sq] at hsub
  replace hsub := sub_ne_zero.mpr hsub
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
  have hr0' : r ≠ 0 := by simpa using hr0
  have h := (hξ (Units.mk0 _ (mul_ne_zero hsub hr0'))).2
  rw [Units.val_mk0, map_mul] at h
  exact (mul_lt_of_lt_one_right ((valuation K).pos_iff.mpr hsub) hr1).not_ge h

/-- The approximation orders `v_K(a - ξ²)` of `a` by squares, for the `ξ` with `a ≠ ξ²`. -/
private def approxOrders (a : Kˣ) : Set ℤ :=
  {n | ∃ ξ : K, ∃ x : Kˣ, (x : K) = a - ξ ^ 2 ∧ (normalizedValuation K x).toAdd = n}

private theorem approxOrders_nonempty (a : Kˣ) : (approxOrders a).Nonempty :=
  ⟨_, 0, a, by simp, rfl⟩

private theorem bddAbove_approxOrders {a : Kˣ} (ha : ¬IsSquare a) :
    BddAbove (approxOrders a) := by
  rw [← isSquare_units_val_iff] at ha
  obtain ⟨y, hy⟩ := exists_forall_valuation_le_valuation_sub_sq ha
  refine ⟨(normalizedValuation K y).toAdd, ?_⟩
  rintro _ ⟨ξ, x, hx, rfl⟩
  rw [toAdd_normalizedValuation_le_iff_valuation_le, hx]
  exact hy ξ

open Classical in
/-- The **defect exponent** `δ(a) = sup_{ξ ∈ K} v_K(a - ξ²)` of `a : Kˣ`, where `v_K` is the
normalized valuation. It is `⊤` exactly when `a` is a square; otherwise the supremum is attained,
see `TauCeti.exists_defectExponent_eq`. -/
def defectExponent (a : Kˣ) : WithTop ℤ :=
  if IsSquare a then ⊤ else ((sSup (approxOrders a) : ℤ) : WithTop ℤ)

/-- The defect exponent is `⊤` exactly on squares. -/
@[simp]
theorem defectExponent_eq_top_iff {a : Kˣ} : defectExponent a = ⊤ ↔ IsSquare a := by
  unfold defectExponent
  split_ifs with h <;> simp [h]

/-- Every approximation order `v_K(a - ξ²)` is at most the defect exponent. -/
theorem le_defectExponent (a : Kˣ) (ξ : K) (x : Kˣ) (hx : (x : K) = a - ξ ^ 2) :
    ((normalizedValuation K x).toAdd : WithTop ℤ) ≤ defectExponent a := by
  unfold defectExponent
  split_ifs with h
  · exact le_top
  · exact WithTop.coe_le_coe.mpr (le_csSup (bddAbove_approxOrders h) ⟨ξ, x, hx, rfl⟩)

/-- The defect exponent of a nonsquare is attained by some approximation `ξ²` of `a`. -/
theorem exists_defectExponent_eq {a : Kˣ} (ha : ¬IsSquare a) :
    ∃ ξ : K, ∃ x : Kˣ, (x : K) = a - ξ ^ 2 ∧
      ((normalizedValuation K x).toAdd : WithTop ℤ) = defectExponent a := by
  obtain ⟨ξ, x, hx, hn⟩ := Int.csSup_mem (approxOrders_nonempty a) (bddAbove_approxOrders ha)
  refine ⟨ξ, x, hx, ?_⟩
  rw [defectExponent, ite_eq_right ha, hn]

/-- The valuation of `a` is at most its defect exponent, by the approximation `ξ = 0`. -/
theorem toAdd_normalizedValuation_le_defectExponent (a : Kˣ) :
    ((normalizedValuation K a).toAdd : WithTop ℤ) ≤ defectExponent a :=
  le_defectExponent a 0 a (by simp)

/-- An approximation `x = a - ξ²` of a nonsquare attaining the defect exponent has the
smallest valuation among all `a - η²`. -/
private theorem valuation_le_valuation_sub_sq_of_eq {a : Kˣ} (ha : ¬IsSquare a) {x : Kˣ}
    (hx : ((normalizedValuation K x).toAdd : WithTop ℤ) = defectExponent a) (η : K) :
    valuation K (x : K) ≤ valuation K ((a : K) - η ^ 2) := by
  have hne : (a : K) - η ^ 2 ≠ 0 := fun h =>
    ha (isSquare_units_val_iff.mp ⟨η, by rw [← sq]; exact sub_eq_zero.mp h⟩)
  have h := le_defectExponent a η (Units.mk0 _ hne) rfl
  rw [← hx, WithTop.coe_le_coe, toAdd_normalizedValuation_le_iff_valuation_le] at h
  simpa using h

/-- For every `a : Kˣ` some `ξ` makes `a - ξ²` of smallest valuation. For a square, `ξ` is a
square root of `a`. -/
private theorem exists_forall_valuation_sub_sq_le (a : Kˣ) :
    ∃ ξ₀ : K, ∀ ξ : K, valuation K ((a : K) - ξ₀ ^ 2) ≤ valuation K ((a : K) - ξ ^ 2) := by
  by_cases ha : IsSquare a
  · obtain ⟨r, hr⟩ := isSquare_units_val_iff.mpr ha
    exact ⟨r, fun ξ => by simp [hr, sq]⟩
  obtain ⟨ξ₀, x₀, hx₀, h₀⟩ := exists_defectExponent_eq ha
  exact ⟨ξ₀, fun ξ => hx₀ ▸ valuation_le_valuation_sub_sq_of_eq ha h₀ ξ⟩

/-- The fractional ideal `𝔡(a)` exists: the family `(a - ξ²) 𝒪[K]` has a least member. -/
private theorem exists_isGLB (a : Kˣ) : ∃ 𝔡 : FractionalIdeal (nonZeroDivisors 𝒪[K]) K,
    IsGLB (Set.range fun ξ : K => FractionalIdeal.spanSingleton _ ((a : K) - ξ ^ 2)) 𝔡 := by
  obtain ⟨ξ₀, h₀⟩ := exists_forall_valuation_sub_sq_le a
  refine ⟨_, IsLeast.isGLB ⟨⟨ξ₀, rfl⟩, ?_⟩⟩
  rintro _ ⟨ξ, rfl⟩
  exact spanSingleton_le_spanSingleton_iff_valuation_le.mpr (h₀ ξ)

/-- The **quadratic defect** `𝔡(a) = ⋂_{ξ ∈ K} (a - ξ²) 𝒪[K]` of `a : Kˣ`, the greatest
fractional ideal of `𝒪[K]` contained in every principal fractional ideal `(a - ξ²) 𝒪[K]`. -/
def quadraticDefect (a : Kˣ) : FractionalIdeal (nonZeroDivisors 𝒪[K]) K :=
  (exists_isGLB a).choose

/-- The quadratic defect is the greatest lower bound of the principal fractional ideals
`(a - ξ²) 𝒪[K]`. -/
theorem isGLB_quadraticDefect (a : Kˣ) :
    IsGLB (Set.range fun ξ : K => FractionalIdeal.spanSingleton _ ((a : K) - ξ ^ 2))
      (quadraticDefect a) :=
  (exists_isGLB a).choose_spec

/-- The quadratic defect is contained in every `(a - ξ²) 𝒪[K]`. -/
theorem quadraticDefect_le (a : Kˣ) (ξ : K) :
    quadraticDefect a ≤ FractionalIdeal.spanSingleton _ ((a : K) - ξ ^ 2) :=
  (isGLB_quadraticDefect a).1 ⟨ξ, rfl⟩

/-- A fractional ideal contained in every `(a - ξ²) 𝒪[K]` is contained in the quadratic
defect. -/
theorem le_quadraticDefect {a : Kˣ} {I : FractionalIdeal (nonZeroDivisors 𝒪[K]) K}
    (h : ∀ ξ : K, I ≤ FractionalIdeal.spanSingleton _ ((a : K) - ξ ^ 2)) :
    I ≤ quadraticDefect a :=
  (isGLB_quadraticDefect a).2 (by rintro _ ⟨ξ, rfl⟩; exact h ξ)

/-- If `a - ξ₀²` has the smallest valuation among the `a - ξ²`, the quadratic defect is
`(a - ξ₀²) 𝒪[K]`. -/
theorem quadraticDefect_eq_spanSingleton_of_forall {a : Kˣ} {ξ₀ : K}
    (h : ∀ ξ : K, valuation K ((a : K) - ξ₀ ^ 2) ≤ valuation K ((a : K) - ξ ^ 2)) :
    quadraticDefect a = FractionalIdeal.spanSingleton _ ((a : K) - ξ₀ ^ 2) :=
  le_antisymm (quadraticDefect_le a ξ₀)
    (le_quadraticDefect fun ξ => spanSingleton_le_spanSingleton_iff_valuation_le.mpr (h ξ))

/-- The infimum defining the quadratic defect is attained: `𝔡(a) = (a - ξ²) 𝒪[K]` for some
`ξ ∈ K`. -/
theorem exists_quadraticDefect_eq_spanSingleton (a : Kˣ) :
    ∃ ξ : K, quadraticDefect a = FractionalIdeal.spanSingleton _ ((a : K) - ξ ^ 2) :=
  (exists_forall_valuation_sub_sq_le a).imp fun _ => quadraticDefect_eq_spanSingleton_of_forall

/-- The quadratic defect vanishes exactly on squares. -/
@[simp]
theorem quadraticDefect_eq_zero_iff {a : Kˣ} : quadraticDefect a = 0 ↔ IsSquare a := by
  obtain ⟨ξ₀, h₀⟩ := exists_forall_valuation_sub_sq_le a
  rw [quadraticDefect_eq_spanSingleton_of_forall h₀, FractionalIdeal.spanSingleton_eq_zero_iff,
    sub_eq_zero, ← isSquare_units_val_iff]
  refine ⟨fun h => ⟨ξ₀, by rw [h, sq]⟩, fun ⟨r, hr⟩ => ?_⟩
  have h := h₀ r
  rwa [sq r, ← hr, sub_self, map_zero, le_zero_iff, map_eq_zero, sub_eq_zero] at h

/-- The quadratic defect of an integral element is an integral ideal. -/
theorem quadraticDefect_le_one {a : Kˣ} (ha : (a : K) ∈ 𝒪[K]) : quadraticDefect a ≤ 1 := by
  refine (quadraticDefect_le a 0).trans ?_
  rw [← FractionalIdeal.spanSingleton_one, spanSingleton_le_spanSingleton_iff_valuation_le,
    zero_pow two_ne_zero, sub_zero, map_one]
  exact (Valuation.mem_integer_iff _ _).mp ha

/-- Multiplying `a` by the square `c²` multiplies its quadratic defect by `c²`. -/
theorem quadraticDefect_mul_sq (a c : Kˣ) :
    quadraticDefect (a * c ^ 2) =
      FractionalIdeal.spanSingleton _ ((c : K) ^ 2) * quadraticDefect a := by
  obtain ⟨ξ₀, h₀⟩ := exists_forall_valuation_sub_sq_le a
  have hc : (c : K) ≠ 0 := c.ne_zero
  have key : ∀ ξ : K, ((a * c ^ 2 : Kˣ) : K) - (c * ξ) ^ 2 = (c : K) ^ 2 * ((a : K) - ξ ^ 2) :=
    fun ξ => by push_cast; ring
  rw [quadraticDefect_eq_spanSingleton_of_forall h₀,
    FractionalIdeal.spanSingleton_mul_spanSingleton, ← key]
  refine quadraticDefect_eq_spanSingleton_of_forall fun η => ?_
  have hη : η = c * (η / c) := by field_simp
  rw [hη, key, key, map_mul, map_mul]
  exact mul_le_mul_right (h₀ _) _

/-- Multiplying `a` by the square `c²` shifts its defect exponent by `2 v_K(c)`. -/
theorem defectExponent_mul_sq (a c : Kˣ) :
    defectExponent (a * c ^ 2) =
      defectExponent a + (2 * (normalizedValuation K c).toAdd : ℤ) := by
  have hsq : IsSquare (a * c ^ 2) ↔ IsSquare a :=
    ⟨fun h => by simpa [mul_assoc, ← mul_pow] using h.mul (IsSquare.sq c⁻¹),
      fun h => h.mul (IsSquare.sq c)⟩
  by_cases ha : IsSquare a
  · rw [defectExponent_eq_top_iff.mpr (hsq.mpr ha), defectExponent_eq_top_iff.mpr ha,
      WithTop.top_add]
  have hv : ∀ z d : Kˣ, (normalizedValuation K (z * d ^ 2)).toAdd =
      (normalizedValuation K z).toAdd + 2 * (normalizedValuation K d).toAdd := fun z d => by
    rw [map_mul, map_pow, toAdd_mul, toAdd_pow]
    ring
  have hc : (c : K) ≠ 0 := c.ne_zero
  obtain ⟨ξ, x, hx, hxd⟩ := exists_defectExponent_eq ha
  obtain ⟨η, y, hy, hyd⟩ := exists_defectExponent_eq (mt hsq.mp ha)
  -- `x c²` approximates `a c²` and `y c⁻²` approximates `a`.
  have h1 := le_defectExponent (a * c ^ 2) (c * ξ) (x * c ^ 2) (by push_cast; rw [hx]; ring)
  have h2 := le_defectExponent a (η / c) (y * c⁻¹ ^ 2)
    (by push_cast at hy ⊢; rw [hy]; field_simp)
  rw [hv, ← hyd] at h1
  rw [hv, ← hxd, map_inv, toAdd_inv] at h2
  rw [← hxd, ← hyd]
  norm_cast at h1 h2 ⊢
  omega

/-- For `a` of odd valuation, `v(a - ξ²) = min (v(a), 2 v(ξ))` never exceeds `v(a)`. -/
private theorem valuation_le_valuation_sub_sq {a : Kˣ}
    (ha : ¬Even (normalizedValuation K a).toAdd) (ξ : K) :
    valuation K (a : K) ≤ valuation K ((a : K) - ξ ^ 2) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  have hne : valuation K (ξ ^ 2) ≠ valuation K (a : K) := fun h => ha <| by
    have e : (normalizedValuation K (Units.mk0 ξ hξ ^ 2)).toAdd =
        (normalizedValuation K a).toAdd :=
      le_antisymm ((toAdd_normalizedValuation_le_iff_valuation_le _ _).mpr (by simpa using h.ge))
        ((toAdd_normalizedValuation_le_iff_valuation_le _ _).mpr (by simpa using h.le))
    rw [← e, map_pow, toAdd_pow]
    exact ⟨_, two_nsmul _⟩
  rcases hne.lt_or_gt with h | h
  · exact (Valuation.map_sub_eq_of_lt_left _ h).ge
  · exact (Valuation.map_sub_eq_of_lt_right _ h).symm ▸ h.le

/-- The defect exponent of an element of odd valuation is its valuation. -/
theorem defectExponent_of_odd {a : Kˣ} (ha : Odd (normalizedValuation K a).toAdd) :
    defectExponent a = (normalizedValuation K a).toAdd := by
  have ha' : ¬Even (normalizedValuation K a).toAdd := Int.not_even_iff_odd.mpr ha
  have hsq : ¬IsSquare a := fun ha => ha' (even_toAdd_normalizedValuation_of_isSquare ha)
  refine le_antisymm ?_ (toAdd_normalizedValuation_le_defectExponent a)
  obtain ⟨ξ, x, hx, hxd⟩ := exists_defectExponent_eq hsq
  rw [← hxd, WithTop.coe_le_coe, toAdd_normalizedValuation_le_iff_valuation_le, hx]
  exact valuation_le_valuation_sub_sq ha' ξ

/-- The quadratic defect of an element `a` of odd valuation is `a 𝒪[K]`. -/
theorem quadraticDefect_of_odd {a : Kˣ} (ha : Odd (normalizedValuation K a).toAdd) :
    quadraticDefect a = FractionalIdeal.spanSingleton _ (a : K) := by
  have ha' : ¬Even (normalizedValuation K a).toAdd := Int.not_even_iff_odd.mpr ha
  simpa using quadraticDefect_eq_spanSingleton_of_forall (a := a) (ξ₀ := 0)
    (by simpa using valuation_le_valuation_sub_sq ha')

/-- The quadratic defect of a nonsquare is `𝓂[K] ^ δ(a)`, for its defect exponent `δ(a)`. -/
theorem quadraticDefect_eq_maximalIdeal_zpow {a : Kˣ} {n : ℤ} (h : defectExponent a = n) :
    quadraticDefect a =
      ((IsLocalRing.maximalIdeal 𝒪[K] : Ideal 𝒪[K]) : FractionalIdeal (nonZeroDivisors 𝒪[K]) K) ^
        n := by
  have ha : ¬IsSquare a := fun hsq => by simp [defectExponent_eq_top_iff.mpr hsq] at h
  obtain ⟨ξ, x, hx, hxd⟩ := exists_defectExponent_eq ha
  have hle := valuation_le_valuation_sub_sq_of_eq ha hxd
  rw [h, WithTop.coe_inj] at hxd
  rw [← hxd, ← Units.spanSingleton_eq_maximalIdeal_zpow, hx]
  exact quadraticDefect_eq_spanSingleton_of_forall (hx ▸ hle)


section UnitDefect

variable {π : 𝒪[K]}

/-- **The improvement step of O'Meara 63:2.** In residue characteristic two, an approximation
`u - ξ²` of an integral element `u` of `Kˣ` of order exactly `2k` with `k < v_K(2)` is not
optimal: writing `(u - ξ²)/π^{2k} ≡ s² mod 𝓂[K]`, which is possible because the residue field is
perfect of characteristic two, the correction `ξ + π^k s` approximates `u` to order at least
`2k + 1`. The hypothesis `k < v_K(2)` is what makes the cross term `2 ξ π^k s` negligible. -/
theorem exists_valuation_sub_sq_le_of_lt_natCastValuation (h2 : (2 : K) ≠ 0)
    (hπ : Irreducible π) {u : Kˣ} (hu : valuation K (u : K) ≤ 1) {ξ : K} {k : ℕ}
    (hk : k < natCastValuation K 2 h2)
    (hξ : valuation K ((u : K) - ξ ^ 2) = valuation K (π : K) ^ (2 * k)) :
    ∃ η : K, valuation K ((u : K) - η ^ 2) ≤ valuation K (π : K) ^ (2 * k + 1) := by
  have hπ0 : (π : K) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hπ1 : valuation K (π : K) < 1 :=
    Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ
  have hπv : valuation K (π : K) ≠ 0 := by simpa using hπ0
  -- The residue field has characteristic two, so every residue is a square.
  have hchar : ringChar 𝓀[K] = 2 :=
    (natCastValuation_ne_zero_iff_ringChar_eq K Nat.prime_two h2).mp (by omega)
  -- `c = (u - ξ²)/π^{2k}` is a unit of `𝒪[K]`.
  set c : K := ((u : K) - ξ ^ 2) / (π : K) ^ (2 * k) with hc
  have hcv : valuation K c = 1 := by
    rw [hc, map_div₀, hξ, map_pow, div_self (pow_ne_zero _ hπv)]
  have hcO : c ∈ 𝒪[K] := (Valuation.mem_integer_iff _ _).mpr hcv.le
  obtain ⟨t, ht⟩ := FiniteField.isSquare_of_char_two hchar
    (IsLocalRing.residue 𝒪[K] ⟨c, hcO⟩)
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective t
  have hsmem : (⟨c, hcO⟩ : 𝒪[K]) - s ^ 2 ∈ 𝓂[K] := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simp [sq, ht]
  have hsv : valuation K (c - (s : K) ^ 2) ≤ valuation K (π : K) := by
    have h := (Set.ext_iff.mp
      (hπ.maximalIdeal_eq_setOfPred_le_v_coe (valuation K))
      ((⟨c, hcO⟩ : 𝒪[K]) - s ^ 2)).mp hsmem
    convert h using 1
    simp
  -- The corrected approximation.
  refine ⟨ξ + (π : K) ^ k * (s : K), ?_⟩
  have hcmul : ((π : K) ^ k) ^ 2 * c = (u : K) - ξ ^ 2 := by
    rw [hc, ← pow_mul, mul_comm k 2, mul_div_cancel₀ _ (pow_ne_zero _ hπ0)]
  have hid : (u : K) - (ξ + (π : K) ^ k * (s : K)) ^ 2
      = ((π : K) ^ k) ^ 2 * (c - (s : K) ^ 2) - 2 * ξ * ((π : K) ^ k * (s : K)) := by
    linear_combination -hcmul
  -- Both terms have valuation at most `v(π)^{2k+1}`.
  have hb1 : valuation K (((π : K) ^ k) ^ 2 * (c - (s : K) ^ 2))
      ≤ valuation K (π : K) ^ (2 * k + 1) := by
    rw [map_mul, map_pow, map_pow, ← pow_mul, mul_comm k 2,
      pow_succ (valuation K (π : K)) (2 * k)]
    exact mul_le_mul' le_rfl hsv
  have hb2 : valuation K (2 * ξ * ((π : K) ^ k * (s : K)))
      ≤ valuation K (π : K) ^ (2 * k + 1) := by
    have hv2 : valuation K (2 : K) ≤ valuation K (π : K) ^ natCastValuation K 2 h2 :=
      (valuation_natCast_eq_pow hπ 2 h2).le
    have hξ1 : valuation K ξ ≤ 1 :=
      valuation_le_one_of_sub_sq_le_one hu
        (hξ ▸ pow_le_one₀ zero_le hπ1.le)
    have hs1 : valuation K (s : K) ≤ 1 := (Valuation.mem_integer_iff _ _).mp s.2
    calc valuation K (2 * ξ * ((π : K) ^ k * (s : K)))
        = valuation K (2 : K) * valuation K ξ *
            (valuation K (π : K) ^ k * valuation K (s : K)) := by
          rw [map_mul, map_mul, map_mul, map_pow]
      _ ≤ valuation K (π : K) ^ natCastValuation K 2 h2 * 1 * (valuation K (π : K) ^ k * 1) := by
          gcongr
      _ = valuation K (π : K) ^ (natCastValuation K 2 h2 + k) := by
          rw [pow_add, mul_one, mul_one]
      _ ≤ valuation K (π : K) ^ (2 * k + 1) :=
          pow_le_pow_right_of_le_one' hπ1.le (by omega)
  rw [hid]
  exact le_trans ((valuation K).map_sub _ _) (max_le hb1 hb2)

/-- **The local square theorem bounds the defect of a unit.** A unit of `𝒪[K]` approximated by a
square to order `2 v_K(2) + 1` is a square, so the defect exponent of a nonsquare unit is at most
`2 v_K(2)`. In odd residue characteristic the bound is `0`. -/
theorem defectExponent_le_two_mul_natCastValuation (h2 : (2 : K) ≠ 0) {u : Kˣ}
    (hu : valuation K (u : K) = 1) (hsq : ¬IsSquare u) :
    defectExponent u ≤ ((2 * natCastValuation K 2 h2 : ℕ) : ℤ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[K])
  obtain ⟨ξ, x, hx, hxd⟩ := exists_defectExponent_eq hsq
  rw [← hxd, WithTop.coe_le_coe]
  by_contra hcon
  rw [not_le] at hcon
  have hπ1 : valuation K (π : K) < 1 :=
    Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ
  -- `x = u - ξ²` is deeper than the local square theorem needs.
  have hxv : valuation K (x : K)
      ≤ valuation K (π : K) ^ (2 * natCastValuation K 2 h2 + 1) := by
    have h := (le_toAdd_normalizedValuation_iff_valuation_le_zpow
      (normalizedValuation_irreducible hπ)
      ((2 * natCastValuation K 2 h2 + 1 : ℕ) : ℤ) x).mp (by push_cast; omega)
    simpa only [zpow_natCast, Units.val_mk0] using h
  have hxlt : valuation K (x : K) < 1 :=
    hxv.trans_lt (pow_lt_one₀ zero_le hπ1 (Nat.succ_ne_zero _))
  -- Hence `ξ` is a unit of `𝒪[K]`.
  have hξv : valuation K (ξ ^ 2) = 1 := by
    have hsub : (ξ : K) ^ 2 = (u : K) - (x : K) := by rw [hx]; ring
    rw [hsub, Valuation.map_sub_eq_of_lt_left _ (hu ▸ hxlt), hu]
  have hξ0 : ξ ≠ 0 := by rintro rfl; simp at hξv
  set ξu : Kˣ := Units.mk0 ξ hξ0 with hξu
  -- `u / ξ²` is a unit of depth `2 v_K(2) + 1`, hence a square.
  set w : Kˣ := u * (ξu ^ 2)⁻¹ with hw
  have hwval : (w : K) = (u : K) * (ξ ^ 2)⁻¹ := by simp [hw, hξu]
  have hw1 : (w : K) - 1 = (x : K) / ξ ^ 2 := by
    rw [hwval, hx]
    field_simp
  have hwmem : w ∈ unitFiltration K (2 * natCastValuation K 2 h2 + 1) := by
    rw [mem_unitFiltration_succ_valuation _ _ π hπ, hw1, map_div₀, hξv, div_one, map_pow]
    exact hxv
  obtain ⟨z, hz⟩ := unitFiltration_le_range_powMonoidHom_two h2 hwmem
  rw [powMonoidHom_apply] at hz
  refine hsq ⟨z * ξu, ?_⟩
  rw [← sq, mul_pow, hz, hw]
  group

/-- **The possible defects of a unit** (O'Meara 63:2). For a unit of `𝒪[K]` which is not a square,
the defect exponent is either `2 v_K(2)` or an odd number below `2 v_K(2)`; equivalently, by
`TauCeti.quadraticDefect_eq_maximalIdeal_zpow`, the defect is `𝓂[K] ^ (2 v_K(2)) = 4 𝒪[K]` or
`𝓂[K] ^ (2k+1)` with `k < v_K(2)`. In odd residue characteristic the list has the single entry
`𝒪[K]`, and the statement is Hensel's lemma. The defect of a square is `0`. -/
theorem defectExponent_eq_two_mul_natCastValuation_or_odd (h2 : (2 : K) ≠ 0) {u : Kˣ}
    (hu : valuation K (u : K) = 1) (hsq : ¬IsSquare u) :
    defectExponent u = ((2 * natCastValuation K 2 h2 : ℕ) : ℤ) ∨
      ∃ k < natCastValuation K 2 h2, defectExponent u = ((2 * k + 1 : ℕ) : ℤ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[K])
  obtain ⟨ξ, x, hx, hxd⟩ := exists_defectExponent_eq hsq
  set e := natCastValuation K 2 h2 with he
  set d := (normalizedValuation K x).toAdd with hd
  -- The valuation of `u` is one of the approximation orders, so `0 ≤ δ(u)`.
  have hd0 : 0 ≤ d := by
    have h := toAdd_normalizedValuation_le_defectExponent u
    rw [← hxd, (normalizedValuation_eq_one_iff u).mpr hu, toAdd_one, WithTop.coe_le_coe] at h
    exact h
  have hdle : d ≤ 2 * e := by
    have h := defectExponent_le_two_mul_natCastValuation h2 hu hsq
    rw [← hxd, WithTop.coe_le_coe] at h
    exact_mod_cast h
  -- Below `2 v_K(2)` an even order can always be improved, so `δ(u)` is odd there.
  have hodd : d < 2 * e → Odd d := by
    intro hlt
    rw [← Int.not_even_iff_odd]
    rintro ⟨m, hm⟩
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = m := ⟨m.toNat, Int.toNat_of_nonneg (by omega)⟩
    have hξv : valuation K ((u : K) - ξ ^ 2) = valuation K (π : K) ^ (2 * k) := by
      have h := (toAdd_normalizedValuation_eq_iff_valuation_eq_zpow
        (normalizedValuation_irreducible hπ) ((2 * k : ℕ) : ℤ) x).mp (by push_cast; omega)
      rw [hx] at h
      simpa only [zpow_natCast, Units.val_mk0] using h
    obtain ⟨η, hη⟩ := exists_valuation_sub_sq_le_of_lt_natCastValuation h2 hπ hu.le
      (k := k) (by omega) hξv
    have hle := (valuation_le_valuation_sub_sq_of_eq hsq hxd η).trans hη
    have h := (le_toAdd_normalizedValuation_iff_valuation_le_zpow
      (normalizedValuation_irreducible hπ) ((2 * k + 1 : ℕ) : ℤ) x).mpr
      (by simpa only [zpow_natCast, Units.val_mk0] using hle)
    push_cast at h
    omega
  rcases eq_or_lt_of_le hdle with heq | hlt
  · left
    rw [← hxd]
    exact_mod_cast heq
  · obtain ⟨m, hm⟩ := hodd hlt
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = m := ⟨m.toNat, Int.toNat_of_nonneg (by omega)⟩
    have hd_eq : d = ((2 * k + 1 : ℕ) : ℤ) := by
      push_cast
      omega
    exact Or.inr ⟨k, by omega, by rw [← hxd, hd_eq]⟩

/-- The maximal finite unit defect is attained. This is the defect-theoretic form of the
sharpness of the local square theorem: a nonsquare in `U(K, 2 v_K(2))` is approximated by `1²`
to order at least `2 v_K(2)`, while no nonsquare unit has larger defect exponent. -/
theorem exists_unit_defectExponent_eq_two_mul_natCastValuation (h2 : (2 : K) ≠ 0) :
    ∃ u : Kˣ, valuation K (u : K) = 1 ∧ ¬IsSquare u ∧
      defectExponent u = ((2 * natCastValuation K 2 h2 : ℕ) : ℤ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[K])
  obtain ⟨u, hu, hsq⟩ := SetLike.not_le_iff_exists.mp
    (not_unitFiltration_le_range_powMonoidHom_two (K := K) h2)
  have huval : valuation K (u : K) = 1 := ((mem_unitFiltration_iff_valuation_le hπ).mp hu).1
  have hnsq : ¬IsSquare u := by
    simpa only [MonoidHom.mem_range, powMonoidHom_apply, isSquare_iff_exists_sq, eq_comm] using hsq
  refine ⟨u, huval, hnsq, le_antisymm
    (defectExponent_le_two_mul_natCastValuation h2 huval hnsq) ?_⟩
  have hu1 : valuation K ((u : K) - 1) ≤
      valuation K (π : K) ^ (2 * natCastValuation K 2 h2) :=
    ((mem_unitFiltration_iff_valuation_le hπ).mp hu).2
  have hu_ne : (u : K) - 1 ≠ 0 := by
    intro huz
    apply hnsq
    have : u = 1 := Units.ext (sub_eq_zero.mp huz)
    rw [this]
    exact IsSquare.one
  let x : Kˣ := Units.mk0 ((u : K) - 1) hu_ne
  have hx : ((2 * natCastValuation K 2 h2 : ℕ) : ℤ) ≤
      (normalizedValuation K x).toAdd :=
    (le_toAdd_normalizedValuation_iff_valuation_le_zpow
      (normalizedValuation_irreducible hπ)
      ((2 * natCastValuation K 2 h2 : ℕ) : ℤ) x).mpr
        (by simpa only [x, Units.val_mk0, zpow_natCast] using hu1)
  exact (WithTop.coe_le_coe.mpr hx).trans (le_defectExponent u 1 x (by simp [x]))

/-- For `k < v_K(2)`, the unit represented by `1 + π^(2k+1)` has defect exponent exactly
`2k+1`. -/
theorem defectExponent_one_add_pow_odd (h2 : (2 : K) ≠ 0) {π : 𝒪[K]}
    (hπ : Irreducible π) {k : ℕ} (hk : k < natCastValuation K 2 h2) :
    defectExponent (Units.mk0 (1 + (π : K) ^ (2 * k + 1))
      (one_add_pow_ne_zero_of_valuation_lt_one
        (Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ) (by omega))) =
      ((2 * k + 1 : ℕ) : ℤ) := by
  have hπ0 : (π : K) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
  have hπ1 : valuation K (π : K) < 1 :=
    Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ
  let hu0 : 1 + (π : K) ^ (2 * k + 1) ≠ 0 :=
    one_add_pow_ne_zero_of_valuation_lt_one hπ1 (by omega)
  -- Proof irrelevance identifies the nonzero proof in the statement with the named proof `hu0`.
  change defectExponent (Units.mk0 (1 + (π : K) ^ (2 * k + 1)) hu0) = _
  let u : Kˣ := Units.mk0 (1 + (π : K) ^ (2 * k + 1)) hu0
  have hnsq : ¬IsSquare u := by
    simpa only [u] using not_isSquare_one_add_pow_odd h2 hπ hk
  obtain ⟨ξ, x, hx, hxd⟩ := exists_defectExponent_eq hnsq
  have hp0 : (π : K) ^ (2 * k + 1) ≠ 0 := pow_ne_zero _ hπ0
  let p : Kˣ := Units.mk0 ((π : K) ^ (2 * k + 1)) hp0
  have hpadd : (normalizedValuation K p).toAdd = ((2 * k + 1 : ℕ) : ℤ) :=
    (toAdd_normalizedValuation_eq_iff_valuation_eq_zpow
      (normalizedValuation_irreducible hπ) _ p).mpr
        (by simp only [p, Units.val_mk0, zpow_natCast, map_pow])
  have hlower : (((2 * k + 1 : ℕ) : ℤ) : WithTop ℤ) ≤ defectExponent u := by
    rw [← hpadd]
    exact le_defectExponent u 1 p (by simp [u, p])
  have hupper : defectExponent u ≤ (((2 * k + 1 : ℕ) : ℤ) : WithTop ℤ) := by
    rw [← hxd, WithTop.coe_le_coe]
    by_contra hle
    have hlt : ((2 * k + 1 : ℕ) : ℤ) < (normalizedValuation K x).toAdd :=
      lt_of_not_ge hle
    have hnle : ¬(normalizedValuation K x).toAdd ≤ (normalizedValuation K p).toAdd := by
      rw [hpadd]
      exact not_le.mpr hlt
    rw [toAdd_normalizedValuation_le_iff_valuation_le] at hnle
    have hxlt : valuation K (x : K) < valuation K (p : K) := lt_of_not_ge hnle
    apply valuation_sq_sub_one_ne_pow_odd h2 hπ hk ξ
    calc
      valuation K (ξ ^ 2 - 1) =
          valuation K (((u : K) - 1) - ((u : K) - ξ ^ 2)) := by congr 1; ring
      _ = valuation K (((u : K) - 1) - (x : K)) := by rw [hx]
      _ = valuation K ((u : K) - 1) :=
        (valuation K).map_sub_eq_of_lt_left (by simpa [u, p] using hxlt)
      _ = valuation K (π : K) ^ (2 * k + 1) := by simp [u, map_pow]
  exact le_antisymm hupper hlower

/-- Every odd unit defect below the maximal one is attained. -/
theorem exists_unit_defectExponent_eq_odd (h2 : (2 : K) ≠ 0)
    {k : ℕ} (hk : k < natCastValuation K 2 h2) :
    ∃ u : Kˣ, valuation K (u : K) = 1 ∧ ¬IsSquare u ∧
      defectExponent u = ((2 * k + 1 : ℕ) : ℤ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[K])
  have hπ1 : valuation K (π : K) < 1 :=
    Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ
  have hp1 : valuation K ((π : K) ^ (2 * k + 1)) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le hπ1 (by omega)
  have huval : valuation K (1 + (π : K) ^ (2 * k + 1)) = 1 :=
    (valuation K).map_one_add_of_lt hp1
  have hu0 : 1 + (π : K) ^ (2 * k + 1) ≠ 0 := by
    exact one_add_pow_ne_zero_of_valuation_lt_one hπ1 (by omega)
  let u : Kˣ := Units.mk0 (1 + (π : K) ^ (2 * k + 1)) hu0
  exact ⟨u, by simpa [u] using huval, by
    simpa only [u] using not_isSquare_one_add_pow_odd h2 hπ hk, by
    simpa only [u] using defectExponent_one_add_pow_odd h2 hπ hk⟩

/-- **The possible defects of a unit, as ideals** (O'Meara 63:2). The quadratic defect of a
nonsquare unit of `𝒪[K]` is `𝓂[K] ^ (2 v_K(2))`, which is the ideal `4 𝒪[K]` by
`TauCeti.span_four_eq_maximalIdeal_pow`, or `𝓂[K] ^ (2k+1)` for some `k < v_K(2)`. With
`TauCeti.quadraticDefect_eq_zero_iff`, which covers the squares, this is the complete list of
the defects of units, of length `v_K(2) + 2`. -/
theorem quadraticDefect_eq_maximalIdeal_zpow_or_odd (h2 : (2 : K) ≠ 0) {u : Kˣ}
    (hu : valuation K (u : K) = 1) (hsq : ¬IsSquare u) :
    quadraticDefect u =
        ((IsLocalRing.maximalIdeal 𝒪[K] : Ideal 𝒪[K]) :
          FractionalIdeal (nonZeroDivisors 𝒪[K]) K) ^ ((2 * natCastValuation K 2 h2 : ℕ) : ℤ) ∨
      ∃ k < natCastValuation K 2 h2, quadraticDefect u =
        ((IsLocalRing.maximalIdeal 𝒪[K] : Ideal 𝒪[K]) :
          FractionalIdeal (nonZeroDivisors 𝒪[K]) K) ^ ((2 * k + 1 : ℕ) : ℤ) := by
  rcases defectExponent_eq_two_mul_natCastValuation_or_odd h2 hu hsq with h | ⟨k, hk, h⟩
  · exact Or.inl (quadraticDefect_eq_maximalIdeal_zpow h)
  · exact Or.inr ⟨k, hk, quadraticDefect_eq_maximalIdeal_zpow h⟩

end UnitDefect

end TauCeti
