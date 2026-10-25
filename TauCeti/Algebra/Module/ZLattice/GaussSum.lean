/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.IndexNSmul
public import TauCeti.Algebra.Module.ZLattice.Integral
public import TauCeti.Analysis.SpecialFunctions.Exp.Periodic

/-!
# Gauss sums of an even lattice

Let `L` be an even lattice in a real inner product space `E`, write `e(x) = exp (2 π i x)`, and
let `c` be a natural number. For `a : ℤ` the *Gauss sum* of `L` is the finite sum

`G_L(a, c) = ∑_{y ∈ L / cL} e(a ‖y‖² / (2c))`,

and for `m` in the dual lattice `L^∨` the *twisted Gauss sum* is

`G_L(a, c; m) = ∑_{y ∈ L / cL} e(a ‖y‖² / (2c) + ⟪y, m⟫ / c)`.

The summand is a function on the quotient `L / cL` because `L` is even and `m ∈ L^∨`: replacing
`y` by `y + c w` with `w ∈ L` changes the argument of `e` by
`a ⟪y, w⟫ + a c ‖w‖² / 2 + ⟪w, m⟫ ∈ ℤ`. Both hypotheses are needed: on the odd lattice `ℤ ⊆ ℝ`,
with `a = c = 1` and `m = 0`, the representatives `0` and `1` of the single class of `ℤ / ℤ` give
`e(0) = 1` and `e(1/2) = -1`. They are therefore arguments of the summand `ZLattice.gaussTerm`:
the evenness of `L` as a proof, and `m` as an element of `L^∨` rather than of `E`. Here `cL` is
the lattice `(c : ℝ) • L`, read in `L` through `Submodule.submoduleOf`, so that the classes of
`L / cL` are those used to split a theta series of `L` into theta series of translates of `cL`.
For a full lattice of rank `n` and `c ≠ 0` the quotient is finite of order `c ^ n`.

These sums are the arithmetic input to the transformation law of the theta series of an even
lattice under `Γ₀(N)`, where `N` is the level of `L`: the least `N > 0` with `N ‖x‖² ∈ 2ℤ` for
every `x ∈ L^∨`. Splitting `L` into classes modulo `c` expresses the theta series at a cusp `a / c`
through the twisted Gauss sums, and the two facts proved here for `c` with `c ‖x‖² ∈ 2ℤ` on `L^∨`
(that is, for multiples `c` of the level) reduce them to the untwisted sum: `G_L(a, c; m)` vanishes
unless `m ∈ L`, by the shift `y ↦ y + c w`, `w ∈ L^∨`, which multiplies the sum by `e(⟪w, m⟫)`; and
for `m ∈ L` and `a d ≡ 1 (mod c)`, completing the square gives
`G_L(a, c; m) = e(-a d² ‖m‖² / (2c)) G_L(a, c)`.

## Main definitions

* `ZLattice.gaussTerm L hL a c m`: the summand `e(a ‖y‖² / (2c) + ⟪y, m⟫ / c)` on `L / cL`.
* `ZLattice.gaussSumTwisted L hL a c m`: the twisted Gauss sum `G_L(a, c; m)`.
* `ZLattice.gaussSum L hL a c`: the Gauss sum `G_L(a, c)`.

## Main statements

* `ZLattice.card_quotient_smul_submoduleOf`: `L / cL` has `c ^ n` elements for a full lattice
  `L` of rank `n`; it is finite for `c ≠ 0`.
* `ZLattice.gaussSumTwisted_eq_of_modEq`, `ZLattice.gaussSum_eq_of_modEq`: the Gauss sums depend
  on `a` only modulo `c`.
* `ZLattice.gaussSumTwisted_one`, `ZLattice.gaussSum_one`: `G_L(a, 1; m) = G_L(a, 1) = 1`.
* `ZLattice.gaussSum_comap`: the Gauss sums are invariant under linear isometry equivalences.
* `ZLattice.gaussSumTwisted_eq_zero`: if `c ‖x‖² ∈ 2ℤ` for every `x ∈ L^∨`, then
  `G_L(a, c; m) = 0` for `m ∈ L^∨ \ L`.
* `ZLattice.gaussSumTwisted_eq_of_mem`: for `m ∈ L` and `a d ≡ 1 (mod c)`,
  `G_L(a, c; m) = e(-a d² ‖m‖² / (2c)) G_L(a, c)`.

## References

* B. Schoeneberg, *Elliptic Modular Functions*, Springer, 1974, Chapter IX.
-/

public section

open Complex Module Submodule
open scoped Pointwise Real RealInnerProductSpace

namespace ZLattice

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-! ### The quotient `L / cL` -/

section Quotient

variable {L : Submodule ℤ E}

/-- A vector of `L` lies in `cL = (c : ℝ) • L` exactly when it is `c` times a vector of `L`. -/
theorem mem_smul_submoduleOf_iff {c : ℕ} {v : L} :
    v ∈ ((c : ℝ) • L).submoduleOf L ↔ ∃ w : L, c • w = v := by
  rw [submoduleOf, Submodule.mem_comap, subtype_apply, mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, hw, h⟩
    exact ⟨⟨w, hw⟩, Subtype.ext (by rw [← h, Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul])⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w, w.2, by rw [Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul]⟩

variable (L) [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L]

/-- The quotient `L / cL` of a full lattice of rank `n` has `c ^ n` elements. For `c = 0` this
reads `Nat.card L = 0 ^ n`: the lattice is infinite unless `n = 0`. -/
theorem card_quotient_smul_submoduleOf (c : ℕ) :
    Nat.card (L ⧸ ((c : ℝ) • L).submoduleOf L) = c ^ finrank ℝ E := by
  have h : (((c : ℝ) • L).submoduleOf L).toAddSubgroup = (nsmulAddMonoidHom (α := L) c).range := by
    ext v
    simp [mem_smul_submoduleOf_iff]
  rw [← ZLattice.rank ℝ L, ← AddSubgroup.index_range_nsmul L c, ← h]
  -- The quotient by a submodule is by definition the quotient by its additive subgroup, whose
  -- order is the index.
  rfl

instance (c : ℕ) [NeZero c] : Finite (L ⧸ ((c : ℝ) • L).submoduleOf L) :=
  Nat.finite_of_card_ne_zero <| by
    rw [card_quotient_smul_submoduleOf]
    exact pow_ne_zero _ (NeZero.ne c)

end Quotient

/-! ### The summand -/

section GaussTerm

/-- The argument of `e` in the twisted Gauss summand, at `v + c w`: the change from `v` is
`a ⟪v, w⟫ + a c ‖w‖² / 2 + ⟪w, m⟫`. -/
private theorem gaussArg_add_smul (a : ℝ) {c : ℝ} (hc : c ≠ 0) (m v w : E) :
    (a * ‖v + c • w‖ ^ 2 / 2 + ⟪v + c • w, m⟫) / c =
      (a * ‖v‖ ^ 2 / 2 + ⟪v, m⟫) / c + (a * ⟪v, w⟫ + a * (c * ‖w‖ ^ 2) / 2 + ⟪w, m⟫) := by
  rw [norm_add_sq_real, norm_smul, inner_add_left, inner_smul_left, inner_smul_right,
    Real.norm_eq_abs, mul_pow, sq_abs, conj_trivial]
  field_simp
  ring

variable (L : Submodule ℤ E)

/-- The summand `e(a ‖y‖² / (2c) + ⟪y, m⟫ / c)` of the twisted Gauss sums of an even lattice `L`,
as a function of the class `y ∈ L / cL`. It is well defined because `L` is even and `m ∈ L^∨`;
both are therefore arguments. -/
noncomputable def gaussTerm (hL : IsEven L) (a : ℤ) (c : ℕ) (m : dual L)
    (y : L ⧸ ((c : ℝ) • L).submoduleOf L) : ℂ :=
  Quotient.liftOn' y
    (fun v : L => cexp (2 * π * I * (((a * ‖(v : E)‖ ^ 2 / 2 + ⟪(v : E), (m : E)⟫) / c : ℝ) : ℂ)))
    fun v₁ v₂ h => by
      obtain ⟨w, hw⟩ := mem_smul_submoduleOf_iff.mp (quotientRel_def _ |>.mp h)
      obtain rfl : v₁ = v₂ + c • w := by rw [hw]; abel
      rcases eq_or_ne c 0 with rfl | hc
      · simp
      have hc' : (c : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hc
      obtain ⟨i, hi⟩ := isIntegral_iff.mp hL.isIntegral _ v₂.2 _ w.2
      obtain ⟨j, hj⟩ := isEven_iff.mp hL _ w.2
      obtain ⟨k, hk⟩ := mem_dual.mp m.2 _ w.2
      -- The argument changes by `a ⟪v₂, w⟫ + a c ‖w‖² / 2 + ⟪w, m⟫`, an integer.
      have hint : (a : ℝ) * i + a * (c * (2 * j)) / 2 + k = ((a * i + a * c * j + k : ℤ) : ℝ) := by
        push_cast; ring
      simp only [coe_add, Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul ℝ]
      rw [gaussArg_add_smul _ hc', hi, hj, real_inner_comm (m : E) (w : E), hk, hint,
        ofReal_add _ ((a * i + a * c * j + k : ℤ) : ℝ), ofReal_intCast,
        exp_two_pi_mul_I_mul_add_intCast]

variable {L}

/-- The Gauss summand of the class of `v ∈ L` is `e((a ‖v‖² / 2 + ⟪v, m⟫) / c)`. -/
@[simp]
theorem gaussTerm_mk (hL : IsEven L) (a : ℤ) (c : ℕ) (m : dual L) (v : L) :
    gaussTerm L hL a c m (Submodule.Quotient.mk v) =
      cexp (2 * π * I * (((a * ‖(v : E)‖ ^ 2 / 2 + ⟪(v : E), (m : E)⟫) / c : ℝ) : ℂ)) :=
  (rfl)

end GaussTerm

/-! ### Gauss sums -/

variable (L : Submodule ℤ E)

/-- The twisted Gauss sum `G_L(a, c; m) = ∑_{y ∈ L / cL} e(a ‖y‖² / (2c) + ⟪y, m⟫ / c)` of an even
lattice `L`, for `m ∈ L^∨`. The quotient `L / cL` is finite for a full lattice and `c ≠ 0`. -/
noncomputable def gaussSumTwisted (hL : IsEven L) (a : ℤ) (c : ℕ)
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (m : dual L) : ℂ :=
  ∑ y, gaussTerm L hL a c m y

/-- The Gauss sum `G_L(a, c) = ∑_{y ∈ L / cL} e(a ‖y‖² / (2c))` of an even lattice `L`. -/
noncomputable def gaussSum (hL : IsEven L) (a : ℤ) (c : ℕ)
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] : ℂ :=
  ∑ y, gaussTerm L hL a c 0 y

variable {L} (hL : IsEven L)

theorem gaussSumTwisted_def (a : ℤ) (c : ℕ) [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)]
    (m : dual L) : gaussSumTwisted L hL a c m = ∑ y, gaussTerm L hL a c m y :=
  (rfl)

theorem gaussSum_def (a : ℤ) (c : ℕ) [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] :
    gaussSum L hL a c = ∑ y, gaussTerm L hL a c 0 y :=
  (rfl)

/-- The twisted Gauss sum at `m = 0` is the Gauss sum. -/
@[simp]
theorem gaussSumTwisted_zero (a : ℤ) (c : ℕ) [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] :
    gaussSumTwisted L hL a c 0 = gaussSum L hL a c :=
  (rfl)

/-- The Gauss summand depends on `a` only modulo `c`, because `‖y‖² / 2 ∈ ℤ` on the even
lattice `L`. -/
theorem gaussTerm_eq_of_modEq {a a' : ℤ} {c : ℕ} (h : a ≡ a' [ZMOD c]) (m : dual L)
    (y : L ⧸ ((c : ℝ) • L).submoduleOf L) : gaussTerm L hL a c m y = gaussTerm L hL a' c m y := by
  induction y using Submodule.Quotient.induction_on with | H v
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  obtain ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp h.symm
  obtain ⟨j, hj⟩ := isEven_iff.mp hL _ v.2
  have hc' : (c : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hc
  -- Replacing `a'` by `a' + c t` changes the argument by the integer `t j`, as `‖v‖² = 2 j`.
  have harg : (((a' + c * t : ℤ) : ℝ) * ‖(v : E)‖ ^ 2 / 2 + ⟪(v : E), (m : E)⟫) / c =
      (a' * ‖(v : E)‖ ^ 2 / 2 + ⟪(v : E), (m : E)⟫) / c + ((t * j : ℤ) : ℝ) := by
    rw [hj]; push_cast; field_simp; ring
  rw [gaussTerm_mk, gaussTerm_mk, ht, harg, ofReal_add _ ((t * j : ℤ) : ℝ), ofReal_intCast,
    exp_two_pi_mul_I_mul_add_intCast]

/-- The twisted Gauss sums depend on `a` only modulo `c`. -/
theorem gaussSumTwisted_eq_of_modEq {a a' : ℤ} {c : ℕ} (h : a ≡ a' [ZMOD c])
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (m : dual L) :
    gaussSumTwisted L hL a c m = gaussSumTwisted L hL a' c m :=
  Finset.sum_congr rfl fun y _ => gaussTerm_eq_of_modEq hL h m y

/-- The Gauss sums depend on `a` only modulo `c`. -/
theorem gaussSum_eq_of_modEq {a a' : ℤ} {c : ℕ} (h : a ≡ a' [ZMOD c])
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] : gaussSum L hL a c = gaussSum L hL a' c :=
  gaussSumTwisted_eq_of_modEq hL h 0

/-- For `c = 1` the quotient `L / cL` is trivial and the twisted Gauss sum is `1`. -/
@[simp]
theorem gaussSumTwisted_one (a : ℤ) [Fintype (L ⧸ (((1 : ℕ) : ℝ) • L).submoduleOf L)]
    (m : dual L) : gaussSumTwisted L hL a 1 m = 1 := by
  have : Subsingleton (L ⧸ (((1 : ℕ) : ℝ) • L).submoduleOf L) :=
    Submodule.Quotient.subsingleton_iff.mpr <| eq_top_iff.mpr fun v _ =>
      mem_smul_submoduleOf_iff.mpr ⟨v, one_smul ℕ v⟩
  rw [gaussSumTwisted_def, Fintype.sum_subsingleton _ (Submodule.Quotient.mk 0), gaussTerm_mk]
  simp

/-- For `c = 1` the Gauss sum is `1`. -/
@[simp]
theorem gaussSum_one (a : ℤ) [Fintype (L ⧸ (((1 : ℕ) : ℝ) • L).submoduleOf L)] :
    gaussSum L hL a 1 = 1 :=
  gaussSumTwisted_one hL a 0

/-! ### Invariance under isometries -/

section Isometry

variable (e : F ≃ₗᵢ[ℝ] E) (hL' : IsEven (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap))
  (a : ℤ) (c : ℕ) [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)]
  [Fintype (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap ⧸
    ((c : ℝ) • ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap).submoduleOf
      (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap))]

/-- The twisted Gauss sums are invariant under linear isometry equivalences: pulling `L` back
along `e` and the twisting vector along with it does not change `G_L(a, c; m)`. -/
theorem gaussSumTwisted_comap {m' : dual (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap)}
    {m : dual L} (hm : (m : E) = e m') :
    gaussSumTwisted (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) hL' a c m' =
      gaussSumTwisted L hL a c m := by
  let φ := ZLattice.comap_equiv ℝ L e.toLinearEquiv
  have hφ : (((c : ℝ) • L).submoduleOf L).map (φ : L →ₗ[ℤ] _) =
      ((c : ℝ) • ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap).submoduleOf
        (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) := by
    ext x
    simp only [mem_map, mem_smul_submoduleOf_iff, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨φ w, (map_nsmul φ c w).symm⟩
    · rintro ⟨w, rfl⟩
      exact ⟨c • φ.symm w, ⟨φ.symm w, rfl⟩, by simp⟩
  refine (Fintype.sum_equiv (Submodule.Quotient.equiv _ _ φ hφ).toEquiv _ _ fun y => ?_).symm
  induction y using Submodule.Quotient.induction_on with | H v
  rw [LinearEquiv.coe_toEquiv, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply,
    gaussTerm_mk, gaussTerm_mk, LinearEquiv.coe_coe, ZLattice.comap_equiv_apply, hm]
  simp only [LinearIsometryEquiv.coe_symm_toLinearEquiv, LinearIsometryEquiv.norm_map]
  rw [← e.inner_map_map, e.apply_symm_apply]

/-- The Gauss sums are invariant under linear isometry equivalences. -/
theorem gaussSum_comap :
    gaussSum (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) hL' a c = gaussSum L hL a c :=
  gaussSumTwisted_comap hL e hL' a c (by simp)

end Isometry

/-! ### Vanishing and completing the square -/

/-- For `c` with `c ‖x‖² ∈ 2ℤ` for every `x ∈ L^∨` (for instance a multiple of the level of `L`),
the twisted Gauss sum `G_L(a, c; m)` vanishes unless `m ∈ L`. Indeed `c • L^∨ ≤ L`, and shifting
the summation variable by `c w`, `w ∈ L^∨`, multiplies the sum by `e(⟪w, m⟫)`; as `L = (L^∨)^∨`,
some `w ∈ L^∨` has `⟪w, m⟫ ∉ ℤ` when `m ∉ L`. -/
theorem gaussSumTwisted_eq_zero [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L]
    (a : ℤ) {c : ℕ} [NeZero c] [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)]
    (hc : ∀ x ∈ dual L, ∃ k : ℤ, (c : ℝ) * ‖x‖ ^ 2 = 2 * k) {m : dual L} (hm : (m : E) ∉ L) :
    gaussSumTwisted L hL a c m = 0 := by
  obtain ⟨w, hw, hwm⟩ : ∃ w ∈ dual L, ∀ k : ℤ, ⟪(m : E), w⟫ ≠ k := by
    by_contra! h
    exact hm ((dual_dual L).le (mem_dual.mpr h))
  let u : L := ⟨(c : ℝ) • w, smul_mem_of_mem_dual hc hw⟩
  -- Shifting by the class of `c w ∈ L` multiplies every term by `e(⟪m, w⟫)`.
  have hshift (y : L ⧸ ((c : ℝ) • L).submoduleOf L) :
      gaussTerm L hL a c m (y + Submodule.Quotient.mk u) =
        cexp (2 * π * I * (⟪(m : E), w⟫ : ℂ)) * gaussTerm L hL a c m y := by
    induction y using Submodule.Quotient.induction_on with | H v
    obtain ⟨i, hi⟩ := mem_dual.mp hw _ v.2
    obtain ⟨j, hj⟩ := hc w hw
    -- The argument changes by `⟪m, w⟫` plus the integer `a ⟪v, w⟫ + a c ‖w‖² / 2 = a i + a j`.
    have harg (x : ℝ) : x + (a * i + a * (2 * j) / 2 + ⟪(m : E), w⟫) =
        (x + ⟪(m : E), w⟫) + ((a * i + a * j : ℤ) : ℝ) := by
      push_cast; ring
    rw [← Submodule.Quotient.mk_add, gaussTerm_mk, gaussTerm_mk, coe_add,
      gaussArg_add_smul _ (Nat.cast_ne_zero.mpr (NeZero.ne c)), real_inner_comm w (v : E), hi, hj,
      real_inner_comm (m : E) w, harg, ofReal_add _ ((a * i + a * j : ℤ) : ℝ), ofReal_intCast,
      exp_two_pi_mul_I_mul_add_intCast, ofReal_add, mul_add, exp_add, mul_comm]
  have hne : cexp (2 * π * I * (⟪(m : E), w⟫ : ℂ)) ≠ 1 := by
    rw [Ne, exp_eq_one_iff]
    rintro ⟨k, hk⟩
    refine hwm k (ofReal_injective ?_)
    rw [ofReal_intCast]
    have : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    exact mul_left_cancel₀ this (hk.trans (mul_comm _ _))
  have h : gaussSumTwisted L hL a c m =
      cexp (2 * π * I * (⟪(m : E), w⟫ : ℂ)) * gaussSumTwisted L hL a c m := by
    rw [gaussSumTwisted_def, Finset.mul_sum,
      ← Equiv.sum_comp (Equiv.addRight (Submodule.Quotient.mk u)) (gaussTerm L hL a c m)]
    exact Finset.sum_congr rfl fun y _ => hshift y
  by_contra h0
  exact hne (mul_eq_right₀ h0 |>.mp h.symm)

/-- **Completing the square.** For `m ∈ L` and `a d ≡ 1 (mod c)`, the twisted Gauss sum is a
multiple of the untwisted one: `G_L(a, c; m) = e(-a d² ‖m‖² / (2c)) G_L(a, c)`. The shift
`y ↦ y + d m` turns `e(a ‖y‖² / (2c))` into `e(a d² ‖m‖² / (2c))` times the twisted summand. -/
theorem gaussSumTwisted_eq_of_mem {a d : ℤ} {c : ℕ} [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)]
    (had : a * d ≡ 1 [ZMOD c]) {m : dual L} (hm : (m : E) ∈ L) :
    gaussSumTwisted L hL a c m =
      cexp (-(2 * π * I * ((a * d ^ 2 * ‖(m : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ))) *
        gaussSum L hL a c := by
  let u : L := d • ⟨m, hm⟩
  have hterm (y : L ⧸ ((c : ℝ) • L).submoduleOf L) :
      gaussTerm L hL a c 0 (y + Submodule.Quotient.mk u) =
        cexp (2 * π * I * ((a * d ^ 2 * ‖(m : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) *
          gaussTerm L hL a c m y := by
    induction y using Submodule.Quotient.induction_on with | H v
    rw [← Submodule.Quotient.mk_add, gaussTerm_mk, gaussTerm_mk, ← exp_add, ← mul_add,
      ← ofReal_add]
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    obtain ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp had.symm
    obtain ⟨i, hi⟩ := mem_dual.mp m.2 _ v.2
    have hc' : (c : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hc
    have had' : (a : ℝ) * d = 1 + c * t := by exact_mod_cast ht
    have huv : ((v + u : L) : E) = v + (d : ℝ) • (m : E) := by
      simp [u, ← Int.cast_smul_eq_zsmul ℝ]
    have harg : (a * ‖(v : E) + (d : ℝ) • (m : E)‖ ^ 2 / 2) / c =
        a * d ^ 2 * ‖(m : E)‖ ^ 2 / (2 * c) + (a * ‖(v : E)‖ ^ 2 / 2 + ⟪(v : E), (m : E)⟫) / c +
          ((t * i : ℤ) : ℝ) := by
      rw [norm_add_sq_real, norm_smul, inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs,
        real_inner_comm, hi]
      push_cast
      field_simp
      linear_combination (2 * (i : ℝ)) * had'
    rw [huv, ZeroMemClass.coe_zero, inner_zero_right, add_zero, harg,
      ofReal_add _ ((t * i : ℤ) : ℝ), ofReal_intCast, exp_two_pi_mul_I_mul_add_intCast]
  have h : gaussSum L hL a c =
      cexp (2 * π * I * ((a * d ^ 2 * ‖(m : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) *
        gaussSumTwisted L hL a c m := by
    rw [gaussSum_def, gaussSumTwisted_def, Finset.mul_sum,
      ← Equiv.sum_comp (Equiv.addRight (Submodule.Quotient.mk u)) (gaussTerm L hL a c 0)]
    exact Finset.sum_congr rfl fun y _ => hterm y
  rw [h, ← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul]

end ZLattice
