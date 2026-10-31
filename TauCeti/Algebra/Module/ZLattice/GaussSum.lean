/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.FrickePartner
public import TauCeti.Algebra.Module.ZLattice.Quotient
public import TauCeti.Analysis.SpecialFunctions.Exp.Periodic
import TauCeti.GroupTheory.Coset.Fiber

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
For a full lattice of rank `n` and `c ≠ 0` the quotient is finite of order `c ^ n`
(`ZLattice.card_quotient_smul_submoduleOf`).

These sums are the arithmetic input to the transformation law of the theta series of an even
lattice under `Γ₀(N)`, where `N = ZLattice.level L` is the level of `L`: the least `N > 0` with
`N ‖x‖² ∈ 2ℤ` for every `x ∈ L^∨`. Splitting `L` into classes modulo `c` expresses the theta series
at a cusp `a / c` through the twisted Gauss sums, and two facts proved here reduce them to the
untwisted sum. For a multiple `c` of the level, `G_L(a, c; m)` vanishes unless `m ∈ L`, by the
shift `y ↦ y + c w`, `w ∈ L^∨`, which multiplies the sum by `e(⟪w, m⟫)`; and for `m ∈ L` and
`a d ≡ 1 (mod c)`, completing the square gives `G_L(a, c; m) = e(-a d² ‖m‖² / (2c)) G_L(a, c)`.

The reciprocity law for these sums exchanges the modulus and the coefficient and passes to the
dual lattice: its other side is the sum

`∑_{y ∈ L^∨ / cL} e(a ‖y‖² / (2c))`

over the classes of `L^∨` modulo `cL`, again well defined because `L` is even. For an integral
full lattice of rank `n` and `c ≠ 0` the quotient `L^∨ / cL` is finite with
`cⁿ |L^∨ / L| = cⁿ det L` elements (`ZLattice.IsIntegral.card_quotient_smul_submoduleOf_dual`).
When the coefficient is a multiple `N b` of the level, the summand is invariant under the larger
lattice `c L^∨`, and the scaling `y ↦ √N • y` turns the sum into `|L^∨ / L|` times the Gauss sum
`G_{√N • L^∨}(b, c)` of the Fricke partner `√N • L^∨`, which is again an even lattice.

## Main definitions

* `ZLattice.gaussTerm L hL a c m`: the summand `e(a ‖y‖² / (2c) + ⟪y, m⟫ / c)` on `L / cL`.
* `ZLattice.gaussSumTwisted L hL a c m`: the twisted Gauss sum `G_L(a, c; m)`.
* `ZLattice.gaussSum L hL a c`: the Gauss sum `G_L(a, c)`.
* `ZLattice.dualGaussTerm L hL a c`: the summand `e(a ‖y‖² / (2c))` on `L^∨ / cL`.
* `ZLattice.dualGaussSum L hL a c`: the Gauss sum `∑_{y ∈ L^∨ / cL} e(a ‖y‖² / (2c))`.

## Main statements

* `ZLattice.gaussSumTwisted_eq_of_modEq`, `ZLattice.gaussSum_eq_of_modEq`: the Gauss sums depend
  on `a` only modulo `c`.
* `ZLattice.gaussSumTwisted_one`, `ZLattice.gaussSum_one`: `G_L(a, 1; m) = G_L(a, 1) = 1`.
* `ZLattice.gaussSum_comap`: the Gauss sums are invariant under linear isometry equivalences.
* `ZLattice.gaussSumTwisted_orthSum`, `ZLattice.gaussSum_orthSum`: the Gauss sums are
  multiplicative under orthogonal direct sums, `G_{L ⊕ M}(a, c) = G_L(a, c) G_M(a, c)`.
* `ZLattice.gaussSumTwisted_eq_zero`: if the level of `L` divides `c`, then `G_L(a, c; m) = 0`
  for `m ∈ L^∨ \ L`.
* `ZLattice.gaussSumTwisted_eq_of_mem`: for `m ∈ L` and `a d ≡ 1 (mod c)`,
  `G_L(a, c; m) = e(-a d² ‖m‖² / (2c)) G_L(a, c)`.
* `ZLattice.dualGaussSum_level_mul`: for an even full lattice of level `N`,
  `∑_{y ∈ L^∨ / cL} e(N b ‖y‖² / (2c)) = |L^∨ / L| · G_{√N • L^∨}(b, c)`.

## References

* B. Schoeneberg, *Elliptic Modular Functions*, Springer, 1974, Chapter IX.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Springer, 1973, Appendix 4.
-/

public section

open Complex Module Submodule
open scoped Pointwise Real RealInnerProductSpace

namespace ZLattice

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

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

/-! ### Orthogonal direct sums -/

section OrthSum

variable {M : Submodule ℤ F} (hM : IsEven M) (a : ℤ) (c : ℕ)

variable [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] [Fintype (M ⧸ ((c : ℝ) • M).submoduleOf M)]
  [Fintype (orthSum L M ⧸ ((c : ℝ) • orthSum L M).submoduleOf (orthSum L M))]

/-- The twisted Gauss sums are multiplicative under orthogonal direct sums: for `m ∈ (L ⊕ M)^∨`
with components `m₁ ∈ L^∨` and `m₂ ∈ M^∨`, `G_{L ⊕ M}(a, c; m) = G_L(a, c; m₁) G_M(a, c; m₂)`. -/
theorem gaussSumTwisted_orthSum {m : dual (orthSum L M)} {m₁ : dual L} {m₂ : dual M}
    (hm : (m : WithLp 2 (E × F)) = WithLp.toLp 2 ((m₁ : E), (m₂ : F))) :
    gaussSumTwisted (orthSum L M) (isEven_orthSum_iff.mpr ⟨hL, hM⟩) a c m =
      gaussSumTwisted L hL a c m₁ * gaussSumTwisted M hM a c m₂ := by
  rw [gaussSumTwisted_def, gaussSumTwisted_def, gaussSumTwisted_def, Finset.sum_mul_sum,
    ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (quotientSmulOrthSumEquiv L M c).toEquiv _ _ fun y => ?_
  induction y using Submodule.Quotient.induction_on with | H x
  simp only [LinearEquiv.coe_toEquiv, quotientSmulOrthSumEquiv_mk, gaussTerm_mk,
    coe_orthSumEquivProd_apply_fst, coe_orthSumEquivProd_apply_snd, hm,
    WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd]
  rw [← exp_add]
  congr 1
  push_cast
  ring

/-- The Gauss sums are multiplicative under orthogonal direct sums:
`G_{L ⊕ M}(a, c) = G_L(a, c) G_M(a, c)`. -/
theorem gaussSum_orthSum :
    gaussSum (orthSum L M) (isEven_orthSum_iff.mpr ⟨hL, hM⟩) a c =
      gaussSum L hL a c * gaussSum M hM a c :=
  gaussSumTwisted_orthSum hL hM a c rfl

end OrthSum

/-! ### Vanishing and completing the square -/

/-- For a multiple `c` of the level of `L`, that is, `c ‖x‖² ∈ 2ℤ` for every `x ∈ L^∨`, the
twisted Gauss sum `G_L(a, c; m)` vanishes unless `m ∈ L`. Indeed `c • L^∨ ≤ L`, and shifting
the summation variable by `c w`, `w ∈ L^∨`, multiplies the sum by `e(⟪w, m⟫)`; as `L = (L^∨)^∨`,
some `w ∈ L^∨` has `⟪w, m⟫ ∉ ℤ` when `m ∉ L`. -/
theorem gaussSumTwisted_eq_zero [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L]
    (a : ℤ) {c : ℕ} [NeZero c] [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)]
    (hc : level L ∣ c) {m : dual L} (hm : (m : E) ∉ L) :
    gaussSumTwisted L hL a c m = 0 := by
  obtain ⟨w, hw, hwm⟩ : ∃ w ∈ dual L, ∀ k : ℤ, ⟪(m : E), w⟫ ≠ k := by
    by_contra! h
    exact hm ((dual_dual L).le (mem_dual.mpr h))
  have hcw : (c : ℝ) • w ∈ L := by
    obtain ⟨k, hk⟩ := hc
    rw [hk, Nat.cast_smul_eq_nsmul, mul_comm, mul_smul]
    exact L.nsmul_mem (level_nsmul_mem hw) k
  let u : L := ⟨(c : ℝ) • w, hcw⟩
  -- Shifting by the class of `c w ∈ L` multiplies every term by `e(⟪m, w⟫)`.
  have hshift (y : L ⧸ ((c : ℝ) • L).submoduleOf L) :
      gaussTerm L hL a c m (y + Submodule.Quotient.mk u) =
        cexp (2 * π * I * (⟪(m : E), w⟫ : ℂ)) * gaussTerm L hL a c m y := by
    induction y using Submodule.Quotient.induction_on with | H v
    obtain ⟨i, hi⟩ := mem_dual.mp hw _ v.2
    obtain ⟨j, hj⟩ := level_dvd_iff.mp hc w hw
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

/-! ### Gauss sums over `L^∨ / cL` -/

section DualGaussSum

variable (L) in
/-- The summand `e(a ‖y‖² / (2c))` of the Gauss sums of an even lattice `L` over `L^∨ / cL`, as a
function of the class `y`. It is well defined because `L` is even: replacing `y ∈ L^∨` by
`y + c w` with `w ∈ L` changes the argument of `e` by the integer `a ⟪y, w⟫ + a c ‖w‖² / 2`. -/
noncomputable def dualGaussTerm (hL : IsEven L) (a : ℤ) (c : ℕ)
    (y : dual L ⧸ ((c : ℝ) • L).submoduleOf (dual L)) : ℂ :=
  Quotient.liftOn' y (fun v : dual L => cexp (2 * π * I * ((a * ‖(v : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)))
    fun v₁ v₂ h => by
      rw [quotientRel_def, submoduleOf, Submodule.mem_comap, subtype_apply,
        mem_smul_pointwise_iff_exists] at h
      obtain ⟨w, hw, hvw⟩ := h
      have hv : (v₁ : E) = v₂ + (c : ℝ) • w := by rw [hvw, AddSubgroupClass.coe_sub]; abel
      rcases eq_or_ne c 0 with rfl | hc
      · simp
      obtain ⟨k, hk⟩ := mem_dual.mp v₂.2 w hw
      obtain ⟨j, hj⟩ := isEven_iff.mp hL w hw
      -- The argument changes by `a ⟪v₂, w⟫ + a c ‖w‖² / 2 = a k + a c j`, an integer.
      have harg : a * ‖(v₂ : E) + (c : ℝ) • w‖ ^ 2 / (2 * c) =
          a * ‖(v₂ : E)‖ ^ 2 / (2 * c) + ((a * k + a * c * j : ℤ) : ℝ) := by
        rw [norm_add_sq_real, norm_smul, inner_smul_right, hk, Real.norm_eq_abs, mul_pow, sq_abs,
          hj]
        push_cast
        field_simp
        ring
      rw [hv, harg, ofReal_add _ ((a * k + a * c * j : ℤ) : ℝ), ofReal_intCast,
        exp_two_pi_mul_I_mul_add_intCast]

/-- The dual Gauss summand of the class of `v ∈ L^∨` is `e(a ‖v‖² / (2c))`. -/
@[simp]
theorem dualGaussTerm_mk (a : ℤ) (c : ℕ) (v : dual L) :
    dualGaussTerm L hL a c (Submodule.Quotient.mk v) =
      cexp (2 * π * I * ((a * ‖(v : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) :=
  (rfl)

variable (L) in
/-- The Gauss sum `∑_{y ∈ L^∨ / cL} e(a ‖y‖² / (2c))` of an even lattice `L` over the classes of
its dual lattice modulo `cL`. For a full lattice of rank `n` and `c ≠ 0` the quotient is finite
of order `cⁿ |L^∨ / L|` (`ZLattice.IsIntegral.card_quotient_smul_submoduleOf_dual`). -/
noncomputable def dualGaussSum (hL : IsEven L) (a : ℤ) (c : ℕ)
    [Fintype (dual L ⧸ ((c : ℝ) • L).submoduleOf (dual L))] : ℂ :=
  ∑ y, dualGaussTerm L hL a c y

theorem dualGaussSum_def (a : ℤ) (c : ℕ) [Fintype (dual L ⧸ ((c : ℝ) • L).submoduleOf (dual L))] :
    dualGaussSum L hL a c = ∑ y, dualGaussTerm L hL a c y :=
  (rfl)

variable [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L]

/-- The descent to the Fricke partner `M = √N • L^∨`, with `M` kept abstract. The summand
`e(N b ‖y‖² / (2c))` is invariant under translation by `c L^∨`, the scaling `x ↦ √N • x` induces
a surjection `L^∨ / cL → M / cM` under which the summands correspond, and its fibres are copies
of `c L^∨ / cL ≅ L^∨ / L`. -/
private theorem dualGaussSum_level_mul_aux (b : ℤ) (c : ℕ)
    [Fintype (dual L ⧸ ((c : ℝ) • L).submoduleOf (dual L))] {M : Submodule ℤ E}
    (hM : M = √(level L : ℝ) • dual L) (hMe : IsEven M)
    [Fintype (M ⧸ ((c : ℝ) • M).submoduleOf M)] :
    dualGaussSum L hL (level L * b) c = Nat.card (DiscriminantGroup L) * gaussSum M hMe b c := by
  have hN : (0 : ℝ) < level L := Nat.cast_pos.mpr hL.isIntegral.level_pos
  have : NeZero √(level L : ℝ) := ⟨(Real.sqrt_pos.mpr hN).ne'⟩
  have : DiscreteTopology M := by subst hM; infer_instance
  have : IsZLattice ℝ M := by subst hM; infer_instance
  -- The scaling `L^∨ → M`, `x ↦ √N • x`, followed by the reduction modulo `cM`.
  let g : dual L →ₗ[ℤ] M := LinearMap.codRestrict M
    (DistribSMul.toLinearMap ℤ E √(level L : ℝ) ∘ₗ (dual L).subtype)
    fun x => hM ▸ smul_mem_pointwise_smul _ _ _ x.2
  -- `g` is a local definition, so its values are computed by unfolding it.
  have hg (x : dual L) : (g x : E) = √(level L : ℝ) • (x : E) := (rfl)
  let f₀ := (((c : ℝ) • M).submoduleOf M).mkQ ∘ₗ g
  have hle : ((c : ℝ) • L).submoduleOf (dual L) ≤ LinearMap.ker f₀ := by
    intro x hx
    rw [submoduleOf, Submodule.mem_comap, subtype_apply, mem_smul_pointwise_iff_exists] at hx
    obtain ⟨w, hw, hwx⟩ := hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, mkQ_apply, Submodule.Quotient.mk_eq_zero,
      submoduleOf, Submodule.mem_comap, subtype_apply, hg, ← hwx, smul_comm, hM]
    exact smul_mem_pointwise_smul _ _ _ <| smul_mem_pointwise_smul _ _ _ <|
      isIntegral_iff_le_dual.mp hL.isIntegral hw
  let f := (((c : ℝ) • L).submoduleOf (dual L)).liftQ f₀ hle
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨⟨m, hm⟩, rfl⟩ := mkQ_surjective _ z
    obtain ⟨x, hx, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp (hM ▸ hm)
    exact ⟨Submodule.Quotient.mk ⟨x, hx⟩, rfl⟩
  -- The kernel of `f` has `|L^∨ / L|` elements, by counting `L^∨ / cL` and `M / cM`.
  have hker : Nat.card f.toAddMonoidHom.ker = Nat.card (DiscriminantGroup L) := by
    have hcard := f.toAddMonoidHom.natCard_preimage_of_surjective hf Set.univ
    rw [Set.preimage_univ, Nat.card_univ, Nat.card_univ,
      hL.isIntegral.card_quotient_smul_submoduleOf_dual, card_quotient_smul_submoduleOf] at hcard
    have hpos : 0 < c ^ finrank ℝ E := card_quotient_smul_submoduleOf M c ▸ Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_left hpos hcard).symm
  have hterm (y : dual L ⧸ ((c : ℝ) • L).submoduleOf (dual L)) :
      dualGaussTerm L hL (level L * b) c y = gaussTerm M hMe b c 0 (f.toAddMonoidHom y) := by
    induction y using Submodule.Quotient.induction_on with | H v
    rw [LinearMap.toAddMonoidHom_coe, liftQ_apply, dualGaussTerm_mk, LinearMap.comp_apply,
      mkQ_apply, gaussTerm_mk, hg, ZeroMemClass.coe_zero, inner_zero_right, add_zero, norm_smul,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hN.le]
    push_cast
    ring_nf
  rw [dualGaussSum_def, gaussSum_def, Fintype.sum_congr _ _ hterm,
    AddMonoidHom.sum_comp_of_surjective f.toAddMonoidHom hf, hker, nsmul_eq_mul]

/-- **Descent to the Fricke partner.** Let `L` be an even full lattice of level `N`. For a
coefficient `N b` divisible by the level, the Gauss sum over `L^∨ / cL` is `|L^∨ / L|` times the
Gauss sum of the Fricke partner `√N • L^∨`:
`∑_{y ∈ L^∨ / cL} e(N b ‖y‖² / (2c)) = |L^∨ / L| · G_{√N • L^∨}(b, c)`.
Here `|L^∨ / L| = det L` (`ZLattice.IsIntegral.det_eq_card_discriminantGroup`), and the right
side is a sum over `L^∨ / c L^∨`, read on the scaled lattice `√N • L^∨`. -/
theorem dualGaussSum_level_mul (b : ℤ) (c : ℕ)
    [Fintype (dual L ⧸ ((c : ℝ) • L).submoduleOf (dual L))]
    [Fintype ((√(level L : ℝ) • dual L : Submodule ℤ E) ⧸
      ((c : ℝ) • (√(level L : ℝ) • dual L)).submoduleOf (√(level L : ℝ) • dual L))] :
    dualGaussSum L hL (level L * b) c =
      Nat.card (DiscriminantGroup L) *
        gaussSum (√(level L : ℝ) • dual L) (isEven_sqrt_level_smul_dual L) b c :=
  dualGaussSum_level_mul_aux hL b c rfl _

end DualGaussSum

end ZLattice
