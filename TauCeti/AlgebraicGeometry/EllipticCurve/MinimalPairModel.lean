/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.NormalForms
public import TauCeti.AlgebraicGeometry.EllipticCurve.ShortWeierstrass

import Mathlib.Algebra.CharP.Invertible
import Mathlib.Data.Int.Interval
import TauCeti.Data.Int.WeightedPrimitivePair
import TauCeti.Data.Rat.NumDenDvd

/-!
# The minimal-pair short equation of an elliptic curve over `ℚ`, and its naïve height

An elliptic curve `E` over `ℚ` has infinitely many short Weierstrass equations
`y² = x³ + Ax + B`: the scaling `x = u²x'`, `y = u³y'` replaces `(A, B)` by `(u⁻⁴A, u⁻⁶B)` for
every `u ∈ ℚˣ`. Among the equations with `A, B ∈ ℤ` exactly one is a **minimal pair**, meaning
that no prime `ℓ` has both `ℓ⁴ ∣ A` and `ℓ⁶ ∣ B`; the residual freedom `u = ±1` acts trivially
on it. This file constructs that equation, proves it unique, and defines the **naïve height** of
`E` as `max (4|A|³) (27B²)` computed from it. The height is the quantity by which tables of
elliptic curves over `ℚ` are ordered, and the bounded-height finiteness theorem is what makes
such a table finite.

## Main definitions

* `WeierstrassCurve.shortEquationHeight W`: `max (4|a₄|³) (27a₆²)` for a short equation `W`
  over `ℤ`. A property of the equation, not of the curve.
* `WeierstrassCurve.IsMinimalPairNF W`: `W` is short and `(a₄, a₆)` is a minimal pair.
* `WeierstrassCurve.MinimalPairModel E`: a minimal-pair equation over `ℤ` whose base change is
  isomorphic to `E`, with a chosen change of variables
  `WeierstrassCurve.MinimalPairModel.variableChange` realising the isomorphism, and
  `WeierstrassCurve.MinimalPairModel.height`, the height of its equation.
* `WeierstrassCurve.minimalPairModel E`: a chosen such model, and
  `WeierstrassCurve.naiveHeight E`, its height: the curve-level invariant.

## Main results

* `WeierstrassCurve.exists_minimalPairModel`: every elliptic curve over `ℚ` has a minimal-pair
  model.
* `WeierstrassCurve.minimalPairModel_unique`: any two minimal-pair models of `E` have the same
  equation, so `MinimalPairModel E` is a subsingleton. Hence `WeierstrassCurve.naiveHeight_eq`
  (every model computes the curve's height) and `WeierstrassCurve.naiveHeight_variableChange`
  (invariance under `ℚ`-isomorphism).
* `WeierstrassCurve.finite_shortEquations_bounded_height` and
  `WeierstrassCurve.finite_minimalPairEquations_bounded_height`: finitely many short equations
  over `ℤ`, in particular finitely many minimal-pair equations, have height at most `H`.
* `WeierstrassCurve.shortEquationHeight_le_of_natAbs_le` and
  `WeierstrassCurve.natAbs_Δ_le_mul_shortEquationHeight`: the height is monotone in `|a₄|` and
  `|a₆|`, and bounds the discriminant, `|Δ| ≤ 32 · H`.

## Design

* **The carrier is the content.** On short equations over `ℚ` the expression
  `max (4|A|³) (27B²)` is not an invariant: scaling by `u` divides it by `|u|¹²`, so one curve
  has rational short equations of arbitrarily small height and bounded-height finiteness fails.
  Pinning the equation to the minimal pair over `ℤ` is what makes the height well defined, which
  is why `shortEquationHeight` takes an equation over `ℤ` and only `naiveHeight` is curve-level.
* **A minimal pair is not a minimal Weierstrass equation.** At `2` and `3` the minimal-pair
  short equation need not be minimal in the sense of `WeierstrassCurve.IsMinimal`, and the
  globally minimal equation of a curve over `ℚ` is in general a long one. The two canonical
  equations serve different purposes, and neither replaces the other.
* **The equation is the only data.** A `MinimalPairModel` records the equation and the existence
  of an isomorphism to `E`, not a particular change of variables: that is unique only up to the
  automorphisms of `E`, and composing it with `[-1]` gives another. `minimalPairModel_unique`
  makes the type a subsingleton, and `MinimalPairModel.variableChange` recovers a witness when a
  computation needs one.
* The naïve height on *points*, `WeierstrassCurve.Affine.Point.naiveHeight`, is a different
  quantity on a different type.

## References

* J. S. Balakrishnan, W. Ho, N. Kaplan, S. Spicer, W. Stein, J. Weigandt, *Databases of elliptic
  curves ordered by height and distributions of Selmer groups and ranks*, LMS J. Comput. Math.
  19 (2016), 351–370: the minimal-pair convention and the height computed from it.
* LMFDB knowl `ec.q.naive_height`.

## Provenance

`naiveHeight` is adapted from LeanBridge (`github.com/CBirkbeck/LeanBridge`, Apache-2.0), file
`LeanBridge/ForMathlib/4-EC.lean` at `JaneShi99/LeanBridge@d84dd305` (branch
`formalize/ec-defs`), by Jane Shi, where it is the `ℚ`-valued expression `max (4|a₄|³) (27a₆²)`
on any short equation over `ℚ`. Here it is `ℕ`-valued and pinned to the minimal-pair equation
over `ℤ`; the minimal-pair normal form, the bundled model, and the existence, uniqueness and
finiteness theorems are new.
-/

public section

namespace WeierstrassCurve

/-! ### The height of an integral short equation -/

/-- **The height of a short Weierstrass equation** `y² = x³ + a₄x + a₆` over `ℤ`:
`max (4|a₄|³) (27a₆²)`. The formula is stated for every Weierstrass equation over `ℤ`, but it is
the height of the equation only when the equation is short, which is how it is used. It is a
function of the equation, not of the curve it defines: over `ℚ`, the scaling `x = u²x'`,
`y = u³y'` sends `(a₄, a₆)` to `(u⁻⁴a₄, u⁻⁶a₆)` and divides the same expression by `|u|¹²`. It
becomes an invariant of the curve once the equation is pinned to the minimal pair, which is
`naiveHeight`. -/
def shortEquationHeight (W : WeierstrassCurve ℤ) : ℕ :=
  max (4 * W.a₄.natAbs ^ 3) (27 * W.a₆.natAbs ^ 2)

section Height

variable (W : WeierstrassCurve ℤ)

/-- `shortEquationHeight`, unfolded. This is the interface to
`WeierstrassCurve.shortEquationHeight` outside its defining module. -/
@[simp]
theorem shortEquationHeight_def :
    shortEquationHeight W = max (4 * W.a₄.natAbs ^ 3) (27 * W.a₆.natAbs ^ 2) :=
  (rfl)

/-- The height of a short equation bounds `|a₄|`. -/
theorem natAbs_a₄_le_shortEquationHeight : W.a₄.natAbs ≤ shortEquationHeight W := by
  have := Nat.le_self_pow three_ne_zero W.a₄.natAbs
  rw [shortEquationHeight_def]
  omega

/-- The height of a short equation bounds `|a₆|`. -/
theorem natAbs_a₆_le_shortEquationHeight : W.a₆.natAbs ≤ shortEquationHeight W := by
  have := Nat.le_self_pow two_ne_zero W.a₆.natAbs
  rw [shortEquationHeight_def]
  omega

/-- The height of a short equation is monotone in `|a₄|` and `|a₆|`. -/
theorem shortEquationHeight_le_of_natAbs_le {W' : WeierstrassCurve ℤ}
    (h₄ : W.a₄.natAbs ≤ W'.a₄.natAbs) (h₆ : W.a₆.natAbs ≤ W'.a₆.natAbs) :
    shortEquationHeight W ≤ shortEquationHeight W' := by
  rw [shortEquationHeight_def, shortEquationHeight_def]
  gcongr

/-- **The height of a short equation bounds its discriminant**: `Δ = -16(4a₄³ + 27a₆²)` has
`|Δ| ≤ 32 · max (4|a₄|³) (27a₆²)`. -/
theorem natAbs_Δ_le_mul_shortEquationHeight [W.IsShortNF] :
    W.Δ.natAbs ≤ 32 * shortEquationHeight W := by
  have h := Int.natAbs_add_le (4 * W.a₄ ^ 3) (27 * W.a₆ ^ 2)
  rw [Δ_of_isShortNF, shortEquationHeight_def]
  norm_num [Int.natAbs_mul, Int.natAbs_pow] at h ⊢
  omega

end Height

/-! ### The minimal-pair normal form -/

/-- **The minimal-pair normal form** of an integral short equation: `W` is short, and no prime
`ℓ` has both `ℓ⁴ ∣ a₄` and `ℓ⁶ ∣ a₆`. This is the condition that kills the scaling freedom
`(a₄, a₆) ↦ (u⁴a₄, u⁶a₆)` of short equations over `ℤ`, so that the equation, and with it
`shortEquationHeight`, is determined by the curve (`minimalPairModel_unique`). It is a condition
on the pair `(a₄, a₆)`, not minimality of the Weierstrass equation in the sense of
`WeierstrassCurve.IsMinimal`: at `2` and `3` the two notions differ. -/
def IsMinimalPairNF (W : WeierstrassCurve ℤ) : Prop :=
  W.IsShortNF ∧ ∀ ℓ : ℕ, ℓ.Prime → ¬ ((ℓ : ℤ) ^ 4 ∣ W.a₄ ∧ (ℓ : ℤ) ^ 6 ∣ W.a₆)

section MinimalPair

variable {W : WeierstrassCurve ℤ}

/-- The minimal-pair normal form, unfolded. This is the interface to
`WeierstrassCurve.IsMinimalPairNF` outside its defining module. -/
@[simp]
theorem isMinimalPairNF_iff :
    IsMinimalPairNF W ↔
      W.IsShortNF ∧ ∀ ℓ : ℕ, ℓ.Prime → ¬ ((ℓ : ℤ) ^ 4 ∣ W.a₄ ∧ (ℓ : ℤ) ^ 6 ∣ W.a₆) :=
  Iff.rfl

/-- A minimal-pair equation is short. -/
theorem IsMinimalPairNF.isShortNF (h : IsMinimalPairNF W) : W.IsShortNF := h.1

/-- No prime `ℓ` has both `ℓ⁴ ∣ a₄` and `ℓ⁶ ∣ a₆` for a minimal-pair equation. -/
theorem IsMinimalPairNF.not_dvd_and_dvd (h : IsMinimalPairNF W) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ¬ ((ℓ : ℤ) ^ 4 ∣ W.a₄ ∧ (ℓ : ℤ) ^ 6 ∣ W.a₆) :=
  h.2 ℓ hℓ

/-- A short equation over `ℤ` such that no prime `ℓ` has both `ℓ⁴ ∣ a₄` and `ℓ⁶ ∣ a₆` is in
minimal-pair normal form. -/
theorem IsMinimalPairNF.of_forall_not_dvd [W.IsShortNF]
    (h : ∀ ℓ : ℕ, ℓ.Prime → ¬ ((ℓ : ℤ) ^ 4 ∣ W.a₄ ∧ (ℓ : ℤ) ^ 6 ∣ W.a₆)) :
    IsMinimalPairNF W :=
  ⟨inferInstance, h⟩

/-- **The only integers `x` with `x⁴ ∣ a₄` and `x⁶ ∣ a₆` for a minimal pair are `±1`.** This is
the form in which the minimal-pair condition is consumed: it rules out every scaling of the
equation but the sign. -/
theorem IsMinimalPairNF.isUnit_of_pow_dvd (h : IsMinimalPairNF W) {x : ℤ} (h₄ : x ^ 4 ∣ W.a₄)
    (h₆ : x ^ 6 ∣ W.a₆) : IsUnit x := by
  rw [Int.isUnit_iff_natAbs_eq]
  by_contra hx
  obtain ⟨ℓ, hℓ, hℓx⟩ := Nat.exists_prime_and_dvd hx
  have hℓx' : (ℓ : ℤ) ∣ x := Int.natCast_dvd.mpr hℓx
  exact h.not_dvd_and_dvd hℓ
    ⟨(pow_dvd_pow_of_dvd hℓx' 4).trans h₄, (pow_dvd_pow_of_dvd hℓx' 6).trans h₆⟩

/-- **Two minimal-pair equations related by a rational scaling coincide.** If
`(a₄', a₆') = (q⁴a₄, q⁶a₆)` for some `q ∈ ℚ` and both pairs are minimal, then `q = ±1` and the
equations are equal. -/
theorem IsMinimalPairNF.eq_of_intCast_eq_pow_mul {W' : WeierstrassCurve ℤ}
    (hW : IsMinimalPairNF W) (hW' : IsMinimalPairNF W') {q : ℚ}
    (h₄ : (W'.a₄ : ℚ) = q ^ 4 * W.a₄) (h₆ : (W'.a₆ : ℚ) = q ^ 6 * W.a₆) : W' = W := by
  -- `q.den⁴ ∣ a₄` and `q.den⁶ ∣ a₆` force `q.den = 1`; `q.num⁴ ∣ a₄'` and `q.num⁶ ∣ a₆'` force
  -- `q.num = ±1`. So `q = ±1`, `q⁴ = q⁶ = 1`, and the coefficients agree.
  have hden : q.den = 1 := by
    have h := hW.isUnit_of_pow_dvd (x := q.den)
      (by simpa [Rat.den_pow] using (q ^ 4).den_dvd_of_intCast_eq_mul_intCast h₄)
      (by simpa [Rat.den_pow] using (q ^ 6).den_dvd_of_intCast_eq_mul_intCast h₆)
    simpa using Int.isUnit_iff_natAbs_eq.mp h
  have hnum : q.num = 1 ∨ q.num = -1 :=
    Int.isUnit_iff.mp (hW'.isUnit_of_pow_dvd
      (by simpa [Rat.num_pow] using (q ^ 4).num_dvd_of_intCast_eq_mul_intCast h₄)
      (by simpa [Rat.num_pow] using (q ^ 6).num_dvd_of_intCast_eq_mul_intCast h₆))
  have hq : q = 1 ∨ q = -1 := by
    rw [← Rat.coe_int_num_of_den_eq_one hden]
    rcases hnum with h | h <;> simp [h]
  have hq4 : q ^ 4 = 1 := by rcases hq with rfl | rfl <;> norm_num
  have hq6 : q ^ 6 = 1 := by rcases hq with rfl | rfl <;> norm_num
  rw [hq4, one_mul, Int.cast_inj] at h₄
  rw [hq6, one_mul, Int.cast_inj] at h₆
  have := hW.isShortNF
  have := hW'.isShortNF
  ext <;> simp [h₄, h₆]

end MinimalPair

/-! ### Bundled minimal-pair models -/

/-- **A minimal-pair model of an elliptic curve `E` over `ℚ`**: a minimal-pair short equation
over `ℤ` whose base change is isomorphic to `E` over `ℚ`. The equation is unique
(`minimalPairModel_unique`), so the type is a subsingleton. A change of variables realising the
isomorphism is available as `MinimalPairModel.variableChange`; it is not part of the data, since
it is unique only up to the automorphisms of `E`. -/
@[ext]
structure MinimalPairModel (E : WeierstrassCurve ℚ) [E.IsElliptic] where
  /-- The integral short equation. -/
  model : WeierstrassCurve ℤ
  /-- It is short and a minimal pair. -/
  isMinimalPair : IsMinimalPairNF model
  /-- Some change of variables carries the base-changed model to `E`. -/
  isomorphic : ∃ C : VariableChange ℚ, C • (model.baseChange ℚ) = E

namespace MinimalPairModel

variable {E : WeierstrassCurve ℚ} [E.IsElliptic] (M : MinimalPairModel E)

/-- A change of variables carrying the base change of the model to `E`, chosen from
`MinimalPairModel.isomorphic`. It is not unique: composing it with an automorphism of `E` gives
another. -/
noncomputable def variableChange : VariableChange ℚ :=
  M.isomorphic.choose

/-- The chosen change of variables carries the base change of the model to `E`. -/
@[simp]
theorem variableChange_smul_baseChange : M.variableChange • M.model.baseChange ℚ = E :=
  M.isomorphic.choose_spec

/-- The base change of a minimal-pair model is an elliptic curve, being isomorphic to `E`. -/
instance isElliptic_baseChange_model : (M.model.baseChange ℚ).IsElliptic := by
  rw [← inv_smul_smul M.variableChange (M.model.baseChange ℚ), M.variableChange_smul_baseChange]
  infer_instance

/-- **The height of a minimal-pair model**: the `shortEquationHeight` of its equation. -/
def height : ℕ :=
  shortEquationHeight M.model

/-- `MinimalPairModel.height`, unfolded. This is the interface to
`WeierstrassCurve.MinimalPairModel.height` outside its defining module. -/
@[simp]
theorem height_def : M.height = max (4 * M.model.a₄.natAbs ^ 3) (27 * M.model.a₆.natAbs ^ 2) :=
  (rfl)

/-- The height of a minimal-pair model depends only on its equation. -/
theorem height_eq_of_model_eq {N : MinimalPairModel E} (h : M.model = N.model) :
    M.height = N.height := by
  rw [height_def, height_def, h]

end MinimalPairModel

/-! ### Existence -/

/-- **Existence of a minimal-pair model**: every elliptic curve over `ℚ` is isomorphic over `ℚ`
to the base change of a minimal-pair short equation over `ℤ`. -/
theorem exists_minimalPairModel (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Nonempty (MinimalPairModel E) := by
  -- Take a short equation `C • E` over `ℚ` and a common denominator `d` of `a₄` and `a₆`, so that
  -- `(d⁴a₄, d⁶a₆)` is a pair of integers; strip every prime `ℓ` with `ℓ⁴ ∣ A` and `ℓ⁶ ∣ B` from
  -- it, writing `(d⁴a₄, d⁶a₆) = (e⁴A', e⁶B')`. The scaling by `u = d / e` then carries
  -- `y² = x³ + A'x + B'` back to `C • E`.
  obtain ⟨C, hC⟩ := E.exists_variableChange_isShortNF
  obtain ⟨⟨d, hdmem⟩, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors ℤ)
    ({(C • E).a₄, (C • E).a₆} : Finset ℚ)
  have hd' : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (nonZeroDivisors.ne_zero hdmem)
  obtain ⟨A₀, hA₀⟩ := hd _ (Finset.mem_insert_self _ _)
  obtain ⟨B₀, hB₀⟩ := hd _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  simp only [eq_intCast, zsmul_eq_mul] at hA₀ hB₀
  have hA₁ : (d : ℚ) ^ 4 * (C • E).a₄ = ((d ^ 3 * A₀ : ℤ) : ℚ) := by
    push_cast
    linear_combination (-(d : ℚ) ^ 3) * hA₀
  have hB₁ : (d : ℚ) ^ 6 * (C • E).a₆ = ((d ^ 5 * B₀ : ℤ) : ℚ) := by
    push_cast
    linear_combination (-(d : ℚ) ^ 5) * hB₀
  generalize d ^ 3 * A₀ = A₂ at hA₁
  generalize d ^ 5 * B₀ = B₂ at hB₁
  have hne : A₂ ≠ 0 ∨ B₂ ≠ 0 := by
    -- Otherwise `a₄ = a₆ = 0` for `C • E`, whose discriminant `-16(4a₄³ + 27a₆²)` would vanish.
    by_contra h
    push Not at h
    have ha₄ : (C • E).a₄ = 0 :=
      (mul_eq_zero.mp (hA₁.trans (by rw [h.1, Int.cast_zero]))).resolve_left (pow_ne_zero 4 hd')
    have ha₆ : (C • E).a₆ = 0 :=
      (mul_eq_zero.mp (hB₁.trans (by rw [h.2, Int.cast_zero]))).resolve_left (pow_ne_zero 6 hd')
    exact (C • E).isUnit_Δ.ne_zero (by rw [Δ_of_isShortNF, ha₄, ha₆]; norm_num)
  obtain ⟨e, A, B, he, hA, hB, hmin⟩ :=
    A₂.exists_eq_pow_mul_and_forall_prime_not_pow_dvd_of_ne_zero B₂ (m := 4) (n := 6)
      (by norm_num) (by norm_num) hne
  have he' : (e : ℚ) ≠ 0 := Int.cast_ne_zero.mpr he
  have hA' : (A₂ : ℚ) = (e : ℚ) ^ 4 * A := by exact_mod_cast hA
  have hB' : (B₂ : ℚ) = (e : ℚ) ^ 6 * B := by exact_mod_cast hB
  let u : ℚˣ := Units.mk0 ((d : ℚ) / e) (div_ne_zero hd' he')
  have key : (⟨u, 0, 0, 0⟩ : VariableChange ℚ) • (shortCurve A B).baseChange ℚ = C • E := by
    rw [baseChange_shortCurve, smul_shortCurve, ← shortCurve_a₄_a₆ (C • E)]
    simp only [u, Units.val_inv_eq_inv_val, Units.val_mk0, eq_intCast, inv_div, div_pow,
      div_mul_eq_mul_div]
    congr 1
    · rw [div_eq_iff (pow_ne_zero 4 hd')]
      linear_combination -hA₁ - hA'
    · rw [div_eq_iff (pow_ne_zero 6 hd')]
      linear_combination -hB₁ - hB'
  exact ⟨⟨shortCurve A B, .of_forall_not_dvd (by simpa using hmin), C⁻¹ * ⟨u, 0, 0, 0⟩,
    by rw [mul_smul, key, inv_smul_smul]⟩⟩

/-- **A chosen minimal-pair model** of an elliptic curve over `ℚ`. Its equation and its height
do not depend on the choice (`minimalPairModel_unique`, `naiveHeight_eq`). -/
noncomputable def minimalPairModel (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    MinimalPairModel E :=
  Classical.choice (exists_minimalPairModel E)

/-! ### Uniqueness, and the naïve height of a curve -/

/-- **Uniqueness of the minimal-pair equation**: any two minimal-pair models of `E` have the same
equation, not merely isomorphic ones. Together with existence, this makes the height of the
equation an invariant of the curve. -/
theorem minimalPairModel_unique (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (M N : MinimalPairModel E) : M.model = N.model := by
  -- With `CM • M.model = E = CN • N.model` over `ℚ`, the change of variables `CN⁻¹ * CM` carries
  -- `M.model` to `N.model`. Between short equations it scales `(a₄, a₆)` by `(q⁴, q⁶)` for
  -- `q = u⁻¹`, and a rational scaling between two minimal pairs is trivial.
  have := M.isMinimalPair.isShortNF
  have := N.isMinimalPair.isShortNF
  obtain ⟨CM, hM⟩ := M.isomorphic
  obtain ⟨CN, hN⟩ := N.isomorphic
  have hD : (CN⁻¹ * CM) • M.model.baseChange ℚ = N.model.baseChange ℚ := by
    rw [mul_smul, hM]
    exact inv_smul_eq_iff.mpr hN.symm
  have : ((CN⁻¹ * CM) • M.model.baseChange ℚ).IsShortNF := by
    rw [hD]
    infer_instance
  have h₄ := variableChange_a₄_of_isShortNF (M.model.baseChange ℚ) (CN⁻¹ * CM)
    (isRegular_iff_ne_zero.mpr two_ne_zero) (isRegular_iff_ne_zero.mpr three_ne_zero)
  have h₆ := variableChange_a₆_of_isShortNF (M.model.baseChange ℚ) (CN⁻¹ * CM)
    (isRegular_iff_ne_zero.mpr two_ne_zero) (isRegular_iff_ne_zero.mpr three_ne_zero)
  rw [hD] at h₄ h₆
  simp only [baseChange, map_a₄, map_a₆, eq_intCast] at h₄ h₆
  exact (M.isMinimalPair.eq_of_intCast_eq_pow_mul N.isMinimalPair h₄ h₆).symm

/-- Minimal-pair models of `E` form a subsingleton: their only data is the equation, and that is
unique. -/
instance MinimalPairModel.instSubsingleton (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Subsingleton (MinimalPairModel E) :=
  ⟨fun M N => MinimalPairModel.ext (minimalPairModel_unique E M N)⟩

/-- **The naïve height of an elliptic curve over `ℚ`**: the height `max (4|A|³) (27B²)` of its
minimal-pair equation `y² = x³ + Ax + B`. It can be computed from any minimal-pair model
(`naiveHeight_eq`), is invariant under `ℚ`-isomorphism (`naiveHeight_variableChange`), and is the
quantity by which tables of elliptic curves over `ℚ` are ordered. -/
noncomputable def naiveHeight (E : WeierstrassCurve ℚ) [E.IsElliptic] : ℕ :=
  (minimalPairModel E).height

/-- Every minimal-pair model computes the naïve height of the curve. -/
theorem naiveHeight_eq {E : WeierstrassCurve ℚ} [E.IsElliptic] (M : MinimalPairModel E) :
    naiveHeight E = M.height :=
  (minimalPairModel E).height_eq_of_model_eq (minimalPairModel_unique E _ M)

/-- The naïve height is invariant under an admissible change of variables over `ℚ`. -/
theorem naiveHeight_variableChange (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (C : VariableChange ℚ) : naiveHeight (C • E) = naiveHeight E := by
  -- The chosen model of `E`, with its change of variables composed with `C`, is a model of
  -- `C • E` with the same equation.
  rw [naiveHeight_eq (E := C • E) ⟨(minimalPairModel E).model, (minimalPairModel E).isMinimalPair,
    C * (minimalPairModel E).variableChange,
    by rw [mul_smul, (minimalPairModel E).variableChange_smul_baseChange]⟩,
    naiveHeight_eq (minimalPairModel E), MinimalPairModel.height_def,
    MinimalPairModel.height_def]

/-! ### Finiteness -/

/-- **There are only finitely many short equations over `ℤ` of bounded height**: the bound
`max (4|a₄|³) (27a₆²) ≤ H` leaves `|a₄|, |a₆| ≤ H`, and the two coefficients determine a short
equation. -/
theorem finite_shortEquations_bounded_height (H : ℕ) :
    Set.Finite {W : WeierstrassCurve ℤ |
      W.IsShortNF ∧ max (4 * W.a₄.natAbs ^ 3) (27 * W.a₆.natAbs ^ 2) ≤ H} := by
  -- Such an equation is `shortCurve A B` with `|A|, |B| ≤ H`, and there are finitely many pairs.
  refine (((Set.finite_Icc (-(H : ℤ)) H).prod (Set.finite_Icc (-(H : ℤ)) H)).image
    fun p : ℤ × ℤ => shortCurve p.1 p.2).subset ?_
  rintro W ⟨hW, hH⟩
  rw [← shortEquationHeight_def] at hH
  have h₄ := W.natAbs_a₄_le_shortEquationHeight.trans hH
  have h₆ := W.natAbs_a₆_le_shortEquationHeight.trans hH
  refine ⟨(W.a₄, W.a₆), ?_, W.shortCurve_a₄_a₆⟩
  simp only [Set.mem_prod, Set.mem_Icc]
  omega

/-- **There are only finitely many minimal-pair short equations of bounded height.** The
statement is about equations over `ℤ` in minimal-pair normal form: the set of all rational
equations of a single curve is infinite, so finiteness of bounded-height `ℚ`-isomorphism classes
is a consequence of this statement, not a statement about terms `E : WeierstrassCurve ℚ`. -/
theorem finite_minimalPairEquations_bounded_height (H : ℕ) :
    Set.Finite {W : WeierstrassCurve ℤ |
      IsMinimalPairNF W ∧ (W.baseChange ℚ).IsElliptic ∧
        max (4 * W.a₄.natAbs ^ 3) (27 * W.a₆.natAbs ^ 2) ≤ H} :=
  (finite_shortEquations_bounded_height H).subset fun _ ⟨hW, _, hH⟩ => ⟨hW.isShortNF, hH⟩

end WeierstrassCurve

end
