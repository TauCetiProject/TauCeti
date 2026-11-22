/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.Normed.Ring.WithAbs
import Mathlib.Algebra.CharP.Algebra

/-!
# Metric and uniform properties of rings with an absolute value

A scalar action on a ring `A` that commutes with right multiplication,
`m • (x * y) = (m • x) * y` (`IsScalarTower M A A`), such as the algebra action of a commutative
semiring, induces a uniformly continuous action on `WithAbs v` for every fixed scalar. This lets
the scalar action extend to the completion; Mathlib's corresponding instance covers only algebra
actions of a commutative ring on a field.

In addition, a ring isomorphism `σ : R ≃+* T` that intertwines real absolute values `v` on `R` and
`w` on `T` (`w (σ x) = v x`) induces an isometry `WithAbs.congr v w σ : WithAbs v ≃+* WithAbs w`
(`WithAbs.isometry_congr`), bundled as `WithAbs.isometryEquivCongr : WithAbs v ≃ᵢ WithAbs w`.

`WithAbs v` also inherits `CharP` and `CharZero` from its base semiring, and equipping a ring
without zero divisors with `AbsoluteValue.trivial` gives a complete ultrametric normed ring whose
nonzero elements all have norm `1`.
-/

public section

namespace WithAbs

section SMul

variable {M A : Type*} [Ring A] [SMul M A] [IsScalarTower M A A]

/-- A scalar action on a ring with an absolute value that commutes with right multiplication, such
as an algebra action, is uniformly continuous in its argument. -/
instance (priority := 100) uniformContinuousConstSMul (v : AbsoluteValue A ℝ) :
    UniformContinuousConstSMul M (WithAbs v) where
  -- An action commuting with right multiplication is left multiplication by `m • 1`.
  uniformContinuous_const_smul m := by
    simpa only [smul_eq_mul, smul_one_mul] using
      uniformContinuous_const_smul (X := WithAbs v) (m • 1 : WithAbs v)

end SMul

section Congr

variable {R T U : Type*} [Ring R] [Ring T] [Ring U]
  {v : AbsoluteValue R ℝ} {w : AbsoluteValue T ℝ} {u : AbsoluteValue U ℝ}

/-- A ring isomorphism carrying the real absolute value `v` to `w` is an isometry from `WithAbs v`
to `WithAbs w`. -/
theorem isometry_congr (σ : R ≃+* T) (hσ : ∀ x, w (σ x) = v x) :
    Isometry (WithAbs.congr v w σ) :=
  AddMonoidHomClass.isometry_of_norm _ fun x ↦ by
    rw [norm_eq_apply_ofAbs, norm_eq_apply_ofAbs, congr_apply, ofAbs_toAbs, hσ]

/-- A ring isomorphism carrying the real absolute value `v` to `w`, bundled as an isometric
equivalence `WithAbs v ≃ᵢ WithAbs w`. -/
noncomputable def isometryEquivCongr (σ : R ≃+* T) (hσ : ∀ x, w (σ x) = v x) :
    WithAbs v ≃ᵢ WithAbs w where
  toEquiv := (WithAbs.congr v w σ).toEquiv
  isometry_toFun := isometry_congr σ hσ

/-- The underlying map of `isometryEquivCongr σ hσ` is `WithAbs.congr v w σ`. -/
@[simp]
theorem coe_isometryEquivCongr (σ : R ≃+* T) (hσ : ∀ x, w (σ x) = v x) :
    ⇑(isometryEquivCongr σ hσ) = WithAbs.congr v w σ :=
  (rfl)

/-- The bijection underlying `isometryEquivCongr σ hσ` is `(WithAbs.congr v w σ).toEquiv`. -/
@[simp]
theorem toEquiv_isometryEquivCongr (σ : R ≃+* T) (hσ : ∀ x, w (σ x) = v x) :
    (isometryEquivCongr σ hσ).toEquiv = (WithAbs.congr v w σ).toEquiv :=
  (rfl)

/-- `WithAbs.isometryEquivCongr` of the identity is the identity. -/
@[simp]
theorem isometryEquivCongr_refl (h : ∀ x, v (RingEquiv.refl R x) = v x := fun _ ↦ rfl) :
    isometryEquivCongr (RingEquiv.refl R) h = IsometryEquiv.refl (WithAbs v) :=
  IsometryEquiv.ext fun _ ↦ rfl

/-- `WithAbs.isometryEquivCongr` is compatible with composition of ring isomorphisms. -/
@[simp]
theorem isometryEquivCongr_trans (σ : R ≃+* T) (hσ : ∀ x, w (σ x) = v x)
    (τ : T ≃+* U) (hτ : ∀ y, u (τ y) = w y) :
    (isometryEquivCongr σ hσ).trans (isometryEquivCongr τ hτ) =
      isometryEquivCongr (σ.trans τ) (fun x ↦ by rw [RingEquiv.trans_apply, hτ, hσ]) :=
  IsometryEquiv.ext fun _ ↦ rfl

/-- The inverse of `isometryEquivCongr σ hσ` is `isometryEquivCongr` of `σ.symm`. -/
@[simp]
theorem isometryEquivCongr_symm (σ : R ≃+* T) (hσ : ∀ x, w (σ x) = v x) :
    (isometryEquivCongr σ hσ).symm =
      isometryEquivCongr σ.symm (fun y ↦ by rw [← hσ, σ.apply_symm_apply]) :=
  IsometryEquiv.ext fun _ ↦ rfl

end Congr

section Char

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (v : AbsoluteValue R S)

/-- `WithAbs v` inherits the characteristic of `R`. -/
instance instCharP (p : ℕ) [CharP R p] : CharP (WithAbs v) p :=
  charP_of_injective_ringHom (f := (equiv v).symm.toRingHom) (equiv v).symm.injective p

/-- `WithAbs v` inherits characteristic zero from `R`. -/
instance instCharZero [CharZero R] : CharZero (WithAbs v) :=
  charZero_of_injective_ringHom (f := (equiv v).symm.toRingHom) (equiv v).symm.injective

end Char

section Trivial

variable {R : Type*} [Ring R] [DecidablePred fun x : R ↦ x = 0] [NoZeroDivisors R]

/-- Every nonzero element of `WithAbs AbsoluteValue.trivial` has norm `1`. -/
@[simp]
theorem norm_trivial_eq_one {x : WithAbs (AbsoluteValue.trivial : AbsoluteValue R ℝ)}
    (hx : x ≠ 0) : ‖x‖ = 1 := by
  rw [norm_eq_apply_ofAbs, AbsoluteValue.trivial_apply (by simpa using hx)]

/-- Every element of `WithAbs AbsoluteValue.trivial` has norm at most `1`. -/
theorem norm_trivial_le_one (x : WithAbs (AbsoluteValue.trivial : AbsoluteValue R ℝ)) :
    ‖x‖ ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp [hx]

/-- The norm induced by `AbsoluteValue.trivial` is ultrametric. -/
instance instIsUltrametricDistTrivial :
    IsUltrametricDist (WithAbs (AbsoluteValue.trivial : AbsoluteValue R ℝ)) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact le_max_of_le_left ((norm_trivial_le_one (x + y)).trans_eq (norm_trivial_eq_one hx).symm)

/-- `WithAbs AbsoluteValue.trivial` is complete because distinct points have distance `1`. -/
instance instCompleteSpaceTrivial :
    CompleteSpace (WithAbs (AbsoluteValue.trivial : AbsoluteValue R ℝ)) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (1 / 2) (by positivity)
  refine ⟨u N, tendsto_atTop_of_eventually_const (i₀ := N) fun n hn ↦ ?_⟩
  by_contra hne
  have hd : dist (u n) (u N) = 1 := by
    rw [dist_eq_norm, norm_trivial_eq_one (sub_ne_zero.mpr hne)]
  linarith [hN n hn N le_rfl]

end Trivial

end WithAbs
