/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Complex.Order

/-!
# Heisenberg data, vacua and multipliers

Let `W` be an abelian topological group. A *Heisenberg datum* on `W` is a continuous function
`β : W → W → ℂ`, multiplicative in each variable, with values of modulus one and `β x x = 1`: the
commutator pairing of a Heisenberg group over `W`. A *representation* of `β` on a complex normed
space `X` is a jointly continuous family of linear isometries `ϱ x` with
`ϱ x (ϱ y v) = β x y • ϱ (x + y) v`.

For a measure `μ` on `W`, a *vacuum* is a continuous, integrable, even, real-valued function `e`
with `e 0 = 1` that satisfies the twisted convolution identity
`∫ e z * β z y * β (z + y) x * e (x - (z + y)) dμ(z) = e y * e x`. It plays the part of the matrix
coefficient of a vacuum vector: a Gaussian at the real places, or a twisted lattice indicator at
the finite places. A vacuum has `L²` norm one and is bounded by one.

A group `G` acting on `W` by automorphisms that preserve `β` and `μ` carries *multipliers*:
continuous functions `Δ : G → ℂ` with `Δ 1 = 1` and `Δ g⁻¹ = conj (Δ g)`. The *cocycle* of `Δ`
for a vacuum `e` is the scalar
`c g h = Δ g * Δ h * Δ (g * h)⁻¹ * ∫∫ e (h • x) * e ((g * h) • y) * β x y * e (x + y)`, which
measures the failure of the Weil operators of `Δ` to multiply
(`TauCeti.ReproducingModel.weilOp_inv_mul_weilOp_mul_weilOp`).

## Main definitions

* `TauCeti.HeisenbergDatum W`: a Heisenberg datum on `W`.
* `TauCeti.HeisenbergDatum.Representation β X`: a representation of `β` on `X`.
* `TauCeti.HeisenbergDatum.IsVacuum β μ e`: `e` is a vacuum for `β` and `μ`.
* `TauCeti.HeisenbergDatum.Multiplier β μ G`: a multiplier for an action of `G` that preserves `β`
  and `μ`, and `TauCeti.HeisenbergDatum.Multiplier.cocycle`, its cocycle for a vacuum.

## Main results

* `TauCeti.HeisenbergDatum.IsVacuum.integral_norm_sq_eq_one`,
  `TauCeti.HeisenbergDatum.IsVacuum.norm_le_one`: a vacuum has `L²` norm one and modulus at most
  one.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
Anthropic, PBC), file `src/Lib/Weil/Construction/HeisenbergModel.lean`
(`New.Heisenberg`, `New.Heisenberg.Rep`, `New.Heisenberg.IsVacuum`,
`New.Heisenberg.MultiplierAction`, `New.Heisenberg.IsVacuum.integral_norm_sq_eq_one`,
`New.Heisenberg.IsVacuum.norm_le_one`). Here the cocycle is a function of the multiplier rather
than a parameter of the action, and the vacuum class takes its measure and function as ordinary
arguments.

## References

* A. Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964), 143–211.
* S. Kudla, *Notes on the local theta correspondence*, lectures at the European School in Group
  Theory (1996).
-/

public section

open MeasureTheory
open scoped ComplexConjugate

namespace TauCeti

/-- A *Heisenberg datum* on an abelian topological group `W`: a continuous function
`β : W → W → ℂ`, multiplicative in each variable, with values of modulus one and `β x x = 1`. -/
structure HeisenbergDatum (W : Type*) [AddCommGroup W] [TopologicalSpace W] where
  /-- The pairing `β x y`. -/
  toFun : W → W → ℂ
  map_add_left' (x x' y : W) : toFun (x + x') y = toFun x y * toFun x' y
  map_add_right' (x y y' : W) : toFun x (y + y') = toFun x y * toFun x y'
  apply_self' (x : W) : toFun x x = 1
  norm_apply' (x y : W) : ‖toFun x y‖ = 1
  continuous_uncurry' : Continuous fun p : W × W ↦ toFun p.1 p.2

namespace HeisenbergDatum

variable {W : Type*} [AddCommGroup W] [TopologicalSpace W]

instance : FunLike (HeisenbergDatum W) W (W → ℂ) where
  coe := toFun
  coe_injective β β' h := by cases β; cases β'; congr

variable (β : HeisenbergDatum W) (x x' y y' : W)

@[ext]
theorem ext {β β' : HeisenbergDatum W} (h : ∀ x y, β x y = β' x y) : β = β' :=
  DFunLike.ext _ _ fun x ↦ funext (h x)

@[simp]
theorem toFun_eq_coe : β.toFun = β := rfl

theorem map_add_left : β (x + x') y = β x y * β x' y := β.map_add_left' x x' y

theorem map_add_right : β x (y + y') = β x y * β x y' := β.map_add_right' x y y'

@[simp]
theorem apply_self : β x x = 1 := β.apply_self' x

@[simp]
theorem norm_apply : ‖β x y‖ = 1 := β.norm_apply' x y

theorem continuous_uncurry : Continuous fun p : W × W ↦ β p.1 p.2 := β.continuous_uncurry'

@[simp]
theorem enorm_apply : ‖β x y‖ₑ = 1 := by
  rw [← ofReal_norm, β.norm_apply, ENNReal.ofReal_one]

@[fun_prop]
theorem continuous_apply_apply {α : Type*} [TopologicalSpace α] {f g : α → W} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun a ↦ β (f a) (g a) :=
  β.continuous_uncurry.comp (hf.prodMk hg)

@[simp]
theorem apply_ne_zero : β x y ≠ 0 := by simp [← norm_pos_iff]

@[simp]
theorem zero_apply : β 0 y = 1 := by simpa using β.map_add_left 0 0 y

/-- A Heisenberg datum is alternating: `β x y * β y x = 1`. -/
@[simp]
theorem apply_mul_apply_swap : β x y * β y x = 1 := by
  have h := β.apply_self (x + y)
  rwa [map_add_left, map_add_right, map_add_right, apply_self, apply_self, one_mul, mul_one] at h

@[simp]
theorem apply_zero : β y 0 = 1 := by simpa using β.apply_mul_apply_swap 0 y

@[simp]
theorem neg_apply : β (-x) y = β y x := by
  have h : β x y * β (-x) y = 1 := by rw [← map_add_left, add_neg_cancel, zero_apply]
  exact inv_unique h (β.apply_mul_apply_swap x y)

@[simp]
theorem apply_neg : β x (-y) = β y x := by rw [← neg_apply, neg_neg]

theorem map_sub_right : β x (y - y') = β x y * β y' x := by
  rw [sub_eq_add_neg, map_add_right, apply_neg]

theorem map_sub_left : β (x - x') y = β x y * β y x' := by
  rw [sub_eq_add_neg, map_add_left, neg_apply]

@[simp]
theorem conj_apply : conj (β x y) = β y x := by
  rw [← Complex.inv_eq_conj (β.norm_apply x y)]
  exact inv_eq_of_mul_eq_one_right (β.apply_mul_apply_swap x y)

/-- A *representation* of a Heisenberg datum `β` on a complex normed space `X`: linear isometries
`ϱ x`, jointly continuous in `(x, v)`, with `ϱ x (ϱ y v) = β x y • ϱ (x + y) v`. -/
structure Representation (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] where
  /-- The operator `ϱ x`. -/
  toFun : W → X →L[ℂ] X
  apply_apply' (x y : W) (v : X) : toFun x (toFun y v) = β x y • toFun (x + y) v
  norm_apply' (x : W) (v : X) : ‖toFun x v‖ = ‖v‖
  continuous_uncurry' : Continuous fun p : W × X ↦ toFun p.1 p.2

namespace Representation

variable {β} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (ϱ : β.Representation X)
  (v : X)

instance : CoeFun (β.Representation X) fun _ ↦ W → X →L[ℂ] X := ⟨toFun⟩

theorem apply_apply : ϱ x (ϱ y v) = β x y • ϱ (x + y) v := ϱ.apply_apply' x y v

@[simp]
theorem norm_apply : ‖ϱ x v‖ = ‖v‖ := ϱ.norm_apply' x v

theorem continuous_uncurry : Continuous fun p : W × X ↦ ϱ p.1 p.2 := ϱ.continuous_uncurry'

@[fun_prop]
theorem continuous_apply_apply {α : Type*} [TopologicalSpace α] {f : α → W} {g : α → X}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a ↦ ϱ (f a) (g a) :=
  ϱ.continuous_uncurry.comp (hf.prodMk hg)

@[simp]
theorem zero_apply : ϱ 0 v = v := by
  have h : ϱ 0 (ϱ 0 v) = ϱ 0 v := by rw [apply_apply, β.zero_apply, one_smul, add_zero]
  rw [← sub_eq_zero, ← norm_eq_zero, ← ϱ.norm_apply 0, map_sub, h, sub_self, norm_zero]

@[simp]
theorem apply_neg_apply : ϱ x (ϱ (-x) v) = v := by simp [apply_apply]

end Representation

/-- A *vacuum* for a Heisenberg datum `β` and a measure `μ`: a continuous, integrable, even,
real-valued function `e` with `e 0 = 1` and the twisted convolution identity
`∫ e z * (β z y * (β (z + y) x * e (x - (z + y)))) dμ(z) = e y * e x`. -/
class IsVacuum [MeasurableSpace W] (μ : Measure W) (e : W → ℂ) : Prop where
  continuous : Continuous e
  integrable : Integrable e μ
  apply_zero : e 0 = 1
  apply_neg (x : W) : e (-x) = e x
  conj_apply (x : W) : conj (e x) = e x
  integral_mul_apply (y x : W) :
    ∫ z : W, e z * (β z y * (β (z + y) x * e (x - (z + y)))) ∂μ = e y * e x

namespace IsVacuum

variable {β} [MeasurableSpace W] {μ : Measure W} {e : W → ℂ}

/-- A vacuum has `L²` norm one. -/
theorem integral_norm_sq_eq_one (he : β.IsVacuum μ e) : ∫ x : W, ‖e x‖ ^ 2 ∂μ = 1 := by
  have h_conv : ∫ z : W, e z * e z ∂μ = 1 := by
    simpa [he.apply_zero, he.apply_neg] using he.integral_mul_apply 0 0
  have h_sq (z : W) : e z * e z = (‖e z‖ : ℂ) ^ 2 := by
    rw [← Complex.mul_conj', he.conj_apply]
  rw [← Complex.ofReal_inj, ← integral_complex_ofReal]
  simpa [← h_sq] using h_conv

/-- A vacuum has modulus at most one. -/
theorem norm_le_one (he : β.IsVacuum μ e) (x : W) : ‖e x‖ ≤ 1 := by
  have h_norm (z : W) :
      ‖e z * (β z x * (β (z + x) x * e (x - (z + x))))‖ = ‖e z‖ ^ 2 := by
    simp [he.apply_neg, sq]
  refine (sq_le_one_iff₀ (norm_nonneg _)).1 ?_
  calc ‖e x‖ ^ 2 = ‖∫ z : W, e z * (β z x * (β (z + x) x * e (x - (z + x)))) ∂μ‖ := by
        rw [he.integral_mul_apply, norm_mul, sq]
    _ ≤ ∫ z : W, ‖e z * (β z x * (β (z + x) x * e (x - (z + x))))‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = 1 := by simpa only [h_norm] using he.integral_norm_sq_eq_one

/-- The reproducing kernel `β y x * e (x - y)` of a vacuum has modulus at most one. -/
theorem norm_kernel_le_one (he : β.IsVacuum μ e) (x y : W) : ‖β y x * e (x - y)‖ ≤ 1 := by
  simpa using he.norm_le_one (x - y)

end IsVacuum

/-- A *multiplier* for an action of a topological group `G` on `W` by automorphisms that preserve
the Heisenberg datum `β` and the measure `μ`: a continuous `Δ : G → ℂ` with `Δ 1 = 1` and
`Δ g⁻¹ = conj (Δ g)`. The preservation of `β` and `μ` by the action is part of the data. -/
structure Multiplier [MeasurableSpace W] (μ : Measure W) (G : Type*) [Group G]
    [TopologicalSpace G] [DistribMulAction G W] where
  /-- The multiplier `Δ g`. -/
  toFun : G → ℂ
  apply_smul_smul (g : G) (x y : W) : β (g • x) (g • y) = β x y
  measurePreserving_smul (g : G) : MeasurePreserving (g • · : W → W) μ μ
  continuous_toFun : Continuous toFun
  map_one' : toFun 1 = 1
  map_inv' (g : G) : toFun g⁻¹ = conj (toFun g)

namespace Multiplier

variable {β} [MeasurableSpace W] {μ : Measure W} {G : Type*} [Group G] [TopologicalSpace G]
  [DistribMulAction G W] (Δ : β.Multiplier μ G)

instance : CoeFun (β.Multiplier μ G) fun _ ↦ G → ℂ := ⟨toFun⟩

@[fun_prop]
theorem continuous : Continuous Δ := Δ.continuous_toFun

@[simp]
theorem map_one : Δ 1 = 1 := Δ.map_one'

theorem map_inv (g : G) : Δ g⁻¹ = conj (Δ g) := Δ.map_inv' g

/-- The *cocycle* of the multiplier `Δ` for a function `e` on `W`:
`c g h = Δ g * Δ h * Δ (g * h)⁻¹ * ∫∫ e (h • x) * e ((g * h) • y) * β x y * e (x + y)`. -/
noncomputable def cocycle (e : W → ℂ) (g h : G) : ℂ :=
  Δ g * Δ h * Δ (g * h)⁻¹ *
    ∫ x : W, ∫ y : W, e (h • x) * e ((g * h) • y) * β x y * e (x + y) ∂μ ∂μ

theorem cocycle_def (e : W → ℂ) (g h : G) : Δ.cocycle e g h = Δ g * Δ h * Δ (g * h)⁻¹ *
    ∫ x : W, ∫ y : W, e (h • x) * e ((g * h) • y) * β x y * e (x + y) ∂μ ∂μ := (rfl)

end Multiplier

end HeisenbergDatum

end TauCeti
