/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Quaternion
public import TauCeti.Algebra.Central.Quaternion
public import TauCeti.Analysis.Calculus.FDeriv.Remainder

/-!
# One-sided quotient derivatives of quaternionic functions

A function `f : ℍ → ℍ` has *left quotient derivative* (or *left slope*) `b` at `q` when
`h⁻¹ * (f (q + h) - f q) → b` as `h → 0`, and *right quotient derivative* `a` at `q` when
`(f (q + h) - f q) * h⁻¹ → a`. Since `ℍ` is not commutative these are different notions, and
neither is the real Fréchet derivative: a left slope `b` means that the real derivative of `f` at
`q` is right multiplication `h ↦ h * b`, and a right slope `a` means that it is left
multiplication `h ↦ a * h`.

We take the Fréchet form as the definition and prove the limit characterisations as theorems.
The order of multiplication is part of every statement.

## Main declarations

* `TauCeti.HasLeftQuotientFDerivAt f q b`: the real derivative of `f` at `q` is `h ↦ h * b`.
* `TauCeti.HasRightQuotientFDerivAt f q a`: the real derivative of `f` at `q` is `h ↦ a * h`.
* `TauCeti.LeftQuotientDifferentiableAt`, `TauCeti.LeftQuotientDifferentiableOn` and their right
  counterparts: some slope exists at the point, respectively at every point of the set.
* `TauCeti.HasLeftQuotientFDerivAt.unique`: a left slope is unique, and likewise on the right.
* `TauCeti.LeftQuotientDifferentiableAt.hasLeftQuotientFDerivAt` and its right counterpart: when a
  slope exists, it is `fderiv ℝ f q 1`.
* `TauCeti.hasLeftQuotientFDerivAt_iff_tendsto_inv_mul` and
  `TauCeti.hasRightQuotientFDerivAt_iff_tendsto_mul_inv`: the quotient limits
  `h⁻¹ * (f (q + h) - f q) → b` and `(f (q + h) - f q) * h⁻¹ → a` along `𝓝[≠] 0`.
* `TauCeti.hasLeftQuotientFDerivAt_iff_tendsto_norm_div` and its right counterpart: the
  remainder form `‖f (q + h) - f q - h * b‖ / ‖h‖ → 0`.
* `TauCeti.HasLeftQuotientFDerivAt.eq_of_hasRightQuotientFDerivAt` and
  `TauCeti.HasLeftQuotientFDerivAt.im_eq_zero_of_hasRightQuotientFDerivAt`: a left and a right
  slope at the same point coincide and are real.
* `TauCeti.not_hasLeftQuotientFDerivAt_const_mul`: for nonreal `a`, the map `x ↦ a * x` has no
  left slope at any point, although it has right slope `a` everywhere; dually for `x ↦ x * b`.

## References

* O. Dzagnidze, *On the differentiability of quaternion functions*, arXiv:1203.5619v1, §1, p. 2,
  for the two one-sided quotient limits.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. **85** (1979),
  199–225, Theorem 1 and the one-sided quaternion derivatives it concerns.
* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. **218** (2008), §2.1 (arXiv:0711.2699v5), for the multiplicative norm used in the
  remainder estimates.
-/

public section

open Filter Topology
open scoped Quaternion

namespace TauCeti

variable {f g : ℍ → ℍ} {q a b c : ℍ}

/-! ### Definitions -/

/-- `f` has *left quotient derivative* `b` at `q`: the real Fréchet derivative of `f` at `q` is
right multiplication `h ↦ h * b`. Equivalently `h⁻¹ * (f (q + h) - f q) → b` as `h → 0`, see
`TauCeti.hasLeftQuotientFDerivAt_iff_tendsto_inv_mul`. -/
def HasLeftQuotientFDerivAt (f : ℍ → ℍ) (q b : ℍ) : Prop :=
  HasFDerivAt f ((ContinuousLinearMap.mul ℝ ℍ).flip b) q

/-- `f` has *right quotient derivative* `a` at `q`: the real Fréchet derivative of `f` at `q` is
left multiplication `h ↦ a * h`. Equivalently `(f (q + h) - f q) * h⁻¹ → a` as `h → 0`, see
`TauCeti.hasRightQuotientFDerivAt_iff_tendsto_mul_inv`. -/
def HasRightQuotientFDerivAt (f : ℍ → ℍ) (q a : ℍ) : Prop :=
  HasFDerivAt f (ContinuousLinearMap.mul ℝ ℍ a) q

/-- `f` is *left quotient differentiable* at `q` when it has some left quotient derivative there. -/
def LeftQuotientDifferentiableAt (f : ℍ → ℍ) (q : ℍ) : Prop :=
  ∃ b, HasLeftQuotientFDerivAt f q b

/-- `f` is *right quotient differentiable* at `q` when it has some right quotient derivative
there. -/
def RightQuotientDifferentiableAt (f : ℍ → ℍ) (q : ℍ) : Prop :=
  ∃ a, HasRightQuotientFDerivAt f q a

/-- `f` is *left quotient differentiable* on `s` when it is left quotient differentiable at every
point of `s`. -/
def LeftQuotientDifferentiableOn (f : ℍ → ℍ) (s : Set ℍ) : Prop :=
  ∀ q ∈ s, LeftQuotientDifferentiableAt f q

/-- `f` is *right quotient differentiable* on `s` when it is right quotient differentiable at every
point of `s`. -/
def RightQuotientDifferentiableOn (f : ℍ → ℍ) (s : Set ℍ) : Prop :=
  ∀ q ∈ s, RightQuotientDifferentiableAt f q

theorem hasLeftQuotientFDerivAt_iff_hasFDerivAt :
    HasLeftQuotientFDerivAt f q b ↔ HasFDerivAt f ((ContinuousLinearMap.mul ℝ ℍ).flip b) q :=
  Iff.rfl

theorem hasRightQuotientFDerivAt_iff_hasFDerivAt :
    HasRightQuotientFDerivAt f q a ↔ HasFDerivAt f (ContinuousLinearMap.mul ℝ ℍ a) q :=
  Iff.rfl

theorem leftQuotientDifferentiableAt_iff :
    LeftQuotientDifferentiableAt f q ↔ ∃ b, HasLeftQuotientFDerivAt f q b :=
  Iff.rfl

theorem rightQuotientDifferentiableAt_iff :
    RightQuotientDifferentiableAt f q ↔ ∃ a, HasRightQuotientFDerivAt f q a :=
  Iff.rfl

theorem leftQuotientDifferentiableOn_iff {s : Set ℍ} :
    LeftQuotientDifferentiableOn f s ↔ ∀ q ∈ s, LeftQuotientDifferentiableAt f q :=
  Iff.rfl

theorem rightQuotientDifferentiableOn_iff {s : Set ℍ} :
    RightQuotientDifferentiableOn f s ↔ ∀ q ∈ s, RightQuotientDifferentiableAt f q :=
  Iff.rfl

/-! ### Relation with the real derivative -/

namespace HasLeftQuotientFDerivAt

theorem hasFDerivAt (hf : HasLeftQuotientFDerivAt f q b) :
    HasFDerivAt f ((ContinuousLinearMap.mul ℝ ℍ).flip b) q :=
  hf

theorem differentiableAt (hf : HasLeftQuotientFDerivAt f q b) : DifferentiableAt ℝ f q :=
  hf.hasFDerivAt.differentiableAt

theorem leftQuotientDifferentiableAt (hf : HasLeftQuotientFDerivAt f q b) :
    LeftQuotientDifferentiableAt f q :=
  ⟨b, hf⟩

theorem fderiv (hf : HasLeftQuotientFDerivAt f q b) :
    fderiv ℝ f q = (ContinuousLinearMap.mul ℝ ℍ).flip b :=
  hf.hasFDerivAt.fderiv

theorem fderiv_apply (hf : HasLeftQuotientFDerivAt f q b) (h : ℍ) :
    _root_.fderiv ℝ f q h = h * b := by
  simp [hf.fderiv]

/-- A left quotient derivative is unique: it is the value of the real derivative at `1`. -/
theorem unique (hb : HasLeftQuotientFDerivAt f q b) (hc : HasLeftQuotientFDerivAt f q c) :
    b = c := by
  simpa using DFunLike.congr_fun (hb.hasFDerivAt.unique hc.hasFDerivAt) 1

/-- A left slope depends only on the germ of the function at the point. -/
theorem congr_of_eventuallyEq (hf : HasLeftQuotientFDerivAt f q b) (h : g =ᶠ[𝓝 q] f) :
    HasLeftQuotientFDerivAt g q b :=
  hf.hasFDerivAt.congr_of_eventuallyEq h

end HasLeftQuotientFDerivAt

namespace HasRightQuotientFDerivAt

theorem hasFDerivAt (hf : HasRightQuotientFDerivAt f q a) :
    HasFDerivAt f (ContinuousLinearMap.mul ℝ ℍ a) q :=
  hf

theorem differentiableAt (hf : HasRightQuotientFDerivAt f q a) : DifferentiableAt ℝ f q :=
  hf.hasFDerivAt.differentiableAt

theorem rightQuotientDifferentiableAt (hf : HasRightQuotientFDerivAt f q a) :
    RightQuotientDifferentiableAt f q :=
  ⟨a, hf⟩

theorem fderiv (hf : HasRightQuotientFDerivAt f q a) :
    fderiv ℝ f q = ContinuousLinearMap.mul ℝ ℍ a :=
  hf.hasFDerivAt.fderiv

theorem fderiv_apply (hf : HasRightQuotientFDerivAt f q a) (h : ℍ) :
    _root_.fderiv ℝ f q h = a * h := by
  simp [hf.fderiv]

/-- A right quotient derivative is unique: it is the value of the real derivative at `1`. -/
theorem unique (ha : HasRightQuotientFDerivAt f q a) (hc : HasRightQuotientFDerivAt f q c) :
    a = c := by
  simpa using DFunLike.congr_fun (ha.hasFDerivAt.unique hc.hasFDerivAt) 1

/-- A right slope depends only on the germ of the function at the point. -/
theorem congr_of_eventuallyEq (hf : HasRightQuotientFDerivAt f q a) (h : g =ᶠ[𝓝 q] f) :
    HasRightQuotientFDerivAt g q a :=
  hf.hasFDerivAt.congr_of_eventuallyEq h

end HasRightQuotientFDerivAt

theorem LeftQuotientDifferentiableAt.differentiableAt (hf : LeftQuotientDifferentiableAt f q) :
    DifferentiableAt ℝ f q :=
  hf.elim fun _ hb ↦ hb.differentiableAt

theorem RightQuotientDifferentiableAt.differentiableAt (hf : RightQuotientDifferentiableAt f q) :
    DifferentiableAt ℝ f q :=
  hf.elim fun _ ha ↦ ha.differentiableAt

/-- If `f` has some left slope at `q`, then that slope is `fderiv ℝ f q 1`. -/
theorem LeftQuotientDifferentiableAt.hasLeftQuotientFDerivAt
    (hf : LeftQuotientDifferentiableAt f q) : HasLeftQuotientFDerivAt f q (fderiv ℝ f q 1) := by
  obtain ⟨b, hb⟩ := hf
  rwa [hb.fderiv_apply, one_mul]

/-- If `f` has some right slope at `q`, then that slope is `fderiv ℝ f q 1`. -/
theorem RightQuotientDifferentiableAt.hasRightQuotientFDerivAt
    (hf : RightQuotientDifferentiableAt f q) : HasRightQuotientFDerivAt f q (fderiv ℝ f q 1) := by
  obtain ⟨a, ha⟩ := hf
  rwa [ha.fderiv_apply, mul_one]

theorem leftQuotientDifferentiableAt_iff_hasLeftQuotientFDerivAt_fderiv :
    LeftQuotientDifferentiableAt f q ↔ HasLeftQuotientFDerivAt f q (fderiv ℝ f q 1) :=
  ⟨LeftQuotientDifferentiableAt.hasLeftQuotientFDerivAt,
    HasLeftQuotientFDerivAt.leftQuotientDifferentiableAt⟩

theorem rightQuotientDifferentiableAt_iff_hasRightQuotientFDerivAt_fderiv :
    RightQuotientDifferentiableAt f q ↔ HasRightQuotientFDerivAt f q (fderiv ℝ f q 1) :=
  ⟨RightQuotientDifferentiableAt.hasRightQuotientFDerivAt,
    HasRightQuotientFDerivAt.rightQuotientDifferentiableAt⟩

theorem LeftQuotientDifferentiableOn.mono {s t : Set ℍ} (hf : LeftQuotientDifferentiableOn f t)
    (hst : s ⊆ t) : LeftQuotientDifferentiableOn f s :=
  fun q hq ↦ hf q (hst hq)

theorem RightQuotientDifferentiableOn.mono {s t : Set ℍ} (hf : RightQuotientDifferentiableOn f t)
    (hst : s ⊆ t) : RightQuotientDifferentiableOn f s :=
  fun q hq ↦ hf q (hst hq)

theorem LeftQuotientDifferentiableOn.differentiableOn {s : Set ℍ}
    (hf : LeftQuotientDifferentiableOn f s) : DifferentiableOn ℝ f s :=
  fun q hq ↦ (hf q hq).differentiableAt.differentiableWithinAt

theorem RightQuotientDifferentiableOn.differentiableOn {s : Set ℍ}
    (hf : RightQuotientDifferentiableOn f s) : DifferentiableOn ℝ f s :=
  fun q hq ↦ (hf q hq).differentiableAt.differentiableWithinAt

/-! ### Linear combinations and elementary examples -/

namespace HasLeftQuotientFDerivAt

theorem add (hf : HasLeftQuotientFDerivAt f q b) (hg : HasLeftQuotientFDerivAt g q c) :
    HasLeftQuotientFDerivAt (fun x ↦ f x + g x) q (b + c) := by
  rw [hasLeftQuotientFDerivAt_iff_hasFDerivAt, map_add]
  exact hf.hasFDerivAt.add hg.hasFDerivAt

theorem sub (hf : HasLeftQuotientFDerivAt f q b) (hg : HasLeftQuotientFDerivAt g q c) :
    HasLeftQuotientFDerivAt (fun x ↦ f x - g x) q (b - c) := by
  rw [hasLeftQuotientFDerivAt_iff_hasFDerivAt, map_sub]
  exact hf.hasFDerivAt.sub hg.hasFDerivAt

theorem neg (hf : HasLeftQuotientFDerivAt f q b) :
    HasLeftQuotientFDerivAt (fun x ↦ -f x) q (-b) := by
  rw [hasLeftQuotientFDerivAt_iff_hasFDerivAt, map_neg]
  exact hf.hasFDerivAt.neg

theorem const_smul (hf : HasLeftQuotientFDerivAt f q b) (r : ℝ) :
    HasLeftQuotientFDerivAt (fun x ↦ r • f x) q (r • b) := by
  rw [hasLeftQuotientFDerivAt_iff_hasFDerivAt, map_smul]
  exact hf.hasFDerivAt.const_smul r

theorem const_add (hf : HasLeftQuotientFDerivAt f q b) (a : ℍ) :
    HasLeftQuotientFDerivAt (fun x ↦ a + f x) q b :=
  hf.hasFDerivAt.const_add a

theorem add_const (hf : HasLeftQuotientFDerivAt f q b) (a : ℍ) :
    HasLeftQuotientFDerivAt (fun x ↦ f x + a) q b :=
  hf.hasFDerivAt.add_const a

end HasLeftQuotientFDerivAt

namespace HasRightQuotientFDerivAt

theorem add (hf : HasRightQuotientFDerivAt f q a) (hg : HasRightQuotientFDerivAt g q c) :
    HasRightQuotientFDerivAt (fun x ↦ f x + g x) q (a + c) := by
  rw [hasRightQuotientFDerivAt_iff_hasFDerivAt, map_add]
  exact hf.hasFDerivAt.add hg.hasFDerivAt

theorem sub (hf : HasRightQuotientFDerivAt f q a) (hg : HasRightQuotientFDerivAt g q c) :
    HasRightQuotientFDerivAt (fun x ↦ f x - g x) q (a - c) := by
  rw [hasRightQuotientFDerivAt_iff_hasFDerivAt, map_sub]
  exact hf.hasFDerivAt.sub hg.hasFDerivAt

theorem neg (hf : HasRightQuotientFDerivAt f q a) :
    HasRightQuotientFDerivAt (fun x ↦ -f x) q (-a) := by
  rw [hasRightQuotientFDerivAt_iff_hasFDerivAt, map_neg]
  exact hf.hasFDerivAt.neg

theorem const_smul (hf : HasRightQuotientFDerivAt f q a) (r : ℝ) :
    HasRightQuotientFDerivAt (fun x ↦ r • f x) q (r • a) := by
  rw [hasRightQuotientFDerivAt_iff_hasFDerivAt, map_smul]
  exact hf.hasFDerivAt.const_smul r

theorem const_add (hf : HasRightQuotientFDerivAt f q a) (b : ℍ) :
    HasRightQuotientFDerivAt (fun x ↦ b + f x) q a :=
  hf.hasFDerivAt.const_add b

theorem add_const (hf : HasRightQuotientFDerivAt f q a) (b : ℍ) :
    HasRightQuotientFDerivAt (fun x ↦ f x + b) q a :=
  hf.hasFDerivAt.add_const b

end HasRightQuotientFDerivAt

/-- A constant has left slope `0`. -/
theorem hasLeftQuotientFDerivAt_const (c q : ℍ) : HasLeftQuotientFDerivAt (fun _ ↦ c) q 0 := by
  rw [hasLeftQuotientFDerivAt_iff_hasFDerivAt, map_zero]
  exact hasFDerivAt_const c q

/-- A constant has right slope `0`. -/
theorem hasRightQuotientFDerivAt_const (c q : ℍ) : HasRightQuotientFDerivAt (fun _ ↦ c) q 0 := by
  rw [hasRightQuotientFDerivAt_iff_hasFDerivAt, map_zero]
  exact hasFDerivAt_const c q

/-- Right multiplication `x ↦ x * b` has left slope `b` at every point. -/
theorem hasLeftQuotientFDerivAt_mul_const (b q : ℍ) :
    HasLeftQuotientFDerivAt (fun x ↦ x * b) q b := by
  have hfun : ⇑((ContinuousLinearMap.mul ℝ ℍ).flip b) = fun x ↦ x * b := by
    funext x; simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply']
  rw [hasLeftQuotientFDerivAt_iff_hasFDerivAt, ← hfun]
  exact ((ContinuousLinearMap.mul ℝ ℍ).flip b).hasFDerivAt

/-- Left multiplication `x ↦ a * x` has right slope `a` at every point. -/
theorem hasRightQuotientFDerivAt_const_mul (a q : ℍ) :
    HasRightQuotientFDerivAt (fun x ↦ a * x) q a := by
  have hfun : ⇑(ContinuousLinearMap.mul ℝ ℍ a) = fun x ↦ a * x := by
    funext x; simp only [ContinuousLinearMap.mul_apply']
  rw [hasRightQuotientFDerivAt_iff_hasFDerivAt, ← hfun]
  exact (ContinuousLinearMap.mul ℝ ℍ a).hasFDerivAt

/-- The identity has left slope `1`. -/
theorem hasLeftQuotientFDerivAt_id (q : ℍ) : HasLeftQuotientFDerivAt id q 1 := by
  rw [show (id : ℍ → ℍ) = fun x ↦ x * 1 from funext fun x ↦ (mul_one x).symm]
  exact hasLeftQuotientFDerivAt_mul_const 1 q

/-- The identity has right slope `1`. -/
theorem hasRightQuotientFDerivAt_id (q : ℍ) : HasRightQuotientFDerivAt id q 1 := by
  rw [show (id : ℍ → ℍ) = fun x ↦ 1 * x from funext fun x ↦ (one_mul x).symm]
  exact hasRightQuotientFDerivAt_const_mul 1 q

/-! ### Limit characterisations -/

/-- **Remainder form of the left quotient derivative.** `f` has left slope `b` at `q` exactly
when `‖f (q + h) - f q - h * b‖ / ‖h‖ → 0` as `h → 0`, `h ≠ 0`. -/
theorem hasLeftQuotientFDerivAt_iff_tendsto_norm_div :
    HasLeftQuotientFDerivAt f q b ↔
      Tendsto (fun h ↦ ‖f (q + h) - f q - h * b‖ / ‖h‖) (𝓝[≠] 0) (𝓝 0) := by
  rw [hasLeftQuotientFDerivAt_iff_hasFDerivAt, hasFDerivAt_iff_tendsto_norm_div_nhdsNE]
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply']

/-- **Remainder form of the right quotient derivative.** `f` has right slope `a` at `q` exactly
when `‖f (q + h) - f q - a * h‖ / ‖h‖ → 0` as `h → 0`, `h ≠ 0`. -/
theorem hasRightQuotientFDerivAt_iff_tendsto_norm_div :
    HasRightQuotientFDerivAt f q a ↔
      Tendsto (fun h ↦ ‖f (q + h) - f q - a * h‖ / ‖h‖) (𝓝[≠] 0) (𝓝 0) := by
  rw [hasRightQuotientFDerivAt_iff_hasFDerivAt, hasFDerivAt_iff_tendsto_norm_div_nhdsNE]
  simp only [ContinuousLinearMap.mul_apply']

/-- **The left quotient limit.** `f` has left slope `b` at `q` exactly when
`h⁻¹ * (f (q + h) - f q) → b` as `h → 0`, `h ≠ 0`. The increment stands on the left of the
difference quotient. -/
theorem hasLeftQuotientFDerivAt_iff_tendsto_inv_mul :
    HasLeftQuotientFDerivAt f q b ↔
      Tendsto (fun h ↦ h⁻¹ * (f (q + h) - f q)) (𝓝[≠] 0) (𝓝 b) := by
  rw [hasLeftQuotientFDerivAt_iff_tendsto_norm_div]
  refine Iff.trans (tendsto_congr' ?_) tendsto_iff_norm_sub_tendsto_zero.symm
  refine eventually_nhdsWithin_of_forall fun (h : ℍ) hh ↦ ?_
  replace hh : h ≠ 0 := hh
  dsimp only
  -- `h⁻¹ * Δ - b = h⁻¹ * (Δ - h * b)`, and the norm is multiplicative.
  rw [div_eq_inv_mul, ← norm_inv, ← norm_mul, mul_sub, ← mul_assoc, inv_mul_cancel₀ hh, one_mul]

/-- **The right quotient limit.** `f` has right slope `a` at `q` exactly when
`(f (q + h) - f q) * h⁻¹ → a` as `h → 0`, `h ≠ 0`. The increment stands on the right of the
difference quotient. -/
theorem hasRightQuotientFDerivAt_iff_tendsto_mul_inv :
    HasRightQuotientFDerivAt f q a ↔
      Tendsto (fun h ↦ (f (q + h) - f q) * h⁻¹) (𝓝[≠] 0) (𝓝 a) := by
  rw [hasRightQuotientFDerivAt_iff_tendsto_norm_div]
  refine Iff.trans (tendsto_congr' ?_) tendsto_iff_norm_sub_tendsto_zero.symm
  refine eventually_nhdsWithin_of_forall fun (h : ℍ) hh ↦ ?_
  replace hh : h ≠ 0 := hh
  dsimp only
  -- `Δ * h⁻¹ - a = (Δ - a * h) * h⁻¹`, and the norm is multiplicative.
  rw [div_eq_mul_inv, ← norm_inv, ← norm_mul, sub_mul, mul_assoc, mul_inv_cancel₀ hh, mul_one]

/-! ### Simultaneous left and right slopes -/

namespace HasLeftQuotientFDerivAt

/-- If `f` has left slope `b` and right slope `a` at the same point, then `b = a`: both are the
value of the real derivative at `1`. -/
theorem eq_of_hasRightQuotientFDerivAt (hb : HasLeftQuotientFDerivAt f q b)
    (ha : HasRightQuotientFDerivAt f q a) : b = a := by
  simpa using DFunLike.congr_fun (hb.hasFDerivAt.unique ha.hasFDerivAt) 1

/-- If `f` has left slope `b` and right slope `a` at the same point, then the slope is real:
`h ↦ h * b` and `h ↦ a * h` are the same map, so `b` is central in `ℍ`. -/
theorem im_eq_zero_of_hasRightQuotientFDerivAt (hb : HasLeftQuotientFDerivAt f q b)
    (ha : HasRightQuotientFDerivAt f q a) : b.im = 0 := by
  have hD := hb.hasFDerivAt.unique ha.hasFDerivAt
  obtain rfl := hb.eq_of_hasRightQuotientFDerivAt ha
  have hcenter : b ∈ Subalgebra.center ℝ ℍ :=
    Subalgebra.mem_center_iff.mpr fun h ↦ by simpa using DFunLike.congr_fun hD h
  obtain ⟨r, rfl⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hcenter)
  simp

end HasLeftQuotientFDerivAt

/-- For nonreal `a`, the map `x ↦ a * x` has no left slope at any point, although it has right
slope `a` everywhere (`TauCeti.hasRightQuotientFDerivAt_const_mul`). -/
theorem not_hasLeftQuotientFDerivAt_const_mul (ha : a.im ≠ 0) (q c : ℍ) :
    ¬HasLeftQuotientFDerivAt (fun x ↦ a * x) q c := fun hc ↦ by
  have hra := hasRightQuotientFDerivAt_const_mul a q
  obtain rfl := hc.eq_of_hasRightQuotientFDerivAt hra
  exact ha (hc.im_eq_zero_of_hasRightQuotientFDerivAt hra)

/-- For nonreal `b`, the map `x ↦ x * b` has no right slope at any point, although it has left
slope `b` everywhere (`TauCeti.hasLeftQuotientFDerivAt_mul_const`). -/
theorem not_hasRightQuotientFDerivAt_mul_const (hb : b.im ≠ 0) (q c : ℍ) :
    ¬HasRightQuotientFDerivAt (fun x ↦ x * b) q c := fun hc ↦
  hb ((hasLeftQuotientFDerivAt_mul_const b q).im_eq_zero_of_hasRightQuotientFDerivAt hc)

end TauCeti
