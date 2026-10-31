/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
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
The order of multiplication is part of every statement. One-sided quotient differentiability is
not closed under products or pointwise inverses; the product and inverse criteria below say
exactly when the real product and inverse rules produce a derivative of the required one-sided
shape, while the chain rule always does.

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
* `HasFDerivAt.hasLeftQuotientFDerivAt_iff` and its right counterpart: when the real derivative
  `D` of `f` at `q` is known, `b` is a left slope exactly when `D h = h * b` for every `h`.
* `TauCeti.HasLeftQuotientFDerivAt.mul_iff`: if `f` and `g` have left slopes `b` and `c` at `q`,
  then `f * g` has left slope `b * g q + f q * c` exactly when `c = 0` or `f q` is real.
  `TauCeti.HasRightQuotientFDerivAt.mul_iff`: for right slopes `a` and `c`, the product has right
  slope `a * g q + f q * c` exactly when `a = 0` or `g q` is real. Since a slope of the product is
  forced to be this value, the same alternatives decide whether the product has any slope
  (`TauCeti.HasLeftQuotientFDerivAt.leftQuotientDifferentiableAt_mul_iff` and its right
  counterpart).
* `TauCeti.HasLeftQuotientFDerivAt.inv_iff` and `TauCeti.HasRightQuotientFDerivAt.inv_iff`: for
  `f q ≠ 0`, the pointwise inverse has the slope `-((f q)⁻¹ * b * (f q)⁻¹)` on the same side
  exactly when the slope `b` of `f` vanishes or `f q` is real.
* `TauCeti.HasLeftQuotientFDerivAt.comp` and `TauCeti.HasRightQuotientFDerivAt.comp`: the chain
  rules, with left slope `c * b` and right slope `a * c` for `f ∘ g`, in that order.

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

/-- A quaternion is real exactly when it commutes with every quaternion. -/
private theorem im_eq_zero_iff_forall_commute {x : ℍ} : x.im = 0 ↔ ∀ h, Commute x h := by
  refine ⟨fun hx h ↦ ?_, fun hx ↦ ?_⟩
  · rw [← Quaternion.re_add_im x, hx, add_zero]
    exact Quaternion.coe_commute _ _
  · have hcenter : x ∈ Subalgebra.center ℝ ℍ :=
      Subalgebra.mem_center_iff.mpr fun h ↦ (hx h).symm.eq
    obtain ⟨r, rfl⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hcenter)
    simp

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
  exact im_eq_zero_iff_forall_commute.mpr fun h ↦
    (commute_iff_eq b h).mpr (by simpa using (DFunLike.congr_fun hD h).symm)

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

/-! ### Slopes read off a known real derivative -/

/-- If `f` has real derivative `D` at `q`, then `f` has left slope `b` at `q` exactly when
`D h = h * b` for every `h`. -/
theorem _root_.HasFDerivAt.hasLeftQuotientFDerivAt_iff {D : ℍ →L[ℝ] ℍ}
    (hD : HasFDerivAt f D q) : HasLeftQuotientFDerivAt f q b ↔ ∀ h, D h = h * b :=
  ⟨fun hb h ↦ by simpa using DFunLike.congr_fun (hD.unique hb.hasFDerivAt) h,
    fun H ↦ hD.congr_fderiv (ContinuousLinearMap.ext fun h ↦ by simp [H])⟩

/-- If `f` has real derivative `D` at `q`, then `f` has right slope `a` at `q` exactly when
`D h = a * h` for every `h`. -/
theorem _root_.HasFDerivAt.hasRightQuotientFDerivAt_iff {D : ℍ →L[ℝ] ℍ}
    (hD : HasFDerivAt f D q) : HasRightQuotientFDerivAt f q a ↔ ∀ h, D h = a * h :=
  ⟨fun ha h ↦ by simpa using DFunLike.congr_fun (hD.unique ha.hasFDerivAt) h,
    fun H ↦ hD.congr_fderiv (ContinuousLinearMap.ext fun h ↦ by simp [H])⟩

/-- If `f` has real derivative `D` at `q`, then `f` has some left slope at `q` exactly when
`D 1` is a left slope. -/
theorem _root_.HasFDerivAt.leftQuotientDifferentiableAt_iff {D : ℍ →L[ℝ] ℍ}
    (hD : HasFDerivAt f D q) :
    LeftQuotientDifferentiableAt f q ↔ HasLeftQuotientFDerivAt f q (D 1) := by
  rw [leftQuotientDifferentiableAt_iff_hasLeftQuotientFDerivAt_fderiv, hD.fderiv]

/-- If `f` has real derivative `D` at `q`, then `f` has some right slope at `q` exactly when
`D 1` is a right slope. -/
theorem _root_.HasFDerivAt.rightQuotientDifferentiableAt_iff {D : ℍ →L[ℝ] ℍ}
    (hD : HasFDerivAt f D q) :
    RightQuotientDifferentiableAt f q ↔ HasRightQuotientFDerivAt f q (D 1) := by
  rw [rightQuotientDifferentiableAt_iff_hasRightQuotientFDerivAt_fderiv, hD.fderiv]

/-! ### Products, inverses and compositions -/

/-- `x * h * y = h * x * y` for every `h` exactly when `y = 0` or `x` is real. -/
private theorem forall_mul_mul_eq_iff {x y : ℍ} :
    (∀ h, x * h * y = h * x * y) ↔ y = 0 ∨ x.im = 0 := by
  rw [im_eq_zero_iff_forall_commute]
  refine ⟨fun H ↦ or_iff_not_imp_left.mpr fun hy h ↦
    (commute_iff_eq x h).mpr (mul_right_cancel₀ hy (H h)), ?_⟩
  rintro (rfl | hx) h
  · simp
  · rw [(hx h).eq]

/-- `y * h * x = y * x * h` for every `h` exactly when `y = 0` or `x` is real. -/
private theorem forall_mul_mul_eq_iff' {x y : ℍ} :
    (∀ h, y * h * x = y * x * h) ↔ y = 0 ∨ x.im = 0 := by
  rw [im_eq_zero_iff_forall_commute]
  refine ⟨fun H ↦ or_iff_not_imp_left.mpr fun hy h ↦ ?_, ?_⟩
  · exact (commute_iff_eq x h).mpr (mul_left_cancel₀ hy (by simpa only [mul_assoc] using H h)).symm
  rintro (rfl | hx) h
  · simp
  · rw [mul_assoc, mul_assoc, (hx h).eq]

namespace HasLeftQuotientFDerivAt

/-- **Left product criterion.** If `f` and `g` have left slopes `b` and `c` at `q`, then the
pointwise product `f * g` has left slope `b * g q + f q * c` at `q` exactly when `c = 0` or `f q`
is real. -/
theorem mul_iff (hf : HasLeftQuotientFDerivAt f q b) (hg : HasLeftQuotientFDerivAt g q c) :
    HasLeftQuotientFDerivAt (fun x ↦ f x * g x) q (b * g q + f q * c) ↔
      c = 0 ∨ (f q).im = 0 := by
  rw [(hf.hasFDerivAt.fun_mul' hg.hasFDerivAt).hasLeftQuotientFDerivAt_iff,
    ← forall_mul_mul_eq_iff]
  refine forall_congr' fun h ↦ ?_
  simp [mul_add, mul_assoc, add_comm]

/-- If `f` and `g` have left slopes `b` and `c` at `q`, then `f * g` has some left slope at `q`
exactly when `c = 0` or `f q` is real; the slope is then `b * g q + f q * c`
(`TauCeti.HasLeftQuotientFDerivAt.mul_iff`). -/
theorem leftQuotientDifferentiableAt_mul_iff (hf : HasLeftQuotientFDerivAt f q b)
    (hg : HasLeftQuotientFDerivAt g q c) :
    LeftQuotientDifferentiableAt (fun x ↦ f x * g x) q ↔ c = 0 ∨ (f q).im = 0 := by
  rw [(hf.hasFDerivAt.fun_mul' hg.hasFDerivAt).leftQuotientDifferentiableAt_iff, ← hf.mul_iff hg]
  simp [add_comm]

/-- **Left inverse criterion.** If `f` has left slope `b` at `q` and `f q ≠ 0`, then the pointwise
inverse `x ↦ (f x)⁻¹` has left slope `-((f q)⁻¹ * b * (f q)⁻¹)` at `q` exactly when `b = 0` or
`f q` is real. The real derivative of the inverse is `h ↦ -((f q)⁻¹ * (h * b) * (f q)⁻¹)`. -/
theorem inv_iff (hf : HasLeftQuotientFDerivAt f q b) (hq : f q ≠ 0) :
    HasLeftQuotientFDerivAt (fun x ↦ (f x)⁻¹) q (-((f q)⁻¹ * b * (f q)⁻¹)) ↔
      b = 0 ∨ (f q).im = 0 := by
  have hD : HasFDerivAt (fun x ↦ (f x)⁻¹) _ q := (hasFDerivAt_inv' hq).comp q hf.hasFDerivAt
  have hinv : (f q)⁻¹.im = 0 ↔ (f q).im = 0 := by
    simp only [im_eq_zero_iff_forall_commute, Commute.inv_left_iff₀]
  rw [hD.hasLeftQuotientFDerivAt_iff, ← hinv, ← forall_mul_mul_eq_iff]
  refine forall_congr' fun h ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply', mul_neg, neg_inj, ← mul_assoc]
  exact mul_left_inj' (inv_ne_zero hq)

/-- If `f` has left slope `b` at `q` and `f q ≠ 0`, then `x ↦ (f x)⁻¹` has some left slope at `q`
exactly when `b = 0` or `f q` is real; the slope is then `-((f q)⁻¹ * b * (f q)⁻¹)`
(`TauCeti.HasLeftQuotientFDerivAt.inv_iff`). -/
theorem leftQuotientDifferentiableAt_inv_iff (hf : HasLeftQuotientFDerivAt f q b) (hq : f q ≠ 0) :
    LeftQuotientDifferentiableAt (fun x ↦ (f x)⁻¹) q ↔ b = 0 ∨ (f q).im = 0 := by
  have hD : HasFDerivAt (fun x ↦ (f x)⁻¹) _ q := (hasFDerivAt_inv' hq).comp q hf.hasFDerivAt
  rw [hD.leftQuotientDifferentiableAt_iff, ← hf.inv_iff hq]
  simp

/-- **Chain rule for left slopes.** If `g` has left slope `c` at `q` and `f` has left slope `b` at
`g q`, then `f ∘ g` has left slope `c * b` at `q`. -/
theorem comp (q : ℍ) (hf : HasLeftQuotientFDerivAt f (g q) b)
    (hg : HasLeftQuotientFDerivAt g q c) : HasLeftQuotientFDerivAt (f ∘ g) q (c * b) := by
  rw [(hf.hasFDerivAt.comp q hg.hasFDerivAt).hasLeftQuotientFDerivAt_iff]
  simp [mul_assoc]

end HasLeftQuotientFDerivAt

namespace HasRightQuotientFDerivAt

/-- **Right product criterion.** If `f` and `g` have right slopes `a` and `c` at `q`, then the
pointwise product `f * g` has right slope `a * g q + f q * c` at `q` exactly when `a = 0` or `g q`
is real. -/
theorem mul_iff (hf : HasRightQuotientFDerivAt f q a) (hg : HasRightQuotientFDerivAt g q c) :
    HasRightQuotientFDerivAt (fun x ↦ f x * g x) q (a * g q + f q * c) ↔
      a = 0 ∨ (g q).im = 0 := by
  rw [(hf.hasFDerivAt.fun_mul' hg.hasFDerivAt).hasRightQuotientFDerivAt_iff,
    ← forall_mul_mul_eq_iff']
  refine forall_congr' fun h ↦ ?_
  simp only [add_apply, smul_apply, ContinuousLinearMap.mul_apply', smul_eq_mul, op_smul_eq_mul,
    add_mul, mul_assoc]
  rw [add_comm, add_left_inj]

/-- If `f` and `g` have right slopes `a` and `c` at `q`, then `f * g` has some right slope at `q`
exactly when `a = 0` or `g q` is real; the slope is then `a * g q + f q * c`
(`TauCeti.HasRightQuotientFDerivAt.mul_iff`). -/
theorem rightQuotientDifferentiableAt_mul_iff (hf : HasRightQuotientFDerivAt f q a)
    (hg : HasRightQuotientFDerivAt g q c) :
    RightQuotientDifferentiableAt (fun x ↦ f x * g x) q ↔ a = 0 ∨ (g q).im = 0 := by
  rw [(hf.hasFDerivAt.fun_mul' hg.hasFDerivAt).rightQuotientDifferentiableAt_iff,
    ← hf.mul_iff hg]
  simp [add_comm]

/-- **Right inverse criterion.** If `f` has right slope `a` at `q` and `f q ≠ 0`, then the
pointwise inverse `x ↦ (f x)⁻¹` has right slope `-((f q)⁻¹ * a * (f q)⁻¹)` at `q` exactly when
`a = 0` or `f q` is real. The real derivative of the inverse is
`h ↦ -((f q)⁻¹ * (a * h) * (f q)⁻¹)`. -/
theorem inv_iff (hf : HasRightQuotientFDerivAt f q a) (hq : f q ≠ 0) :
    HasRightQuotientFDerivAt (fun x ↦ (f x)⁻¹) q (-((f q)⁻¹ * a * (f q)⁻¹)) ↔
      a = 0 ∨ (f q).im = 0 := by
  have hD : HasFDerivAt (fun x ↦ (f x)⁻¹) _ q := (hasFDerivAt_inv' hq).comp q hf.hasFDerivAt
  have hinv : (f q)⁻¹.im = 0 ↔ (f q).im = 0 := by
    simp only [im_eq_zero_iff_forall_commute, Commute.inv_left_iff₀]
  have ha : (f q)⁻¹ * a = 0 ↔ a = 0 := by simp [hq]
  rw [hD.hasRightQuotientFDerivAt_iff, ← hinv, ← ha, ← forall_mul_mul_eq_iff']
  refine forall_congr' fun h ↦ ?_
  simp [mul_assoc]

/-- If `f` has right slope `a` at `q` and `f q ≠ 0`, then `x ↦ (f x)⁻¹` has some right slope at
`q` exactly when `a = 0` or `f q` is real; the slope is then `-((f q)⁻¹ * a * (f q)⁻¹)`
(`TauCeti.HasRightQuotientFDerivAt.inv_iff`). -/
theorem rightQuotientDifferentiableAt_inv_iff (hf : HasRightQuotientFDerivAt f q a)
    (hq : f q ≠ 0) :
    RightQuotientDifferentiableAt (fun x ↦ (f x)⁻¹) q ↔ a = 0 ∨ (f q).im = 0 := by
  have hD : HasFDerivAt (fun x ↦ (f x)⁻¹) _ q := (hasFDerivAt_inv' hq).comp q hf.hasFDerivAt
  rw [hD.rightQuotientDifferentiableAt_iff, ← hf.inv_iff hq]
  simp

/-- **Chain rule for right slopes.** If `g` has right slope `c` at `q` and `f` has right slope `a`
at `g q`, then `f ∘ g` has right slope `a * c` at `q`. -/
theorem comp (q : ℍ) (hf : HasRightQuotientFDerivAt f (g q) a)
    (hg : HasRightQuotientFDerivAt g q c) : HasRightQuotientFDerivAt (f ∘ g) q (a * c) := by
  rw [(hf.hasFDerivAt.comp q hg.hasFDerivAt).hasRightQuotientFDerivAt_iff]
  simp [mul_assoc]

end HasRightQuotientFDerivAt

end TauCeti
