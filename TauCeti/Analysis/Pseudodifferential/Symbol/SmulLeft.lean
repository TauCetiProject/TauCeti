/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic

/-!
# Multiplying a symbol by a smooth function of the position

For a smooth scalar function `ψ` on `ℝⁿ` and a symbol `a(x, ξ)` of order `m`, the product
`ψ(x) a(x, ξ)` is again a symbol of order `m`: it is the composition of `a` with the order-`0`
symbol `ψ(x) id` of multiplication by `ψ`. Its quantization is `ψ Op(a)`, which localizes the
operator `Op(a)` in the position.

## Main results

* `TauCeti.Symbol.smulLeft`: the symbol `ψ(x) a(x, ξ)`, with coefficient
  `TauCeti.Symbol.coefficient_smulLeft`, and `TauCeti.Symbol.coefficient_smulLeft_ofReal` for a
  real `ψ`.
* `TauCeti.Symbol.hasCompactSpatialSupport_smulLeft`: when `ψ` has compact support, `ψ(x) a(x, ξ)`
  has compact spatial support.
* `TauCeti.Symbol.HasCompactSpatialSupport.smulLeft`: when `a` has compact spatial support, so does
  `ψ(x) a(x, ξ)`.
-/

public section

noncomputable section

open scoped ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The product `ψ(x) a(x, ξ)` of a symbol `a` with a smooth scalar function `ψ` of the position,
a symbol of the same order as `a`: the composition with the symbol of multiplication by `ψ`. -/
def smulLeft {ψ : CoordinateSpace n → ℂ} (hψ : ContDiff ℝ ∞ ψ) (a : Symbol n V W m) :
    Symbol n V W m :=
  inclusion (zero_add m).le
    ((ofSpatial (fun x ↦ ψ x • ContinuousLinearMap.id ℂ W) (hψ.smul contDiff_const)).comp a)

@[simp]
theorem coefficient_smulLeft {ψ : CoordinateSpace n → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (a : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    (smulLeft hψ a).coefficient p = ψ p.1 • a.coefficient p := by
  simp [smulLeft, coefficient_inclusion, ContinuousLinearMap.smul_comp]

/-- `TauCeti.Symbol.coefficient_smulLeft` for a real smooth function `ψ`, viewed in `ℂ`: the
coefficient of `ψ(x) a(x, ξ)` is the real multiple `ψ(x) • a(x, ξ)`. -/
theorem coefficient_smulLeft_ofReal {ψ : CoordinateSpace n → ℝ}
    (hψ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ ψ)) (a : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (smulLeft hψ a).coefficient p = ψ p.1 • a.coefficient p := by
  simp [Complex.coe_smul]

/-- Multiplying any symbol by a compactly supported smooth function of the position gives a symbol
with compact spatial support. -/
theorem hasCompactSpatialSupport_smulLeft {ψ : CoordinateSpace n → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (a : Symbol n V W m) :
    (smulLeft hψ a).HasCompactSpatialSupport :=
  hasCompactSpatialSupport_iff.2
    ⟨tsupport ψ, hψc, fun x hx ξ ↦ by simp [image_eq_zero_of_notMem_tsupport hx]⟩

/-- Multiplying a symbol with compact spatial support by any smooth function of the position keeps
compact spatial support. -/
theorem HasCompactSpatialSupport.smulLeft {a : Symbol n V W m} (ha : a.HasCompactSpatialSupport)
    {ψ : CoordinateSpace n → ℂ} (hψ : ContDiff ℝ ∞ ψ) :
    (Symbol.smulLeft hψ a).HasCompactSpatialSupport :=
  (ha.comp_left _).inclusion _

end Symbol

end TauCeti
