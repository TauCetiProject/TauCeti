/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Dual
public import TauCeti.MeasureTheory.OptimalTransport.Disintegration
public import TauCeti.MeasureTheory.OptimalTransport.Duality.Certificate

/-!
# The twist condition and uniqueness of contact partners

Let `φ`, `ψ` be a dual feasible pair for a real cost `c` on `E × Y`, where `E` is a real normed
space, so that `φ x' + ψ y ≤ c (x', y)` everywhere, and let `(x, y)` lie in their contact set,
where this is an equality. Then `x' ↦ c (x', y) - φ x'` attains its minimum at `x`. If both `φ`
and the section `c (·, y)` are differentiable at `x`, the first-order condition for that
minimum says that the derivative of the potential at `x` is the `x`-derivative of the cost at
`(x, y)`:

`D φ (x) = Dₓ c (x, y)`.

The right-hand side depends on `y` and the left-hand side does not. So if the cost satisfies the
*twist condition* — for each `x`, the map `y ↦ Dₓ c (x, y)` is injective — then at every point
where `φ` is differentiable there is at most one contact partner `y`. When `φ` is differentiable
`μ`-almost everywhere, almost every contact fibre is therefore a subsingleton.

A plan concentrated on the contact set then has deterministic conditional laws: together with
`TauCeti.IsCoupling.ae_exists_condKernel_eq_dirac`, the conditional kernel of such a coupling is,
for `μ`-almost every `x`, the Dirac mass at the unique contact partner of `x`. Once a dual
optimizer exists, every optimal plan is concentrated on its contact set
(`TauCeti.IsDualCertificate.of_isOptimalCoupling`), so this gives uniqueness of the optimal plan,
`TauCeti.IsDualCertificate.eq_of_isOptimalCoupling`. This is the mechanism behind
the existence and uniqueness of optimal transport maps for twisted costs: the Euclidean quadratic
cost, for which `Dₓ c (x, y) = x - y` up to the Riesz identification, and the strictly convex
costs `c (x, y) = h (x - y)`, for which `Dₓ c (x, y) = D h (x - y)`.

The potential `φ` is extended-real valued, as the `c`-concave potentials of
`TauCeti.cTransformSymm` are. It is differentiated through `EReal.toReal`, and the statements
ask that `φ` not take the value `⊥` near the point, since the dual constraint carries no
information where `φ = ⊥`. The value `⊤` is excluded automatically wherever the constraint holds
against a contact partner.

The pointwise statements, `TauCeti.hasFDerivAt_eq_of_mem_contactSet` and
`TauCeti.subsingleton_setOf_mem_contactSet`, use only local feasibility and differentiability of
the cost sections at the contact partners, with twist asked for on the set where the
`x`-derivative of the cost exists. The measure-level statements take the standard global form
of these hypotheses: the cost is differentiable in its first variable and twisted at every
point. Nothing about semiconcavity of the cost is assumed; the differentiability of `φ` is a
hypothesis, to be supplied by a Rademacher-type theorem for the potentials at hand.

## Main statements

* `TauCeti.hasFDerivAt_eq_of_mem_contactSet` — the first-order condition `D φ (x) = Dₓ c (x, y)`
  at a contact point, and `TauCeti.fderiv_eq_of_mem_contactSet` its `fderiv` form;
* `TauCeti.subsingleton_setOf_mem_contactSet` — under the twist condition, a point where the
  potential is differentiable has at most one contact partner;
* `TauCeti.injective_fderiv_norm_sub_sq_div_two` — the quadratic cost `‖x - y‖ ^ 2 / 2` on a
  real inner product space is twisted;
* `TauCeti.ae_subsingleton_setOf_mem_contactSet` — the contact fibres are almost all
  subsingletons when the potential is differentiable almost everywhere;
* `TauCeti.IsDualCertificate.eq_of_isOptimalCoupling` — under the same hypotheses, a coupling
  certified by a dual pair is the only optimal coupling.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 10, the
  twist condition and the solution of the Monge problem for twisted costs;
* W. Gangbo and R. J. McCann, *The geometry of optimal transportation*, Acta Math. 177 (1996),
  113--161;
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Progress in Nonlinear
  Differential Equations and their Applications 87, Birkhäuser 2015, §1.3.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace TauCeti

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {c : E × Y → ℝ} {φ : E → EReal} {ψ : Y → EReal} {x : E} {y : Y}

/-! ### The first-order condition at a contact point -/

/-- **The first-order condition at a contact point.** If the dual constraint
`φ x' + ψ y ≤ c (x', y)` holds for `x'` near `x` and is an equality at `x`, then the derivative
of the potential at `x` is the `x`-derivative of the cost at `(x, y)`. The potential is
differentiated through `EReal.toReal`, and is asked not to take the value `⊥` near `x`. -/
theorem hasFDerivAt_eq_of_mem_contactSet {φ' c' : E →L[ℝ] ℝ}
    (hfeas : ∀ᶠ x' in 𝓝 x, φ x' + ψ y ≤ (c (x', y) : EReal))
    (hfin : ∀ᶠ x' in 𝓝 x, φ x' ≠ ⊥) (hxy : (x, y) ∈ contactSet c φ ψ)
    (hφ : HasFDerivAt (fun x' ↦ (φ x').toReal) φ' x)
    (hc : HasFDerivAt (fun x' ↦ c (x', y)) c' x) : φ' = c' := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_coe_of_mem_contactSet hxy
  have hmin : IsLocalMin (fun x' ↦ c (x', y) - (φ x').toReal) x := by
    filter_upwards [hfeas, hfin] with x' hle hbot
    have htop : φ x' ≠ ⊤ := by
      rintro h
      rw [h, hb, EReal.top_add_coe] at hle
      exact EReal.coe_ne_top _ (top_le_iff.1 hle)
    rw [hb, ← EReal.coe_toReal htop hbot, ← EReal.coe_add, EReal.coe_le_coe_iff] at hle
    rw [ha, EReal.toReal_coe]
    linarith
  exact (sub_eq_zero.1 (hmin.hasFDerivAt_eq_zero (hc.sub hφ))).symm

/-- The `fderiv` form of `TauCeti.hasFDerivAt_eq_of_mem_contactSet`: at a contact point, the
derivative of the potential is the `x`-derivative of the cost. -/
theorem fderiv_eq_of_mem_contactSet
    (hfeas : ∀ᶠ x' in 𝓝 x, φ x' + ψ y ≤ (c (x', y) : EReal))
    (hfin : ∀ᶠ x' in 𝓝 x, φ x' ≠ ⊥) (hxy : (x, y) ∈ contactSet c φ ψ)
    (hφ : DifferentiableAt ℝ (fun x' ↦ (φ x').toReal) x)
    (hc : DifferentiableAt ℝ (fun x' ↦ c (x', y)) x) :
    fderiv ℝ (fun x' ↦ (φ x').toReal) x = fderiv ℝ (fun x' ↦ c (x', y)) x :=
  hasFDerivAt_eq_of_mem_contactSet hfeas hfin hxy hφ.hasFDerivAt hc.hasFDerivAt

/-! ### The twist condition -/

/-- **The twist theorem at a point.** Suppose the cost is twisted at `x`: the map
`y ↦ Dₓ c (x, y)` is injective on the set of `y` for which the section `c (·, y)` is
differentiable at `x`. If the potential is differentiable at `x`, finite near `x`, and satisfies
the dual constraint near `x`, and the cost sections of the contact partners of `x` are
differentiable at `x`, then `x` has at most one contact partner. -/
theorem subsingleton_setOf_mem_contactSet
    (hfeas : ∀ y, ∀ᶠ x' in 𝓝 x, φ x' + ψ y ≤ (c (x', y) : EReal))
    (hfin : ∀ᶠ x' in 𝓝 x, φ x' ≠ ⊥) (hφ : DifferentiableAt ℝ (fun x' ↦ (φ x').toReal) x)
    (hc : ∀ y, (x, y) ∈ contactSet c φ ψ → DifferentiableAt ℝ (fun x' ↦ c (x', y)) x)
    (htwist : Set.InjOn (fun y ↦ fderiv ℝ (fun x' ↦ c (x', y)) x)
      {y | DifferentiableAt ℝ (fun x' ↦ c (x', y)) x}) :
    {y | (x, y) ∈ contactSet c φ ψ}.Subsingleton := by
  intro y₁ h₁ y₂ h₂
  refine htwist (hc y₁ h₁) (hc y₂ h₂) ?_
  exact (fderiv_eq_of_mem_contactSet (hfeas y₁) hfin h₁ hφ (hc y₁ h₁)).symm.trans
    (fderiv_eq_of_mem_contactSet (hfeas y₂) hfin h₂ hφ (hc y₂ h₂))

/-- **The quadratic cost is twisted.** On a real inner product space, the `x`-derivative of the
cost `‖x - y‖ ^ 2 / 2` at `x` is `⟪x - y, ·⟫`, which determines `y`. -/
theorem injective_fderiv_norm_sub_sq_div_two {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (x : F) :
    Function.Injective fun y : F ↦ fderiv ℝ (fun x' ↦ ‖x' - y‖ ^ 2 / 2) x := by
  have hderiv (y : F) : fderiv ℝ (fun x' ↦ ‖x' - y‖ ^ 2 / 2) x = innerSL ℝ (x - y) := by
    simp_rw [div_eq_mul_inv]
    refine (HasFDerivAt.mul_const (HasFDerivAt.norm_sq ((hasFDerivAt_id x).sub_const y))
      2⁻¹).fderiv.trans ?_
    ext v
    simp
  intro y₁ y₂ h
  simpa only [hderiv, innerSL_inj, sub_right_inj] using h

variable [MeasurableSpace E] {μ : Measure E}

/-- **The twist theorem.** For a cost that is differentiable in its first variable with
`y ↦ Dₓ c (x, y)` injective at every `x`, and a dual feasible pair whose first potential is
finite near, and differentiable at, `μ`-almost every point, the contact fibres
`{y | (x, y) ∈ contactSet c φ ψ}` are subsingletons for `μ`-almost every `x`. Combined with
`TauCeti.IsCoupling.ae_exists_condKernel_eq_dirac`, a finite coupling of `μ` concentrated on the
contact set has, for `μ`-almost every `x`, the Dirac mass at the unique contact partner of `x`
as its conditional law. -/
theorem ae_subsingleton_setOf_mem_contactSet (μ : Measure E)
    (hfeas : ∀ x y, φ x + ψ y ≤ (c (x, y) : EReal))
    (hφ : ∀ᵐ x ∂μ,
      (∀ᶠ x' in 𝓝 x, φ x' ≠ ⊥) ∧ DifferentiableAt ℝ (fun x' ↦ (φ x').toReal) x)
    (hc : ∀ x y, DifferentiableAt ℝ (fun x' ↦ c (x', y)) x)
    (htwist : ∀ x, Function.Injective fun y ↦ fderiv ℝ (fun x' ↦ c (x', y)) x) :
    ∀ᵐ x ∂μ, {y | (x, y) ∈ contactSet c φ ψ}.Subsingleton := by
  filter_upwards [hφ] with x ⟨hfin, hdiff⟩
  exact subsingleton_setOf_mem_contactSet (fun y ↦ .of_forall fun x' ↦ hfeas x' y) hfin hdiff
    (fun y _ ↦ hc x y) (htwist x).injOn

variable [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y] {ν : Measure Y}
  [IsFiniteMeasure μ] {φ : E → ℝ} {ψ : Y → ℝ} {π σ : Measure (E × Y)}

/-- **Uniqueness of the optimal plan for a twisted cost.** Let `c` be a nonnegative real cost,
differentiable in its first variable, with `y ↦ Dₓ c (x, y)` injective at every `x`. If `π` is
certified optimal by a dual pair `(φ, ψ)` whose first potential is differentiable `μ`-almost
everywhere, then every optimal coupling of `μ` and `ν` whose cost is almost everywhere
measurable is equal to `π`. -/
theorem IsDualCertificate.eq_of_isOptimalCoupling (hc₀ : ∀ z, 0 ≤ c z)
    (h : IsDualCertificate (fun z ↦ ENNReal.ofReal (c z)) π μ ν φ ψ)
    (hσ : IsOptimalCoupling (fun z ↦ ENNReal.ofReal (c z)) σ μ ν)
    (hcσ : AEMeasurable (fun z ↦ ENNReal.ofReal (c z)) σ) (hφ : ∀ᵐ x ∂μ, DifferentiableAt ℝ φ x)
    (hc : ∀ x y, DifferentiableAt ℝ (fun x' ↦ c (x', y)) x)
    (htwist : ∀ x, Function.Injective fun y ↦ fderiv ℝ (fun x' ↦ c (x', y)) x) :
    σ = π := by
  have hσ' := h.of_isOptimalCoupling hcσ hσ
  have hfeas : ∀ x y, (φ x : EReal) + (ψ y : EReal) ≤ (c (x, y) : EReal) := fun x y ↦ by
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    exact (dualFeasible_ofReal_iff hc₀ φ ψ).1 h.dualFeasible x y
  have hsub := ae_subsingleton_setOf_mem_contactSet (φ := fun x ↦ (φ x : EReal))
    (ψ := fun y ↦ (ψ y : EReal)) μ hfeas
    (hφ.mono fun x hx ↦ ⟨.of_forall fun _ ↦ EReal.coe_ne_bot _, by simpa using hx⟩) hc htwist
  have := h.toIsCoupling.isFiniteMeasure
  have := hσ.toIsCoupling.isFiniteMeasure
  rw [← dualContactSet_ofReal hc₀] at hsub
  exact hσ.toIsCoupling.eq_of_ae_mem_of_subsingleton h.toIsCoupling
    hσ'.ae_mem_dualContactSet h.ae_mem_dualContactSet hsub

end TauCeti
