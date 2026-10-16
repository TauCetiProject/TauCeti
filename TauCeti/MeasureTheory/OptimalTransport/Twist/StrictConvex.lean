/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Differentiability
public import TauCeti.Analysis.Convex.Extrema
public import TauCeti.MeasureTheory.OptimalTransport.MeasurableSelection
public import TauCeti.MeasureTheory.OptimalTransport.Twist.Basic

/-!
# Contact partners for strictly convex displacement costs

Let `h : E → ℝ` be convex on a real normed space and consider the displacement cost
`c (x, y) = h (x - y)`. Such an `h` need not be differentiable, so the twist theorem
`TauCeti.subsingleton_setOf_mem_contactSet`, which compares `x`-derivatives of the cost, does not
apply. Gangbo and McCann replace the derivative of `h` by its subgradients.

Let `(φ, ψ)` satisfy the dual constraint `φ x' + ψ y ≤ h (x' - y)` near `x`, with equality at `x`,
and let `φ` be differentiable at `x`. Then `x' ↦ h (x' - y) - φ x'` has a local minimum at `x`, so
the derivative `φ'` of `φ` at `x` is a subgradient of `h` at `x - y`:

`h (x - y) + φ' (w - (x - y)) ≤ h w` for every `w`.

If `h` is strictly convex, distinct points have disjoint subdifferentials, so `x - y`, and hence
the contact partner `y`, is determined by `φ'`. The pointwise statements use no
differentiability, growth or nonnegativity of `h`. On a real inner product space,
conjugate-subgradient reciprocity then gives `x - y ∈ ∂h⋆(∇φ x)`, and where the Legendre–Fenchel
conjugate `h⋆` is differentiable this is the Gangbo–McCann formula `y = x - ∇h⋆(∇φ x)`.

When `φ` is differentiable `μ`-almost everywhere, almost every contact fibre is therefore a
subsingleton. A finite coupling concentrated on the contact set is then the graph plan of a
measurable map `T` whose increments `x - T x` carry the derivative of `φ` as a subgradient of `h`,
and it is the only coupling of its source marginal concentrated on that contact set.

## Main statements

* `TauCeti.add_le_of_mem_contactSet_sub` — at a contact point of a convex displacement cost, the
  derivative of the potential is a subgradient of `h` at `x - y`, with
  `TauCeti.mem_subdifferential_of_mem_contactSet_sub` its form for an arbitrary pairing;
* `TauCeti.subsingleton_setOf_mem_contactSet_of_strictConvexOn` — for strictly convex `h`, a
  point where the potential is differentiable has at most one contact partner;
* `TauCeti.gradient_fenchelConjugate_eq_sub_of_mem_contactSet` — the formula
  `x - y = ∇h⋆(∇φ x)` at a contact point;
* `TauCeti.ae_subsingleton_setOf_mem_contactSet_of_strictConvexOn` — almost every contact fibre
  is a subsingleton when the potential is differentiable almost everywhere;
* `TauCeti.IsCoupling.exists_graphPlan_of_ae_mem_contactSet_of_strictConvexOn` and
  `TauCeti.IsCoupling.eq_of_ae_mem_contactSet_of_strictConvexOn` — a coupling concentrated on the
  contact set is induced by a measurable map, and is unique;
* `TauCeti.IsDualCertificate.eq_of_isOptimalCoupling_of_strictConvexOn` — uniqueness of the
  optimal plan for a certified nonnegative strictly convex displacement cost.

## References

* W. Gangbo and R. J. McCann, *The geometry of optimal transportation*, Acta Math. 177 (1996),
  113--161, for the subgradient form of the twist condition for strictly convex costs
  `h (x - y)`.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 10.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology ENNReal Gradient

namespace TauCeti

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {h : E → ℝ} {φ ψ : E → EReal}
  {x y : E}

/-! ### The first-order condition -/

/-- **The first-order condition for a convex displacement cost.** Let `h` be convex. If the dual
constraint `φ x' + ψ y ≤ h (x' - y)` holds for `x'` near `x` and is an equality at `x`, `φ` does
not take the value `⊥` near `x`, and its real representative has derivative `φ'` at `x`, then `φ'`
is a subgradient of `h` at `x - y`. No differentiability of `h` is needed. -/
theorem add_le_of_mem_contactSet_sub {φ' : E →L[ℝ] ℝ} (hh : ConvexOn ℝ univ h)
    (hfeas : ∀ᶠ x' in 𝓝 x, φ x' + ψ y ≤ (h (x' - y) : EReal))
    (hfin : ∀ᶠ x' in 𝓝 x, φ x' ≠ ⊥) (hxy : (x, y) ∈ contactSet (fun z ↦ h (z.1 - z.2)) φ ψ)
    (hφ : HasFDerivAt (fun x' ↦ (φ x').toReal) φ' x) (w : E) :
    h (x - y) + φ' (w - (x - y)) ≤ h w := by
  -- Translating by `y`, the function `w ↦ h w - (φ (w + y)).toReal` has a local minimum at
  -- `x - y`, and its subtracted part has derivative `φ'` there.
  have hmin := isLocalMin_sub_toReal_of_mem_contactSet (c := fun z ↦ h (z.1 - z.2)) hfeas hfin hxy
  have hg : HasFDerivAt (fun w ↦ (φ (w + y)).toReal) φ' (x - y) :=
    (hasFDerivAt_comp_add_right y).2 (by rwa [sub_add_cancel])
  have hmin' : IsLocalMinOn (fun w ↦ h w - (φ (w + y)).toReal) univ (x - y) := by
    rw [isLocalMinOn_univ_iff]
    have ht : Tendsto (fun w ↦ w + y) (𝓝 (x - y)) (𝓝 x) :=
      Continuous.tendsto' (by fun_prop) (x - y) x (sub_add_cancel x y)
    filter_upwards [ht.eventually hmin] with w hw
    simpa only [add_sub_cancel_right, sub_add_cancel] using hw
  exact hh.add_le_of_isLocalMinOn_sub (mem_univ _) hg.hasFDerivWithinAt hmin' w (mem_univ w)

/-- The form of `TauCeti.add_le_of_mem_contactSet_sub` for a pairing `B`: if `p` represents the
derivative `φ'` of the potential at a contact point `(x, y)`, then `p ∈ ∂h(x - y)`. -/
theorem mem_subdifferential_of_mem_contactSet_sub {F : Type*} [AddCommMonoid F] [Module ℝ F]
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {φ' : E →L[ℝ] ℝ} {p : F} (hh : ConvexOn ℝ univ h)
    (hfeas : ∀ᶠ x' in 𝓝 x, φ x' + ψ y ≤ (h (x' - y) : EReal))
    (hfin : ∀ᶠ x' in 𝓝 x, φ x' ≠ ⊥) (hxy : (x, y) ∈ contactSet (fun z ↦ h (z.1 - z.2)) φ ψ)
    (hφ : HasFDerivAt (fun x' ↦ (φ x').toReal) φ' x) (hp : ∀ v, φ' v = B v p) :
    p ∈ subdifferential B (fun z ↦ (h z : EReal)) (x - y) :=
  (mem_subdifferential_coe_iff B h).2 fun w ↦
    hp (w - (x - y)) ▸ add_le_of_mem_contactSet_sub hh hfeas hfin hxy hφ w

/-! ### Uniqueness of contact partners -/

/-- **Contact partners for a strictly convex displacement cost.** Let `h` be strictly convex. If
the potential satisfies the dual constraint near `x` against every `y`, does not take the value `⊥`
near `x`, and is differentiable at `x`, then `x` has at most one contact partner. -/
theorem subsingleton_setOf_mem_contactSet_of_strictConvexOn (hh : StrictConvexOn ℝ univ h)
    (hfeas : ∀ y, ∀ᶠ x' in 𝓝 x, φ x' + ψ y ≤ (h (x' - y) : EReal))
    (hfin : ∀ᶠ x' in 𝓝 x, φ x' ≠ ⊥) (hφ : DifferentiableAt ℝ (fun x' ↦ (φ x').toReal) x) :
    {y | (x, y) ∈ contactSet (fun z ↦ h (z.1 - z.2)) φ ψ}.Subsingleton := by
  have hsub : ∀ y, (x, y) ∈ contactSet (fun z ↦ h (z.1 - z.2)) φ ψ →
      fderiv ℝ (fun x' ↦ (φ x').toReal) x ∈
        subdifferential (topDualPairing ℝ E).flip (fun z ↦ (h z : EReal)) (x - y) :=
    fun y hy ↦ mem_subdifferential_of_mem_contactSet_sub _ hh.convexOn (hfeas y) hfin hy
      hφ.hasFDerivAt fun v ↦ by simp
  intro y₁ h₁ y₂ h₂
  exact sub_right_injective <|
    hh.eq_of_mem_subdifferential _ (mem_univ _) (mem_univ _) (hsub y₁ h₁) (hsub y₂ h₂)


variable [MeasurableSpace E] {μ ν : Measure E}

/-- **Gangbo–McCann uniqueness of contact partners.** For a strictly convex `h` and a dual
feasible pair whose first potential is finite near, and differentiable at, `μ`-almost every
point, the contact fibres of the cost `h (x - y)` are subsingletons for `μ`-almost every `x`. -/
theorem ae_subsingleton_setOf_mem_contactSet_of_strictConvexOn (μ : Measure E)
    (hh : StrictConvexOn ℝ univ h) (hfeas : ∀ x y, φ x + ψ y ≤ (h (x - y) : EReal))
    (hφ : ∀ᵐ x ∂μ,
      (∀ᶠ x' in 𝓝 x, φ x' ≠ ⊥) ∧ DifferentiableAt ℝ (fun x' ↦ (φ x').toReal) x) :
    ∀ᵐ x ∂μ, {y | (x, y) ∈ contactSet (fun z ↦ h (z.1 - z.2)) φ ψ}.Subsingleton := by
  filter_upwards [hφ] with x ⟨hfin, hdiff⟩
  exact subsingleton_setOf_mem_contactSet_of_strictConvexOn hh
    (fun y ↦ .of_forall fun x' ↦ hfeas x' y) hfin hdiff

variable [StandardBorelSpace E] {π : Measure (E × E)}

namespace IsCoupling

/-- **Couplings on a strictly convex contact set are induced by maps.** Let `h` be strictly convex
and let `(φ, ψ)` be a dual feasible pair for the cost `h (x - y)` whose first potential is finite
near, and differentiable at, `μ`-almost every point. A finite coupling of `μ` and `ν` concentrated
on the contact set is the graph plan of a measurable map `T` pushing `μ` to `ν`. For `μ`-almost
every `x`, the pair `(x, T x)` is a contact point and the derivative of `φ` at `x` is a subgradient
of `h` at `x - T x`. -/
theorem exists_graphPlan_of_ae_mem_contactSet_of_strictConvexOn [IsFiniteMeasure π]
    (hπ : IsCoupling π μ ν) (hh : StrictConvexOn ℝ univ h)
    (hfeas : ∀ x y, φ x + ψ y ≤ (h (x - y) : EReal))
    (hφ : ∀ᵐ x ∂μ,
      (∀ᶠ x' in 𝓝 x, φ x' ≠ ⊥) ∧ DifferentiableAt ℝ (fun x' ↦ (φ x').toReal) x)
    (hcon : ∀ᵐ z ∂π, z ∈ contactSet (fun z ↦ h (z.1 - z.2)) φ ψ) :
    ∃ T : E → E, Measurable T ∧ HasLaw T ν μ ∧ π = graphPlan T μ ∧
      ∀ᵐ x ∂μ, (x, T x) ∈ contactSet (fun z ↦ h (z.1 - z.2)) φ ψ ∧
        ∀ w, h (x - T x) + fderiv ℝ (fun x' ↦ (φ x').toReal) x (w - (x - T x)) ≤ h w := by
  obtain ⟨T, hT, hLaw, hgraph⟩ := hπ.exists_graphPlan_of_ae_exists_condKernel_eq_dirac
    ((hπ.ae_exists_condKernel_eq_dirac hcon
      (ae_subsingleton_setOf_mem_contactSet_of_strictConvexOn μ hh hfeas hφ)).mono
        fun _ ⟨y, _, hy⟩ ↦ ⟨y, hy⟩)
  have hcontact : ∀ᵐ x ∂μ, (x, T x) ∈ contactSet (fun z ↦ h (z.1 - z.2)) φ ψ := by
    rw [hgraph, graphPlan_def] at hcon
    exact ae_of_ae_map (aemeasurable_prodMk_self hT.aemeasurable) hcon
  refine ⟨T, hT, hLaw, hgraph, ?_⟩
  filter_upwards [hcontact, hφ] with x hx ⟨hfin, hdiff⟩
  exact ⟨hx, add_le_of_mem_contactSet_sub hh.convexOn (.of_forall fun x' ↦ hfeas x' (T x)) hfin
    hx hdiff.hasFDerivAt⟩

/-- **Uniqueness of couplings on a strictly convex contact set.** Under the hypotheses of
`TauCeti.IsCoupling.exists_graphPlan_of_ae_mem_contactSet_of_strictConvexOn`, two finite couplings
of the same source marginal `μ`, both concentrated on the contact set, are equal. In particular
their target marginals agree. -/
theorem eq_of_ae_mem_contactSet_of_strictConvexOn [IsFiniteMeasure π] {π' : Measure (E × E)}
    {ν' : Measure E} (hπ : IsCoupling π μ ν) (hπ' : IsCoupling π' μ ν')
    (hh : StrictConvexOn ℝ univ h) (hfeas : ∀ x y, φ x + ψ y ≤ (h (x - y) : EReal))
    (hφ : ∀ᵐ x ∂μ,
      (∀ᶠ x' in 𝓝 x, φ x' ≠ ⊥) ∧ DifferentiableAt ℝ (fun x' ↦ (φ x').toReal) x)
    (hcon : ∀ᵐ z ∂π, z ∈ contactSet (fun z ↦ h (z.1 - z.2)) φ ψ)
    (hcon' : ∀ᵐ z ∂π', z ∈ contactSet (fun z ↦ h (z.1 - z.2)) φ ψ) : π = π' :=
  hπ.eq_of_ae_mem_of_subsingleton hπ' hcon hcon'
    (ae_subsingleton_setOf_mem_contactSet_of_strictConvexOn μ hh hfeas hφ)

end IsCoupling

/-- **Uniqueness of the optimal plan for a strictly convex displacement cost.** Let `h` be
nonnegative and strictly convex. If `π` is certified optimal for the cost `h (x - y)` by a dual
pair `(φ, ψ)` whose first potential is differentiable `μ`-almost everywhere, then every optimal
coupling of `μ` and `ν` whose cost is almost everywhere measurable is equal to `π`. -/
theorem IsDualCertificate.eq_of_isOptimalCoupling_of_strictConvexOn [IsFiniteMeasure μ]
    {φ ψ : E → ℝ} {σ : Measure (E × E)} (hh₀ : ∀ z, 0 ≤ h z) (hh : StrictConvexOn ℝ univ h)
    (hcert : IsDualCertificate (fun z ↦ ENNReal.ofReal (h (z.1 - z.2))) π μ ν φ ψ)
    (hσ : IsOptimalCoupling (fun z ↦ ENNReal.ofReal (h (z.1 - z.2))) σ μ ν)
    (hcσ : AEMeasurable (fun z ↦ ENNReal.ofReal (h (z.1 - z.2))) σ)
    (hφ : ∀ᵐ x ∂μ, DifferentiableAt ℝ φ x) : σ = π := by
  have hc₀ : ∀ z : E × E, 0 ≤ h (z.1 - z.2) := fun z ↦ hh₀ _
  have hσ' := hcert.of_isOptimalCoupling hcσ hσ
  have := hcert.toIsCoupling.isFiniteMeasure
  have := hσ.toIsCoupling.isFiniteMeasure
  have hfeas : ∀ x y, (φ x : EReal) + (ψ y : EReal) ≤ (h (x - y) : EReal) := fun x y ↦ by
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    exact (dualFeasible_ofReal_iff hc₀ φ ψ).1 hcert.dualFeasible x y
  have hcon := hcert.ae_mem_dualContactSet
  have hcon' := hσ'.ae_mem_dualContactSet
  rw [dualContactSet_ofReal hc₀] at hcon hcon'
  exact hσ.toIsCoupling.eq_of_ae_mem_contactSet_of_strictConvexOn hcert.toIsCoupling hh hfeas
    (hφ.mono fun x hx ↦ ⟨.of_forall fun _ ↦ EReal.coe_ne_bot _, by simpa using hx⟩) hcon' hcon

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {h : E → ℝ} {φ ψ : E → EReal} {x y : E}

/-- At a contact point of a convex displacement cost on a real inner product space, the gradient
of the potential is a subgradient of `h` at `x - y`. -/
theorem gradient_mem_subdifferential_of_mem_contactSet_sub (hh : ConvexOn ℝ univ h)
    (hfeas : ∀ᶠ x' in 𝓝 x, φ x' + ψ y ≤ (h (x' - y) : EReal))
    (hfin : ∀ᶠ x' in 𝓝 x, φ x' ≠ ⊥) (hxy : (x, y) ∈ contactSet (fun z ↦ h (z.1 - z.2)) φ ψ)
    (hφ : DifferentiableAt ℝ (fun x' ↦ (φ x').toReal) x) :
    ∇ (fun x' ↦ (φ x').toReal) x ∈ subdifferential (innerₗ E) (fun z ↦ (h z : EReal)) (x - y) :=
  mem_subdifferential_of_mem_contactSet_sub (innerₗ E) hh hfeas hfin hxy hφ.hasFDerivAt
    fun v ↦ by rw [← toDual_gradient, toDual_apply_apply, innerₗ_apply_apply, real_inner_comm]

/-- **The Gangbo–McCann formula.** Let `h` be convex on a real inner product space and let
`(x, y)` be a contact point at which the potential is differentiable. If the Legendre–Fenchel
conjugate `h⋆` is finite near `∇φ x` and differentiable there, then `x - y = ∇h⋆(∇φ x)`, that is
`y = x - ∇h⋆(∇φ x)`. -/
theorem gradient_fenchelConjugate_eq_sub_of_mem_contactSet (hh : ConvexOn ℝ univ h)
    (hfeas : ∀ᶠ x' in 𝓝 x, φ x' + ψ y ≤ (h (x' - y) : EReal))
    (hfin : ∀ᶠ x' in 𝓝 x, φ x' ≠ ⊥) (hxy : (x, y) ∈ contactSet (fun z ↦ h (z.1 - z.2)) φ ψ)
    (hφ : DifferentiableAt ℝ (fun x' ↦ (φ x').toReal) x)
    (hdom : ∀ᶠ q in 𝓝 (∇ (fun x' ↦ (φ x').toReal) x),
      fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q ≠ ⊤)
    (hconj : DifferentiableAt ℝ
      (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal)
      (∇ (fun x' ↦ (φ x').toReal) x)) :
    ∇ (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal)
      (∇ (fun x' ↦ (φ x').toReal) x) = x - y := by
  have hmem := mem_subdifferential_fenchelConjugate_of_mem_subdifferential (innerₗ E)
    (gradient_mem_subdifferential_of_mem_contactSet_sub hh hfeas hfin hxy hφ)
  rw [flip_innerₗ] at hmem
  exact gradient_toReal_eq_of_mem_subdifferential hmem hdom hconj

end InnerProduct

end TauCeti
