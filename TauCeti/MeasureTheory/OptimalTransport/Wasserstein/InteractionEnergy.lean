/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.PotentialEnergy
public import TauCeti.Probability.Moments.Variance
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Convex.Strong
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp

/-!
# Interaction energy and its displacement convexity

The *interaction energy* of a measure `μ` in an interaction kernel `W : X × X → ℝ` is
`(1 / 2) ∫∫ W(x, y) dμ(x) dμ(y)`. It is one of the three basic energies on the Wasserstein space
(with the potential and internal energies), and the energy whose Wasserstein gradient flow is the
aggregation equation. It is the potential energy of `W / 2` against `μ ⊗ μ`
(`TauCeti.interactionEnergy`), so it inherits the extended-real conventions of
`TauCeti.potentialEnergy`: the value is `⊤` when the positive part of `W` has infinite integral.

On an additive group, a kernel of the form `W(x, y) = w(x - y)` gives an energy that is
invariant under translations of `μ` (`TauCeti.interactionEnergy_map_add_right`), and that is the
potential energy of `w / 2` against the law of `x - y` under `μ ⊗ μ`
(`TauCeti.interactionEnergy_comp_sub`). Along the interpolation `μ_t` of a plan `π`, the law of
`(1 - t) • x + t • y` under `π`, that difference law is the interpolation of the plan obtained by
pairing two independent copies of `π`, so the convexity inequality of the potential energy
applies to it. For an `m`-strongly convex `w` on a real normed space this gives
(`StrongConvexOn.interactionEnergy_map_le`)

`I(μ_t) ≤ (1 - t) I(π.fst) + t I(π.snd) - (m / 4) t (1 - t) ∫∫ ‖(x - y) - (x' - y')‖² dπ dπ`.

Convexity of `w` therefore makes the interaction energy `0`-geodesically convex on the
`2`-Wasserstein space `P₂(E)` of a separable Banach space
(`ConvexOn.geodesicallyConvex_interactionEnergy`). On a separable Hilbert space the double
integral is twice the variance of the displacement, and the remainder becomes
`(m / 2) t (1 - t) (W₂(μ₀, μ₁)² - ‖∫ x dμ₀ - ∫ x dμ₁‖²)`
(`StrongConvexOn.exists_isGeodesicSegment_interactionEnergy_le`): the modulus `m` survives only
after subtracting the squared distance between the two means, in particular between laws with the
same mean (`StrongConvexOn.exists_isGeodesicSegment_convexAlong_interactionEnergy`).

This loss is unavoidable. Translation invariance means the energy cannot see the distance between
the means: if `w` is smallest at `0`, as a convex even `w` is, then for `m > 0` the interaction
energy is never `m`-geodesically convex on `P₂(E)`, however strongly convex `w` is
(`TauCeti.not_geodesicallyConvex_interactionEnergy`). Two Dirac masses already witness this.

The first variation of the interaction energy at `μ` is described by the *interaction gradient*
`ξ x = (1 / 2) ∫ (∇w (x - y) - ∇w (y - x)) dμ(y)` (`TauCeti.interactionGradient`), the convolution
`∫ ∇w (x - y) dμ(y)` when `w` is even (`TauCeti.interactionGradient_of_even`). For a
differentiable `m`-strongly convex `w`, with any real `m`, whose gradient grows at most linearly,
the first-order condition of `w` at `x - x'` towards `y - y'`, integrated over two independent
pairs `(x, y)` and `(x', y')` drawn from a coupling `γ` of `μ` and `ν`, gives
(`StrongConvexOn.interactionEnergy_add_le`)

`I(ν) ≥ I(μ) + ∫ ⟪ξ x, y - x⟫ dγ + (m / 4) ∫∫ ‖(x - y) - (x' - y')‖² dγ dγ`.

The linear term is identified by exchanging the two pairs and integrating out the second one. This
is the inequality that makes `ξ` a Wasserstein subgradient of the interaction energy
(`StrongConvexOn.mem_wassersteinSubdifferential_interactionEnergy`).

## Main definitions

* `TauCeti.interactionEnergy W μ`: the interaction energy `(1 / 2) ∫∫ W d(μ ⊗ μ)`, as an extended
  real.
* `TauCeti.interactionGradient w μ`: the interaction gradient
  `x ↦ (1 / 2) ∫ (∇w (x - y) - ∇w (y - x)) dμ(y)` of a kernel `w (x - y)`.

## Main results

* `TauCeti.interactionEnergy_of_integrable`: for an integrable kernel, the interaction energy is
  half the Bochner integral of the kernel.
* `TauCeti.interactionEnergy_eq_integral_prod`: for an integrable kernel, the interaction energy
  as an integral over two independent copies of a measure carried to the law.
* `TauCeti.interactionEnergy_map`: the interaction energy of a pushforward measure.
* `TauCeti.interactionEnergy_map_add_right`: the interaction energy of a difference kernel is
  invariant under translation.
* `StrongConvexOn.interactionEnergy_map_le`: the convexity inequality of the interaction energy of
  an `m`-strongly convex difference kernel along the interpolation of a plan.
* `ConvexOn.geodesicallyConvex_interactionEnergy`: the interaction energy of a convex difference
  kernel is geodesically convex on `P₂(E)`.
* `StrongConvexOn.exists_isGeodesicSegment_interactionEnergy_le`: on a separable Hilbert space, the
  displacement convexity inequality with the variance-type remainder.
* `TauCeti.not_geodesicallyConvex_interactionEnergy`: no positive modulus of geodesic convexity.
* `TauCeti.interactionGradient_of_even`: for an even kernel the interaction gradient is the
  convolution `∫ ∇w (x - y) dμ(y)`.
* `TauCeti.stronglyMeasurable_interactionGradient`: the interaction gradient is strongly
  measurable.
* `TauCeti.memLp_interactionGradient`: the interaction gradient at a law with finite second moment
  is square integrable.
* `StrongConvexOn.interactionEnergy_add_le`: the first-order inequality of the interaction energy
  along a coupling.

## References

* R. McCann, *A convexity principle for interacting gases*, Adv. Math. 128 (1997), 153--179.
* J. A. Carrillo, R. J. McCann, C. Villani, *Kinetic equilibration rates for granular media and
  related equations: entropy dissipation and mass transportation estimates*, Rev. Mat.
  Iberoamericana 19 (2003), 971--1018.
* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, §9.3 and §10.4.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §7.3.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace TauCeti

section Definition

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {W W' : X × X → ℝ}
  {μ : Measure X}

/-- The *interaction energy* `(1 / 2) ∫∫ W(x, y) dμ(x) dμ(y)` of a measure `μ` in an interaction
kernel `W : X × X → ℝ`, as an extended real: the potential energy of `W / 2` against `μ ⊗ μ`. It is
`⊤` when the positive part of `W` has infinite integral against `μ ⊗ μ`. -/
def interactionEnergy (W : X × X → ℝ) (μ : Measure X) : EReal :=
  potentialEnergy (fun z ↦ W z / 2) (μ.prod μ)

/-- The interaction energy is the potential energy of half the kernel against the product
measure. -/
theorem interactionEnergy_def :
    interactionEnergy W μ = potentialEnergy (fun z ↦ W z / 2) (μ.prod μ) :=
  (rfl)

/-- For an integrable kernel, the interaction energy is half the Bochner integral of the kernel
against the product measure. -/
theorem interactionEnergy_of_integrable (h : Integrable W (μ.prod μ)) :
    interactionEnergy W μ = ((∫ z, W z ∂μ.prod μ) / 2 : ℝ) := by
  rw [interactionEnergy, potentialEnergy_of_integrable (h.div_const 2), integral_div]

/-- For an integrable kernel, the interaction energy of `μ` as half the integral of the kernel over
two independent copies of a measure `γ` carried to `μ` by a measure-preserving map `f`. -/
theorem interactionEnergy_eq_integral_prod (h : Integrable W (μ.prod μ))
    {α : Type*} [MeasurableSpace α] {γ : Measure α} [SFinite γ] {f : α → X}
    (hf : MeasurePreserving f γ μ) :
    interactionEnergy W μ = ((∫ p, W (f p.1, f p.2) ∂γ.prod γ) / 2 : ℝ) := by
  have hmp := hf.prod hf
  rw [interactionEnergy_of_integrable h, ← hmp.map_eq,
    integral_map hmp.measurable.aemeasurable (hmp.map_eq ▸ h.aestronglyMeasurable), Prod.map_def]

/-- The interaction energy is monotone in the kernel. -/
theorem interactionEnergy_mono (h : W ≤ᵐ[μ.prod μ] W') :
    interactionEnergy W μ ≤ interactionEnergy W' μ :=
  potentialEnergy_mono (h.mono fun _ hz ↦ div_le_div_of_nonneg_right hz zero_le_two)

/-- A lower bound on the kernel gives a lower bound on the interaction energy of a probability
measure. -/
theorem le_interactionEnergy [IsProbabilityMeasure μ] {c : ℝ} (h : ∀ᵐ z ∂μ.prod μ, c ≤ W z) :
    ((c / 2 : ℝ) : EReal) ≤ interactionEnergy W μ := by
  have hc := interactionEnergy_mono (W := fun _ ↦ c) h
  rwa [interactionEnergy_of_integrable (integrable_const c), integral_const, probReal_univ,
    one_smul] at hc

/-- The interaction energy of the zero measure is `0`. -/
@[simp]
theorem interactionEnergy_zero_measure (W : X × X → ℝ) : interactionEnergy W 0 = 0 := by
  simp [interactionEnergy]

/-- The interaction energy of a Dirac mass at `x` is `W (x, x) / 2`. -/
@[simp]
theorem interactionEnergy_dirac [MeasurableSingletonClass X] (W : X × X → ℝ) (x : X) :
    interactionEnergy W (Measure.dirac x) = (W (x, x) / 2 : ℝ) := by
  rw [interactionEnergy, Measure.dirac_prod_dirac, potentialEnergy_dirac]

/-- The interaction energy of a pushforward measure is the interaction energy of the pulled-back
kernel. -/
theorem interactionEnergy_map {f : Y → X} {ν : Measure Y} [SFinite ν] (hW : Measurable W)
    (hf : Measurable f) :
    interactionEnergy W (ν.map f) = interactionEnergy (fun z ↦ W (f z.1, f z.2)) ν := by
  rw [interactionEnergy, Measure.map_prod_map ν ν hf hf,
    potentialEnergy_map (hW.div_const 2) (hf.prodMap hf).aemeasurable, interactionEnergy]
  simp only [Prod.map_apply']

end Definition

section AddGroup

variable {G : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableSub₂ G] {w : G → ℝ}
  {μ : Measure G}

/-- For a kernel `w (x - y)`, the interaction energy is the potential energy of `w / 2` against
the law of `x - y` under `μ ⊗ μ`. -/
theorem interactionEnergy_comp_sub (hw : Measurable w) :
    interactionEnergy (fun z ↦ w (z.1 - z.2)) μ =
      potentialEnergy (fun x ↦ w x / 2) ((μ.prod μ).map fun z ↦ z.1 - z.2) := by
  rw [interactionEnergy, potentialEnergy_map (hw.div_const 2) measurable_sub.aemeasurable]

/-- **Translation invariance.** For a kernel `w (x - y)`, the interaction energy is unchanged when
the measure is translated. -/
theorem interactionEnergy_map_add_right [MeasurableAdd G] [SFinite μ] (hw : Measurable w)
    (a : G) :
    interactionEnergy (fun z ↦ w (z.1 - z.2)) (μ.map (· + a)) =
      interactionEnergy (fun z ↦ w (z.1 - z.2)) μ := by
  rw [interactionEnergy_map (W := fun z ↦ w (z.1 - z.2)) (hw.comp measurable_sub)
    (measurable_add_const a)]
  simp only [add_sub_add_right_eq_sub]

end AddGroup

section Growth

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]

/-- For a kernel `w (x - y)` whose negative part grows at most quadratically, the interaction
energy of a finite measure with finite second moment is `≠ ⊥`. -/
theorem interactionEnergy_ne_bot_of_hasFiniteMoment {w : E → ℝ} {μ : Measure E}
    [IsFiniteMeasure μ] (hμ : HasFiniteMoment 2 μ) {A B : ℝ}
    (hwAB : ∀ x, -(A + B * ‖x‖ ^ 2) ≤ w x) :
    interactionEnergy (fun z ↦ w (z.1 - z.2)) μ ≠ ⊥ := by
  -- A nonpositive quadratic minorant, integrable against `μ`.
  set g : E → ℝ := fun x ↦ -(|A| / 4 + max B 0 * ‖x‖ ^ 2) with hg_def
  have hg : Integrable g μ := by
    refine (integrable_iff_potentialEnergy_ne_top_and_ne_bot (by fun_prop)).2
      ⟨?_, potentialEnergy_ne_bot_of_hasFiniteMoment hμ fun x ↦ le_rfl⟩
    have h0 (x : E) : ENNReal.ofReal (g x) = 0 :=
      ENNReal.ofReal_eq_zero.2 (neg_nonpos.2 (by positivity))
    simp [Ne, potentialEnergy_eq_top_iff, h0]
  refine potentialEnergy_ne_bot_of_le ((hg.comp_fst μ).add (hg.comp_snd μ))
    (.of_forall fun z ↦ ?_)
  have h₁ := hwAB (z.1 - z.2)
  have h₂ : ‖z.1 - z.2‖ ^ 2 ≤ 2 * ‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2 := by
    nlinarith [norm_sub_le z.1 z.2, norm_nonneg (z.1 - z.2), sq_nonneg (‖z.1‖ - ‖z.2‖)]
  have h₃ : B * ‖z.1 - z.2‖ ^ 2 ≤ max B 0 * ‖z.1 - z.2‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  have h₄ := mul_le_mul_of_nonneg_left h₂ (le_max_right B 0)
  simp only [Pi.add_apply, hg_def]
  linarith [le_abs_self A]

end Growth

section Convexity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {w : E → ℝ} {m : ℝ}

/-- **Convexity of the interaction energy along a plan.** If `w` is `m`-strongly convex, then along
the interpolation `t ↦ μ_t`, with `μ_t` the law of `(1 - t) • x + t • y` under a measure `π` on
`E × E`, the interaction energy of the kernel `w (x - y)` satisfies, for `t ∈ [0, 1]`,
`I(μ_t) ≤ (1 - t) I(π.fst) + t I(π.snd) - (m / 4) t (1 - t) ∫∫ ‖(x - y) - (x' - y')‖² dπ dπ`,
the double integral running over two independent pairs `(x, y)` and `(x', y')` drawn from `π`.
The interaction energies of the two marginals must not be `⊥`, and the integrand of the double
integral must be integrable. -/
theorem _root_.StrongConvexOn.interactionEnergy_map_le (hw : StrongConvexOn univ m w)
    (hwm : Measurable w) {π : Measure (E × E)} [SFinite π]
    (h₀ : interactionEnergy (fun z ↦ w (z.1 - z.2)) π.fst ≠ ⊥)
    (h₁ : interactionEnergy (fun z ↦ w (z.1 - z.2)) π.snd ≠ ⊥)
    (hπ : Integrable (fun z : (E × E) × (E × E) ↦ ‖(z.1.1 - z.1.2) - (z.2.1 - z.2.2)‖ ^ 2)
      (π.prod π))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    interactionEnergy (fun z ↦ w (z.1 - z.2)) (π.map fun z ↦ (1 - t) • z.1 + t • z.2) ≤
      ((1 - t : ℝ) : EReal) * interactionEnergy (fun z ↦ w (z.1 - z.2)) π.fst +
        (t : EReal) * interactionEnergy (fun z ↦ w (z.1 - z.2)) π.snd -
        ((m / 4 * t * (1 - t) *
          ∫ z, ‖(z.1.1 - z.1.2) - (z.2.1 - z.2.2)‖ ^ 2 ∂π.prod π : ℝ) : EReal) := by
  -- Pair two independent copies `(x, y)` and `(x', y')` of `π` into the plan `ρ` of
  -- `(x - x', y - y')`. Its marginals are the difference laws of the marginals of `π`, and its
  -- interpolation is the difference law of the interpolation of `π`.
  set D : (E × E) × (E × E) → E × E := fun z ↦ (z.1.1 - z.2.1, z.1.2 - z.2.2) with hD
  have hDm : Measurable D := by fun_prop
  set ρ := (π.prod π).map D
  have hρ (f : E × E → E) (hf : Measurable f) (hfD : ∀ z, f (D z) = f z.1 - f z.2) :
      ρ.map f = ((π.map f).prod (π.map f)).map fun z ↦ z.1 - z.2 := by
    rw [Measure.map_map hf hDm, Measure.map_prod_map π π hf hf,
      Measure.map_map measurable_sub (hf.prodMap hf)]
    congr 1
    ext z
    exact hfD z
  have hfst : ρ.fst = (π.fst.prod π.fst).map fun z ↦ z.1 - z.2 :=
    hρ Prod.fst measurable_fst fun _ ↦ rfl
  have hsnd : ρ.snd = (π.snd.prod π.snd).map fun z ↦ z.1 - z.2 :=
    hρ Prod.snd measurable_snd fun _ ↦ rfl
  have hinterp : ρ.map (fun z ↦ (1 - t) • z.1 + t • z.2) =
      ((π.map fun z ↦ (1 - t) • z.1 + t • z.2).prod
        (π.map fun z ↦ (1 - t) • z.1 + t • z.2)).map fun z ↦ z.1 - z.2 :=
    hρ _ (by fun_prop) fun z ↦ by simp only [hD, smul_sub]; abel
  -- `w / 2` is `(m / 2)`-strongly convex.
  have hw₂ : StrongConvexOn univ (m / 2) fun x ↦ w x / 2 := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
    have := hw.2 (mem_univ x) (mem_univ y) ha hb hab
    simp only [smul_eq_mul] at this ⊢
    linarith
  have hDsub (z : (E × E) × (E × E)) : (D z).1 - (D z).2 = (z.1.1 - z.1.2) - (z.2.1 - z.2.2) := by
    simp only [hD]
    abel
  have hnorm : ∫ z, ‖z.1 - z.2‖ ^ 2 ∂ρ =
      ∫ z, ‖(z.1.1 - z.1.2) - (z.2.1 - z.2.2)‖ ^ 2 ∂π.prod π := by
    rw [integral_map hDm.aemeasurable (by fun_prop)]
    simp only [hDsub]
  have hρint : Integrable (fun z : E × E ↦ ‖z.1 - z.2‖ ^ 2) ρ := by
    rw [integrable_map_measure (by fun_prop) hDm.aemeasurable]
    simpa only [Function.comp_def, hDsub] using hπ
  rw [interactionEnergy_comp_sub hwm, ← hfst] at h₀
  rw [interactionEnergy_comp_sub hwm, ← hsnd] at h₁
  simp only [interactionEnergy_comp_sub hwm]
  rw [← hfst, ← hsnd, ← hinterp, ← hnorm]
  convert hw₂.potentialEnergy_map_le (hwm.div_const 2) h₀ h₁ hρint ht using 4
  ring

variable [CompleteSpace E]

/-- **Displacement convexity of the interaction energy.** On a separable Banach space `E`, the
interaction energy of a kernel `w (x - y)`, for a convex measurable `w` whose negative part grows at
most quadratically, is geodesically convex on the `2`-Wasserstein space `P₂(E)`: two laws are joined
by a Wasserstein geodesic, the interpolation of an optimal plan, along which
`I(μ_t) ≤ (1 - t) I(μ₀) + t I(μ₁)`. -/
theorem _root_.ConvexOn.geodesicallyConvex_interactionEnergy (hw : ConvexOn ℝ univ w)
    (hwm : Measurable w) {A B : ℝ} (hwAB : ∀ x, -(A + B * ‖x‖ ^ 2) ≤ w x) :
    GeodesicallyConvex 0 fun μ : WassersteinSpace 2 E ↦
      interactionEnergy (fun z ↦ w (z.1 - z.2)) ((μ : ProbabilityMeasure E) : Measure E) := by
  rw [geodesicallyConvex_def]
  intro μ₀ μ₁ _ _
  obtain ⟨π, hπ, hmem, -, γ, hγ, hγt⟩ :=
    WassersteinSpace.exists_dist_sq_eq_integral_isGeodesicSegment_map_smul_add_smul μ₀ μ₁
  have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  refine ⟨γ, hγ, hγ.convexAlong_iff.2 fun t ht ↦ ?_⟩
  rw [hγt t ht, ← hπ.fst_eq, ← hπ.snd_eq]
  refine ((strongConvexOn_zero.2 hw).interactionEnergy_map_le hwm
    (hπ.fst_eq ▸ interactionEnergy_ne_bot_of_hasFiniteMoment
      (WassersteinSpace.hasFiniteMoment μ₀) hwAB)
    (hπ.snd_eq ▸ interactionEnergy_ne_bot_of_hasFiniteMoment
      (WassersteinSpace.hasFiniteMoment μ₁) hwAB)
    hmem.integrable_norm_sub_sq_prod ht).trans_eq ?_
  simp

omit [NormedSpace ℝ E] in
/-- **No positive modulus.** If `w` is smallest at `0`, as a convex even function is, then for
`m > 0` the interaction energy of the kernel `w (x - y)` is not `m`-geodesically convex on the
`2`-Wasserstein space of a nontrivial normed space, however strongly convex `w` is. The energy of
every probability measure is at least `w 0 / 2`, the energy of each Dirac mass, while
`m`-convexity along a geodesic between two distinct Dirac masses would force a smaller value at its
midpoint. -/
theorem not_geodesicallyConvex_interactionEnergy [Nontrivial E] (hw : ∀ x, w 0 ≤ w x)
    (hm : 0 < m) :
    ¬ GeodesicallyConvex m fun μ : WassersteinSpace 2 E ↦
      interactionEnergy (fun z ↦ w (z.1 - z.2)) ((μ : ProbabilityMeasure E) : Measure E) := by
  intro h
  obtain ⟨a, ha⟩ := exists_ne (0 : E)
  -- The Dirac masses at `0` and `a`, as points of `P₂(E)`.
  let δ (x : E) : WassersteinSpace 2 E :=
    .mk ⟨Measure.dirac x, inferInstance⟩ (hasFiniteMoment_dirac 2 x)
  have hδ (x : E) : ((δ x : ProbabilityMeasure E) : Measure E) = Measure.dirac x :=
    congrArg ProbabilityMeasure.toMeasure (WassersteinSpace.coe_mk _ _)
  have hI (x : E) : interactionEnergy (fun z ↦ w (z.1 - z.2))
      ((δ x : ProbabilityMeasure E) : Measure E) = (w 0 / 2 : ℝ) := by
    rw [hδ, interactionEnergy_dirac, sub_self]
  have hdist : dist (δ 0) (δ a) = ‖a‖ := by
    rw [WassersteinSpace.dist_def, hδ, hδ, wassersteinEDist_dirac_dirac two_ne_zero,
      edist_dist, dist_zero_left, ENNReal.toReal_ofReal (norm_nonneg a)]
  obtain ⟨γ, hγ, hconv⟩ :=
    geodesicallyConvex_def.1 h (x := δ 0) (y := δ a) (by simp [hI]) (by simp [hI])
  have hmid := (hγ.convexAlong_iff.1 hconv) (1 / 2) ⟨by norm_num, by norm_num⟩
  have hlow := le_interactionEnergy (W := fun z ↦ w (z.1 - z.2))
    (μ := ((γ (1 / 2) : ProbabilityMeasure E) : Measure E)) (.of_forall fun z ↦ hw (z.1 - z.2))
  rw [hI, hI, hdist] at hmid
  have key := hlow.trans hmid
  have hreal : w 0 / 2 ≤ (1 - 1 / 2) * (w 0 / 2) + 1 / 2 * (w 0 / 2) -
      m / 2 * (1 / 2) * (1 - 1 / 2) * ‖a‖ ^ 2 := by
    exact_mod_cast key
  have : 0 < m / 2 * (1 / 2) * (1 - 1 / 2) * ‖a‖ ^ 2 := by
    have := norm_pos_iff.2 ha
    positivity
  linarith

end Convexity

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {w : E → ℝ} {m : ℝ}

/-- **Displacement convexity of the interaction energy, with the variance-type remainder.** On a
separable Hilbert space `E`, let `w` be `m`-strongly convex and measurable, with negative part
growing at most quadratically. Then any two laws `μ₀` and `μ₁` of `P₂(E)` are joined by a
Wasserstein geodesic, the interpolation of an optimal plan, along which the interaction energy of
the kernel `w (x - y)` satisfies
`I(μ_t) ≤ (1 - t) I(μ₀) + t I(μ₁) - (m / 2) t (1 - t) (W₂(μ₀, μ₁)² - ‖∫ x dμ₀ - ∫ x dμ₁‖²)`.
For `m > 0` the squared distance between the two means cannot be dropped from the remainder
(`TauCeti.not_geodesicallyConvex_interactionEnergy`). -/
theorem _root_.StrongConvexOn.exists_isGeodesicSegment_interactionEnergy_le
    (hw : StrongConvexOn univ m w) (hwm : Measurable w) {A B : ℝ}
    (hwAB : ∀ x, -(A + B * ‖x‖ ^ 2) ≤ w x) (μ₀ μ₁ : WassersteinSpace 2 E) :
    ∃ γ : ℝ → WassersteinSpace 2 E, IsGeodesicSegment γ μ₀ μ₁ ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      interactionEnergy (fun z ↦ w (z.1 - z.2)) ((γ t : ProbabilityMeasure E) : Measure E) ≤
        ((1 - t : ℝ) : EReal) *
            interactionEnergy (fun z ↦ w (z.1 - z.2)) ((μ₀ : ProbabilityMeasure E) : Measure E) +
          (t : EReal) *
            interactionEnergy (fun z ↦ w (z.1 - z.2)) ((μ₁ : ProbabilityMeasure E) : Measure E) -
          ((m / 2 * t * (1 - t) * (dist μ₀ μ₁ ^ 2 -
            ‖∫ x, x ∂((μ₀ : ProbabilityMeasure E) : Measure E) -
              ∫ x, x ∂((μ₁ : ProbabilityMeasure E) : Measure E)‖ ^ 2) : ℝ) : EReal) := by
  obtain ⟨π, hπ, hmem, hdist, γ, hγ, hγt⟩ :=
    WassersteinSpace.exists_dist_sq_eq_integral_isGeodesicSegment_map_smul_add_smul μ₀ μ₁
  have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  refine ⟨γ, hγ, fun t ht ↦ ?_⟩
  -- The mean displacement of `π` is the difference of the means of its marginals.
  have hmean : ∫ z, z.1 - z.2 ∂π =
      ∫ x, x ∂((μ₀ : ProbabilityMeasure E) : Measure E) -
        ∫ x, x ∂((μ₁ : ProbabilityMeasure E) : Measure E) := by
    have h₀ : Integrable (fun z : E × E ↦ z.1) π := hπ.integrable_comp_fst
      ((WassersteinSpace.hasFiniteMoment μ₀).memLp_id.integrable one_le_two)
    have h₁ : Integrable (fun z : E × E ↦ z.2) π := hπ.integrable_comp_snd
      ((WassersteinSpace.hasFiniteMoment μ₁).memLp_id.integrable one_le_two)
    rw [integral_sub h₀ h₁, hπ.integral_comp_fst (f := fun x ↦ x) aestronglyMeasurable_id,
      hπ.integral_comp_snd (f := fun x ↦ x) aestronglyMeasurable_id]
  -- The double integral of the remainder is twice the variance of the displacement.
  have hvar : ∫ z, ‖(z.1.1 - z.1.2) - (z.2.1 - z.2.2)‖ ^ 2 ∂π.prod π =
      2 * (dist μ₀ μ₁ ^ 2 -
        ‖∫ x, x ∂((μ₀ : ProbabilityMeasure E) : Measure E) -
          ∫ x, x ∂((μ₁ : ProbabilityMeasure E) : Measure E)‖ ^ 2) := by
    rw [integral_norm_sub_sq_prod hmem, probReal_univ, one_mul, hdist, hmean]
  have key := hw.interactionEnergy_map_le hwm
    (hπ.fst_eq ▸ interactionEnergy_ne_bot_of_hasFiniteMoment
      (WassersteinSpace.hasFiniteMoment μ₀) hwAB)
    (hπ.snd_eq ▸ interactionEnergy_ne_bot_of_hasFiniteMoment
      (WassersteinSpace.hasFiniteMoment μ₁) hwAB)
    hmem.integrable_norm_sub_sq_prod ht
  rw [hπ.fst_eq, hπ.snd_eq, hvar] at key
  rw [hγt t ht]
  refine key.trans_eq ?_
  congr 2
  ring

/-- **The fixed-mean class.** On a separable Hilbert space, for an `m`-strongly convex measurable
`w` with negative part growing at most quadratically, two laws of `P₂(E)` with the same mean are
joined by a Wasserstein geodesic along which the interaction energy of the kernel `w (x - y)` is
`m`-convex. -/
theorem _root_.StrongConvexOn.exists_isGeodesicSegment_convexAlong_interactionEnergy
    (hw : StrongConvexOn univ m w) (hwm : Measurable w) {A B : ℝ}
    (hwAB : ∀ x, -(A + B * ‖x‖ ^ 2) ≤ w x) {μ₀ μ₁ : WassersteinSpace 2 E}
    (hmean : ∫ x, x ∂((μ₀ : ProbabilityMeasure E) : Measure E) =
      ∫ x, x ∂((μ₁ : ProbabilityMeasure E) : Measure E)) :
    ∃ γ : ℝ → WassersteinSpace 2 E, IsGeodesicSegment γ μ₀ μ₁ ∧
      ConvexAlong m (fun μ : WassersteinSpace 2 E ↦
        interactionEnergy (fun z ↦ w (z.1 - z.2)) ((μ : ProbabilityMeasure E) : Measure E)) γ := by
  obtain ⟨γ, hγ, hle⟩ := hw.exists_isGeodesicSegment_interactionEnergy_le hwm hwAB μ₀ μ₁
  refine ⟨γ, hγ, hγ.convexAlong_iff.2 fun t ht ↦ ?_⟩
  simpa [hmean] using hle t ht

section FirstVariation

variable {C : ℝ} {μ ν : Measure E}

/-- The *interaction gradient* of a kernel `w (x - y)` at a measure `μ`: the vector field
`x ↦ (1 / 2) ∫ (∇w (x - y) - ∇w (y - x)) dμ(y)`, the gradient of the symmetrized kernel
`(w z + w (-z)) / 2` convolved with `μ`. For a differentiable semiconvex `w` whose gradient grows
at most linearly it is a Wasserstein subgradient of the interaction energy
(`StrongConvexOn.mem_wassersteinSubdifferential_interactionEnergy`). For an even kernel `∇w` is
odd, and the field is the convolution `∫ ∇w (x - y) dμ(y)` (`interactionGradient_of_even`). -/
def interactionGradient (w : E → ℝ) (μ : Measure E) (x : E) : E :=
  (2 : ℝ)⁻¹ • ∫ y, (gradient w (x - y) - gradient w (y - x)) ∂μ

omit [BorelSpace E] [SecondCountableTopology E] in
/-- The defining formula of the interaction gradient. -/
theorem interactionGradient_def (w : E → ℝ) (μ : Measure E) (x : E) :
    interactionGradient w μ x = (2 : ℝ)⁻¹ • ∫ y, (gradient w (x - y) - gradient w (y - x)) ∂μ :=
  (rfl)

/-- The interaction gradient at a Dirac mass at `a` is `(∇w (x - a) - ∇w (a - x)) / 2`. -/
@[simp]
theorem interactionGradient_dirac (w : E → ℝ) (a x : E) :
    interactionGradient w (Measure.dirac a) x =
      (2 : ℝ)⁻¹ • (gradient w (x - a) - gradient w (a - x)) := by
  rw [interactionGradient_def, integral_dirac]

omit [BorelSpace E] [SecondCountableTopology E] in
/-- For an even kernel, `w (-z) = w z`, the interaction gradient is the convolution
`x ↦ ∫ ∇w (x - y) dμ(y)`, since the gradient of an even function is odd. -/
theorem interactionGradient_of_even (hw : ∀ z, w (-z) = w z) (μ : Measure E) (x : E) :
    interactionGradient w μ x = ∫ y, gradient w (x - y) ∂μ := by
  have h (y : E) : gradient w (x - y) - gradient w (y - x) = (2 : ℝ) • gradient w (x - y) := by
    rw [← neg_sub x y, gradient_neg_of_even hw, sub_neg_eq_add, two_smul]
  simp_rw [interactionGradient_def, h, integral_smul, smul_smul]
  norm_num

/-- The interaction gradient at an s-finite measure is strongly measurable. -/
theorem stronglyMeasurable_interactionGradient (w : E → ℝ) (μ : Measure E) [SFinite μ] :
    StronglyMeasurable (interactionGradient w μ) := by
  have : StronglyMeasurable fun z : E × E ↦ gradient w (z.1 - z.2) - gradient w (z.2 - z.1) :=
    (((measurable_gradient w).comp (by fun_prop)).sub
      ((measurable_gradient w).comp (by fun_prop))).stronglyMeasurable
  exact this.integral_prod_right'.const_smul _

/-- For a gradient of linear growth and a finite measure with finite second moment, the integrand
of the interaction gradient is integrable at every point. -/
private theorem integrable_gradient_sub_sub [IsFiniteMeasure μ]
    (hw' : ∀ x, ‖gradient w x‖ ≤ C * (1 + ‖x‖)) (hμ : HasFiniteMoment 2 μ) (x : E) :
    Integrable (fun y ↦ gradient w (x - y) - gradient w (y - x)) μ := by
  have hg := (measurable_gradient w).stronglyMeasurable
  have h₁ := ((memLp_const x).sub hμ.memLp_id).comp_of_norm_le_mul_one_add hg hw'
  have h₂ := (hμ.memLp_id.sub (memLp_const x)).comp_of_norm_le_mul_one_add hg hw'
  exact (h₁.integrable one_le_two).sub (h₂.integrable one_le_two)

/-- For a gradient of linear growth, `‖∇w z‖ ≤ C (1 + ‖z‖)`, and a finite measure `μ` with finite
second moment, the interaction gradient lies in `L²(μ; E)`. -/
theorem memLp_interactionGradient [IsFiniteMeasure μ]
    (hw' : ∀ x, ‖gradient w x‖ ≤ C * (1 + ‖x‖)) (hμ : HasFiniteMoment 2 μ) :
    MemLp (interactionGradient w μ) 2 μ := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hw' 0)
  have hn : Integrable (fun y : E ↦ ‖y‖) μ := (hμ.memLp_id.integrable one_le_two).norm
  -- The field is bounded by an affine function of `‖x‖`.
  have hbound : MemLp (fun x : E ↦ C * (μ.real univ * (1 + ‖x‖) + ∫ y, ‖y‖ ∂μ)) 2 μ :=
    ((((memLp_const 1).add hμ.memLp_id.norm).const_mul _).add (memLp_const _)).const_mul C
  refine hbound.of_le (stronglyMeasurable_interactionGradient w μ).aestronglyMeasurable
    (.of_forall fun x ↦ ?_)
  have hle : ∀ y, ‖gradient w (x - y) - gradient w (y - x)‖ ≤ 2 * C * (1 + ‖x‖ + ‖y‖) := by
    intro y
    have h₁ := hw' (x - y)
    have h₂ := hw' (y - x)
    have h₃ := norm_sub_le x y
    have h₄ := norm_sub_le y x
    calc _ ≤ ‖gradient w (x - y)‖ + ‖gradient w (y - x)‖ := norm_sub_le _ _
      _ ≤ _ := by nlinarith
  have hint : ∫ y, 2 * C * (1 + ‖x‖ + ‖y‖) ∂μ =
      2 * (C * (μ.real univ * (1 + ‖x‖) + ∫ y, ‖y‖ ∂μ)) := by
    rw [integral_const_mul, integral_add (integrable_const _) hn, integral_const, smul_eq_mul]
    ring
  rw [interactionGradient_def, norm_smul, Real.norm_eq_abs,
    Real.norm_of_nonneg (by positivity), abs_of_pos (by norm_num)]
  have hgi : Integrable (fun y ↦ 2 * C * (1 + ‖x‖ + ‖y‖)) μ :=
    ((integrable_const _).add hn).const_mul _
  have := norm_integral_le_of_norm_le hgi (.of_forall hle)
  rw [hint] at this
  linarith

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The first-order condition of the `m`-strong convexity of `w` at `x - x'` towards `y - y'`, for
two pairs `p = ((x, y), (x', y'))`, with the linear term split along the two pairs. -/
private theorem add_inner_sub_inner_add_le (hw : StrongConvexOn univ m w)
    (hwd : Differentiable ℝ w) (p : (E × E) × (E × E)) :
    w (p.1.1 - p.2.1) + (⟪gradient w (p.1.1 - p.2.1), p.1.2 - p.1.1⟫ -
      ⟪gradient w (p.1.1 - p.2.1), p.2.2 - p.2.1⟫) +
      m / 2 * ‖(p.1.1 - p.1.2) - (p.2.1 - p.2.2)‖ ^ 2 ≤ w (p.1.2 - p.2.2) := by
  have := hw.add_add_le_of_hasFDerivWithinAt (mem_univ (p.1.1 - p.2.1))
    (mem_univ (p.1.2 - p.2.2)) (hwd _).hasFDerivAt.hasFDerivWithinAt
  rw [← toDual_gradient, InnerProductSpace.toDual_apply_apply] at this
  have h₁ : p.1.2 - p.2.2 - (p.1.1 - p.2.1) = (p.1.2 - p.1.1) - (p.2.2 - p.2.1) := by abel
  have h₂ : ‖(p.1.2 - p.1.1) - (p.2.2 - p.2.1)‖ = ‖(p.1.1 - p.1.2) - (p.2.1 - p.2.2)‖ := by
    rw [← norm_neg]
    congr 1
    abel
  rwa [h₁, inner_sub_right, h₂] at this

/-- The linear term of the first-order inequality, integrated over two independent copies of a
finite coupling `γ` of `μ` and `ν`, is twice the pairing of the interaction gradient at `μ` with
the displacement. The proof exchanges the two copies and applies Fubini's theorem. -/
private theorem integral_inner_sub_integral_inner (hw' : ∀ x, ‖gradient w x‖ ≤ C * (1 + ‖x‖))
    {γ : Measure (E × E)} [IsFiniteMeasure γ] (hγ : IsCoupling γ μ ν) (hμ : HasFiniteMoment 2 μ)
    (hH : Integrable (fun p : (E × E) × (E × E) ↦
      ⟪gradient w (p.1.1 - p.2.1), p.1.2 - p.1.1⟫) (γ.prod γ))
    (hK : Integrable (fun p : (E × E) × (E × E) ↦
      ⟪gradient w (p.1.1 - p.2.1), p.2.2 - p.2.1⟫) (γ.prod γ)) :
    ∫ p, ⟪gradient w (p.1.1 - p.2.1), p.1.2 - p.1.1⟫ ∂γ.prod γ -
      ∫ p, ⟪gradient w (p.1.1 - p.2.1), p.2.2 - p.2.1⟫ ∂γ.prod γ =
      2 * ∫ z, ⟪interactionGradient w μ z.1, z.2 - z.1⟫ ∂γ := by
  have : IsFiniteMeasure μ := by rw [← hγ.fst_eq]; infer_instance
  have hKs : Integrable (fun p : (E × E) × (E × E) ↦
      ⟪gradient w (p.2.1 - p.1.1), p.1.2 - p.1.1⟫) (γ.prod γ) := hK.swap
  have hHKs : Integrable (fun p : (E × E) × (E × E) ↦
      ⟪gradient w (p.1.1 - p.2.1) - gradient w (p.2.1 - p.1.1), p.1.2 - p.1.1⟫) (γ.prod γ) := by
    refine (hH.sub hKs).congr (.of_forall fun p ↦ ?_)
    simp only [Pi.sub_apply, inner_sub_left]
  rw [← integral_prod_swap (fun p : (E × E) × (E × E) ↦
    ⟪gradient w (p.1.1 - p.2.1), p.2.2 - p.2.1⟫)]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [← integral_sub hH hKs]
  simp only [← inner_sub_left]
  rw [integral_prod _ hHKs, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun z ↦ ?_)
  have hg := integrable_gradient_sub_sub hw' hμ z.1
  simp only [real_inner_comm (z.2 - z.1)]
  rw [integral_inner (hγ.integrable_comp_fst hg), hγ.integral_comp_fst hg.1,
    interactionGradient_def, real_inner_smul_right]
  simp

/-- **The first-order inequality of the interaction energy along a coupling.** Let `w` be a
differentiable `m`-strongly convex function, for any real `m`, whose gradient grows at most
linearly, `‖∇w z‖ ≤ C (1 + ‖z‖)`, and let `γ` be a finite coupling of two measures `μ` and `ν` with
finite second moments. Then the interaction energy `I` of the kernel `w (x - y)` satisfies
`I(ν) ≥ I(μ) + ∫ ⟪ξ x, y - x⟫ dγ + (m / 4) ∫∫ ‖(x - y) - (x' - y')‖² dγ dγ`,
where `ξ` is the interaction gradient of `w` at `μ` and the double integral runs over two
independent pairs `(x, y)` and `(x', y')` drawn from `γ`. -/
theorem _root_.StrongConvexOn.interactionEnergy_add_le (hw : StrongConvexOn univ m w)
    (hwd : Differentiable ℝ w) (hw' : ∀ x, ‖gradient w x‖ ≤ C * (1 + ‖x‖))
    {γ : Measure (E × E)} [IsFiniteMeasure γ] (hγ : IsCoupling γ μ ν)
    (hμ : HasFiniteMoment 2 μ) (hν : HasFiniteMoment 2 ν) :
    interactionEnergy (fun z ↦ w (z.1 - z.2)) μ +
      ((∫ z, ⟪interactionGradient w μ z.1, z.2 - z.1⟫ ∂γ +
        m / 4 * ∫ p, ‖(p.1.1 - p.1.2) - (p.2.1 - p.2.2)‖ ^ 2 ∂γ.prod γ : ℝ) : EReal) ≤
      interactionEnergy (fun z ↦ w (z.1 - z.2)) ν := by
  have : IsFiniteMeasure μ := by rw [← hγ.fst_eq]; infer_instance
  have : IsFiniteMeasure ν := by rw [← hγ.snd_eq]; infer_instance
  rw [interactionEnergy_eq_integral_prod (W := fun z ↦ w (z.1 - z.2))
      (integrable_comp_of_norm_gradient_le hwd hw'
        ((hμ.memLp_id.comp_fst μ).sub (hμ.memLp_id.comp_snd μ))) hγ.measurePreserving_fst,
    interactionEnergy_eq_integral_prod (W := fun z ↦ w (z.1 - z.2))
      (integrable_comp_of_norm_gradient_le hwd hw'
        ((hν.memLp_id.comp_fst ν).sub (hν.memLp_id.comp_snd ν))) hγ.measurePreserving_snd,
    ← EReal.coe_add, EReal.coe_le_coe_iff]
  -- Integrability over `γ ⊗ γ` of every term of the first-order condition.
  set P := γ.prod γ
  have hx : MemLp (fun z : E × E ↦ z.1) 2 γ :=
    hμ.memLp_id.comp_measurePreserving hγ.measurePreserving_fst
  have hy : MemLp (fun z : E × E ↦ z.2) 2 γ :=
    hν.memLp_id.comp_measurePreserving hγ.measurePreserving_snd
  have hA : MemLp (fun p : (E × E) × (E × E) ↦ p.1.1 - p.2.1) 2 P :=
    (hx.comp_fst γ).sub (hx.comp_snd γ)
  have hG : MemLp (fun p : (E × E) × (E × E) ↦ gradient w (p.1.1 - p.2.1)) 2 P :=
    hA.comp_of_norm_le_mul_one_add (measurable_gradient w).stronglyMeasurable hw'
  have hwA : Integrable (fun p : (E × E) × (E × E) ↦ w (p.1.1 - p.2.1)) P :=
    integrable_comp_of_norm_gradient_le hwd hw' hA
  have hwB : Integrable (fun p : (E × E) × (E × E) ↦ w (p.1.2 - p.2.2)) P :=
    integrable_comp_of_norm_gradient_le hwd hw' ((hy.comp_fst γ).sub (hy.comp_snd γ))
  have hH : Integrable (fun p : (E × E) × (E × E) ↦
      ⟪gradient w (p.1.1 - p.2.1), p.1.2 - p.1.1⟫) P :=
    hG.integrable_inner_of_holderConjugate ((hy.sub hx).comp_fst γ)
  have hK : Integrable (fun p : (E × E) × (E × E) ↦
      ⟪gradient w (p.1.1 - p.2.1), p.2.2 - p.2.1⟫) P :=
    hG.integrable_inner_of_holderConjugate ((hy.sub hx).comp_snd γ)
  have hsq : Integrable (fun p : (E × E) × (E × E) ↦
      ‖(p.1.1 - p.1.2) - (p.2.1 - p.2.2)‖ ^ 2) P :=
    (hx.sub hy).integrable_norm_sub_sq_prod
  have hHK : Integrable (fun p : (E × E) × (E × E) ↦ ⟪gradient w (p.1.1 - p.2.1),
      p.1.2 - p.1.1⟫ - ⟪gradient w (p.1.1 - p.2.1), p.2.2 - p.2.1⟫) P := hH.sub hK
  have hwHK : Integrable (fun p : (E × E) × (E × E) ↦ w (p.1.1 - p.2.1) +
      (⟪gradient w (p.1.1 - p.2.1), p.1.2 - p.1.1⟫ -
        ⟪gradient w (p.1.1 - p.2.1), p.2.2 - p.2.1⟫)) P := hwA.add hHK
  -- Integrate the first-order condition, then identify the linear term.
  have hfo : ∫ p, (w (p.1.1 - p.2.1) + (⟪gradient w (p.1.1 - p.2.1), p.1.2 - p.1.1⟫ -
      ⟪gradient w (p.1.1 - p.2.1), p.2.2 - p.2.1⟫) +
        m / 2 * ‖(p.1.1 - p.1.2) - (p.2.1 - p.2.2)‖ ^ 2) ∂P ≤ ∫ p, w (p.1.2 - p.2.2) ∂P :=
    integral_mono (hwHK.add (hsq.const_mul (m / 2))) hwB (add_inner_sub_inner_add_le hw hwd)
  rw [integral_add hwHK (hsq.const_mul _), integral_add hwA hHK, integral_sub hH hK,
    integral_inner_sub_integral_inner hw' hγ hμ hH hK, integral_const_mul] at hfo
  linarith

end FirstVariation

end InnerProductSpace

end TauCeti
