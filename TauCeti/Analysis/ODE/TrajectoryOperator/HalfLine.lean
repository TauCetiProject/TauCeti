/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import TauCeti.Analysis.ODE.TrajectoryOperator.Kernel
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegrableOn
import TauCeti.Analysis.ODE.Caratheodory
import TauCeti.Analysis.ODE.DysonSeries

/-!
# Solutions of a linear equation that are square integrable on a half-line

Let `A : ℝ → End(F)` be a family of bounded operators on a real normed space `F`. The space
`TauCeti.squareIntegrableSolutions A` of initial values of the solutions of `v' + A(s) v = 0`
that are square integrable on the whole line models the kernel of the trajectory operator
`d/ds + A`. This file introduces the two half-line versions:

* `TauCeti.squareIntegrableSolutionsAtTop A`, the initial values at time `0` of the solutions
  that are square integrable on `(0, ∞)`;
* `TauCeti.squareIntegrableSolutionsAtBot A`, those of the solutions that are square integrable
  on `(-∞, 0)`.

For a gradient trajectory `γ` of a Morse function from `p` to `q` and `A(s) = Hess f(γ s)`, these
spaces are the linear models of the tangent spaces at `γ 0` of the stable manifold of `q` and of
the unstable manifold of `p`, and transversality of these manifolds along `γ` corresponds to the
two spaces spanning; that identification is not made here.

For a continuous family, a solution is square integrable on the whole line exactly when it is so
on both half-lines (`TauCeti.squareIntegrableSolutions_eq_inf`). Reversing time exchanges the two
half-lines (`TauCeti.squareIntegrableSolutionsAtBot_eq_atTop`), and the half-line spaces depend
only on the family near the corresponding end (`TauCeti.squareIntegrableSolutionsAtTop_congr`).
At an end where the family is eventually the scalar `c • 1`, every solution decays there when
`c < 0`, and only the zero solution does when `c > 0`.

If `B(s)` is adjoint to `A(s)` for every `s`, the pairing `⟪v s, w s⟫` of a solution of
`v' + A v = 0` with a solution of `w' = B w` is constant in `s`. When both solutions are square
integrable on a half-line, this constant is integrable there, hence zero. So the half-line spaces
of the equation and of its formal adjoint are orthogonal
(`TauCeti.squareIntegrableSolutionsAtTop_neg_le_orthogonal`,
`TauCeti.squareIntegrableSolutionsAtBot_neg_le_orthogonal`). For hyperbolic limits they are
orthogonal complements; this is proved, together with its consequence for the surjectivity of the
trajectory operator, in `TauCeti.Analysis.ODE.EnergyEstimate.Surjective`.

## Main declarations

* `TauCeti.squareIntegrableSolutionsAtTop` and `TauCeti.squareIntegrableSolutionsAtBot`: the
  half-line spaces.
* `TauCeti.squareIntegrableSolutions_eq_inf`: the whole-line space is their intersection.
* `TauCeti.squareIntegrableSolutionsAtBot_eq_atTop`: time reversal.
* `TauCeti.squareIntegrableSolutionsAtTop_congr`: the space at `+∞` only depends on the family on
  a neighbourhood of `[0, ∞)`.
* `TauCeti.squareIntegrableSolutionsAtBot_eq_top_of_forall_le` and
  `TauCeti.squareIntegrableSolutionsAtBot_eq_bot_of_forall_le`: scalar coefficients at `-∞`.
* `TauCeti.squareIntegrableSolutionsAtTop_neg_le_orthogonal` and
  `TauCeti.squareIntegrableSolutionsAtBot_neg_le_orthogonal`: orthogonality against the formal
  adjoint equation.

## References

* M. Schwarz, *Morse Homology*, Birkhäuser, 1993, Chapter 2 (decaying solutions of the
  linearized equation and the cokernel of the linearized operator).
* K. J. Palmer, *Exponential dichotomies and transversal homoclinic points*, J. Differential
  Equations **55** (1984), 225--256 (the stable and unstable solution spaces of a linear equation
  and the Fredholm property of `d/ds + A`).
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The initial values at time `0` of the solutions `v : ℝ → F` of the linear equation
`v' + A(s) v = 0` that are square integrable on `(0, ∞)`. -/
def squareIntegrableSolutionsAtTop (A : ℝ → F →L[ℝ] F) : Submodule ℝ F where
  carrier := {x | ∃ v : ℝ → F, v 0 = x ∧ (∀ s, HasDerivAt v (-A s (v s)) s) ∧
    MemLp v 2 (volume.restrict (Ioi 0))}
  zero_mem' := ⟨0, rfl, fun s ↦ by simp, MemLp.zero⟩
  add_mem' := by
    rintro _ _ ⟨v, rfl, hv, hv2⟩ ⟨w, rfl, hw, hw2⟩
    exact ⟨v + w, rfl, fun s ↦ by simpa [add_comm] using (hv s).add (hw s), hv2.add hw2⟩
  smul_mem' := by
    rintro c _ ⟨v, rfl, hv, hv2⟩
    exact ⟨c • v, rfl, fun s ↦ by simpa using (hv s).const_smul c, hv2.const_smul c⟩

/-- The initial values at time `0` of the solutions `v : ℝ → F` of the linear equation
`v' + A(s) v = 0` that are square integrable on `(-∞, 0)`. -/
def squareIntegrableSolutionsAtBot (A : ℝ → F →L[ℝ] F) : Submodule ℝ F where
  carrier := {x | ∃ v : ℝ → F, v 0 = x ∧ (∀ s, HasDerivAt v (-A s (v s)) s) ∧
    MemLp v 2 (volume.restrict (Iio 0))}
  zero_mem' := ⟨0, rfl, fun s ↦ by simp, MemLp.zero⟩
  add_mem' := by
    rintro _ _ ⟨v, rfl, hv, hv2⟩ ⟨w, rfl, hw, hw2⟩
    exact ⟨v + w, rfl, fun s ↦ by simpa [add_comm] using (hv s).add (hw s), hv2.add hw2⟩
  smul_mem' := by
    rintro c _ ⟨v, rfl, hv, hv2⟩
    exact ⟨c • v, rfl, fun s ↦ by simpa using (hv s).const_smul c, hv2.const_smul c⟩

variable {A B : ℝ → F →L[ℝ] F} {x : F}

/-- A vector lies in `TauCeti.squareIntegrableSolutionsAtTop A` when it is the value at time `0`
of a solution of `v' + A v = 0` that is square integrable on `(0, ∞)`. -/
theorem mem_squareIntegrableSolutionsAtTop : x ∈ squareIntegrableSolutionsAtTop A ↔
    ∃ v : ℝ → F, v 0 = x ∧ (∀ s, HasDerivAt v (-A s (v s)) s) ∧
      MemLp v 2 (volume.restrict (Ioi 0)) :=
  Iff.rfl

/-- A vector lies in `TauCeti.squareIntegrableSolutionsAtBot A` when it is the value at time `0`
of a solution of `v' + A v = 0` that is square integrable on `(-∞, 0)`. -/
theorem mem_squareIntegrableSolutionsAtBot : x ∈ squareIntegrableSolutionsAtBot A ↔
    ∃ v : ℝ → F, v 0 = x ∧ (∀ s, HasDerivAt v (-A s (v s)) s) ∧
      MemLp v 2 (volume.restrict (Iio 0)) :=
  Iff.rfl

/-- A solution square integrable on the whole line is square integrable on `(0, ∞)`. -/
theorem squareIntegrableSolutions_le_atTop :
    squareIntegrableSolutions A ≤ squareIntegrableSolutionsAtTop A := by
  intro x hx
  obtain ⟨v, rfl, hv, hv2⟩ := mem_squareIntegrableSolutions.1 hx
  exact ⟨v, rfl, hv, hv2.restrict _⟩

/-- A solution square integrable on the whole line is square integrable on `(-∞, 0)`. -/
theorem squareIntegrableSolutions_le_atBot :
    squareIntegrableSolutions A ≤ squareIntegrableSolutionsAtBot A := by
  intro x hx
  obtain ⟨v, rfl, hv, hv2⟩ := mem_squareIntegrableSolutions.1 hx
  exact ⟨v, rfl, hv, hv2.restrict _⟩

/-- **A solution is square integrable on the line exactly when it is so on both half-lines.**
For a continuous family `A`, the solutions of `v' + A v = 0` square integrable on the whole line
are those square integrable on `(-∞, 0)` and on `(0, ∞)`. The two witnesses of the half-line
conditions are the same solution, by uniqueness of solutions of a linear equation. -/
theorem squareIntegrableSolutions_eq_inf (hA : Continuous A) :
    squareIntegrableSolutions A =
      squareIntegrableSolutionsAtBot A ⊓ squareIntegrableSolutionsAtTop A := by
  refine le_antisymm (le_inf squareIntegrableSolutions_le_atBot squareIntegrableSolutions_le_atTop)
    ?_
  rintro x ⟨⟨v, rfl, hv, hv2⟩, ⟨w, hw0, hw, hw2⟩⟩
  have hvw : w = v := hA.neg.eq_of_hasDerivAt_clm_apply (B := -A) (t₀ := 0)
    (fun s ↦ by simpa using hw s) (fun s ↦ by simpa using hv s) hw0
  subst hvw
  have hcont : Continuous w := continuous_iff_continuousAt.2 fun s ↦ (hw s).continuousAt
  refine mem_squareIntegrableSolutions.2
    ⟨w, hw0, hw, (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ?_⟩
  have hbot := (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).1 hv2
  have htop := (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).1 hw2
  rw [← integrableOn_univ, ← Iio_union_Ici (a := (0 : ℝ))]
  exact IntegrableOn.union hbot ((integrableOn_Ici_iff_integrableOn_Ioi (by simp)).2 htop)

/-- Reversing time sends solutions of `v' + A(s) v = 0` to solutions of `u' - A(-s) u = 0`. -/
private theorem hasDerivAt_comp_neg {v : ℝ → F} (hv : ∀ s, HasDerivAt v (-A s (v s)) s) (s : ℝ) :
    HasDerivAt (fun s ↦ v (-s)) (-(fun s ↦ -A (-s)) s ((fun s ↦ v (-s)) s)) s := by
  simpa [Function.comp_def] using (hv (-s)).scomp s (hasDerivAt_neg s)

/-- The reflection `s ↦ -s` carries Lebesgue measure on `(0, ∞)` to Lebesgue measure on
`(-∞, 0)`. -/
private theorem measurePreserving_neg_Ioi :
    MeasurePreserving (Neg.neg : ℝ → ℝ) (volume.restrict (Ioi 0)) (volume.restrict (Iio 0)) := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
    (measurableSet_Iio (a := (0 : ℝ)))
  rwa [show (Neg.neg : ℝ → ℝ) ⁻¹' Iio 0 = Ioi 0 by ext; simp] at h

/-- The reflection `s ↦ -s` carries Lebesgue measure on `(-∞, 0)` to Lebesgue measure on
`(0, ∞)`. -/
private theorem measurePreserving_neg_Iio :
    MeasurePreserving (Neg.neg : ℝ → ℝ) (volume.restrict (Iio 0)) (volume.restrict (Ioi 0)) := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
    (measurableSet_Ioi (a := (0 : ℝ)))
  rwa [show (Neg.neg : ℝ → ℝ) ⁻¹' Ioi 0 = Iio 0 by ext; simp] at h

/-- **Time reversal exchanges the two half-lines.** Reversing time turns the solutions of
`v' + A(s) v = 0` into those of `u' - A(-s) u = 0` with the same initial value, and turns square
integrability on `(-∞, 0)` into square integrability on `(0, ∞)`. -/
theorem squareIntegrableSolutionsAtBot_eq_atTop (A : ℝ → F →L[ℝ] F) :
    squareIntegrableSolutionsAtBot A = squareIntegrableSolutionsAtTop fun s ↦ -A (-s) := by
  ext x
  constructor
  · rintro ⟨v, rfl, hv, hv2⟩
    exact ⟨fun s ↦ v (-s), by simp, hasDerivAt_comp_neg hv,
      hv2.comp_measurePreserving measurePreserving_neg_Ioi⟩
  · rintro ⟨u, rfl, hu, hu2⟩
    refine ⟨fun s ↦ u (-s), by simp, fun s ↦ by simpa using hasDerivAt_comp_neg hu s,
      hu2.comp_measurePreserving measurePreserving_neg_Iio⟩

/-- Two continuous families that agree on `(a, ∞)`, with `a < 0`, have solutions that agree on
`(a, ∞)` when their values at `0` agree. -/
private theorem eqOn_Ioi_of_eqOn (hA : Continuous A) {a : ℝ} (ha : a < 0)
    (hAB : ∀ s, a < s → A s = B s) {v w : ℝ → F} (hv : ∀ s, HasDerivAt v (-A s (v s)) s)
    (hw : ∀ s, HasDerivAt w (-B s (w s)) s) (h0 : v 0 = w 0) : EqOn v w (Ioi a) := by
  intro t ht
  set b := max t 0 + 1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hA.continuousOn (s := Icc a b))
  have hLip (s : ℝ) (hs : s ∈ Ioo a b) : LipschitzOnWith (Real.toNNReal C) (fun y ↦ -A s y) univ :=
    ((-A s).lipschitzWith.weaken (NNReal.le_toNNReal_of_coe_le (by
      simpa using hC s (Ioo_subset_Icc_self hs)))).lipschitzOnWith
  exact ODE_solution_unique_of_mem_Ioo (s := fun _ ↦ univ) hLip (t₀ := 0)
    ⟨ha, by positivity⟩ (fun s _ ↦ ⟨hv s, mem_univ _⟩)
    (fun s hs ↦ ⟨by simpa [hAB s hs.1] using hw s, mem_univ _⟩) h0
    ⟨ht, by simp [b]; grind⟩

/-- Where the family is the scalar `c • 1`, a solution of `v' + A(s) v = 0` is
`v s = exp (c (b - s)) • v b`. -/
private theorem eq_exp_smul_of_forall_le {c a : ℝ} (hAc : ∀ s ≤ a, A s = c • 1) {v : ℝ → F}
    (hv : ∀ s, HasDerivAt v (-A s (v s)) s) {s b : ℝ} (hs : s < a) (hb : b < a) :
    v s = Real.exp (c * (b - s)) • v b := by
  have hd : ∀ t ∈ Iio a, HasDerivAt (fun t ↦ Real.exp (c * t) • v t) 0 t := by
    intro t ht
    have h1 : HasDerivAt (fun t ↦ Real.exp (c * t)) (Real.exp (c * t) * c) t := by
      simpa using ((hasDerivAt_id t).const_mul c).exp
    have h := h1.smul (hv t)
    rw [hAc t (le_of_lt ht)] at h
    convert h using 1
    simp [smul_smul, mul_comm]
  have h := isOpen_Iio.is_const_of_deriv_eq_zero isPreconnected_Iio
    (fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ (hd t ht).deriv) (mem_Iio.2 hs) (mem_Iio.2 hb)
  calc v s = Real.exp (-(c * s)) • (Real.exp (c * s) • v s) := by
        rw [smul_smul, ← Real.exp_add]; simp
    _ = Real.exp (-(c * s)) • (Real.exp (c * b) • v b) := by rw [h]
    _ = Real.exp (c * (b - s)) • v b := by rw [smul_smul, ← Real.exp_add]; ring_nf

/-- **A scalar coefficient `c > 0` at `-∞` admits no decaying solutions there.** If a continuous
family is `c • 1` on `(-∞, a]` with `c > 0`, the only solution of `v' + A(s) v = 0` square
integrable on `(-∞, 0)` is zero: on `(-∞, a]` the norm of a solution grows backwards in time. -/
theorem squareIntegrableSolutionsAtBot_eq_bot_of_forall_le (hA : Continuous A) {c a : ℝ}
    (hc : 0 < c) (hAc : ∀ s ≤ a, A s = c • 1) : squareIntegrableSolutionsAtBot A = ⊥ := by
  refine eq_bot_iff.2 fun x hx ↦ ?_
  obtain ⟨v, rfl, hv, hv2⟩ := hx
  have hcont : Continuous v := continuous_iff_continuousAt.2 fun s ↦ (hv s).continuousAt
  set b := min a 0 - 1
  have hba : b < a := by grind
  have hint : IntegrableOn (fun s ↦ ‖v s‖ ^ 2) (Iic b) :=
    IntegrableOn.mono_set ((memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).1 hv2)
      (Iic_subset_Iio.2 (by grind))
  have hconst : IntegrableOn (fun _ ↦ ‖v b‖ ^ 2) (Iic b) := by
    refine hint.mono' aestronglyMeasurable_const
      (ae_restrict_of_forall_mem measurableSet_Iic fun s hs ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
      eq_exp_smul_of_forall_le hAc hv ((mem_Iic.1 hs).trans_lt hba) hba, norm_smul,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
    have h1 : 1 ≤ Real.exp (c * (b - s)) ^ 2 :=
      one_le_pow₀ (Real.one_le_exp (mul_nonneg hc.le (by linarith [mem_Iic.1 hs])))
    nlinarith [sq_nonneg ‖v b‖]
  rw [integrableOn_const_iff (by simp)] at hconst
  have hvb : v b = 0 := by
    rcases hconst with h | h
    · simpa using h
    · simp [Real.volume_Iic] at h
  have : v = 0 := hA.neg.eq_of_hasDerivAt_clm_apply (B := -A) (t₀ := b)
    (fun s ↦ by simpa using hv s) (fun s ↦ by simp)
    (by simpa using hvb)
  simp [this]

section Complete

variable [CompleteSpace F]

/-- Every initial value is the value at `0` of a solution of `v' + A(s) v = 0` on the whole
line, for a continuous family `A` on a Banach space. -/
private theorem exists_solution (hA : Continuous A) (x : F) :
    ∃ v : ℝ → F, v 0 = x ∧ ∀ s, HasDerivAt v (-A s (v s)) s :=
  ⟨fun t ↦ dysonSeriesLeft (-A) t x, by simp [dysonSeriesLeft_zero],
    fun s ↦ by simpa using hasDerivAt_dysonSeriesLeft_apply hA.neg x s⟩

/-- **The space at `+∞` only depends on the family near `[0, ∞)`.** If two continuous families
on a Banach space agree on `(a, ∞)` for some `a < 0`, the solutions of their equations that are
square integrable on `(0, ∞)` have the same initial values. -/
theorem squareIntegrableSolutionsAtTop_congr (hA : Continuous A) (hB : Continuous B) {a : ℝ}
    (ha : a < 0) (hAB : ∀ s, a < s → A s = B s) :
    squareIntegrableSolutionsAtTop A = squareIntegrableSolutionsAtTop B := by
  suffices key : ∀ {A B : ℝ → F →L[ℝ] F}, Continuous A → Continuous B →
      (∀ s, a < s → A s = B s) →
      squareIntegrableSolutionsAtTop A ≤ squareIntegrableSolutionsAtTop B from
    le_antisymm (key hA hB hAB) (key hB hA fun s hs ↦ (hAB s hs).symm)
  intro A B hA hB hAB
  rintro _ ⟨v, rfl, hv, hv2⟩
  obtain ⟨w, hw0, hw⟩ := exists_solution hB (v 0)
  refine ⟨w, hw0, hw, hv2.ae_eq ?_⟩
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ ?_
  exact eqOn_Ioi_of_eqOn hA ha hAB hv hw hw0.symm (lt_trans ha ht)

/-- **A scalar coefficient `c < 0` at `-∞` makes every solution decay there.** If a continuous
family on a Banach space is `c • 1` on `(-∞, a]` with `c < 0`, every solution of
`v' + A(s) v = 0` is square integrable on `(-∞, 0)`, since it decays exponentially on
`(-∞, a]`. -/
theorem squareIntegrableSolutionsAtBot_eq_top_of_forall_le (hA : Continuous A) {c a : ℝ}
    (hc : c < 0) (hAc : ∀ s ≤ a, A s = c • 1) : squareIntegrableSolutionsAtBot A = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨v, hv0, hv⟩ := exists_solution hA x
  have hcont : Continuous v := continuous_iff_continuousAt.2 fun s ↦ (hv s).continuousAt
  refine ⟨v, hv0, hv, (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ?_⟩
  set b := a - 1
  have hba : b < a := by grind
  have htail : IntegrableOn (fun s ↦ ‖v s‖ ^ 2) (Iic b) := by
    refine IntegrableOn.congr_fun
      ((integrableOn_exp_mul_Iic (a := -2 * c) (by linarith) b).mul_const
        (Real.exp (2 * c * b) * ‖v b‖ ^ 2)) (fun s hs ↦ ?_) measurableSet_Iic
    rw [eq_exp_smul_of_forall_le hAc hv ((mem_Iic.1 hs).trans_lt hba) hba, norm_smul,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, sq (Real.exp _),
      ← Real.exp_add]
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
  have hmid : IntegrableOn (fun s ↦ ‖v s‖ ^ 2) (Icc b 0) :=
    (hcont.norm.pow 2).integrableOn_Icc
  refine (htail.union hmid).mono_set fun s hs ↦ ?_
  rcases le_or_gt s b with h | h
  exacts [Or.inl h, Or.inr ⟨h.le, (mem_Iio.1 hs).le⟩]

end Complete

section Orthogonal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {A B : ℝ → E →L[ℝ] E}

/-- If `B(s)` is adjoint to `A(s)`, the pairing of a solution of `v' + A v = 0` with a solution
of `w' = B w` is constant in time. -/
private theorem inner_eq_inner_zero (hAB : ∀ s x y, ⟪A s x, y⟫_ℝ = ⟪x, B s y⟫_ℝ) {v w : ℝ → E}
    (hv : ∀ s, HasDerivAt v (-A s (v s)) s) (hw : ∀ s, HasDerivAt w (-(-B s) (w s)) s)
    (s : ℝ) : ⟪v s, w s⟫_ℝ = ⟪v 0, w 0⟫_ℝ := by
  have hd : ∀ t, HasDerivAt (fun t ↦ ⟪v t, w t⟫_ℝ) 0 t := by
    intro t
    convert (hv t).inner ℝ (hw t) using 1
    simp [inner_neg_left, hAB]
  exact is_const_of_deriv_eq_zero (fun t ↦ (hd t).differentiableAt) (fun t ↦ (hd t).deriv) s 0

/-- If the pairing of two paths is constant and both are square integrable on a set of infinite
measure, the constant vanishes. -/
private theorem inner_eq_zero_of_memLp {S : Set ℝ} (hS : volume S = ∞) {v w : ℝ → E}
    (hconst : ∀ s, ⟪v s, w s⟫_ℝ = ⟪v 0, w 0⟫_ℝ) (hv2 : MemLp v 2 (volume.restrict S))
    (hw2 : MemLp w 2 (volume.restrict S)) : ⟪v 0, w 0⟫_ℝ = 0 := by
  have hprod : IntegrableOn (fun s ↦ ‖v s‖ * ‖w s‖) S := hv2.norm.integrable_mul hw2.norm
  have hint : IntegrableOn (fun s ↦ ⟪v s, w s⟫_ℝ) S :=
    hprod.mono' (hv2.aestronglyMeasurable.inner hw2.aestronglyMeasurable) (.of_forall fun s ↦ by
      simpa using abs_real_inner_le_norm (v s) (w s))
  simp_rw [hconst] at hint
  rcases (integrableOn_const_iff (by simp)).1 hint with h | h
  · simpa using h
  · simp [hS] at h

/-- **Decaying solutions at `+∞` are orthogonal to decaying solutions of the adjoint equation.**
If `B(s)` is adjoint to `A(s)` for every `s`, the initial value of a solution of `v' + A v = 0`
and that of a solution of `w' = B w`, both square integrable on `(0, ∞)`, are orthogonal. -/
theorem inner_eq_zero_of_mem_squareIntegrableSolutionsAtTop
    (hAB : ∀ s x y, ⟪A s x, y⟫_ℝ = ⟪x, B s y⟫_ℝ) {x y : E}
    (hx : x ∈ squareIntegrableSolutionsAtTop A)
    (hy : y ∈ squareIntegrableSolutionsAtTop fun s ↦ -B s) : ⟪x, y⟫_ℝ = 0 := by
  obtain ⟨v, rfl, hv, hv2⟩ := hx
  obtain ⟨w, rfl, hw, hw2⟩ := hy
  exact inner_eq_zero_of_memLp (by simp) (inner_eq_inner_zero hAB hv hw) hv2 hw2

/-- **Decaying solutions at `-∞` are orthogonal to decaying solutions of the adjoint equation.**
If `B(s)` is adjoint to `A(s)` for every `s`, the initial value of a solution of `v' + A v = 0`
and that of a solution of `w' = B w`, both square integrable on `(-∞, 0)`, are orthogonal. -/
theorem inner_eq_zero_of_mem_squareIntegrableSolutionsAtBot
    (hAB : ∀ s x y, ⟪A s x, y⟫_ℝ = ⟪x, B s y⟫_ℝ) {x y : E}
    (hx : x ∈ squareIntegrableSolutionsAtBot A)
    (hy : y ∈ squareIntegrableSolutionsAtBot fun s ↦ -B s) : ⟪x, y⟫_ℝ = 0 := by
  obtain ⟨v, rfl, hv, hv2⟩ := hx
  obtain ⟨w, rfl, hw, hw2⟩ := hy
  exact inner_eq_zero_of_memLp (by simp) (inner_eq_inner_zero hAB hv hw) hv2 hw2

/-- The decaying solutions at `+∞` of the formal adjoint equation `w' = B w` lie in the
orthogonal complement of those of `v' + A v = 0`. -/
theorem squareIntegrableSolutionsAtTop_neg_le_orthogonal
    (hAB : ∀ s x y, ⟪A s x, y⟫_ℝ = ⟪x, B s y⟫_ℝ) :
    squareIntegrableSolutionsAtTop (fun s ↦ -B s) ≤ (squareIntegrableSolutionsAtTop A)ᗮ :=
  fun _ hy ↦ (Submodule.mem_orthogonal _ _).2 fun _ hx ↦
    inner_eq_zero_of_mem_squareIntegrableSolutionsAtTop hAB hx hy

/-- The decaying solutions at `-∞` of the formal adjoint equation `w' = B w` lie in the
orthogonal complement of those of `v' + A v = 0`. -/
theorem squareIntegrableSolutionsAtBot_neg_le_orthogonal
    (hAB : ∀ s x y, ⟪A s x, y⟫_ℝ = ⟪x, B s y⟫_ℝ) :
    squareIntegrableSolutionsAtBot (fun s ↦ -B s) ≤ (squareIntegrableSolutionsAtBot A)ᗮ :=
  fun _ hy ↦ (Submodule.mem_orthogonal _ _).2 fun _ hx ↦
    inner_eq_zero_of_mem_squareIntegrableSolutionsAtBot hAB hx hy

end Orthogonal

end TauCeti
