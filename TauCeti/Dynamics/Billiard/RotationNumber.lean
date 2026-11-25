/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.Smooth
public import TauCeti.Dynamics.Circle.RotationNumber.Comparison

/-!
# Rotation numbers of invariant graphs of the billiard map

Let `χ` be an arclength parametrization of the boundary of a strictly convex billiard table
(`TauCeti.StrictConvexBilliardTable`), with period `L`, and let `B(s, v) = (t, w)` be its
next-collision map on the strip `ℝ × (-1, 1)`. An *invariant graph* is a continuous `L`-periodic
function `ψ : ℝ → (-1, 1)` whose graph `{v = ψ(s)}` is mapped into itself by `B`
(`TauCeti.StrictConvexBilliardTable.IsInvariantGraph`): it is a rotational invariant curve of the
billiard map on `AddCircle L × (-1, 1)` written as a graph over the boundary.

On the graph, `B` acts through its first coordinate `g(s) = t(s, ψ(s))`
(`TauCeti.StrictConvexBilliardTable.graphLift`): `B(s, ψ(s)) = (g(s), ψ(g(s)))`. For a `C²` table
`g` is continuous, injective because `B` is, and commutes with `s ↦ s + L`, so it is strictly
increasing (`TauCeti.StrictConvexBilliardTable.IsInvariantGraph.strictMono_graphLift`). Rescaled
by the period, `x ↦ g(L x) / L` is a lift of a circle homeomorphism
(`TauCeti.StrictConvexBilliardTable.IsInvariantGraph.circleLift`), and the *rotation number* of
the invariant graph is its translation number
(`TauCeti.StrictConvexBilliardTable.IsInvariantGraph.rotationNumber`). It is the asymptotic
average displacement along any orbit on the graph, measured in periods:
`(tₙ - s) / (n L) → ρ`, where `tₙ` is the parameter of `Bⁿ(s, ψ(s))`
(`TauCeti.StrictConvexBilliardTable.IsInvariantGraph.tendsto_rotationNumber`).

Since `s < g(s) < s + L`, the rotation number lies strictly between `0` and `1`
(`TauCeti.StrictConvexBilliardTable.IsInvariantGraph.rotationNumber_mem_Ioo`). Time reversal
`ι(s, v) = (s, -v)` maps invariant graphs to invariant graphs
(`TauCeti.StrictConvexBilliardTable.IsInvariantGraph.neg`), and the reversed graph has rotation
number `1 - ρ` (`TauCeti.StrictConvexBilliardTable.IsInvariantGraph.rotationNumber_neg`): its lift
composed with `g` is the deck translation `s ↦ s + L`. Since `t(s, v)` is decreasing in `v`, a
higher invariant graph has a rotation number that is no larger
(`TauCeti.StrictConvexBilliardTable.IsInvariantGraph.rotationNumber_anti`); for two graphs
`ψ₁ < ψ₂` it is strictly smaller when one of the two rotation numbers is irrational
(`TauCeti.StrictConvexBilliardTable.IsInvariantGraph.rotationNumber_lt_of_irrational`), by the
strict comparison of circle lifts
(`CircleDeg1Lift.translationNumber_lt_of_forall_lt_of_irrational_left`).
The rotation numbers of the circular table are computed in `TauCeti.Dynamics.Billiard.Circle`.

The rotation number is a rational `p / q` (`q ≥ 1`) exactly when some state on the graph returns
after `q` collisions to itself, displaced by `p` periods: `B^q(s, ψ(s)) = (s + p L, ψ(s))`
(`TauCeti.StrictConvexBilliardTable.IsInvariantGraph.rotationNumber_eq_div_iff`), which is a
periodic orbit of type `(p, q)` of the billiard map on the graph. In particular a graph with
irrational rotation number carries no periodic orbit
(`TauCeti.StrictConvexBilliardTable.IsInvariantGraph.iterate_nextCollision_ne_of_irrational`).

In the angle coordinate `δ` with `v = cos δ`, the graph `{v = ψ}` is the graph
`{δ = arccos ψ}`, the time reversal is `δ ↦ π - δ`, and rotation numbers are nondecreasing in `δ`.

## Main definitions

* `TauCeti.StrictConvexBilliardTable.IsInvariantGraph`: an invariant graph of the billiard map.
* `TauCeti.StrictConvexBilliardTable.graphLift`: the first coordinate of the next-collision map
  along a graph.
* `TauCeti.StrictConvexBilliardTable.IsInvariantGraph.circleLift`,
  `TauCeti.StrictConvexBilliardTable.IsInvariantGraph.rotationNumber`: the rescaled circle lift and
  the rotation number of an invariant graph.

## References

* Michael-R. Herman, *Sur les courbes invariantes par les difféomorphismes de l'anneau*, Vol. 1,
  Astérisque 103–104, 1983, Chapitre I, 2.4.
* Anatole Katok and Boris Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*,
  Cambridge University Press, 1995, Chapter 13.
-/

public section

noncomputable section

open Function Set Filter Topology Module

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]

namespace StrictConvexBilliardTable

variable {o : Orientation ℝ E (Fin 2)} (χ : StrictConvexBilliardTable o)

/-- An **invariant graph** of the billiard map: a continuous `L`-periodic function
`ψ : ℝ → (-1, 1)` whose graph `{(s, ψ(s))}` the next-collision map sends into itself, so that the
state `(s, ψ(s))` goes to `(t, ψ(t))` with `t = nextParam s (ψ s)`. -/
structure IsInvariantGraph (ψ : ℝ → ℝ) : Prop where
  continuous : Continuous ψ
  periodic : Periodic ψ χ.period
  mem_Ioo : ∀ s, ψ s ∈ Ioo (-1) 1
  nextTangential_eq : ∀ s, χ.nextTangential s (ψ s) = ψ (χ.nextParam s (ψ s))

/-- The first coordinate `g(s) = nextParam s (ψ s)` of the next-collision map along the graph of
`ψ`. -/
def graphLift (ψ : ℝ → ℝ) (s : ℝ) : ℝ :=
  χ.nextParam s (ψ s)

theorem graphLift_def (ψ : ℝ → ℝ) (s : ℝ) : χ.graphLift ψ s = χ.nextParam s (ψ s) :=
  (rfl)

namespace IsInvariantGraph

variable {χ} {ψ : ℝ → ℝ} (h : χ.IsInvariantGraph ψ)
include h

/-- On an invariant graph the next-collision map is `(s, ψ(s)) ↦ (g(s), ψ(g(s)))`. -/
theorem nextCollision_eq (s : ℝ) :
    χ.nextCollision (s, ψ s) = (χ.graphLift ψ s, ψ (χ.graphLift ψ s)) := by
  simp [graphLift_def, h.nextTangential_eq]

/-- The orbit of a state on an invariant graph stays on the graph, and its parameters are the
iterates of the graph lift. -/
theorem iterate_nextCollision (n : ℕ) (s : ℝ) :
    χ.nextCollision^[n] (s, ψ s) = ((χ.graphLift ψ)^[n] s, ψ ((χ.graphLift ψ)^[n] s)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', ih, h.nextCollision_eq, iterate_succ_apply']

/-- The billiard map sends the class of a state on an invariant graph to the class of the next
state on the graph. -/
theorem billiardMap_coe (s : ℝ) :
    χ.billiardMap ((s : AddCircle χ.period), ⟨ψ s, h.mem_Ioo s⟩) =
      ((χ.graphLift ψ s : AddCircle χ.period),
        ⟨ψ (χ.graphLift ψ s), h.mem_Ioo _⟩) := by
  rw [StrictConvexBilliardTable.billiardMap_coe]
  exact Prod.ext rfl (Subtype.ext (h.nextTangential_eq s))

theorem graphLift_mem_Ioo (s : ℝ) : χ.graphLift ψ s ∈ Ioo s (s + χ.period) :=
  χ.nextParam_mem_Ioo (h.mem_Ioo s)

theorem graphLift_add_period (s : ℝ) :
    χ.graphLift ψ (s + χ.period) = χ.graphLift ψ s + χ.period := by
  rw [graphLift_def, h.periodic s, χ.nextParam_add_period (h.mem_Ioo s), graphLift_def]

/-- The graph lift is injective, since the next-collision map is injective on the strip. -/
theorem injective_graphLift : Injective (χ.graphLift ψ) := by
  intro s t hst
  have key : χ.nextCollision (s, ψ s) = χ.nextCollision (t, ψ t) := by
    rw [h.nextCollision_eq, h.nextCollision_eq, hst]
  exact congrArg Prod.fst (χ.injOn_nextCollision ⟨mem_univ s, h.mem_Ioo s⟩
    ⟨mem_univ t, h.mem_Ioo t⟩ key)

theorem continuous_graphLift (hχ : ContDiff ℝ 2 χ) : Continuous (χ.graphLift ψ) :=
  continuous_iff_continuousAt.2 fun s ↦
    (χ.contDiffAt_nextParam (n := 0) (hχ.contDiffAt.of_le (by norm_num))
      (hχ.contDiffAt.of_le (by norm_num)) (h.mem_Ioo s)).continuousAt.comp
      (f := fun s ↦ (s, ψ s)) (continuous_id.prodMk h.continuous).continuousAt

/-- The rescaled graph lift `x ↦ g(L x) / L` is continuous for a `C²` table. -/
private theorem continuous_rescale (hχ : ContDiff ℝ 2 χ) :
    Continuous fun x ↦ χ.graphLift ψ (χ.period * x) / χ.period :=
  ((h.continuous_graphLift hχ).comp (continuous_const.mul continuous_id)).div_const _

private theorem injective_rescale :
    Injective fun x ↦ χ.graphLift ψ (χ.period * x) / χ.period := by
  intro x y hxy
  exact mul_left_cancel₀ χ.period_pos.ne'
    (h.injective_graphLift ((div_left_inj₀ χ.period_pos.ne').1 hxy))

private theorem rescale_add_one (x : ℝ) :
    χ.graphLift ψ (χ.period * (x + 1)) / χ.period =
      χ.graphLift ψ (χ.period * x) / χ.period + 1 := by
  rw [mul_add_one, h.graphLift_add_period, add_div, div_self χ.period_pos.ne']

/-- For a `C²` table the graph lift of an invariant graph is strictly increasing. -/
theorem strictMono_graphLift (hχ : ContDiff ℝ 2 χ) : StrictMono (χ.graphLift ψ) := by
  have hL := χ.period_pos
  intro x y hxy
  have := (h.continuous_rescale hχ).strictMono_of_injective_of_map_add_one h.injective_rescale
    h.rescale_add_one (div_lt_div_of_pos_right hxy hL)
  simpa only [mul_div_cancel₀ _ hL.ne', div_lt_div_iff_of_pos_right hL] using this

/-- The **circle lift** of an invariant graph of a `C²` table: the graph lift rescaled by the
period, `x ↦ g(L x) / L`, a lift of a homeomorphism of the circle `ℝ / ℤ`. -/
def circleLift (hχ : ContDiff ℝ 2 χ) : CircleDeg1Lift :=
  CircleDeg1Lift.ofInjective _ (h.continuous_rescale hχ) h.injective_rescale h.rescale_add_one

@[simp]
theorem circleLift_apply (hχ : ContDiff ℝ 2 χ) (x : ℝ) :
    h.circleLift hχ x = χ.graphLift ψ (χ.period * x) / χ.period := by
  rw [circleLift, CircleDeg1Lift.coe_ofInjective]

theorem continuous_circleLift (hχ : ContDiff ℝ 2 χ) : Continuous (h.circleLift hχ) :=
  CircleDeg1Lift.continuous_ofInjective _ _ _

theorem iterate_circleLift (hχ : ContDiff ℝ 2 χ) (n : ℕ) (x : ℝ) :
    (h.circleLift hχ)^[n] x = (χ.graphLift ψ)^[n] (χ.period * x) / χ.period := by
  induction n with
  | zero => simp [χ.period_pos.ne']
  | succ n ih =>
    rw [iterate_succ_apply', ih, circleLift_apply, iterate_succ_apply',
      mul_div_cancel₀ _ χ.period_pos.ne']

/-- The **rotation number** of an invariant graph of a `C²` table: the translation number of its
circle lift `x ↦ g(L x) / L`, the asymptotic displacement along the graph per collision, measured
in periods. -/
def rotationNumber (hχ : ContDiff ℝ 2 χ) : ℝ :=
  (h.circleLift hχ).translationNumber

theorem rotationNumber_def (hχ : ContDiff ℝ 2 χ) :
    h.rotationNumber hχ = (h.circleLift hχ).translationNumber :=
  (rfl)

/-- Along every orbit on an invariant graph, the parameters `tₙ` of the iterates `Bⁿ(s, ψ(s))`
satisfy `(tₙ - s) / (n L) → ρ`. -/
theorem tendsto_rotationNumber (hχ : ContDiff ℝ 2 χ) (s : ℝ) :
    Tendsto (fun n : ℕ ↦ ((χ.nextCollision^[n] (s, ψ s)).1 - s) / (n * χ.period)) atTop
      (𝓝 (h.rotationNumber hχ)) := by
  refine ((h.circleLift hχ).tendsto_translationNumber (s / χ.period)).congr fun n ↦ ?_
  rw [CircleDeg1Lift.coe_pow, h.iterate_circleLift, h.iterate_nextCollision,
    mul_div_cancel₀ _ χ.period_pos.ne']
  field_simp

/-- **The rotation number lies strictly between `0` and `1`**: every collision advances the
parameter by more than `0` and less than one period. -/
theorem rotationNumber_mem_Ioo (hχ : ContDiff ℝ 2 χ) : h.rotationNumber hχ ∈ Ioo 0 1 := by
  have hL := χ.period_pos
  have h₁ := (h.circleLift hχ).translationNumber_lt_int_iff (h.continuous_circleLift hχ) (n := 1)
  rw [Int.cast_one] at h₁
  refine ⟨((h.circleLift hχ).translationNumber_pos_iff (h.continuous_circleLift hχ)).2
    fun x ↦ ?_, h₁.2 fun x ↦ ?_⟩
  · rw [circleLift_apply, lt_div_iff₀ hL, mul_comm]
    exact (h.graphLift_mem_Ioo _).1
  · rw [circleLift_apply, div_lt_iff₀ hL, add_mul, one_mul, mul_comm]
    exact (h.graphLift_mem_Ioo _).2

/-- For a `C²` table the graph lift of an invariant graph is onto. -/
theorem surjective_graphLift (hχ : ContDiff ℝ 2 χ) : Surjective (χ.graphLift ψ) := by
  intro t
  obtain ⟨x, hx⟩ := (h.circleLift hχ).continuous_iff_surjective.1 (h.continuous_circleLift hχ)
    (t / χ.period)
  refine ⟨χ.period * x, ?_⟩
  rw [circleLift_apply] at hx
  exact (div_left_inj₀ χ.period_pos.ne').1 hx

/-! ### Time reversal -/

/-- **Time reversal of invariant graphs.** For a `C²` table, the image `{v = -ψ(s)}` of an
invariant graph under the time reversal `ι(s, v) = (s, -v)` is an invariant graph. -/
theorem neg (hχ : ContDiff ℝ 2 χ) : χ.IsInvariantGraph (-ψ) where
  continuous := h.continuous.neg
  periodic s := by simp [h.periodic s]
  mem_Ioo s := by
    rw [Pi.neg_apply]
    exact ⟨neg_lt_neg (h.mem_Ioo s).2, neg_lt.1 (h.mem_Ioo s).1⟩
  nextTangential_eq t := by
    obtain ⟨s, rfl⟩ := h.surjective_graphLift hχ t
    have hs := h.mem_Ioo s
    simp only [Pi.neg_apply, graphLift_def, ← h.nextTangential_eq s,
      χ.nextParam_nextParam_neg_nextTangential hs, χ.nextTangential_nextParam_neg_nextTangential hs,
      h.periodic s]

/-- The graph lift of the reversed graph undoes the graph lift up to one period. -/
theorem graphLift_neg_graphLift (s : ℝ) :
    χ.graphLift (-ψ) (χ.graphLift ψ s) = s + χ.period := by
  rw [graphLift_def, graphLift_def, Pi.neg_apply, ← h.nextTangential_eq s,
    χ.nextParam_nextParam_neg_nextTangential (h.mem_Ioo s)]

/-- **Rotation number under time reversal**: `ρ(ι C) = 1 - ρ(C)`. -/
theorem rotationNumber_neg (hχ : ContDiff ℝ 2 χ) :
    (h.neg hχ).rotationNumber hχ = 1 - h.rotationNumber hχ := by
  have hL := χ.period_pos.ne'
  set f := (h.neg hχ).circleLift hχ
  set g := h.circleLift hχ
  have hfg : ∀ x, f (g x) = x + 1 := fun x ↦ by
    rw [circleLift_apply, circleLift_apply, mul_div_cancel₀ _ hL, h.graphLift_neg_graphLift]
    field_simp
  have hgf : ∀ x, g (f x) = x + 1 := fun x ↦ by
    obtain ⟨y, hy⟩ := (g.continuous_iff_surjective).1 (h.continuous_circleLift hχ) x
    rw [← hy, hfg, g.map_add_one]
  have hcomm : Commute f g := CircleDeg1Lift.commute_iff_commute.2 fun x ↦ by rw [hfg, hgf]
  have htr : f * g = (CircleDeg1Lift.translate (Multiplicative.ofAdd 1) : CircleDeg1Lift) :=
    CircleDeg1Lift.ext fun x ↦ by
      rw [CircleDeg1Lift.mul_apply, hfg, CircleDeg1Lift.translate_apply, add_comm]
  have := CircleDeg1Lift.translationNumber_mul_of_commute hcomm
  rw [htr, CircleDeg1Lift.translationNumber_translate] at this
  rw [rotationNumber_def, rotationNumber_def]
  linarith

/-! ### Periodic orbits -/

/-- **Rational rotation numbers and periodic orbits.** The rotation number of an invariant graph
of a `C²` table is `p / q`, for `q ≥ 1`, exactly when some state on the graph is sent by `q`
collisions to the same state displaced by `p` periods. -/
theorem rotationNumber_eq_div_iff (hχ : ContDiff ℝ 2 χ) {p : ℤ} {q : ℕ} (hq : 0 < q) :
    h.rotationNumber hχ = p / q ↔
      ∃ s, χ.nextCollision^[q] (s, ψ s) = (s + p * χ.period, ψ s) := by
  have hL := χ.period_pos.ne'
  rw [rotationNumber_def, (h.circleLift hχ).translationNumber_eq_rat_iff
    (h.continuous_circleLift hχ) hq]
  simp only [CircleDeg1Lift.coe_pow, h.iterate_circleLift, h.iterate_nextCollision, Prod.ext_iff]
  constructor
  · rintro ⟨x, hx⟩
    have hx' : (χ.graphLift ψ)^[q] (χ.period * x) = χ.period * x + p * χ.period := by
      rw [div_eq_iff hL] at hx
      rw [hx]
      ring
    exact ⟨χ.period * x, hx', by rw [hx', h.periodic.int_mul p]⟩
  · rintro ⟨s, hs, -⟩
    refine ⟨s / χ.period, ?_⟩
    rw [mul_div_cancel₀ _ hL, hs]
    field_simp

/-- **No periodic orbit at an irrational rotation number.** If an invariant graph of a `C²` table
has irrational rotation number, no state on it returns after `q ≥ 1` collisions to itself
displaced by a whole number of periods. -/
theorem iterate_nextCollision_ne_of_irrational (hχ : ContDiff ℝ 2 χ)
    (hirr : Irrational (h.rotationNumber hχ)) {q : ℕ} (hq : 0 < q) (p : ℤ) (s : ℝ) :
    χ.nextCollision^[q] (s, ψ s) ≠ (s + p * χ.period, ψ s) := fun hs ↦
  hirr ⟨(p : ℚ) / q, by push_cast; exact ((h.rotationNumber_eq_div_iff hχ hq).2 ⟨s, hs⟩).symm⟩

end IsInvariantGraph

/-- **Monotonicity of rotation numbers.** Of two invariant graphs `ψ₁ ≤ ψ₂` of a `C²` table, the
higher one has a rotation number no larger than the lower one: a larger tangential component
lands earlier. -/
theorem IsInvariantGraph.rotationNumber_anti (hχ : ContDiff ℝ 2 χ) {ψ₁ ψ₂ : ℝ → ℝ}
    (h₁ : χ.IsInvariantGraph ψ₁) (h₂ : χ.IsInvariantGraph ψ₂) (hle : ψ₁ ≤ ψ₂) :
    h₂.rotationNumber hχ ≤ h₁.rotationNumber hχ := by
  refine CircleDeg1Lift.translationNumber_mono fun x ↦ ?_
  rw [circleLift_apply, circleLift_apply]
  exact div_le_div_of_nonneg_right ((χ.strictAntiOn_nextParam _).antitoneOn (h₁.mem_Ioo _)
    (h₂.mem_Ioo _) (hle _)) χ.period_pos.le

/-- **Strict monotonicity at irrational rotation numbers.** Of two invariant graphs `ψ₁ < ψ₂` of a
`C²` table, if one of the two rotation numbers is irrational, the higher graph has a strictly
smaller rotation number. -/
theorem IsInvariantGraph.rotationNumber_lt_of_irrational (hχ : ContDiff ℝ 2 χ) {ψ₁ ψ₂ : ℝ → ℝ}
    (h₁ : χ.IsInvariantGraph ψ₁) (h₂ : χ.IsInvariantGraph ψ₂) (hlt : ∀ s, ψ₁ s < ψ₂ s)
    (hirr : Irrational (h₁.rotationNumber hχ) ∨ Irrational (h₂.rotationNumber hχ)) :
    h₂.rotationNumber hχ < h₁.rotationNumber hχ := by
  have hle : ∀ x, h₂.circleLift hχ x < h₁.circleLift hχ x := fun x ↦ by
    rw [circleLift_apply, circleLift_apply]
    exact div_lt_div_of_pos_right (χ.strictAntiOn_nextParam _ (h₁.mem_Ioo _) (h₂.mem_Ioo _)
      (hlt _)) χ.period_pos
  rcases hirr with hirr | hirr
  · exact CircleDeg1Lift.translationNumber_lt_of_forall_lt_of_irrational_right
      (h₂.continuous_circleLift hχ) (h₁.continuous_circleLift hχ) hle hirr
  · exact CircleDeg1Lift.translationNumber_lt_of_forall_lt_of_irrational_left
      (h₂.continuous_circleLift hχ) (h₁.continuous_circleLift hχ) hle hirr

end StrictConvexBilliardTable

end TauCeti
