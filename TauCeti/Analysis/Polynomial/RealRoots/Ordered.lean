/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.RealRoots.Basic
public import Mathlib.Topology.LocallyConstant.Basic

import Mathlib.Data.Finset.Sort
import TauCeti.Topology.MetricSpace.SeparatedBalls

/-!
# Ordered real roots in continuous polynomial families

For a real polynomial family of fixed degree with continuous coefficients, a locally
nonincreasing number of distinct complex roots forces its increasing enumeration of real roots
to vary continuously. The multiplicity at each position is locally constant. On a preconnected
base, both the number of real roots and their ordered multiplicities are constant, so a single
finite ordered list gives continuous root functions on the whole base.

The local statements require a strictly increasing complete enumeration only near the parameter,
without assuming its continuity. The connected existence theorem constructs it using Mathlib's
`Finset.orderEmbOfFin`, and excludes zero fibers by its fixed-degree hypothesis. Constant
polynomials and empty root lists are included.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Springer, 2006, §5.1 (continuity of roots with respect to coefficients).
-/

public section

open Filter Metric Topology

namespace Polynomial

variable {B : Type*} [TopologicalSpace B] {F : B → ℝ[X]} {d n : ℕ}

/-- An increasing complete enumeration of the distinct real roots moves arbitrarily little
near `x₀` and preserves multiplicities, when the coefficients are continuous, the degree is
locally fixed, and the number of distinct complex roots is locally nonincreasing. The enumeration
is required to be increasing and complete only near `x₀`; no continuity is assumed. -/
theorem eventually_ordered_roots_close_of_card_aroots_le {x₀ : B}
    (hF : ∀ i ≤ d, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).degree = d)
    (hcard : ∀ᶠ x in 𝓝 x₀,
      ((F x).aroots ℂ).toFinset.card ≤ ((F x₀).aroots ℂ).toFinset.card)
    {r : B → Fin n → ℝ} (hr : ∀ᶠ x in 𝓝 x₀, StrictMono (r x))
    (hroots : ∀ᶠ x in 𝓝 x₀, Set.range (r x) = (F x).roots.toFinset)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∀ i,
      |r x i - r x₀ i| < ε ∧ (F x).rootMultiplicity (r x i) =
        (F x₀).rootMultiplicity (r x₀ i) := by
  classical
  have hr₀ := hr.self_of_nhds
  have hroots₀ := hroots.self_of_nhds
  obtain ⟨δ, hδ, _, hsep⟩ := TauCeti.exists_pos_closedBall_subset_and_lt_dist
    (T := (F x₀).roots.toFinset) (U := fun _ => Set.univ) (fun _ _ => univ_mem)
  have hmem {x : B} (hx : Set.range (r x) = (F x).roots.toFinset) (i : Fin n) :
      r x i ∈ (F x).roots.toFinset := by
    rw [← Finset.mem_coe, ← hx]
    exact Set.mem_range_self i
  filter_upwards [eventually_exists_bijOn_roots_toFinset_of_card_aroots_le
    hF hdeg hcard (lt_min hε hδ), hr, hroots] with x ⟨e, he, hed⟩ hrx hrootsx
  have hclose (i : Fin n) := hed (r x₀ i) (Multiset.mem_toFinset.1 (hmem hroots₀ i))
  have hmono : StrictMono (fun i => e (r x₀ i)) := by
    intro i j hij
    have hij' := hr₀ hij
    have hd := hsep _ (hmem hroots₀ i) _ (hmem hroots₀ j) (ne_of_lt hij')
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hij'.le)] at hd
    have hi := (abs_lt.1 (hclose i).1).2
    have hj := (abs_lt.1 (hclose j).1).1
    have := min_le_right ε δ
    linarith
  have heq : (fun i => e (r x₀ i)) = r x := by
    apply (hmono.range_inj_of_wellFoundedLT hrx).1
    rw [← Function.comp_def, Set.range_comp, hroots₀, he.image_eq, hrootsx]
  intro i
  rw [← congrFun heq i]
  exact ⟨(hclose i).1.trans_le (min_le_left ε δ), (hclose i).2⟩

/-- Every position in an increasing complete enumeration of real roots is continuous at a
parameter where the coefficients are continuous, the degree is locally fixed, and the number
of distinct complex roots is locally nonincreasing. The enumeration is required to be
increasing and complete only near that parameter. -/
theorem continuousAt_ordered_root_of_card_aroots_le {x₀ : B}
    (hF : ∀ i ≤ d, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).degree = d)
    (hcard : ∀ᶠ x in 𝓝 x₀,
      ((F x).aroots ℂ).toFinset.card ≤ ((F x₀).aroots ℂ).toFinset.card)
    {r : B → Fin n → ℝ} (hr : ∀ᶠ x in 𝓝 x₀, StrictMono (r x))
    (hroots : ∀ᶠ x in 𝓝 x₀, Set.range (r x) = (F x).roots.toFinset) (i : Fin n) :
    ContinuousAt (fun x => r x i) x₀ := by
  refine Metric.continuousAt_iff'.2 fun ε hε => ?_
  filter_upwards [eventually_ordered_roots_close_of_card_aroots_le
    hF hdeg hcard hr hroots hε] with x hx
  simpa only [Real.dist_eq] using (hx i).1

/-- Multiplicity at each position in an increasing complete enumeration of real roots is
locally constant, provided the coefficient and root-count hypotheses hold at every parameter. -/
theorem isLocallyConstant_rootMultiplicity_ordered_root_of_card_aroots_le
    (hF : ∀ i ≤ d, Continuous (fun x => (F x).coeff i))
    (hdeg : ∀ x, (F x).degree = d)
    (hcard : ∀ x₀, ∀ᶠ x in 𝓝 x₀,
      ((F x).aroots ℂ).toFinset.card ≤ ((F x₀).aroots ℂ).toFinset.card)
    {r : B → Fin n → ℝ} (hr : ∀ x, StrictMono (r x))
    (hroots : ∀ x, Set.range (r x) = (F x).roots.toFinset) (i : Fin n) :
    IsLocallyConstant (fun x => (F x).rootMultiplicity (r x i)) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x₀ => ?_
  filter_upwards [eventually_ordered_roots_close_of_card_aroots_le
    (fun i hi => (hF i hi).continuousAt) (Eventually.of_forall hdeg) (hcard x₀)
    (Eventually.of_forall hr) (Eventually.of_forall hroots) one_pos] with x hx
  exact (hx i).2

/-- The number of distinct real roots is constant on a preconnected base if the degree is
fixed, the coefficients are continuous, and the number of distinct complex roots is locally
nonincreasing. -/
theorem card_roots_toFinset_eq_of_preconnectedSpace [PreconnectedSpace B]
    (hF : ∀ i ≤ d, Continuous (fun x => (F x).coeff i))
    (hdeg : ∀ x, (F x).degree = d)
    (hcard : ∀ x₀, ∀ᶠ x in 𝓝 x₀,
      ((F x).aroots ℂ).toFinset.card ≤ ((F x₀).aroots ℂ).toFinset.card) (x y : B) :
    (F x).roots.toFinset.card = (F y).roots.toFinset.card := by
  have hlocal : IsLocallyConstant (fun x => (F x).roots.toFinset.card) :=
    (IsLocallyConstant.iff_eventually_eq _).2 fun x₀ =>
      eventually_card_roots_toFinset_eq_of_card_aroots_le
        (fun i hi => (hF i hi).continuousAt) (Eventually.of_forall hdeg) (hcard x₀)
  exact hlocal.apply_eq_of_preconnectedSpace x y

/-- On a nonempty preconnected base, a fixed-degree continuous polynomial family with locally
nonincreasing number of distinct complex roots has a global finite increasing enumeration of
all its real zeros by continuous functions. The multiplicity at each position is constant.
No fixed real root count or continuous root enumeration is assumed. -/
theorem exists_continuous_ordered_roots_of_preconnectedSpace [PreconnectedSpace B] [Nonempty B]
    (hF : ∀ i ≤ d, Continuous (fun x => (F x).coeff i))
    (hdeg : ∀ x, (F x).degree = d)
    (hcard : ∀ x₀, ∀ᶠ x in 𝓝 x₀,
      ((F x).aroots ℂ).toFinset.card ≤ ((F x₀).aroots ℂ).toFinset.card) :
    ∃ n : ℕ, ∃ r : B → Fin n → ℝ,
      (∀ i, Continuous (fun x => r x i)) ∧ (∀ x, StrictMono (r x)) ∧
      (∀ x t, (F x).IsRoot t ↔ ∃ i, r x i = t) ∧
      (∀ i x y, (F x).rootMultiplicity (r x i) = (F y).rootMultiplicity (r y i)) := by
  classical
  let x₀ : B := Classical.arbitrary B
  let n := (F x₀).roots.toFinset.card
  have hcount (x : B) : (F x).roots.toFinset.card = n :=
    card_roots_toFinset_eq_of_preconnectedSpace hF hdeg hcard x x₀
  let r (x : B) : Fin n → ℝ := (F x).roots.toFinset.orderEmbOfFin (hcount x)
  have hr (x : B) : StrictMono (r x) := (Finset.orderEmbOfFin _ _).strictMono
  have hroots (x : B) : Set.range (r x) = (F x).roots.toFinset :=
    Finset.range_orderEmbOfFin _ _
  refine ⟨n, r, fun i => continuous_iff_continuousAt.2 (fun x => ?_), hr, ?_, ?_⟩
  · exact continuousAt_ordered_root_of_card_aroots_le
      (fun i hi => (hF i hi).continuousAt) (Eventually.of_forall hdeg) (hcard x)
      (Eventually.of_forall hr) (Eventually.of_forall hroots) i
  · intro x t
    have hne : F x ≠ 0 := degree_ne_bot.1 (by rw [hdeg x]; exact WithBot.coe_ne_bot)
    rw [← mem_roots hne, ← Multiset.mem_toFinset, ← Finset.mem_coe, ← hroots x]
    rfl
  · intro i x y
    exact (isLocallyConstant_rootMultiplicity_ordered_root_of_card_aroots_le
      hF hdeg hcard hr hroots i).apply_eq_of_preconnectedSpace x y

end Polynomial

end
