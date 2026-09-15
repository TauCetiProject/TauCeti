/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Cost.Basic
public import TauCeti.Probability.HasLaw

/-!
# The Monge problem

The *Monge problem* for a cost `c : X × Y → ℝ≥0∞` and two measures `μ` and `ν` asks for a
transport *map* — a map `T : X → Y` with `ProbabilityTheory.HasLaw T ν μ`, so that `T` pushes
`μ` forward to `ν` — of least cost `∫⁻ x, c (x, T x) ∂μ`. This is the original transport
problem, and it is genuinely harder than the Kantorovich problem
`TauCeti.transportCost` of `TauCeti/MeasureTheory/OptimalTransport/Cost/Basic.lean`, whose
feasible set is the couplings: the feasible set here can be empty when the Kantorovich one is
not, so `TauCeti.mongeCost` is only an upper bound for `TauCeti.transportCost`.

This file introduces the objective `TauCeti.transportMapCost`, the value
`TauCeti.mongeCost`, the two optimality predicates for maps, and the relations between them.
The relaxation `TauCeti.transportCost_le_mongeCost` is the passage from Monge to Kantorovich,
and it comes from the graph plan of `TauCeti/MeasureTheory/OptimalTransport/GraphPlan.lean`:
every transport map induces a coupling whose cost is at most the map cost. Its equality case,
`TauCeti.isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan`, says that a map is
optimal for the Kantorovich value exactly when its graph plan is an optimal plan; this is the
form in which the existence of an optimal map is proved downstream, where a plan is first shown
to be deterministic and then read as a map.

The inequality is strict in general: `TauCeti.transportCost_lt_mongeCost_dirac` splits a Dirac
source, whose mass cannot be divided by any map, over a target that is null on singletons. So a
statement about transport maps really is a statement about `TauCeti.mongeCost`, and the two
optimality notions for maps — minimality among maps, `TauCeti.IsMongeMinimizer`, and attainment
of the Kantorovich value, `TauCeti.IsKantorovichOptimalTransportMap` — are kept apart: the second
implies the first, and the gap between them is exactly the gap between the two values.

The definitions and the relaxation need no topology and no normalisation (only the strict
example asks for a probability target), and the two factors are arbitrary measurable spaces; the
cost is extended-nonnegative and integrated by `lintegral`, so an infeasible problem
and a feasible problem whose maps all have infinite cost both take the value `∞`; the value alone
does not distinguish these cases. `TauCeti.exists_hasLaw_of_mongeCost_ne_top` only proves that a
non-top value implies feasibility.

## Main definitions

* `TauCeti.transportMapCost c μ T` — the cost `∫⁻ x, c (x, T x) ∂μ` of transporting `μ` by the
  map `T`, the objective of the Monge problem;
* `TauCeti.mongeCost c μ ν` — the Monge value: the infimum of `TauCeti.transportMapCost c μ T`
  over the transport maps `T` from `μ` to `ν`, and `∞` when there are none;
* `TauCeti.IsMongeMinimizer c μ ν T` — `T` is a transport map attaining the Monge value;
* `TauCeti.IsKantorovichOptimalTransportMap c μ ν T` — `T` is a transport map whose cost is the
  Kantorovich value `TauCeti.transportCost c μ ν`.

## Main statements

* `TauCeti.transportCost_le_mongeCost` — **the Monge-to-Kantorovich relaxation inequality**, the
  Monge value dominates the Kantorovich value;
* `TauCeti.transportCost_lt_mongeCost_dirac` — the inequality is strict for a Dirac source and
  a target that is null on singletons, where
  `TauCeti.mongeCost_eq_top_of_measure_singleton_ne_zero` makes the Monge problem infeasible
  while the Kantorovich problem is not;
* `TauCeti.mongeCost_eq_top_of_measure_atom` — a positive finite-mass measurable atom makes the
  Monge problem infeasible when the standard Borel target law is null on singletons;
* `TauCeti.isMongeMinimizer_iff` — minimality among transport maps is the form of
  `TauCeti.IsMongeMinimizer` that avoids the value `TauCeti.mongeCost c μ ν`, which may be `∞`;
* `TauCeti.IsKantorovichOptimalTransportMap.isMongeMinimizer` and
  `TauCeti.isKantorovichOptimalTransportMap_iff` — a map attaining the Kantorovich value is a
  Monge minimizer, and forces the two values to agree; the converse needs that agreement;
* `TauCeti.isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan` — the equality case
  of the relaxation: a transport map attains the Kantorovich value exactly when its graph plan
  is an optimal plan;
* `TauCeti.isKantorovichOptimalTransportMap_id` and `TauCeti.mongeCost_self_eq_zero` — for a
  cost vanishing on the diagonal the identity transports any measure onto itself at no cost;
* `TauCeti.isKantorovichOptimalTransportMap_dirac_dirac` and `TauCeti.mongeCost_dirac_dirac` —
  between two Dirac measures the constant transport map is optimal and the Monge value is the
  value of the cost at the pair.

## Implementation notes

`TauCeti.mongeCost` is an iterated `⨅` over maps and over proofs of
`ProbabilityTheory.HasLaw`, matching `TauCeti.transportCost`: an empty feasible set gives `∞`
with no case split.

The two optimality predicates are structures extending `ProbabilityTheory.HasLaw`, so that a
minimizer carries its transport-map hypothesis, exactly as `TauCeti.IsOptimalCoupling` extends
`TauCeti.IsCoupling`.

Transport maps are only assumed `μ`-almost everywhere measurable, since that is what
`ProbabilityTheory.HasLaw` supplies; `TauCeti.transportMapCost_congr` shows the objective only
sees a map up to `μ`-a.e. equality, and `TauCeti.IsMongeMinimizer.congr` propagates this to the
minimizers.

## References

* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  §1.1.1, where the Monge problem is stated and relaxed to the Kantorovich problem.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Progress in Nonlinear
  Differential Equations and their Applications 87, 2015, §1.1, for the Dirac counterexample to
  equality of the two values.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti

universe u v

variable {X : Type u} {Y : Type v} [MeasurableSpace X]
  {c c' : X × Y → ℝ≥0∞} {μ : Measure X} {T S : X → Y} {a : ℝ≥0∞}

/-! ### The cost of a transport map -/

/-- The cost of transporting `μ` by the map `T`: the mass at `x` travels to `T x`, at price
`c (x, T x)`. This is the objective of the Monge problem, whose value is
`TauCeti.mongeCost`. -/
def transportMapCost (c : X × Y → ℝ≥0∞) (μ : Measure X) (T : X → Y) : ℝ≥0∞ :=
  ∫⁻ x, c (x, T x) ∂μ

/-- The cost of a transport map as its defining integral, exposed as a convenient rewrite
lemma. -/
theorem transportMapCost_def : transportMapCost c μ T = ∫⁻ x, c (x, T x) ∂μ := (rfl)

/-- There is nothing to transport out of the zero measure. -/
@[simp]
theorem transportMapCost_zero_measure (c : X × Y → ℝ≥0∞) (T : X → Y) :
    transportMapCost c (0 : Measure X) T = 0 := by
  rw [transportMapCost_def, lintegral_zero_measure]

/-- The cost of a transport map only depends on the map up to `μ`-almost everywhere equality,
which is the equivalence `ProbabilityTheory.HasLaw` is invariant under. -/
theorem transportMapCost_congr (h : T =ᵐ[μ] S) (c : X × Y → ℝ≥0∞) :
    transportMapCost c μ T = transportMapCost c μ S := by
  rw [transportMapCost_def, transportMapCost_def]
  exact lintegral_congr_ae <| h.mono fun x hx ↦ by simp only [hx]

/-- The cost of a transport map is monotone in the cost function. -/
@[gcongr]
theorem transportMapCost_mono (h : c ≤ c') : transportMapCost c μ T ≤ transportMapCost c' μ T := by
  rw [transportMapCost_def, transportMapCost_def]
  exact lintegral_mono fun _ ↦ h _

/-- A Dirac source leaves a map nothing to integrate: the cost of `T` is the cost of its single
move. -/
@[simp]
theorem transportMapCost_dirac [MeasurableSingletonClass X] (c : X × Y → ℝ≥0∞) (x : X)
    (T : X → Y) : transportMapCost c (Measure.dirac x) T = c (x, T x) := by
  rw [transportMapCost_def, lintegral_dirac]

variable [MeasurableSpace Y] {ν : Measure Y}

/-- The cost of a transport map is the cost integral of its graph plan. -/
theorem transportMapCost_eq_lintegral_graphPlan (hT : AEMeasurable T μ)
    (hc : AEMeasurable c (graphPlan T μ)) :
    transportMapCost c μ T = ∫⁻ z, c z ∂graphPlan T μ := by
  rw [transportMapCost_def, lintegral_graphPlan hT hc]

/-! ### The Monge value -/

/-- The **Monge value** of `μ` and `ν` for the cost `c`: the infimum of
`TauCeti.transportMapCost c μ T` over the transport maps `T` from `μ` to `ν`. It is `∞` when
`μ` and `ν` admit no transport map at all, which — unlike for `TauCeti.transportCost` — happens
already for a Dirac `μ` and a `ν` that is null on singletons. -/
def mongeCost (c : X × Y → ℝ≥0∞) (μ : Measure X) (ν : Measure Y) : ℝ≥0∞ :=
  ⨅ (T : X → Y) (_ : HasLaw T ν μ), transportMapCost c μ T

/-- The Monge value as the infimum of the costs of all transport maps. -/
theorem mongeCost_def :
    mongeCost c μ ν = ⨅ (T : X → Y) (_ : HasLaw T ν μ), transportMapCost c μ T := (rfl)

/-- Every transport map bounds the Monge value from above. -/
theorem mongeCost_le_transportMapCost (hT : HasLaw T ν μ) (c : X × Y → ℝ≥0∞) :
    mongeCost c μ ν ≤ transportMapCost c μ T := by
  rw [mongeCost_def]
  exact iInf₂_le T hT

/-- A bound valid on every transport map bounds the Monge value from below. -/
theorem le_mongeCost (h : ∀ T, HasLaw T ν μ → a ≤ transportMapCost c μ T) :
    a ≤ mongeCost c μ ν := by
  rw [mongeCost_def]
  exact le_iInf₂ h

/-- The Monge value is below a threshold exactly when some transport map is. -/
theorem mongeCost_lt_iff :
    mongeCost c μ ν < a ↔ ∃ T, HasLaw T ν μ ∧ transportMapCost c μ T < a := by
  simp only [mongeCost, iInf_lt_iff, exists_prop]

/-- The Monge value is monotone in the cost function. -/
@[gcongr]
theorem mongeCost_mono (h : c ≤ c') : mongeCost c μ ν ≤ mongeCost c' μ ν := by
  rw [mongeCost_def, mongeCost_def]
  exact iInf₂_mono fun _ _ ↦ transportMapCost_mono h

/-- An infeasible Monge problem has value `∞`. -/
theorem mongeCost_eq_top_of_not_exists_hasLaw (h : ¬∃ T : X → Y, HasLaw T ν μ)
    (c : X × Y → ℝ≥0∞) : mongeCost c μ ν = ⊤ :=
  eq_top_iff.2 <| le_mongeCost fun T hT ↦ absurd ⟨T, hT⟩ h

/-- A finite Monge value is witnessed by a transport map. The converse fails: feasibility does not
guarantee a finite-cost transport map, since every feasible map may have infinite cost. This is why
the result is not stated as an `iff` with `TauCeti.mongeCost_eq_top_of_not_exists_hasLaw`. -/
theorem exists_hasLaw_of_mongeCost_ne_top (h : mongeCost c μ ν ≠ ⊤) :
    ∃ T : X → Y, HasLaw T ν μ := by
  obtain ⟨T, hT, -⟩ := mongeCost_lt_iff.1 h.lt_top
  exact ⟨T, hT⟩

/-- **The Monge-to-Kantorovich relaxation inequality**: the Kantorovich value of `μ` and `ν` is
at most their Monge value, because the graph plan of a transport map is a coupling whose cost is
at most the map cost. The inequality can be strict — see
`TauCeti.transportCost_lt_mongeCost_dirac` — and its
equality case at a fixed map is
`TauCeti.isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan`. -/
theorem transportCost_le_mongeCost (c : X × Y → ℝ≥0∞) (μ : Measure X) (ν : Measure Y) :
    transportCost c μ ν ≤ mongeCost c μ ν :=
  le_mongeCost fun T hT ↦ by
    rw [transportMapCost_def]; exact transportCost_le_lintegral_of_hasLaw hT c

/-! ### Optimal transport maps -/

/-- `IsMongeMinimizer c μ ν T` says that `T` solves the Monge problem: it is a transport map
from `μ` to `ν`, and its cost is the Monge value of the pair. -/
structure IsMongeMinimizer (c : X × Y → ℝ≥0∞) (μ : Measure X) (ν : Measure Y) (T : X → Y) : Prop
    extends HasLaw T ν μ where
  /-- A Monge minimizer attains the Monge value. -/
  transportMapCost_eq : transportMapCost c μ T = mongeCost c μ ν

/-- `IsKantorovichOptimalTransportMap c μ ν T` says that `T` is a transport map from `μ` to `ν`
whose cost is the *Kantorovich* value of the pair. By `TauCeti.transportCost_le_mongeCost` this
is the stronger of the two optimality notions: such a map is a Monge minimizer,
`TauCeti.IsKantorovichOptimalTransportMap.isMongeMinimizer`, and it forces the two values to
agree. It is the conclusion of the existence theorems for optimal maps, which produce a map out
of an optimal plan. -/
structure IsKantorovichOptimalTransportMap (c : X × Y → ℝ≥0∞) (μ : Measure X) (ν : Measure Y)
    (T : X → Y) : Prop extends HasLaw T ν μ where
  /-- A Kantorovich-optimal transport map attains the Kantorovich value. -/
  transportMapCost_eq : transportMapCost c μ T = transportCost c μ ν

namespace IsMongeMinimizer

/-- A Monge minimizer costs no more than any other transport map of the same pair. -/
theorem transportMapCost_le (h : IsMongeMinimizer c μ ν T) (hS : HasLaw S ν μ) :
    transportMapCost c μ T ≤ transportMapCost c μ S :=
  h.transportMapCost_eq.trans_le (mongeCost_le_transportMapCost hS c)

/-- Being a Monge minimizer only depends on the map up to `μ`-almost everywhere equality. -/
protected theorem congr (h : IsMongeMinimizer c μ ν T) (hS : S =ᵐ[μ] T) :
    IsMongeMinimizer c μ ν S where
  toHasLaw := h.toHasLaw.congr hS
  transportMapCost_eq := by rw [transportMapCost_congr hS, h.transportMapCost_eq]

end IsMongeMinimizer

/-- Being a Monge minimizer is minimality among the transport maps. This form of the definition
avoids the value `TauCeti.mongeCost c μ ν`, so it is the one to check when that value may be
`∞`. -/
theorem isMongeMinimizer_iff :
    IsMongeMinimizer c μ ν T ↔
      HasLaw T ν μ ∧ ∀ S, HasLaw S ν μ → transportMapCost c μ T ≤ transportMapCost c μ S :=
  ⟨fun h ↦ ⟨h.toHasLaw, fun _ hS ↦ h.transportMapCost_le hS⟩, fun ⟨hT, h⟩ ↦
    ⟨hT, le_antisymm (le_mongeCost h) (mongeCost_le_transportMapCost hT c)⟩⟩

namespace IsKantorovichOptimalTransportMap

/-- A map attaining the Kantorovich value closes the gap in
`TauCeti.transportCost_le_mongeCost`: the two values agree. -/
theorem mongeCost_eq_transportCost (h : IsKantorovichOptimalTransportMap c μ ν T) :
    mongeCost c μ ν = transportCost c μ ν :=
  le_antisymm (h.transportMapCost_eq ▸ mongeCost_le_transportMapCost h.toHasLaw c)
    (transportCost_le_mongeCost c μ ν)

/-- A map attaining the Kantorovich value is a Monge minimizer. -/
theorem isMongeMinimizer (h : IsKantorovichOptimalTransportMap c μ ν T) :
    IsMongeMinimizer c μ ν T where
  toHasLaw := h.toHasLaw
  transportMapCost_eq := h.transportMapCost_eq.trans h.mongeCost_eq_transportCost.symm

/-- Attaining the Kantorovich value only depends on the map up to `μ`-almost everywhere
equality. -/
protected theorem congr (h : IsKantorovichOptimalTransportMap c μ ν T) (hS : S =ᵐ[μ] T) :
    IsKantorovichOptimalTransportMap c μ ν S where
  toHasLaw := h.toHasLaw.congr hS
  transportMapCost_eq := by rw [transportMapCost_congr hS, h.transportMapCost_eq]

end IsKantorovichOptimalTransportMap

/-- A Monge minimizer attains the Kantorovich value exactly when the two values agree. So the
two optimality notions for maps differ by exactly the gap in
`TauCeti.transportCost_le_mongeCost`. -/
theorem isKantorovichOptimalTransportMap_iff :
    IsKantorovichOptimalTransportMap c μ ν T ↔
      IsMongeMinimizer c μ ν T ∧ mongeCost c μ ν = transportCost c μ ν :=
  ⟨fun h ↦ ⟨h.isMongeMinimizer, h.mongeCost_eq_transportCost⟩,
    fun ⟨h, he⟩ ↦ ⟨h.toHasLaw, h.transportMapCost_eq.trans he⟩⟩

/-- **The equality case of the relaxation inequality at a fixed map**: a transport map attains
the Kantorovich value exactly when its graph plan is an optimal plan. This is how an optimal map
is read off an optimal plan that has been shown to be deterministic. -/
theorem isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan (hT : HasLaw T ν μ)
    (hc : AEMeasurable c (graphPlan T μ)) :
    IsKantorovichOptimalTransportMap c μ ν T ↔ IsOptimalCoupling c (graphPlan T μ) μ ν := by
  rw [isOptimalCoupling_graphPlan_iff hT hc]
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨hT, ?_⟩⟩
  · rw [← lintegral_graphPlan hT.aemeasurable hc,
      ← transportMapCost_eq_lintegral_graphPlan hT.aemeasurable hc, h.transportMapCost_eq]
  · rw [transportMapCost_eq_lintegral_graphPlan hT.aemeasurable hc,
      lintegral_graphPlan hT.aemeasurable hc, h]

/-! ### Transporting a measure to itself -/

/-- A cost vanishing on the diagonal makes the identity a free transport map, so the Monge
problem of a measure with itself has value `0` for every measure. -/
theorem mongeCost_self_eq_zero {c : X × X → ℝ≥0∞} (hc : ∀ x, c (x, x) = 0) (μ : Measure X) :
    mongeCost c μ μ = 0 :=
  nonpos_iff_eq_zero.1 <| (mongeCost_le_transportMapCost HasLaw.id c).trans_eq <| by
    rw [transportMapCost_def]; simp [hc]

/-- The identity is a Kantorovich-optimal transport map of a measure onto itself whenever the
cost vanishes on the diagonal. Together with `TauCeti.mongeCost_self_eq_zero` this exhibits both
optimality notions at an arbitrary measure, not only at Dirac measures. -/
theorem isKantorovichOptimalTransportMap_id {c : X × X → ℝ≥0∞} (hc : ∀ x, c (x, x) = 0)
    (μ : Measure X) : IsKantorovichOptimalTransportMap c μ μ id where
  toHasLaw := HasLaw.id
  transportMapCost_eq := by
    have h : transportCost c μ μ = 0 :=
      nonpos_iff_eq_zero.1 <|
        (transportCost_le_mongeCost c μ μ).trans_eq (mongeCost_self_eq_zero hc μ)
    rw [transportMapCost_def, h]
    simp [hc]

/-! ### Dirac measures -/

/-- Between two Dirac measures the constant map is a transport map attaining the Kantorovich
value computed by `TauCeti.transportCost_dirac_dirac`. -/
theorem isKantorovichOptimalTransportMap_dirac_dirac (hc : Measurable c) (x : X) (y : Y) :
    IsKantorovichOptimalTransportMap c (Measure.dirac x) (Measure.dirac y) (fun _ ↦ y) where
  aemeasurable := aemeasurable_const
  map_eq := Measure.map_dirac' measurable_const x
  transportMapCost_eq := by
    have hcxy : Measurable (fun x' : X ↦ c (x', y)) :=
      hc.comp (measurable_id.prodMk measurable_const)
    rw [transportMapCost_def, lintegral_dirac' x hcxy, transportCost_dirac_dirac hc]

/-- The Monge value of two Dirac measures is the value of the cost at the pair, matching
`TauCeti.transportCost_dirac_dirac`. -/
theorem mongeCost_dirac_dirac (hc : Measurable c) (x : X) (y : Y) :
    mongeCost c (Measure.dirac x) (Measure.dirac y) = c (x, y) :=
  (isKantorovichOptimalTransportMap_dirac_dirac hc x y).mongeCost_eq_transportCost.trans
    (transportCost_dirac_dirac hc x y)

/-! ### Source atoms obstruct the Monge problem -/

/-- **A positive finite-mass source atom makes the Monge problem infeasible over a singleton-null
standard Borel target.** An a.e.-measurable map sends the entire mass of the atom to one point,
whereas a law that is null on singletons gives that point no mass. Consequently the Monge value
is `∞` for every cost. -/
theorem mongeCost_eq_top_of_measure_atom [StandardBorelSpace Y]
    [NullSingletonClass ν] {A : Set X} (hAfin : μ A ≠ ⊤) (hAatom : μ.IsAtom A)
    (c : X × Y → ℝ≥0∞) : mongeCost c μ ν = ⊤ :=
  mongeCost_eq_top_of_not_exists_hasLaw
    (fun ⟨T, hT⟩ ↦
      TauCeti.Probability.not_hasLaw_of_measure_atom hAfin hAatom T hT) c

/-- **A nonzero source singleton makes the Monge problem infeasible over a target that is null on
singletons.** No map can split the mass sitting at a single point, so such a source has no
transport map onto the target, and the Monge value is `∞` for every cost. -/
theorem mongeCost_eq_top_of_measure_singleton_ne_zero [NullSingletonClass ν] {x : X}
    (hx : μ {x} ≠ 0) (c : X × Y → ℝ≥0∞) : mongeCost c μ ν = ⊤ :=
  mongeCost_eq_top_of_not_exists_hasLaw
    (fun ⟨_, hT⟩ ↦ Probability.not_hasLaw_of_measure_singleton_ne_zero hx _ hT) c

/-- **The relaxation inequality is strict in general.** Splitting a Dirac source over an
target that is null on singletons and has finite cost is a Kantorovich problem with a finite
value and a Monge problem with no competitor at all. This is the standard obstruction to
Monge's problem: there is no map carrying a point mass onto such a measure. -/
theorem transportCost_lt_mongeCost_dirac [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (hc : Measurable c) {x : X} (h : ∫⁻ y, c (x, y) ∂ν ≠ ⊤) :
    transportCost c (Measure.dirac x) ν < mongeCost c (Measure.dirac x) ν := by
  have hx : Measure.dirac x {x} ≠ 0 := by
    rw [Measure.dirac_apply_of_mem (mem_singleton x)]
    exact one_ne_zero
  rw [transportCost_dirac_left hc x, mongeCost_eq_top_of_measure_singleton_ne_zero hx c]
  exact h.lt_top

end TauCeti
