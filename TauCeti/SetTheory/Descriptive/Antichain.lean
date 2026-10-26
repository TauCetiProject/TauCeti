/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Perfect
public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.Topology.DerivedSet
import Mathlib.Topology.MetricSpace.Perfect
import TauCeti.Topology.Perfect

/-!
# Perfect and Cantor antichains of an equivalence relation

Let `E` be an equivalence relation on a topological space `X` and `A ⊆ X`. Dichotomy theorems
for equivalence relations, such as Silver's theorem, conclude that `E` either has few classes on
`A` or has a large family of pairwise inequivalent points there:

* `E.HasCantorAntichainOn A`: a continuous map of Cantor space `ℕ → Bool` into `A` sending distinct
  points to `E`-inequivalent points. It is automatically injective, by reflexivity of `E`.
* `E.HasPerfectAntichainOn A`: a nonempty perfect subset of `A` of pairwise `E`-inequivalent
  points.
* `E.IsThinOn A`: there is no perfect antichain.

Builders produce the Cantor form; ambient statements use the perfect form. In a Hausdorff space a
Cantor antichain gives a perfect antichain, its range; in a completely metrizable space a perfect
antichain gives a Cantor antichain, through `Perfect.exists_nat_bool_injection`. In particular
the two agree on Polish spaces.

A Cantor antichain on `A` gives continuum many classes, both of `E` and of its restriction
`E.comap ((↑) : A → X)` to `A`. The restriction is reached through
`Setoid.hasCantorAntichainOn_subtype_iff`, which passes Cantor antichains between `A` and the whole
subtype `↥A`.

## Main definitions

* `Setoid.HasCantorAntichainOn`, `Setoid.HasPerfectAntichainOn`, `Setoid.IsThinOn`.

## Main results

* `Setoid.HasCantorAntichainOn.mono`, `Setoid.HasCantorAntichainOn.mono_relation` and their
  perfect and thin counterparts: monotonicity in the ambient set and in the relation.
* `Setoid.HasCantorAntichainOn.mono_topology`: a Cantor antichain for a finer topology is one for
  a coarser topology.
* `Setoid.hasCantorAntichainOn_subtype_iff`: Cantor antichains on `A` and on `↥A`.
* `Setoid.HasCantorAntichainOn.continuum_le_mk_quotient` and
  `Setoid.HasCantorAntichainOn.continuum_le_mk_quotient_comap`: continuum many classes, of `E`
  and of its restriction to `A`.
* `Setoid.HasCantorAntichainOn.hasPerfectAntichainOn` (Hausdorff spaces),
  `Setoid.HasPerfectAntichainOn.hasCantorAntichainOn` (completely metrizable spaces) and
  `Setoid.hasCantorAntichainOn_iff_hasPerfectAntichainOn`.

## References

* Ported from `cameronfreer/infinitary-logic` at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, `InfinitaryLogic/Descriptive/PerfectAntichain.lean`.
* Divergences from that source: the predicates are in the `Setoid` namespace; relation
  monotonicity uses Mathlib's order on setoids; the subtype bridge is an equivalence, with the
  continuum bound for the quotient of the subtype; the perfect-to-Cantor direction assumes a
  completely metrizable topology rather than a complete metric.
-/

public section

open Cardinal Set Topology

universe u

namespace Setoid

variable {X : Type u} [TopologicalSpace X]

/-- `A` carries a **Cantor antichain** for `E`: a continuous map of Cantor space into `A` whose
distinct points have `E`-inequivalent images. -/
def HasCantorAntichainOn (E : Setoid X) (A : Set X) : Prop :=
  ∃ f : (ℕ → Bool) → X, Continuous f ∧ (∀ a, f a ∈ A) ∧ ∀ a b, a ≠ b → ¬ E (f a) (f b)

/-- `A` carries a **perfect antichain** for `E`: a nonempty perfect subset of `A` whose points are
pairwise `E`-inequivalent. -/
def HasPerfectAntichainOn (E : Setoid X) (A : Set X) : Prop :=
  ∃ P : Set X, Perfect P ∧ P.Nonempty ∧ P ⊆ A ∧ ∀ x ∈ P, ∀ y ∈ P, E x y → x = y

/-- `A` is **thin** for `E`: it carries no perfect antichain. -/
def IsThinOn (E : Setoid X) (A : Set X) : Prop :=
  ¬ E.HasPerfectAntichainOn A

variable {E F : Setoid X} {A B : Set X}

/-- Unfolding lemma for `Setoid.HasCantorAntichainOn`. -/
theorem hasCantorAntichainOn_iff : E.HasCantorAntichainOn A ↔
    ∃ f : (ℕ → Bool) → X, Continuous f ∧ (∀ a, f a ∈ A) ∧ ∀ a b, a ≠ b → ¬ E (f a) (f b) :=
  Iff.rfl

/-- Unfolding lemma for `Setoid.HasPerfectAntichainOn`. -/
theorem hasPerfectAntichainOn_iff : E.HasPerfectAntichainOn A ↔
    ∃ P : Set X, Perfect P ∧ P.Nonempty ∧ P ⊆ A ∧ ∀ x ∈ P, ∀ y ∈ P, E x y → x = y :=
  Iff.rfl

/-- Unfolding lemma for `Setoid.IsThinOn`. -/
theorem isThinOn_iff : E.IsThinOn A ↔ ¬ E.HasPerfectAntichainOn A :=
  Iff.rfl

/-! ### Monotonicity -/

/-- A Cantor antichain on `A` is one on every superset of `A`. -/
theorem HasCantorAntichainOn.mono (h : E.HasCantorAntichainOn A) (hAB : A ⊆ B) :
    E.HasCantorAntichainOn B :=
  let ⟨f, hf, hA, hE⟩ := h
  ⟨f, hf, fun a => hAB (hA a), hE⟩

/-- A perfect antichain on `A` is one on every superset of `A`. -/
theorem HasPerfectAntichainOn.mono (h : E.HasPerfectAntichainOn A) (hAB : A ⊆ B) :
    E.HasPerfectAntichainOn B :=
  let ⟨P, hP, hne, hPA, hE⟩ := h
  ⟨P, hP, hne, hPA.trans hAB, hE⟩

/-- A subset of a thin set is thin. -/
theorem IsThinOn.anti (h : E.IsThinOn B) (hAB : A ⊆ B) : E.IsThinOn A :=
  fun hA => h (hA.mono hAB)

/-- A Cantor antichain for a coarser relation `F` is one for the finer relation `E`. -/
theorem HasCantorAntichainOn.mono_relation (hEF : E ≤ F) (h : F.HasCantorAntichainOn A) :
    E.HasCantorAntichainOn A :=
  let ⟨f, hf, hA, hF⟩ := h
  ⟨f, hf, hA, fun a b hab hE => hF a b hab (hEF hE)⟩

/-- A perfect antichain for a coarser relation `F` is one for the finer relation `E`. -/
theorem HasPerfectAntichainOn.mono_relation (hEF : E ≤ F) (h : F.HasPerfectAntichainOn A) :
    E.HasPerfectAntichainOn A :=
  let ⟨P, hP, hne, hPA, hF⟩ := h
  ⟨P, hP, hne, hPA, fun x hx y hy hE => hF x hx y hy (hEF hE)⟩

/-- A set thin for a finer relation `E` is thin for every coarser relation `F`. -/
theorem IsThinOn.mono_relation (hEF : E ≤ F) (h : E.IsThinOn A) : F.IsThinOn A :=
  fun hF => h (hF.mono_relation hEF)

omit [TopologicalSpace X] in
/-- A Cantor antichain for a finer topology `t` is one for every coarser topology `t'`: a witness
continuous into `t` remains continuous into `t'`. This carries witnesses built in a finer, for
example Polish, topology back to the original one. -/
theorem HasCantorAntichainOn.mono_topology {t t' : TopologicalSpace X} (htt' : t ≤ t')
    (h : @HasCantorAntichainOn X t E A) : @HasCantorAntichainOn X t' E A :=
  let ⟨f, hf, hA, hE⟩ := h
  ⟨f, continuous_le_rng htt' hf, hA, hE⟩

/-! ### Injectivity, subtypes and the number of classes -/

/-- A Cantor antichain is injective: equal images are equivalent, by reflexivity. The witness keeps
its antichain property. -/
theorem HasCantorAntichainOn.exists_injective (h : E.HasCantorAntichainOn A) :
    ∃ f : (ℕ → Bool) → X, Continuous f ∧ range f ⊆ A ∧ Function.Injective f ∧
      ∀ a b, a ≠ b → ¬ E (f a) (f b) :=
  let ⟨f, hf, hA, hE⟩ := h
  ⟨f, hf, range_subset_iff.2 hA,
    fun a b hab => by_contra fun hne => hE a b hne (hab ▸ E.refl _), hE⟩

/-- **The subtype bridge.** `A` carries a Cantor antichain for `E` exactly when the whole subtype
`↥A` carries one for the restriction of `E` to `A`. -/
theorem hasCantorAntichainOn_subtype_iff :
    (E.comap ((↑) : A → X)).HasCantorAntichainOn univ ↔ E.HasCantorAntichainOn A := by
  constructor
  · rintro ⟨f, hf, -, hE⟩
    exact ⟨fun a => f a, continuous_subtype_val.comp hf, fun a => (f a).2, hE⟩
  · rintro ⟨f, hf, hA, hE⟩
    exact ⟨fun a => ⟨f a, hA a⟩, hf.subtype_mk _, fun _ => trivial, hE⟩

/-- **Continuum many classes.** If `A` carries a Cantor antichain for `E`, then `E` has at least
continuum many classes. -/
theorem HasCantorAntichainOn.continuum_le_mk_quotient (h : E.HasCantorAntichainOn A) :
    𝔠 ≤ #(Quotient E) := by
  obtain ⟨f, -, -, hE⟩ := h
  have hinj : Function.Injective fun a : ℕ → Bool => (Quotient.mk E (f a)) :=
    fun a b hab => by_contra fun hne => hE a b hne (Quotient.exact hab)
  simpa using lift_mk_le_lift_mk_of_injective hinj

/-- **Continuum many classes on `A`.** If `A` carries a Cantor antichain for `E`, then the
restriction of `E` to `A` has at least continuum many classes. -/
theorem HasCantorAntichainOn.continuum_le_mk_quotient_comap (h : E.HasCantorAntichainOn A) :
    𝔠 ≤ #(Quotient (E.comap ((↑) : A → X))) :=
  (hasCantorAntichainOn_subtype_iff.2 h).continuum_le_mk_quotient

/-! ### Cantor antichains and perfect antichains -/

/-- **A Cantor antichain is a perfect antichain** in a Hausdorff space: its range is closed, as
the continuous injective image of a compact space, and has no isolated points. -/
theorem HasCantorAntichainOn.hasPerfectAntichainOn [T2Space X] (h : E.HasCantorAntichainOn A) :
    E.HasPerfectAntichainOn A := by
  obtain ⟨f, hf, hA, hinj, hE⟩ := h.exists_injective
  refine ⟨range f, ⟨(hf.isClosedEmbedding hinj).isClosed_range, ?_⟩,
    ⟨_, mem_range_self fun _ => false⟩, hA, ?_⟩
  · rintro _ ⟨a, rfl⟩
    -- `AccPt.map` spelled out: dot notation would resolve to `Filter.NeBot.map`.
    -- Cantor space is perfect (`TauCeti.perfectSpace_pi`), so `a` is an accumulation point of
    -- the whole space, and the continuous injection `f` carries this to `f a`
    simpa [Filter.map_principal] using
      AccPt.map (PerfectSpace.univ_preperfect a (mem_univ a)) hf.continuousAt hinj
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
    by_contra hne
    exact hE a b (fun h => hne (congrArg f h)) hab

/-- **A perfect antichain gives a Cantor antichain** in a completely metrizable space, through
the Cantor injection of a nonempty perfect set. -/
theorem HasPerfectAntichainOn.hasCantorAntichainOn [TopologicalSpace.IsCompletelyMetrizableSpace X]
    (h : E.HasPerfectAntichainOn A) : E.HasCantorAntichainOn A := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable X
  obtain ⟨P, hP, hne, hPA, hE⟩ := h
  obtain ⟨f, hfP, hf, hinj⟩ := hP.exists_nat_bool_injection hne
  exact ⟨f, hf, fun a => hPA (hfP (mem_range_self a)),
    fun a b hab hab' => hab (hinj (hE _ (hfP (mem_range_self a)) _ (hfP (mem_range_self b)) hab'))⟩

/-- In a completely metrizable space, in particular a Polish space, Cantor antichains and perfect
antichains exist together. -/
theorem hasCantorAntichainOn_iff_hasPerfectAntichainOn
    [TopologicalSpace.IsCompletelyMetrizableSpace X] :
    E.HasCantorAntichainOn A ↔ E.HasPerfectAntichainOn A :=
  ⟨fun h => h.hasPerfectAntichainOn, fun h => h.hasCantorAntichainOn⟩

/-- In a completely metrizable space, a set is thin exactly when it carries no Cantor
antichain. -/
theorem isThinOn_iff_not_hasCantorAntichainOn [TopologicalSpace.IsCompletelyMetrizableSpace X] :
    E.IsThinOn A ↔ ¬ E.HasCantorAntichainOn A :=
  hasCantorAntichainOn_iff_hasPerfectAntichainOn.not.symm

end Setoid
