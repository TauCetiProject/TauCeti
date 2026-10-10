/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# Moore paths

A **Moore path** in a space `X` is a continuous map `γ : [0, ∞) → X` together with a duration
`L ≥ 0` at which it stops: `γ t = γ L` for every `t ≥ L`.  Unlike the paths of `Path`, which are
parametrized by the unit interval, Moore paths concatenate by placing one after the other with the
durations adding up, and this concatenation is strictly associative with strict units.  The Moore
loops at a point therefore form a topological monoid, whose chains are a differential graded
algebra without any Eilenberg–Zilber correction.  The constant path of duration `0` is the unit;
for `X` a point the Moore loop space is `[0, ∞)`, so it is not homeomorphic to `Map_*(S¹, X)`.

The space of Moore paths is topologized as a subspace of `ℝ≥0 × C(ℝ≥0, X)`, with the compact-open
topology on the second factor.  Since `ℝ≥0` is locally compact, evaluation is continuous and a map
into `MoorePath X` is continuous exactly when its duration and its uncurried evaluation are.

This file defines the carrier, its topology, the end points and the constant paths.
Concatenation, loops and the comparison with `Path` are in subsequent files.

## Main definitions

* `TauCeti.MoorePath X`: Moore paths in `X`, with `length`, `source` and `target`.
* `TauCeti.MoorePath.const x`: the constant path of duration `0` at `x`.
* `TauCeti.MoorePath.pathsBetween A B`: the paths starting in `A` and ending in `B`.

## Main results

* `TauCeti.MoorePath.isEmbedding_toProd`: `γ ↦ (γ.length, γ)` embeds `MoorePath X` into
  `ℝ≥0 × C(ℝ≥0, X)`.
* `TauCeti.MoorePath.continuous_eval`, `continuous_source`, `continuous_target`,
  `continuous_length`.
* `TauCeti.MoorePath.continuous_iff`: continuity of a map into `MoorePath X` is continuity of the
  duration and of the uncurried evaluation.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Section 7.1.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter III.
-/

public section

open NNReal Topology

namespace TauCeti

universe u

/-- A **Moore path** in `X`: a continuous map `[0, ∞) → X` together with a duration `length`
from which on the map is constant. -/
structure MoorePath (X : Type u) [TopologicalSpace X] extends C(ℝ≥0, X) where
  /-- The duration of the path. -/
  length : ℝ≥0
  /-- The path is stopped from time `length` on. -/
  stopped' : ∀ t, length ≤ t → toFun t = toFun length

namespace MoorePath

variable {X : Type u} [TopologicalSpace X]

instance : CoeFun (MoorePath X) fun _ ↦ ℝ≥0 → X := ⟨fun γ ↦ γ.toContinuousMap⟩

@[simp]
theorem mk_apply (f : C(ℝ≥0, X)) (L : ℝ≥0) (h : ∀ t, L ≤ t → f t = f L) (t : ℝ≥0) :
    (⟨f, L, h⟩ : MoorePath X) t = f t :=
  (rfl)

@[simp]
theorem mk_length (f : C(ℝ≥0, X)) (L : ℝ≥0) (h : ∀ t, L ≤ t → f t = f L) :
    (⟨f, L, h⟩ : MoorePath X).length = L :=
  (rfl)

theorem continuous (γ : MoorePath X) : Continuous γ :=
  γ.continuous_toFun

/-- A Moore path is constant from its duration on. -/
theorem apply_of_length_le (γ : MoorePath X) {t : ℝ≥0} (h : γ.length ≤ t) : γ t = γ γ.length :=
  γ.stopped' t h

/-- Two Moore paths with the same duration and the same values are equal. -/
@[ext]
theorem ext {γ δ : MoorePath X} (hl : γ.length = δ.length) (h : ∀ t, γ t = δ t) : γ = δ := by
  obtain ⟨⟨f, hf⟩, L, hs⟩ := γ
  obtain ⟨⟨g, hg⟩, L', hs'⟩ := δ
  dsimp only at hl
  subst hl
  have : f = g := funext h
  subst this
  rfl

/-- The starting point of a Moore path. -/
def source (γ : MoorePath X) : X := γ 0

/-- The end point of a Moore path. -/
def target (γ : MoorePath X) : X := γ γ.length

theorem source_eq_apply (γ : MoorePath X) : γ.source = γ 0 :=
  (rfl)

theorem target_eq_apply (γ : MoorePath X) : γ.target = γ γ.length :=
  (rfl)

theorem apply_eq_target_of_length_le (γ : MoorePath X) {t : ℝ≥0} (h : γ.length ≤ t) :
    γ t = γ.target :=
  γ.apply_of_length_le h

/-! ### Topology -/

/-- The duration and the underlying map, as a point of `ℝ≥0 × C(ℝ≥0, X)`; the topology of
`MoorePath X` is induced through it. -/
def toProd (γ : MoorePath X) : ℝ≥0 × C(ℝ≥0, X) := (γ.length, γ.toContinuousMap)

@[simp]
theorem toProd_fst (γ : MoorePath X) : γ.toProd.1 = γ.length :=
  (rfl)

@[simp]
theorem toProd_snd (γ : MoorePath X) : γ.toProd.2 = γ.toContinuousMap :=
  (rfl)

theorem toProd_injective : Function.Injective (toProd : MoorePath X → ℝ≥0 × C(ℝ≥0, X)) :=
  fun _ _ h ↦ ext (congrArg Prod.fst h) fun t ↦
    congrArg (fun f : C(ℝ≥0, X) ↦ f t) (congrArg Prod.snd h)

instance : TopologicalSpace (MoorePath X) :=
  TopologicalSpace.induced toProd inferInstance

theorem isInducing_toProd : IsInducing (toProd : MoorePath X → ℝ≥0 × C(ℝ≥0, X)) :=
  ⟨rfl⟩

/-- Moore paths form a subspace of `ℝ≥0 × C(ℝ≥0, X)`. -/
theorem isEmbedding_toProd : IsEmbedding (toProd : MoorePath X → ℝ≥0 × C(ℝ≥0, X)) :=
  ⟨isInducing_toProd, toProd_injective⟩

theorem continuous_toProd : Continuous (toProd : MoorePath X → ℝ≥0 × C(ℝ≥0, X)) :=
  continuous_induced_dom

theorem continuous_length : Continuous (length : MoorePath X → ℝ≥0) :=
  continuous_fst.comp continuous_toProd

theorem continuous_toContinuousMap :
    Continuous (toContinuousMap : MoorePath X → C(ℝ≥0, X)) :=
  continuous_snd.comp continuous_toProd

/-- Evaluation `(γ, t) ↦ γ t` is continuous: `ℝ≥0` is locally compact. -/
theorem continuous_eval : Continuous fun p : MoorePath X × ℝ≥0 ↦ p.1 p.2 :=
  (continuous_toContinuousMap.comp continuous_fst).eval continuous_snd

theorem continuous_eval_const (t : ℝ≥0) : Continuous fun γ : MoorePath X ↦ γ t :=
  continuous_eval.comp (continuous_id.prodMk _root_.continuous_const)

theorem continuous_source : Continuous (source : MoorePath X → X) :=
  continuous_eval_const 0

theorem continuous_target : Continuous (target : MoorePath X → X) :=
  continuous_eval.comp (continuous_id.prodMk continuous_length)

/-- A map into the Moore paths is continuous exactly when the duration and the uncurried
evaluation are continuous: the exponential law for the locally compact source `ℝ≥0`. -/
theorem continuous_iff {Y : Type*} [TopologicalSpace Y] {f : Y → MoorePath X} :
    Continuous f ↔
      Continuous (fun y ↦ (f y).length) ∧ Continuous fun p : Y × ℝ≥0 ↦ f p.1 p.2 := by
  refine ⟨fun hf ↦ ⟨continuous_length.comp hf, continuous_eval.comp (hf.prodMap continuous_id)⟩,
    fun ⟨hl, he⟩ ↦ ?_⟩
  rw [isInducing_toProd.continuous_iff]
  exact hl.prodMk (ContinuousMap.continuous_of_continuous_uncurry _ he)

/-! ### Constant paths -/

/-- The constant Moore path at `x`, of duration `0`. -/
def const (x : X) : MoorePath X where
  toFun _ := x
  length := 0
  stopped' _ _ := rfl

@[simp]
theorem const_apply (x : X) (t : ℝ≥0) : const x t = x :=
  (rfl)

@[simp]
theorem length_const (x : X) : (const x).length = 0 :=
  (rfl)

@[simp]
theorem source_const (x : X) : (const x).source = x :=
  (rfl)

@[simp]
theorem target_const (x : X) : (const x).target = x :=
  (rfl)

theorem continuous_const : Continuous (const : X → MoorePath X) :=
  continuous_iff.2 ⟨_root_.continuous_const, continuous_fst⟩

/-- A Moore path of duration `0` is constant. -/
theorem eq_const_of_length_eq_zero {γ : MoorePath X} (h : γ.length = 0) : γ = const γ.source :=
  ext (by rw [length_const, h]) fun t ↦ by
    rw [const_apply, source_eq_apply, γ.apply_of_length_le (h.trans_le zero_le), h]

/-! ### Paths between subsets -/

/-- The Moore paths starting in `A` and ending in `B`. -/
def pathsBetween (A B : Set X) : Set (MoorePath X) :=
  {γ | γ.source ∈ A ∧ γ.target ∈ B}

@[simp]
theorem mem_pathsBetween_iff {A B : Set X} {γ : MoorePath X} :
    γ ∈ pathsBetween A B ↔ γ.source ∈ A ∧ γ.target ∈ B :=
  Iff.rfl

theorem isClosed_pathsBetween {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) :
    IsClosed (pathsBetween A B) :=
  (hA.preimage continuous_source).inter (hB.preimage continuous_target)

end MoorePath

end TauCeti
