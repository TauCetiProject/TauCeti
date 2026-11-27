/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Algebra.Ring.Real

public import Mathlib.Topology.Separation.Hausdorff
public import TauCeti.Data.Finset.Pi
import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sigma

/-!
# Shrinking open sets into dense open sets of finite products

The open unit cube in a finite product of copies of `ℝ` is open.

Given nonempty open sets `V i` in a topological space `X` and a dense open set `U ⊆ κ → X` for a
finite type `κ`, the sets `V i` can be shrunk to nonempty open subsets so that the box
`∏ j, W (t j)` along one given injective tuple `t : κ → I` lies in `U`. When the index type `I`
is also finite, iterating this shrinks the `V i` so that, for finitely many dense open sets
`U c ⊆ κ c → X` with each `κ c` finite, every box along every injective tuple `t : κ c → I` lies
in `U c`. Such shrinking steps are the
basic move in Baire category constructions of perfect sets of independent points, such as the
proof of Mycielski's theorem.

In a Hausdorff space the injective tuples indexed by a finite type form an open subset of the
product, such as the ordered triples of distinct points of the Riemann sphere.

Repeating the first entry of a finite tuple, `(q₀, …, qₙ) ↦ (q₀, q₀, q₁, …, qₙ)`, is an embedding.

Density in a product only has to be checked on finitely many coordinates at a time, which is how
approximation theorems at finitely many places give density in a product of completions.

## Main results

* `TauCeti.isOpen_setOf_forall_abs_lt_one`: the finite-dimensional open unit cube is open.
* `TauCeti.exists_univ_pi_subset`: shrinking along one injective tuple.
* `TauCeti.exists_forall_univ_pi_subset`: when the index type is finite, shrinking along all
  injective tuples for finitely many dense open sets at once.
* `TauCeti.isOpen_setOf_injective`: in a Hausdorff space, the injective finite tuples form an open
  set.
* `TauCeti.continuous_extend_subtypeVal`: extending functions on a subset along `Subtype.val`,
  with a fixed fallback, is continuous.
* `TauCeti.isEmbedding_cons_apply_zero`: repeating the first entry of a tuple is an embedding.
* `TauCeti.denseRange_pi_subtype_of_forall_finset`: a map into a product over a set `T` has dense
  range if it hits finitely many nonempty open sets at finitely many coordinates in `T`.
* `Finset.continuous_extendByZero₂`: extension by zero of dependent functions on a finite set
  `s` to a finite set `t` is continuous.
-/

public section

open Set Function Topology

namespace TauCeti

/-- The open unit cube in a finite product of copies of `ℝ` is open. -/
theorem isOpen_setOf_forall_abs_lt_one {ι : Type*} [Finite ι] :
    IsOpen {z : ι → ℝ | ∀ i, |z i| < 1} := by
  -- Express the coordinatewise bound as a finite product of open intervals.
  rw [show {z : ι → ℝ | ∀ i, |z i| < 1} =
      Set.univ.pi fun _ ↦ Set.Ioo (-1) 1 by ext z; simp [abs_lt]]
  exact isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo

variable {X : Type*} [TopologicalSpace X]

/-- Extending functions on a subset `s` along `Subtype.val`, with a fixed fallback `e` outside `s`,
is continuous for the product topologies. -/
theorem continuous_extend_subtypeVal {ι : Type*} {s : Set ι} (e : ι → X) :
    Continuous fun g : s → X ↦ extend Subtype.val g e := by
  refine continuous_pi fun j ↦ ?_
  by_cases hj : j ∈ s
  · exact (continuous_apply _).congr fun g ↦ (extend_val_apply (g := g) (j := e) hj).symm
  · exact continuous_const.congr fun g ↦ (extend_val_apply' (g := g) (j := e) hj).symm

/-- In a Hausdorff space, the injective tuples indexed by a finite type form an open subset of the
product: injectivity asks finitely many pairs of coordinates to differ. -/
theorem isOpen_setOf_injective [T2Space X] {κ : Type*} [Finite κ] :
    IsOpen {t : κ → X | Injective t} := by
  have : {t : κ → X | Injective t} = ⋂ (i : κ) (j : κ) (_ : i ≠ j), {t | t i ≠ t j} := by
    ext t
    simp only [mem_ofPred_eq, mem_iInter]
    exact ⟨fun ht i j hij hji ↦ hij (ht hji), fun ht i j hij ↦ by_contra fun h ↦ ht i j h hij⟩
  rw [this]
  exact isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦
    isOpen_iInter_of_finite fun _ ↦ isOpen_ne_fun (continuous_apply i) (continuous_apply j)

/-- Repeating the first entry, `(q₀, …, qₙ) ↦ (q₀, q₀, q₁, …, qₙ)`, is an embedding of tuples:
forgetting the first entry is a continuous left inverse. -/
theorem isEmbedding_cons_apply_zero {n : ℕ} :
    IsEmbedding fun q : Fin (n + 1) → X ↦ (Fin.cons (q 0) q : Fin (n + 2) → X) :=
  IsEmbedding.of_comp ((continuous_apply 0).finCons (A := fun _ ↦ X) continuous_id)
    continuous_id.finTail <| by
      -- forgetting the repeated first entry gives back the tuple
      simp only [Function.comp_def, id_eq, Fin.tail_cons]
      exact IsEmbedding.id

/-- Shrinking along one injective tuple: nonempty open sets `V i` can be shrunk to nonempty open
sets `W i ⊆ V i` so that the box `∏ j, W (t j)` along an injective finite tuple `t` of indices
lies in a given dense open set. This is the inductive step of `exists_forall_univ_pi_subset`. -/
theorem exists_univ_pi_subset {I κ : Type*} [Finite κ] {V : I → Set X}
    (hVo : ∀ i, IsOpen (V i)) (hVne : ∀ i, (V i).Nonempty) {t : κ → I} (ht : Injective t)
    {U : Set (κ → X)} (hUo : IsOpen U) (hUd : Dense U) :
    ∃ W : I → Set X, (∀ i, IsOpen (W i)) ∧ (∀ i, (W i).Nonempty) ∧ (∀ i, W i ⊆ V i) ∧
      univ.pi (fun j => W (t j)) ⊆ U := by
  classical
  -- a point of `U` in the box `∏ j, V (t j)`, and an open box around it inside `U`
  obtain ⟨y, hyV, hyU⟩ := hUd.inter_open_nonempty (univ.pi fun j => V (t j))
    (isOpen_set_pi finite_univ fun j _ => hVo (t j)) (univ_pi_nonempty_iff.2 fun j => hVne (t j))
  obtain ⟨u, hu, huU⟩ := isOpen_pi_iff'.1 hUo y hyU
  -- cut `V (t j)` down by `u j`, leaving the other sets alone
  let u' : I → Set X := extend t u fun _ => univ
  have hu'o (i : I) : IsOpen (u' i) := by
    by_cases hi : ∃ j, t j = i
    · obtain ⟨j, rfl⟩ := hi
      simpa [u', ht.extend_apply] using (hu j).1
    · simp [u', extend_apply' _ _ _ hi]
  refine ⟨fun i => V i ∩ u' i, fun i => (hVo i).inter (hu'o i), fun i => ?_,
    fun i => inter_subset_left, fun x hx => huU fun j _ => ?_⟩
  · by_cases hi : ∃ j, t j = i
    · obtain ⟨j, rfl⟩ := hi
      exact ⟨y j, hyV j (mem_univ j), by simpa [u', ht.extend_apply] using (hu j).2⟩
    · simpa [u', extend_apply' _ _ _ hi] using hVne i
  · simpa [u', ht.extend_apply] using (hx j (mem_univ j)).2

/-- **Shrinking along all injective tuples.** Nonempty open sets `V i`, indexed by a finite type,
can be shrunk to nonempty open sets `W i ⊆ V i` so that for each of finitely many dense open sets
`U c ⊆ κ c → X`, every box `∏ j, W (t j)` along an injective tuple `t : κ c → I` lies in `U c`. -/
theorem exists_forall_univ_pi_subset {I C : Type*} [Finite I] [Finite C] {κ : C → Type*}
    {V : I → Set X} (hVo : ∀ i, IsOpen (V i)) (hVne : ∀ i, (V i).Nonempty)
    {U : ∀ c, Set (κ c → X)} (hUo : ∀ c, IsOpen (U c)) (hUd : ∀ c, Dense (U c)) :
    ∃ W : I → Set X, (∀ i, IsOpen (W i)) ∧ (∀ i, (W i).Nonempty) ∧ (∀ i, W i ⊆ V i) ∧
      ∀ c (t : κ c → I), Injective t → univ.pi (fun j => W (t j)) ⊆ U c := by
  classical
  -- treat the finitely many pairs of a set `U c` and an injective tuple one at a time
  let Q := Σ c, {t : κ c → I // Injective t}
  have : ∀ c, Finite {t : κ c → I // Injective t} := fun c ↦
    Finite.of_equiv (κ c ↪ I) (Equiv.subtypeInjectiveEquivEmbedding (κ c) I).symm
  have : Fintype Q := Fintype.ofFinite Q
  suffices h : ∀ s : Finset Q, ∃ W : I → Set X, (∀ i, IsOpen (W i)) ∧ (∀ i, (W i).Nonempty) ∧
      (∀ i, W i ⊆ V i) ∧ ∀ q ∈ s, univ.pi (fun j => W (q.2.val j)) ⊆ U q.1 by
    obtain ⟨W, hWo, hWne, hWV, hW⟩ := h Finset.univ
    exact ⟨W, hWo, hWne, hWV, fun c t ht => hW ⟨c, t, ht⟩ (Finset.mem_univ _)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨V, hVo, hVne, fun _ => subset_rfl, by simp⟩
  | insert q s _ ih =>
    obtain ⟨W, hWo, hWne, hWV, hW⟩ := ih
    have := Finite.of_injective q.2.val q.2.property
    obtain ⟨W', hW'o, hW'ne, hW'W, hW'⟩ :=
      exists_univ_pi_subset hWo hWne q.2.property (hUo q.1) (hUd q.1)
    refine ⟨W', hW'o, hW'ne, fun i => (hW'W i).trans (hWV i), fun q' hq' => ?_⟩
    rcases Finset.mem_insert.1 hq' with rfl | hq'
    · exact hW'
    · exact (pi_mono fun j _ => hW'W _).trans (hW q' hq')

/-- An infinite product of nontrivial spaces is not discrete: every basic open set constrains only
finitely many coordinates, so it contains a point differing from any given one in a free
coordinate. -/
theorem not_discreteTopology_pi {ι : Type*} {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)]
    [Infinite ι] [∀ i, Nontrivial (Y i)] : ¬DiscreteTopology (∀ i, Y i) := fun _ ↦ by
  classical
  choose x y hxy using fun i ↦ exists_pair_ne (Y i)
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 (isOpen_discrete ({x} : Set (∀ i, Y i))) x rfl
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset I
  have hmem : Function.update x j (y j) ∈ (I : Set ι).pi u := fun i hi ↦ by
    rw [Function.update_of_ne (by rintro rfl; exact hj hi)]
    exact (hu i hi).2
  have := congrFun (hsub hmem) j
  simp only [Function.update_self] at this
  exact hxy j this.symm

/-- A map into the product of spaces `Y i` over the points of a set `T` has dense range if, for
every finite subset `J` of `T` and all nonempty open sets `u i ⊆ Y i` for `i ∈ J`, some value of
the map lies in `u i` at every coordinate `i ∈ J`. The sets `u i` for `i ∉ J` are unconstrained. -/
theorem denseRange_pi_subtype_of_forall_finset {ι α : Type*} {Y : ι → Type*}
    [∀ i, TopologicalSpace (Y i)] {T : Set ι} {f : α → ∀ i : T, Y i}
    (h : ∀ (J : Finset ι), (J : Set ι) ⊆ T → ∀ u : ∀ i, Set (Y i),
      (∀ i ∈ J, IsOpen (u i) ∧ (u i).Nonempty) → ∃ x, ∀ i : T, i.val ∈ J → f x i ∈ u i) :
    DenseRange f := by
  classical
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨g, hg⟩
  -- `U` contains a basic open set, a product of opens `u i` over a finite set `I ⊆ T`.
  obtain ⟨I, u, hu, hIU⟩ := isOpen_pi_iff.1 hU g hg
  have hI (i : ι) : i ∈ I.map (Embedding.subtype (· ∈ T)) ↔ ∃ h : i ∈ T, ⟨i, h⟩ ∈ I := by simp
  obtain ⟨x, hx⟩ := h (I.map (Embedding.subtype (· ∈ T))) (fun i hi ↦ ((hI i).1 hi).1)
    (fun i ↦ if h : i ∈ T then u ⟨i, h⟩ else univ) fun i hi ↦ by
      obtain ⟨hiT, hiI⟩ := (hI i).1 hi
      simp only [hiT, ↓reduceDIte]
      exact ⟨(hu _ hiI).1, _, (hu _ hiI).2⟩
  refine ⟨f x, hIU fun i hi ↦ ?_, x, rfl⟩
  simpa only [i.property, ↓reduceDIte] using hx i ((hI i).2 ⟨i.property, hi⟩)

end TauCeti

/-- Extension by zero of dependent functions on a finite set `s` to a finite set `t` is continuous
for the product topologies. -/
@[continuity, fun_prop]
theorem Finset.continuous_extendByZero₂ {ι : Type*} [DecidableEq ι] {π : ι → Type*}
    [∀ i, Zero (π i)] [∀ i, TopologicalSpace (π i)] {s : Finset ι} (t : Finset ι) :
    Continuous (Finset.extendByZero₂ (π := π) (s := s) t) :=
  continuous_pi fun i ↦ by
    by_cases h : i.val ∈ s
    · simpa only [Finset.extendByZero₂_of_mem _ _ h] using continuous_apply (⟨i, h⟩ : s)
    · simpa only [Finset.extendByZero₂_of_notMem _ _ h] using continuous_const
