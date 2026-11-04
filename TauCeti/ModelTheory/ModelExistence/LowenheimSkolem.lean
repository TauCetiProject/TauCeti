/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.ModelExistence.AElementary
public import Mathlib.ModelTheory.Substructures
public import TauCeti.ModelTheory.Substructures.Cardinality
public import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Fintype.Order

/-!
# The witness hull and downward Löwenheim–Skolem for fragments

Let `A` be a fragment of `L_{ω₁ω}`, `M` an `L`-structure and `X ⊆ M`. Then `X` lies in an
`A`-elementary substructure of `M`, its **witness hull**, with at most
`max ℵ₀ |X| |A| |Σ n, L.Functions n|` elements. Neither `M` nor `X` need be nonempty. The function
symbols enter the bound separately, because a fragment need not contain an atomic formula
mentioning them. The three cardinals start in the universes of `M`, of the formulas and of the
function symbols, and are compared after lifting into their common universe.

## Main definitions

* `FirstOrder.Language.Fragment.witnessHull`: the witness hull of a set.
* `FirstOrder.Language.Fragment.witness`, `FirstOrder.Language.Fragment.witnessSet` and
  `FirstOrder.Language.Fragment.hullStage`: the chosen counterexamples and the stages of the hull.

## Main results

* `FirstOrder.Language.Fragment.aElementary_witnessHull`: the witness hull is `A`-elementary.
* `FirstOrder.Language.Fragment.lift_mk_witnessHull_le`: its cardinal bound.
* `FirstOrder.Language.exists_aElementary_substructure`: downward Löwenheim–Skolem for fragments.
* `FirstOrder.Language.exists_countable_aElementary_substructure`: the countable form.
* `FirstOrder.Language.exists_aElementary_substructure_of_eq_univ`: the form in one universe.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, Chapter 1,
  Theorem 1.22 and Exercise 1.23.
* Ported from `cameronfreer/infinitary-logic` at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  `InfinitaryLogic/ModelTheory/FragmentLowenheimSkolem.lean`.
* Divergences from that source: the chosen counterexamples come from one partial choice function
  on the members of `A` and tuples, and their number is bounded by an injection into
  `A × List Y`, rather than by per-arity slices; the hull is the directed supremum of the stage
  closures; the bounds are stated for an abstract infinite cardinal bounding the inputs, each lifted
  from its own universe.
-/

public section

open Cardinal

universe u v w

namespace FirstOrder

namespace Language

namespace Fragment

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] (A : Fragment L)

open Classical in
/-- The chosen counterexample to a universal formula `∀ x, φ` at a tuple `a`, if `φ` has one; for
every other formula, nothing. -/
noncomputable def witness : (p : Σ n, L.BoundedFormulaω Empty n) → (Fin p.1 → M) → Option M
  | ⟨_, .all φ⟩, a =>
    if h : ∃ m, ¬ φ.Realize Empty.elim (Fin.snoc a m) then some h.choose else none
  | _, _ => none

open Classical in
/-- At a universal formula `∀ x, φ`, the witness is the chosen counterexample to `φ`, if any. -/
theorem witness_all {n : ℕ} (φ : L.BoundedFormulaω Empty (n + 1)) (a : Fin n → M) :
    witness ⟨n, φ.all⟩ a =
      if h : ∃ m, ¬ φ.Realize Empty.elim (Fin.snoc a m) then some h.choose else none :=
  (rfl)

/-- A chosen counterexample is a counterexample. -/
theorem witness_all_spec {n : ℕ} {φ : L.BoundedFormulaω Empty (n + 1)} {a : Fin n → M} {m : M}
    (h : witness ⟨n, φ.all⟩ a = some m) : ¬ φ.Realize Empty.elim (Fin.snoc a m) := by
  rw [witness_all] at h
  split_ifs at h with hex
  exact Option.some_injective _ h ▸ hex.choose_spec

/-- A universal formula with a counterexample has a chosen one. -/
theorem exists_witness_all {n : ℕ} {φ : L.BoundedFormulaω Empty (n + 1)} {a : Fin n → M}
    (hex : ∃ m, ¬ φ.Realize Empty.elim (Fin.snoc a m)) : ∃ m, witness ⟨n, φ.all⟩ a = some m := by
  rw [witness_all]
  exact ⟨_, dite_eq_left hex⟩

/-- A chosen witness is produced only for a universal formula `∀ x, φ`, and is then a
counterexample to `φ`. -/
theorem exists_eq_all_of_witness_eq_some {n : ℕ} {ψ : L.BoundedFormulaω Empty n} {a : Fin n → M}
    {m : M} (h : witness ⟨n, ψ⟩ a = some m) :
    ∃ φ : L.BoundedFormulaω Empty (n + 1), ψ = φ.all ∧ ¬ φ.Realize Empty.elim (Fin.snoc a m) := by
  cases ψ with
  | all φ => exact ⟨φ, rfl, witness_all_spec h⟩
  | _ => exact absurd h (by simp [witness])

/-- The chosen counterexamples for the members of `A` at the tuples from `Y`. -/
def witnessSet (Y : Set M) : Set M :=
  {m | ∃ p ∈ A, ∃ a : Fin p.1 → M, (∀ i, a i ∈ Y) ∧ witness p a = some m}

/-- Membership in `witnessSet`: a chosen counterexample for a member of `A` at a tuple from `Y`. -/
@[simp]
theorem mem_witnessSet {Y : Set M} {m : M} :
    m ∈ A.witnessSet Y ↔ ∃ p ∈ A, ∃ a : Fin p.1 → M, (∀ i, a i ∈ Y) ∧ witness p a = some m :=
  Iff.rfl

/-- The stages of the witness hull of `X`: alternately close under the function symbols and add,
for each universal member `∀ x, φ` of `A` and each tuple from the closure at which `φ` has a
counterexample in `M`, a chosen counterexample. -/
def hullStage (X : Set M) : ℕ → Set M
  | 0 => X
  | k + 1 => (Substructure.closure L (hullStage X k) : Set M) ∪
      A.witnessSet (Substructure.closure L (hullStage X k))

/-- The first stage of the witness hull of `X` is `X`. -/
@[simp]
theorem hullStage_zero (X : Set M) : A.hullStage X 0 = X := (rfl)

/-- The next stage adds to the closure of a stage its chosen counterexamples. -/
@[simp]
theorem hullStage_succ (X : Set M) (k : ℕ) :
    A.hullStage X (k + 1) = (Substructure.closure L (A.hullStage X k) : Set M) ∪
      A.witnessSet (Substructure.closure L (A.hullStage X k)) := (rfl)

/-- The closures of the stages increase. -/
theorem monotone_closure_hullStage (X : Set M) :
    Monotone fun k => Substructure.closure L (A.hullStage X k) :=
  monotone_nat_of_le_succ fun k => Substructure.closure_mono <| by
    rw [hullStage_succ]
    exact Substructure.subset_closure.trans Set.subset_union_left

/-- The **witness hull** of `X`: the union of the closures of its stages. -/
def witnessHull (X : Set M) : L.Substructure M :=
  ⨆ k, Substructure.closure L (A.hullStage X k)

/-- Membership in the witness hull is membership in the closure of some stage. -/
theorem mem_witnessHull {X : Set M} {m : M} :
    m ∈ A.witnessHull X ↔ ∃ k, m ∈ Substructure.closure L (A.hullStage X k) :=
  Substructure.mem_iSup_of_directed (A.monotone_closure_hullStage X).directed_le

/-- The witness hull contains its seed. -/
theorem subset_witnessHull (X : Set M) : X ⊆ A.witnessHull X := fun _ hm =>
  mem_witnessHull A |>.2 ⟨0, Substructure.subset_closure hm⟩

/-- **The witness hull is `A`-elementary**, by the fragment Tarski–Vaught criterion. -/
theorem aElementary_witnessHull (X : Set M) : AElementary A (A.witnessHull X).subtype := by
  -- The Tarski–Vaught criterion holds by construction. The counterexamples are chosen from
  -- existence proofs, so no element of `M` is needed in advance.
  refine aElementary_of_tarskiVaught _ fun φ hφ a hex => ?_
  -- the tuple lies in the closure of one stage
  choose ks hks using fun i => (A.mem_witnessHull).1 (a i).2
  obtain ⟨K, hK⟩ := (A.monotone_closure_hullStage X).directed_le.finite_le ks
  obtain ⟨m, hm⟩ := exists_witness_all hex
  -- its chosen counterexample is added at the next stage
  have hmK : m ∈ A.hullStage X (K + 1) := by
    rw [hullStage_succ]
    exact Or.inr ⟨_, hφ, _, fun i => hK i (hks i), hm⟩
  exact ⟨⟨m, A.mem_witnessHull.2 ⟨K + 1, Substructure.subset_closure hmK⟩⟩,
    witness_all_spec hm⟩

/-- The witness hull is the union of the closures of its stages. -/
theorem coe_witnessHull (X : Set M) :
    (A.witnessHull X : Set M) = ⋃ k, (Substructure.closure L (A.hullStage X k) : Set M) :=
  Set.ext fun _ => A.mem_witnessHull.trans Set.mem_iUnion.symm

/-! ### The cardinal bound

Each step is bounded by an infinite cardinal `κ` in the common universe `max u v w` that bounds
the seed, the fragment and the function symbols; the three start in different universes, so each
is lifted into `max u v w` from its own. -/

section Bound

variable {A} {κ : Cardinal.{max u v w}}

/-- The chosen counterexamples at the tuples from a set of at most `κ` elements number at most
`κ`, when `κ` also bounds the fragment. -/
theorem lift_mk_witnessSet_le (hκ : ℵ₀ ≤ κ) (hA : lift.{w} #A ≤ κ) {Y : Set M}
    (hY : lift.{max u v} #Y ≤ κ) : lift.{max u v} #(A.witnessSet Y) ≤ κ := by
  classical
  -- each counterexample is recovered from a member of `A` and a list of elements of `Y`
  let g : A × List Y → Option M := fun q =>
    if h : q.2.length = q.1.1.1 then witness q.1.1 fun i => (q.2.get (Fin.cast h.symm i) : M)
    else none
  have key (m : A.witnessSet Y) : ∃ q, g q = some m := by
    obtain ⟨p, hp, a, ha, hm⟩ := m.2
    refine ⟨(⟨p, hp⟩, List.ofFn fun i => ⟨a i, ha i⟩), ?_⟩
    simpa [g] using hm
  choose f hf using key
  have hinj : Function.Injective f := fun m m' h =>
    Subtype.ext (Option.some_injective _ ((hf m).symm.trans (h ▸ hf m')))
  have h1 := lift_mk_le_lift_mk_of_injective hinj
  rw [mk_prod, lift_mul, lift_lift, lift_lift, lift_umax.{w, max u v}] at h1
  have hL : lift.{max u v} #(List Y) ≤ κ := by
    have := lift_le.{max u v}.2 (mk_list_le_max Y)
    rw [lift_max, lift_aleph0] at this
    exact this.trans (max_le hκ hY)
  exact h1.trans ((mul_le_mul' hA hL).trans (mul_eq_self hκ).le)

/-- Each stage of the witness hull of `X` has at most `κ` elements. -/
theorem lift_mk_hullStage_le (hκ : ℵ₀ ≤ κ) (hA : lift.{w} #A ≤ κ)
    (hF : lift.{max v w} #(Σ n, L.Functions n) ≤ κ) {X : Set M} (hX : lift.{max u v} #X ≤ κ)
    (k : ℕ) : lift.{max u v} #(A.hullStage X k) ≤ κ := by
  induction k with
  | zero => exact hX
  | succ k ih =>
    have hC := Substructure.lift_mk_closure_le hκ hF ih
    rw [hullStage_succ]
    refine (lift_le.2 (mk_union_le _ _)).trans ?_
    rw [lift_add]
    exact (add_le_add hC (lift_mk_witnessSet_le hκ hA hC)).trans (add_eq_self hκ).le

/-- The witness hull of `X` has at most `κ` elements. -/
theorem lift_mk_witnessHull_le (hκ : ℵ₀ ≤ κ) (hA : lift.{w} #A ≤ κ)
    (hF : lift.{max v w} #(Σ n, L.Functions n) ≤ κ) {X : Set M} (hX : lift.{max u v} #X ≤ κ) :
    lift.{max u v} #(A.witnessHull X) ≤ κ := by
  have h := lift_le.{max u v}.2 (mk_iUnion_le_lift
    fun k => (Substructure.closure L (A.hullStage X k) : Set M))
  rw [← coe_witnessHull] at h
  simp only [lift_uzero, lift_mul, mk_nat, lift_aleph0, lift_iSup bddAbove_of_small] at h
  refine h.trans ((mul_le_mul' le_rfl (ciSup_le' fun k => ?_)).trans (aleph0_mul_eq hκ).le)
  exact Substructure.lift_mk_closure_le hκ hF (lift_mk_hullStage_le hκ hA hF hX k)

end Bound

end Fragment

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- **Downward Löwenheim–Skolem for fragments.** Every subset `X` of `M` lies in an `A`-elementary
substructure with at most `max ℵ₀ |X| |A| |Σ n, L.Functions n|` elements. -/
theorem exists_aElementary_substructure (A : Fragment L) (X : Set M) :
    ∃ N : L.Substructure M, X ⊆ N ∧ AElementary A N.subtype ∧
      lift.{max u v} #N ≤ max ℵ₀ (max (lift.{max u v} #X)
        (max (lift.{w} #A) (lift.{max v w} #(Σ n, L.Functions n)))) := by
  refine ⟨A.witnessHull X, A.subset_witnessHull X, A.aElementary_witnessHull X,
    Fragment.lift_mk_witnessHull_le (le_max_left _ _) ?_ ?_ ?_⟩
  · exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · exact (le_max_left _ _).trans (le_max_right _ _)

/-- **Countable `A`-elementary substructures.** With countably many function symbols, a countable
fragment and a countable `X ⊆ M`, there is a countable `A`-elementary substructure containing
`X`. -/
theorem exists_countable_aElementary_substructure [Countable (Σ n, L.Functions n)]
    (A : Fragment L) (hA : (A : Set (Σ n, L.BoundedFormulaω Empty n)).Countable) {X : Set M}
    (hX : X.Countable) :
    ∃ N : L.Substructure M, X ⊆ N ∧ AElementary A N.subtype ∧ Countable N := by
  obtain ⟨N, hXN, hN, hcard⟩ := exists_aElementary_substructure A X
  refine ⟨N, hXN, hN, mk_le_aleph0_iff.1 (lift_le_aleph0.1 (hcard.trans (max_le le_rfl ?_)))⟩
  refine max_le (lift_le_aleph0.2 hX.le_aleph0) (max_le (lift_le_aleph0.2 ?_) ?_)
  · exact mk_le_aleph0_iff.2 hA.to_subtype
  · exact lift_le_aleph0.2 mk_le_aleph0

/-- **Downward Löwenheim–Skolem for fragments, in one universe.** For a language and a structure
in one universe the bound needs no lifts. -/
theorem exists_aElementary_substructure_of_eq_univ {L : Language.{u, u}} {M : Type u}
    [L.Structure M] (A : Fragment L) (X : Set M) :
    ∃ N : L.Substructure M, X ⊆ N ∧ AElementary A N.subtype ∧
      #N ≤ max ℵ₀ (max #X (max #A #(Σ n, L.Functions n))) := by
  simpa using exists_aElementary_substructure A X

end Language

end FirstOrder
