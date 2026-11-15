/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Obstruction.Invariance
public import TauCeti.Combinatorics.SimpleGraph.Degree
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.Parity

/-!
# Non-formal loop deformations of zigzag algebras

Let `Z` be the zigzag algebra of a finite simple graph `G` with no isolated vertex, graded by path
length and regarded as an `A∞` algebra whose only operation is the product
(`TauCeti.zigzagStrictAInfinityAlgebra`). A loop deformation `TauCeti.zigzagLoopAInfinityAlgebra` is
a minimal, strictly unital `A∞` structure on `Z` with the same grading and product and one higher
operation `mₙ` built as a linear combination of loop operations of closed walks. This file shows
that such deformations can be **nontrivial modulo `A∞` isomorphism**, and hence that `Z` is in
general not intrinsically formal.

Three obstruction mechanisms combine to eliminate characteristic hypotheses for quartic deformations
and to reach higher even arities:

* **Invariance of the first obstruction** (`TauCeti.AInfinityAlgebra.IsMinimal`): when `2` is
  invertible (in arity four) or over a `ℚ`-algebra (in every arity `n + 2 ≥ 3`), a formal minimal
  loop deformation has a higher operation which is a Hochschild coboundary of `Z`
  (`TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra`,
  `TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_of_algebraRat`).
* **Even-arity parity** (`TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.Parity`): over every
  commutative ring, balanced quartic backtrack pairings and even-arity anticyclic word pairings send
  the first obstruction of any formal minimal deformation into the ideal `2 k`. When `2` is not a
  unit in `k`—in particular in characteristic `2` or over `ℤ`—any deformation on which such a
  pairing takes a unit value is not formal
  (`TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_of_not_isUnit_two_of_isUnit_zigzagWordPairing`,
  `TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_of_anticyclic_of_not_isUnit_two`).
* **Unconditional quartic non-formality**: splitting on whether `(2 : k)` is a unit combines the
  `Invertible (2 : k)` obstruction theorem with the `2 k` parity restriction, so any quartic loop
  deformation on which a balanced backtrack pairing or anticyclic functional takes a unit value is
  non-formal over **every** nontrivial commutative ring `k`
  (`TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_of_isUnit_zigzagBacktrackPairing`,
  `TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_of_anticyclic_four`).

Applying the balanced backtrack pairings of
`TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.HochschildClass`, which evaluate to `1` on the
single walk `n₁ → v → n₀ → v → n₁` at a vertex of valency at least four or at two branch vertices
joined by a walk, yields unconditional quartic non-formality over every nontrivial commutative ring,
with no assumption on `(2 : k)`. For the affine `D₄` graph the walk is Liu--Wang's `β₄ α₁ β₁ α₄`;
see `TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.Affine.D.Four` and
`TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.Affine.D.Basic`.

## Main results

* `TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra` and
  `TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_of_algebraRat`: coboundary criteria for
  non-formality in arity four when `2` is invertible and in every arity `n + 2` over a `ℚ`-algebra.
* `TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_of_not_isUnit_two_of_isUnit_zigzagWordPairing`
  and `TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_of_anticyclic_of_not_isUnit_two`: even-arity
  non-formality when `(2 : k)` is not a unit and a word pairing or anticyclic functional evaluates
  to a unit.
* `TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_of_isUnit_zigzagBacktrackPairing` and
  `TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_of_anticyclic_four`: quartic non-formality over
  every nontrivial commutative ring when a balanced backtrack pairing or anticyclic functional
  evaluates to a unit.
* `TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal`: if a loop
  deformation of any arity is not formal, then the strict zigzag algebra is not intrinsically
  formal.
* `TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_single` and
  `TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_single_of_walk`: the loop deformation of a
  single closed walk `n₁ → v → n₀ → v → n₁` is not formal over every nontrivial commutative ring,
  at a vertex with four distinct neighbours or at two branch vertices joined by a walk.
* `TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra`,
  `TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_walk`,
  `TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_four_le_degree` and
  `TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_three_le_degree`: the strict
  zigzag algebra is not intrinsically formal over every nontrivial commutative ring when `G` has a
  vertex of degree at least four, or two distinct vertices of degree at least three joined by a
  walk.

## References

* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  Section 4, for minimal `A∞` deformations of zigzag algebras and their intrinsic formality.
* T. Kadeishvili, *The structure of the `A(∞)`-algebra, and the Hochschild and Harrison
  cohomologies*, Trudy Tbiliss. Mat. Inst. 91 (1988), 19--27, for the obstruction method.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver AInfinity ReducedTensorWords

universe u w

variable {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V} [Finite V]
  {hns : ∀ i : V, ∃ j, G.Adj i j}

local notation "𝒵" => zigzagStrictAInfinityAlgebra k hns

/-! ### General non-formality criteria -/

/-- **A loop deformation whose quartic operation is not a coboundary is not formal**, when `2` is
invertible. If the quartic operation of the loop deformation with coefficients `c` is not the
Hochschild differential of a suspended cochain of degree zero of the strict zigzag algebra, then
the loop deformation is not formal. Equivalently it is not `A∞` isomorphic to the strict zigzag
algebra (`TauCeti.AInfinityAlgebra.IsMinimal.isFormal_iff_exists_isIso`). -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra [Invertible (2 : k)] (c : (Fin 4 → G.Dart) →₀ k)
    (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd)
    (hobs : ¬∃ φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k]
        nonisolatedZigzagQuotient k G,
      LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1))
          ((𝒵).grading.shift 1).piece 0 ∧
        (𝒵).hochschildDifferential 0 φ =
          (zigzagLoopAInfinityAlgebra hns c hc).obstruction 𝒵 ⟨4, by norm_num⟩) :
    ¬(zigzagLoopAInfinityAlgebra hns c hc).IsFormal :=
  AInfinityAlgebra.IsMinimal.not_isFormal_of_not_exists_hochschildDifferential_eq_obstruction_four
    (isMinimal_zigzagLoopAInfinityAlgebra c hc) isMinimal_zigzagStrictAInfinityAlgebra
    (fun _ hn ↦ zigzagStrictAInfinityAlgebra_m_eq_zero (by omega))
    (zigzagLoopAInfinityAlgebra_grading_eq_zigzagStrictAInfinityAlgebra_grading c hc)
    (zigzagLoopAInfinityAlgebra_m_two_eq_zigzagStrictAInfinityAlgebra_m_two c hc)
    (zigzagLoopAInfinityAlgebra_m_eq_zero c hc (by decide) (by decide)) hobs

/-- **Over a `ℚ`-algebra, a loop deformation whose higher operation is not a coboundary is not
formal.** If the arity-`n + 2` obstruction of the loop deformation with coefficients `c` is not the
Hochschild differential of a suspended cochain of degree zero of `𝒵`, then the loop deformation is
not formal. -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra_of_algebraRat [Algebra ℚ k] {n : ℕ}
    (c : (Fin (n + 2) → G.Dart) →₀ k) (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd)
    (hobs : ¬∃ φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k]
        nonisolatedZigzagQuotient k G,
      LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1))
          ((𝒵).grading.shift 1).piece 0 ∧
        (𝒵).hochschildDifferential 0 φ =
          (zigzagLoopAInfinityAlgebra hns c hc).obstruction 𝒵 ⟨n + 2, by omega⟩) :
    ¬(zigzagLoopAInfinityAlgebra hns c hc).IsFormal :=
  AInfinityAlgebra.IsMinimal.not_isFormal_of_not_exists_hochschildDifferential_eq_obstruction
    (isMinimal_zigzagLoopAInfinityAlgebra c hc) isMinimal_zigzagStrictAInfinityAlgebra
    (fun _ hr ↦ zigzagStrictAInfinityAlgebra_m_eq_zero (by omega))
    (zigzagLoopAInfinityAlgebra_grading_eq_zigzagStrictAInfinityAlgebra_grading c hc)
    (zigzagLoopAInfinityAlgebra_m_two_eq_zigzagStrictAInfinityAlgebra_m_two c hc)
    (fun r hr1 hr2 ↦ zigzagLoopAInfinityAlgebra_m_eq_zero c hc (by omega) (by omega)) hobs

/-- **Even-arity non-formality when `2` is not a unit.** If `(2 : k)` is not a unit (for instance in
characteristic `2` or over `ℤ`) and an anticyclic word pairing satisfying the signless relations
evaluates to a unit on the coefficients `c` of a loop deformation of even arity `2 m + 2` (`m ≥ 1`),
then the loop deformation is not formal. -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra_of_not_isUnit_two_of_isUnit_zigzagWordPairing
    [Fintype G.Dart] [DecidableEq V] (h2 : ¬IsUnit (2 : k)) {m : ℕ} (hm : 1 ≤ m)
    {a : (Fin (2 * m + 2) → G.Dart) → k}
    (hrot : ∀ (u : Fin (2 * m + 1) → G.Dart) (e : G.Dart), a (Fin.snoc u e) = -a (Fin.cons e u))
    (hrel : ∀ (p : Fin (2 * m + 1)) (u : Fin (2 * m) → G.Dart) (v : V),
      ∑ d : G.Dart with d.snd = v, a (Fin.insertNth p.castSucc d (Fin.insertNth p d.symm u)) = 0)
    (c : (Fin (2 * m + 2) → G.Dart) →₀ k)
    (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd)
    (hu : IsUnit (∑ w, a w * c w)) :
    ¬(zigzagLoopAInfinityAlgebra hns c hc).IsFormal := fun hF ↦ by
  obtain ⟨y, hy⟩ := exists_zigzagWordPairing_obstruction_eq_two_mul_of_isFormal
    (isMinimal_zigzagLoopAInfinityAlgebra c hc)
    (zigzagLoopAInfinityAlgebra_grading_eq_zigzagStrictAInfinityAlgebra_grading c hc)
    (zigzagLoopAInfinityAlgebra_m_two_eq_zigzagStrictAInfinityAlgebra_m_two c hc)
    (fun r hr1 hr2 ↦ zigzagLoopAInfinityAlgebra_m_eq_zero c hc (by omega) (by omega)) hF hrot hrel
  rw [zigzagWordPairing_obstruction (by omega : 1 ≤ 2 * m) a c hc] at hy
  exact h2 (isUnit_of_dvd_unit ⟨y, hy⟩ (((Units.isUnit _).map (Int.castRingHom k)).mul hu))

/-- **Even-arity non-formality from an anticyclic functional when `2` is not a unit.** Let `β`
satisfy the signless relations and let `f` be anticyclic on the `β e`. When `(2 : k)` is not a unit
and `∑ w, f (β (w 0) ⋯ β (w (2 m + 1))) * c w` is a unit (`m ≥ 1`), the loop deformation with
coefficients `c` is not formal. -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra_of_anticyclic_of_not_isUnit_two
    [Fintype G.Dart] [DecidableEq V] {B : Type*} [Semiring B] [Module k B]
    (h2 : ¬IsUnit (2 : k)) {m : ℕ} (hm : 1 ≤ m) (β : G.Dart → B)
    (hβ : ∀ v : V, ∑ d : G.Dart with d.snd = v, β d * β d.symm = 0)
    (f : B →ₗ[k] k) (hf : ∀ (e : G.Dart) (y : B), f (y * β e) = -f (β e * y))
    (c : (Fin (2 * m + 2) → G.Dart) →₀ k)
    (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd)
    (hu : IsUnit (∑ w, f (List.ofFn fun t ↦ β (w t)).prod * c w)) :
    ¬(zigzagLoopAInfinityAlgebra hns c hc).IsFormal := fun hF ↦ by
  obtain ⟨y, hy⟩ := exists_zigzagWordPairing_obstruction_eq_two_mul_of_anticyclic_of_isFormal
    (m := m) (isMinimal_zigzagLoopAInfinityAlgebra c hc)
    (zigzagLoopAInfinityAlgebra_grading_eq_zigzagStrictAInfinityAlgebra_grading c hc)
    (zigzagLoopAInfinityAlgebra_m_two_eq_zigzagStrictAInfinityAlgebra_m_two c hc)
    (fun r hr1 hr2 ↦ zigzagLoopAInfinityAlgebra_m_eq_zero c hc (by omega) (by omega)) hF β hβ f hf
  rw [zigzagWordPairing_obstruction (by omega : 1 ≤ 2 * m) _ c hc] at hy
  exact h2 (isUnit_of_dvd_unit ⟨y, hy⟩ (((Units.isUnit _).map (Int.castRingHom k)).mul hu))

/-- **Quartic non-formality from a balanced backtrack pairing, over any nontrivial commutative
ring.** If a symmetric, head-preserving, balanced matrix `a` pairs the quartic obstruction of a loop
deformation to a unit in `k`, then the loop deformation is not formal: when `2` is invertible its
obstruction is not a Hochschild coboundary, and when `2` is not a unit its pairing cannot lie in
`2 k`. -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra_of_isUnit_zigzagBacktrackPairing
    [Nontrivial k] [Fintype G.Dart] {a : Matrix G.Dart G.Dart k} (ha : a.IsSymm)
    (hhead : ∀ d e, d.snd ≠ e.snd → a d e = 0) (hbal : ∀ e, ∑ d, a d e = a e.symm e.symm)
    (c : (Fin 4 → G.Dart) →₀ k) (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd)
    (hu : IsUnit (zigzagBacktrackPairing hns a
      ((zigzagLoopAInfinityAlgebra hns c hc).obstruction 𝒵 ⟨4, by norm_num⟩))) :
    ¬(zigzagLoopAInfinityAlgebra hns c hc).IsFormal := by
  by_cases h2 : IsUnit (2 : k)
  · let _ := h2.invertible
    exact not_isFormal_zigzagLoopAInfinityAlgebra c hc
      (not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra ha hhead hbal
        c hc (zigzagBacktrackPairing_obstruction (hns := hns) a c hc ▸ hu.ne_zero))
  · intro hF
    obtain ⟨y, hy⟩ := exists_zigzagBacktrackPairing_obstruction_eq_two_mul_of_isFormal
      (isMinimal_zigzagLoopAInfinityAlgebra c hc)
      (zigzagLoopAInfinityAlgebra_grading_eq_zigzagStrictAInfinityAlgebra_grading c hc)
      (zigzagLoopAInfinityAlgebra_m_two_eq_zigzagStrictAInfinityAlgebra_m_two c hc)
      (zigzagLoopAInfinityAlgebra_m_eq_zero c hc (by decide) (by decide)) hF ha hhead hbal
    exact h2 (isUnit_of_dvd_unit ⟨y, hy⟩ hu)

/-- **Quartic non-formality from an anticyclic functional, over any nontrivial commutative ring.**
When `β` satisfies the signless relations, `f` is anticyclic on the `β e`, and
`∑ w, f (β (w 0) ⋯ β (w 3)) * c w` is a unit in `k`, the quartic loop deformation with coefficients
`c` is not formal. -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra_of_anticyclic_four
    [Nontrivial k] [Fintype G.Dart] [DecidableEq V] {B : Type*} [Semiring B] [Module k B]
    (β : G.Dart → B) (hβ : ∀ v : V, ∑ d : G.Dart with d.snd = v, β d * β d.symm = 0)
    (f : B →ₗ[k] k) (hf : ∀ (e : G.Dart) (y : B), f (y * β e) = -f (β e * y))
    (c : (Fin 4 → G.Dart) →₀ k) (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd)
    (hu : IsUnit (∑ w, f (List.ofFn fun t ↦ β (w t)).prod * c w)) :
    ¬(zigzagLoopAInfinityAlgebra hns c hc).IsFormal := by
  by_cases h2 : IsUnit (2 : k)
  · let _ := h2.invertible
    exact not_isFormal_zigzagLoopAInfinityAlgebra c hc
      (not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_anticyclic
        (n := 2) one_le_two β hβ f hf c hc hu.ne_zero)
  · exact not_isFormal_zigzagLoopAInfinityAlgebra_of_anticyclic_of_not_isUnit_two
      h2 (m := 1) le_rfl β hβ f hf c hc hu

/-- **A non-formal loop deformation shows that the strict zigzag algebra is not intrinsically
formal.** A loop deformation of any arity is a minimal `A∞` structure on the zigzag algebra with its
grading and product, so if it is not formal, then the strict zigzag algebra is not intrinsically
formal. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal
    {n : ℕ} [NeZero n] {c : (Fin n → G.Dart) →₀ k}
    {hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd}
    (h : ¬(zigzagLoopAInfinityAlgebra hns c hc).IsFormal) : ¬(𝒵).IsIntrinsicallyFormal := fun hf ↦
  h <| hf.isFormal_of_isMinimal
    (zigzagLoopAInfinityAlgebra_grading_eq_zigzagStrictAInfinityAlgebra_grading _ _)
    (isMinimal_zigzagLoopAInfinityAlgebra _ _)
    (zigzagLoopAInfinityAlgebra_m_two_eq_zigzagStrictAInfinityAlgebra_m_two _ _)

/-! ### Four-valent vertices -/

/-- **A non-formal quartic deformation of a zigzag algebra**, over every nontrivial commutative
ring. Let `δ 0, …, δ 3` be four distinct darts with a common head `v`, for instance the darts into
`v` from four distinct neighbours. The loop deformation whose quartic operation is the loop
operation of the single closed walk `(δ 3).symm, δ 0, (δ 0).symm, δ 3` (in product order) is a
minimal, strictly unital `A∞` structure on the zigzag algebra, with its grading and product, which
is not formal: it is not `A∞` isomorphic to the strict zigzag algebra. -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra_single [Nontrivial k]
    {δ : Fin 4 → G.Dart} (hδ : Function.Injective δ) {v : V} (hv : ∀ i, (δ i).snd = v) :
    ¬(zigzagLoopAInfinityAlgebra hns _
      (fst_eq_snd_of_mem_support_single_rotate_zigzagBacktrackWalk
        ((hv 3).trans (hv 0).symm) (1 : k))).IsFormal := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨a, ha, hhead, hbal, h1⟩ := exists_zigzagBacktrackPairing_obstruction_single_eq_one
    (k := k) (hns := hns) hδ hv
  exact not_isFormal_zigzagLoopAInfinityAlgebra_of_isUnit_zigzagBacktrackPairing
    ha hhead hbal _ _ (h1.symm ▸ isUnit_one)

/-- **The zigzag algebra of a graph with a vertex of valency at least four is not intrinsically
formal**, over every nontrivial commutative ring: when four distinct darts of `G` have a common
head, some `A∞` algebra whose cohomology algebra is the path-graded zigzag algebra is not formal. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra [Nontrivial k]
    {δ : Fin 4 → G.Dart} (hδ : Function.Injective δ) {v : V} (hv : ∀ i, (δ i).snd = v) :
    ¬(𝒵).IsIntrinsicallyFormal :=
  not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal
    (not_isFormal_zigzagLoopAInfinityAlgebra_single hδ hv)

/-- **The zigzag algebra of a graph with a vertex of degree at least four is not intrinsically
formal**, over every nontrivial commutative ring. This is
`TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra` for the darts into `v` from four
distinct neighbours. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_four_le_degree [Nontrivial k]
    {v : V} [Fintype (G.neighborSet v)] (hv : 4 ≤ G.degree v) :
    ¬(𝒵).IsIntrinsicallyFormal := by
  obtain ⟨ι⟩ : Nonempty (Fin 4 ↪ G.neighborSet v) := Function.Embedding.nonempty_of_card_le
    (by rwa [Fintype.card_fin, SimpleGraph.card_neighborSet_eq_degree])
  exact not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra
    (δ := fun i ↦ ⟨((ι i : V), v), (ι i).2.symm⟩)
    (fun i j h ↦ ι.injective (Subtype.ext (congrArg (·.fst) h))) (v := v) fun _ ↦ rfl

/-! ### Two branch vertices joined by a walk -/

/-- **A non-formal quartic deformation at two branch vertices**, over every nontrivial commutative
ring. Let `d` and `e` be distinct darts with a common head `v`, and let the non-backtracking walk of
darts `f 0, …, f n` lead from `v`, along neither `d.symm` nor `e.symm`, to a vertex `w` without
returning to `v`. Let `d'` and `e'` be distinct darts with head `w`, both distinct from the last
dart `f n` of the walk. The loop deformation whose quartic operation is the loop operation of the
single closed walk `e.symm, d, d.symm, e` (in product order) is a minimal, strictly unital `A∞`
structure on the zigzag algebra, with its grading and product, which is not formal: it is not `A∞`
isomorphic to the strict zigzag algebra. -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra_single_of_walk [Nontrivial k]
    {d e d' e' : G.Dart} {n : ℕ} {f : Fin (n + 1) → G.Dart} (hde : d ≠ e)
    (hed : e.snd = d.snd) (hf₀ : (f 0).fst = d.snd) (hdf : d ≠ (f 0).symm)
    (hef : e ≠ (f 0).symm) (hf : ∀ t : Fin n, G.DartAdj (f t.castSucc) (f t.succ))
    (hf' : ∀ t : Fin n, f t.castSucc ≠ (f t.succ).symm) (hfd : ∀ t, (f t).snd ≠ d.snd)
    (hde' : d' ≠ e') (hd' : d'.snd = (f (Fin.last n)).snd) (he' : e'.snd = (f (Fin.last n)).snd)
    (hdf' : d' ≠ f (Fin.last n)) (hef' : e' ≠ f (Fin.last n)) :
    ¬(zigzagLoopAInfinityAlgebra hns _
      (fst_eq_snd_of_mem_support_single_rotate_zigzagBacktrackWalk hed (1 : k))).IsFormal := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨a, ha, hhead, hbal, h1⟩ := exists_zigzagBacktrackPairing_obstruction_single_eq_one_of_walk
    (k := k) (hns := hns) hde hed hf₀ hdf hef hf hf' hfd hde' hd' he' hdf' hef'
  exact not_isFormal_zigzagLoopAInfinityAlgebra_of_isUnit_zigzagBacktrackPairing
    ha hhead hbal _ _ (h1.symm ▸ isUnit_one)

/-- **The zigzag algebra of a graph with two branch vertices joined by a suitable walk is not
intrinsically formal**, over every nontrivial commutative ring. The hypotheses are those of
`TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_single_of_walk`: two vertices with three distinct
neighbours each, joined by a non-backtracking walk which leaves the first through its third
neighbour, enters the second through its third neighbour, and does not return to the first. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_walk [Nontrivial k]
    {d e d' e' : G.Dart} {n : ℕ} {f : Fin (n + 1) → G.Dart} (hde : d ≠ e)
    (hed : e.snd = d.snd) (hf₀ : (f 0).fst = d.snd) (hdf : d ≠ (f 0).symm)
    (hef : e ≠ (f 0).symm) (hf : ∀ t : Fin n, G.DartAdj (f t.castSucc) (f t.succ))
    (hf' : ∀ t : Fin n, f t.castSucc ≠ (f t.succ).symm) (hfd : ∀ t, (f t).snd ≠ d.snd)
    (hde' : d' ≠ e') (hd' : d'.snd = (f (Fin.last n)).snd) (he' : e'.snd = (f (Fin.last n)).snd)
    (hdf' : d' ≠ f (Fin.last n)) (hef' : e' ≠ f (Fin.last n)) :
    ¬(𝒵).IsIntrinsicallyFormal :=
  not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal
    (not_isFormal_zigzagLoopAInfinityAlgebra_single_of_walk hde hed hf₀ hdf hef hf hf' hfd hde' hd'
      he' hdf' hef')

/-- **The zigzag algebra of a graph with two branch vertices in one component is not
intrinsically formal**, over every nontrivial commutative ring: if two distinct vertices `v` and `w`
of `G`, each of degree at least three, are joined by a walk, then some `A∞` algebra whose cohomology
algebra is the path-graded zigzag algebra is not formal. The detecting deformation is that of
`TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_single_of_walk` along a path from `v` to `w`.
Together with `TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_four_le_degree`
this covers every finite tree other than a path or a tree with at most one vertex of degree
three. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_three_le_degree [Nontrivial k]
    {v w : V} [Fintype (G.neighborSet v)] [Fintype (G.neighborSet w)]
    (hvw : v ≠ w) (hr : G.Reachable v w) (hv : 3 ≤ G.degree v) (hw : 3 ≤ G.degree w) :
    ¬(𝒵).IsIntrinsicallyFormal := by
  classical
  -- The darts `f 0, …, f n` of a path `p` from `v` to `w`; the vertices of `p` are distinct.
  obtain ⟨p, hp⟩ := hr.exists_isPath
  obtain ⟨n, hn⟩ : ∃ n, p.length = n + 1 :=
    Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero fun h ↦ hvw (p.eq_of_length_eq_zero h))
  have hinj {i j : ℕ} (hi : i ≤ n + 1) (hj : j ≤ n + 1) (h : p.getVert i = p.getVert j) : i = j :=
    hp.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) h
  let f : Fin (n + 1) → G.Dart := fun t ↦
    ⟨(p.getVert t, p.getVert (t + 1)), p.adj_getVert_succ (by omega)⟩
  obtain ⟨a, b, ha, hb, hab, hau, hbu⟩ := G.exists_adj_adj_ne_of_three_le_degree hv (p.getVert 1)
  obtain ⟨a', b', ha', hb', hab', hau', hbu'⟩ :=
    G.exists_adj_adj_ne_of_three_le_degree hw (p.getVert n)
  have hd : (⟨(a, v), ha.symm⟩ : G.Dart).snd = p.getVert 0 := p.getVert_zero.symm
  -- Distinct darts are told apart by their tails. The vertices `(f 0).snd` and `(f n).fst` unfold
  -- to `p.getVert 1` and `p.getVert n`, and consecutive darts of `f` are adjacent by definition.
  refine not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_walk (f := f)
    (d := ⟨(a, v), ha.symm⟩) (e := ⟨(b, v), hb.symm⟩) (d' := ⟨(a', w), ha'.symm⟩)
    (e' := ⟨(b', w), hb'.symm⟩)
    (fun h ↦ hab (congrArg (·.fst) h)) rfl ?_ (fun h ↦ hau (congrArg (·.fst) h))
    (fun h ↦ hbu (congrArg (·.fst) h)) (fun _ ↦ rfl) (fun t h ↦ ?_) (fun t h ↦ ?_)
    (fun h ↦ hab' (congrArg (·.fst) h)) ?_ ?_ (fun h ↦ hau' (congrArg (·.fst) h))
    (fun h ↦ hbu' (congrArg (·.fst) h))
  · simp [f]
  · have := hinj (by omega) (by omega) (congrArg (·.fst) h)
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  · rw [hd] at h
    exact Nat.succ_ne_zero _ (hinj (by omega) (by omega) h)
  all_goals simp [f, ← hn]

end TauCeti
