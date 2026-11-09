/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.TwistingChainSystem
public import TauCeti.Algebra.Homology.DG.Twisted.Homotopy
import TauCeti.Algebra.Ring.NegOnePow

/-!
# Continuation and parametrized chain systems

Let `S` and `S'` be twisting chain systems (`TauCeti.TwistingChainSystem`) on graded finite sets
`(P, ind)` and `(Q, indQ)`, for spaces `M x y` and `M' x y` with composition maps `ι` and `ι'`.
In Morse theory these are the representing chain systems of the compactified trajectory spaces of
two Morse functions. A homotopy between the two functions has compactified spaces `N x y` of
continuation trajectories from `x ∈ P` to `y ∈ Q`, whose boundary contains the broken trajectories
`M x z × N z y` and `N x z × M' z y`, included by maps `κ` and `κ'`.

A **continuation chain system** is a family of normalized cubical chains `ν x y` of `N x y`, of
dimension `ind x - indQ y` (cohomological degree `indQ y - ind x`), satisfying

`∂ ν x y = Σ_z κ_* (s x z × ν z y) + Σ_z (-1) ^ (ind x - indQ z - 1) • κ'_* (ν x z × s' z y)`

(`TauCeti.ContinuationChainSystem`). Two such systems, on spaces `N₀ x y` and `N₁ x y`, are joined
by a **parametrized chain system** on spaces `H x y` containing both, through maps `j₀` and `j₁`:
chains `h x y` of dimension `ind x - indQ y + 1` with

`∂ h x y = j₁_* ν₁ x y - j₀_* ν₀ x y + Σ_z (-1) ^ (ind x - ind z) • κH_* (s x z × h z y)
  + Σ_z (-1) ^ (ind x - indQ z) • κH'_* (h x z × s' z y)`,

where `κH` and `κH'` are the composition maps of the spaces `H x y`
(`TauCeti.ParametrizedChainSystem`). In Morse theory `H x y` is the compactified space of
trajectories of a one-parameter family of homotopies.

The right-hand side of the continuation equation, the **continuation sum**
`TauCeti.continuationChainSum`, is a cycle as soon as the continuation equation holds at the pairs
of smaller index difference and the composition maps are associative
(`TauCeti.cubicalChainDifferential_continuationChainSum`). This is the condition for the inductive
step of the construction of a continuation chain system.

Evaluation maps into a topological monoid `G` which are multiplicative for all the composition maps
carry these systems to the algebra: the push-forwards of a continuation chain system form a
continuation cocycle between the twisting cocycles of `S` and `S'`
(`TauCeti.ContinuationChainSystem.continuationCocycle`), and those of a parametrized chain system
form a parametrized cocycle between the two continuation cocycles
(`TauCeti.ParametrizedChainSystem.parametrizedCocycle`). So the continuation maps of the twisted
complexes induced by `ν₀` and `ν₁` are chain homotopic, through
`TauCeti.ParametrizedCocycle.homotopy`. When moreover `S` and `S'` are representing chain systems,
`ν` and `h` are fundamental chains of the continuation and parametrized trajectory spaces and the
evaluation maps send trajectories to Moore loops of a space, these are the continuation cocycles
relating the Barraud–Cornea cocycles of two choices of data.

## Main definitions

* `TauCeti.continuationChainSum`: the right-hand side of the continuation equation.
* `TauCeti.ContinuationChainSystem`: chains satisfying the continuation equation.
* `TauCeti.ContinuationChainSystem.continuationCocycle`: the continuation cocycle of push-forwards.
* `TauCeti.parametrizedChainSum`: the right-hand side of the parametrized equation.
* `TauCeti.ParametrizedChainSystem`: chains satisfying the parametrized equation.
* `TauCeti.ParametrizedChainSystem.parametrizedCocycle`: the parametrized cocycle of
  push-forwards.

## Main results

* `TauCeti.continuationChainSum_eq_zero_of_le` and `TauCeti.parametrizedChainSum_eq_zero_of_lt`:
  the continuation and parametrized sums of graded families vanish for degree reasons.
* `TauCeti.cubicalChainDifferential_continuationChainSum` and
  `TauCeti.cubicalChainDifferential_parametrizedChainSum`: the continuation and parametrized sums
  are cycles.
* `TauCeti.cubicalChainSumMap_continuationChainSum` and
  `TauCeti.cubicalChainSumMap_parametrizedChainSum`: push-forward along multiplicative evaluation
  maps.
* `TauCeti.cubicalChainSumMap_continuationChainSum_of_comp`: push-forward of the continuation sum
  along maps compatible with the composition maps.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4, Definitions 1.10 and 1.11.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 5 and 6.
-/

public section

noncomputable section

namespace TauCeti

open NormalizedCubicalChain

section Continuation

variable {P : Type*} [Fintype P] (ind : P → ℤ) {M : P → P → Type*}
  [∀ x y, TopologicalSpace (M x y)] {Q : Type*} [Fintype Q] (indQ : Q → ℤ)
  {M' : Q → Q → Type*} [∀ x y, TopologicalSpace (M' x y)] {N : P → Q → Type*}
  [∀ x y, TopologicalSpace (N x y)] (κ : ∀ x y z, C(M x y × N y z, N x z))
  (κ' : ∀ x y z, C(N x y × M' y z, N x z)) (R : Type*) [CommRing R]

/-- The **continuation sum** of families of chains `s x y` of `M x y`, `s' x y` of `M' x y` and
`ν x y` of `N x y`:
`Σ_z κ_* (s x z × ν z y) + Σ_z (-1) ^ (ind x - indQ z - 1) • κ'_* (ν x z × s' z y)`, the right-hand
side of the continuation equation. -/
def continuationChainSum (s : ∀ x y, normalizedCubicalChainAlgebra (M x y) R)
    (s' : ∀ x y, normalizedCubicalChainAlgebra (M' x y) R)
    (ν : ∀ x y, normalizedCubicalChainAlgebra (N x y) R) (x : P) (y : Q) :
    normalizedCubicalChainAlgebra (N x y) R :=
  ∑ z, cubicalChainSumPairing R (κ x z y) (s x z) (ν z y) +
    ∑ z, (ind x - indQ z - 1).negOnePow • cubicalChainSumPairing R (κ' x z y) (ν x z) (s' z y)

/-- The continuation sum, unfolded. -/
theorem continuationChainSum_def (s : ∀ x y, normalizedCubicalChainAlgebra (M x y) R)
    (s' : ∀ x y, normalizedCubicalChainAlgebra (M' x y) R)
    (ν : ∀ x y, normalizedCubicalChainAlgebra (N x y) R) (x : P) (y : Q) :
    continuationChainSum ind indQ κ κ' R s s' ν x y =
      ∑ z, cubicalChainSumPairing R (κ x z y) (s x z) (ν z y) +
        ∑ z, (ind x - indQ z - 1).negOnePow •
          cubicalChainSumPairing R (κ' x z y) (ν x z) (s' z y) :=
  (rfl)

variable {ind indQ R} {ι : ∀ x y z, C(M x y × M y z, M x z)}
  {ι' : ∀ x y z, C(M' x y × M' y z, M' x z)}

section Graded

variable {κ κ'} {s : ∀ x y, normalizedCubicalChainAlgebra (M x y) R}
  {s' : ∀ x y, normalizedCubicalChainAlgebra (M' x y) R}
  {ν : ∀ x y, normalizedCubicalChainAlgebra (N x y) R}

/-- The continuation sum of families of chains of cohomological degrees `ind y - ind x + 1`,
`indQ y - indQ x + 1` and `indQ y - ind x` vanishes when `ind x ≤ indQ y`. -/
theorem continuationChainSum_eq_zero_of_le
    (hs : ∀ x y, s x y ∈ cubicalChainGrading (M x y) R (ind y - ind x + 1))
    (hs' : ∀ x y, s' x y ∈ cubicalChainGrading (M' x y) R (indQ y - indQ x + 1))
    (hν : ∀ x y, ν x y ∈ cubicalChainGrading (N x y) R (indQ y - ind x)) {x : P} {y : Q}
    (hxy : ind x ≤ indQ y) : continuationChainSum ind indQ κ κ' R s s' ν x y = 0 := by
  -- Every term has cohomological degree `indQ y - ind x + 1 > 0`.
  have h₁ (z : P) : cubicalChainSumPairing R (κ x z y) (s x z) (ν z y) = 0 :=
    eq_zero_of_mem_cubicalChainGrading_of_pos _ _ (by omega)
      (cubicalChainSumPairing_mem _ (hs x z) (hν z y))
  have h₂ (z : Q) : cubicalChainSumPairing R (κ' x z y) (ν x z) (s' z y) = 0 :=
    eq_zero_of_mem_cubicalChainGrading_of_pos _ _ (by omega)
      (cubicalChainSumPairing_mem _ (hν x z) (hs' z y))
  simp [continuationChainSum_def, h₁, h₂]

end Graded

/-- A **continuation chain system** from the twisting chain system `S` to the twisting chain
system `S'`, for the composition maps `κ` and `κ'`: chains `ν x y` of `N x y`, of cohomological
degree `indQ y - ind x`, satisfying the continuation equation
`∂ ν x y = Σ_z κ_* (s x z × ν z y) + Σ_z (-1) ^ (ind x - indQ z - 1) • κ'_* (ν x z × s' z y)`. -/
structure ContinuationChainSystem (S : TwistingChainSystem ind ι R)
    (S' : TwistingChainSystem indQ ι' R) where
  /-- The chain of the space `N x y`. -/
  chain : ∀ x y, normalizedCubicalChainAlgebra (N x y) R
  /-- Each chain is homogeneous, of cohomological degree `indQ y - ind x`. -/
  mem_graded : ∀ x y, chain x y ∈ cubicalChainGrading (N x y) R (indQ y - ind x)
  /-- The continuation equation. -/
  continuation : ∀ x y, cubicalChainDifferential (N x y) R (chain x y) =
    continuationChainSum ind indQ κ κ' R S.chain S'.chain chain x y

namespace ContinuationChainSystem

variable {κ κ'} {S : TwistingChainSystem ind ι R} {S' : TwistingChainSystem indQ ι' R}

@[ext]
theorem ext {T₁ T₂ : ContinuationChainSystem κ κ' S S'} (h : ∀ x y, T₁.chain x y = T₂.chain x y) :
    T₁ = T₂ := by
  cases T₁; cases T₂
  congr
  funext x y
  exact h x y

/-- The chain of `(x, y)` vanishes when `ind x < indQ y`. -/
theorem chain_eq_zero_of_lt (T : ContinuationChainSystem κ κ' S S') {x : P} {y : Q}
    (hxy : ind x < indQ y) : T.chain x y = 0 :=
  eq_zero_of_mem_cubicalChainGrading_of_pos _ _ (by omega) (T.mem_graded x y)

end ContinuationChainSystem

/-! ### The continuation sum is a cycle -/

section Cycle

variable {κ κ'} (S : TwistingChainSystem ind ι R) (S' : TwistingChainSystem indQ ι' R)
  {ν : ∀ x y, normalizedCubicalChainAlgebra (N x y) R}

/-- The continuation equation holds automatically at the pairs `(x, y)` with `ind x ≤ indQ y`,
where both sides vanish for degree reasons. -/
private theorem continuation_of_le
    (hν : ∀ x y, ν x y ∈ cubicalChainGrading (N x y) R (indQ y - ind x)) {x : P} {y : Q}
    (hxy : ind x ≤ indQ y) :
    cubicalChainDifferential (N x y) R (ν x y) =
      continuationChainSum ind indQ κ κ' R S.chain S'.chain ν x y := by
  rw [cubicalChainDifferential_eq_zero_of_nonneg _ _ (by omega) (hν x y),
    continuationChainSum_eq_zero_of_le S.mem_graded S'.mem_graded hν hxy]

/-- The Leibniz rule on a term of the first sum of the continuation sum, with the boundaries of
the factors replaced by their sums. -/
private theorem cubicalChainDifferential_continuation_left
    (hν : ∀ x y, ν x y ∈ cubicalChainGrading (N x y) R (indQ y - ind x)) {x z : P} {y : Q}
    (hl : indQ y < ind z → ind z < ind x → cubicalChainDifferential (N z y) R (ν z y) =
      continuationChainSum ind indQ κ κ' R S.chain S'.chain ν z y) :
    cubicalChainDifferential (N x y) R
      (cubicalChainSumPairing R (κ x z y) (S.chain x z) (ν z y)) =
        cubicalChainSumPairing R (κ x z y) (twistingChainSum ind ι R S.chain x z) (ν z y) +
          (ind z - ind x + 1).negOnePow • cubicalChainSumPairing R (κ x z y) (S.chain x z)
            (continuationChainSum ind indQ κ κ' R S.chain S'.chain ν z y) := by
  rw [cubicalChainDifferential_cubicalChainSumPairing _ (S.mem_graded x z), S.twisting]
  by_cases hzx : ind z < ind x
  · by_cases hyz : indQ y < ind z
    · rw [hl hyz hzx]
    · rw [continuation_of_le S S' hν (show ind z ≤ indQ y by omega)]
  · rw [S.chain_eq_zero_of_le (show ind x ≤ ind z by omega), map_zero, LinearMap.zero_apply,
      LinearMap.zero_apply]

/-- The Leibniz rule on a term of the second sum of the continuation sum, with the boundaries of
the factors replaced by their sums. -/
private theorem cubicalChainDifferential_continuation_right
    (hν : ∀ x y, ν x y ∈ cubicalChainGrading (N x y) R (indQ y - ind x)) {x : P} {y z : Q}
    (hr : indQ y < indQ z → indQ z < ind x → cubicalChainDifferential (N x z) R (ν x z) =
      continuationChainSum ind indQ κ κ' R S.chain S'.chain ν x z) :
    cubicalChainDifferential (N x y) R
      (cubicalChainSumPairing R (κ' x z y) (ν x z) (S'.chain z y)) =
        cubicalChainSumPairing R (κ' x z y)
            (continuationChainSum ind indQ κ κ' R S.chain S'.chain ν x z) (S'.chain z y) +
          (indQ z - ind x).negOnePow • cubicalChainSumPairing R (κ' x z y) (ν x z)
            (twistingChainSum indQ ι' R S'.chain z y) := by
  rw [cubicalChainDifferential_cubicalChainSumPairing _ (hν x z), S'.twisting]
  by_cases hyz : indQ y < indQ z
  · by_cases hzx : indQ z < ind x
    · rw [hr hyz hzx]
    · rw [continuation_of_le S S' hν (show ind x ≤ indQ z by omega)]
  · rw [S'.chain_eq_zero_of_le (show indQ z ≤ indQ y by omega), map_zero, map_zero]

omit [Fintype Q] in
/-- The double sums through `M x w × M w z × N z y` in the boundary of the continuation sum
cancel, by associativity of `κ` with `ι`. -/
private theorem continuation_cancel_left {x : P} {y : Q}
    (hκ : ∀ w z (a : M x w) (b : M w z) (c : N z y),
      κ x z y (ι x w z (a, b), c) = κ x w y (a, κ w z y (b, c))) :
    ∑ z, cubicalChainSumPairing R (κ x z y) (twistingChainSum ind ι R S.chain x z) (ν z y) +
      ∑ z, (ind z - ind x + 1).negOnePow • ∑ w,
        cubicalChainSumPairing R (κ x z y) (S.chain x z)
          (cubicalChainSumPairing R (κ z w y) (S.chain z w) (ν w y)) = 0 := by
  simp only [twistingChainSum_def, map_sum, map_zsmul_unit, LinearMap.sum_apply,
    LinearMap.smul_apply, Finset.smul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun w _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun z _ ↦ ?_
  rw [cubicalChainSumPairing_assoc (hκ w z),
    Int.negOnePow_eq_neg_of_odd_sub (a := ind w - ind x + 1) (b := ind x - ind w)
      ⟨ind w - ind x, by ring⟩, Units.neg_smul, add_neg_cancel]

/-- The double sums through `M x w × N w z × M' z y` in the boundary of the continuation sum
cancel, by associativity of `κ` with `κ'`. -/
private theorem continuation_cancel_middle {x : P} {y : Q}
    (hκκ' : ∀ w z (a : M x w) (b : N w z) (c : M' z y),
      κ' x z y (κ x w z (a, b), c) = κ x w y (a, κ' w z y (b, c))) :
    ∑ z, (ind z - ind x + 1).negOnePow • ∑ w, (ind z - indQ w - 1).negOnePow •
        cubicalChainSumPairing R (κ x z y) (S.chain x z)
          (cubicalChainSumPairing R (κ' z w y) (ν z w) (S'.chain w y)) +
      ∑ z, (ind x - indQ z - 1).negOnePow • ∑ w, cubicalChainSumPairing R (κ' x z y)
        (cubicalChainSumPairing R (κ x w z) (S.chain x w) (ν w z)) (S'.chain z y) = 0 := by
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm (f := fun (z : Q) (w : P) ↦ _), ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun w _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun z _ ↦ ?_
  rw [cubicalChainSumPairing_assoc (hκκ' w z), smul_smul, ← Int.negOnePow_add,
    Int.negOnePow_eq_neg_of_odd_sub (a := ind w - ind x + 1 + (ind w - indQ z - 1))
      (b := ind x - indQ z - 1) ⟨ind w - ind x, by ring⟩, Units.neg_smul, neg_add_cancel]

omit [Fintype P] in
/-- The double sums through `N x w × M' w z × M' z y` in the boundary of the continuation sum
cancel, by associativity of `κ'` with `ι'`. -/
private theorem continuation_cancel_right {x : P} {y : Q}
    (hκ' : ∀ w z (a : N x w) (b : M' w z) (c : M' z y),
      κ' x z y (κ' x w z (a, b), c) = κ' x w y (a, ι' w z y (b, c))) :
    ∑ z, (ind x - indQ z - 1).negOnePow • ∑ w, (ind x - indQ w - 1).negOnePow •
        cubicalChainSumPairing R (κ' x z y)
          (cubicalChainSumPairing R (κ' x w z) (ν x w) (S'.chain w z)) (S'.chain z y) +
      ∑ z, (ind x - indQ z - 1).negOnePow • (indQ z - ind x).negOnePow •
        cubicalChainSumPairing R (κ' x z y) (ν x z) (twistingChainSum indQ ι' R S'.chain z y) =
          0 := by
  simp only [twistingChainSum_def, map_sum, map_zsmul_unit, Finset.smul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun w _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun z _ ↦ ?_
  rw [cubicalChainSumPairing_assoc (hκ' w z), smul_smul, smul_smul, smul_smul,
    ← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_add,
    Int.negOnePow_eq_neg_of_odd_sub (a := ind x - indQ z - 1 + (ind x - indQ w - 1))
      (b := ind x - indQ w - 1 + (indQ w - ind x) + (indQ w - indQ z))
      ⟨ind x - indQ w - 1, by ring⟩, Units.neg_smul, neg_add_cancel]

/-- **The continuation sum is a cycle.** Let the composition maps be associative,
`κ (ι (a, b), c) = κ (a, κ (b, c))`, `κ' (κ (a, b), c) = κ (a, κ' (b, c))` and
`κ' (κ' (a, b), c) = κ' (a, ι' (b, c))`, and let `ν` be a family of chains of cohomological degrees
`indQ y - ind x` satisfying the continuation equation at the pairs `(z, y)` with
`indQ y < ind z < ind x` and `(x, z)` with `indQ y < indQ z < ind x` (elsewhere it holds
automatically for degree reasons). Then the continuation sum of `(x, y)` is a cycle. -/
theorem cubicalChainDifferential_continuationChainSum
    (hν : ∀ x y, ν x y ∈ cubicalChainGrading (N x y) R (indQ y - ind x)) {x : P} {y : Q}
    (hκ : ∀ w z (a : M x w) (b : M w z) (c : N z y),
      κ x z y (ι x w z (a, b), c) = κ x w y (a, κ w z y (b, c)))
    (hκκ' : ∀ w z (a : M x w) (b : N w z) (c : M' z y),
      κ' x z y (κ x w z (a, b), c) = κ x w y (a, κ' w z y (b, c)))
    (hκ' : ∀ w z (a : N x w) (b : M' w z) (c : M' z y),
      κ' x z y (κ' x w z (a, b), c) = κ' x w y (a, ι' w z y (b, c)))
    (hl : ∀ z, indQ y < ind z → ind z < ind x → cubicalChainDifferential (N z y) R (ν z y) =
      continuationChainSum ind indQ κ κ' R S.chain S'.chain ν z y)
    (hr : ∀ z, indQ y < indQ z → indQ z < ind x → cubicalChainDifferential (N x z) R (ν x z) =
      continuationChainSum ind indQ κ κ' R S.chain S'.chain ν x z) :
    cubicalChainDifferential (N x y) R
      (continuationChainSum ind indQ κ κ' R S.chain S'.chain ν x y) = 0 := by
  rw [continuationChainSum_def, map_add, map_sum, map_sum]
  simp only [map_zsmul_unit, fun z ↦ cubicalChainDifferential_continuation_left S S' hν (hl z),
    fun z ↦ cubicalChainDifferential_continuation_right S S' hν (hr z), continuationChainSum_def,
    map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_add,
    Finset.sum_add_distrib]
  have hregroup : ∀ a b c d e f : normalizedCubicalChainAlgebra (N x y) R,
      a + (b + c) + (d + e + f) = (a + b) + (c + d) + (e + f) := fun _ _ _ _ _ _ ↦ by abel
  rw [hregroup, continuation_cancel_left S hκ, continuation_cancel_middle S S' hκκ',
    continuation_cancel_right S' hκ', add_zero, add_zero]

end Cycle

variable {κ κ'} in
/-- **Push-forward of the continuation sum along compatible maps**: if
`j (κ (u, v)) = κ₂ (u, j v)` and `j (κ' (u, v)) = κ₂' (j u, v)`, the push-forward along `j` of the
continuation sum for `κ` and `κ'` is the continuation sum for `κ₂` and `κ₂'` of the
push-forwards. -/
theorem cubicalChainSumMap_continuationChainSum_of_comp {N' : P → Q → Type*}
    [∀ x y, TopologicalSpace (N' x y)] {κ₂ : ∀ x y z, C(M x y × N' y z, N' x z)}
    {κ₂' : ∀ x y z, C(N' x y × M' y z, N' x z)} (j : ∀ x y, C(N x y, N' x y)) {x : P} {y : Q}
    (hjκ : ∀ z (u : M x z) (v : N z y), j x y (κ x z y (u, v)) = κ₂ x z y (u, j z y v))
    (hjκ' : ∀ z (u : N x z) (v : M' z y), j x y (κ' x z y (u, v)) = κ₂' x z y (j x z u, v))
    (s : ∀ x y, normalizedCubicalChainAlgebra (M x y) R)
    (s' : ∀ x y, normalizedCubicalChainAlgebra (M' x y) R)
    (ν : ∀ x y, normalizedCubicalChainAlgebra (N x y) R) :
    cubicalChainSumMap R (j x y) (continuationChainSum ind indQ κ κ' R s s' ν x y) =
      continuationChainSum ind indQ κ₂ κ₂' R s s' (fun x y ↦ cubicalChainSumMap R (j x y) (ν x y))
        x y := by
  simp only [continuationChainSum_def, map_add, map_sum, map_zsmul_unit,
    fun z ↦ cubicalChainSumMap_cubicalChainSumPairing_of_comp (R := R) (h := ContinuousMap.id _)
      (hjκ z),
    fun z ↦ cubicalChainSumMap_cubicalChainSumPairing_of_comp (R := R) (h' := ContinuousMap.id _)
      (hjκ' z),
    cubicalChainSumMap_id, LinearMap.id_apply]

/-! ### Push-forward along multiplicative evaluation maps -/

section Evaluation

variable {G : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G] {q : ∀ x y, C(M x y, G)}
  {q' : ∀ x y, C(M' x y, G)} {r : ∀ x y, C(N x y, G)}

variable {κ κ'} in
/-- **Push-forward of the continuation sum along multiplicative evaluation maps**: if
`r (κ (u, v)) = q u * r v` and `r (κ' (u, v)) = r u * q' v`, the push-forward of the continuation
sum is the continuation sum of the Pontryagin products of the push-forwards. -/
theorem cubicalChainSumMap_continuationChainSum {x : P} {y : Q}
    (hκ : ∀ z (u : M x z) (v : N z y), r x y (κ x z y (u, v)) = q x z u * r z y v)
    (hκ' : ∀ z (u : N x z) (v : M' z y), r x y (κ' x z y (u, v)) = r x z u * q' z y v)
    (s : ∀ x y, normalizedCubicalChainAlgebra (M x y) R)
    (s' : ∀ x y, normalizedCubicalChainAlgebra (M' x y) R)
    (ν : ∀ x y, normalizedCubicalChainAlgebra (N x y) R) :
    cubicalChainSumMap R (r x y) (continuationChainSum ind indQ κ κ' R s s' ν x y) =
      ∑ z, cubicalChainSumMap R (q x z) (s x z) * cubicalChainSumMap R (r z y) (ν z y) +
        ∑ z, (ind x - indQ z - 1).negOnePow •
          (cubicalChainSumMap R (r x z) (ν x z) * cubicalChainSumMap R (q' z y) (s' z y)) := by
  simp only [continuationChainSum_def, map_add, map_sum, map_zsmul_unit,
    fun z ↦ cubicalChainSumMap_cubicalChainSumPairing_of_mul (R := R) (hκ z),
    fun z ↦ cubicalChainSumMap_cubicalChainSumPairing_of_mul (R := R) (hκ' z)]

namespace ContinuationChainSystem

variable {κ κ'} {S : TwistingChainSystem ind ι R} {S' : TwistingChainSystem indQ ι' R}

variable (r) in
/-- **The continuation cocycle of push-forwards** of a continuation chain system: for evaluation
maps `q`, `q'` and `r` into a topological monoid that are multiplicative for all the composition
maps, `q (ι (u, v)) = q u * q v`, `q' (ι' (u, v)) = q' u * q' v`, `r (κ (u, v)) = q u * r v` and
`r (κ' (u, v)) = r u * q' v`, the push-forwards `r_* (ν x y)` form a continuation cocycle from the
twisting cocycle of push-forwards of `S` to that of `S'`. -/
def continuationCocycle (T : ContinuationChainSystem κ κ' S S')
    (hq : ∀ x z y (u : M x z) (v : M z y), q x y (ι x z y (u, v)) = q x z u * q z y v)
    (hq' : ∀ x z y (u : M' x z) (v : M' z y), q' x y (ι' x z y (u, v)) = q' x z u * q' z y v)
    (hκ : ∀ x z y (u : M x z) (v : N z y), r x y (κ x z y (u, v)) = q x z u * r z y v)
    (hκ' : ∀ x z y (u : N x z) (v : M' z y), r x y (κ' x z y (u, v)) = r x z u * q' z y v) :
    ContinuationCocycle (S.twistingCocycle q hq) (S'.twistingCocycle q' hq') where
  ν x y := cubicalChainSumMap R (r x y) (T.chain x y)
  mem_graded x y := cubicalChainSumMap_mem _ (T.mem_graded x y)
  continuation x y := by
    rw [cubicalChainDifferential_cubicalChainSumMap, T.continuation,
      cubicalChainSumMap_continuationChainSum (hκ x · y) (hκ' x · y)]
    simp only [TwistingChainSystem.twistingCocycle_m]

/-- The entries of the continuation cocycle of push-forwards are the push-forwards of the
chains. -/
@[simp]
theorem continuationCocycle_ν (T : ContinuationChainSystem κ κ' S S')
    (hq : ∀ x z y (u : M x z) (v : M z y), q x y (ι x z y (u, v)) = q x z u * q z y v)
    (hq' : ∀ x z y (u : M' x z) (v : M' z y), q' x y (ι' x z y (u, v)) = q' x z u * q' z y v)
    (hκ : ∀ x z y (u : M x z) (v : N z y), r x y (κ x z y (u, v)) = q x z u * r z y v)
    (hκ' : ∀ x z y (u : N x z) (v : M' z y), r x y (κ' x z y (u, v)) = r x z u * q' z y v)
    (x : P) (y : Q) :
    (T.continuationCocycle r hq hq' hκ hκ').ν x y = cubicalChainSumMap R (r x y) (T.chain x y) :=
  (rfl)

end ContinuationChainSystem

end Evaluation

end Continuation

/-! ### Parametrized chain systems -/

section Parametrized

variable {P : Type*} [Fintype P] (ind : P → ℤ) {M : P → P → Type*}
  [∀ x y, TopologicalSpace (M x y)] {Q : Type*} [Fintype Q] (indQ : Q → ℤ)
  {M' : Q → Q → Type*} [∀ x y, TopologicalSpace (M' x y)] {N₀ N₁ H : P → Q → Type*}
  [∀ x y, TopologicalSpace (N₀ x y)] [∀ x y, TopologicalSpace (N₁ x y)]
  [∀ x y, TopologicalSpace (H x y)] (κH : ∀ x y z, C(M x y × H y z, H x z))
  (κH' : ∀ x y z, C(H x y × M' y z, H x z)) (j₀ : ∀ x y, C(N₀ x y, H x y))
  (j₁ : ∀ x y, C(N₁ x y, H x y)) (R : Type*) [CommRing R]

/-- The **parametrized sum** of families of chains `s x y` of `M x y`, `s' x y` of `M' x y`,
`ν₀ x y` of `N₀ x y`, `ν₁ x y` of `N₁ x y` and `h x y` of `H x y`:
`j₁_* ν₁ x y - j₀_* ν₀ x y + Σ_z (-1) ^ (ind x - ind z) • κH_* (s x z × h z y)
  + Σ_z (-1) ^ (ind x - indQ z) • κH'_* (h x z × s' z y)`,
the right-hand side of the parametrized equation. -/
def parametrizedChainSum (s : ∀ x y, normalizedCubicalChainAlgebra (M x y) R)
    (s' : ∀ x y, normalizedCubicalChainAlgebra (M' x y) R)
    (ν₀ : ∀ x y, normalizedCubicalChainAlgebra (N₀ x y) R)
    (ν₁ : ∀ x y, normalizedCubicalChainAlgebra (N₁ x y) R)
    (h : ∀ x y, normalizedCubicalChainAlgebra (H x y) R) (x : P) (y : Q) :
    normalizedCubicalChainAlgebra (H x y) R :=
  cubicalChainSumMap R (j₁ x y) (ν₁ x y) - cubicalChainSumMap R (j₀ x y) (ν₀ x y) +
    ∑ z, (ind x - ind z).negOnePow • cubicalChainSumPairing R (κH x z y) (s x z) (h z y) +
    ∑ z, (ind x - indQ z).negOnePow • cubicalChainSumPairing R (κH' x z y) (h x z) (s' z y)

/-- The parametrized sum, unfolded. -/
theorem parametrizedChainSum_def (s : ∀ x y, normalizedCubicalChainAlgebra (M x y) R)
    (s' : ∀ x y, normalizedCubicalChainAlgebra (M' x y) R)
    (ν₀ : ∀ x y, normalizedCubicalChainAlgebra (N₀ x y) R)
    (ν₁ : ∀ x y, normalizedCubicalChainAlgebra (N₁ x y) R)
    (h : ∀ x y, normalizedCubicalChainAlgebra (H x y) R) (x : P) (y : Q) :
    parametrizedChainSum ind indQ κH κH' j₀ j₁ R s s' ν₀ ν₁ h x y =
      cubicalChainSumMap R (j₁ x y) (ν₁ x y) - cubicalChainSumMap R (j₀ x y) (ν₀ x y) +
        ∑ z, (ind x - ind z).negOnePow • cubicalChainSumPairing R (κH x z y) (s x z) (h z y) +
        ∑ z, (ind x - indQ z).negOnePow •
          cubicalChainSumPairing R (κH' x z y) (h x z) (s' z y) :=
  (rfl)

variable {ind indQ R} {ι : ∀ x y z, C(M x y × M y z, M x z)}
  {ι' : ∀ x y z, C(M' x y × M' y z, M' x z)} {κ₀ : ∀ x y z, C(M x y × N₀ y z, N₀ x z)}
  {κ₀' : ∀ x y z, C(N₀ x y × M' y z, N₀ x z)} {κ₁ : ∀ x y z, C(M x y × N₁ y z, N₁ x z)}
  {κ₁' : ∀ x y z, C(N₁ x y × M' y z, N₁ x z)} {S : TwistingChainSystem ind ι R}
  {S' : TwistingChainSystem indQ ι' R}

section Graded

variable {κH κH' j₀ j₁} {s : ∀ x y, normalizedCubicalChainAlgebra (M x y) R}
  {s' : ∀ x y, normalizedCubicalChainAlgebra (M' x y) R}
  {ν₀ : ∀ x y, normalizedCubicalChainAlgebra (N₀ x y) R}
  {ν₁ : ∀ x y, normalizedCubicalChainAlgebra (N₁ x y) R}
  {h : ∀ x y, normalizedCubicalChainAlgebra (H x y) R}

/-- The parametrized sum of families of chains of cohomological degrees `ind y - ind x + 1`,
`indQ y - indQ x + 1`, `indQ y - ind x` and `indQ y - ind x - 1` vanishes when
`ind x < indQ y`. -/
theorem parametrizedChainSum_eq_zero_of_lt
    (hs : ∀ x y, s x y ∈ cubicalChainGrading (M x y) R (ind y - ind x + 1))
    (hs' : ∀ x y, s' x y ∈ cubicalChainGrading (M' x y) R (indQ y - indQ x + 1))
    (hν₀ : ∀ x y, ν₀ x y ∈ cubicalChainGrading (N₀ x y) R (indQ y - ind x))
    (hν₁ : ∀ x y, ν₁ x y ∈ cubicalChainGrading (N₁ x y) R (indQ y - ind x))
    (hh : ∀ x y, h x y ∈ cubicalChainGrading (H x y) R (indQ y - ind x - 1)) {x : P} {y : Q}
    (hxy : ind x < indQ y) :
    parametrizedChainSum ind indQ κH κH' j₀ j₁ R s s' ν₀ ν₁ h x y = 0 := by
  -- Every term has cohomological degree `indQ y - ind x > 0`.
  have h₁ (z : P) : cubicalChainSumPairing R (κH x z y) (s x z) (h z y) = 0 :=
    eq_zero_of_mem_cubicalChainGrading_of_pos _ _ (by omega)
      (cubicalChainSumPairing_mem _ (hs x z) (hh z y))
  have h₂ (z : Q) : cubicalChainSumPairing R (κH' x z y) (h x z) (s' z y) = 0 :=
    eq_zero_of_mem_cubicalChainGrading_of_pos _ _ (by omega)
      (cubicalChainSumPairing_mem _ (hh x z) (hs' z y))
  simp [parametrizedChainSum_def, h₁, h₂,
    eq_zero_of_mem_cubicalChainGrading_of_pos _ _ (by omega) (hν₀ x y),
    eq_zero_of_mem_cubicalChainGrading_of_pos _ _ (by omega) (hν₁ x y)]

end Graded

/-- A **parametrized chain system** between the continuation chain systems `T₀` and `T₁`, for the
composition maps `κH` and `κH'` and the inclusions `j₀` and `j₁`: chains `h x y` of `H x y`, of
cohomological degree `indQ y - ind x - 1`, satisfying the parametrized equation
`∂ h x y = j₁_* ν₁ x y - j₀_* ν₀ x y + Σ_z (-1) ^ (ind x - ind z) • κH_* (s x z × h z y)
  + Σ_z (-1) ^ (ind x - indQ z) • κH'_* (h x z × s' z y)`. -/
structure ParametrizedChainSystem (T₀ : ContinuationChainSystem κ₀ κ₀' S S')
    (T₁ : ContinuationChainSystem κ₁ κ₁' S S') where
  /-- The chain of the space `H x y`. -/
  chain : ∀ x y, normalizedCubicalChainAlgebra (H x y) R
  /-- Each chain is homogeneous, of cohomological degree `indQ y - ind x - 1`. -/
  mem_graded : ∀ x y, chain x y ∈ cubicalChainGrading (H x y) R (indQ y - ind x - 1)
  /-- The parametrized equation. -/
  parametrized : ∀ x y, cubicalChainDifferential (H x y) R (chain x y) =
    parametrizedChainSum ind indQ κH κH' j₀ j₁ R S.chain S'.chain T₀.chain T₁.chain chain x y

namespace ParametrizedChainSystem

variable {κH κH' j₀ j₁} {T₀ : ContinuationChainSystem κ₀ κ₀' S S'}
  {T₁ : ContinuationChainSystem κ₁ κ₁' S S'}

@[ext]
theorem ext {η₁ η₂ : ParametrizedChainSystem κH κH' j₀ j₁ T₀ T₁}
    (h : ∀ x y, η₁.chain x y = η₂.chain x y) : η₁ = η₂ := by
  cases η₁; cases η₂
  congr
  funext x y
  exact h x y

/-- The chain of `(x, y)` vanishes when `ind x + 1 < indQ y`. -/
theorem chain_eq_zero_of_lt (η : ParametrizedChainSystem κH κH' j₀ j₁ T₀ T₁) {x : P} {y : Q}
    (hxy : ind x + 1 < indQ y) : η.chain x y = 0 :=
  eq_zero_of_mem_cubicalChainGrading_of_pos _ _ (by omega) (η.mem_graded x y)

end ParametrizedChainSystem

/-! ### The parametrized sum is a cycle -/

section Cycle

variable {κH κH'}

variable (T₀ : ContinuationChainSystem κ₀ κ₀' S S') (T₁ : ContinuationChainSystem κ₁ κ₁' S S')
  {h : ∀ x y, normalizedCubicalChainAlgebra (H x y) R}

/-- The boundary of the difference `j₁_* ν₁ - j₀_* ν₀` of the pushed-forward continuation chains
is its continuation sum, when the inclusions are compatible with the composition maps. -/
private theorem cubicalChainDifferential_sub_cubicalChainSumMap {x : P} {y : Q}
    (hj₀κ : ∀ z (u : M x z) (v : N₀ z y), j₀ x y (κ₀ x z y (u, v)) = κH x z y (u, j₀ z y v))
    (hj₀κ' : ∀ z (u : N₀ x z) (v : M' z y), j₀ x y (κ₀' x z y (u, v)) = κH' x z y (j₀ x z u, v))
    (hj₁κ : ∀ z (u : M x z) (v : N₁ z y), j₁ x y (κ₁ x z y (u, v)) = κH x z y (u, j₁ z y v))
    (hj₁κ' : ∀ z (u : N₁ x z) (v : M' z y), j₁ x y (κ₁' x z y (u, v)) = κH' x z y (j₁ x z u, v)) :
    cubicalChainDifferential (H x y) R (cubicalChainSumMap R (j₁ x y) (T₁.chain x y) -
      cubicalChainSumMap R (j₀ x y) (T₀.chain x y)) =
        continuationChainSum ind indQ κH κH' R S.chain S'.chain (fun x y ↦
          cubicalChainSumMap R (j₁ x y) (T₁.chain x y) -
            cubicalChainSumMap R (j₀ x y) (T₀.chain x y)) x y := by
  rw [map_sub, cubicalChainDifferential_cubicalChainSumMap,
    cubicalChainDifferential_cubicalChainSumMap, T₁.continuation, T₀.continuation,
    cubicalChainSumMap_continuationChainSum_of_comp j₁ hj₁κ hj₁κ',
    cubicalChainSumMap_continuationChainSum_of_comp j₀ hj₀κ hj₀κ']
  simp only [continuationChainSum_def, map_sub, LinearMap.sub_apply, smul_sub,
    Finset.sum_sub_distrib]
  abel

/-- The parametrized equation holds automatically at the pairs `(x, y)` with `ind x < indQ y`,
where both sides vanish for degree reasons. -/
private theorem parametrized_of_lt
    (hh : ∀ x y, h x y ∈ cubicalChainGrading (H x y) R (indQ y - ind x - 1)) {x : P} {y : Q}
    (hxy : ind x < indQ y) :
    cubicalChainDifferential (H x y) R (h x y) =
      parametrizedChainSum ind indQ κH κH' j₀ j₁ R S.chain S'.chain T₀.chain T₁.chain h x y := by
  rw [cubicalChainDifferential_eq_zero_of_nonneg _ _ (by omega) (hh x y),
    parametrizedChainSum_eq_zero_of_lt S.mem_graded S'.mem_graded T₀.mem_graded T₁.mem_graded hh
      hxy]

/-- The Leibniz rule on a term of the first sum of the parametrized sum, with the boundaries of
the factors replaced by their sums. -/
private theorem cubicalChainDifferential_parametrized_left
    (hh : ∀ x y, h x y ∈ cubicalChainGrading (H x y) R (indQ y - ind x - 1)) {x z : P} {y : Q}
    (hl : indQ y ≤ ind z → ind z < ind x → cubicalChainDifferential (H z y) R (h z y) =
      parametrizedChainSum ind indQ κH κH' j₀ j₁ R S.chain S'.chain T₀.chain T₁.chain h z y) :
    cubicalChainDifferential (H x y) R
      ((ind x - ind z).negOnePow • cubicalChainSumPairing R (κH x z y) (S.chain x z) (h z y)) =
        (ind x - ind z).negOnePow •
            cubicalChainSumPairing R (κH x z y) (twistingChainSum ind ι R S.chain x z) (h z y) -
          cubicalChainSumPairing R (κH x z y) (S.chain x z)
            (parametrizedChainSum ind indQ κH κH' j₀ j₁ R S.chain S'.chain T₀.chain T₁.chain h
              z y) := by
  have hsign : (ind x - ind z).negOnePow * (ind z - ind x + 1).negOnePow = -1 := by
    rw [← Int.negOnePow_add, show ind x - ind z + (ind z - ind x + 1) = 1 by ring,
      Int.negOnePow_one]
  rw [map_zsmul_unit, cubicalChainDifferential_cubicalChainSumPairing _ (S.mem_graded x z),
    S.twisting, smul_add, smul_smul, hsign, Units.neg_smul, one_smul, ← sub_eq_add_neg]
  by_cases hzx : ind z < ind x
  · by_cases hyz : indQ y ≤ ind z
    · rw [hl hyz hzx]
    · rw [parametrized_of_lt j₀ j₁ T₀ T₁ hh (show ind z < indQ y by omega)]
  · rw [S.chain_eq_zero_of_le (show ind x ≤ ind z by omega), map_zero, LinearMap.zero_apply,
      LinearMap.zero_apply]

/-- The Leibniz rule on a term of the second sum of the parametrized sum, with the boundaries of
the factors replaced by their sums. -/
private theorem cubicalChainDifferential_parametrized_right
    (hh : ∀ x y, h x y ∈ cubicalChainGrading (H x y) R (indQ y - ind x - 1)) {x : P} {y z : Q}
    (hr : indQ y < indQ z → indQ z ≤ ind x → cubicalChainDifferential (H x z) R (h x z) =
      parametrizedChainSum ind indQ κH κH' j₀ j₁ R S.chain S'.chain T₀.chain T₁.chain h x z) :
    cubicalChainDifferential (H x y) R
      ((ind x - indQ z).negOnePow • cubicalChainSumPairing R (κH' x z y) (h x z) (S'.chain z y)) =
        (ind x - indQ z).negOnePow • cubicalChainSumPairing R (κH' x z y)
            (parametrizedChainSum ind indQ κH κH' j₀ j₁ R S.chain S'.chain T₀.chain T₁.chain h
              x z) (S'.chain z y) -
          cubicalChainSumPairing R (κH' x z y) (h x z)
            (twistingChainSum indQ ι' R S'.chain z y) := by
  have hsign : (ind x - indQ z).negOnePow * (indQ z - ind x - 1).negOnePow = -1 := by
    rw [← Int.negOnePow_add, show ind x - indQ z + (indQ z - ind x - 1) = -1 by ring,
      Int.negOnePow_neg, Int.negOnePow_one]
  rw [map_zsmul_unit, cubicalChainDifferential_cubicalChainSumPairing _ (hh x z), S'.twisting,
    smul_add, smul_smul, hsign, Units.neg_smul, one_smul, ← sub_eq_add_neg]
  by_cases hyz : indQ y < indQ z
  · by_cases hzx : indQ z ≤ ind x
    · rw [hr hyz hzx]
    · rw [parametrized_of_lt j₀ j₁ T₀ T₁ hh (show ind x < indQ z by omega)]
  · rw [S'.chain_eq_zero_of_le (show indQ z ≤ indQ y by omega), map_zero, map_zero]

omit [Fintype Q] in
/-- The double sums through `M x w × M w z × H z y` in the boundary of the parametrized sum agree,
by associativity of `κH` with `ι`. -/
private theorem parametrized_cancel_left {x : P} {y : Q}
    (hκH : ∀ w z (a : M x w) (b : M w z) (c : H z y),
      κH x z y (ι x w z (a, b), c) = κH x w y (a, κH w z y (b, c))) :
    ∑ z, (ind x - ind z).negOnePow •
        cubicalChainSumPairing R (κH x z y) (twistingChainSum ind ι R S.chain x z) (h z y) =
      ∑ z, ∑ w, (ind z - ind w).negOnePow • cubicalChainSumPairing R (κH x z y) (S.chain x z)
        (cubicalChainSumPairing R (κH z w y) (S.chain z w) (h w y)) := by
  simp only [twistingChainSum_def, map_sum, map_zsmul_unit, LinearMap.sum_apply,
    LinearMap.smul_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ ↦ Finset.sum_congr rfl fun z _ ↦ ?_
  rw [cubicalChainSumPairing_assoc (hκH w z), smul_smul, ← Int.negOnePow_add]
  exact congrArg (· • _) ((Int.negOnePow_eq_iff _ _).2 ⟨ind x - ind w, by ring⟩)

/-- The double sums through `M x w × H w z × M' z y` in the boundary of the parametrized sum
agree, by associativity of `κH` with `κH'`. -/
private theorem parametrized_cancel_middle {x : P} {y : Q}
    (hκHκH' : ∀ w z (a : M x w) (b : H w z) (c : M' z y),
      κH' x z y (κH x w z (a, b), c) = κH x w y (a, κH' w z y (b, c))) :
    ∑ z, (ind x - indQ z).negOnePow • ∑ w, (ind x - ind w).negOnePow •
        cubicalChainSumPairing R (κH' x z y)
          (cubicalChainSumPairing R (κH x w z) (S.chain x w) (h w z)) (S'.chain z y) =
      ∑ z, ∑ w, (ind z - indQ w).negOnePow • cubicalChainSumPairing R (κH x z y) (S.chain x z)
        (cubicalChainSumPairing R (κH' z w y) (h z w) (S'.chain w y)) := by
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ ↦ Finset.sum_congr rfl fun z _ ↦ ?_
  rw [cubicalChainSumPairing_assoc (hκHκH' w z), smul_smul, ← Int.negOnePow_add]
  exact congrArg (· • _) ((Int.negOnePow_eq_iff _ _).2 ⟨ind x - ind w, by ring⟩)

omit [Fintype P] in
/-- The double sums through `H x w × M' w z × M' z y` in the boundary of the parametrized sum
agree, by associativity of `κH'` with `ι'`. -/
private theorem parametrized_cancel_right {x : P} {y : Q}
    (hκH' : ∀ w z (a : H x w) (b : M' w z) (c : M' z y),
      κH' x z y (κH' x w z (a, b), c) = κH' x w y (a, ι' w z y (b, c))) :
    ∑ z, (ind x - indQ z).negOnePow • ∑ w, (ind x - indQ w).negOnePow •
        cubicalChainSumPairing R (κH' x z y)
          (cubicalChainSumPairing R (κH' x w z) (h x w) (S'.chain w z)) (S'.chain z y) =
      ∑ z, cubicalChainSumPairing R (κH' x z y) (h x z)
        (twistingChainSum indQ ι' R S'.chain z y) := by
  simp only [twistingChainSum_def, map_sum, map_zsmul_unit, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ ↦ Finset.sum_congr rfl fun z _ ↦ ?_
  rw [cubicalChainSumPairing_assoc (hκH' w z), smul_smul, ← Int.negOnePow_add]
  exact congrArg (· • _) ((Int.negOnePow_eq_iff _ _).2 ⟨ind x - indQ w, by ring⟩)

/-- **The parametrized sum is a cycle.** Let `T₀` and `T₁` be continuation chain systems whose
inclusions into `H` are compatible with the composition maps, `j (κ (u, v)) = κH (u, j v)` and
`j (κ' (u, v)) = κH' (j u, v)`, let the composition maps be associative,
`κH (ι (a, b), c) = κH (a, κH (b, c))`, `κH' (κH (a, b), c) = κH (a, κH' (b, c))` and
`κH' (κH' (a, b), c) = κH' (a, ι' (b, c))`, and let `h` be a family of chains of cohomological
degrees `indQ y - ind x - 1` satisfying the parametrized equation at the pairs `(z, y)` with
`indQ y ≤ ind z < ind x` and `(x, z)` with `indQ y < indQ z ≤ ind x` (elsewhere it holds
automatically for degree reasons). Then the parametrized sum of `(x, y)` is a cycle. -/
theorem cubicalChainDifferential_parametrizedChainSum
    (hh : ∀ x y, h x y ∈ cubicalChainGrading (H x y) R (indQ y - ind x - 1)) {x : P} {y : Q}
    (hκH : ∀ w z (a : M x w) (b : M w z) (c : H z y),
      κH x z y (ι x w z (a, b), c) = κH x w y (a, κH w z y (b, c)))
    (hκHκH' : ∀ w z (a : M x w) (b : H w z) (c : M' z y),
      κH' x z y (κH x w z (a, b), c) = κH x w y (a, κH' w z y (b, c)))
    (hκH' : ∀ w z (a : H x w) (b : M' w z) (c : M' z y),
      κH' x z y (κH' x w z (a, b), c) = κH' x w y (a, ι' w z y (b, c)))
    (hj₀κ : ∀ z (u : M x z) (v : N₀ z y), j₀ x y (κ₀ x z y (u, v)) = κH x z y (u, j₀ z y v))
    (hj₀κ' : ∀ z (u : N₀ x z) (v : M' z y), j₀ x y (κ₀' x z y (u, v)) = κH' x z y (j₀ x z u, v))
    (hj₁κ : ∀ z (u : M x z) (v : N₁ z y), j₁ x y (κ₁ x z y (u, v)) = κH x z y (u, j₁ z y v))
    (hj₁κ' : ∀ z (u : N₁ x z) (v : M' z y), j₁ x y (κ₁' x z y (u, v)) = κH' x z y (j₁ x z u, v))
    (hl : ∀ z, indQ y ≤ ind z → ind z < ind x → cubicalChainDifferential (H z y) R (h z y) =
      parametrizedChainSum ind indQ κH κH' j₀ j₁ R S.chain S'.chain T₀.chain T₁.chain h z y)
    (hr : ∀ z, indQ y < indQ z → indQ z ≤ ind x → cubicalChainDifferential (H x z) R (h x z) =
      parametrizedChainSum ind indQ κH κH' j₀ j₁ R S.chain S'.chain T₀.chain T₁.chain h x z) :
    cubicalChainDifferential (H x y) R
      (parametrizedChainSum ind indQ κH κH' j₀ j₁ R S.chain S'.chain T₀.chain T₁.chain h x y) =
        0 := by
  -- `δ` is the difference of the pushed-forward continuation chains.
  set δ : ∀ x y, normalizedCubicalChainAlgebra (H x y) R := fun x y ↦
    cubicalChainSumMap R (j₁ x y) (T₁.chain x y) - cubicalChainSumMap R (j₀ x y) (T₀.chain x y)
  have hPS (x : P) (y : Q) :
      parametrizedChainSum ind indQ κH κH' j₀ j₁ R S.chain S'.chain T₀.chain T₁.chain h x y =
        δ x y +
          ∑ z, (ind x - ind z).negOnePow •
            cubicalChainSumPairing R (κH x z y) (S.chain x z) (h z y) +
          ∑ z, (ind x - indQ z).negOnePow •
            cubicalChainSumPairing R (κH' x z y) (h x z) (S'.chain z y) :=
    parametrizedChainSum_def ..
  have hdδ : cubicalChainDifferential (H x y) R (δ x y) =
      continuationChainSum ind indQ κH κH' R S.chain S'.chain δ x y :=
    cubicalChainDifferential_sub_cubicalChainSumMap j₀ j₁ T₀ T₁ hj₀κ hj₀κ' hj₁κ hj₁κ'
  have hε (z : Q) : (ind x - indQ z - 1).negOnePow = -(ind x - indQ z).negOnePow :=
    Int.negOnePow_eq_neg_of_odd_sub ⟨-1, by ring⟩
  rw [hPS, map_add, map_add, hdδ, continuationChainSum_def, map_sum, map_sum]
  simp only [fun z ↦ cubicalChainDifferential_parametrized_left j₀ j₁ T₀ T₁ hh (hl z),
    fun z ↦ cubicalChainDifferential_parametrized_right j₀ j₁ T₀ T₁ hh (hr z)]
  simp only [hPS, map_add, map_sum, map_zsmul_unit, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_add, hε, Units.neg_smul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [parametrized_cancel_left hκH, parametrized_cancel_middle hκHκH',
    parametrized_cancel_right hκH']
  abel

end Cycle

/-! ### Push-forward along multiplicative evaluation maps -/

section Evaluation

variable {G : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G] {q : ∀ x y, C(M x y, G)}
  {q' : ∀ x y, C(M' x y, G)} {r₀ : ∀ x y, C(N₀ x y, G)} {r₁ : ∀ x y, C(N₁ x y, G)}
  {rH : ∀ x y, C(H x y, G)}

variable {κH κH' j₀ j₁} in
/-- **Push-forward of the parametrized sum along multiplicative evaluation maps**: if
`rH ∘ j₀ = r₀`, `rH ∘ j₁ = r₁`, `rH (κH (u, v)) = q u * rH v` and
`rH (κH' (u, v)) = rH u * q' v`, the push-forward of the parametrized sum is the parametrized sum
of the push-forwards. -/
theorem cubicalChainSumMap_parametrizedChainSum {x : P} {y : Q}
    (hj₀ : (rH x y).comp (j₀ x y) = r₀ x y) (hj₁ : (rH x y).comp (j₁ x y) = r₁ x y)
    (hκH : ∀ z (u : M x z) (v : H z y), rH x y (κH x z y (u, v)) = q x z u * rH z y v)
    (hκH' : ∀ z (u : H x z) (v : M' z y), rH x y (κH' x z y (u, v)) = rH x z u * q' z y v)
    (s : ∀ x y, normalizedCubicalChainAlgebra (M x y) R)
    (s' : ∀ x y, normalizedCubicalChainAlgebra (M' x y) R)
    (ν₀ : ∀ x y, normalizedCubicalChainAlgebra (N₀ x y) R)
    (ν₁ : ∀ x y, normalizedCubicalChainAlgebra (N₁ x y) R)
    (h : ∀ x y, normalizedCubicalChainAlgebra (H x y) R) :
    cubicalChainSumMap R (rH x y) (parametrizedChainSum ind indQ κH κH' j₀ j₁ R s s' ν₀ ν₁ h x y) =
      cubicalChainSumMap R (r₁ x y) (ν₁ x y) - cubicalChainSumMap R (r₀ x y) (ν₀ x y) +
        ∑ z, (ind x - ind z).negOnePow •
          (cubicalChainSumMap R (q x z) (s x z) * cubicalChainSumMap R (rH z y) (h z y)) +
        ∑ z, (ind x - indQ z).negOnePow •
          (cubicalChainSumMap R (rH x z) (h x z) * cubicalChainSumMap R (q' z y) (s' z y)) := by
  simp only [parametrizedChainSum_def, map_add, map_sub, map_sum, map_zsmul_unit,
    ← LinearMap.comp_apply, ← cubicalChainSumMap_comp, hj₀, hj₁]
  simp only [LinearMap.comp_apply,
    fun z ↦ cubicalChainSumMap_cubicalChainSumPairing_of_mul (R := R) (hκH z),
    fun z ↦ cubicalChainSumMap_cubicalChainSumPairing_of_mul (R := R) (hκH' z)]

namespace ParametrizedChainSystem

variable {κH κH' j₀ j₁} {T₀ : ContinuationChainSystem κ₀ κ₀' S S'}
  {T₁ : ContinuationChainSystem κ₁ κ₁' S S'}

variable (rH) in
/-- **The parametrized cocycle of push-forwards** of a parametrized chain system: for evaluation
maps into a topological monoid that are multiplicative for all the composition maps and compatible
with the inclusions, `rH ∘ j₀ = r₀` and `rH ∘ j₁ = r₁`, the push-forwards `rH_* (h x y)` form a
parametrized cocycle between the continuation cocycles of push-forwards of `T₀` and `T₁`. -/
def parametrizedCocycle (η : ParametrizedChainSystem κH κH' j₀ j₁ T₀ T₁)
    (hq : ∀ x z y (u : M x z) (v : M z y), q x y (ι x z y (u, v)) = q x z u * q z y v)
    (hq' : ∀ x z y (u : M' x z) (v : M' z y), q' x y (ι' x z y (u, v)) = q' x z u * q' z y v)
    (hκ₀ : ∀ x z y (u : M x z) (v : N₀ z y), r₀ x y (κ₀ x z y (u, v)) = q x z u * r₀ z y v)
    (hκ₀' : ∀ x z y (u : N₀ x z) (v : M' z y), r₀ x y (κ₀' x z y (u, v)) = r₀ x z u * q' z y v)
    (hκ₁ : ∀ x z y (u : M x z) (v : N₁ z y), r₁ x y (κ₁ x z y (u, v)) = q x z u * r₁ z y v)
    (hκ₁' : ∀ x z y (u : N₁ x z) (v : M' z y), r₁ x y (κ₁' x z y (u, v)) = r₁ x z u * q' z y v)
    (hj₀ : ∀ x y, (rH x y).comp (j₀ x y) = r₀ x y) (hj₁ : ∀ x y, (rH x y).comp (j₁ x y) = r₁ x y)
    (hκH : ∀ x z y (u : M x z) (v : H z y), rH x y (κH x z y (u, v)) = q x z u * rH z y v)
    (hκH' : ∀ x z y (u : H x z) (v : M' z y), rH x y (κH' x z y (u, v)) = rH x z u * q' z y v) :
    ParametrizedCocycle (T₀.continuationCocycle r₀ hq hq' hκ₀ hκ₀')
      (T₁.continuationCocycle r₁ hq hq' hκ₁ hκ₁') where
  h x y := cubicalChainSumMap R (rH x y) (η.chain x y)
  mem_graded x y := cubicalChainSumMap_mem _ (η.mem_graded x y)
  parametrized x y := by
    rw [cubicalChainDifferential_cubicalChainSumMap, η.parametrized,
      cubicalChainSumMap_parametrizedChainSum (hj₀ x y) (hj₁ x y) (hκH x · y) (hκH' x · y)]
    simp only [ContinuationChainSystem.continuationCocycle_ν,
      TwistingChainSystem.twistingCocycle_m]

/-- The entries of the parametrized cocycle of push-forwards are the push-forwards of the
chains. -/
@[simp]
theorem parametrizedCocycle_h (η : ParametrizedChainSystem κH κH' j₀ j₁ T₀ T₁)
    (hq : ∀ x z y (u : M x z) (v : M z y), q x y (ι x z y (u, v)) = q x z u * q z y v)
    (hq' : ∀ x z y (u : M' x z) (v : M' z y), q' x y (ι' x z y (u, v)) = q' x z u * q' z y v)
    (hκ₀ : ∀ x z y (u : M x z) (v : N₀ z y), r₀ x y (κ₀ x z y (u, v)) = q x z u * r₀ z y v)
    (hκ₀' : ∀ x z y (u : N₀ x z) (v : M' z y), r₀ x y (κ₀' x z y (u, v)) = r₀ x z u * q' z y v)
    (hκ₁ : ∀ x z y (u : M x z) (v : N₁ z y), r₁ x y (κ₁ x z y (u, v)) = q x z u * r₁ z y v)
    (hκ₁' : ∀ x z y (u : N₁ x z) (v : M' z y), r₁ x y (κ₁' x z y (u, v)) = r₁ x z u * q' z y v)
    (hj₀ : ∀ x y, (rH x y).comp (j₀ x y) = r₀ x y) (hj₁ : ∀ x y, (rH x y).comp (j₁ x y) = r₁ x y)
    (hκH : ∀ x z y (u : M x z) (v : H z y), rH x y (κH x z y (u, v)) = q x z u * rH z y v)
    (hκH' : ∀ x z y (u : H x z) (v : M' z y), rH x y (κH' x z y (u, v)) = rH x z u * q' z y v)
    (x : P) (y : Q) :
    (η.parametrizedCocycle rH hq hq' hκ₀ hκ₀' hκ₁ hκ₁' hj₀ hj₁ hκH hκH').h x y =
      cubicalChainSumMap R (rH x y) (η.chain x y) :=
  (rfl)

end ParametrizedChainSystem

end Evaluation

end Parametrized

end TauCeti
