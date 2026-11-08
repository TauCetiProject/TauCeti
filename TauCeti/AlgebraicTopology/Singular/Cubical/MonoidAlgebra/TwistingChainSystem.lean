/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Pairing
public import TauCeti.Algebra.Homology.DG.Twisted.Cocycle

/-!
# Twisting chain systems and the Barraud–Cornea cocycle

Let `P` be a finite set graded by `ind : P → ℤ`, and let `M x y` be spaces, one for each pair of
elements of `P`, with composition maps `ι x z y : M x z × M z y → M x y`. In Morse theory `P` is
the set of critical points of a Morse function graded by the Morse index, `M x y` is the
compactified space of trajectories from `x` to `y`, and `ι x z y` includes the broken trajectories
through `z` into its boundary.

A **twisting chain system** is a family of normalized cubical chains `s x y` of `M x y`, of
dimension `ind x - ind y - 1` (cohomological degree `ind y - ind x + 1`), satisfying

`∂ s x y = Σ_z (-1) ^ (ind x - ind z) • ι_* (s x z × s z y)`

(`TauCeti.TwistingChainSystem`). A representing chain system of Barraud and Cornea is such a
system in which each `s x y` is moreover a fundamental chain of `M x y` relative to its boundary.

Two facts about the right-hand side, the **twisting sum** `TauCeti.twistingChainSum`, are proved:

* It is a cycle as soon as the twisting equation holds at `(x, z)` and `(z, y)` for every `z`
  whose index lies strictly between those of `y` and `x`, and the composition maps are associative
  (`TauCeti.cubicalChainDifferential_twistingChainSum`). This is what makes an inductive
  construction of a chain system possible: once the chains of the pairs with smaller index
  difference are chosen, the twisting sum of `(x, y)` is a cycle, and `s x y` is any chain
  bounding it.
* Evaluation maps `q x y : M x y → G` to a topological monoid that are multiplicative,
  `q (ι (u, v)) = q u * q v`, carry it to the twisting product of the push-forwards
  (`TauCeti.cubicalChainSumMap_twistingChainSum`).

Consequently the push-forwards `q_* (s x y)` form a twisting cocycle with values in the
differential graded algebra `C^□_*(G; R)` (`TauCeti.TwistingChainSystem.twistingCocycle`). For
`G` the Moore loops of a space `B` and `q` the evaluation of trajectories into loops, this is the
**Barraud–Cornea cocycle**, the input of the Morse complex with coefficients in a DG local system.

## Main definitions

* `TauCeti.twistingChainSum`: the twisting sum `Σ_z (-1) ^ (ind x - ind z) • ι_* (s x z × s z y)`.
* `TauCeti.TwistingChainSystem`: chains satisfying the twisting equation.
* `TauCeti.TwistingChainSystem.twistingCocycle`: the twisting cocycle of push-forwards along
  multiplicative evaluation maps.

## Main results

* `TauCeti.twistingChainSum_eq_zero_of_le`: the twisting sum of a graded family vanishes when
  `ind x ≤ ind y`, and so does the chain of `(x, y)` in a twisting chain system
  (`TauCeti.TwistingChainSystem.chain_eq_zero_of_le`).
* `TauCeti.cubicalChainDifferential_twistingChainSum`: the twisting sum is a cycle.
* `TauCeti.cubicalChainSumMap_twistingChainSum`: push-forward along multiplicative evaluation maps.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. 166 (2007), 657–722, Section 2 and Appendix A.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 5 and 6.
-/

public section

noncomputable section

namespace TauCeti

open NormalizedCubicalChain

variable {P : Type*} [Fintype P] (ind : P → ℤ) {M : P → P → Type*}
  [∀ x y, TopologicalSpace (M x y)] (ι : ∀ x y z, C(M x y × M y z, M x z)) (R : Type*)
  [CommRing R]

/-- The **twisting sum** of a family of chains `s x y` of the spaces `M x y`:
`Σ_z (-1) ^ (ind x - ind z) • ι_* (s x z × s z y)`, the right-hand side of the twisting
equation. -/
def twistingChainSum (s : ∀ x y, normalizedCubicalChainAlgebra (M x y) R) (x y : P) :
    normalizedCubicalChainAlgebra (M x y) R :=
  ∑ z, (ind x - ind z).negOnePow • cubicalChainSumPairing R (ι x z y) (s x z) (s z y)

/-- The twisting sum, unfolded. -/
theorem twistingChainSum_def (s : ∀ x y, normalizedCubicalChainAlgebra (M x y) R) (x y : P) :
    twistingChainSum ind ι R s x y =
      ∑ z, (ind x - ind z).negOnePow • cubicalChainSumPairing R (ι x z y) (s x z) (s z y) :=
  (rfl)

/-- A **twisting chain system** for the composition maps `ι`: chains `s x y` of `M x y`, of
cohomological degree `ind y - ind x + 1`, satisfying the twisting equation
`∂ s x y = Σ_z (-1) ^ (ind x - ind z) • ι_* (s x z × s z y)`. -/
structure TwistingChainSystem where
  /-- The chain of the space `M x y`. -/
  chain : ∀ x y, normalizedCubicalChainAlgebra (M x y) R
  /-- Each chain is homogeneous, of cohomological degree `ind y - ind x + 1`. -/
  mem_graded : ∀ x y, chain x y ∈ cubicalChainGrading (M x y) R (ind y - ind x + 1)
  /-- The twisting equation. -/
  twisting : ∀ x y,
    cubicalChainDifferential (M x y) R (chain x y) = twistingChainSum ind ι R chain x y

variable {ind ι R}

section Graded

variable {s : ∀ x y, normalizedCubicalChainAlgebra (M x y) R}

/-- The twisting sum of a family of chains of cohomological degrees `ind y - ind x + 1` vanishes
when `ind x ≤ ind y`: the term of `z` vanishes because the chain of `(x, z)` does when
`ind x ≤ ind z`, and the chain of `(z, y)` does when `ind z < ind x ≤ ind y`. -/
theorem twistingChainSum_eq_zero_of_le
    (hs : ∀ x y, s x y ∈ cubicalChainGrading (M x y) R (ind y - ind x + 1)) {x y : P}
    (hxy : ind x ≤ ind y) : twistingChainSum ind ι R s x y = 0 := by
  refine Finset.sum_eq_zero fun z _ ↦ ?_
  rcases le_or_gt (ind x) (ind z) with hxz | hxz
  · rw [eq_zero_of_mem_cubicalChainGrading_of_pos _ _ (by omega) (hs x z), map_zero,
      LinearMap.zero_apply, smul_zero]
  · rw [eq_zero_of_mem_cubicalChainGrading_of_pos _ _ (by omega) (hs z y), map_zero, smul_zero]

end Graded

namespace TwistingChainSystem

@[ext]
theorem ext {S₁ S₂ : TwistingChainSystem ind ι R} (h : ∀ x y, S₁.chain x y = S₂.chain x y) :
    S₁ = S₂ := by
  cases S₁; cases S₂
  congr
  funext x y
  exact h x y

/-- The chain of `(x, y)` vanishes when `ind x ≤ ind y`. -/
theorem chain_eq_zero_of_le (S : TwistingChainSystem ind ι R) {x y : P} (hxy : ind x ≤ ind y) :
    S.chain x y = 0 :=
  eq_zero_of_mem_cubicalChainGrading_of_pos _ _ (by omega) (S.mem_graded x y)

end TwistingChainSystem

/-! ### The twisting sum is a cycle -/

section Cycle

variable {s : ∀ x y, normalizedCubicalChainAlgebra (M x y) R}

/-- The twisting equation holds automatically at the pairs `(x, z)` with `ind x ≤ ind z`, where
both sides vanish; so in a product `ι_* (s x z × s z y)` the boundary of the left factor may be
replaced by its twisting sum as soon as the equation holds when `z` is strictly between `y` and
`x`. -/
private theorem pairing_differential_left
    (hs : ∀ x y, s x y ∈ cubicalChainGrading (M x y) R (ind y - ind x + 1)) {x z y : P}
    (h : ind y < ind z → ind z < ind x →
      cubicalChainDifferential (M x z) R (s x z) = twistingChainSum ind ι R s x z) :
    cubicalChainSumPairing R (ι x z y) (cubicalChainDifferential (M x z) R (s x z)) (s z y) =
      cubicalChainSumPairing R (ι x z y) (twistingChainSum ind ι R s x z) (s z y) := by
  by_cases hzy : ind y < ind z
  · by_cases hxz : ind z < ind x
    · rw [h hzy hxz]
    · rw [eq_zero_of_mem_cubicalChainGrading_of_pos _ _ (by omega) (hs x z),
        twistingChainSum_eq_zero_of_le hs (by omega), map_zero]
  · rw [eq_zero_of_mem_cubicalChainGrading_of_pos _ _ (by omega) (hs z y), map_zero,
      map_zero]

/-- The right-hand analogue of `pairing_differential_left`. -/
private theorem pairing_differential_right
    (hs : ∀ x y, s x y ∈ cubicalChainGrading (M x y) R (ind y - ind x + 1)) {x z y : P}
    (h : ind y < ind z → ind z < ind x →
      cubicalChainDifferential (M z y) R (s z y) = twistingChainSum ind ι R s z y) :
    cubicalChainSumPairing R (ι x z y) (s x z) (cubicalChainDifferential (M z y) R (s z y)) =
      cubicalChainSumPairing R (ι x z y) (s x z) (twistingChainSum ind ι R s z y) := by
  by_cases hxz : ind z < ind x
  · by_cases hzy : ind y < ind z
    · rw [h hzy hxz]
    · rw [eq_zero_of_mem_cubicalChainGrading_of_pos _ _ (by omega) (hs z y),
        twistingChainSum_eq_zero_of_le hs (by omega), map_zero]
  · rw [eq_zero_of_mem_cubicalChainGrading_of_pos _ _ (by omega) (hs x z), map_zero,
      LinearMap.zero_apply, LinearMap.zero_apply]

/-- **The twisting sum is a cycle.** Let the composition maps be associative,
`ι x z y (ι x w z (a, b), c) = ι x w y (a, ι w z y (b, c))`, and let `s` be a family of chains of
the cohomological degrees `ind y - ind x + 1` satisfying the twisting equation at the pairs
`(x, z)` and `(z, y)` for every `z` whose index lies strictly between those of `y` and `x`. Then
the twisting sum of `(x, y)` is a cycle. -/
theorem cubicalChainDifferential_twistingChainSum
    (hs : ∀ x y, s x y ∈ cubicalChainGrading (M x y) R (ind y - ind x + 1)) {x y : P}
    (hι : ∀ w z (a : M x w) (b : M w z) (c : M z y),
      ι x z y (ι x w z (a, b), c) = ι x w y (a, ι w z y (b, c)))
    (h : ∀ z, ind y < ind z → ind z < ind x →
      cubicalChainDifferential (M x z) R (s x z) = twistingChainSum ind ι R s x z ∧
        cubicalChainDifferential (M z y) R (s z y) = twistingChainSum ind ι R s z y) :
    cubicalChainDifferential (M x y) R (twistingChainSum ind ι R s x y) = 0 := by
  -- The Leibniz rule, with the boundaries of the factors replaced by their twisting sums.
  have hL (z : P) : cubicalChainDifferential (M x y) R
      ((ind x - ind z).negOnePow • cubicalChainSumPairing R (ι x z y) (s x z) (s z y)) =
        (ind x - ind z).negOnePow •
            cubicalChainSumPairing R (ι x z y) (twistingChainSum ind ι R s x z) (s z y) -
          cubicalChainSumPairing R (ι x z y) (s x z) (twistingChainSum ind ι R s z y) := by
    have hsign : (ind x - ind z).negOnePow * (ind z - ind x + 1).negOnePow = -1 := by
      rw [← Int.negOnePow_add, show ind x - ind z + (ind z - ind x + 1) = 1 by ring,
        Int.negOnePow_one]
    rw [map_zsmul_unit, cubicalChainDifferential_cubicalChainSumPairing _ (hs x z),
      pairing_differential_left hs fun h₁ h₂ ↦ (h z h₁ h₂).1,
      pairing_differential_right hs fun h₁ h₂ ↦ (h z h₁ h₂).2, smul_add, smul_smul, hsign,
      Units.neg_smul, one_smul]
    exact (sub_eq_add_neg _ _).symm
  rw [twistingChainSum_def, map_sum, Finset.sum_congr rfl fun z _ ↦ hL z, Finset.sum_sub_distrib,
    sub_eq_zero]
  -- Both sides are double sums of products of three chains; associativity identifies them.
  simp only [twistingChainSum_def, map_sum, map_zsmul_unit, LinearMap.sum_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ ↦ Finset.sum_congr rfl fun z _ ↦ ?_
  have hsign : (ind x - ind z).negOnePow * (ind x - ind w).negOnePow =
      (ind w - ind z).negOnePow := by
    rw [← Int.negOnePow_add, Int.negOnePow_eq_iff]
    exact ⟨ind x - ind w, by ring⟩
  rw [LinearMap.smul_apply, smul_smul, cubicalChainSumPairing_assoc (hι w z), hsign]

end Cycle

/-! ### Push-forward along multiplicative evaluation maps -/

section Evaluation

variable {G : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  {q : ∀ x y, C(M x y, G)}

/-- **Push-forward of the twisting sum along multiplicative evaluation maps**: if
`q x y (ι x z y (u, v)) = q x z u * q z y v`, the push-forward of the twisting sum is the twisting
sum of the Pontryagin products of the push-forwards. -/
theorem cubicalChainSumMap_twistingChainSum {x y : P}
    (hq : ∀ z (u : M x z) (v : M z y), q x y (ι x z y (u, v)) = q x z u * q z y v)
    (s : ∀ x y, normalizedCubicalChainAlgebra (M x y) R) :
    cubicalChainSumMap R (q x y) (twistingChainSum ind ι R s x y) =
      ∑ z, (ind x - ind z).negOnePow •
        (cubicalChainSumMap R (q x z) (s x z) * cubicalChainSumMap R (q z y) (s z y)) := by
  rw [twistingChainSum_def, map_sum]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  have hcomp : (q x y).comp (ι x z y) = (mulMap G).comp ((q x z).prodMap (q z y)) :=
    ContinuousMap.ext fun ⟨u, v⟩ ↦ by simpa using hq z u v
  rw [map_zsmul_unit, cubicalChainSumMap_cubicalChainSumPairing, hcomp,
    cubicalChainSumPairing_comp_prodMap, cubicalChainSumPairing_mulMap]

namespace TwistingChainSystem

variable (q) in
/-- **The Barraud–Cornea cocycle** of a twisting chain system: for evaluation maps
`q x y : M x y → G` into a topological monoid that are multiplicative,
`q x y (ι x z y (u, v)) = q x z u * q z y v`, the push-forwards `q_* (s x y)` form a twisting
cocycle with values in the differential graded algebra `C^□_*(G; R)` of normalized cubical
chains. For the Moore loops `G = Ω_b B` of a space, it is a `TauCeti.LoopTwistingCocycle`. -/
def twistingCocycle (S : TwistingChainSystem ind ι R)
    (hq : ∀ x z y (u : M x z) (v : M z y), q x y (ι x z y (u, v)) = q x z u * q z y v) :
    TwistingCocycle (R := R) (A := normalizedCubicalChainAlgebra G R) (cubicalChainGrading G R)
      (cubicalChainDifferential G R) P ind :=
  TwistingCocycle.ofNonpos (fun x y ↦ cubicalChainSumMap R (q x y) (S.chain x y))
    (fun x y ↦ cubicalChainSumMap_mem _ (S.mem_graded x y))
    (fun x y ↦ by
      rw [cubicalChainDifferential_cubicalChainSumMap, S.twisting,
        cubicalChainSumMap_twistingChainSum (hq x · y)])
    fun _ hn ↦ cubicalChainGrading_eq_bot G R hn

/-- The entries of the Barraud–Cornea cocycle are the push-forwards of the chains. -/
@[simp]
theorem twistingCocycle_m (S : TwistingChainSystem ind ι R)
    (hq : ∀ x z y (u : M x z) (v : M z y), q x y (ι x z y (u, v)) = q x z u * q z y v)
    (x y : P) :
    (S.twistingCocycle q hq).m x y = cubicalChainSumMap R (q x y) (S.chain x y) := by
  rw [twistingCocycle, TwistingCocycle.ofNonpos_m]

end TwistingChainSystem

end Evaluation

end TauCeti
