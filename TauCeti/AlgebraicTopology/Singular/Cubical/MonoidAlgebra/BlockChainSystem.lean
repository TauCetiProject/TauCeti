/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.ContinuationChainSystem
public import TauCeti.Algebra.Homology.DG.Twisted.Block
import TauCeti.Algebra.Ring.NegOnePow

/-!
# Block-triangular twisting chain systems are continuation chain systems

Let `(P, ind)` and `(Q, indQ)` be finite graded sets, and grade `P ⊕ Q` by `ind x + 1` on `P` and
`indQ y` on `Q`. Let `S` be a twisting chain system (`TauCeti.TwistingChainSystem`) on spaces
`M a b` indexed by `P ⊕ Q`, with composition maps `ι`, whose chains from `Q` to `P` vanish,
`S.chain (inr y) (inl x) = 0`. This is the situation of the spaces of trajectories of a field on
`M × ℝ` realizing a homotopy from a Morse function `f₀` to a Morse function `f₁`: the critical
points are the `(p, 0)`, of index `ind p + 1`, and the `(q, 1)`, of index `ind q`, and no trajectory
goes from the level `1` back to the level `0`, so the spaces `M (inr y) (inl x)` are empty.

* The chains between generators of `P`, respectively of `Q`, form twisting chain systems
  `TauCeti.TwistingChainSystem.blockLeft` on the spaces `M (inl x) (inl y)` and
  `TauCeti.TwistingChainSystem.blockRight` on the spaces `M (inr x) (inr y)`.
* The chains from `P` to `Q`, with the sign `(-1) ^ ind x` of their row, form a continuation chain
  system (`TauCeti.ContinuationChainSystem`) from the first to the second, on the spaces
  `N x y = M (inl x) (inr y)`, whose broken trajectories through `P` and through `Q` are included by
  the composition maps `ι (inl x) (inl z) (inr y)` and `ι (inl x) (inr z) (inr y)`
  (`TauCeti.TwistingChainSystem.blockContinuation`).

The construction commutes with the evaluation into a topological monoid: for evaluation maps `q`
which are multiplicative for `ι`, the twisting cocycles of the diagonal blocks are the diagonal
blocks of the twisting cocycle of `S` (`TauCeti.TwistingChainSystem.twistingCocycle_blockLeft`,
`TauCeti.TwistingChainSystem.twistingCocycle_blockRight`), and the continuation cocycle of the
off-diagonal block is its off-diagonal block
(`TauCeti.TwistingChainSystem.continuationCocycle_blockContinuation_ν`), the algebraic construction
`TauCeti.TwistingCocycle.blockContinuation`.

## Main definitions

* `TauCeti.TwistingChainSystem.blockLeft`, `TauCeti.TwistingChainSystem.blockRight`: the diagonal
  blocks of a block-triangular twisting chain system.
* `TauCeti.TwistingChainSystem.blockContinuation`: its off-diagonal block, a continuation chain
  system between the diagonal blocks.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 5 and 6.
-/

public section

noncomputable section

namespace TauCeti

open NormalizedCubicalChain

variable {P : Type*} [Fintype P] {ind : P → ℤ} {Q : Type*} [Fintype Q] {indQ : Q → ℤ}
  {M : P ⊕ Q → P ⊕ Q → Type*} [∀ a b, TopologicalSpace (M a b)]
  {ι : ∀ a b c, C(M a b × M b c, M a c)} {R : Type*} [CommRing R]

/-- The sign of a term of the twisting sum on `P ⊕ Q` through a generator of `P`, multiplied by
the sign of the row, is the sign of the column of its second factor. -/
private theorem negOnePow_smul_negOnePow_smul_pairing_left {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (f : C(X × Y, Z)) (i j : ℤ)
    (a : normalizedCubicalChainAlgebra X R) (b : normalizedCubicalChainAlgebra Y R) :
    i.negOnePow • (i + 1 - (j + 1)).negOnePow • cubicalChainSumPairing R f a b =
      cubicalChainSumPairing R f a (j.negOnePow • b) := by
  rw [map_zsmul_unit, smul_smul]
  congr 1
  rw [← Int.negOnePow_add, Int.negOnePow_eq_iff]
  exact ⟨i - j, by ring⟩

/-- The sign of a term of the twisting sum on `P ⊕ Q` through a generator of `Q`, multiplied by
the sign `(-1) ^ i` of the row, is the sign of the continuation sum applied to `(-1) ^ i • a`. -/
private theorem negOnePow_smul_negOnePow_smul_pairing_right {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (f : C(X × Y, Z)) (i j : ℤ)
    (a : normalizedCubicalChainAlgebra X R) (b : normalizedCubicalChainAlgebra Y R) :
    i.negOnePow • (i + 1 - j).negOnePow • cubicalChainSumPairing R f a b =
      (i - j - 1).negOnePow • cubicalChainSumPairing R f (i.negOnePow • a) b := by
  rw [map_zsmul_unit, LinearMap.smul_apply, smul_smul, smul_smul]
  congr 1
  rw [← Int.negOnePow_add, ← Int.negOnePow_add, Int.negOnePow_eq_iff]
  exact ⟨1, by ring⟩

namespace TwistingChainSystem

variable (S : TwistingChainSystem (Sum.elim (fun x ↦ ind x + 1) indQ) ι R)
  (h : ∀ x y, S.chain (.inr y) (.inl x) = 0)

/-- The **upper-left block** of a twisting chain system on `P ⊕ Q` whose chains from `Q` to `P`
vanish: its chains between generators of `P`, a twisting chain system on `(P, ind)`. -/
def blockLeft : TwistingChainSystem ind (fun x y z ↦ ι (.inl x) (.inl y) (.inl z)) R where
  chain x y := S.chain (.inl x) (.inl y)
  mem_graded x y := by simpa using S.mem_graded (.inl x) (.inl y)
  twisting x y := by
    rw [S.twisting, twistingChainSum_def, twistingChainSum_def, Fintype.sum_sum_type]
    simp [h]

@[simp]
theorem blockLeft_chain (x y : P) : (S.blockLeft h).chain x y = S.chain (.inl x) (.inl y) :=
  (rfl)

/-- The **lower-right block** of a twisting chain system on `P ⊕ Q` whose chains from `Q` to `P`
vanish: its chains between generators of `Q`, a twisting chain system on `(Q, indQ)`. -/
def blockRight : TwistingChainSystem indQ (fun x y z ↦ ι (.inr x) (.inr y) (.inr z)) R where
  chain x y := S.chain (.inr x) (.inr y)
  mem_graded x y := by simpa using S.mem_graded (.inr x) (.inr y)
  twisting x y := by
    rw [S.twisting, twistingChainSum_def, twistingChainSum_def, Fintype.sum_sum_type]
    simp [h]

@[simp]
theorem blockRight_chain (x y : Q) : (S.blockRight h).chain x y = S.chain (.inr x) (.inr y) :=
  (rfl)

/-- The **off-diagonal block** of a twisting chain system on `P ⊕ Q` whose chains from `Q` to `P`
vanish, with the sign `(-1) ^ ind x` of its row: the chains `(-1) ^ ind x • s (inl x) (inr y)` form
a continuation chain system from the upper-left block to the lower-right block, on the spaces
`M (inl x) (inr y)`. -/
def blockContinuation :
    ContinuationChainSystem (fun x z y ↦ ι (.inl x) (.inl z) (.inr y))
      (fun x z y ↦ ι (.inl x) (.inr z) (.inr y)) (S.blockLeft h) (S.blockRight h) where
  chain x y := (ind x).negOnePow • S.chain (.inl x) (.inr y)
  mem_graded x y := by
    have := S.mem_graded (.inl x) (.inr y)
    rw [Sum.elim_inl, Sum.elim_inr, show indQ y - (ind x + 1) + 1 = indQ y - ind x by ring] at this
    rw [Units.smul_def]
    exact zsmul_mem this _
  continuation x y := by
    rw [map_zsmul_unit, S.twisting, twistingChainSum_def, Fintype.sum_sum_type,
      continuationChainSum_def, smul_add, Finset.smul_sum, Finset.smul_sum]
    -- The terms through `P` first: the pattern of the terms through `Q` also matches them.
    simp only [Sum.elim_inl, Sum.elim_inr, blockLeft_chain, blockRight_chain,
      negOnePow_smul_negOnePow_smul_pairing_left]
    simp only [negOnePow_smul_negOnePow_smul_pairing_right]

@[simp]
theorem blockContinuation_chain (x : P) (y : Q) :
    (S.blockContinuation h).chain x y = (ind x).negOnePow • S.chain (.inl x) (.inr y) :=
  (rfl)

section Evaluation

variable {G : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G] {q : ∀ a b, C(M a b, G)}
  (hq : ∀ a c b (u : M a c) (v : M c b), q a b (ι a c b (u, v)) = q a c u * q c b v)

include h in
/-- The twisting cocycle of push-forwards of `S` never goes from `Q` to `P`. -/
theorem twistingCocycle_m_inr_inl (x : P) (y : Q) :
    (S.twistingCocycle q hq).m (.inr y) (.inl x) = 0 := by
  rw [twistingCocycle_m, h, map_zero]

/-- The twisting cocycle of push-forwards of the upper-left block is the upper-left block of the
twisting cocycle of push-forwards. -/
theorem twistingCocycle_blockLeft :
    (S.blockLeft h).twistingCocycle (fun x y ↦ q (.inl x) (.inl y))
        (fun x z y ↦ hq (.inl x) (.inl z) (.inl y)) =
      (S.twistingCocycle q hq).blockLeft (S.twistingCocycle_m_inr_inl h hq) :=
  TwistingCocycle.ext fun x y ↦ by simp

/-- The twisting cocycle of push-forwards of the lower-right block is the lower-right block of
the twisting cocycle of push-forwards. -/
theorem twistingCocycle_blockRight :
    (S.blockRight h).twistingCocycle (fun x y ↦ q (.inr x) (.inr y))
        (fun x z y ↦ hq (.inr x) (.inr z) (.inr y)) =
      (S.twistingCocycle q hq).blockRight (S.twistingCocycle_m_inr_inl h hq) :=
  TwistingCocycle.ext fun x y ↦ by simp

/-- The continuation cocycle of push-forwards of the off-diagonal block has the entries of the
off-diagonal block of the twisting cocycle of push-forwards. -/
theorem continuationCocycle_blockContinuation_ν (x : P) (y : Q) :
    ((S.blockContinuation h).continuationCocycle (fun x y ↦ q (.inl x) (.inr y))
        (fun x z y ↦ hq (.inl x) (.inl z) (.inl y)) (fun x z y ↦ hq (.inr x) (.inr z) (.inr y))
        (fun x z y ↦ hq (.inl x) (.inl z) (.inr y))
        (fun x z y ↦ hq (.inl x) (.inr z) (.inr y))).ν x y =
      ((S.twistingCocycle q hq).blockContinuation (S.twistingCocycle_m_inr_inl h hq)).ν x y := by
  simp [map_zsmul_unit]

end Evaluation

end TwistingChainSystem

end TauCeti
