/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Continuation
import TauCeti.Algebra.Ring.NegOnePow

/-!
# Block-triangular twisting cocycles and continuation cocycles

Let `(P, ind)` and `(Q, indQ)` be finite graded sets of generators. Grade their disjoint union by
`ind x + 1` on `P` and `indQ y` on `Q`. A twisting cocycle `m` on `P ⊕ Q` which never goes from `Q`
back to `P`, `m (inr y) (inl x) = 0`, is block upper triangular:

`m = [[mP, μ], [0, mQ]]`.

Its diagonal blocks are twisting cocycles on `(P, ind)` and on `(Q, indQ)`
(`TauCeti.TwistingCocycle.blockLeft`, `TauCeti.TwistingCocycle.blockRight`): the shift of the
index of `P` by one does not change the differences of indices of `P`, which are all that the
twisting equation sees. The off-diagonal block, corrected by the sign `(-1) ^ ind x` of its row,
`ν x y = (-1) ^ ind x • μ x y`, is a continuation cocycle from `mP` to `mQ`
(`TauCeti.TwistingCocycle.blockContinuation`): the twisting equation of `m` at `(inl x, inr y)` is
the continuation equation of `ν` at `(x, y)`.

Conversely, every continuation cocycle `ν` from `mP` to `mQ` without entries strictly increasing
the index (automatic over a cohomologically nonpositive algebra,
`TauCeti.ContinuationCocycle.ν_eq_zero_of_lt_of_nonpos`) is the off-diagonal block of the
twisting cocycle `[[mP, (-1) ^ ind x • ν], [0, mQ]]` on `P ⊕ Q`
(`TauCeti.ContinuationCocycle.cone`), and the two constructions are inverse to each other
(`TauCeti.ContinuationCocycle.blockLeft_cone`, `TauCeti.ContinuationCocycle.blockRight_cone`,
`TauCeti.ContinuationCocycle.blockContinuation_cone_ν`,
`TauCeti.TwistingCocycle.cone_blockContinuation`). So continuation cocycles are the same thing as
block-triangular twisting cocycles on the disjoint union, with the index of the source shifted by
one.

This is how continuation maps arise in Morse theory. A homotopy from a Morse function `f₀` to a
Morse function `f₁` on `M` is realized by a field on `M × ℝ` whose time component is positive in
the slab `M × (0, 1)`; the critical points of the corresponding function on the slab are the points
`(p, 0)` for the critical points `p` of `f₀`, of index `ind p + 1`, and `(q, 1)` for those of `f₁`,
of index `ind q`, and no trajectory goes from the level `1` back to the level `0`. The twisting
cocycle of the slab is block upper triangular, its diagonal blocks are the cocycles of `f₀` and
`f₁`, and its off-diagonal block is the continuation cocycle from the one to the other. The
twisted complex of `ν.cone` is, as a graded module, the mapping cone of the continuation map of
`ν`; that identification is not made here.

## Main definitions

* `TauCeti.TwistingCocycle.blockLeft`, `TauCeti.TwistingCocycle.blockRight`: the diagonal blocks
  of a block-triangular twisting cocycle on `P ⊕ Q`.
* `TauCeti.TwistingCocycle.blockContinuation`: its off-diagonal block, as a continuation cocycle
  between the diagonal blocks.
* `TauCeti.ContinuationCocycle.cone`: the block-triangular twisting cocycle on `P ⊕ Q` of a
  continuation cocycle.

## Main results

* `TauCeti.TwistingCocycle.blockContinuation_ν_eq_zero_of_lt`: the off-diagonal block has no
  entries strictly increasing the index.
* `TauCeti.ContinuationCocycle.blockLeft_cone`, `TauCeti.ContinuationCocycle.blockRight_cone`,
  `TauCeti.ContinuationCocycle.blockContinuation_cone_ν`: the blocks of `ν.cone` are `mP`, `mQ`
  and `ν`.
* `TauCeti.TwistingCocycle.cone_blockContinuation`: a block-triangular twisting cocycle is the
  cone of its off-diagonal block.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 6.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4, Definitions 1.9 and 1.10.
-/

public section

namespace TauCeti

universe uR uA uP uQ

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} {d : A →ₗ[R] A}
  {P : Type uP} {Q : Type uQ} [Fintype P] [Fintype Q] {ind : P → ℤ} {indQ : Q → ℤ}

/-- The sign of a term `a * b` of the twisting equation on `P ⊕ Q` through a generator of `P`,
multiplied by the sign of the row, is the sign of the column of `b`. -/
private theorem negOnePow_smul_negOnePow_smul_mul_left (i j : ℤ) (a b : A) :
    i.negOnePow • (i + 1 - (j + 1)).negOnePow • (a * b) = a * j.negOnePow • b := by
  rw [mul_smul_comm, smul_smul, add_sub_add_right_eq_sub, Int.negOnePow_mul_negOnePow_sub]

/-- The sign of a term `a * b` of the twisting equation on `P ⊕ Q` through a generator of `Q`,
multiplied by the sign `(-1) ^ i` of the row, is the sign of the continuation equation applied to
`(-1) ^ i • a`. -/
private theorem negOnePow_smul_negOnePow_smul_mul_right (i j : ℤ) (a b : A) :
    i.negOnePow • (i + 1 - j).negOnePow • (a * b) =
      (i - j - 1).negOnePow • (i.negOnePow • a * b) := by
  rw [Int.negOnePow_add_one_sub, smul_mul_assoc, smul_comm]

/-- The sign of a term `a * (-1) ^ j • b` of the twisting equation of the cone through a generator
of `P` is the sign `(-1) ^ i` of its row. -/
private theorem negOnePow_smul_mul_negOnePow_smul (i j : ℤ) (a b : A) :
    (i + 1 - (j + 1)).negOnePow • (a * j.negOnePow • b) = i.negOnePow • (a * b) := by
  rw [← negOnePow_smul_negOnePow_smul_mul_left i j, smul_comm, Int.negOnePow_smul_negOnePow_smul]

/-- The sign of a term `(-1) ^ i • a * b` of the twisting equation of the cone through a generator
of `Q` is the sign `(-1) ^ i` of its row times the sign of the continuation equation. -/
private theorem negOnePow_smul_negOnePow_smul_mul (i j : ℤ) (a b : A) :
    (i + 1 - j).negOnePow • (i.negOnePow • a * b) =
      i.negOnePow • (i - j - 1).negOnePow • (a * b) := by
  rw [Int.negOnePow_add_one_sub, smul_mul_assoc, smul_comm]

omit [Fintype P] [Fintype Q] in
/-- For the grading of `P ⊕ Q` by `ind x + 1` on `P` and `indQ y` on `Q`, an entry of a twisting
cocycle from `inl x` to `inr y` has the degree `indQ y - ind x` of an entry of a continuation
cocycle. -/
theorem sumElim_inr_sub_sumElim_inl_add_one (x : P) (y : Q) :
    Sum.elim (fun x ↦ ind x + 1) indQ (.inr y) - Sum.elim (fun x ↦ ind x + 1) indQ (.inl x) + 1 =
      indQ y - ind x := by
  rw [Sum.elim_inl, Sum.elim_inr, sub_add_eq_sub_sub, sub_add_cancel]

/-! ### The blocks of a block-triangular twisting cocycle -/

namespace TwistingCocycle

variable (m : TwistingCocycle 𝒜 d (P ⊕ Q) (Sum.elim (fun x ↦ ind x + 1) indQ))
  (h : ∀ x y, m.m (.inr y) (.inl x) = 0)

/-- The **upper-left block** of a twisting cocycle on `P ⊕ Q` which never goes from `Q` to `P`:
its entries between generators of `P`, a twisting cocycle on `(P, ind)`. -/
def blockLeft : TwistingCocycle 𝒜 d P ind where
  m x y := m.m (.inl x) (.inl y)
  mem_graded x y := by
    have := m.mem_graded (.inl x) (.inl y)
    rwa [Sum.elim_inl, Sum.elim_inl, add_sub_add_right_eq_sub] at this
  twisting x y := by
    rw [m.twisting, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, h, mul_zero, smul_zero, Finset.sum_const_zero,
      add_zero, add_sub_add_right_eq_sub]
  one_sided x y hxy := m.one_sided _ _ (by simpa using hxy)

@[simp]
theorem blockLeft_m (x y : P) : (m.blockLeft h).m x y = m.m (.inl x) (.inl y) :=
  (rfl)

/-- The **lower-right block** of a twisting cocycle on `P ⊕ Q` which never goes from `Q` to `P`:
its entries between generators of `Q`, a twisting cocycle on `(Q, indQ)`. -/
def blockRight : TwistingCocycle 𝒜 d Q indQ where
  m x y := m.m (.inr x) (.inr y)
  mem_graded x y := by simpa using m.mem_graded (.inr x) (.inr y)
  twisting x y := by
    rw [m.twisting, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, h, zero_mul, smul_zero, Finset.sum_const_zero,
      zero_add]
  one_sided x y hxy := m.one_sided _ _ (by simpa using hxy)

@[simp]
theorem blockRight_m (x y : Q) : (m.blockRight h).m x y = m.m (.inr x) (.inr y) :=
  (rfl)

/-- The **off-diagonal block** of a twisting cocycle on `P ⊕ Q` which never goes from `Q` to `P`,
with the sign `(-1) ^ ind x` of its row: `ν x y = (-1) ^ ind x • m (inl x) (inr y)`, a
continuation cocycle from the upper-left block to the lower-right block. -/
def blockContinuation : ContinuationCocycle (m.blockLeft h) (m.blockRight h) where
  ν x y := (ind x).negOnePow • m.m (.inl x) (.inr y)
  mem_graded x y := by
    rw [← sumElim_inr_sub_sumElim_inl_add_one]
    exact Submodule.smul_of_tower_mem _ _ (m.mem_graded (.inl x) (.inr y))
  continuation x y := by
    rw [map_zsmul_unit, m.twisting, Fintype.sum_sum_type, smul_add, Finset.smul_sum,
      Finset.smul_sum]
    -- The terms through `P` first: the pattern of the terms through `Q` also matches them.
    simp only [Sum.elim_inl, Sum.elim_inr, blockLeft_m, blockRight_m,
      negOnePow_smul_negOnePow_smul_mul_left]
    simp only [negOnePow_smul_negOnePow_smul_mul_right]

@[simp]
theorem blockContinuation_ν (x : P) (y : Q) :
    (m.blockContinuation h).ν x y = (ind x).negOnePow • m.m (.inl x) (.inr y) :=
  (rfl)

/-- The off-diagonal block has no entries strictly increasing the index: `m (inl x) (inr y)`
vanishes when `ind x + 1 ≤ indQ y`. -/
theorem blockContinuation_ν_eq_zero_of_lt {x : P} {y : Q} (hxy : ind x < indQ y) :
    (m.blockContinuation h).ν x y = 0 := by
  rw [blockContinuation_ν, m.one_sided _ _ (by simp only [Sum.elim_inl, Sum.elim_inr]; omega),
    smul_zero]

end TwistingCocycle

/-! ### The block-triangular twisting cocycle of a continuation cocycle -/

namespace ContinuationCocycle

variable {mP : TwistingCocycle 𝒜 d P ind} {mQ : TwistingCocycle 𝒜 d Q indQ}
  (ν : ContinuationCocycle mP mQ) (hν : ∀ x y, ind x < indQ y → ν.ν x y = 0)

/-- The twisting equation of the block matrix `[[mP, (-1) ^ ind x • ν], [0, mQ]]` at
`(inl x, inr y)`: the continuation equation of `ν`, multiplied by the sign of `x`. -/
private theorem twisting_cone_inl_inr (x : P) (y : Q) :
    d ((ind x).negOnePow • ν.ν x y) =
      ∑ z, (ind x + 1 - (ind z + 1)).negOnePow • (mP.m x z * (ind z).negOnePow • ν.ν z y) +
        ∑ z, (ind x + 1 - indQ z).negOnePow • ((ind x).negOnePow • ν.ν x z * mQ.m z y) := by
  rw [map_zsmul_unit, ν.continuation, smul_add, Finset.smul_sum, Finset.smul_sum]
  simp only [negOnePow_smul_mul_negOnePow_smul, negOnePow_smul_negOnePow_smul_mul]

/-- The **block-triangular twisting cocycle of a continuation cocycle** `ν` from `mP` to `mQ`
without entries strictly increasing the index: the matrix `[[mP, (-1) ^ ind x • ν], [0, mQ]]` on
`P ⊕ Q`, graded by `ind x + 1` on `P` and `indQ y` on `Q`. -/
def cone : TwistingCocycle 𝒜 d (P ⊕ Q) (Sum.elim (fun x ↦ ind x + 1) indQ) where
  m
    | .inl x, .inl y => mP.m x y
    | .inl x, .inr y => (ind x).negOnePow • ν.ν x y
    | .inr _, .inl _ => 0
    | .inr x, .inr y => mQ.m x y
  mem_graded
    | .inl x, .inl y => by simpa using mP.mem_graded x y
    | .inl x, .inr y => by
      rw [sumElim_inr_sub_sumElim_inl_add_one]
      exact Submodule.smul_of_tower_mem _ _ (ν.mem_graded x y)
    | .inr _, .inl _ => zero_mem _
    | .inr x, .inr y => by simpa using mQ.mem_graded x y
  twisting
    | .inl x, .inl y => by simp [Fintype.sum_sum_type, mP.twisting]
    | .inl x, .inr y => by
      simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] using
        ν.twisting_cone_inl_inr x y
    | .inr x, .inl y => by simp [Fintype.sum_sum_type]
    | .inr x, .inr y => by simp [Fintype.sum_sum_type, mQ.twisting]
  one_sided
    | .inl x, .inl y, hxy => mP.one_sided x y (by simpa using hxy)
    | .inl x, .inr y, hxy => by
      simp only [Sum.elim_inl, Sum.elim_inr] at hxy
      simp only [hν x y (by omega), smul_zero]
    | .inr _, .inl _, _ => rfl
    | .inr x, .inr y, hxy => mQ.one_sided x y (by simpa using hxy)

@[simp]
theorem cone_m_inl_inl (x y : P) : (ν.cone hν).m (.inl x) (.inl y) = mP.m x y :=
  (rfl)

@[simp]
theorem cone_m_inl_inr (x : P) (y : Q) :
    (ν.cone hν).m (.inl x) (.inr y) = (ind x).negOnePow • ν.ν x y :=
  (rfl)

/-- The cone of a continuation cocycle never goes from `Q` to `P`. -/
@[simp]
theorem cone_m_inr_inl (x : P) (y : Q) : (ν.cone hν).m (.inr y) (.inl x) = 0 :=
  (rfl)

@[simp]
theorem cone_m_inr_inr (x y : Q) : (ν.cone hν).m (.inr x) (.inr y) = mQ.m x y :=
  (rfl)

/-- The upper-left block of the cone of `ν : mP → mQ` is `mP`. -/
@[simp]
theorem blockLeft_cone : (ν.cone hν).blockLeft (ν.cone_m_inr_inl hν) = mP :=
  TwistingCocycle.ext fun x y ↦ by simp

/-- The lower-right block of the cone of `ν : mP → mQ` is `mQ`. -/
@[simp]
theorem blockRight_cone : (ν.cone hν).blockRight (ν.cone_m_inr_inl hν) = mQ :=
  TwistingCocycle.ext fun x y ↦ by simp

/-- The off-diagonal block of the cone of `ν` has the entries of `ν`. -/
theorem blockContinuation_cone_ν (x : P) (y : Q) :
    ((ν.cone hν).blockContinuation (ν.cone_m_inr_inl hν)).ν x y = ν.ν x y := by
  simp

end ContinuationCocycle

namespace TwistingCocycle

variable (m : TwistingCocycle 𝒜 d (P ⊕ Q) (Sum.elim (fun x ↦ ind x + 1) indQ))
  (h : ∀ x y, m.m (.inr y) (.inl x) = 0)

/-- A twisting cocycle on `P ⊕ Q` which never goes from `Q` to `P` is the cone of its
off-diagonal block. -/
@[simp]
theorem cone_blockContinuation :
    (m.blockContinuation h).cone (fun _ _ ↦ m.blockContinuation_ν_eq_zero_of_lt h) = m :=
  ext fun
    | .inl x, .inl y => by simp
    | .inl x, .inr y => by simp
    | .inr x, .inl y => by simp [h]
    | .inr x, .inr y => by simp

end TwistingCocycle

end TauCeti
