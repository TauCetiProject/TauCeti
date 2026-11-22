/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.BlockDiagonal
public import TauCeti.LinearAlgebra.Matrix.Block
public import TauCeti.LinearAlgebra.Matrix.LDU
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.SuccPred.Nat

/-!
# Block upper-unitriangular groups and their adjacent-trace characters

Let `ι` be a finite linearly ordered type of blocks and `n` a finite type of positions inside a
block. A matrix indexed by `n × ι` (block index second, as for `Matrix.blockDiagonal`) is *block
upper-unitriangular* (`Matrix.BlockUnitriangular` for the ranking `Prod.snd`) when its blocks
below the block diagonal vanish and its diagonal blocks are the identity. For `ι = Fin k` and
`n = Fin c` these matrices form the unipotent radical `U_(c^k)` of the standard parabolic subgroup
of `GL_(kc)` whose Levi factor is `GL_c × ⋯ × GL_c` (`k` factors).

The sum `Matrix.adjacentBlockTrace` of the traces of the blocks just above the block diagonal is
additive on this group: one block above the diagonal, a product of two block upper-unitriangular
matrices only sees the identity diagonal blocks of its factors, so its adjacent blocks are the sums
of theirs. Composing with an additive character `ψ` of the coefficient ring gives the character

`ψ_(k,c)(u) = ψ (∑ᵢ tr u_(i,i+1))`

of `U_(c^k)`, whose functionals define the `(k,c)` models (generalized Whittaker models attached
to the rectangular nilpotent orbit `(k^c)`) of representations of `GL_(kc)`, which are the inputs
of the generalized doubling method. For `c = 1` it is the usual nondegenerate Whittaker character
of the upper-unitriangular group, and for `k = 1` it is trivial.

The block-diagonal Levi subgroup normalizes the group; a tuple `(gᵢ)` conjugates the block
`u_(i,j)` to `gᵢ u_(i,j) gⱼ⁻¹`. When `ψ` is primitive, for instance any nontrivial additive
character of a field, a tuple fixes `ψ_(k,c)` exactly when all its blocks agree: the stabilizer of
the character in the Levi subgroup is the diagonal copy of `GL_c`.

## Main declarations

* `Matrix.adjacentBlockTrace`: the sum of the traces of the blocks just above the diagonal.
* `TauCeti.blockUpperUnitriangularGroup`: the subgroup `U_(c^k)` of `GL (n × ι) R`.
* `TauCeti.BlockUpperUnitriangularGroup.submatrix_coe_mul_of_covBy`: adjacent blocks of a product
  are the sums of the adjacent blocks of the factors.
* `TauCeti.BlockUpperUnitriangularGroup.adjacentTraceChar`: the character `ψ_(k,c)`.
* `TauCeti.BlockUpperUnitriangularGroup.blockDiagonalConj`: the conjugation action of the Levi
  subgroup on `U_(c^k)`.
* `TauCeti.BlockUpperUnitriangularGroup.adjacentTraceChar_comp_blockDiagonalConj_eq_iff`: a Levi
  tuple fixes `ψ_(k,c)` exactly when all its blocks agree.

## References

* Y. Cai, S. Friedberg, E. Kaplan, *Doubling constructions: local and global theory, with an
  application to global functoriality for non-generic cuspidal representations*,
  arXiv:1802.02637, §3.1.
* Y. Cai, S. Friedberg, D. Gourevitch, E. Kaplan, *The generalized doubling method: (k,c)
  models*, Proc. Amer. Math. Soc. 151 (2023), §2.1.
-/

public section

open Matrix

namespace Matrix

variable {n ι R : Type*} [Fintype n] [Fintype ι] [LinearOrder ι]

section AddCommMonoid

variable [AddCommMonoid R]

/-- The sum of the traces of the square blocks just above the block diagonal of a matrix indexed
by `n × ι`: the block in block row `i` and block column `j` contributes when `j` covers `i`. -/
def adjacentBlockTrace (X : Matrix (n × ι) (n × ι) R) : R :=
  ∑ i, ∑ j, if i ⋖ j then (X.submatrix (·, i) (·, j)).trace else 0

theorem adjacentBlockTrace_def (X : Matrix (n × ι) (n × ι) R) :
    adjacentBlockTrace X = ∑ i, ∑ j, if i ⋖ j then (X.submatrix (·, i) (·, j)).trace else 0 :=
  (rfl)

@[simp]
theorem adjacentBlockTrace_zero : adjacentBlockTrace (0 : Matrix (n × ι) (n × ι) R) = 0 := by
  simp [adjacentBlockTrace_def]

@[simp]
theorem adjacentBlockTrace_add (X Y : Matrix (n × ι) (n × ι) R) :
    adjacentBlockTrace (X + Y) = adjacentBlockTrace X + adjacentBlockTrace Y := by
  simp only [adjacentBlockTrace_def, ← Finset.sum_add_distrib, ← ite_add_zero]
  simp [submatrix_add, trace_add]

@[simp]
theorem adjacentBlockTrace_one [DecidableEq n] [One R] :
    adjacentBlockTrace (1 : Matrix (n × ι) (n × ι) R) = 0 :=
  Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
    split_ifs with h
    · simp [trace, h.ne]
    · rfl

/-- With a single block the adjacent block trace vanishes. -/
theorem adjacentBlockTrace_of_subsingleton [Subsingleton ι] (X : Matrix (n × ι) (n × ι) R) :
    adjacentBlockTrace X = 0 :=
  Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
    ite_eq_right_iff.mpr fun h => absurd (Subsingleton.elim i j) h.ne

/-- With blocks of size one the adjacent block trace is the sum of the entries just above the
diagonal, the argument of the usual nondegenerate Whittaker character. -/
theorem adjacentBlockTrace_of_unique [Unique n] (X : Matrix (n × ι) (n × ι) R) :
    adjacentBlockTrace X = ∑ i, ∑ j, if i ⋖ j then X (default, i) (default, j) else 0 := by
  simp [adjacentBlockTrace_def, trace]

/-- For the blocks `Fin (k + 1)`, the adjacent block trace is `∑ᵢ tr X_(i,i+1)`. -/
theorem adjacentBlockTrace_fin {k : ℕ} (X : Matrix (n × Fin (k + 1)) (n × Fin (k + 1)) R) :
    adjacentBlockTrace X = ∑ i : Fin k, (X.submatrix (·, i.castSucc) (·, i.succ)).trace := by
  rw [adjacentBlockTrace_def, Fin.sum_univ_castSucc]
  have hlast : ∀ j : Fin (k + 1), ¬Fin.last k ⋖ j := fun j h => (Fin.le_last j).not_gt h.lt
  have hsucc (i : Fin k) (j : Fin (k + 1)) : i.castSucc ⋖ j ↔ i.succ = j := by
    simp [Fin.ext_iff]
  simp [hlast, hsucc]

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup R]

@[simp]
theorem adjacentBlockTrace_neg (X : Matrix (n × ι) (n × ι) R) :
    adjacentBlockTrace (-X) = -adjacentBlockTrace X := by
  rw [eq_neg_iff_add_eq_zero, ← adjacentBlockTrace_add, neg_add_cancel, adjacentBlockTrace_zero]

@[simp]
theorem adjacentBlockTrace_sub (X Y : Matrix (n × ι) (n × ι) R) :
    adjacentBlockTrace (X - Y) = adjacentBlockTrace X - adjacentBlockTrace Y := by
  rw [sub_eq_add_neg, adjacentBlockTrace_add, adjacentBlockTrace_neg, ← sub_eq_add_neg]

end AddCommGroup

end Matrix

namespace TauCeti

variable (n ι R : Type*) [Fintype n] [DecidableEq n] [Fintype ι] [LinearOrder ι] [CommRing R]

/-- The block upper-unitriangular subgroup of `GL (n × ι) R`: invertible matrices that are block
unitriangular (`Matrix.BlockUnitriangular`) for the block index `Prod.snd`, so their blocks below
the diagonal vanish and their diagonal blocks are the identity. For `ι = Fin k` and `n = Fin c` it
is the unipotent radical `U_(c^k)` of the standard parabolic subgroup of `GL_(kc)` with `k`
diagonal blocks of size `c`. -/
def blockUpperUnitriangularGroup : Subgroup (GL (n × ι) R) where
  carrier := {g | (g : Matrix (n × ι) (n × ι) R).BlockUnitriangular Prod.snd}
  one_mem' := blockUnitriangular_one
  mul_mem' {g h} hg hh := by
    simpa only [Set.mem_ofPred_eq, Units.val_mul] using hg.mul hh
  inv_mem' {g} hg := by
    simpa only [Set.mem_ofPred_eq, coe_units_inv] using hg.inv

variable {n ι R}

@[simp]
theorem mem_blockUpperUnitriangularGroup_iff {g : GL (n × ι) R} :
    g ∈ blockUpperUnitriangularGroup n ι R ↔
      (g : Matrix (n × ι) (n × ι) R).BlockUnitriangular Prod.snd :=
  Iff.rfl

/-- A transvection whose off-diagonal entry lies in a strictly later block column than its row
belongs to the block upper-unitriangular group. -/
theorem transvection_mem_blockUpperUnitriangularGroup {p q : n × ι} (hpq : p.2 < q.2)
    (h : p ≠ q) (t : R) :
    GeneralLinearGroup.transvection p q h t ∈ blockUpperUnitriangularGroup n ι R := by
  rw [mem_blockUpperUnitriangularGroup_iff, blockUnitriangular_iff]
  refine ⟨by simpa using blockTriangular_transvection (b := Prod.snd) hpq.le t,
    fun x y hxy => ?_⟩
  have hxy' : ¬(p = x ∧ q = y) := by
    rintro ⟨rfl, rfl⟩
    exact hpq.ne hxy
  simp [transvection, hxy']

namespace BlockUpperUnitriangularGroup

theorem blockUnitriangular (u : blockUpperUnitriangularGroup n ι R) :
    ((u : GL (n × ι) R) : Matrix (n × ι) (n × ι) R).BlockUnitriangular Prod.snd :=
  u.2

/-- One block above the diagonal, a product of block upper-unitriangular matrices has the sum of
the blocks of its factors. -/
theorem submatrix_coe_mul_of_covBy (u v : blockUpperUnitriangularGroup n ι R) {i j : ι}
    (hij : i ⋖ j) :
    (((u * v : blockUpperUnitriangularGroup n ι R) : GL (n × ι) R) :
        Matrix (n × ι) (n × ι) R).submatrix (·, i) (·, j) =
      ((u : GL (n × ι) R) : Matrix (n × ι) (n × ι) R).submatrix (·, i) (·, j) +
        ((v : GL (n × ι) R) : Matrix (n × ι) (n × ι) R).submatrix (·, i) (·, j) := by
  ext a b
  simp [(blockUnitriangular u).mul_apply_of_covBy (blockUnitriangular v)
    (i := (a, i)) (j := (b, j)) hij]

/-- The adjacent block trace is additive on block upper-unitriangular matrices. -/
theorem adjacentBlockTrace_coe_mul (u v : blockUpperUnitriangularGroup n ι R) :
    adjacentBlockTrace (((u * v : blockUpperUnitriangularGroup n ι R) : GL (n × ι) R) :
        Matrix (n × ι) (n × ι) R) =
      adjacentBlockTrace ((u : GL (n × ι) R) : Matrix (n × ι) (n × ι) R) +
        adjacentBlockTrace ((v : GL (n × ι) R) : Matrix (n × ι) (n × ι) R) := by
  simp only [adjacentBlockTrace_def, ← Finset.sum_add_distrib, ← ite_add_zero]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · rw [submatrix_coe_mul_of_covBy u v hij, trace_add]
  · rfl

/-- The adjacent block trace as a homomorphism to the additive group of the coefficients. -/
def adjacentTraceHom : blockUpperUnitriangularGroup n ι R →* Multiplicative R where
  toFun u := .ofAdd (adjacentBlockTrace ((u : GL (n × ι) R) : Matrix (n × ι) (n × ι) R))
  map_one' := by simp
  map_mul' u v := by rw [adjacentBlockTrace_coe_mul, ofAdd_add]

@[simp]
theorem adjacentTraceHom_apply (u : blockUpperUnitriangularGroup n ι R) :
    adjacentTraceHom u =
      .ofAdd (adjacentBlockTrace ((u : GL (n × ι) R) : Matrix (n × ι) (n × ι) R)) :=
  (rfl)

variable {M : Type*} [Monoid M]

/-- The character `u ↦ ψ (∑ᵢ tr u_(i,i+1))` of the block upper-unitriangular group attached to
an additive character `ψ`. For `ι = Fin k`, `n = Fin c` and a nontrivial `ψ` this is the character
`ψ_(k,c)` of `U_(c^k)` defining `(k,c)` functionals. -/
def adjacentTraceChar (ψ : AddChar R M) : blockUpperUnitriangularGroup n ι R →* M :=
  ψ.toMonoidHom.comp adjacentTraceHom

@[simp]
theorem adjacentTraceChar_apply (ψ : AddChar R M) (u : blockUpperUnitriangularGroup n ι R) :
    adjacentTraceChar ψ u =
      ψ (adjacentBlockTrace ((u : GL (n × ι) R) : Matrix (n × ι) (n × ι) R)) :=
  (rfl)

/-- With a single block the character is trivial. -/
theorem adjacentTraceChar_of_subsingleton [Subsingleton ι] (ψ : AddChar R M) :
    adjacentTraceChar (n := n) (ι := ι) ψ = 1 := by
  ext u
  simp [adjacentBlockTrace_of_subsingleton]

end BlockUpperUnitriangularGroup

/-- Conjugation by a Levi element preserves the block upper-unitriangular group. -/
theorem blockDiagonalGL_mul_mul_inv_mem (g : ι → GL n R) {u : GL (n × ι) R}
    (hu : u ∈ blockUpperUnitriangularGroup n ι R) :
    blockDiagonalGL n ι R g * u * (blockDiagonalGL n ι R g)⁻¹ ∈
      blockUpperUnitriangularGroup n ι R := by
  rw [mem_blockUpperUnitriangularGroup_iff] at hu ⊢
  refine blockUnitriangular_iff.mpr ⟨?_, fun x y hxy => ?_⟩
  · simp only [Units.val_mul, coe_blockDiagonalGL, coe_blockDiagonalGL_inv]
    exact ((blockTriangular_blockDiagonal _).mul hu.blockTriangular).mul
      (blockTriangular_blockDiagonal _)
  · obtain ⟨a, i⟩ := x
    obtain ⟨b, i'⟩ := y
    obtain rfl : i = i' := hxy
    have hu1 : (u : Matrix (n × ι) (n × ι) R).submatrix (·, i) (·, i) = 1 := by
      ext c d
      simpa [Matrix.one_apply] using hu.apply_of_eq (i := (c, i)) (j := (d, i)) rfl
    have h := congr_fun₂ (submatrix_blockDiagonalGL_mul_mul_inv g
      (u : Matrix (n × ι) (n × ι) R) i i) a b
    rw [hu1, Matrix.mul_one, Units.mul_inv, submatrix_apply] at h
    rw [Units.val_mul, Units.val_mul, h]
    simp [Matrix.one_apply]

theorem blockDiagonalGL_mem_normalizer (g : ι → GL n R) :
    blockDiagonalGL n ι R g ∈
      Subgroup.normalizer (blockUpperUnitriangularGroup n ι R : Set (GL (n × ι) R)) := by
  refine Subgroup.mem_normalizer_iff.mpr fun u =>
    ⟨blockDiagonalGL_mul_mul_inv_mem g, fun hu => ?_⟩
  have := blockDiagonalGL_mul_mul_inv_mem g⁻¹ hu
  simpa only [map_inv, inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using
    this

namespace BlockUpperUnitriangularGroup

/-- The conjugation action of the block-diagonal Levi subgroup on the block upper-unitriangular
group. -/
def blockDiagonalConj : (ι → GL n R) →* MulAut (blockUpperUnitriangularGroup n ι R) :=
  (blockUpperUnitriangularGroup n ι R).normalizerMonoidHom.comp
    ((blockDiagonalGL n ι R).codRestrict _ blockDiagonalGL_mem_normalizer)

@[simp]
theorem coe_blockDiagonalConj_apply (g : ι → GL n R) (u : blockUpperUnitriangularGroup n ι R) :
    ((blockDiagonalConj g u : blockUpperUnitriangularGroup n ι R) : GL (n × ι) R) =
      blockDiagonalGL n ι R g * u * (blockDiagonalGL n ι R g)⁻¹ := by
  simp [blockDiagonalConj]

/-- The adjacent block trace of a Levi conjugate: the block `u_(i,j)` is replaced by
`gᵢ u_(i,j) gⱼ⁻¹`, which has the trace of `gⱼ⁻¹ gᵢ u_(i,j)`. -/
theorem adjacentBlockTrace_blockDiagonalConj (g : ι → GL n R)
    (u : blockUpperUnitriangularGroup n ι R) :
    adjacentBlockTrace
        (((blockDiagonalConj g u : blockUpperUnitriangularGroup n ι R) : GL (n × ι) R) :
          Matrix (n × ι) (n × ι) R) =
      ∑ i, ∑ j, if i ⋖ j then
        (((g j)⁻¹ * g i : GL n R) * ((u : GL (n × ι) R) : Matrix (n × ι) (n × ι) R).submatrix
          (·, i) (·, j)).trace else 0 := by
  simp only [adjacentBlockTrace_def, coe_blockDiagonalConj_apply, Units.val_mul,
    submatrix_blockDiagonalGL_mul_mul_inv]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [trace_mul_cycle]

variable {M : Type*}

/-- A constant Levi tuple, that is an element of the diagonal `GL n R`, fixes the adjacent-trace
character. -/
theorem adjacentTraceChar_comp_blockDiagonalConj_const [Monoid M] (ψ : AddChar R M)
    (g : GL n R) :
    (adjacentTraceChar ψ).comp (blockDiagonalConj (ι := ι) fun _ => g).toMonoidHom =
      adjacentTraceChar ψ := by
  ext u
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    adjacentTraceChar_apply]
  rw [adjacentBlockTrace_blockDiagonalConj]
  simp [adjacentBlockTrace_def]

variable [CommMonoid M]

/-- Against coefficient matrices `B i' j'`, the blocks one step above the diagonal of the
transvection with entry `t` at `((b, i), (a, j))`, where `i ⋖ j`, only contribute at `(i, j)`. -/
private theorem sum_trace_mul_submatrix_transvection {i j : ι} (hij : i ⋖ j) (a b : n) (t : R)
    (B : ι → ι → Matrix n n R) :
    (∑ i', ∑ j', if i' ⋖ j' then (B i' j' *
        (transvection (b, i) (a, j) t : Matrix (n × ι) (n × ι) R).submatrix (·, i') (·, j')).trace
      else 0) =
      (B i j * single b a t).trace := by
  have hblock {i' j' : ι} (h' : i' ⋖ j') :
      (transvection (b, i) (a, j) t : Matrix (n × ι) (n × ι) R).submatrix (·, i') (·, j') =
        if i' = i ∧ j' = j then single b a t else 0 := by
    have hne' : i' ≠ j' := h'.ne
    by_cases hij' : i' = i ∧ j' = j
    · obtain ⟨rfl, rfl⟩ := hij'
      ext c d
      simp [transvection, Matrix.single_apply, hne']
    · ext c d
      simp only [hij', ↓reduceIte, transvection, submatrix_apply, Matrix.add_apply,
        Matrix.one_apply, Matrix.single_apply, Prod.mk.injEq, Matrix.zero_apply]
      grind
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp [hij, hblock hij]
  · intro j' _ hj'
    split_ifs with h'
    · simp [hblock h', hj']
    · rfl
  · simp
  · intro i' _ hi'
    refine Finset.sum_eq_zero fun j' _ => ?_
    split_ifs with h'
    · simp [hblock h', hi']
    · rfl
  · simp

/-- The blocks one step above the diagonal of the transvection with entry `t` at
`((b, i), (a, j))`, where `i ⋖ j`, have total trace `tr (single b a t)`: the case of
`sum_trace_mul_submatrix_transvection` with all coefficient matrices equal to `1`. -/
private theorem sum_trace_submatrix_transvection {i j : ι} (hij : i ⋖ j) (a b : n) (t : R) :
    (∑ i', ∑ j', if i' ⋖ j' then
        ((transvection (b, i) (a, j) t : Matrix (n × ι) (n × ι) R).submatrix (·, i') (·, j')).trace
      else 0) =
      (single b a t : Matrix n n R).trace := by
  simpa using sum_trace_mul_submatrix_transvection hij a b t fun _ _ => 1

/-- If a Levi tuple fixes the character attached to a primitive additive character, its blocks
agree along every cover `i ⋖ j`. -/
private theorem eq_of_covBy_of_adjacentTraceChar_comp_eq {ψ : AddChar R M} (hψ : ψ.IsPrimitive)
    {g : ι → GL n R}
    (h : (adjacentTraceChar ψ).comp (blockDiagonalConj g).toMonoidHom = adjacentTraceChar ψ)
    {i j : ι} (hij : i ⋖ j) : g i = g j := by
  rw [eq_comm, ← inv_mul_eq_one, Units.ext_iff, Units.val_one]
  ext a b
  -- Compare the character on the transvection with entry `t` at `((b, i), (a, j))` and on its
  -- conjugate: their adjacent block traces are `t • 1 a b` and `t • ((g j)⁻¹ * g i) a b`.
  have hpq : ((b, i) : n × ι) ≠ (a, j) := fun hpq => hij.ne (Prod.ext_iff.mp hpq).2
  refine AddChar.to_mulShift_inj_of_isPrimitive hψ (DFunLike.ext _ _ fun t => ?_)
  have hchar := DFunLike.congr_fun h
    ⟨_, transvection_mem_blockUpperUnitriangularGroup (p := (b, i)) (q := (a, j)) hij.lt hpq t⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, adjacentTraceChar_apply,
    adjacentBlockTrace_blockDiagonalConj] at hchar
  simp only [adjacentBlockTrace_def, GeneralLinearGroup.val_transvection] at hchar
  rw [sum_trace_mul_submatrix_transvection hij, sum_trace_submatrix_transvection hij,
    trace_mul_single, op_smul_eq_mul] at hchar
  rw [AddChar.mulShift_apply, AddChar.mulShift_apply, hchar]
  by_cases hab : b = a
  · subst hab
    simp
  · simp [trace_single_eq_of_ne (h := hab), Matrix.one_apply_ne (Ne.symm hab)]

/-- **Stabilizer of the adjacent-trace character.** For a primitive additive character `ψ`,
such as any nontrivial additive character of a field, a block-diagonal Levi tuple fixes the
character `u ↦ ψ (∑ᵢ tr u_(i,i+1))` under conjugation exactly when all its blocks agree. So the
stabilizer of `ψ_(k,c)` in `GL_c × ⋯ × GL_c` is the diagonal `GL_c`. -/
theorem adjacentTraceChar_comp_blockDiagonalConj_eq_iff {ψ : AddChar R M} (hψ : ψ.IsPrimitive)
    (g : ι → GL n R) :
    (adjacentTraceChar ψ).comp (blockDiagonalConj g).toMonoidHom = adjacentTraceChar ψ ↔
      ∀ i j, g i = g j := by
  constructor
  · intro h
    have hle {i j : ι} (hij : i ≤ j) : g i = g j := by
      let _ := Fintype.toLocallyFiniteOrder (α := ι)
      have hrt := le_iff_reflTransGen_covBy.mp hij
      clear hij
      induction hrt with
      | refl => rfl
      | tail _ hcov ih => exact ih.trans (eq_of_covBy_of_adjacentTraceChar_comp_eq hψ h hcov)
    intro i j
    rcases le_total i j with hij | hji
    · exact hle hij
    · exact (hle hji).symm
  · intro h
    obtain ⟨g₀, rfl⟩ : ∃ g₀, g = fun _ => g₀ := by
      rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
      · exact ⟨1, funext isEmptyElim⟩
      · exact ⟨g i₀, funext fun i => h i i₀⟩
    exact adjacentTraceChar_comp_blockDiagonalConj_const ψ g₀

end BlockUpperUnitriangularGroup

end TauCeti
