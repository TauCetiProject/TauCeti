/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import TauCeti.LinearAlgebra.Matrix.HermiteNormalForm.Valuation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Logic.Equiv.Fintype
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Divided splittings and the algebraic glued-lattice construction

This file isolates the matrix content of §3.2(a)--(d) of
`ShortGRH/NormsOfThetaLiftsAndExchangeIdentities`. A divided lattice is represented by its
reduced inverse `M` and a reduced matrix `C` with `C * M = ϖ • 1`. This is precisely the
residue-ring shadow used by the matrix arguments; no adelic unitarity is asserted.

Over a pre-valuation ring, the existing block-triangular decomposition supplies `StackNormalForm`
and `ColumnClearing`. The construction also needs products of `ϖ`-annihilators to vanish.
That condition is recorded by `IsSquareZeroParameter`; square-zero alone is insufficient.

## Main results

* `TauCeti.ThetaLift.DividedSplitting.exists_isGlued`: every matrix has a glued reduced inverse
  over a pre-valuation ring.
* `TauCeti.ThetaLift.DividedSplitting.IsGlued.indicator_eq_sum`: the glued indicator is the sum of
  the block-normalised indicators over the congruence group.

## References

The statements and construction follow [ShortProof](https://github.com/lsernau/grh-lean),
`lsernau/grh-lean` at commit `72fead102f663d5c7a407964a13dc0cf9d977207`, file
`grh/src/New/OneLift/ComparisonOperator/GluedLattices.lean`. They are adapted here to the
algebraic residue-ring shadow of a divided lattice.
The normal forms use `Matrix.exists_eq_submatrix_mul_blockTriangular_of_preValuationRing`
and `Matrix.exists_mul_gl_apply_eq_zero_off_range_of_preValuationRing`.
-/

public noncomputable section

open Matrix Finset
open scoped Matrix

namespace TauCeti.ThetaLift

/-- The index data of a divided splitting. -/
structure DividedSplitting (r n N m a : Type*) (z : r ↪ m) where
  /-- The identification of the split index set with the ambient index set. -/
  epsilon : N ⊕ m ≃ n
  /-- The fixed directions in the first summand. -/
  fixed : r ↪ N
  /-- The divided directions in the first summand. -/
  divided : a ↪ N

namespace DividedSplitting

variable {R : Type*} [CommRing R]
variable {r n N m a : Type*} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n]
  [Fintype N] [DecidableEq N] [Fintype m] [DecidableEq m] [Fintype a] [DecidableEq a]
variable {z : r ↪ m} (V : DividedSplitting r n N m a z)

/-- The ambient inclusion selected by the fixed directions. -/
def incl : r → n := V.epsilon ∘ Sum.inl ∘ V.fixed

/-- The equations on the first summand: `s`, followed by the identity modulo `ϖ`. -/
def stack (_V : DividedSplitting r n N m a z) (varpi : R) (s : Matrix a N R) :
    Matrix (a ⊕ N) N R :=
  fromRows s (varpi • (1 : Matrix N N R))

/-- Block normalisation of an `n × r` matrix. -/
def IsBlockNormalised (varpi : R) (s : Matrix a N R) (x : Matrix n r R) : Prop :=
  x.submatrix (V.epsilon ∘ Sum.inr) id = (1 : Matrix m m R).submatrix id z ∧
    V.stack varpi s * x.submatrix (V.epsilon ∘ Sum.inl) id =
      V.stack varpi s * (1 : Matrix N N R).submatrix id V.fixed

/-- The principal congruence group defined by `Y ≡ 1 (mod ϖ)`. -/
def congruenceGroup (_V : DividedSplitting r n N m a z) (varpi : R) : Subgroup (GL r R) :=
  MulAction.stabilizer (GL r R) (varpi • (1 : Matrix r r R))

omit [Fintype n] [Fintype N] [Fintype m] [Fintype a]
  [DecidableEq n] [DecidableEq N] [DecidableEq m] [DecidableEq a] in
/-- Membership in the congruence group is the scaled matrix equation. -/
theorem mem_congruenceGroup_iff (varpi : R) (Y : GL r R) :
    Y ∈ V.congruenceGroup varpi ↔ varpi • (Y : Matrix r r R) = varpi • 1 := by
  simp [congruenceGroup, MulAction.mem_stabilizer_iff, Units.smul_def]

/-- The algebraic residue-ring shadow of a divided lattice. -/
structure DividedLattice (R : Type*) [CommRing R] (n : Type*) [Fintype n] [DecidableEq n]
    (varpi : R) where
  /-- The reduced inverse. -/
  reducedInverse : Matrix n n R
  /-- A reduced matrix witnessing the divided-lattice left-inverse identity. -/
  reducedAdjoint : Matrix n n R
  /-- The divided-lattice identity after reduction. -/
  reducedAdjoint_mul : reducedAdjoint * reducedInverse = varpi • 1

/-- The three conditions for a reduced inverse to be glued for `s`. -/
structure IsGlued (varpi : R) (s : Matrix a N R) (L : DividedLattice R n varpi) : Prop where
  /-- A solution of the glued equation has a unique block normaliser. -/
  existsUnique (x : Matrix n r R)
    (hx : L.reducedInverse * x = varpi • (1 : Matrix n n R).submatrix id V.incl) :
    ∃! Y : V.congruenceGroup varpi, V.IsBlockNormalised varpi s
      (x * ((Y : GL r R) : Matrix r r R))
  /-- Every block-normalised translate solves the glued equation. -/
  mul_eq_of_isBlockNormalised (x : Matrix n r R) (Y : V.congruenceGroup varpi)
    (hY : V.IsBlockNormalised varpi s (x * ((Y : GL r R) : Matrix r r R))) :
    L.reducedInverse * x = varpi • (1 : Matrix n n R).submatrix id V.incl
  /-- Outside the divided columns, the corrected first-summand columns vanish modulo `ϖ`. -/
  exists_cols_eq_zero : ∃ K : GL N R, ∀ i : n, ∀ j : N, j ∉ Set.range V.divided →
    varpi * (L.reducedInverse.submatrix id (V.epsilon ∘ Sum.inl) *
      (K : Matrix N N R)) i j = 0

/-- Products of two `ϖ`-annihilators vanish, and `ϖ` itself has square zero. -/
structure IsSquareZeroParameter (varpi : R) : Prop where
  /-- The square-zero identity. -/
  sq_zero : varpi * varpi = 0
  /-- The annihilator ideal has square zero (a weakening of `ann ϖ = (ϖ)`). -/
  mul_eq_zero {x y : R} : varpi * x = 0 → varpi * y = 0 → x * y = 0

/-- The Hermite-divisor data required for the stacked matrix. -/
structure StackNormalForm (V : DividedSplitting r n N m a z) (varpi : R)
    (s : Matrix a N R) where
  /-- The complementary divisor. -/
  B : Matrix N N R
  /-- The Hermite divisor. -/
  D : Matrix N N R
  /-- A left-sample matrix expressing the stacked rows in terms of `D`. -/
  P : Matrix (a ⊕ N) N R
  /-- A left-sample matrix expressing `D` in terms of the stacked rows. -/
  Q : Matrix N (a ⊕ N) R
  /-- The divisor identity. -/
  mul_D : B * D = varpi • 1
  /-- The first row-equivalence. -/
  stack_eq : V.stack varpi s = P * D
  /-- The second row-equivalence, oriented toward the normal form. -/
  D_eq : Q * V.stack varpi s = D

/-- An invertible column operation clearing `s` outside the divided directions. -/
structure ColumnClearing (V : DividedSplitting r n N m a z) (s : Matrix a N R) where
  /-- The clearing operation. -/
  K : GL N R
  /-- All non-divided columns vanish after clearing. -/
  cleared : ∀ i : a, ∀ j : N, j ∉ Set.range V.divided →
    (s * (K : Matrix N N R)) i j = 0

open Classical in
/-- The lower diagonal used by the glued reduced inverse. -/
def lowerDiagonal (varpi : R) (z : r ↪ m) : Matrix m m R :=
  Matrix.diagonal fun i ↦ if i ∈ Set.range z then varpi else 1

open Classical in
/-- The lower diagonal used by the reduced adjoint. -/
def upperDiagonal (varpi : R) (z : r ↪ m) : Matrix m m R :=
  Matrix.diagonal fun i ↦ if i ∈ Set.range z then 1 else varpi

/-- The explicit block matrix giving the glued reduced inverse in split coordinates. -/
def glueMatrix (varpi : R) (z : r ↪ m) (fix : r ↪ N) (D : Matrix N N R) :
    Matrix (N ⊕ m) (N ⊕ m) R :=
  Matrix.fromBlocks D (-D.submatrix id fix * (1 : Matrix m m R).submatrix z id) 0
    (lowerDiagonal varpi z)

/-- The explicit reduced adjoint of `glueMatrix`. -/
def glueAdjoint (varpi : R) (z : r ↪ m) (fix : r ↪ N) (B : Matrix N N R) :
    Matrix (N ⊕ m) (N ⊕ m) R :=
  Matrix.fromBlocks B ((1 : Matrix N N R).submatrix id fix * (1 : Matrix m m R).submatrix z id) 0
    (upperDiagonal varpi z)

omit [Fintype r] [Fintype n] [Fintype m] [DecidableEq r] [DecidableEq n]
  [DecidableEq m] [DecidableEq a] in
/-- Row-equivalence supplied by a stacked normal form. -/
theorem StackNormalForm.mul_eq_mul_iff {varpi : R} {s : Matrix a N R}
    (F : StackNormalForm V varpi s) (X Y : Matrix N r R) :
    V.stack varpi s * X = V.stack varpi s * Y ↔ F.D * X = F.D * Y := by
  constructor
  · intro h
    rw [← F.D_eq, Matrix.mul_assoc, h, Matrix.mul_assoc]
  · intro h
    rw [F.stack_eq, Matrix.mul_assoc, h, Matrix.mul_assoc]

omit [Fintype n] [Fintype a] [DecidableEq r] [DecidableEq n] [DecidableEq a] in
/-- The explicit reduced adjoint satisfies the divided-lattice identity. -/
theorem glueAdjoint_mul_glueMatrix {varpi : R} {B D : Matrix N N R}
    (hBD : B * D = varpi • 1) :
    glueAdjoint varpi z V.fixed B * glueMatrix varpi z V.fixed D = varpi • 1 := by
  classical
  have h_diag :
      (1 : Matrix N N R).submatrix id V.fixed * (lowerDiagonal varpi z).submatrix z id =
        varpi • ((1 : Matrix N N R).submatrix id V.fixed * (1 : Matrix m m R).submatrix z id) := by
    rw [← Matrix.mul_smul]
    congr 1
    ext i j
    by_cases hij : j = z i
    · subst j
      simp [lowerDiagonal, Matrix.one_apply]
    · simp [lowerDiagonal, Ne.symm hij]
  have h1 : (1 : Matrix m m R).submatrix z id * lowerDiagonal varpi z =
      (lowerDiagonal varpi z).submatrix z id := by
    simpa using Matrix.one_submatrix_mul z (Equiv.refl m) (lowerDiagonal varpi z)
  have h2 : B * D.submatrix id V.fixed =
      varpi • (1 : Matrix N N R).submatrix id V.fixed := by
    have hD : D * (1 : Matrix N N R).submatrix id V.fixed = D.submatrix id V.fixed := by
      simpa using Matrix.mul_submatrix_one (Equiv.refl N) V.fixed D
    rw [← hD, ← Matrix.mul_assoc, hBD, Matrix.smul_mul, Matrix.one_mul]
  rw [glueAdjoint, glueMatrix, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul,
    fromBlocks_inj]
  refine ⟨by simp [hBD], ?_, by simp, ?_⟩
  · rw [Matrix.mul_assoc _ ((1 : Matrix m m R).submatrix z id), h1, h_diag,
      Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc, h2, Matrix.smul_mul,
      neg_add_cancel, smul_zero]
  · ext i j
    by_cases _hi : i ∈ Set.range z <;> simp_all [lowerDiagonal, upperDiagonal,
      diagonal_apply, Matrix.one_apply]

/-- Package a reindexed glue matrix and its adjoint as a divided lattice. -/
def dividedLatticeOfNormalForm {varpi : R} {s : Matrix a N R}
    (F : StackNormalForm V varpi s)
    (epsilon' : N ⊕ m ≃ n) : DividedLattice R n varpi where
  reducedInverse := (glueMatrix varpi z V.fixed F.D).reindex epsilon' V.epsilon
  reducedAdjoint := (glueAdjoint varpi z V.fixed F.B).reindex V.epsilon epsilon'
  reducedAdjoint_mul := by
    simp [Matrix.reindex, F.mul_D, glueAdjoint_mul_glueMatrix, submatrix_smul]

omit [Fintype n] [Fintype a] [DecidableEq r] [DecidableEq n] [DecidableEq a] in
/-- The split-coordinate glued equation, expanded into its two block equations. -/
theorem glueMatrix_mul_eq_iff {varpi : R} (D : Matrix N N R) (x : Matrix n r R) :
    glueMatrix varpi z V.fixed D * x.submatrix V.epsilon id =
        varpi • (1 : Matrix (N ⊕ m) (N ⊕ m) R).submatrix id (Sum.inr ∘ z) ↔
      D * x.submatrix (V.epsilon ∘ Sum.inl) id =
          D.submatrix id V.fixed * (x.submatrix (V.epsilon ∘ Sum.inr) id).submatrix z id ∧
        lowerDiagonal varpi z * x.submatrix (V.epsilon ∘ Sum.inr) id =
          varpi • (1 : Matrix m m R).submatrix id z := by
  classical
  simp [glueMatrix, lowerDiagonal, diagonal_apply, sum_mul,
    sum_comm (γ := m), add_neg_eq_zero, ← Matrix.ext_iff, Matrix.mul_apply, Matrix.one_apply]

/-- The lower block equation is equivalent to the full inclusion matrix once its
`z` rows are `1`. -/
theorem lowerDiagonal_mul_eq_iff {varpi : R} {X : Matrix m r R}
    (h_top : X.submatrix z id = 1) :
    lowerDiagonal varpi z * X = varpi • (1 : Matrix m m R).submatrix id z ↔
      X = (1 : Matrix m m R).submatrix id z := by
  classical
  simp only [← Matrix.ext_iff, lowerDiagonal, diagonal_mul,
    Matrix.smul_apply, submatrix_apply, id_eq, _root_.smul_eq_mul,
    mul_ite, mul_one, mul_zero, Matrix.one_apply] at h_top ⊢
  grind

omit [Fintype n] [DecidableEq n] [DecidableEq a] in
/-- Block normalisation is the split-coordinate glued equation together with unit `z`-rows. -/
theorem isBlockNormalised_iff {varpi : R} {s : Matrix a N R}
    (F : StackNormalForm V varpi s) (x : Matrix n r R) :
    V.IsBlockNormalised varpi s x ↔ x.submatrix (V.epsilon ∘ Sum.inr ∘ z) id = 1 ∧
      glueMatrix varpi z V.fixed F.D * x.submatrix V.epsilon id =
        varpi • (1 : Matrix (N ⊕ m) (N ⊕ m) R).submatrix id (Sum.inr ∘ z) := by
  have hmul : F.D * (1 : Matrix N N R).submatrix id V.fixed = F.D.submatrix id V.fixed := by
    simpa using Matrix.mul_submatrix_one (Equiv.refl N) V.fixed F.D
  rw [IsBlockNormalised, F.mul_eq_mul_iff, hmul, V.glueMatrix_mul_eq_iff]
  have h_split : x.submatrix (V.epsilon ∘ Sum.inr ∘ z) id =
      (x.submatrix (V.epsilon ∘ Sum.inr) id).submatrix z id := by
    rfl
  rw [h_split]
  constructor
  · rintro ⟨h_m, h_N⟩
    have h_top : (x.submatrix (V.epsilon ∘ Sum.inr) id).submatrix z id = 1 := by
      rw [h_m]
      ext i j
      simp [Matrix.one_apply]
    refine ⟨h_top, by rwa [h_top, Matrix.mul_one], ?_⟩
    exact (lowerDiagonal_mul_eq_iff h_top).2 h_m
  · rintro ⟨h_top, h_N, h_lower⟩
    have h_m := (lowerDiagonal_mul_eq_iff h_top).1 h_lower
    exact ⟨h_m, by simpa [h_top] using h_N⟩

omit [DecidableEq r] [DecidableEq a] in
/-- Reindex the split-coordinate glued equation to the ambient coordinates. -/
theorem dividedLatticeOfNormalForm_mul_eq_iff {varpi : R} {s : Matrix a N R}
    (F : StackNormalForm V varpi s) (epsilon' : N ⊕ m ≃ n)
    (h_epsilon' : ∀ i : r, epsilon' (Sum.inr (z i)) = V.incl i) (x : Matrix n r R) :
    (V.dividedLatticeOfNormalForm F epsilon').reducedInverse * x =
        varpi • (1 : Matrix n n R).submatrix id V.incl ↔
      glueMatrix varpi z V.fixed F.D * x.submatrix V.epsilon id =
        varpi • (1 : Matrix (N ⊕ m) (N ⊕ m) R).submatrix id (Sum.inr ∘ z) := by
  rw [dividedLatticeOfNormalForm]
  rw [← (Matrix.reindex epsilon'.symm (.refl r)).injective.eq_iff]
  have h_reindex_mul :
      Matrix.reindex epsilon'.symm (.refl r)
        (((glueMatrix varpi z V.fixed F.D).reindex epsilon' V.epsilon) * x) =
        glueMatrix varpi z V.fixed F.D * x.submatrix V.epsilon id := by
    ext i j
    simp [Matrix.reindex, Matrix.mul_apply, ← V.epsilon.sum_comp]
  have h_reindex_incl : Matrix.reindex epsilon'.symm (.refl r)
      (varpi • (1 : Matrix n n R).submatrix id V.incl) =
        varpi • (1 : Matrix (N ⊕ m) (N ⊕ m) R).submatrix id (Sum.inr ∘ z) := by
    ext i j
    simp [Matrix.one_apply, ← h_epsilon']
  rw [h_reindex_mul, h_reindex_incl]

omit [Fintype n] [Fintype N] [Fintype m] [Fintype a]
  [DecidableEq n] [DecidableEq N] [DecidableEq m] [DecidableEq a] in
/-- Right multiplication by the congruence group preserves a `ϖ`-scaled equation. -/
theorem mul_congruenceGroup_eq_smul_iff (varpi : R)
    (A B : Matrix n r R) (Y : V.congruenceGroup varpi) :
    A * ((Y : GL r R) : Matrix r r R) = varpi • B ↔ A = varpi • B := by
  have hY : varpi • (((Y : GL r R) : Matrix r r R)) = varpi • 1 :=
    (V.mem_congruenceGroup_iff varpi Y).1 Y.property
  have h_fix : varpi • B * ((Y : GL r R) : Matrix r r R) = varpi • B := by
    rw [Matrix.smul_mul, ← Matrix.mul_smul, hY, Matrix.mul_smul, Matrix.mul_one]
  nth_rw 1 [← h_fix]
  exact Matrix.mul_left_inj_of_invertible (m := n) ((Y : GL r R) : Matrix r r R)

omit [DecidableEq a] in
/-- Characterise block normalisation after translation by a congruence-group element. -/
theorem isBlockNormalised_mul_iff {varpi : R} {s : Matrix a N R}
    (F : StackNormalForm V varpi s) (epsilon' : N ⊕ m ≃ n)
    (h_epsilon' : ∀ i : r, epsilon' (Sum.inr (z i)) = V.incl i)
    (x : Matrix n r R) (Y : V.congruenceGroup varpi) :
    V.IsBlockNormalised varpi s (x * ((Y : GL r R) : Matrix r r R)) ↔
      x.submatrix (V.epsilon ∘ Sum.inr ∘ z) id =
          (((Y⁻¹ : V.congruenceGroup varpi) : GL r R) : Matrix r r R) ∧
        (V.dividedLatticeOfNormalForm F epsilon').reducedInverse * x =
          varpi • (1 : Matrix n n R).submatrix id V.incl := by
  have h_top : x.submatrix (V.epsilon ∘ Sum.inr ∘ z) id =
        (((Y⁻¹ : V.congruenceGroup varpi) : GL r R) : Matrix r r R) ↔
      (x * ((Y : GL r R) : Matrix r r R)).submatrix
        (V.epsilon ∘ Sum.inr ∘ z) id = 1 :=
    ((Y : GL r R).mul_eq_one_iff_eq_inv).symm
  rw [h_top, V.isBlockNormalised_iff F,
    ← V.dividedLatticeOfNormalForm_mul_eq_iff F epsilon' h_epsilon',
    ← Matrix.mul_assoc, V.mul_congruenceGroup_eq_smul_iff]

/-- Divisibility of `ϖ`-annihilators gives the annihilator-product hypothesis. -/
theorem IsSquareZeroParameter.of_annihilator_dvd {varpi : R} (h_sq : varpi * varpi = 0)
    (h_div : ∀ x : R, varpi * x = 0 → ∃ u : R, x = varpi * u) :
    IsSquareZeroParameter varpi where
  sq_zero := h_sq
  mul_eq_zero {x y} hx hy := by
    obtain ⟨u, rfl⟩ := h_div x hx
    obtain ⟨v, rfl⟩ := h_div y hy
    calc
      (varpi * u) * (varpi * v) = (varpi * varpi) * (u * v) := by ac_rfl
      _ = 0 := by rw [h_sq, zero_mul]

/-- A matrix killed by `ϖ` has square zero under the parameter hypothesis. -/
theorem IsSquareZeroParameter.sq_eq_zero {varpi : R} (hvarpi : IsSquareZeroParameter varpi)
    {Y : Matrix r r R} (hY : varpi • Y = 0) : Y ^ 2 = 0 := by
  ext i k
  simp only [pow_two, Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro j _
  apply hvarpi.mul_eq_zero
  · have h := congrFun₂ hY i j
    simpa [Matrix.smul_apply] using h
  · have h := congrFun₂ hY j k
    simpa [Matrix.smul_apply] using h

omit [Fintype n] [Fintype N] [Fintype m] [Fintype a]
  [DecidableEq n] [DecidableEq N] [DecidableEq m] [DecidableEq a] in
/-- Construct a congruence-group element whose inverse is `1 - Y`. -/
theorem exists_congruenceGroup_inv_eq_one_sub {varpi : R}
    (hvarpi : IsSquareZeroParameter varpi) {Y : Matrix r r R} (hY : varpi • Y = 0) :
    ∃ A : V.congruenceGroup varpi,
      (((A⁻¹ : V.congruenceGroup varpi) : GL r R) : Matrix r r R) = 1 - Y := by
  have h_sq : Y ^ 2 = 0 := hvarpi.sq_eq_zero hY
  obtain ⟨A, hA⟩ : IsUnit (1 - Y) := IsNilpotent.isUnit_one_sub ⟨2, h_sq⟩
  refine ⟨⟨A, ?_⟩⁻¹, ?_⟩
  · apply (V.mem_congruenceGroup_iff varpi A).2
    simp [hA, smul_sub, hY]
  · simp [hA]

omit [Fintype r] [Fintype n] [Fintype m] [Fintype a] [DecidableEq r] [DecidableEq n]
  [DecidableEq m] [DecidableEq a] in
/-- The column operation supplied by `ColumnClearing` also clears the stacked matrix modulo `ϖ`. -/
theorem ColumnClearing.stack_cleared {varpi : R} {s : Matrix a N R}
    (hvarpi : IsSquareZeroParameter varpi) (C : ColumnClearing V s) :
    ∀ i : a ⊕ N, ∀ j : N, j ∉ Set.range V.divided →
      varpi * (V.stack varpi s * (C.K : Matrix N N R)) i j = 0 := by
  intro i j hj
  cases i with
  | inl i => simpa [stack] using congrArg (fun t : R ↦ varpi * t) (C.cleared i j hj)
  | inr i => simp [stack, ← mul_assoc, hvarpi.sq_zero]

omit [Fintype r] [Fintype n] [Fintype m] [DecidableEq r] [DecidableEq n]
  [DecidableEq m] [DecidableEq a] in
/-- The Hermite divisor inherits column vanishing from the stacked matrix. -/
theorem column_cleared_of_normalForm {varpi : R} {s : Matrix a N R}
    (hvarpi : IsSquareZeroParameter varpi) (F : StackNormalForm V varpi s)
    (C : ColumnClearing V s) (i j : N) (hj : j ∉ Set.range V.divided) :
    varpi * (F.D * (C.K : Matrix N N R)) i j = 0 := by
  have h_zero (k : a ⊕ N) : varpi * (V.stack varpi s * (C.K : Matrix N N R)) k j = 0 :=
    ColumnClearing.stack_cleared V hvarpi C k j hj
  rw [← F.D_eq, Matrix.mul_assoc, Matrix.mul_apply]
  simp [mul_add, mul_sum, mul_left_comm varpi, h_zero]

omit [DecidableEq r] [DecidableEq a] in
/-- The constructed reduced inverse has the required vanishing outside the divided columns. -/
theorem exists_glued_columns {varpi : R} {s : Matrix a N R}
    (hvarpi : IsSquareZeroParameter varpi) (F : StackNormalForm V varpi s)
    (C : ColumnClearing V s) (epsilon' : N ⊕ m ≃ n) :
    ∃ K : GL N R, ∀ i : n, ∀ j : N, j ∉ Set.range V.divided →
      varpi * ((V.dividedLatticeOfNormalForm F epsilon').reducedInverse.submatrix id
        (V.epsilon ∘ Sum.inl) * (K : Matrix N N R)) i j = 0 := by
  refine ⟨C.K, ?_⟩
  have h_cols : ∀ i j : N, j ∉ Set.range V.divided →
      varpi * (F.D * (C.K : Matrix N N R)) i j = 0 :=
    fun i j hj ↦ V.column_cleared_of_normalForm hvarpi F C i j hj
  simpa [dividedLatticeOfNormalForm, Matrix.reindex, glueMatrix,
    epsilon'.surjective.forall, Matrix.mul_apply] using h_cols

omit [DecidableEq a] in
/-- The glued equation has a unique block normaliser for the explicit construction. -/
theorem existsUnique_blockNormalised {varpi : R} {s : Matrix a N R}
    (hvarpi : IsSquareZeroParameter varpi) (F : StackNormalForm V varpi s)
    (epsilon' : N ⊕ m ≃ n)
    (h_epsilon' : ∀ i : r, epsilon' (Sum.inr (z i)) = V.incl i)
    (x : Matrix n r R)
    (hx : (V.dividedLatticeOfNormalForm F epsilon').reducedInverse * x =
      varpi • (1 : Matrix n n R).submatrix id V.incl) :
    ∃! Y : V.congruenceGroup varpi, V.IsBlockNormalised varpi s
      (x * ((Y : GL r R) : Matrix r r R)) := by
  have h_one : varpi • (1 - x.submatrix (V.epsilon ∘ Sum.inr ∘ z) id) = 0 := by
    ext i j
    simpa [glueMatrix, lowerDiagonal, diagonal_apply, Matrix.mul_apply,
      Matrix.one_apply, Matrix.smul_apply, mul_sub, sub_eq_zero] using
      congrFun₂ ((V.dividedLatticeOfNormalForm_mul_eq_iff F epsilon' h_epsilon' x).1 hx).symm
        (Sum.inr (z i)) j
  obtain ⟨Y, hY⟩ : ∃ Y : V.congruenceGroup varpi,
      (((Y⁻¹ : V.congruenceGroup varpi) : GL r R) : Matrix r r R) =
        x.submatrix (V.epsilon ∘ Sum.inr ∘ z) id := by
    simpa only [sub_sub_cancel] using
      V.exists_congruenceGroup_inv_eq_one_sub hvarpi h_one
  have h_iff (Y : V.congruenceGroup varpi) :=
    V.isBlockNormalised_mul_iff F epsilon' h_epsilon' x Y
  refine ⟨Y, (h_iff Y).2 ⟨hY.symm, hx⟩, fun Y' hY' ↦
    inv_injective (Subtype.ext (Units.ext ?_))⟩
  rw [hY, ((h_iff Y').1 hY').1]

omit [DecidableEq a] in
/-- Assemble the explicit reduced inverse into a glued divided lattice. -/
theorem isGlued_of_normalForm {varpi : R} {s : Matrix a N R}
    (hvarpi : IsSquareZeroParameter varpi) (F : StackNormalForm V varpi s)
    (C : ColumnClearing V s) (epsilon' : N ⊕ m ≃ n)
    (h_epsilon' : ∀ i : r, epsilon' (Sum.inr (z i)) = V.incl i) :
    V.IsGlued varpi s (V.dividedLatticeOfNormalForm F epsilon') where
  existsUnique := V.existsUnique_blockNormalised hvarpi F epsilon' h_epsilon'
  mul_eq_of_isBlockNormalised x Y hY :=
    ((V.isBlockNormalised_mul_iff F epsilon' h_epsilon' x Y).1 hY).2
  exists_cols_eq_zero := V.exists_glued_columns hvarpi F C epsilon'

omit [Fintype r] [Fintype n] [Fintype N] [Fintype m] [Fintype a] [DecidableEq r]
  [DecidableEq n] [DecidableEq N] [DecidableEq m] [DecidableEq a] in
/-- Extend the fixed and `z` inclusions to a permutation of the ambient coordinates. -/
theorem exists_row_equivalence [Finite r] : ∃ epsilon' : N ⊕ m ≃ n,
    ∀ i : r, epsilon' (Sum.inr (z i)) = V.incl i := by
  classical
  let _ := Fintype.ofFinite r
  obtain ⟨sigma, h_sigma⟩ := Equiv.Perm.exists_extending_pair
    (V.epsilon ∘ Sum.inr ∘ z) V.incl
    (V.epsilon.injective.comp (Sum.inr_injective.comp z.injective))
    (V.epsilon.injective.comp (Sum.inl_injective.comp V.fixed.injective))
  exact ⟨V.epsilon.trans sigma, h_sigma⟩

omit [Fintype m] [DecidableEq a] in
/-- Existence of a glued reduced inverse from the two explicit normal-form principles. -/
theorem exists_isGlued_of_normalForm {varpi : R}
    (hvarpi : IsSquareZeroParameter varpi)
    (s : Matrix a N R) (F : StackNormalForm V varpi s) (C : ColumnClearing V s) :
    ∃ L : DividedLattice R n varpi, V.IsGlued varpi s L := by
  have : Finite m := Finite.of_injective (V.epsilon ∘ Sum.inr)
    (V.epsilon.injective.comp Sum.inr_injective)
  let _ := Fintype.ofFinite m
  obtain ⟨epsilon', h_epsilon'⟩ := V.exists_row_equivalence
  exact ⟨V.dividedLatticeOfNormalForm F epsilon',
    V.isGlued_of_normalForm hvarpi F C epsilon' h_epsilon'⟩

omit [Fintype r] [Fintype n] [Fintype m] [DecidableEq r] [DecidableEq n]
  [DecidableEq m] [DecidableEq a] in
/-- The stacked matrix has a Hermite divisor over a pre-valuation ring. -/
theorem exists_stackNormalForm_of_preValuationRing [PreValuationRing R] (varpi : R)
    (s : Matrix a N R) : Nonempty (StackNormalForm V varpi s) := by
  classical
  obtain ⟨U, D, -, hUD, hD⟩ :=
    Matrix.exists_eq_submatrix_mul_blockTriangular_of_preValuationRing
      (V.stack varpi s) Function.Embedding.inr (fun _ ↦ ())
  refine ⟨
    { B := (U : Matrix (a ⊕ N) (a ⊕ N) R).submatrix Sum.inr Sum.inr
      D := D
      P := (U : Matrix (a ⊕ N) (a ⊕ N) R).submatrix id Sum.inr
      Q := ((U⁻¹ : GL (a ⊕ N) R) : Matrix (a ⊕ N) (a ⊕ N) R).submatrix
        Sum.inr id
      mul_D := ?_
      stack_eq := hUD
      D_eq := hD }⟩
  have h := congrArg Matrix.toRows₂ hUD
  ext i j
  have hij := congrFun₂ h.symm i j
  simpa [stack, Matrix.toRows₂, Matrix.mul_apply] using hij

omit [Fintype r] [Fintype n] [Fintype m] [Fintype a] [DecidableEq r] [DecidableEq n]
  [DecidableEq m] [DecidableEq a] in
/-- Every matrix has a column-clearing operation over a pre-valuation ring. -/
theorem exists_columnClearing_of_preValuationRing [PreValuationRing R]
    (s : Matrix a N R) : Nonempty (ColumnClearing V s) := by
  classical
  obtain ⟨K, hK⟩ := Matrix.exists_mul_gl_apply_eq_zero_off_range_of_preValuationRing
    s V.divided
  exact ⟨⟨K, hK⟩⟩

omit [Fintype m] [Fintype a] [DecidableEq a] in
/-- Every `s` has a glued divided lattice over a pre-valuation ring. -/
theorem exists_isGlued {varpi : R} [PreValuationRing R]
    (hvarpi : IsSquareZeroParameter varpi) (s : Matrix a N R) :
    ∃ L : DividedLattice R n varpi, V.IsGlued varpi s L := by
  have : Finite m := Finite.of_injective (V.epsilon ∘ Sum.inr)
    (V.epsilon.injective.comp Sum.inr_injective)
  have : Finite a := Finite.of_injective V.divided V.divided.injective
  let _ := Fintype.ofFinite m
  let _ := Fintype.ofFinite a
  obtain ⟨F⟩ := V.exists_stackNormalForm_of_preValuationRing varpi s
  obtain ⟨C⟩ := V.exists_columnClearing_of_preValuationRing s
  exact V.exists_isGlued_of_normalForm hvarpi s F C

omit [Fintype m] [Fintype a] [DecidableEq a] in
open Classical in
/-- A glued indicator is the finite sum of its block-normalised indicators. -/
theorem IsGlued.indicator_eq_sum {V : DividedSplitting r n N m a z} {varpi : R}
    {s : Matrix a N R} {L : DividedLattice R n varpi} (hL : V.IsGlued varpi s L)
    [Fintype (V.congruenceGroup varpi)] {A : Type*} [AddCommMonoid A]
    (x : Matrix n r R) (c : A) :
    (if L.reducedInverse * x = varpi • (1 : Matrix n n R).submatrix id V.incl then c else 0) =
      ∑ Y : V.congruenceGroup varpi,
        if V.IsBlockNormalised varpi s (x * ((Y : GL r R) : Matrix r r R)) then c else 0 := by
  classical
  split_ifs with hx
  · obtain ⟨Y, hY, h_unique⟩ := hL.existsUnique x hx
    rw [Finset.sum_eq_single Y fun Y' _ h_ne ↦
      ite_eq_right (mt (h_unique Y') h_ne), ite_eq_left hY]
    simp
  · rw [Finset.sum_eq_zero fun Y _ ↦
      ite_eq_right (mt (hL.mul_eq_of_isBlockNormalised x Y) hx)]

end DividedSplitting

end TauCeti.ThetaLift
