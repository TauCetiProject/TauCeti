/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.MetricSpace.ProperSpace
public import TauCeti.Algebra.Star.Pi
public import TauCeti.Algebra.Star.Projection.Family
public import TauCeti.RingTheory.Semisimple.Wedderburn.Presentation

import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.SimpleRing.Matrix
import TauCeti.Algebra.Matrix.Pi
import TauCeti.RingTheory.Semisimple.Star
import TauCeti.RingTheory.Semisimple.Wedderburn.Uniqueness

/-!
# Block decomposition of finite-dimensional complex C⋆-algebras

Every finite-dimensional (or proper) complex C⋆-algebra, even if presented without a unit, is
automatically unital and `⋆`-isomorphic to a finite direct product of full complex matrix
C⋆-algebras:
`A ≃⋆ₐ[ℂ] ∀ i : Fin k, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ` with `0 < n i`.

The proof proceeds in three stages:

1. **Automatic unitality (`CStarAlgebra.isUnital_of_properSpace`)**: in a `NonUnitalCStarAlgebra`
   whose closed balls are compact, the canonical increasing approximate unit lies in the compact
   closed unit ball and therefore admits a cluster point. Hausdorffness and separate continuity of
   multiplication force any cluster point to be a two-sided multiplicative identity, and the
   involution forces it to be a star projection.
2. **Single-block upgrade (`CStarAlgebra.nonempty_starAlgEquiv_matrix_of_algEquiv`)**: if a unital
   C⋆-algebra `B` is algebra-isomorphic (without assuming compatibility with `star`) to `Mₙ(ℂ)`,
   transporting a minimal matrix idempotent `E₀₀` produces a rank-one idempotent `q ∈ B`. Scaling
   `star q * q` yields a nonzero minimal star projection `p` whose corner `p * B * p` is `ℂ • p`.
   Equipping the left ideal `{x : B | x * p = x}` with the `p`-valued inner product makes it an
   `n`-dimensional complex Hilbert space whose bounded operators identify `⋆`-isomorphically with
   `B` by left multiplication.
3. **Multi-block Artin--Wedderburn upgrade (`CStarAlgebra.nonempty_cstarWedderburnPresentation`)**:
   a finite-dimensional unital C⋆-algebra has a proper involution, so it is semisimple by
   `TauCeti.isSemisimpleRing_of_isProperStar` and splits algebraically over `ℂ` into matrix blocks.
   Each block's central idempotent is normal in `A`, hence automatically a star projection by
   `isStarProjection_iff_isIdempotentElem_and_isStarNormal`. Cutting `A` along these central star
   projections decomposes `A` as a `⋆`-algebra product of closed ideals, each algebra-isomorphic
   (and therefore `⋆`-isomorphic by Stage 2) to a matrix algebra.

## Main definitions

* `TauCeti.CStarWedderburnPresentation`: a bundled `⋆`-algebra decomposition
  `A ≃⋆ₐ[ℂ] ∀ i : Fin blockCount, CStarMatrix (Fin (degree i)) (Fin (degree i)) ℂ` with positive
  block degrees, stated assuming only `[Add A] [Mul A] [SMul ℂ A] [Star A]` so it applies uniformly
  to both `NonUnitalCStarAlgebra` and `CStarAlgebra`.
* `TauCeti.CStarWedderburnPresentation.centralProjection`: the minimal central star projections of a
  chosen presentation.
* `CStarAlgebra.cstarWedderburnPresentation`: choose a `CStarWedderburnPresentation` of a
  finite-dimensional complex C⋆-algebra.

## Main results

* `CStarAlgebra.existsUnique_isStarProjection_mul_id_of_properSpace`,
  `CStarAlgebra.isUnital_of_properSpace`, `CStarAlgebra.isUnital_of_finiteDimensional`: every
  proper (equivalently, finite-dimensional) complex C⋆-algebra has a unique two-sided multiplicative
  identity, which is a star projection.
* `CStarAlgebra.nonempty_starAlgEquiv_matrix_of_algEquiv`,
  `CStarAlgebra.nonempty_starAlgEquiv_cstarMatrix_of_algEquiv`: a C⋆-algebra algebra-isomorphic to
  `Matrix m m ℂ` is `⋆`-algebra isomorphic to `Matrix m m ℂ` and `CStarMatrix m m ℂ`.
* `CStarAlgebra.nonempty_cstarWedderburnPresentation`,
  `CStarAlgebra.exists_starAlgEquiv_pi_cstarMatrix`: existence of the matrix-block
  `⋆`-decomposition.
* `TauCeti.CStarWedderburnPresentation.exists_equiv_degree_eq`,
  `TauCeti.CStarWedderburnPresentation.finrank_eq_sum_sq`,
  `TauCeti.CStarWedderburnPresentation.isMulCommutative_iff_forall_degree_eq_one`: uniqueness of
  block sizes up to permutation, the dimension formula `finrank ℂ A = ∑ i, degree i ^ 2`, and the
  commutativity criterion `∀ i, degree i = 1`.
* `CStarAlgebra.isMulCommutative_iff_nonempty_starAlgEquiv_fun`: a finite-dimensional complex
  C⋆-algebra is commutative iff it is `⋆`-isomorphic to `Fin (Module.finrank ℂ A) → ℂ`.

## References

* K. R. Davidson, *C⋆-Algebras by Example*, Fields Institute Monographs 6, Chapter III, Theorem
  III.1.1.
* M. Takesaki, *Theory of Operator Algebras I*, Chapter I, §11.
-/

public section

open Filter Topology
open scoped BigOperators CStarAlgebra

universe u

namespace CStarAlgebra

/-! ### Automatic unitality of proper and finite-dimensional C⋆-algebras -/

section AutomaticUnit

/-- Every C⋆-algebra whose closed balls are compact admits a unique two-sided multiplicative
identity. -/
theorem existsUnique_mul_id_of_properSpace (A : Type*) [NonUnitalCStarAlgebra A] [ProperSpace A] :
    ∃! e : A, ∀ a : A, e * a = a ∧ a * e = a := by
  let _ := CStarAlgebra.spectralOrder A
  have _ := CStarAlgebra.spectralOrderedRing A
  have hl := increasingApproximateUnit A
  obtain ⟨e, -, he⟩ := (isCompact_closedBall (0 : A) 1).exists_clusterPt
    (le_principal_iff.mpr hl.closedBall_mem)
  have : (𝓝 e ⊓ approximateUnit A).NeBot := he
  have hid : ∀ a : A, e * a = a ∧ a * e = a := fun a ↦
    ⟨tendsto_nhds_unique
      (((by fun_prop : Continuous (· * a)).tendsto e).mono_left inf_le_left)
      ((hl.tendsto_mul_right a).mono_left inf_le_right),
    tendsto_nhds_unique
      (((by fun_prop : Continuous (a * ·)).tendsto e).mono_left inf_le_left)
      ((hl.tendsto_mul_left a).mono_left inf_le_right)⟩
  refine ⟨e, hid, fun e' he' ↦ ?_⟩
  calc
    e' = e * e' := ((hid e').1).symm
    _ = e := (he' e).2

/-- In a proper C⋆-algebra, the unique two-sided multiplicative identity is a star projection. -/
theorem existsUnique_isStarProjection_mul_id_of_properSpace (A : Type*)
    [NonUnitalCStarAlgebra A] [ProperSpace A] :
    ∃! e : A, IsStarProjection e ∧ ∀ a : A, e * a = a ∧ a * e = a := by
  obtain ⟨e, he, huniq⟩ := existsUnique_mul_id_of_properSpace A
  have hsa : IsSelfAdjoint e := by
    rw [IsSelfAdjoint, ← (he (star e)).1]
    simpa only [star_mul, star_star] using congrArg star (he (star e)).1
  exact ⟨e, ⟨⟨(he e).1, hsa⟩, he⟩, fun e' he' ↦ huniq e' he'.2⟩

/-- Every C⋆-algebra whose closed balls are compact is unital (`IsUnital`). -/
theorem isUnital_of_properSpace (A : Type*) [NonUnitalCStarAlgebra A] [ProperSpace A] :
    IsUnital A := by
  obtain ⟨e, he, -⟩ := existsUnique_mul_id_of_properSpace A
  exact ⟨e, he⟩

/-- Every finite-dimensional complex C⋆-algebra is unital, even if given only as a
`NonUnitalCStarAlgebra`. -/
theorem isUnital_of_finiteDimensional (A : Type*) [NonUnitalCStarAlgebra A]
    [FiniteDimensional ℂ A] : IsUnital A := by
  have := FiniteDimensional.proper ℂ A
  exact isUnital_of_properSpace A

end AutomaticUnit

end CStarAlgebra

/-! ### Chosen C⋆-Wedderburn presentations -/

namespace TauCeti

/-- A chosen `⋆`-algebra decomposition of `A` as a finite direct product of full complex matrix
C⋆-algebras of positive degree.

Only addition, multiplication, complex scalar multiplication, and involution are required on `A`,
so the same structure applies without change to both `NonUnitalCStarAlgebra` and `CStarAlgebra`. -/
structure CStarWedderburnPresentation (A : Type u) [Add A] [Mul A] [SMul ℂ A] [Star A] where
  /-- The number of matrix blocks. -/
  blockCount : ℕ
  /-- The matrix size of each block. -/
  degree : Fin blockCount → ℕ
  /-- Every matrix block has positive size. -/
  [instNeZeroDegree : ∀ i, NeZero (degree i)]
  /-- The chosen product decomposition into matrix C⋆-algebras. -/
  equiv : A ≃⋆ₐ[ℂ] ∀ i, CStarMatrix (Fin (degree i)) (Fin (degree i)) ℂ

attribute [instance] CStarWedderburnPresentation.instNeZeroDegree

namespace CStarWedderburnPresentation

section Minimal

variable {A : Type u} [Add A] [Mul A] [SMul ℂ A] [Star A] (P : CStarWedderburnPresentation A)

/-- Every block in a C⋆-Wedderburn presentation has strictly positive matrix degree. -/
theorem degree_pos (i : Fin P.blockCount) : 0 < P.degree i :=
  Nat.pos_of_ne_zero (NeZero.ne (P.degree i))

/-- Every block in a C⋆-Wedderburn presentation has degree at least `1`. -/
theorem one_le_degree (i : Fin P.blockCount) : 1 ≤ P.degree i :=
  P.degree_pos i

/-- Reinterpret a C⋆-Wedderburn presentation using ordinary `Matrix` blocks rather than
`CStarMatrix` blocks. -/
def matrixStarAlgEquiv : A ≃⋆ₐ[ℂ] ∀ i, Matrix (Fin (P.degree i)) (Fin (P.degree i)) ℂ :=
  P.equiv.trans (StarAlgEquiv.piCongrRight fun _ ↦ CStarMatrix.ofMatrixStarAlgEquiv.symm)

@[simp]
theorem matrixStarAlgEquiv_apply (a : A) (i : Fin P.blockCount) :
    P.matrixStarAlgEquiv a i = CStarMatrix.ofMatrix.symm (P.equiv a i) := by
  simp only [matrixStarAlgEquiv, StarAlgEquiv.trans_apply, StarAlgEquiv.piCongrRight_apply]
  rfl

@[simp]
theorem matrixStarAlgEquiv_symm_apply
    (x : ∀ i, Matrix (Fin (P.degree i)) (Fin (P.degree i)) ℂ) :
    P.matrixStarAlgEquiv.symm x = P.equiv.symm fun i ↦ CStarMatrix.ofMatrix (x i) := by
  simp only [matrixStarAlgEquiv, StarAlgEquiv.symm_trans_apply, StarAlgEquiv.piCongrRight_symm,
    StarAlgEquiv.symm_symm]
  exact congrArg P.equiv.symm (funext fun i ↦ StarAlgEquiv.piCongrRight_apply _ x i)

/-- **Uniqueness of C⋆-Wedderburn blocks**: any two C⋆-Wedderburn presentations of `A` have the
same block degrees up to a permutation of the block indices. -/
theorem exists_equiv_degree_eq (Q : CStarWedderburnPresentation A) :
    ∃ σ : Fin P.blockCount ≃ Fin Q.blockCount, ∀ i, P.degree i = Q.degree (σ i) := by
  obtain ⟨σ, hσ⟩ := RingEquiv.wedderburn_blocks_unique
    P.matrixStarAlgEquiv.toRingEquiv Q.matrixStarAlgEquiv.toRingEquiv
  refine ⟨σ, fun i ↦ ?_⟩
  simpa only [Fintype.card_fin] using (hσ i).1

/-- The number of matrix blocks is an invariant of `A`. -/
theorem blockCount_eq (Q : CStarWedderburnPresentation A) : P.blockCount = Q.blockCount := by
  obtain ⟨σ, -⟩ := P.exists_equiv_degree_eq Q
  simpa only [Fintype.card_fin] using Fintype.card_congr σ

/-- The multiset of matrix block degrees is an invariant of `A`. -/
theorem multiset_degree_eq (Q : CStarWedderburnPresentation A) :
    Multiset.map P.degree Finset.univ.val = Multiset.map Q.degree Finset.univ.val := by
  obtain ⟨σ, hσ⟩ := P.exists_equiv_degree_eq Q
  have huniv : Finset.univ.val.map σ = Finset.univ.val :=
    congrArg Finset.val (Finset.univ_map_equiv_to_embedding σ)
  calc
    Multiset.map P.degree Finset.univ.val
      = Multiset.map (Q.degree ∘ σ) Finset.univ.val :=
        Multiset.map_congr rfl fun i _ ↦ hσ i
    _ = Multiset.map Q.degree (Finset.univ.val.map σ) := (Multiset.map_map Q.degree σ _).symm
    _ = Multiset.map Q.degree Finset.univ.val := by rw [huniv]

end Minimal

section SplitAlgebra

variable {A : Type u} [Ring A] [Algebra ℂ A] [Star A] (P : CStarWedderburnPresentation A)

/-- Forget the involution and C⋆-matrix norm to obtain a split algebraic Wedderburn presentation
over `ℂ`. -/
@[expose]
def toSplitWedderburnAlgebraPresentation : SplitWedderburnAlgebraPresentation ℂ A where
  blockCount := P.blockCount
  degree := P.degree
  equiv := P.matrixStarAlgEquiv.toAlgEquiv

@[simp]
theorem toSplitWedderburnAlgebraPresentation_blockCount :
    P.toSplitWedderburnAlgebraPresentation.blockCount = P.blockCount :=
  rfl

@[simp]
theorem toSplitWedderburnAlgebraPresentation_degree :
    P.toSplitWedderburnAlgebraPresentation.degree = P.degree :=
  rfl

@[simp]
theorem toSplitWedderburnAlgebraPresentation_equiv :
    P.toSplitWedderburnAlgebraPresentation.equiv = P.matrixStarAlgEquiv.toAlgEquiv :=
  rfl

/-- The center of a unital algebra admitting a C⋆-Wedderburn presentation has complex dimension
equal to the number of matrix blocks. -/
theorem finrank_center : Module.finrank ℂ (Subalgebra.center ℂ A) = P.blockCount := by
  rw [(Subalgebra.centerCongr P.matrixStarAlgEquiv.toAlgEquiv).toLinearEquiv.finrank_eq,
    TauCeti.finrank_center_pi_matrix ℂ P.degree, Fintype.card_fin]

end SplitAlgebra

section ModuleAndProjections

variable {A : Type u} [NonUnitalRing A] [StarRing A] [Module ℂ A]
  (P : CStarWedderburnPresentation A)

include P in
/-- An algebra admitting a C⋆-Wedderburn presentation is finite-dimensional over `ℂ`. -/
theorem finiteDimensional : FiniteDimensional ℂ A :=
  let eLin : A ≃ₗ[ℂ] ∀ i, Matrix (Fin (P.degree i)) (Fin (P.degree i)) ℂ :=
    { P.matrixStarAlgEquiv.toAddEquiv with map_smul' := map_smul P.matrixStarAlgEquiv }
  Module.Finite.equiv eLin.symm

/-- **Dimension formula**: the complex dimension of `A` equals the sum of the squares of its matrix
block degrees. -/
theorem finrank_eq_sum_sq : Module.finrank ℂ A = ∑ i, P.degree i ^ 2 :=
  let eLin : A ≃ₗ[ℂ] ∀ i, Matrix (Fin (P.degree i)) (Fin (P.degree i)) ℂ :=
    { P.matrixStarAlgEquiv.toAddEquiv with map_smul' := map_smul P.matrixStarAlgEquiv }
  eLin.finrank_eq.trans (TauCeti.finrank_pi_matrix ℂ P.degree)

/-- Every block degree satisfies `degree i ^ 2 ≤ Module.finrank ℂ A`. -/
theorem sq_degree_le_finrank (i : Fin P.blockCount) :
    P.degree i ^ 2 ≤ Module.finrank ℂ A := by
  rw [P.finrank_eq_sum_sq]
  exact Finset.single_le_sum (f := fun j ↦ P.degree j ^ 2) (fun _ _ ↦ Nat.zero_le _)
    (Finset.mem_univ i)

/-- The number of blocks is at most `Module.finrank ℂ A`. -/
theorem blockCount_le_finrank : P.blockCount ≤ Module.finrank ℂ A := by
  rw [P.finrank_eq_sum_sq]
  calc
    P.blockCount = ∑ _i : Fin P.blockCount, 1 := by simp
    _ ≤ ∑ i : Fin P.blockCount, P.degree i ^ 2 :=
      Finset.sum_le_sum fun i _ ↦ Nat.one_le_pow 2 (P.degree i) (P.degree_pos i)

/-- The `i`-th minimal central star projection of `A` associated with the presentation `P`,
obtained by pulling back the unit of the `i`-th matrix block. -/
def centralProjection (i : Fin P.blockCount) : A :=
  P.equiv.symm (Pi.single (M := fun j ↦ CStarMatrix (Fin (P.degree j)) (Fin (P.degree j)) ℂ) i 1)

@[simp]
theorem equiv_centralProjection (i : Fin P.blockCount) :
    P.equiv (P.centralProjection i) =
      Pi.single (M := fun j ↦ CStarMatrix (Fin (P.degree j)) (Fin (P.degree j)) ℂ) i 1 :=
  P.equiv.apply_symm_apply _

/-- Each `P.centralProjection i` is a star projection. -/
theorem isStarProjection_centralProjection (i : Fin P.blockCount) :
    IsStarProjection (P.centralProjection i) := by
  have hsingle : IsStarProjection
      (Pi.single (M := fun j ↦ CStarMatrix (Fin (P.degree j)) (Fin (P.degree j)) ℂ) i 1) := by
    refine ⟨?_, ?_⟩
    · rw [IsIdempotentElem, ← Pi.single_mul, one_mul]
    · rw [IsSelfAdjoint, ← Pi.single_star, star_one]
  exact hsingle.map P.equiv.symm

/-- Each `P.centralProjection i` is nonzero. -/
theorem centralProjection_ne_zero (i : Fin P.blockCount) : P.centralProjection i ≠ 0 := by
  intro h
  have h1 : (1 : CStarMatrix (Fin (P.degree i)) (Fin (P.degree i)) ℂ) = 0 := by
    have := congrFun (congrArg P.equiv h) i
    simpa only [equiv_centralProjection, Pi.single_eq_same, map_zero, Pi.zero_apply] using this
  have hentry : (1 : CStarMatrix (Fin (P.degree i)) (Fin (P.degree i)) ℂ) 0 0 = 0 := by
    rw [h1]; rfl
  exact one_ne_zero hentry

/-- Distinct minimal central projections of `P` multiply to zero. -/
theorem centralProjection_mul_of_ne {i j : Fin P.blockCount} (hij : i ≠ j) :
    P.centralProjection i * P.centralProjection j = 0 := by
  apply EquivLike.injective P.equiv
  rw [map_mul, map_zero, equiv_centralProjection, equiv_centralProjection]
  ext k
  by_cases hik : i = k
  · subst hik; simp [hij]
  · simp [hik]

/-- Minimal central projections of `P` are pairwise star-orthogonal. -/
theorem pairwise_isStarOrtho_centralProjection :
    Pairwise fun i j ↦ IsStarOrtho (P.centralProjection i) (P.centralProjection j) := by
  intro i j hij
  have hj := (P.isStarProjection_centralProjection j).isSelfAdjoint.star_eq
  exact ⟨by rw [hj, P.centralProjection_mul_of_ne hij],
    by rw [hj, P.centralProjection_mul_of_ne hij.symm]⟩

/-- Every minimal central projection of `P` commutes with all elements of `A`. -/
theorem commute_centralProjection (i : Fin P.blockCount) (a : A) :
    Commute (P.centralProjection i) a := by
  rw [commute_iff_eq]
  apply EquivLike.injective P.equiv
  rw [map_mul, map_mul, equiv_centralProjection]
  ext j
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

/-- `A` is multiplicatively commutative if and only if every block in `P` has degree `1`. -/
theorem isMulCommutative_iff_forall_degree_eq_one :
    IsMulCommutative A ↔ ∀ i, P.degree i = 1 := by
  refine ⟨fun hcomm i ↦ ?_, fun hdeg ↦ ⟨⟨fun a b ↦ ?_⟩⟩⟩
  · by_contra hne
    have hgt : 1 < P.degree i := lt_of_le_of_ne (P.one_le_degree i) (Ne.symm hne)
    let i₀ : Fin (P.degree i) := ⟨0, P.degree_pos i⟩
    let i₁ : Fin (P.degree i) := ⟨1, hgt⟩
    have hi₀₁ : i₀ ≠ i₁ := by simp [i₀, i₁]
    let x : ∀ j, Matrix (Fin (P.degree j)) (Fin (P.degree j)) ℂ :=
      Pi.single i (Matrix.single i₀ i₁ 1)
    let y : ∀ j, Matrix (Fin (P.degree j)) (Fin (P.degree j)) ℂ :=
      Pi.single i (Matrix.single i₁ i₀ 1)
    have hxy : P.matrixStarAlgEquiv.symm x * P.matrixStarAlgEquiv.symm y =
        P.matrixStarAlgEquiv.symm y * P.matrixStarAlgEquiv.symm x := hcomm.is_comm.comm _ _
    have hmat : Matrix.single i₀ i₁ (1 : ℂ) * Matrix.single i₁ i₀ 1 =
        Matrix.single i₁ i₀ 1 * Matrix.single i₀ i₁ 1 := by
      have := congrFun (congrArg P.matrixStarAlgEquiv hxy) i
      simpa only [map_mul, StarAlgEquiv.apply_symm_apply, Pi.mul_apply, x, y,
        Pi.single_eq_same] using this
    have hentry := congrFun (congrFun hmat i₀) i₀
    simp [Matrix.mul_apply, Matrix.single_apply, hi₀₁.symm] at hentry
  · apply EquivLike.injective P.matrixStarAlgEquiv
    rw [map_mul, map_mul]
    ext i r s
    have hsub : Subsingleton (Fin (P.degree i)) := by
      rw [hdeg i]; infer_instance
    rw [Pi.mul_apply, Pi.mul_apply, Subsingleton.elim r s, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Subsingleton.elim k s, mul_comm]

/-- When every block of `P` has degree `1`, collapsing the `1 × 1` matrix blocks gives a
`⋆`-algebra equivalence `A ≃⋆ₐ[ℂ] (Fin P.blockCount → ℂ)`. -/
def equivFunOfForallDegreeEqOne (h : ∀ i, P.degree i = 1) :
    A ≃⋆ₐ[ℂ] (Fin P.blockCount → ℂ) :=
  P.equiv.trans <| StarAlgEquiv.piCongrRight fun i ↦
    have : Subsingleton (Fin (P.degree i)) := h i ▸ inferInstance
    { toFun M := M 0 0
      invFun z := CStarMatrix.ofMatrix (Matrix.of fun _ _ ↦ z)
      left_inv M := by
        ext r s
        simp [Subsingleton.elim r 0, Subsingleton.elim s 0]
      right_inv _ := rfl
      map_mul' M N := by
        rw [CStarMatrix.mul_apply]
        exact Finset.sum_eq_single 0 (fun k _ hk ↦ absurd (Subsingleton.elim k 0) hk) (by simp)
      map_add' _ _ := rfl
      map_star' _ := rfl
      map_smul' _ _ := rfl }

@[simp]
theorem equivFunOfForallDegreeEqOne_apply (h : ∀ i, P.degree i = 1) (a : A)
    (i : Fin P.blockCount) :
    P.equivFunOfForallDegreeEqOne h a i = P.equiv a i 0 0 := by
  simp only [equivFunOfForallDegreeEqOne, StarAlgEquiv.trans_apply, StarAlgEquiv.piCongrRight_apply]
  rfl

end ModuleAndProjections

section UnitalProjections

variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A] (P : CStarWedderburnPresentation A)

/-- In a unital algebra, the minimal central projections of `P` form a complete orthogonal
projection family summing to `1`. -/
theorem isCompleteOrthogonalProjectionFamily_centralProjection :
    IsCompleteOrthogonalProjectionFamily P.centralProjection := by
  rw [isCompleteOrthogonalProjectionFamily_iff]
  refine ⟨?_, P.isStarProjection_centralProjection⟩
  have hsingle : CompleteOrthogonalIdempotents
      (fun i : Fin P.blockCount ↦
        Pi.single (M := fun j ↦ CStarMatrix (Fin (P.degree j)) (Fin (P.degree j)) ℂ) i 1) :=
    CompleteOrthogonalIdempotents.single _
  exact hsingle.map P.equiv.symm.toRingEquiv.toRingHom

end UnitalProjections

end CStarWedderburnPresentation

end TauCeti

/-! ### Upgrading algebraic matrix isomorphisms to `⋆`-isomorphisms -/

namespace CStarAlgebra

open TauCeti

section SingleBlock

/-- Positive real multiples of `star y * y` are nonnegative in the spectral order of a
C⋆-algebra. -/
private theorem real_smul_star_mul_self_nonneg {B : Type*} [CStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] {t : ℝ} (ht : 0 ≤ t) (y : B) :
    0 ≤ (t : ℂ) • (star y * y) := by
  let s : ℂ := Real.sqrt t
  have hs : star s * s = (t : ℂ) := by
    simp [s, ← Complex.ofReal_mul, Real.mul_self_sqrt ht]
  have hsq : star (s • y) * (s • y) = (t : ℂ) • (star y * y) := by
    rw [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hs]
  rw [← hsq]
  exact star_mul_self_nonneg (s • y)

/-- If `q ≠ 0` and `0 ≤ c • (star q * q)` in the spectral order of a C⋆-algebra, then `c` is a
nonnegative real scalar (`c = (c.re : ℂ)` and `0 ≤ c.re`). -/
private theorem eq_ofReal_re_and_re_nonneg_of_smul_star_mul_self_nonneg {B : Type*}
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] {q : B} (hq : q ≠ 0) {c : ℂ}
    (hnonneg : 0 ≤ c • (star q * q)) : c = (c.re : ℂ) ∧ 0 ≤ c.re := by
  have hsq_ne : star q * q ≠ 0 := star_mul_self_ne_zero.mpr hq
  have hsa : star (c • (star q * q)) = c • (star q * q) :=
    (IsSelfAdjoint.of_nonneg hnonneg).star_eq
  rw [star_smul, (IsSelfAdjoint.star_mul_self q).star_eq] at hsa
  have hc_conj : star c = c :=
    sub_eq_zero.mp ((smul_eq_zero.mp (by rw [sub_smul, hsa, sub_self])).resolve_right hsq_ne)
  have hc_eq : c = (c.re : ℂ) := (Complex.conj_eq_iff_re.mp hc_conj).symm
  refine ⟨hc_eq, ?_⟩
  by_contra! hneg
  have hneg_nonneg : 0 ≤ -(c • (star q * q)) := by
    have hneg_eq : -(c • (star q * q)) = ((-c.re : ℝ) : ℂ) • (star q * q) := by
      conv_lhs => rw [hc_eq]
      rw [Complex.ofReal_neg, neg_smul]
    rw [hneg_eq]
    exact real_smul_star_mul_self_nonneg (neg_nonneg.mpr hneg.le) q
  have hzero : c • (star q * q) = 0 := le_antisymm (neg_nonneg.mp hneg_nonneg) hnonneg
  have hc0 : c = 0 := (smul_eq_zero.mp hzero).resolve_right hsq_ne
  rw [hc0, Complex.zero_re] at hneg
  exact lt_irrefl 0 hneg

/-- From an algebra isomorphism `Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] B` with `n ≠ 0`, extract a nonzero
minimal star projection `p : B` whose corner `p * b * p` is scalar along `p`, and whose left ideal
`{x : B | x * p = x}` coincides with `{x : B | x * g (Matrix.single 0 0 1) = x}`. -/
private theorem exists_minimal_isStarProjection_of_algEquiv {B : Type*} [CStarAlgebra B] {n : ℕ}
    [NeZero n] (g : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] B) :
    ∃ (p : B) (ψ : B →ₗ[ℂ] ℂ),
      IsStarProjection p ∧ p ≠ 0 ∧ (∀ b : B, p * b * p = ψ b • p) ∧
      ∀ x : B, x * p = x ↔ x * g (Matrix.single 0 0 1) = x := by
  let _ := CStarAlgebra.spectralOrder B
  have _ := CStarAlgebra.spectralOrderedRing B
  let e₀ : Matrix (Fin n) (Fin n) ℂ := Matrix.single 0 0 1
  have he₀_ne : e₀ ≠ 0 := fun h ↦
    one_ne_zero (by simpa [e₀] using congrFun (congrFun h 0) 0 : (1 : ℂ) = 0)
  have he₀_corner (M : Matrix (Fin n) (Fin n) ℂ) : e₀ * M * e₀ = M 0 0 • e₀ := by
    ext i j
    by_cases hi : 0 = i <;> by_cases hj : 0 = j <;>
      simp [e₀, Matrix.mul_apply, Matrix.single_apply, ite_and, hi, hj]
  set q : B := g e₀
  have hq_ne : q ≠ 0 := fun h ↦ he₀_ne (g.injective (h.trans (map_zero g).symm))
  have hq_idem : q * q = q := by simp [q, e₀, ← map_mul]
  have hq_corner (b : B) : q * b * q = (g.symm b 0 0) • q := by
    simpa only [q, map_mul, map_smul, AlgEquiv.apply_symm_apply] using
      congrArg g (he₀_corner (g.symm b))
  set c : ℂ := g.symm (star q) 0 0
  set a : B := star q * q
  have ha_ne : a ≠ 0 := star_mul_self_ne_zero.mpr hq_ne
  have ha_sa : IsSelfAdjoint a := .star_mul_self q
  have ha_sq : a * a = c • a := by
    calc
      a * a = star q * (q * star q * q) := by simp only [a, mul_assoc]
      _ = c • a := by rw [hq_corner (star q), mul_smul_comm]
  have ha2_star : star a * a = c • (star q * q) := by rw [ha_sa.star_eq, ha_sq]
  have ha2_nonneg : 0 ≤ c • (star q * q) := ha2_star ▸ star_mul_self_nonneg a
  obtain ⟨hc_eq, -⟩ := eq_ofReal_re_and_re_nonneg_of_smul_star_mul_self_nonneg hq_ne ha2_nonneg
  have hc_conj : star c = c := Complex.conj_eq_iff_re.mpr hc_eq.symm
  have hc_ne : c ≠ 0 := fun hc0 ↦ by
    have ha2_zero : star a * a = 0 := by rw [ha2_star, hc0, zero_smul]
    exact ha_ne (star_mul_self_eq_zero.mp ha2_zero)
  set p : B := c⁻¹ • a
  have hp_proj : IsStarProjection p := ⟨by
    rw [IsIdempotentElem]
    calc
      p * p = (c⁻¹ * (c⁻¹ * c)) • a := by
        simp only [p, smul_mul_assoc, mul_smul_comm, smul_smul, ha_sq]
      _ = p := by rw [inv_mul_cancel₀ hc_ne, mul_one],
    by rw [IsSelfAdjoint, star_smul, ha_sa.star_eq, star_inv₀, hc_conj]⟩
  have hpq : p * q = p := by simp only [p, a, smul_mul_assoc, mul_assoc, hq_idem]
  have hqp : q * p = q := by
    calc
      q * p = c⁻¹ • (q * star q * q) := by
        simp only [p, a, mul_smul_comm]; rw [← mul_assoc]
      _ = (c⁻¹ * c) • q := by rw [hq_corner (star q), smul_smul]
      _ = q := by rw [inv_mul_cancel₀ hc_ne, one_smul]
  have hp_ne : p ≠ 0 := fun hp0 ↦ hq_ne (by rw [← hqp, hp0, mul_zero])
  let ψ : B →ₗ[ℂ] ℂ :=
    { toFun b := c⁻¹ * g.symm (b * star q) 0 0
      map_add' b₁ b₂ := by simp [add_mul, mul_add]
      map_smul' r b := by simp [mul_left_comm] }
  have hp_corner (b : B) : p * b * p = ψ b • p := by
    have haba : a * b * a = g.symm (b * star q) 0 0 • a := by
      calc
        a * b * a = star q * (q * (b * star q) * q) := by simp only [a, mul_assoc]
        _ = g.symm (b * star q) 0 0 • a := by rw [hq_corner (b * star q), mul_smul_comm]
    calc
      p * b * p = (c⁻¹ * c⁻¹) • (a * b * a) := by
        simp only [p, smul_mul_assoc, mul_smul_comm, smul_smul]
      _ = ψ b • p := by rw [haba, smul_smul, smul_smul, mul_right_comm]; rfl
  refine ⟨p, ψ, hp_proj, hp_ne, hp_corner, fun x ↦
    ⟨fun hx ↦ by rw [← hx, mul_assoc, hpq], fun hx ↦ by rw [← hx, mul_assoc, hqp]⟩⟩

/-- The left ideal `{x : B | x * p = x}` generated by `p` as a complex linear subspace of `B`. -/
private def minimalLeftIdeal {B : Type*} [CStarAlgebra B] (p : B) : Submodule ℂ B where
  carrier := {x : B | x * p = x}
  add_mem' {x y} hx hy := by dsimp at hx hy ⊢; rw [add_mul, hx, hy]
  zero_mem' := zero_mul p
  smul_mem' r {x} hx := by dsimp at hx ⊢; rw [smul_mul_assoc, hx]

@[simp]
private theorem mem_minimalLeftIdeal {B : Type*} [CStarAlgebra B] {p x : B} :
    x ∈ minimalLeftIdeal p ↔ x * p = x :=
  Iff.rfl

/-- For `x, y` in `minimalLeftIdeal p` of a minimal star projection `p`, `star x * y` lies in the
scalar corner `ℂ • p`. -/
private theorem minimalLeftIdeal_star_mul {B : Type*} [CStarAlgebra B] {p : B} {ψ : B →ₗ[ℂ] ℂ}
    (hp : IsStarProjection p) (hp_corner : ∀ b : B, p * b * p = ψ b • p)
    (x y : minimalLeftIdeal p) :
    star (x : B) * (y : B) = ψ (star (x : B) * (y : B)) • p := by
  have hx : p * star (x : B) = star (x : B) := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star x.2
  calc
    star (x : B) * (y : B) = p * (star (x : B) * (y : B)) * p := by
      rw [← mul_assoc, hx, mul_assoc, y.2]
    _ = ψ (star (x : B) * (y : B)) • p := hp_corner _

/-- Equip `minimalLeftIdeal p` with its `p`-valued complex inner product
`⟪x, y⟫ = ψ (star x * y)` compatible with the C⋆-norm inherited from `B`. -/
@[instance_reducible]
private noncomputable def minimalLeftIdealInnerProductSpace {B : Type*} [CStarAlgebra B] {p : B}
    {ψ : B →ₗ[ℂ] ℂ} (hp : IsStarProjection p) (hp_ne : p ≠ 0)
    (hp_corner : ∀ b : B, p * b * p = ψ b • p) :
    InnerProductSpace ℂ (minimalLeftIdeal p) := by
  let _ := CStarAlgebra.spectralOrder B
  have _ := CStarAlgebra.spectralOrderedRing B
  have hp_norm : ‖p‖ = 1 := by
    have hmul : ‖p‖ * ‖p‖ = ‖p‖ := by
      rw [← CStarRing.norm_star_mul_self, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
    exact mul_left_cancel₀ (norm_ne_zero_iff.mpr hp_ne) (hmul.trans (mul_one ‖p‖).symm)
  have hcoeff_eq {z₁ z₂ : ℂ} (hz : z₁ • p = z₂ • p) : z₁ = z₂ :=
    sub_eq_zero.mp ((smul_eq_zero.mp (by rw [sub_smul, hz, sub_self])).resolve_right hp_ne)
  exact
    { inner x y := ψ (star (x : B) * (y : B))
      norm_sq_eq_re_inner x := by
        set z : ℂ := ψ (star (x : B) * (x : B))
        have hxx : star (x : B) * (x : B) = z • p := minimalLeftIdeal_star_mul hp hp_corner x x
        have hzp_nonneg : 0 ≤ z • (star p * p) := by
          rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq, ← hxx]
          exact star_mul_self_nonneg (x : B)
        obtain ⟨hz_eq, hz_nonneg⟩ :=
          eq_ofReal_re_and_re_nonneg_of_smul_star_mul_self_nonneg hp_ne hzp_nonneg
        calc
          ‖x‖ ^ 2 = ‖(x : B)‖ * ‖(x : B)‖ := sq ‖(x : B)‖
          _ = ‖star (x : B) * (x : B)‖ := CStarRing.norm_star_mul_self.symm
          _ = ‖(z.re : ℂ) • p‖ := by conv_lhs => rw [hxx, hz_eq]
          _ = ‖(z.re : ℂ)‖ * ‖p‖ := norm_smul _ _
          _ = z.re := by rw [hp_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg hz_nonneg]
      conj_inner_symm x y := by
        apply hcoeff_eq
        have h1 := congrArg star (minimalLeftIdeal_star_mul hp hp_corner y x)
        rw [star_mul, star_star, star_smul, hp.isSelfAdjoint.star_eq, Complex.star_def] at h1
        exact h1.symm.trans (minimalLeftIdeal_star_mul hp hp_corner x y)
      add_left x y w := by simp [star_add, add_mul]
      smul_left x y r := by simp [star_smul] }

/-- Identify `minimalLeftIdeal p` linearly with `Fin n → ℂ` via the first column of
`Matrix (Fin n) (Fin n) ℂ` along `g`. -/
private def minimalLeftIdealColEquiv {B : Type*} [CStarAlgebra B] {n : ℕ} [NeZero n]
    (g : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] B) {p : B}
    (hright : ∀ x : B, x * p = x ↔ x * g (Matrix.single 0 0 1) = x) :
    (Fin n → ℂ) ≃ₗ[ℂ] minimalLeftIdeal p where
  toFun v := ⟨g (Matrix.of fun i j ↦ if j = 0 then v i else 0), by
    rw [mem_minimalLeftIdeal, hright, ← map_mul]
    congr 1; ext i j
    by_cases hj : j = 0
    · subst hj; simp [Matrix.mul_apply, Matrix.single_apply]
    · simp [Matrix.mul_apply, hj, Ne.symm hj]⟩
  invFun x i := g.symm x.1 i 0
  left_inv v := by ext i; simp
  right_inv x := by
    ext1
    apply g.symm.injective
    rw [AlgEquiv.symm_apply_apply]
    have hx0 : g.symm x.1 * Matrix.single 0 0 1 = g.symm x.1 := by
      apply g.injective
      simpa only [map_mul, AlgEquiv.apply_symm_apply] using (hright x.1).mp x.2
    have hmat : (Matrix.of fun r s ↦ if s = 0 then g.symm x.1 r 0 else 0) =
        g.symm x.1 * Matrix.single 0 0 1 := by
      ext i j
      by_cases hj : j = 0
      · subst hj; simp [Matrix.mul_apply, Matrix.single_apply]
      · simp [Matrix.mul_apply, hj, Ne.symm hj]
    exact hmat.trans hx0
  map_add' v₁ v₂ := by
    ext1; dsimp; rw [← map_add]; congr 1; ext i j; by_cases hj : j = 0 <;> simp [hj]
  map_smul' r v := by
    ext1; dsimp; rw [← map_smul]; congr 1; ext i j; by_cases hj : j = 0 <;> simp [hj]

/-- Left multiplication on the Hilbert space `minimalLeftIdeal p` realizes a simple C⋆-algebra `B`
with an `n × n` matrix `AlgEquiv` as `Matrix (Fin n) (Fin n) ℂ` via a `StarAlgEquiv`. -/
private theorem nonempty_starAlgEquiv_of_minimal_isStarProjection {B : Type*} [CStarAlgebra B]
    {n : ℕ} [NeZero n] (g : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] B) {p : B} {ψ : B →ₗ[ℂ] ℂ}
    (hp : IsStarProjection p) (hp_ne : p ≠ 0) (hp_corner : ∀ b : B, p * b * p = ψ b • p)
    (hright : ∀ x : B, x * p = x ↔ x * g (Matrix.single 0 0 1) = x) :
    Nonempty (B ≃⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ) := by
  let L := minimalLeftIdeal p
  let _ : InnerProductSpace ℂ L := minimalLeftIdealInnerProductSpace hp hp_ne hp_corner
  have hinner_def (x y : L) : inner ℂ x y = ψ (star (x : B) * (y : B)) := rfl
  have hcoeff_eq {z₁ z₂ : ℂ} (hz : z₁ • p = z₂ • p) : z₁ = z₂ :=
    sub_eq_zero.mp ((smul_eq_zero.mp (by rw [sub_smul, hz, sub_self])).resolve_right hp_ne)
  let colEquiv := minimalLeftIdealColEquiv g hright
  have : FiniteDimensional ℂ L := Module.Finite.equiv colEquiv
  have hfinL : Module.finrank ℂ L = n := by simpa using colEquiv.symm.finrank_eq
  have : CompleteSpace L := FiniteDimensional.completeSpace ℂ L
  let leftMulCLM (b : B) : L →L[ℂ] L :=
    LinearMap.toContinuousLinearMap
      { toFun x := ⟨b * x.1, by rw [mem_minimalLeftIdeal, mul_assoc, mem_minimalLeftIdeal.mp x.2]⟩
        map_add' x y := by ext1; exact mul_add b x.1 y.1
        map_smul' r x := by ext1; exact mul_smul_comm r b x.1 }
  have hleftMul_val (b : B) (x : L) : ((leftMulCLM b x : L) : B) = b * x.1 := rfl
  let π : B →⋆ₐ[ℂ] (L →L[ℂ] L) :=
    { toFun := leftMulCLM
      map_one' := by ext x : 2; exact one_mul x.1
      map_mul' a b := by ext x : 2; exact mul_assoc a b x.1
      map_zero' := by ext x : 2; exact zero_mul x.1
      map_add' a b := by ext x : 2; exact add_mul a b x.1
      commutes' r := by ext x : 2; exact (Algebra.smul_def r x.1).symm
      map_star' b := by
        refine (ContinuousLinearMap.eq_adjoint_iff (leftMulCLM (star b)) (leftMulCLM b)).mpr
          fun x y ↦ hcoeff_eq ?_
        rw [hinner_def, hinner_def,
          ← minimalLeftIdeal_star_mul hp hp_corner (leftMulCLM (star b) x) y,
          ← minimalLeftIdeal_star_mul hp hp_corner x (leftMulCLM b y),
          hleftMul_val, hleftMul_val, star_mul, star_star, mul_assoc] }
  have : Nontrivial L := ⟨⟨⟨p, hp.isIdempotentElem.eq⟩, 0, fun h ↦ hp_ne (congrArg Subtype.val h)⟩⟩
  have hcomp_inj : Function.Injective (π.toAlgHom.comp g.toAlgHom).toRingHom := RingHom.injective _
  have hπ_inj : Function.Injective π := fun a b hab ↦ by
    rw [← g.apply_symm_apply a, ← g.apply_symm_apply b]
    exact congrArg g (hcomp_inj (by simpa using hab))
  let matEquiv : (L →L[ℂ] L) ≃⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    (stdOrthonormalBasis ℂ L).repr.conjStarAlgEquiv.trans <|
      Matrix.toEuclideanCLM.symm.trans <|
        CStarMatrix.ofMatrixStarAlgEquiv.trans <|
          (CStarMatrix.reindexₐ ℂ ℂ (finCongr hfinL)).trans
            CStarMatrix.ofMatrixStarAlgEquiv.symm
  have : FiniteDimensional ℂ B := Module.Finite.equiv g.toLinearEquiv
  have : FiniteDimensional ℂ (L →L[ℂ] L) :=
    Module.Finite.equiv matEquiv.toAlgEquiv.toLinearEquiv.symm
  have hfin_eq : Module.finrank ℂ B = Module.finrank ℂ (L →L[ℂ] L) :=
    g.symm.toLinearEquiv.finrank_eq.trans matEquiv.toAlgEquiv.toLinearEquiv.finrank_eq.symm
  have hπ_surj : Function.Surjective π.toAlgHom.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin_eq).mp hπ_inj
  exact ⟨(StarAlgEquiv.ofBijective π ⟨hπ_inj, hπ_surj⟩).trans matEquiv⟩

/-- A unital complex C⋆-algebra that is algebra-isomorphic (without assuming compatibility with
`star`) to `Matrix m m ℂ` is `⋆`-algebra isomorphic to `Matrix m m ℂ`. -/
theorem nonempty_starAlgEquiv_matrix_of_algEquiv {B m : Type*} [CStarAlgebra B] [Fintype m]
    [DecidableEq m] (g : Matrix m m ℂ ≃ₐ[ℂ] B) :
    Nonempty (B ≃⋆ₐ[ℂ] Matrix m m ℂ) := by
  set n := Fintype.card m
  let em : m ≃ Fin n := Fintype.equivFin m
  let gFin : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] B :=
    (Matrix.reindexAlgEquiv ℂ ℂ em.symm).trans g
  have hmatEquiv : Matrix (Fin n) (Fin n) ℂ ≃⋆ₐ[ℂ] Matrix m m ℂ :=
    CStarMatrix.ofMatrixStarAlgEquiv.trans <|
      (CStarMatrix.reindexₐ ℂ ℂ em.symm).trans CStarMatrix.ofMatrixStarAlgEquiv.symm
  rcases eq_or_ne n 0 with hn | hn
  · have : IsEmpty (Fin n) := hn ▸ Fin.isEmpty
    have : Subsingleton (Matrix (Fin n) (Fin n) ℂ) := inferInstance
    have : Subsingleton B := gFin.symm.toEquiv.subsingleton
    exact ⟨({ gFin.symm.toRingEquiv with
      map_star' := fun _ ↦ Subsingleton.elim _ _
      map_smul' := fun _ _ ↦ Subsingleton.elim _ _ } :
        B ≃⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ).trans hmatEquiv⟩
  · have : NeZero n := ⟨hn⟩
    obtain ⟨p, ψ, hp, hp_ne, hp_corner, hright⟩ := exists_minimal_isStarProjection_of_algEquiv gFin
    obtain ⟨eFin⟩ :=
      nonempty_starAlgEquiv_of_minimal_isStarProjection gFin hp hp_ne hp_corner hright
    exact ⟨eFin.trans hmatEquiv⟩

/-- A unital complex C⋆-algebra that is algebra-isomorphic to `Matrix m m ℂ` is `⋆`-algebra
isomorphic to `CStarMatrix m m ℂ`. -/
theorem nonempty_starAlgEquiv_cstarMatrix_of_algEquiv {B m : Type*} [CStarAlgebra B] [Fintype m]
    [DecidableEq m] (g : Matrix m m ℂ ≃ₐ[ℂ] B) :
    Nonempty (B ≃⋆ₐ[ℂ] CStarMatrix m m ℂ) := by
  obtain ⟨e⟩ := nonempty_starAlgEquiv_matrix_of_algEquiv g
  exact ⟨e.trans CStarMatrix.ofMatrixStarAlgEquiv⟩

end SingleBlock

/-! ### Multi-block decomposition of finite-dimensional complex C⋆-algebras -/

section MultiBlock

/-- The principal two-sided `⋆`-ideal `{a : A | z * a = a}` cut out by a central star projection
`z` in a unital C⋆-algebra `A`. -/
private def centralProjectionSubalgebra {A : Type u} [CStarAlgebra A] (z : A)
    (hz_comm : ∀ a : A, Commute z a) (hz_proj : IsStarProjection z) :
    NonUnitalStarSubalgebra ℂ A where
  carrier := {a : A | z * a = a}
  add_mem' {a b} ha hb := by dsimp at ha hb ⊢; rw [mul_add, ha, hb]
  zero_mem' := mul_zero z
  mul_mem' {a b} ha _ := by dsimp at ha ⊢; rw [← mul_assoc, ha]
  smul_mem' r {a} ha := by dsimp at ha ⊢; rw [mul_smul_comm, ha]
  star_mem' {a} ha := by
    dsimp at ha ⊢
    calc
      z * star a = star a * z := hz_comm (star a)
      _ = star (z * a) := by rw [star_mul, hz_proj.isSelfAdjoint.star_eq]
      _ = star a := by rw [ha]

@[simp]
private theorem mem_centralProjectionSubalgebra {A : Type u} [CStarAlgebra A] {z a : A}
    (hz_comm : ∀ b : A, Commute z b) (hz_proj : IsStarProjection z) :
    a ∈ centralProjectionSubalgebra z hz_comm hz_proj ↔ z * a = a :=
  Iff.rfl

/-- Decompose a unital C⋆-algebra `A` as the direct product `∀ i, centralProjectionSubalgebra (z i)`
along a finite family of pairwise orthogonal central star projections summing to `1`. -/
private def starAlgEquivPiCentralProjectionSubalgebra {A : Type u} [CStarAlgebra A] {ι : Type*}
    [Fintype ι] (z : ι → A) (hz_comm : ∀ i a, Commute (z i) a)
    (hz_proj : ∀ i, IsStarProjection (z i)) (hz_ortho : Pairwise fun i j ↦ z i * z j = 0)
    (hz_sum : ∑ i, z i = 1) :
    A ≃⋆ₐ[ℂ] ∀ i, centralProjectionSubalgebra (z i) (hz_comm i) (hz_proj i) where
  toFun a i := ⟨z i * a, by
    rw [mem_centralProjectionSubalgebra, ← mul_assoc, (hz_proj i).isIdempotentElem.eq]⟩
  invFun y := ∑ i, (y i).1
  left_inv a := by simp [← Finset.sum_mul, hz_sum]
  right_inv y := by
    ext i : 2
    dsimp
    rw [Finset.mul_sum]
    have hyi : z i * (y i).1 = (y i).1 := (y i).2
    refine (Finset.sum_eq_single i (fun j _ hji ↦ ?_) (by simp)).trans hyi
    have hyj : z j * (y j).1 = (y j).1 := (y j).2
    rw [← hyj, ← mul_assoc, hz_ortho hji.symm, zero_mul]
  map_mul' a b := by
    ext i : 2
    dsimp
    calc
      z i * (a * b) = (z i * z i) * (a * b) := by rw [(hz_proj i).isIdempotentElem.eq]
      _ = z i * (z i * a) * b := by simp only [mul_assoc]
      _ = z i * (a * z i) * b := by rw [(hz_comm i a).eq]
      _ = (z i * a) * (z i * b) := by simp only [mul_assoc]
  map_add' a b := by ext i : 2; exact mul_add (z i) a b
  map_star' a := by
    ext i : 2
    dsimp
    calc
      z i * star a = star a * z i := hz_comm i (star a)
      _ = star (z i * a) := by rw [star_mul, (hz_proj i).isSelfAdjoint.star_eq]
  map_smul' r a := by ext i : 2; exact mul_smul_comm r (z i) a

/-- Auxiliary multi-block decomposition for a unital finite-dimensional complex C⋆-algebra. -/
private theorem nonempty_cstarWedderburnPresentation_of_unital (A : Type u) [CStarAlgebra A]
    [FiniteDimensional ℂ A] : Nonempty (CStarWedderburnPresentation A) := by
  have : IsArtinianRing A := .of_finite ℂ A
  have : IsSemisimpleRing A := TauCeti.isSemisimpleRing_of_isProperStar A
  let P₀ := IsSemisimpleRing.splitWedderburnAlgebraPresentation ℂ A
  let z (i : Fin P₀.blockCount) : A := P₀.equiv.symm (Pi.single i 1)
  have hz_comm (i : Fin P₀.blockCount) (a : A) : Commute (z i) a := by
    rw [commute_iff_eq]; apply P₀.equiv.injective; dsimp only [z]
    rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
    ext j; by_cases hij : i = j; · subst hij; simp
    · simp [hij]
  have hz_proj (i : Fin P₀.blockCount) : IsStarProjection (z i) :=
    isStarProjection_iff_isIdempotentElem_and_isStarNormal.mpr
      ⟨by rw [IsIdempotentElem]; dsimp only [z]; rw [← map_mul, ← Pi.single_mul, one_mul],
        ⟨(hz_comm i (star (z i))).symm⟩⟩
  have hz_ortho : Pairwise fun i j ↦ z i * z j = 0 := fun i j hij ↦ by
    apply P₀.equiv.injective; dsimp only [z]
    rw [map_mul, map_zero, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    ext k; by_cases hik : i = k; · subst hik; simp [hij]
    · simp [hik]
  have hz_sum : ∑ i : Fin P₀.blockCount, z i = 1 := by
    apply P₀.equiv.injective
    rw [map_sum, map_one]
    simp only [z, AlgEquiv.apply_symm_apply]
    exact Finset.univ_sum_single 1
  let I (i : Fin P₀.blockCount) := centralProjectionSubalgebra (z i) (hz_comm i) (hz_proj i)
  have hI_closed (i : Fin P₀.blockCount) : IsClosed (I i : Set A) :=
    isClosed_eq (by fun_prop) continuous_id
  let _ (i : Fin P₀.blockCount) : NonUnitalCStarAlgebra (I i) :=
    NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (I i)
  let zSub (i : Fin P₀.blockCount) : I i := ⟨z i, (hz_proj i).isIdempotentElem.eq⟩
  have hzSub_unit (i : Fin P₀.blockCount) (x : I i) : zSub i * x = x ∧ x * zSub i = x :=
    ⟨Subtype.ext x.2, Subtype.ext ((hz_comm i x.1).symm.trans x.2)⟩
  let _ (i : Fin P₀.blockCount) : IsUnital (I i) := ⟨zSub i, hzSub_unit i⟩
  let _ (i : Fin P₀.blockCount) : CStarAlgebra (I i) := IsUnital.toCStarAlgebra
  have hblock (i : Fin P₀.blockCount) :
      Nonempty (I i ≃⋆ₐ[ℂ] CStarMatrix (Fin (P₀.degree i)) (Fin (P₀.degree i)) ℂ) := by
    have hI_one : (1 : I i) = zSub i := ((hzSub_unit i 1).1).symm.trans (mul_one (zSub i))
    let g_i : Matrix (Fin (P₀.degree i)) (Fin (P₀.degree i)) ℂ ≃ₐ[ℂ] I i :=
      { toFun M := ⟨P₀.equiv.symm (Pi.single i M), by
          rw [mem_centralProjectionSubalgebra]
          dsimp only [z]; rw [← map_mul, ← Pi.single_mul, one_mul]⟩
        invFun x := P₀.equiv x.1 i
        left_inv M := by simp
        right_inv x := by
          ext1; dsimp; apply P₀.equiv.injective; rw [AlgEquiv.apply_symm_apply]
          have hx : P₀.equiv x.1 = Pi.single i 1 * P₀.equiv x.1 := by
            simpa only [z, map_mul, AlgEquiv.apply_symm_apply] using congrArg P₀.equiv x.2.symm
          rw [hx]; ext j; by_cases hij : i = j; · subst hij; simp
          · simp [hij]
        map_mul' M N := by
          ext1; dsimp
          have hsingle : Pi.single (M := fun j ↦ Matrix (Fin (P₀.degree j)) (Fin (P₀.degree j)) ℂ)
              i (M * N) = Pi.single i M * Pi.single i N := by
            ext j; by_cases hij : i = j; · subst hij; simp
            · simp [hij]
          rw [hsingle, map_mul]
        map_add' M N := by ext1; dsimp; rw [Pi.single_add, map_add]
        commutes' r := by
          have hr : algebraMap ℂ (I i) r = r • zSub i := by
            rw [Algebra.algebraMap_eq_smul_one, hI_one]
          rw [hr]; ext1; dsimp [zSub, z]
          rw [← map_smul, ← Pi.single_smul, Algebra.algebraMap_eq_smul_one] }
    exact nonempty_starAlgEquiv_cstarMatrix_of_algEquiv g_i
  exact ⟨{
    blockCount := P₀.blockCount
    degree := P₀.degree
    equiv := (starAlgEquivPiCentralProjectionSubalgebra z hz_comm hz_proj hz_ortho hz_sum).trans
      (StarAlgEquiv.piCongrRight fun i ↦ (hblock i).some) }⟩

/-- Every complex C⋆-algebra whose closed balls are compact admits a `CStarWedderburnPresentation`
as a finite direct product of full complex matrix C⋆-algebras of positive degree. -/
theorem nonempty_cstarWedderburnPresentation_of_properSpace (A : Type u) [NonUnitalCStarAlgebra A]
    [ProperSpace A] : Nonempty (CStarWedderburnPresentation A) := by
  let : IsUnital A := isUnital_of_properSpace A
  let : CStarAlgebra A := IsUnital.toCStarAlgebra
  have : FiniteDimensional ℂ A := .of_locallyCompactSpace ℂ
  exact nonempty_cstarWedderburnPresentation_of_unital A

/-- **Matrix-block decomposition of finite-dimensional complex C⋆-algebras**: every
finite-dimensional complex C⋆-algebra (unital or not) admits a `CStarWedderburnPresentation`. -/
theorem nonempty_cstarWedderburnPresentation (A : Type u) [NonUnitalCStarAlgebra A]
    [FiniteDimensional ℂ A] : Nonempty (CStarWedderburnPresentation A) := by
  have := FiniteDimensional.proper ℂ A
  exact nonempty_cstarWedderburnPresentation_of_properSpace A

/-- Choose a `CStarWedderburnPresentation` of a finite-dimensional complex C⋆-algebra. -/
noncomputable def cstarWedderburnPresentation (A : Type u) [NonUnitalCStarAlgebra A]
    [FiniteDimensional ℂ A] : CStarWedderburnPresentation A :=
  Classical.choice (nonempty_cstarWedderburnPresentation A)

/-- Existential form of the finite-dimensional C⋆-algebra structure theorem: every
finite-dimensional complex C⋆-algebra is `⋆`-isomorphic to a finite product of full complex matrix
C⋆-algebras of positive degree. -/
theorem exists_starAlgEquiv_pi_cstarMatrix (A : Type u) [NonUnitalCStarAlgebra A]
    [FiniteDimensional ℂ A] :
    ∃ (k : ℕ) (n : Fin k → ℕ) (_ : ∀ i, NeZero (n i)),
      Nonempty (A ≃⋆ₐ[ℂ] ∀ i, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) := by
  obtain ⟨P⟩ := nonempty_cstarWedderburnPresentation A
  exact ⟨P.blockCount, P.degree, P.instNeZeroDegree, ⟨P.equiv⟩⟩

/-- A finite-dimensional complex C⋆-algebra is commutative if and only if it is `⋆`-algebra
isomorphic to `Fin (Module.finrank ℂ A) → ℂ`. -/
theorem isMulCommutative_iff_nonempty_starAlgEquiv_fun (A : Type u) [NonUnitalCStarAlgebra A]
    [FiniteDimensional ℂ A] :
    IsMulCommutative A ↔ Nonempty (A ≃⋆ₐ[ℂ] (Fin (Module.finrank ℂ A) → ℂ)) := by
  refine ⟨fun _ ↦ ?_, fun ⟨e⟩ ↦ ⟨⟨fun a b ↦ e.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩⟩
  let P := cstarWedderburnPresentation A
  have hdeg : ∀ i, P.degree i = 1 := P.isMulCommutative_iff_forall_degree_eq_one.mp inferInstance
  have hdim : Module.finrank ℂ A = P.blockCount := by
    rw [P.finrank_eq_sum_sq]
    simp [hdeg]
  exact ⟨(P.equivFunOfForallDegreeEqOne hdeg).trans
    (StarAlgEquiv.piCongrLeft ℂ (fun _ ↦ ℂ) (finCongr hdim.symm))⟩

end MultiBlock

end CStarAlgebra
