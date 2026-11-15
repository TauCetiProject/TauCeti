/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Algebra.Star.Pi
public import TauCeti.Algebra.Star.Projection.Family
public import TauCeti.RingTheory.Semisimple.Wedderburn.Presentation

import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.Topology.MetricSpace.ProperSpace
import TauCeti.Algebra.Matrix.Pi
import TauCeti.Analysis.CStarAlgebra.CStarMatrix
import TauCeti.Analysis.CStarAlgebra.MinimalProjection
import TauCeti.RingTheory.Semisimple.Star
import TauCeti.RingTheory.Semisimple.Wedderburn.Uniqueness

/-!
# Block decomposition of finite-dimensional complex C⋆-algebras

Every finite-dimensional (equivalently, locally compact) complex C⋆-algebra, even if presented
without a unit, is automatically unital and `⋆`-isomorphic to a finite direct product of full
complex matrix C⋆-algebras:
`A ≃⋆ₐ[ℂ] ∀ i : Fin k, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ` with `0 < n i`.

The proof proceeds in three stages:

1. **Automatic unitality (`CStarAlgebra.isUnital_of_locallyCompactSpace`)**: a locally compact
   complex `NonUnitalCStarAlgebra` is proper, so its canonical increasing approximate unit lies in
   the compact closed unit ball and admits a cluster point. Hausdorffness and separate continuity of
   multiplication force any cluster point to be a two-sided multiplicative identity, and the
   involution forces it to be a star projection.
2. **Single-block upgrade (`CStarAlgebra.nonempty_starAlgEquiv_matrix_of_algEquiv`)**: if a unital
   C⋆-algebra `B` is algebra-isomorphic (without assuming compatibility with `star`) to `Mₙ(ℂ)`,
   transporting a minimal matrix idempotent `E₀₀` produces a rank-one idempotent `q ∈ B`. Using
   `IsIdempotentElem.exists_isStarProjection_of_forall_mul_eq_smul` and
   `IsStarProjection.leftMulStarAlgHom`, normalizing `star q * q` yields a minimal star projection
   `p` whose left ideal `{x : B | x * p = x}` is an `n`-dimensional complex Hilbert space on which
   left multiplication identifies `B` `⋆`-isomorphically with `Mₙ(ℂ)`.
3. **Multi-block Artin--Wedderburn upgrade (`CStarAlgebra.nonempty_cstarWedderburnPresentation`)**:
   a finite-dimensional unital C⋆-algebra has a proper involution, so it is semisimple by
   `TauCeti.isSemisimpleRing_of_isProperStar` and splits algebraically over `ℂ` into matrix blocks.
   Each block's central idempotent is normal in `A`, hence automatically a star projection by
   `isStarProjection_iff_isIdempotentElem_and_isStarNormal`. Cutting `A` along these central star
   projections via `TauCeti.IsCompleteOrthogonalProjectionFamily.starAlgEquivPiOfIsMulCentral`
   decomposes `A` as a `⋆`-algebra product of closed unital C⋆-ideals, each algebra-isomorphic (and
   therefore `⋆`-isomorphic by Stage 2) to a matrix algebra.

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

* `CStarAlgebra.existsUnique_isStarProjection_and_forall_mul_eq_and_mul_eq_of_locallyCompactSpace`,
  `CStarAlgebra.isUnital_of_locallyCompactSpace`, `CStarAlgebra.isUnital_of_finiteDimensional`:
  every locally compact (equivalently, finite-dimensional) complex C⋆-algebra has a unique
  two-sided multiplicative identity, which is a star projection.
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

/-! ### Automatic unitality of locally compact and finite-dimensional C⋆-algebras -/

section AutomaticUnit

/-- Every locally compact complex C⋆-algebra admits a unique two-sided multiplicative identity. -/
theorem existsUnique_forall_mul_eq_and_mul_eq_of_locallyCompactSpace (A : Type*)
    [NonUnitalCStarAlgebra A] [LocallyCompactSpace A] :
    ∃! e : A, ∀ a : A, e * a = a ∧ a * e = a := by
  have : ProperSpace A := .of_locallyCompactSpace ℂ
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

/-- In a locally compact complex C⋆-algebra, the unique two-sided multiplicative identity is a star
projection. -/
theorem existsUnique_isStarProjection_and_forall_mul_eq_and_mul_eq_of_locallyCompactSpace
    (A : Type*) [NonUnitalCStarAlgebra A] [LocallyCompactSpace A] :
    ∃! e : A, IsStarProjection e ∧ ∀ a : A, e * a = a ∧ a * e = a := by
  obtain ⟨e, he, huniq⟩ := existsUnique_forall_mul_eq_and_mul_eq_of_locallyCompactSpace A
  have hsa : IsSelfAdjoint e := by
    rw [IsSelfAdjoint, ← (he (star e)).1]
    simpa only [star_mul, star_star] using congrArg star (he (star e)).1
  exact ⟨e, ⟨⟨(he e).1, hsa⟩, he⟩, fun e' he' ↦ huniq e' he'.2⟩

/-- Every locally compact complex C⋆-algebra is unital (`IsUnital`). -/
theorem isUnital_of_locallyCompactSpace (A : Type*) [NonUnitalCStarAlgebra A]
    [LocallyCompactSpace A] : IsUnital A := by
  obtain ⟨e, he, -⟩ := existsUnique_forall_mul_eq_and_mul_eq_of_locallyCompactSpace A
  exact ⟨e, he⟩

/-- Every finite-dimensional complex C⋆-algebra is unital, even if given only as a
`NonUnitalCStarAlgebra`. -/
theorem isUnital_of_finiteDimensional (A : Type*) [NonUnitalCStarAlgebra A]
    [FiniteDimensional ℂ A] : IsUnital A := by
  have := FiniteDimensional.proper ℂ A
  exact isUnital_of_locallyCompactSpace A

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
  refine (CStarMatrix.ofMatrix.eq_symm_apply).mpr ?_
  rw [CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv]
  exact (CStarMatrix.ofMatrixStarAlgEquiv.apply_symm_apply (P.equiv a i)).symm

@[simp]
theorem matrixStarAlgEquiv_symm_apply
    (x : ∀ i, Matrix (Fin (P.degree i)) (Fin (P.degree i)) ℂ) :
    P.matrixStarAlgEquiv.symm x = P.equiv.symm fun i ↦ CStarMatrix.ofMatrix (x i) := by
  simp only [matrixStarAlgEquiv, StarAlgEquiv.symm_trans_apply, StarAlgEquiv.piCongrRight_symm,
    StarAlgEquiv.symm_symm]
  refine congrArg P.equiv.symm (funext fun i ↦ ?_)
  rw [StarAlgEquiv.piCongrRight_apply, ← CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv]

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

/-- The `i`-th minimal central star projection of `A` associated with the presentation `P`,
obtained by pulling back the unit of the `i`-th matrix block. -/
def centralProjection (i : Fin P.blockCount) : A :=
  P.equiv.symm (Pi.single (M := fun j ↦ CStarMatrix (Fin (P.degree j)) (Fin (P.degree j)) ℂ) i 1)

theorem centralProjection_def (i : Fin P.blockCount) :
    P.centralProjection i =
      P.equiv.symm
        (Pi.single (M := fun j ↦ CStarMatrix (Fin (P.degree j)) (Fin (P.degree j)) ℂ) i 1) :=
  (rfl)

@[simp]
theorem equiv_centralProjection (i : Fin P.blockCount) :
    P.equiv (P.centralProjection i) =
      Pi.single (M := fun j ↦ CStarMatrix (Fin (P.degree j)) (Fin (P.degree j)) ℂ) i 1 :=
  P.equiv.apply_symm_apply _

@[simp]
theorem matrixStarAlgEquiv_centralProjection (i : Fin P.blockCount) :
    P.matrixStarAlgEquiv (P.centralProjection i) =
      Pi.single (M := fun j ↦ Matrix (Fin (P.degree j)) (Fin (P.degree j)) ℂ) i 1 := by
  ext j
  simp only [matrixStarAlgEquiv, StarAlgEquiv.trans_apply, equiv_centralProjection,
    StarAlgEquiv.piCongrRight_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

/-- Each `P.centralProjection i` is a star projection. -/
@[simp]
theorem isStarProjection_centralProjection (i : Fin P.blockCount) :
    IsStarProjection (P.centralProjection i) := by
  have hsingle : IsStarProjection
      (Pi.single (M := fun j ↦ CStarMatrix (Fin (P.degree j)) (Fin (P.degree j)) ℂ) i 1) :=
    ⟨by rw [IsIdempotentElem, ← Pi.single_mul, one_mul],
      by rw [IsSelfAdjoint, ← Pi.single_star, star_one]⟩
  exact hsingle.map P.equiv.symm

@[simp]
theorem star_centralProjection (i : Fin P.blockCount) :
    star (P.centralProjection i) = P.centralProjection i :=
  (P.isStarProjection_centralProjection i).isSelfAdjoint.star_eq

@[simp]
theorem centralProjection_mul_self (i : Fin P.blockCount) :
    P.centralProjection i * P.centralProjection i = P.centralProjection i :=
  (P.isStarProjection_centralProjection i).isIdempotentElem.eq

/-- Every minimal central projection of `P` commutes with all elements of `A`. -/
theorem commute_centralProjection (i : Fin P.blockCount) (a : A) :
    Commute (P.centralProjection i) a := by
  rw [commute_iff_eq]
  apply EquivLike.injective P.equiv
  rw [map_mul, map_mul, equiv_centralProjection, ← Pi.single_mul_left, ← Pi.single_mul_right,
    one_mul, mul_one]

/-- Every minimal central projection of `P` is multiplicatively central in `A`. -/
@[simp]
theorem isMulCentral_centralProjection (i : Fin P.blockCount) :
    IsMulCentral (P.centralProjection i) where
  comm := P.commute_centralProjection i
  left_assoc b c := EquivLike.injective P.equiv <| by simp [map_mul, mul_assoc]
  right_assoc a b := EquivLike.injective P.equiv <| by simp [map_mul, mul_assoc]

/-- When every block of `P` has degree `1`, collapsing the `1 × 1` matrix blocks gives a
`⋆`-algebra equivalence `A ≃⋆ₐ[ℂ] (Fin P.blockCount → ℂ)`. -/
def equivFunOfForallDegreeEqOne (h : ∀ i, P.degree i = 1) :
    A ≃⋆ₐ[ℂ] (Fin P.blockCount → ℂ) :=
  P.equiv.trans <| StarAlgEquiv.piCongrRight fun i ↦
    (CStarMatrix.reindexₐ ℂ ℂ (finCongr (h i))).trans (CStarMatrix.toOneByOne (Fin 1) ℂ ℂ).symm

@[simp]
theorem equivFunOfForallDegreeEqOne_apply (h : ∀ i, P.degree i = 1) (a : A)
    (i : Fin P.blockCount) :
    P.equivFunOfForallDegreeEqOne h a i = P.equiv a i 0 0 := by
  simp only [equivFunOfForallDegreeEqOne, StarAlgEquiv.trans_apply, StarAlgEquiv.piCongrRight_apply]
  change (CStarMatrix.toOneByOne (Fin 1) ℂ ℂ).symm
    (CStarMatrix.reindexₐ ℂ ℂ (finCongr (h i)) (P.equiv a i)) = P.equiv a i 0 0
  have h0 : (finCongr (h i)).symm (0 : Fin 1) = 0 := Fin.ext (by simp)
  rw [CStarMatrix.toOneByOne_symm_apply, Fin.default_eq_zero, CStarMatrix.reindexₐ_apply_apply, h0]

@[simp]
theorem equivFunOfForallDegreeEqOne_symm_apply (h : ∀ i, P.degree i = 1)
    (f : Fin P.blockCount → ℂ) :
    (P.equivFunOfForallDegreeEqOne h).symm f =
      P.equiv.symm fun i ↦ CStarMatrix.ofMatrix (Matrix.of fun _ _ ↦ f i) := by
  simp only [equivFunOfForallDegreeEqOne, StarAlgEquiv.symm_trans_apply,
    StarAlgEquiv.piCongrRight_symm]
  refine congrArg P.equiv.symm (funext fun i ↦ ?_)
  rw [StarAlgEquiv.piCongrRight_apply]
  refine CStarMatrix.ext fun r s ↦ ?_
  change (CStarMatrix.reindexₐ ℂ ℂ (finCongr (h i))).symm
    (CStarMatrix.toOneByOne (Fin 1) ℂ ℂ (f i)) r s =
    (CStarMatrix.ofMatrix (Matrix.of fun _ _ ↦ f i)) r s
  rw [← CStarMatrix.reindexₐ_symm, CStarMatrix.reindexₐ_apply_apply]
  simp

@[simp]
theorem equivFunOfForallDegreeEqOne_centralProjection (h : ∀ i, P.degree i = 1)
    (i : Fin P.blockCount) :
    P.equivFunOfForallDegreeEqOne h (P.centralProjection i) = Pi.single i 1 := by
  ext j
  rw [equivFunOfForallDegreeEqOne_apply, equiv_centralProjection]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

/-- `A` is multiplicatively commutative if and only if every block in `P` has degree `1`. -/
theorem isMulCommutative_iff_forall_degree_eq_one :
    IsMulCommutative A ↔ ∀ i, P.degree i = 1 := by
  refine ⟨fun hcomm i ↦ ?_, fun hdeg ↦ ⟨⟨fun a b ↦ ?_⟩⟩⟩
  · by_contra hne
    have hgt : 1 < P.degree i := lt_of_le_of_ne (P.one_le_degree i) (Ne.symm hne)
    have : Nontrivial (Fin (P.degree i)) := ⟨⟨0, P.degree_pos i⟩, ⟨1, hgt⟩, by simp⟩
    refine CStarMatrix.not_isMulCommutative (m := Fin (P.degree i)) (A := ℂ) ⟨⟨fun M N ↦ ?_⟩⟩
    have hxy := hcomm.is_comm.comm (P.equiv.symm (Pi.single i M)) (P.equiv.symm (Pi.single i N))
    simpa only [map_mul, StarAlgEquiv.apply_symm_apply, Pi.mul_apply, Pi.single_eq_same] using
      congrFun (congrArg P.equiv hxy) i
  · apply (P.equivFunOfForallDegreeEqOne hdeg).injective
    rw [map_mul, map_mul, mul_comm]

end Minimal

section AddZeroClass

/-- Each `P.centralProjection i` is nonzero. -/
theorem centralProjection_ne_zero {A : Type u} [AddZeroClass A] [Mul A] [SMul ℂ A] [Star A]
    (P : CStarWedderburnPresentation A) (i : Fin P.blockCount) : P.centralProjection i ≠ 0 := by
  intro h
  have h1 : (1 : CStarMatrix (Fin (P.degree i)) (Fin (P.degree i)) ℂ) = 0 := by
    simpa only [equiv_centralProjection, Pi.single_eq_same, map_zero, Pi.zero_apply] using
      congrFun (congrArg P.equiv h) i
  exact one_ne_zero h1

/-- Distinct minimal central projections of `P` multiply to zero. -/
theorem centralProjection_mul_of_ne {A : Type u} [AddZeroClass A] [Mul A] [SMul ℂ A] [Star A]
    (P : CStarWedderburnPresentation A) {i j : Fin P.blockCount} (hij : i ≠ j) :
    P.centralProjection i * P.centralProjection j = 0 := by
  apply EquivLike.injective P.equiv
  rw [map_mul, map_zero, equiv_centralProjection, equiv_centralProjection]
  exact (CompleteOrthogonalIdempotents.single
    (fun k : Fin P.blockCount ↦ CStarMatrix (Fin (P.degree k)) (Fin (P.degree k)) ℂ)).ortho hij

end AddZeroClass

/-- Minimal central projections of `P` are pairwise star-orthogonal. -/
theorem pairwise_isStarOrtho_centralProjection {A : Type u} [NonUnitalSemiring A] [StarRing A]
    [SMul ℂ A] (P : CStarWedderburnPresentation A) :
    Pairwise fun i j ↦ IsStarOrtho (P.centralProjection i) (P.centralProjection j) := by
  intro i j hij
  exact ⟨by rw [star_centralProjection, P.centralProjection_mul_of_ne hij],
    by rw [star_centralProjection, P.centralProjection_mul_of_ne hij.symm]⟩

section Dimension

/-- An algebra admitting a C⋆-Wedderburn presentation is finite-dimensional over `ℂ`. -/
theorem finiteDimensional {A : Type u} [AddCommGroup A] [Mul A] [Module ℂ A] [Star A]
    (P : CStarWedderburnPresentation A) : FiniteDimensional ℂ A :=
  let eLin : A ≃ₗ[ℂ] ∀ i, Matrix (Fin (P.degree i)) (Fin (P.degree i)) ℂ :=
    { P.matrixStarAlgEquiv.toAddEquiv with map_smul' := map_smul P.matrixStarAlgEquiv }
  Module.Finite.equiv eLin.symm

/-- **Dimension formula**: the complex dimension of `A` equals the sum of the squares of its matrix
block degrees. -/
theorem finrank_eq_sum_sq {A : Type u} [AddCommMonoid A] [Mul A] [Module ℂ A] [Star A]
    (P : CStarWedderburnPresentation A) : Module.finrank ℂ A = ∑ i, P.degree i ^ 2 :=
  let eLin : A ≃ₗ[ℂ] ∀ i, Matrix (Fin (P.degree i)) (Fin (P.degree i)) ℂ :=
    { P.matrixStarAlgEquiv.toAddEquiv with map_smul' := map_smul P.matrixStarAlgEquiv }
  eLin.finrank_eq.trans (TauCeti.finrank_pi_matrix ℂ P.degree)

/-- Every block degree satisfies `degree i ^ 2 ≤ Module.finrank ℂ A`. -/
theorem sq_degree_le_finrank {A : Type u} [AddCommMonoid A] [Mul A] [Module ℂ A] [Star A]
    (P : CStarWedderburnPresentation A) (i : Fin P.blockCount) :
    P.degree i ^ 2 ≤ Module.finrank ℂ A := by
  rw [P.finrank_eq_sum_sq]
  exact Finset.single_le_sum (f := fun j ↦ P.degree j ^ 2) (fun _ _ ↦ Nat.zero_le _)
    (Finset.mem_univ i)

/-- The number of blocks is at most `Module.finrank ℂ A`. -/
theorem blockCount_le_finrank {A : Type u} [AddCommMonoid A] [Mul A] [Module ℂ A] [Star A]
    (P : CStarWedderburnPresentation A) : P.blockCount ≤ Module.finrank ℂ A := by
  rw [P.finrank_eq_sum_sq]
  calc
    P.blockCount = ∑ _i : Fin P.blockCount, 1 := by simp
    _ ≤ ∑ i : Fin P.blockCount, P.degree i ^ 2 :=
      Finset.sum_le_sum fun i _ ↦ Nat.one_le_pow 2 (P.degree i) (P.degree_pos i)

end Dimension

section UnitalProjections

/-- In a unital algebra, the minimal central projections of `P` form a complete orthogonal
projection family summing to `1`. -/
theorem isCompleteOrthogonalProjectionFamily_centralProjection {A : Type u} [Semiring A]
    [SMul ℂ A] [Star A] (P : CStarWedderburnPresentation A) :
    IsCompleteOrthogonalProjectionFamily P.centralProjection := by
  rw [isCompleteOrthogonalProjectionFamily_iff]
  refine ⟨?_, P.isStarProjection_centralProjection⟩
  have hsingle : CompleteOrthogonalIdempotents
      (fun i : Fin P.blockCount ↦
        Pi.single (M := fun j ↦ CStarMatrix (Fin (P.degree j)) (Fin (P.degree j)) ℂ) i 1) :=
    CompleteOrthogonalIdempotents.single _
  exact hsingle.map P.equiv.symm.toRingEquiv.toRingHom

@[simp]
theorem sum_centralProjection {A : Type u} [Semiring A] [SMul ℂ A] [Star A]
    (P : CStarWedderburnPresentation A) : ∑ i, P.centralProjection i = 1 :=
  P.isCompleteOrthogonalProjectionFamily_centralProjection.complete

end UnitalProjections

section SemiringAlgebra

@[simp]
theorem centralProjection_mem_center {A : Type u} [Semiring A] [Algebra ℂ A] [Star A]
    (P : CStarWedderburnPresentation A) (i : Fin P.blockCount) :
    P.centralProjection i ∈ Subalgebra.center ℂ A :=
  Subalgebra.mem_center_iff.mpr fun a ↦ (P.commute_centralProjection i a).symm.eq

/-- The center of a unital algebra admitting a C⋆-Wedderburn presentation has complex dimension
equal to the number of matrix blocks. -/
theorem finrank_center {A : Type u} [Semiring A] [Algebra ℂ A] [Star A]
    (P : CStarWedderburnPresentation A) :
    Module.finrank ℂ (Subalgebra.center ℂ A) = P.blockCount := by
  rw [(Subalgebra.centerCongr P.matrixStarAlgEquiv.toAlgEquiv).toLinearEquiv.finrank_eq,
    TauCeti.finrank_center_pi_matrix ℂ P.degree, Fintype.card_fin]

end SemiringAlgebra

section SplitAlgebra

/-- Forget the involution and C⋆-matrix norm to obtain a split algebraic Wedderburn presentation
over `ℂ`. -/
@[expose]
def toSplitWedderburnAlgebraPresentation {A : Type u} [Ring A] [Algebra ℂ A] [Star A]
    (P : CStarWedderburnPresentation A) : SplitWedderburnAlgebraPresentation ℂ A where
  blockCount := P.blockCount
  degree := P.degree
  equiv := P.matrixStarAlgEquiv.toAlgEquiv

@[simp]
theorem toSplitWedderburnAlgebraPresentation_blockCount {A : Type u} [Ring A] [Algebra ℂ A]
    [Star A] (P : CStarWedderburnPresentation A) :
    P.toSplitWedderburnAlgebraPresentation.blockCount = P.blockCount :=
  (rfl)

@[simp]
theorem toSplitWedderburnAlgebraPresentation_degree {A : Type u} [Ring A] [Algebra ℂ A] [Star A]
    (P : CStarWedderburnPresentation A) :
    P.toSplitWedderburnAlgebraPresentation.degree = P.degree :=
  (rfl)

@[simp]
theorem toSplitWedderburnAlgebraPresentation_equiv {A : Type u} [Ring A] [Algebra ℂ A] [Star A]
    (P : CStarWedderburnPresentation A) :
    P.toSplitWedderburnAlgebraPresentation.equiv = P.matrixStarAlgEquiv.toAlgEquiv :=
  (rfl)

end SplitAlgebra

end CStarWedderburnPresentation

end TauCeti

/-! ### Upgrading algebraic matrix isomorphisms to `⋆`-isomorphisms -/

namespace CStarAlgebra

open TauCeti

section SingleBlock

/-- From an algebra isomorphism `Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] B` with `n ≠ 0`, extract a nonzero
minimal star projection `p : B` whose corner `p * b * p` is scalar along `p`, and whose left ideal
`{x : B | x * p = x}` coincides with `{x : B | x * g (Matrix.single 0 0 1) = x}`. -/
private theorem exists_minimal_isStarProjection_of_algEquiv {B : Type*} [CStarAlgebra B] {n : ℕ}
    [NeZero n] (g : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] B) :
    ∃ (p : B) (ψ : B →ₗ[ℂ] ℂ),
      IsStarProjection p ∧ p ≠ 0 ∧ (∀ b : B, p * b * p = ψ b • p) ∧
      ∀ x : B, x * p = x ↔ x * g (Matrix.single 0 0 1) = x := by
  -- Transport `E₀₀ = Matrix.single 0 0 1` along `g` to obtain a nonzero scalar-corner idempotent.
  let e₀ : Matrix (Fin n) (Fin n) ℂ := Matrix.single 0 0 1
  have he₀_ne : e₀ ≠ 0 := fun h ↦
    one_ne_zero (by simpa [e₀] using congrFun (congrFun h 0) 0 : (1 : ℂ) = 0)
  have hq_idem : IsIdempotentElem (g e₀) := by rw [IsIdempotentElem, ← map_mul]; simp [e₀]
  have hq_ne : g e₀ ≠ 0 := fun h ↦ he₀_ne (g.injective (h.trans (map_zero g).symm))
  let φ : B →ₗ[ℂ] ℂ :=
    { toFun b := g.symm b 0 0
      map_add' _ _ := by simp
      map_smul' _ _ := by simp }
  have hq_corner (b : B) : g e₀ * b * g e₀ = φ b • g e₀ := by
    have he₀_corner : e₀ * g.symm b * e₀ = (g.symm b 0 0) • e₀ := by simp [e₀]
    simpa only [φ, LinearMap.coe_mk, AddHom.coe_mk, map_mul, map_smul,
      AlgEquiv.apply_symm_apply] using congrArg g he₀_corner
  -- Normalize `g e₀` to a left-equivalent minimal star projection `p`.
  obtain ⟨p, ψ, hp, hp_ne, hp_corner, hpq, hqp⟩ :=
    hq_idem.exists_isStarProjection_of_forall_mul_eq_smul hq_ne φ hq_corner
  exact ⟨p, ψ, hp, hp_ne, hp_corner, fun x ↦
    ⟨fun hx ↦ by rw [← hx, mul_assoc, hpq], fun hx ↦ by rw [← hx, mul_assoc, hqp]⟩⟩

/-- Identify `leftIdealSubmodule ℂ p` linearly with `Fin n → ℂ` via the `0`-th column of
`Matrix (Fin n) (Fin n) ℂ` along `g`. -/
private def minimalLeftIdealColEquiv {B : Type*} [CStarAlgebra B] {n : ℕ} [NeZero n]
    (g : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] B) {p : B}
    (hright : ∀ x : B, x * p = x ↔ x * g (Matrix.single 0 0 1) = x) :
    (Fin n → ℂ) ≃ₗ[ℂ] leftIdealSubmodule ℂ p :=
  have hcol (M : Matrix (Fin n) (Fin n) ℂ) :
      M * Matrix.single 0 0 1 = Matrix.of fun i j ↦ if j = 0 then M i 0 else 0 := by
    ext i j
    by_cases hj : j = 0
    · subst hj; simp [Matrix.mul_single_apply_same]
    · simp [Matrix.mul_single_apply_of_ne, hj]
  { toFun v := ⟨g (Matrix.of fun i j ↦ if j = 0 then v i else 0), by
      rw [mem_leftIdealSubmodule, hright, ← map_mul, hcol]
      simp⟩
    invFun x i := g.symm x.1 i 0
    left_inv v := by ext i; simp
    right_inv x := by
      ext1
      apply g.symm.injective
      rw [AlgEquiv.symm_apply_apply, ← hcol]
      exact g.injective <| by
        simpa only [map_mul, AlgEquiv.apply_symm_apply] using
          (hright x.1).mp (mem_leftIdealSubmodule.mp x.2)
    map_add' v₁ v₂ := by
      ext1; dsimp; rw [← map_add]; congr 1; ext i j; by_cases hj : j = 0 <;> simp [hj]
    map_smul' r v := by
      ext1; dsimp; rw [← map_smul]; congr 1; ext i j; by_cases hj : j = 0 <;> simp [hj] }

/-- Left multiplication on the Hilbert space `leftIdealSubmodule ℂ p` realizes a simple C⋆-algebra
`B` with an `n × n` matrix `AlgEquiv` as `Matrix (Fin n) (Fin n) ℂ` via a `StarAlgEquiv`. -/
private theorem nonempty_starAlgEquiv_of_minimal_isStarProjection {B : Type*} [CStarAlgebra B]
    {n : ℕ} [NeZero n] (g : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] B) {p : B} {ψ : B →ₗ[ℂ] ℂ}
    (hp : IsStarProjection p) (hp_ne : p ≠ 0) (hp_corner : ∀ b : B, p * b * p = ψ b • p)
    (hright : ∀ x : B, x * p = x ↔ x * g (Matrix.single 0 0 1) = x) :
    Nonempty (B ≃⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ) := by
  let L := leftIdealSubmodule ℂ p
  let _ : InnerProductSpace ℂ L := hp.leftIdealInnerProductSpace hp_ne hp_corner
  let colEquiv := minimalLeftIdealColEquiv g hright
  have : FiniteDimensional ℂ L := Module.Finite.equiv colEquiv
  have hfinL : Module.finrank ℂ L = n := by simpa using colEquiv.symm.finrank_eq
  -- Represent `B` faithfully on `L` by bounded left multiplication; simplicity forces injectivity.
  let π := hp.leftMulStarAlgHom hp_ne hp_corner
  have : Nontrivial L :=
    ⟨⟨⟨p, mem_leftIdealSubmodule.mpr hp.isIdempotentElem.eq⟩, 0,
      fun h ↦ hp_ne (congrArg Subtype.val h)⟩⟩
  have hcomp_inj : Function.Injective (π.toAlgHom.comp g.toAlgHom).toRingHom := RingHom.injective _
  have hπ_inj : Function.Injective π := fun a b hab ↦ by
    rw [← g.apply_symm_apply a, ← g.apply_symm_apply b]
    exact congrArg g (hcomp_inj (by simpa using hab))
  -- Identify `L →L[ℂ] L` with `Matrix (Fin n) (Fin n) ℂ` via an orthonormal basis and compare rank.
  let matEquiv : (L →L[ℂ] L) ≃⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    ((stdOrthonormalBasis ℂ L).reindex (finCongr hfinL)).repr.conjStarAlgEquiv.trans
      Matrix.toEuclideanCLM.symm
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
    Matrix.reindexStarAlgEquiv ℂ ℂ em.symm
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

/-- Auxiliary multi-block decomposition for a unital finite-dimensional complex C⋆-algebra. -/
private theorem nonempty_cstarWedderburnPresentation_of_unital (A : Type u) [CStarAlgebra A]
    [FiniteDimensional ℂ A] : Nonempty (CStarWedderburnPresentation A) := by
  -- Split `A` algebraically into matrix blocks via properness of `star`.
  have : IsArtinianRing A := .of_finite ℂ A
  have : IsSemisimpleRing A := TauCeti.isSemisimpleRing_of_isProperStar A
  let P₀ := IsSemisimpleRing.splitWedderburnAlgebraPresentation ℂ A
  -- Pull back the coordinate units; central idempotents in a C⋆-algebra are star projections.
  let z (i : Fin P₀.blockCount) : A := P₀.equiv.symm (Pi.single i 1)
  have hz_central (i : Fin P₀.blockCount) : IsMulCentral (z i) :=
    P₀.equiv.isMulCentral_symm_single_one i
  have hz_coi : CompleteOrthogonalIdempotents z :=
    (CompleteOrthogonalIdempotents.single _).map P₀.equiv.symm.toRingEquiv.toRingHom
  have hz_proj (i : Fin P₀.blockCount) : IsStarProjection (z i) :=
    isStarProjection_iff_isIdempotentElem_and_isStarNormal.mpr
      ⟨hz_coi.idem i, ⟨((hz_central i).comm (star (z i))).symm⟩⟩
  have hz_fam : IsCompleteOrthogonalProjectionFamily z :=
    (isCompleteOrthogonalProjectionFamily_iff z).mpr ⟨hz_coi, hz_proj⟩
  -- Upgrade each central C⋆-ideal from `AlgEquiv` to `StarAlgEquiv` and assemble the product.
  have hblock (i : Fin P₀.blockCount) :
      Nonempty ((hz_fam.isStarProjection i).centralSubalgebra ℂ (hz_central i) ≃⋆ₐ[ℂ]
        CStarMatrix (Fin (P₀.degree i)) (Fin (P₀.degree i)) ℂ) :=
    nonempty_starAlgEquiv_cstarMatrix_of_algEquiv
      (P₀.equiv.centralSubalgebraSingle (hz_fam.isStarProjection i))
  exact ⟨{
    blockCount := P₀.blockCount
    degree := P₀.degree
    equiv := (hz_fam.starAlgEquivPiOfIsMulCentral ℂ hz_central).trans
      (StarAlgEquiv.piCongrRight fun i ↦ (hblock i).some) }⟩

/-- Every locally compact complex C⋆-algebra admits a `CStarWedderburnPresentation` as a finite
direct product of full complex matrix C⋆-algebras of positive degree. -/
theorem nonempty_cstarWedderburnPresentation_of_locallyCompactSpace (A : Type u)
    [NonUnitalCStarAlgebra A] [LocallyCompactSpace A] :
    Nonempty (CStarWedderburnPresentation A) := by
  let : IsUnital A := isUnital_of_locallyCompactSpace A
  let : CStarAlgebra A := IsUnital.toCStarAlgebra
  have : FiniteDimensional ℂ A := .of_locallyCompactSpace ℂ
  exact nonempty_cstarWedderburnPresentation_of_unital A

/-- **Matrix-block decomposition of finite-dimensional complex C⋆-algebras**: every
finite-dimensional complex C⋆-algebra (unital or not) admits a `CStarWedderburnPresentation`. -/
theorem nonempty_cstarWedderburnPresentation (A : Type u) [NonUnitalCStarAlgebra A]
    [FiniteDimensional ℂ A] : Nonempty (CStarWedderburnPresentation A) := by
  have := FiniteDimensional.proper ℂ A
  exact nonempty_cstarWedderburnPresentation_of_locallyCompactSpace A

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
