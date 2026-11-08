/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Data.Matrix.Composition
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Algebra.Homology.ModuleCat.Basic
import TauCeti.Algebra.Homology.ShortComplex.ModuleCat
import TauCeti.LinearAlgebra.Basis.SmulTower
import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Dimensions of boundaries of complexes of vector spaces

In a homological complex of vector spaces, a homology group has dimension at most that of the
finite-dimensional term it is computed from (`HomologicalComplex.finrank_homology_le_finrank_X`).

Let `C` be a homological complex of vector spaces over a field `F`. If `C.X j` is
finite-dimensional, `C` is exact in degree `j` exactly when the dimensions of the images of the
incoming and outgoing differentials add up to the dimension of `C.X j`
(`HomologicalComplex.exactAt_iff_finrank_add_finrank`). The boundaries of a based complex vanish
in a degree where its basis is empty (`HomologicalComplex.finrank_range_d_eq_zero`), so for a
bounded based complex the signs `(-1) ^ (dim Bⱼ · f j)` have finite multiplicative support
(`HomologicalComplex.hasFiniteMulSupport_neg_one_pow_finrank_mul`).

Let `φ : F →+* K` be a homomorphism of fields and let `D` be a complex of vector spaces over `K`
of the same shape. If `C` and `D` have bases in which the matrices of the differentials of `D` are
the images under `φ` of those of `C`, then the images of the differentials have the same
dimensions (`HomologicalComplex.finrank_range_d_eq_of_toMatrix_eq`), since rank is invariant
under `φ` (`Matrix.rank_map`). Consequently `D` is acyclic exactly when `C` is
(`HomologicalComplex.acyclic_iff_of_toMatrix_eq`).

Let `L` be a field extension of `F` with an ordered `F`-basis `β a`, `a : Fin m`, let `C` be a
complex of vector spaces over `L` with bases `c i`, and let `D` be a complex of vector spaces over
`F` with bases `e i` in which the matrix of each differential is the block matrix obtained from the
matrix of the corresponding differential of `C` by replacing each entry `x` with
`Algebra.leftMulMatrix β x`; that is, `(D, e)` is the restriction of scalars of `(C, c)` to `F`,
based by the vectors `β a • c i k`. Then the boundaries of `D` have `m` times the dimension of
those of `C` (`HomologicalComplex.finrank_range_d_eq_mul_of_toMatrix_eq_leftMulMatrix`), and `D`
is acyclic exactly when `C` is (`HomologicalComplex.acyclic_iff_of_toMatrix_eq_leftMulMatrix`).
-/

public section

open CategoryTheory Module

namespace HomologicalComplex

/-- **The weak Morse inequality.**  In a homological complex of vector spaces, a homology group
has dimension at most that of the finite-dimensional term it is computed from. -/
theorem finrank_homology_le_finrank_X {k : Type*} [DivisionRing k] {ι : Type*}
    {c : ComplexShape ι} (K : HomologicalComplex (ModuleCat k) c) (i : ι)
    [Module.Finite k (K.X i)] :
    finrank k (K.homology i) ≤ finrank k (K.X i) :=
  -- The middle term of `K.sc i` is `K.X i` by construction.
  have : Module.Finite k (K.sc i).X₂ := ‹Module.Finite k (K.X i)›
  (K.sc i).finrank_homology_le_finrank_X₂

variable {F : Type*} [Field F] {ι : Type*} {s : ComplexShape ι}

/-- A complex of vector spaces with finite-dimensional term in degree `j` is exact in degree `j`
exactly when the dimensions of the images of the incoming and outgoing differentials add up to the
dimension of the term. -/
theorem exactAt_iff_finrank_add_finrank (C : HomologicalComplex (ModuleCat F) s) {i j k : ι}
    (hi : s.prev j = i) (hk : s.next j = k) [Module.Finite F (C.X j)] :
    C.ExactAt j ↔ finrank F (LinearMap.range (C.d i j).hom) +
      finrank F (LinearMap.range (C.d j k).hom) = finrank F (C.X j) := by
  have hex : C.ExactAt j ↔ LinearMap.ker (C.d j k).hom ≤ LinearMap.range (C.d i j).hom :=
    (C.exactAt_iff' _ _ _ hi hk).trans (ShortComplex.moduleCat_exact_iff_ker_sub_range _)
  have hle : LinearMap.range (C.d i j).hom ≤ LinearMap.ker (C.d j k).hom := by
    rintro _ ⟨x, rfl⟩
    exact d_comp_d_apply C _ _ _ x
  have hrk := LinearMap.finrank_range_add_finrank_ker (C.d j k).hom
  rw [hex]
  refine ⟨fun h ↦ ?_, fun h ↦ (Submodule.eq_of_le_of_finrank_le hle (by omega)).ge⟩
  have := Submodule.finrank_mono h
  have := Submodule.finrank_mono hle
  omega

/-- The boundaries vanish in a degree where the based complex vanishes. -/
theorem finrank_range_d_eq_zero (C : ChainComplex (ModuleCat F) ℤ) {n : ℤ → ℕ}
    (c : ∀ i, Basis (Fin (n i)) F (C.X i)) {j : ℤ} (hj : n j = 0) :
    finrank F (LinearMap.range (C.d (j + 1) j).hom) = 0 := by
  have : Module.Finite F (C.X j) := .of_basis (c j)
  have hle := Submodule.finrank_le (LinearMap.range (C.d (j + 1) j).hom)
  rwa [finrank_eq_card_basis (c j), Fintype.card_fin, hj, Nat.le_zero] at hle

/-- The signs `(-1) ^ (dim Bⱼ · f j)`, where `Bⱼ` is the space of boundaries of a bounded based
complex `C` in degree `j`, have finite multiplicative support. -/
theorem hasFiniteMulSupport_neg_one_pow_finrank_mul (C : ChainComplex (ModuleCat F) ℤ)
    {n : ℤ → ℕ} (c : ∀ i, Basis (Fin (n i)) F (C.X i)) (hn : {i | n i ≠ 0}.Finite)
    (f : ℤ → ℕ) : Function.HasFiniteMulSupport fun j : ℤ ↦
      (-1 : F) ^ (finrank F (LinearMap.range (C.d (j + 1) j).hom) * f j) :=
  hn.subset <| Function.mulSupport_subset_iff'.2 fun j hj ↦ by
    simp [finrank_range_d_eq_zero C c (j := j) (by simpa using hj)]

section RingHom

variable {K : Type*} [Field K] (φ : F →+* K) {C : HomologicalComplex (ModuleCat F) s}
  {D : HomologicalComplex (ModuleCat K) s} {κ : ι → Type*} [∀ i, Fintype (κ i)]
  [∀ i, DecidableEq (κ i)] {c : ∀ i, Basis (κ i) F (C.X i)} {e : ∀ i, Basis (κ i) K (D.X i)}

/-- If the matrix of a differential of `D` is the image under a homomorphism of fields `φ` of the
matrix of the corresponding differential of `C`, then the images of the two differentials have the
same dimension. -/
theorem finrank_range_d_eq_of_toMatrix_eq {i j : ι}
    (hd : LinearMap.toMatrix (e i) (e j) (D.d i j).hom =
      (LinearMap.toMatrix (c i) (c j) (C.d i j).hom).map φ) :
    finrank K (LinearMap.range (D.d i j).hom) = finrank F (LinearMap.range (C.d i j).hom) := by
  have hC := Matrix.rank_eq_finrank_range_toLin
    (LinearMap.toMatrix (c i) (c j) (C.d i j).hom) (c j) (c i)
  have hD := Matrix.rank_eq_finrank_range_toLin
    (LinearMap.toMatrix (e i) (e j) (D.d i j).hom) (e j) (e i)
  rw [Matrix.toLin_toMatrix] at hC hD
  rw [← hC, ← hD, hd, Matrix.rank_map]

/-- If, in bases indexed by the same types, the matrices of the differentials of `D` are the images
under a homomorphism of fields `φ` of the matrices of the differentials of `C`, then `D` is acyclic
exactly when `C` is. -/
theorem acyclic_iff_of_toMatrix_eq
    (hd : ∀ i j, s.Rel i j → LinearMap.toMatrix (e i) (e j) (D.d i j).hom =
      (LinearMap.toMatrix (c i) (c j) (C.d i j).hom).map φ) :
    D.Acyclic ↔ C.Acyclic := by
  have hrk (i j : ι) :
      finrank K (LinearMap.range (D.d i j).hom) = finrank F (LinearMap.range (C.d i j).hom) := by
    by_cases hij : s.Rel i j
    · exact finrank_range_d_eq_of_toMatrix_eq φ (hd i j hij)
    · rw [D.shape i j hij, C.shape i j hij, ModuleCat.hom_zero, ModuleCat.hom_zero,
        LinearMap.range_zero, LinearMap.range_zero, finrank_bot, finrank_bot]
  refine forall_congr' fun j ↦ ?_
  have : Module.Finite F (C.X j) := .of_basis (c j)
  have : Module.Finite K (D.X j) := .of_basis (e j)
  rw [exactAt_iff_finrank_add_finrank D rfl rfl, exactAt_iff_finrank_add_finrank C rfl rfl,
    hrk, hrk, finrank_eq_card_basis (c j), finrank_eq_card_basis (e j)]

end RingHom

section RestrictScalars

open scoped ModuleCat.Algebra

variable {L : Type*} [Field L] [Algebra F L] {m : ℕ} (β : Basis (Fin m) F L)
  {C : HomologicalComplex (ModuleCat L) s} {D : HomologicalComplex (ModuleCat F) s} {n : ι → ℕ}
  {c : ∀ i, Basis (Fin (n i)) L (C.X i)} {e : ∀ i, Basis (Fin (n i * m)) F (D.X i)}

/-- If the matrix of a differential of `D` is obtained from the matrix of the corresponding
differential of `C` by replacing each entry `x` with the matrix `Algebra.leftMulMatrix β x` of
multiplication by `x`, the indices `(k, a)` being ordered by `finProdFinEquiv`, then the image of
the differential of `D` has `m` times the dimension of the image of that of `C`. -/
theorem finrank_range_d_eq_mul_of_toMatrix_eq_leftMulMatrix {i j : ι}
    (hd : LinearMap.toMatrix (e i) (e j) (D.d i j).hom =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.comp _ _ _ _ F
        ((LinearMap.toMatrix (c i) (c j) (C.d i j).hom).map (Algebra.leftMulMatrix β)))) :
    finrank F (LinearMap.range (D.d i j).hom) = finrank L (LinearMap.range (C.d i j).hom) * m := by
  have : Module.Finite F L := .of_basis β
  have hm : finrank F L = m := by rw [finrank_eq_card_basis β, Fintype.card_fin]
  have hD := Matrix.rank_eq_finrank_range_toLin
    (LinearMap.toMatrix (e i) (e j) (D.d i j).hom) (e j) (e i)
  have hC := Matrix.rank_eq_finrank_range_toLin
    (LinearMap.toMatrix (β.smulTower' (c i)) (β.smulTower' (c j))
      ((C.d i j).hom.restrictScalars F)) (β.smulTower' (c j)) (β.smulTower' (c i))
  rw [Matrix.toLin_toMatrix] at hC hD
  rw [← hD, hd, Matrix.rank_reindex, ← LinearMap.toMatrix_restrictScalars, hC,
    LinearMap.range_restrictScalars, mul_comm, ← hm]
  exact (Module.finrank_mul_finrank F L (LinearMap.range (C.d i j).hom)).symm

/-- If, in the bases `c i` and `e i`, the matrix of each differential of `D` is obtained from the
matrix of the corresponding differential of `C` by replacing each entry `x` with the matrix
`Algebra.leftMulMatrix β x` of multiplication by `x`, the indices `(k, a)` being ordered by
`finProdFinEquiv`, then `D` is acyclic exactly when `C` is. -/
theorem acyclic_iff_of_toMatrix_eq_leftMulMatrix
    (hd : ∀ i j, s.Rel i j → LinearMap.toMatrix (e i) (e j) (D.d i j).hom =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.comp _ _ _ _ F
        ((LinearMap.toMatrix (c i) (c j) (C.d i j).hom).map (Algebra.leftMulMatrix β)))) :
    D.Acyclic ↔ C.Acyclic := by
  have hm : m ≠ 0 := (Fin.pos_iff_nonempty.2 β.index_nonempty).ne'
  have hrk (i j : ι) : finrank F (LinearMap.range (D.d i j).hom) =
      finrank L (LinearMap.range (C.d i j).hom) * m := by
    by_cases hij : s.Rel i j
    · exact finrank_range_d_eq_mul_of_toMatrix_eq_leftMulMatrix β (hd i j hij)
    · rw [D.shape i j hij, C.shape i j hij, ModuleCat.hom_zero, ModuleCat.hom_zero,
        LinearMap.range_zero, LinearMap.range_zero, finrank_bot, finrank_bot, zero_mul]
  refine forall_congr' fun j ↦ ?_
  have : Module.Finite F (D.X j) := .of_basis (e j)
  have : Module.Finite L (C.X j) := .of_basis (c j)
  rw [exactAt_iff_finrank_add_finrank D rfl rfl, exactAt_iff_finrank_add_finrank C rfl rfl, hrk,
    hrk, finrank_eq_card_basis (c j), finrank_eq_card_basis (e j), Fintype.card_fin,
    Fintype.card_fin, ← add_mul]
  exact Nat.mul_left_inj hm

end RestrictScalars

end HomologicalComplex
