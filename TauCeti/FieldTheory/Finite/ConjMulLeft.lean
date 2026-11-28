/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti Contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Semisimple
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Conjugacy of Endomorphisms of Finite Field Extensions to Left Multiplication

If `k` is a field, `V` is a finite-dimensional `k`-vector space, and `g : Module.End k V` is
semisimple with characteristic polynomial a power `P ^ j` of an irreducible polynomial `P`, then
`P` annihilates `g`. When `L` is a finite extension of a finite field `k`, any `k`-linear
endomorphism `g` of `L` annihilated by an irreducible `P : k[X]` (in particular, any semisimple
endomorphism with `g.charpoly = P ^ j`) is conjugate to left multiplication by some `y : L`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), `src/Lib/LocalGL/Green/CuspidalFunctions.lean`
(`New.exists_conj_mulLeft_eq`).
-/

@[expose] public section

namespace TauCeti

open Polynomial Module

/-- A semisimple endomorphism whose characteristic polynomial is a power `P ^ j` is annihilated
by `P`. -/
theorem aeval_eq_zero_of_isSemisimple_of_charpoly_eq_pow {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] [Module.Finite k V] {g : End k V} {P : k[X]} {j : ℕ}
    (hg : g.IsSemisimple) (h_charpoly : g.charpoly = P ^ j) :
    Polynomial.aeval g P = 0 :=
  minpoly.dvd_iff.mp <|
    hg.minpoly_squarefree.isRadical j P ((LinearMap.minpoly_dvd_charpoly g).trans h_charpoly.dvd)

/-- Any `k`-linear endomorphism `g` of a finite field extension `L / k` annihilated by an
irreducible polynomial `P : k[X]` is conjugate to left multiplication by an element of `L`. -/
theorem exists_conj_lmul_eq_of_aeval_eq_zero {k L : Type*} [Field k] [Finite k] [Field L]
    [Finite L] [Algebra k L] {g : End k L} {P : k[X]} (hP : Irreducible P)
    (h_aeval : Polynomial.aeval g P = 0) :
    ∃ (e : L ≃ₗ[k] L) (y : L), e.conjAlgEquiv k (Algebra.lmul k L y) = g := by
  let V : Type _ := AEval' g
  have : Fact (Irreducible P) := ⟨hP⟩
  have : Module.Finite k (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
  have : Finite V := inferInstanceAs (Finite L)
  let _ : Module (AdjoinRoot P) V := IsTorsionBy.module (LinearMap.congr_fun h_aeval)
  have : IsScalarTower k (AdjoinRoot P) V := IsTorsionBySet.isScalarTower _
  have tower_V := finrank_mul_finrank k (AdjoinRoot P) V
  let φ : AdjoinRoot P →ₐ[k] L :=
    (FiniteField.nonempty_algHom_of_finrank_dvd (L := L) ⟨_, tower_V.symm⟩).some
  let _ : Algebra (AdjoinRoot P) L := φ.toAlgebra
  have : IsScalarTower k (AdjoinRoot P) L := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let t : V ≃ₗ[AdjoinRoot P] L := LinearEquiv.ofFinrankEq _ _ <|
    mul_left_cancel₀ finrank_pos.ne' (tower_V.trans (finrank_mul_finrank k (AdjoinRoot P) L).symm)
  exact ⟨t.symm.restrictScalars k, algebraMap (AdjoinRoot P) L (AdjoinRoot.root P),
    LinearMap.ext fun x ↦ (t.symm_apply_eq.mpr (t.map_smul _ x).symm).trans (AEval'.X_smul_of g x)⟩

/-- A semisimple `k`-linear endomorphism `g` of a finite field extension `L / k` whose
characteristic polynomial is a power of an irreducible polynomial `P` is conjugate to left
multiplication by some `y : L`. -/
theorem exists_conj_lmul_eq_of_charpoly_eq_pow {k L : Type*} [Field k] [Finite k] [Field L]
    [Finite L] [Algebra k L] {g : End k L} {P : k[X]} {j : ℕ}
    (hg : g.IsSemisimple) (hP : Irreducible P) (h_charpoly : g.charpoly = P ^ j) :
    ∃ (e : L ≃ₗ[k] L) (y : L), e.conjAlgEquiv k (Algebra.lmul k L y) = g :=
  exists_conj_lmul_eq_of_aeval_eq_zero hP
    (aeval_eq_zero_of_isSemisimple_of_charpoly_eq_pow hg h_charpoly)

end TauCeti
