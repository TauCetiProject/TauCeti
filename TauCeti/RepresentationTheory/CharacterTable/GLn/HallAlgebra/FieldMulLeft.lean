/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.RingTheory.Polynomial.Basic
public import TauCeti.LinearAlgebra.Matrix.SimilarityClass
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Conjugacy of semisimple primary endomorphisms to field multiplication

Over a finite field `k`, let `L` be a finite field extension of `k` and let `g : Module.End k L`
be a semisimple `k`-linear endomorphism whose characteristic polynomial is a power `P ^ j` of an
irreducible polynomial `P : k[X]`. Then `P` annihilates `g`, giving `L` the structure of a vector
space over `k[X]/(P)`. Comparing dimensions shows `[k[X]/(P) : k] ∣ [L : k]`, so `k[X]/(P)` embeds
into `L` and `g` is conjugate to left multiplication `Algebra.lmul k L y` by some `y ∈ L`).

* `TauCeti.HallAlgebra.exists_conj_lmul_eq`: `g` is conjugate to `Algebra.lmul k L y` for some
  `e : L ≃ₗ[k] L` and `y : L`.
* `TauCeti.HallAlgebra.exists_ofEnd_eq_ofEnd_lmul`: in `TauCeti.SimilarityClass k`,
  `ofEnd g = ofEnd (Algebra.lmul k L y)` for some `y : L`.

## References

* J. A. Green, *The characters of the finite general linear groups*, Trans. Amer. Math. Soc. 80
  (1955), 402–447.

## Provenance

* Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
  PBC), file `src/Lib/LocalGL/Green/CuspidalFunctions.lean` (`New.exists_conj_mulLeft_eq`).
-/

public section

namespace TauCeti.HallAlgebra

open Polynomial Module

variable {k L : Type*} [Field k] [Field L] [Finite L] [Algebra k L]

/-- A semisimple `k`-linear endomorphism `g` of a finite field extension `L / k` whose
characteristic polynomial is a power `P ^ j` of an irreducible polynomial `P : k[X]` is conjugate
to left multiplication `Algebra.lmul k L y` for some `y ∈ L`. -/
theorem exists_conj_lmul_eq {g : End k L} {P : k[X]} {j : ℕ} (hg : g.IsSemisimple)
    (hP : Irreducible P) (h_charpoly : g.charpoly = P ^ j) :
    ∃ (e : L ≃ₗ[k] L) (y : L), e.conjAlgEquiv k (Algebra.lmul k L y) = g := by
  have h_aeval : Polynomial.aeval g P = 0 :=
    minpoly.dvd_iff.mp <|
      hg.minpoly_squarefree.isRadical j P ((LinearMap.minpoly_dvd_charpoly g).trans h_charpoly.dvd)
  let V : Type _ := AEval' g
  have : Fact (Irreducible P) := ⟨hP⟩
  have : Module.Finite k (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
  have : Finite V := inferInstanceAs (Finite L)
  let _ : Module (AdjoinRoot P) V := IsTorsionBy.module (LinearMap.congr_fun h_aeval)
  have : IsScalarTower k (AdjoinRoot P) V := IsTorsionBySet.isScalarTower _
  have h_tower := finrank_mul_finrank k (AdjoinRoot P) V
  let φ : AdjoinRoot P →ₐ[k] L :=
    (FiniteField.nonempty_algHom_of_finrank_dvd (L := L) ⟨_, h_tower.symm⟩).some
  let _ : Algebra (AdjoinRoot P) L := φ.toAlgebra
  have : IsScalarTower k (AdjoinRoot P) L := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let t : V ≃ₗ[AdjoinRoot P] L := LinearEquiv.ofFinrankEq _ _ <|
    mul_left_cancel₀ finrank_pos.ne' (h_tower.trans (finrank_mul_finrank k (AdjoinRoot P) L).symm)
  exact ⟨t.symm.restrictScalars k, φ (AdjoinRoot.root P),
    LinearMap.ext fun x ↦ (t.symm_apply_eq.mpr (t.map_smul _ x).symm).trans (AEval'.X_smul_of g x)⟩

/-- In `SimilarityClass k`, a semisimple `k`-linear endomorphism `g` of a finite field extension
`L / k` with primary characteristic polynomial `P ^ j` (`P` irreducible) has the same similarity
class as left multiplication `Algebra.lmul k L y` for some `y ∈ L`. -/
theorem exists_ofEnd_eq_ofEnd_lmul {g : End k L} {P : k[X]} {j : ℕ} (hg : g.IsSemisimple)
    (hP : Irreducible P) (h_charpoly : g.charpoly = P ^ j) :
    ∃ y : L, SimilarityClass.ofEnd g = SimilarityClass.ofEnd (Algebra.lmul k L y) := by
  obtain ⟨e, y, rfl⟩ := exists_conj_lmul_eq hg hP h_charpoly
  exact ⟨y, SimilarityClass.ofEnd_conj e _⟩

end TauCeti.HallAlgebra
