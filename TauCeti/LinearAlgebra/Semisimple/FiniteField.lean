/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Semisimple

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Conjugacy of endomorphisms annihilated by an irreducible polynomial over finite fields

Let `L / k` be an extension of finite fields, and let `g : Module.End k W` be a `k`-linear
endomorphism of a finite-dimensional `k`-vector space `W` with
`Module.finrank k W = Module.finrank k L`. If `g` is annihilated by an irreducible polynomial
`P : k[X]` (`Polynomial.aeval g P = 0`), then `W` becomes a vector space over `k[X]/(P)`.
Comparing dimensions shows `[k[X]/(P) : k] ∣ [L : k]`, so `k[X]/(P)` embeds into `L` and `g` is
conjugate via a `k`-linear equivalence `L ≃ₗ[k] W` to left multiplication `Algebra.lmul k L y` by
some `y ∈ L`.

In particular, this applies when `g` is semisimple with primary characteristic polynomial `P ^ j`.

* `Module.End.exists_conj_lmul_eq_of_aeval_eq_zero`: any endomorphism `g` annihilated by an
  irreducible `P : k[X]` is conjugate to `Algebra.lmul k L y` for some `e : L ≃ₗ[k] W` and `y : L`.
* `Module.End.IsSemisimple.exists_conj_lmul_eq`: specialization to semisimple `g` with
  `g.charpoly = P ^ j`.

## References

* J. A. Green, *The characters of the finite general linear groups*, Trans. Amer. Math. Soc. 80
  (1955), 402–447.

## Provenance

* Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
  PBC), file `src/Lib/LocalGL/Green/CuspidalFunctions.lean` (`New.exists_conj_mulLeft_eq`).
-/

public section

namespace Module.End

open Polynomial Module

/-- Let `L / k` be an extension of finite fields. Any `k`-linear endomorphism `g` of a
finite-dimensional `k`-vector space `W` with `Module.finrank k W = Module.finrank k L` that is
annihilated by an irreducible polynomial `P : k[X]` is conjugate to left multiplication
`Algebra.lmul k L y` for some `e : L ≃ₗ[k] W` and `y ∈ L`. -/
theorem exists_conj_lmul_eq_of_aeval_eq_zero {k L W : Type*} [Field k] [Field L] [Finite L]
    [Algebra k L] [AddCommGroup W] [Module k W] [Module.Finite k W]
    (hdim : finrank k W = finrank k L) {g : End k W} {P : k[X]} (hP : Irreducible P)
    (h_aeval : Polynomial.aeval g P = 0) :
    ∃ (e : L ≃ₗ[k] W) (y : L), e.conjAlgEquiv k (Algebra.lmul k L y) = g := by
  let V : Type _ := AEval' g
  let e₀ : W ≃ₗ[k] V := AEval'.of g
  have : Fact (Irreducible P) := ⟨hP⟩
  have : Module.Finite k (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
  have : Module.Finite k V := Module.Finite.equiv e₀
  have hfin : finrank k V = finrank k L := e₀.finrank_eq.symm.trans hdim
  let _ : Module (AdjoinRoot P) V := IsTorsionBy.module (LinearMap.congr_fun h_aeval)
  have : IsScalarTower k (AdjoinRoot P) V := IsTorsionBySet.isScalarTower _
  let φ : AdjoinRoot P →ₐ[k] L :=
    (FiniteField.nonempty_algHom_of_finrank_dvd (L := L)
      (hfin ▸ finrank_dvd_finrank_right k (AdjoinRoot P) V)).some
  let _ : Algebra (AdjoinRoot P) L := φ.toAlgebra
  have : IsScalarTower k (AdjoinRoot P) L := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have hdim_eq : finrank (AdjoinRoot P) V = finrank (AdjoinRoot P) L := by
    rw [← finrank_div_finrank_cancel_left_of_nontrivial k (AdjoinRoot P) V,
      ← finrank_div_finrank_cancel_left_of_nontrivial k (AdjoinRoot P) L, hfin]
  have : Module.Finite (AdjoinRoot P) V := Module.Finite.of_restrictScalars_finite k _ _
  have : Module.Finite (AdjoinRoot P) L := Module.Finite.of_restrictScalars_finite k _ _
  let t : V ≃ₗ[AdjoinRoot P] L := LinearEquiv.ofFinrankEq _ _ hdim_eq
  have h_root_V (w : W) : AdjoinRoot.root P • e₀ w = e₀ (g w) := by
    -- `AdjoinRoot.root P` is `Ideal.Quotient.mk (span {P}) X`, whose `IsTorsionBy.module`
    -- action on `AEval' g` agrees with `X • e₀ w = e₀ (g w)`.
    exact AEval'.X_smul_of g w
  have h_root_L (x : L) : AdjoinRoot.root P • x = φ (AdjoinRoot.root P) * x := by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    rfl
  refine ⟨(t.symm.restrictScalars k).trans e₀.symm, φ (AdjoinRoot.root P), LinearMap.ext fun w ↦ ?_⟩
  simp [← h_root_L, ← t.map_smul, h_root_V]

/-- Let `L / k` be an extension of finite fields. Any semisimple `k`-linear endomorphism `g` of a
finite-dimensional `k`-vector space `W` with `Module.finrank k W = Module.finrank k L` whose
characteristic polynomial is a power `P ^ j` of an irreducible polynomial `P : k[X]` is conjugate
to left multiplication `Algebra.lmul k L y` for some `e : L ≃ₗ[k] W` and `y ∈ L`. -/
theorem IsSemisimple.exists_conj_lmul_eq {k L W : Type*} [Field k] [Field L] [Finite L]
    [Algebra k L] [AddCommGroup W] [Module k W] [Module.Finite k W]
    (hdim : finrank k W = finrank k L) {g : End k W} {P : k[X]} {j : ℕ} (hg : g.IsSemisimple)
    (hP : Irreducible P) (h_charpoly : g.charpoly = P ^ j) :
    ∃ (e : L ≃ₗ[k] W) (y : L), e.conjAlgEquiv k (Algebra.lmul k L y) = g :=
  exists_conj_lmul_eq_of_aeval_eq_zero hdim hP <| minpoly.dvd_iff.mp <|
    hg.minpoly_squarefree.isRadical j P ((LinearMap.minpoly_dvd_charpoly g).trans h_charpoly.dvd)

end Module.End
