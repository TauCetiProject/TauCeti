/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.DominantTorus

/-!
# Dominant diagonal matrices in `GL_m(K)` over a valued field

Given a valuation subring `A` of a field `K` and a finite preordered index type `m`, a diagonal
matrix `TauCeti.diagGL t` (`t : m → Kˣ`) is *dominant* if its diagonal entries have weakly
increasing multiplicative valuations (`i ≤ j → A.valuation (t i) ≤ A.valuation (t j)`).

This file packages these matrices as the submonoid `ValuationSubring.dominantDiagSubmonoid A m` of
`GL m K`, defined as the image of `TauCeti.dominantTorus m A.valuation` under `TauCeti.diagGL`:

* `ValuationSubring.dominantDiagSubmonoid`: the submonoid `T⁺ ⊆ GL_m(K)` of dominant diagonal
  matrices.
* `ValuationSubring.mem_dominantDiagSubmonoid_iff`: existential membership characterization.
* `ValuationSubring.diagGL_mem_dominantDiagSubmonoid_iff`: `diagGL t ∈ A.dominantDiagSubmonoid m`
  iff `i ↦ A.valuation (t i)` is monotone.
-/

public section

open Matrix TauCeti

namespace ValuationSubring

variable {K : Type*} [Field K] (A : ValuationSubring K)
  {m : Type*} [Fintype m] [DecidableEq m] [Preorder m]

/-- The submonoid of `GL_m(K)` consisting of dominant diagonal matrices `diagGL t`, where
`t : m → Kˣ` has weakly increasing multiplicative valuations
(`i ≤ j → A.valuation (t i) ≤ A.valuation (t j)`). -/
noncomputable def dominantDiagSubmonoid (m : Type*) [Fintype m] [DecidableEq m] [Preorder m] :
    Submonoid (GL m K) :=
  (dominantTorus m A.valuation).map diagGL

/-- A matrix lies in `A.dominantDiagSubmonoid m` iff it is `diagGL t` for some `t : m → Kˣ` with
weakly increasing multiplicative valuations. -/
theorem mem_dominantDiagSubmonoid_iff {g : GL m K} :
    g ∈ A.dominantDiagSubmonoid m ↔
      ∃ t : m → Kˣ, (Monotone fun i ↦ A.valuation (t i : K)) ∧ diagGL t = g := by
  simp [dominantDiagSubmonoid]

/-- A diagonal matrix `diagGL t` lies in `A.dominantDiagSubmonoid m` iff its diagonal entries have
weakly increasing multiplicative valuations. -/
@[simp]
theorem diagGL_mem_dominantDiagSubmonoid_iff {t : m → Kˣ} :
    diagGL t ∈ A.dominantDiagSubmonoid m ↔ Monotone fun i ↦ A.valuation (t i : K) := by
  rw [mem_dominantDiagSubmonoid_iff]
  constructor
  · rintro ⟨t', ht', h⟩
    have hEq : t' = t := by
      ext i
      have hi := congrArg (fun M : GL m K ↦ (M : Matrix m m K) i i) h
      simpa [diagGL_coe] using hi
    exact hEq ▸ ht'
  · intro ht
    exact ⟨t, ht, rfl⟩

end ValuationSubring
