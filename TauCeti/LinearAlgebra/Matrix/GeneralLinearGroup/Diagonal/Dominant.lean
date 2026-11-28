/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.DominantTorus

/-!
# Dominant diagonal matrices in `GL_m(R)` for a valuation

Given a valuation `v : Valuation R Γ₀` on a ring `R` and a finite preordered index type `m`, a
diagonal matrix `TauCeti.diagGL t` (`t : m → Rˣ`) is *dominant* if its diagonal entries have weakly
increasing multiplicative valuations (`i ≤ j → v (t i) ≤ v (t j)`).

This file packages these matrices as the submonoid `Valuation.dominantDiagSubmonoid v m` of
`GL m R`, defined as the image of `TauCeti.dominantTorus m v` under `TauCeti.diagGL`:

* `Valuation.dominantDiagSubmonoid`: the submonoid `T⁺ ⊆ GL_m(R)` of dominant diagonal matrices.
* `Valuation.mem_dominantDiagSubmonoid_iff`: existential membership characterization.
* `Valuation.diagGL_mem_dominantDiagSubmonoid_iff`: `diagGL t ∈ v.dominantDiagSubmonoid m` iff
  `i ↦ v (t i)` is monotone.
-/

public section

open Matrix TauCeti

namespace Valuation

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)
  {m : Type*} [Fintype m] [DecidableEq m] [Preorder m]

/-- The submonoid of `GL_m(R)` consisting of dominant diagonal matrices `diagGL t`, where
`t : m → Rˣ` has weakly increasing multiplicative valuations (`i ≤ j → v (t i) ≤ v (t j)`). -/
def dominantDiagSubmonoid (m : Type*) [Fintype m] [DecidableEq m] [Preorder m] :
    Submonoid (GL m R) :=
  (dominantTorus m v).map diagGL

/-- A matrix lies in `v.dominantDiagSubmonoid m` iff it is `diagGL t` for some `t : m → Rˣ` with
weakly increasing multiplicative valuations. -/
theorem mem_dominantDiagSubmonoid_iff {g : GL m R} :
    g ∈ v.dominantDiagSubmonoid m ↔
      ∃ t : m → Rˣ, (Monotone fun i ↦ v (t i : R)) ∧ diagGL t = g := by
  simp [dominantDiagSubmonoid]

/-- A diagonal matrix `diagGL t` lies in `v.dominantDiagSubmonoid m` iff its diagonal entries have
weakly increasing multiplicative valuations. -/
@[simp]
theorem diagGL_mem_dominantDiagSubmonoid_iff {t : m → Rˣ} :
    diagGL t ∈ v.dominantDiagSubmonoid m ↔ Monotone fun i ↦ v (t i : R) := by
  simpa only [dominantDiagSubmonoid, mem_dominantTorus_iff] using
    (Submonoid.mem_map_iff_mem diagGL_injective (S := dominantTorus m v) (x := t))

end Valuation
