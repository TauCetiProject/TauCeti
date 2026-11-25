/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.AF.Basic
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Topology.PreorderRestrict
import TauCeti.Topology.ContinuousMap.Finite

/-!
# Continuous functions on a product of finite discrete spaces form an AF algebra

Let `X = ∀ n : ℕ, E n` be a countable product of finite discrete spaces, for instance the Cantor
space `ℕ → Bool`. Then `C(X, ℂ)` is AF. Its `n`-th stage consists of the functions that depend
only on the coordinates `i ≤ n`, the image of `C((i : Finset.Iic n) → E i, ℂ)` under composition
with the restriction map `Preorder.frestrictLe n`. Each stage is finite-dimensional because
`∀ i : Finset.Iic n, E i` is finite, the stages increase, and their union is a ⋆-subalgebra
separating the points of the compact space `X`, hence dense by the Stone–Weierstrass theorem.

## Main statements

* `TauCeti.isAF_continuousMap_pi`: `C((n : ℕ) → E n, ℂ)` is AF for finite discrete spaces `E n`.
-/

public section

open Set

namespace TauCeti

variable {E : ℕ → Type*} [∀ n, TopologicalSpace (E n)] [∀ n, DiscreteTopology (E n)]
  [∀ n, Finite (E n)]

/-- **`C((n : ℕ) → E n, ℂ)` is AF** for finite discrete spaces `E n`; for instance, the continuous
functions on the Cantor space `ℕ → Bool` form an AF algebra. The `n`-th stage consists of the
functions depending only on the coordinates `i ≤ n`. -/
theorem isAF_continuousMap_pi : IsAF C((n : ℕ) → E n, ℂ) := by
  let φ (n : ℕ) := ContinuousMap.compStarAlgHom' ℂ ℂ
    ⟨Preorder.frestrictLe (π := E) n, Preorder.continuous_frestrictLe n⟩
  have hcoe (n : ℕ) :
      ((φ n).toNonUnitalStarAlgHom.range : Set C((n : ℕ) → E n, ℂ)) = (φ n).range := by
    ext
    simp [StarAlgHom.range_eq_map_top]
  have hmono : Monotone fun n ↦ (φ n).range := by
    rintro m n hmn _ ⟨g, rfl⟩
    refine ⟨g.comp ⟨Preorder.frestrictLe₂ hmn, Preorder.continuous_frestrictLe₂ hmn⟩, ?_⟩
    ext x
    simp [φ, ← Preorder.frestrictLe₂_comp_frestrictLe hmn]
  refine isAF_iff.2 ⟨fun n ↦ (φ n).toNonUnitalStarAlgHom.range, fun m n hmn ↦ ?_,
    fun _ ↦ inferInstance, ?_⟩
  · simpa only [← SetLike.coe_subset_coe, hcoe] using hmono hmn
  · simp_rw [hcoe, ← StarSubalgebra.coe_iSup_of_directed hmono.directed_le]
    refine dense_iff_closure_eq.2 ?_
    rw [← StarSubalgebra.topologicalClosure_coe,
      ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ ?_]
    · simp
    intro x y hxy
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
    classical
    let g : C((j : Finset.Iic i) → E j, ℂ) :=
      ⟨fun z ↦ if z ⟨i, Finset.mem_Iic.2 le_rfl⟩ = x i then 1 else 0,
        continuous_of_discreteTopology⟩
    refine ⟨_, ⟨φ i g, le_iSup (fun n ↦ (φ n).range) i ⟨g, rfl⟩, rfl⟩, ?_⟩
    simp [φ, g, Preorder.frestrictLe_apply, hi.symm]

end TauCeti
