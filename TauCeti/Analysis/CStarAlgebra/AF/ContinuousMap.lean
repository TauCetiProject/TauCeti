/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.AF.Basic
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap

/-!
# Continuous functions on a product of finite discrete spaces form an AF algebra

Let `X = ∀ n : ℕ, E n` be a countable product of finite discrete spaces, for instance the Cantor
space `ℕ → Bool`. Then `C(X, ℂ)` is AF. Its `n`-th stage consists of the functions that depend
only on the first `n` coordinates, the image of `C((i : Fin n) → E i, ℂ)` under composition with
the restriction map. Each stage is finite-dimensional because `∀ i : Fin n, E i` is finite and
discrete, the stages increase, and their union is a ⋆-subalgebra separating the points of the
compact space `X`, hence dense by the Stone–Weierstrass theorem.

## Main statements

* `TauCeti.isAF_continuousMap_pi`: `C((n : ℕ) → E n, ℂ)` is AF for finite discrete spaces `E n`.
-/

public section

open Set

namespace TauCeti

/-- The continuous functions from a finite space to a finite-dimensional topological vector space
form a finite-dimensional space. -/
theorem finiteDimensional_continuousMap_of_finite (Y : Type*) [TopologicalSpace Y] [Finite Y]
    (K M : Type*) [Field K] [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]
    [Module K M] [ContinuousConstSMul K M] [FiniteDimensional K M] :
    FiniteDimensional K C(Y, M) :=
  Module.Finite.of_injective (ContinuousMap.coeFnLinearMap K (α := Y) (M := M))
    DFunLike.coe_injective

variable {E : ℕ → Type*} [∀ n, TopologicalSpace (E n)] [∀ n, DiscreteTopology (E n)]
  [∀ n, Finite (E n)]

/-- The restriction `x ↦ (x 0, …, x (n - 1))` of a point of `∀ n, E n` to its first `n`
coordinates. -/
private def restrictFin (n : ℕ) : C((i : ℕ) → E i, (i : Fin n) → E i) :=
  ⟨fun x i ↦ x i, by fun_prop⟩

/-- **`C((n : ℕ) → E n, ℂ)` is AF** for finite discrete spaces `E n`; for instance, the continuous
functions on the Cantor space `ℕ → Bool` form an AF algebra. The `n`-th stage consists of the
functions depending only on the first `n` coordinates. -/
theorem isAF_continuousMap_pi : IsAF C((n : ℕ) → E n, ℂ) := by
  let φ (n : ℕ) := ContinuousMap.compStarAlgHom' ℂ ℂ (restrictFin (E := E) n)
  have hrange (n : ℕ) : ((φ n).range : Set C((n : ℕ) → E n, ℂ)) =
      (⊤ : NonUnitalStarSubalgebra ℂ C((i : Fin n) → E i, ℂ)).map (φ n).toNonUnitalStarAlgHom := by
    ext f
    exact ⟨fun ⟨g, hg⟩ ↦ ⟨g, trivial, hg⟩, fun ⟨g, _, hg⟩ ↦ ⟨g, hg⟩⟩
  have hmono : Monotone fun n ↦ (φ n).range := by
    intro m n hmn f ⟨g, hg⟩
    refine ⟨g.comp ⟨fun y i ↦ y (Fin.castLE hmn i), continuous_of_discreteTopology⟩, ?_⟩
    rw [← hg]
    rfl
  refine isAF_iff.2 ⟨fun n ↦ (⊤ : NonUnitalStarSubalgebra ℂ _).map (φ n).toNonUnitalStarAlgHom,
    fun m n hmn ↦ ?_, fun n ↦ ?_, ?_⟩
  · intro f hf
    rw [← SetLike.mem_coe, ← hrange] at hf ⊢
    exact hmono hmn hf
  · have := finiteDimensional_continuousMap_of_finite ((i : Fin n) → E i) ℂ ℂ
    exact NonUnitalStarSubalgebra.instFiniteDimensionalMap _ _
  · simp_rw [← hrange]
    rw [← StarSubalgebra.coe_iSup_of_directed hmono.directed_le, dense_iff_closure_eq,
      ← StarSubalgebra.topologicalClosure_coe,
      ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints]
    · rfl
    intro x y hxy
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
    classical
    let g : C((j : Fin (i + 1)) → E j, ℂ) :=
      ⟨fun z ↦ if z (Fin.last i) = x i then 1 else 0, continuous_of_discreteTopology⟩
    refine ⟨_, ⟨φ (i + 1) g, le_iSup (fun n ↦ (φ n).range) (i + 1) ⟨g, rfl⟩, rfl⟩, ?_⟩
    simp [φ, g, restrictFin, hi.symm]

end TauCeti
