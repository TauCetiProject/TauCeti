/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.GradedCorrespondence.Basic
public import TauCeti.Algebra.Module.GradedModule.Trivial

/-!
# Graph correspondences into trivially graded modules

Give the target of a graph correspondence Tau Ceti's `trivialGrading`, concentrated in degree
`0 : ℤ`, and let the source carry an arbitrary decomposition. Then each forward transfer from
a homogeneous piece is the linear equivalence `e` in degree zero and zero in every other
degree; symmetrically, each backward transfer into a trivially graded source is `e.symm` in
degree zero. Thus an ungraded equivalence and its inverse are recovered as degree-zero
transfers, regardless of the degree of the input.

For doubling on `ℚ`, with both sides concentrated in degree zero, this gives
`B^{0,0}(1) = 2` and `B^{0,η}(1) = 0` for `η ≠ 0`.

The two transfer formulas and the two check values are not simp lemmas: `simp` already
evaluates such transfers through `GradedCorrespondence.transfer_apply`, the `graph` field
lemmas and `TauCeti.proj_trivialGrading`, and for the doubling graph after rewriting with
`doubleGraph_def`.

Adapted from `Mei/LinearAlgebra/GradedCorrespondence/Trivial.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public section

open TauCeti

namespace TauCeti.GradedCorrespondence

variable {R U V ι κ : Type*} [Semiring R] [AddCommMonoid U] [Module R U]
  [AddCommMonoid V] [Module R V]

/-- A forward graph transfer into a trivially graded module is the equivalence in degree
zero and vanishes in every other degree. The source grading is arbitrary. -/
theorem graph_trivialGrading_transfer_apply (𝒰 : ι → Submodule R U) (e : U ≃ₗ[R] V)
    (i : (Set.univ : Set ι)) (j : ℤ) (a : 𝒰 i) :
    ((graph 𝒰 (trivialGrading R V) e).transfer i j a : V) =
      if j = 0 then e a else 0 := by
  rw [graph_transfer_apply, proj_trivialGrading]

/-- A backward graph transfer into a trivially graded module is the inverse equivalence in
degree zero and vanishes in every other degree. The target grading is arbitrary. -/
theorem graph_trivialGrading_symm_transfer_apply (𝒱 : κ → Submodule R V) (e : U ≃ₗ[R] V)
    (j : (Set.univ : Set κ)) (i : ℤ) (a : 𝒱 j) :
    ((graph (trivialGrading R U) 𝒱 e).symm.transfer j i a : U) =
      if i = 0 then e.symm a else 0 := by
  rw [graph_symm_transfer_apply, proj_trivialGrading]

namespace Examples

/-- Multiplication by `2` on `ℚ`. -/
noncomputable def double : ℚ ≃ₗ[ℚ] ℚ :=
  LinearEquiv.smulOfNeZero ℚ ℚ 2 two_ne_zero

/-- Doubling sends `a` to `2 * a`. -/
@[simp]
theorem double_apply (a : ℚ) : double a = 2 * a := (rfl)

/-- The graph of doubling, with `ℚ` concentrated in degree zero on both sides. -/
noncomputable def doubleGraph :
    GradedCorrespondence (B := ℚ) (trivialGrading ℚ ℚ) (trivialGrading ℚ ℚ)
      Set.univ Set.univ :=
  graph (trivialGrading ℚ ℚ) (trivialGrading ℚ ℚ) double

/-- The doubling correspondence is the graph of `double`. -/
theorem doubleGraph_def :
    doubleGraph = graph (trivialGrading ℚ ℚ) (trivialGrading ℚ ℚ) double := (rfl)

/-- The unit in degree zero, as an admissible homogeneous input. -/
def unitInput : trivialGrading ℚ ℚ ((⟨0, Set.mem_univ 0⟩ : (Set.univ : Set ℤ)) : ℤ) :=
  ⟨1, by simp⟩

/-- The degree-zero input `unitInput` is the rational number `1`. -/
@[simp]
theorem coe_unitInput : (unitInput : ℚ) = 1 := (rfl)

/-- The degree-zero transfer of the doubling graph sends `1` to `2`. -/
theorem doubleGraph_transfer_zero :
    (doubleGraph.transfer ⟨0, Set.mem_univ 0⟩ 0 unitInput : ℚ) = 2 := by
  rw [doubleGraph_def, graph_trivialGrading_transfer_apply, ite_eq_left rfl, coe_unitInput,
    double_apply, mul_one]

/-- Every transfer of the doubling graph to a nonzero degree vanishes on `1`. -/
theorem doubleGraph_transfer_of_ne_zero {η : ℤ} (hη : η ≠ 0) :
    (doubleGraph.transfer ⟨0, Set.mem_univ 0⟩ η unitInput : ℚ) = 0 := by
  rw [doubleGraph_def, graph_trivialGrading_transfer_apply]
  exact ite_eq_right_iff.mpr fun h ↦ (hη h).elim

end Examples

end TauCeti.GradedCorrespondence
