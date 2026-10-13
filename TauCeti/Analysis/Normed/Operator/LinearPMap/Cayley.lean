/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Basic

/-!
# The Cayley transform of a partial linear map

For a partial linear map `A` on a complex normed space, the **Cayley transform**
`LinearPMap.cayley A = 1 + 2i R(-i)` is a bounded operator built from the resolvent
`R(z) = (z - A)⁻¹` at `-i`. Whenever `-i` is a resolvent point it sends `-i y - A y` to
`i y - A y` for every `y ∈ dom A` (`LinearPMap.cayley_neg_I_smul_sub_apply`), so it is the
bounded form of `(A - i)(A + i)⁻¹`. The Cayley transform determines `A`: the graph of `A`
consists of the pairs `(x - U x, i (x + U x))` (`LinearPMap.mem_graph_iff_exists_cayley`), which
is the operator identity `A = i (1 + U) (1 - U)⁻¹`. In particular `1` is not an eigenvalue of `U`.
If both `i` and `-i` are resolvent points, the Cayley transform is surjective.

The isometry and unitarity of the Cayley transform of a symmetric or self-adjoint operator are in
`TauCeti.Analysis.InnerProductSpace.LinearPMap.Cayley`.

## Main definitions

* `LinearPMap.cayley`: the Cayley transform `1 + 2i R(-i)` of a partial linear map.

## Main results

* `LinearPMap.cayley_neg_I_smul_sub_apply`: `U (-i y - A y) = i y - A y` on `dom A`.
* `LinearPMap.mem_graph_iff_exists_cayley`: the graph of `A` is
  `{(x - U x, i (x + U x)) | x}`.
* `LinearPMap.cayley_apply_eq_self_iff`: `1` is not an eigenvalue of `U`.
* `LinearPMap.cayley_surjective`: `U` is surjective when `±i` are resolvent points.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Section VIII.3 (the Cayley transform).
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Section 13.1.
-/

public section

noncomputable section

open Complex

namespace LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : E →ₗ.[ℂ] E}

/-- The **Cayley transform** `1 + 2i R(-i)` of a partial linear map `A`, where
`R(-i) = (-i - A)⁻¹` is its resolvent. When `-i` is a resolvent point this is the bounded form of
`(A - i)(A + i)⁻¹` (`LinearPMap.cayley_neg_I_smul_sub_apply`); otherwise the resolvent, and hence
the Cayley transform, is a junk value. -/
def cayley (A : E →ₗ.[ℂ] E) : E →L[ℂ] E :=
  1 + (2 * I) • A.resolvent (-I)

theorem cayley_apply (A : E →ₗ.[ℂ] E) (x : E) :
    A.cayley x = x + (2 * I) • A.resolvent (-I) x := by
  simp [cayley]

/-- The Cayley transform sends `-i y - A y` to `i y - A y` on the domain of `A`. -/
theorem cayley_neg_I_smul_sub_apply (h : -I ∈ A.resolventSet) (y : A.domain) :
    A.cayley (-I • (y : E) - A y) = I • (y : E) - A y := by
  rw [cayley_apply, resolvent_smul_sub_apply h y]
  module

/-- **The Cayley transform determines the operator.** If `-i` is a resolvent point of `A`, the
graph of `A` consists exactly of the pairs `(x - U x, i (x + U x))`, where `U` is the Cayley
transform; this is the operator identity `A = i (1 + U) (1 - U)⁻¹`. -/
theorem mem_graph_iff_exists_cayley (h : -I ∈ A.resolventSet) {p : E × E} :
    p ∈ A.graph ↔ ∃ x : E, (x - A.cayley x, I • (x + A.cayley x)) = p := by
  constructor
  · obtain ⟨p₁, p₂⟩ := p
    intro hp
    obtain ⟨y, rfl, rfl⟩ := A.mem_graph_iff.mp hp
    refine ⟨(I / 2) • (-I • (y : E) - A y), ?_⟩
    rw [ContinuousLinearMap.map_smul, cayley_neg_I_smul_sub_apply h, Prod.mk.injEq]
    constructor <;> match_scalars <;> first | ring1 | linear_combination -I_sq
  · rintro ⟨x, rfl⟩
    have hmem := (isResolventAt_iff_forall_mem_graph.mp (isResolventAt_resolvent h)).1 x
    convert A.graph.smul_mem (-(2 * I)) hmem using 1
    rw [Prod.smul_mk, cayley_apply, Prod.mk.injEq]
    constructor <;> match_scalars <;> ring

/-- **`1` is not an eigenvalue of the Cayley transform** at an operator having `-i` as a
resolvent point. -/
@[simp]
theorem cayley_apply_eq_self_iff (h : -I ∈ A.resolventSet) {x : E} :
    A.cayley x = x ↔ x = 0 := by
  refine ⟨fun hx => ?_, fun hx => by rw [hx, ContinuousLinearMap.map_zero]⟩
  have hmem := (mem_graph_iff_exists_cayley h).mpr ⟨x, rfl⟩
  rw [hx, sub_self] at hmem
  have h0 : I • (x + x) = 0 := A.graph_fst_eq_zero_snd hmem rfl
  rwa [← two_smul ℂ x, smul_smul, smul_eq_zero_iff_right (by simp)] at h0

/-- The Cayley transform is surjective when both `i` and `-i` are resolvent points. -/
theorem cayley_surjective (hp : I ∈ A.resolventSet) (hm : -I ∈ A.resolventSet) :
    Function.Surjective A.cayley := fun y =>
  ⟨-I • A.resolvent I y - A ⟨A.resolvent I y, resolvent_mem_domain hp y⟩,
    (cayley_neg_I_smul_sub_apply hm ⟨A.resolvent I y, resolvent_mem_domain hp y⟩).trans
      (smul_sub_apply_resolvent hp y)⟩

end LinearPMap

end
