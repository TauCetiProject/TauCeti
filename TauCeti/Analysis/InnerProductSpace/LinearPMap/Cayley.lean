/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-!
# The Cayley transform of a self-adjoint partial linear map

For a partial linear map `A` on a complex normed space, the **Cayley transform**
`LinearPMap.cayley A = 1 + 2i R(-i)` is a bounded operator built from the resolvent
`R(z) = (z - A)⁻¹` at `-i`. Whenever `-i` is a resolvent point it sends `-i y - A y` to
`i y - A y` for every `y ∈ dom A` (`LinearPMap.cayley_neg_I_smul_sub_apply`), so it is the
bounded form of `(A - i)(A + i)⁻¹`. The Cayley transform determines `A`: the graph of `A`
consists of the pairs `(x - U x, i (x + U x))` (`LinearPMap.mem_graph_iff_exists_cayley`), which
is the operator identity `A = i (1 + U) (1 - U)⁻¹`. In particular `1` is not an eigenvalue of `U`.

For a symmetric `A` with `-i` as a resolvent point, the identity `‖-i y - A y‖ = ‖i y - A y‖`
makes the Cayley transform an isometry. If both `i` and `-i` are resolvent points, it is
surjective. Hence the Cayley transform of a
self-adjoint partial linear map on a complex Hilbert space is unitary, and in particular
star-normal. This turns the spectral theory of an unbounded self-adjoint operator into that of a
bounded unitary operator.

## Main definitions

* `LinearPMap.cayley`: the Cayley transform `1 + 2i R(-i)` of a partial linear map.

## Main results

* `LinearPMap.cayley_neg_I_smul_sub_apply`: `U (-i y - A y) = i y - A y` on `dom A`.
* `LinearPMap.mem_graph_iff_exists_cayley`: the graph of `A` is
  `{(x - U x, i (x + U x)) | x}`.
* `LinearPMap.cayley_apply_eq_self_iff`: `1` is not an eigenvalue of `U`.
* `LinearPMap.cayley_surjective`: `U` is surjective when `±i` are resolvent points.
* `LinearPMap.IsFormalAdjoint.norm_cayley_apply`: `U` is isometric for symmetric `A`.
* `IsSelfAdjoint.cayley_mem_unitary`, `IsSelfAdjoint.isStarNormal_cayley`: the Cayley transform
  of a self-adjoint partial linear map is unitary and star-normal.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Section VIII.3 (the Cayley transform).
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Section 13.1.
-/

public section

noncomputable section

open Complex

namespace LinearPMap

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : E →ₗ.[ℂ] E}

/-- The **Cayley transform** `1 + 2i R(-i)` of a partial linear map `A`, where
`R(-i) = (-i - A)⁻¹` is its resolvent. When `-i` is a resolvent point this is the bounded form of
`(A - i)(A + i)⁻¹` (`LinearPMap.cayley_neg_I_smul_sub_apply`); otherwise the resolvent, and hence
the Cayley transform, is a junk value. -/
def cayley (A : E →ₗ.[ℂ] E) : E →L[ℂ] E :=
  1 + (2 * I) • A.resolvent (-I)

theorem cayley_def (A : E →ₗ.[ℂ] E) : A.cayley = 1 + (2 * I) • A.resolvent (-I) := by
  rw [cayley]

theorem cayley_apply (A : E →ₗ.[ℂ] E) (x : E) :
    A.cayley x = x + (2 * I) • A.resolvent (-I) x := by
  simp [cayley_def]

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

end NormedSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {A : E →ₗ.[ℂ] E}

/-- **The Cayley transform of a symmetric operator is isometric** whenever `-i` is a resolvent
point: `‖-i y - A y‖² = ‖y‖² + ‖A y‖² = ‖i y - A y‖²` for `y ∈ dom A`. -/
theorem IsFormalAdjoint.norm_cayley_apply (hA : A.IsFormalAdjoint A) (h : -I ∈ A.resolventSet)
    (x : E) : ‖A.cayley x‖ = ‖x‖ := by
  obtain ⟨y, rfl⟩ : ∃ y : A.domain, -I • (y : E) - A y = x :=
    ⟨⟨A.resolvent (-I) x, resolvent_mem_domain h x⟩, smul_sub_apply_resolvent h x⟩
  rw [cayley_neg_I_smul_sub_apply h, ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    hA.norm_smul_sub_sq I, hA.norm_smul_sub_sq (-I)]
  simp

variable [CompleteSpace E]

/-- The Cayley transform of a self-adjoint partial linear map preserves norms. -/
theorem _root_.IsSelfAdjoint.norm_cayley_apply (hA : IsSelfAdjoint A) (x : E) :
    ‖A.cayley x‖ = ‖x‖ :=
  hA.isFormalAdjoint.norm_cayley_apply (hA.mem_resolventSet_of_im_ne_zero (z := -I) (by simp)) x

/-- The Cayley transform of a self-adjoint partial linear map is surjective. -/
theorem _root_.IsSelfAdjoint.cayley_surjective (hA : IsSelfAdjoint A) :
    Function.Surjective A.cayley :=
  LinearPMap.cayley_surjective (hA.mem_resolventSet_of_im_ne_zero (z := I) (by simp))
    (hA.mem_resolventSet_of_im_ne_zero (z := -I) (by simp))

/-- **The Cayley transform of a self-adjoint partial linear map is unitary.** -/
theorem _root_.IsSelfAdjoint.cayley_mem_unitary (hA : IsSelfAdjoint A) :
    A.cayley ∈ unitary (E →L[ℂ] E) := by
  -- The isometry gives `U† U = 1`; surjectivity upgrades it to `U U† = 1`.
  have hleft : star A.cayley * A.cayley = 1 := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
      ← ContinuousLinearMap.norm_map_iff_adjoint_comp_self]
    exact hA.norm_cayley_apply
  refine Unitary.mem_iff.mpr ⟨hleft, ContinuousLinearMap.ext fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hA.cayley_surjective y
  have hx : star A.cayley (A.cayley x) = x := by
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using
      congr($hleft x)
  rw [mul_apply_eq_comp, hx, one_apply_eq_self]

/-- The Cayley transform of a self-adjoint partial linear map is star-normal. -/
theorem _root_.IsSelfAdjoint.isStarNormal_cayley (hA : IsSelfAdjoint A) :
    IsStarNormal A.cayley :=
  isStarNormal_of_mem_unitary hA.cayley_mem_unitary

end InnerProductSpace

end LinearPMap

end
