/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.Gram.Factor

/-!
# Bounded weak right inverses from a lower bound on a formal adjoint

Let `H` and `G` be Hilbert spaces, and let `L` be an operator, typically a differential operator,
taking fields in `H` to fields in `G` and known only through its formal adjoint on a space `D` of
test fields: a linear map `S : D → H`, playing the role of `L*`, together with the inclusion
`ι : D → G` of the test fields. A vector `y ∈ H` is a *weak solution* of `L y = f` if
`⟪y, S η⟫ = ⟪f, ι η⟫` for every test field `η`, and the *weak kernel* of `L` is the set of weak
solutions of `L y = 0`, namely the orthogonal complement `(range S)ᗮ`.

If the formal adjoint is bounded below, `‖ι η‖ ≤ C ‖S η‖`, then `L` has a bounded weak right
inverse: the continuous linear map `Q = LinearMap.weakRightInverse S ι : G → H` has `‖Q‖ ≤ C`,
`Q f` is a weak solution of `L y = f` for every `f`, and `Q f` is orthogonal to the weak kernel.
A weak solution orthogonal to the weak kernel is unique
(`LinearMap.eq_of_inner_apply_eq_of_mem_orthogonal`), so `Q f` is the weak solution of least
norm. In this sense `L` has vanishing weak cokernel, and `Q` is the operator `L* (L L*)⁻¹` of the
classical theory, defined without first realizing `L L*` as an operator.

The lower bound makes `S η ↦ ι η` a bounded operator on the range of `S`. Its canonical factor
`H → G` through the inclusion of that range (`ContinuousLinearMap.factorThru`) extends it to the
closure and by zero on `(range S)ᗮ`, and `Q` is the Hilbert adjoint of this factor. Lions'
representation theorem (`LinearMap.exists_forall_apply_eq_and_norm_le_of_coercive`) produces a
weak solution for each single right-hand side, through a Hahn–Banach extension; the solution
here is the canonical one and depends linearly and continuously on `f`.

## Main results

* `LinearMap.weakRightInverse`: the weak right inverse.
* `LinearMap.inner_weakRightInverse_apply`, `LinearMap.weakRightInverse_apply_mem_orthogonal`,
  `LinearMap.norm_weakRightInverse_le`: it produces weak solutions, orthogonal to the weak kernel,
  and is bounded by the constant of the lower bound.
* `LinearMap.eq_of_inner_apply_eq_of_mem_orthogonal`: uniqueness of weak solutions orthogonal to
  the weak kernel.

## References

* J.-L. Lions, *Équations différentielles opérationnelles et problèmes aux limites*,
  Grundlehren **111**, Springer, 1961.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Section 4.1.
-/

public section

open Submodule
open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 D H G : Type*} [RCLike 𝕜] [AddCommGroup D] [Module 𝕜 D]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- The **weak right inverse** of the operator `L` whose formal adjoint on the test fields `D` is
`S : D → H`, with `ι : D → G` the inclusion of the test fields. It is the Hilbert adjoint of the
canonical factor `H → G` of the rule `S η ↦ ι η` through the inclusion of the range of `S`
(`ContinuousLinearMap.factorThru` applied to `LinearMap.compLeftInverse`).

When `‖ι η‖ ≤ C ‖S η‖` for some `C`, its values are weak solutions of `L y = f`
(`LinearMap.inner_weakRightInverse_apply`), orthogonal to the weak kernel
(`LinearMap.weakRightInverse_apply_mem_orthogonal`), and it has norm at most `C`
(`LinearMap.norm_weakRightInverse_le`). Without such a bound it is zero. -/
noncomputable def weakRightInverse (S : D →ₗ[𝕜] H) (ι : D →ₗ[𝕜] G) : G →L[𝕜] H :=
  ContinuousLinearMap.adjoint ((ι.compLeftInverse S).factorThru (range S).subtypeL)

variable {S : D →ₗ[𝕜] H} {ι : D →ₗ[𝕜] G}

omit [CompleteSpace H] [CompleteSpace G] in
/-- The bound `‖ι η‖ ≤ C ‖S η‖`, transported to the rule `S η ↦ ι η` on the range of `S`. -/
private theorem norm_compLeftInverse_le {C : ℝ} (h : ∀ η, ‖ι η‖ ≤ C * ‖S η‖) (y : range S) :
    ‖ι.compLeftInverse S y‖ ≤ C * ‖(range S).subtypeL y‖ := by
  obtain ⟨_, η, rfl⟩ := y
  rw [compLeftInverse_apply_of_bdd ι S ⟨C, h⟩ η _ rfl]
  exact h η

/-- **Weak solutions.** If `‖ι η‖ ≤ C ‖S η‖` for some `C`, then
`⟪weakRightInverse S ι f, S η⟫ = ⟪f, ι η⟫` for all `f` and `η`: the weak right inverse sends `f`
to a weak solution of `L y = f`. -/
theorem inner_weakRightInverse_apply (h : ∃ C, ∀ η, ‖ι η‖ ≤ C * ‖S η‖) (f : G) (η : D) :
    ⟪S.weakRightInverse ι f, S η⟫_𝕜 = ⟪f, ι η⟫_𝕜 := by
  obtain ⟨C, hC⟩ := h
  rw [weakRightInverse, ContinuousLinearMap.adjoint_inner_left,
    ← compLeftInverse_apply_of_bdd ι S ⟨C, hC⟩ η _ rfl]
  exact congrArg (⟪f, ·⟫_𝕜) (ContinuousLinearMap.factorThru_apply_apply
    ⟨C, norm_compLeftInverse_le hC⟩ ⟨S η, mem_range_self S η⟩)

/-- The weak right inverse takes values in `(range S)ᗮᗮ`, the closure of the range of `S`, which
is orthogonal to the weak kernel `(range S)ᗮ` of `L`. -/
theorem weakRightInverse_apply_mem_orthogonal (S : D →ₗ[𝕜] H) (ι : D →ₗ[𝕜] G) (f : G) :
    S.weakRightInverse ι f ∈ (range S)ᗮᗮ := by
  -- The factor vanishes on `(range S)ᗮ`, so its adjoint lands in the orthogonal of its kernel.
  refine orthogonal_le (fun y hy ↦ ?_) (ContinuousLinearMap.adjoint_apply_mem_orthogonal_ker _ f)
  refine ContinuousLinearMap.factorThru_apply_of_mem_orthogonal ?_
  rwa [Submodule.toLinearMap_subtypeL, Submodule.range_subtype]

/-- **Norm bound.** If `‖ι η‖ ≤ C ‖S η‖` with `0 ≤ C`, the weak right inverse has norm at most
`C`. -/
theorem norm_weakRightInverse_le {C : ℝ} (hC : 0 ≤ C) (h : ∀ η, ‖ι η‖ ≤ C * ‖S η‖) :
    ‖S.weakRightInverse ι‖ ≤ C := by
  rw [weakRightInverse, LinearIsometryEquiv.norm_map]
  exact ContinuousLinearMap.norm_factorThru_le hC (norm_compLeftInverse_le h)

omit [CompleteSpace H] in
/-- **Uniqueness of weak solutions orthogonal to the weak kernel.** If `y` and `y'` both lie in
`(range S)ᗮᗮ`, the orthogonal complement of the weak kernel `(range S)ᗮ`, and pair in the same
way with every `S η`, then `y = y'`. In particular two weak solutions of the same equation that
are orthogonal to the weak kernel coincide. -/
theorem eq_of_inner_apply_eq_of_mem_orthogonal (S : D →ₗ[𝕜] H) {y y' : H}
    (hy : y ∈ (range S)ᗮᗮ) (hy' : y' ∈ (range S)ᗮᗮ)
    (h : ∀ η, ⟪y, S η⟫_𝕜 = ⟪y', S η⟫_𝕜) : y = y' := by
  have hsub : y - y' ∈ (range S)ᗮ := by
    rw [mem_orthogonal]
    rintro _ ⟨η, rfl⟩
    rw [inner_sub_right, ← inner_conj_symm (S η) y, ← inner_conj_symm (S η) y', h η, sub_self]
  rw [← sub_eq_zero]
  exact (mem_bot 𝕜).1 ((orthogonal_disjoint _).le_bot ⟨hsub, sub_mem hy hy'⟩)

end LinearMap
