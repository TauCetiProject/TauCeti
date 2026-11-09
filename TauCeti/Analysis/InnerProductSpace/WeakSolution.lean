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

If the formal adjoint is bounded below, `c ‖ι η‖ ≤ ‖S η‖` with `c > 0`, then `L` has a bounded
weak right inverse: there is a continuous linear map `Q : G → H` with `‖Q‖ ≤ c⁻¹` such that
`Q f` is a weak solution of `L y = f` for every `f`, and `Q f` is orthogonal to the weak kernel
(`LinearMap.exists_continuousLinearMap_inner_apply_eq_of_mul_norm_le`). A weak solution
orthogonal to the weak kernel is unique (`LinearMap.eq_of_inner_apply_eq_of_mem_orthogonal`),
so `Q f` is the weak solution of least norm. In this sense `L` has vanishing weak cokernel, and
`Q` is the operator `L* (L L*)⁻¹` of the classical theory, defined without first realizing
`L L*` as an operator.

The lower bound makes `S η ↦ ι η` a bounded operator on the range of `S`. Its canonical factor
`H → G` through the inclusion of that range (`ContinuousLinearMap.factorThru`) extends it to the
closure and by zero on `(range S)ᗮ`, and `Q` is the Hilbert adjoint of this factor. Lions'
representation theorem (`LinearMap.exists_forall_apply_eq_and_norm_le_of_coercive`) produces a
weak solution for each single right-hand side, through a Hahn–Banach extension; the solution
here is the canonical one and depends linearly and continuously on `f`.

## Main results

* `LinearMap.exists_continuousLinearMap_inner_apply_eq_of_mul_norm_le`: the bounded weak right
  inverse.
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

/-- **Bounded weak right inverse.** Let `S : D → H` and `ι : D → G` be linear maps into Hilbert
spaces with `c ‖ι η‖ ≤ ‖S η‖` for some `c > 0`; think of `S` as the formal adjoint of an operator
`L` on test fields and of `ι` as the inclusion of the test fields. Then there is a continuous
linear map `Q : G → H` with `‖Q‖ ≤ c⁻¹` such that `⟪Q f, S η⟫ = ⟪f, ι η⟫` for all `f` and `η`,
that is, `Q f` is a weak solution of `L y = f`, and `Q f` lies in `(range S)ᗮᗮ`, the closure of
the range of `S`, which is orthogonal to the weak kernel `(range S)ᗮ` of `L`. -/
theorem exists_continuousLinearMap_inner_apply_eq_of_mul_norm_le (S : D →ₗ[𝕜] H)
    (ι : D →ₗ[𝕜] G) {c : ℝ} (hc : 0 < c) (h : ∀ η, c * ‖ι η‖ ≤ ‖S η‖) :
    ∃ Q : G →L[𝕜] H, ‖Q‖ ≤ c⁻¹ ∧ (∀ f, Q f ∈ (range S)ᗮᗮ) ∧
      ∀ f η, ⟪Q f, S η⟫_𝕜 = ⟪f, ι η⟫_𝕜 := by
  -- The rule `S η ↦ ι η` is a bounded operator on the range of `S`.
  have hb (η : D) : ‖ι η‖ ≤ c⁻¹ * ‖S η‖ := by
    rw [le_inv_mul_iff₀ hc]
    exact h η
  let T : range S →L[𝕜] G := ι.compLeftInverse S
  have hT (η : D) : T ⟨S η, mem_range_self S η⟩ = ι η :=
    compLeftInverse_apply_of_bdd ι S ⟨c⁻¹, hb⟩ η _ rfl
  have hTb (y : range S) : ‖T y‖ ≤ c⁻¹ * ‖(range S).subtypeL y‖ := by
    obtain ⟨_, η, rfl⟩ := y
    rw [hT]
    exact hb η
  -- Its canonical factor `V : H → G` through the inclusion of the range sends `S η` to `ι η`
  -- and vanishes on `(range S)ᗮ`; the weak right inverse is its Hilbert adjoint.
  let V : H →L[𝕜] G := T.factorThru (range S).subtypeL
  have hV (η : D) : V (S η) = ι η := by
    rw [← hT]
    exact ContinuousLinearMap.factorThru_apply_apply ⟨c⁻¹, hTb⟩ ⟨S η, mem_range_self S η⟩
  refine ⟨ContinuousLinearMap.adjoint V, ?_, fun f ↦ ?_, fun f η ↦ ?_⟩
  · rw [LinearIsometryEquiv.norm_map]
    exact ContinuousLinearMap.norm_factorThru_le (inv_nonneg.2 hc.le) hTb
  · refine orthogonal_le (fun y hy ↦ ?_) (V.adjoint_apply_mem_orthogonal_ker f)
    refine ContinuousLinearMap.factorThru_apply_of_mem_orthogonal ?_
    rwa [Submodule.toLinearMap_subtypeL, Submodule.range_subtype]
  · rw [ContinuousLinearMap.adjoint_inner_left, hV]

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
