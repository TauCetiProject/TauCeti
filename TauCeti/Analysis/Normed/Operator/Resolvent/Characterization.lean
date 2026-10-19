/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import TauCeti.Analysis.Normed.Operator.Resolvent.LowerBound
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Characterization

/-!
# Resolvent points of partial linear maps on normed spaces

On a normed space, a scalar `z` lies in the resolvent set of a partial linear map `A` exactly
when the shift `z • I - A : D(A) → X` has closed dense range and is bounded below: the lower
bound `c ‖x‖ ≤ ‖z • x - A x‖` is the boundedness of the inverse on the range, and a closed
dense range is all of `X`.

On a Banach space the closed graph theorem removes the boundedness condition for closed
operators: a closed `A` has `z` as a resolvent point exactly when the shift is a bijection
`D(A) → X`. Since an operator with a resolvent point is closed
(`LinearPMap.isClosed_of_mem_resolventSet`), the resolvent set of an arbitrary `A` on a Banach
space consists of the `z` with bijective shift if `A` is closed, and is empty otherwise.

## Main results

* `LinearPMap.mem_resolventSet_iff_isClosed_denseRange_norm_le`: the resolvent set through
  closed dense range and a lower bound.
* `LinearPMap.IsClosed.mem_resolventSet_iff_bijective`: for a closed operator on a Banach space,
  resolvent points are the points of bijectivity of the shift.
* `LinearPMap.mem_resolventSet_iff_isClosed_and_bijective`: on a Banach space, `z` is a resolvent
  point exactly when `A` is closed and the shift is bijective.

## References

T. Kato, *Perturbation Theory for Linear Operators*, Section III.5.2;
Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section IV.1.
-/

public section

namespace LinearPMap

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {A : X →ₗ.[𝕜] X} {z : 𝕜}

/-- **Resolvent characterization, normed form.** A scalar `z` lies in the resolvent set of `A`
exactly when the shift `z • I - A : D(A) → X` has closed dense range and is bounded below by a
positive multiple of `‖x‖` on `D(A)`. -/
theorem mem_resolventSet_iff_isClosed_denseRange_norm_le :
    z ∈ resolventSet A ↔
      _root_.IsClosed (Set.range fun x : A.domain => z • (x : X) - A x) ∧
        DenseRange (fun x : A.domain => z • (x : X) - A x) ∧
        ∃ c > 0, ∀ x : A.domain, c * ‖(x : X)‖ ≤ ‖z • (x : X) - A x‖ := by
  refine ⟨fun h => ?_, fun ⟨hcl, hd, c, hc, hbound⟩ => ?_⟩
  · obtain ⟨hcl, hd, R, hR⟩ := mem_resolventSet_iff_isClosed_denseRange_apply_smul_sub.mp h
    refine ⟨hcl, hd, (‖R‖ + 1)⁻¹, by positivity, fun x => ?_⟩
    rw [inv_mul_le_iff₀ (by positivity)]
    calc
      ‖(x : X)‖ = ‖R (z • (x : X) - A x)‖ := by rw [hR x]
      _ ≤ ‖R‖ * ‖z • (x : X) - A x‖ := R.le_opNorm _
      _ ≤ (‖R‖ + 1) * ‖z • (x : X) - A x‖ := by gcongr; linarith
  · exact mem_resolventSet_of_surjective_of_norm_le
      (Set.range_eq_univ.mp (hcl.closure_eq ▸ hd.closure_range)) hc hbound

variable [CompleteSpace X]

/-- **Resolvent points of a closed operator.** On a Banach space, a scalar `z` lies in the
resolvent set of a closed partial linear map `A` exactly when the shift `z • I - A : D(A) → X`
is bijective. By the closed graph theorem, the set-theoretic inverse of the shift is then
automatically bounded. -/
theorem IsClosed.mem_resolventSet_iff_bijective (hA : A.IsClosed) :
    z ∈ resolventSet A ↔ Function.Bijective fun x : A.domain => z • (x : X) - A x := by
  refine ⟨smul_sub_bijective, fun hbij => ?_⟩
  obtain ⟨J, hJ, hright, hleft⟩ := exists_linearMap_inverse_smul_sub hbij
  -- The graph of `J` is the preimage of the graph of `A` under `(y, x) ↦ (x, z • x - y)`.
  have hgraph : (J.graph : Set (X × X)) =
      (fun p : X × X => (p.2, z • p.2 - p.1)) ⁻¹' (A.graph : Set (X × X)) := by
    ext ⟨y, x⟩
    simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, Set.mem_preimage, mem_graph_iff]
    constructor
    · rintro rfl
      exact ⟨⟨J y, hJ y⟩, rfl, by rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', hright]⟩
    · rintro ⟨u, rfl, hAu⟩
      rw [← hleft u, hAu, sub_sub_cancel]
  have hclosed : _root_.IsClosed (J.graph : Set (X × X)) := by
    rw [hgraph]
    exact hA.preimage (continuous_snd.prodMk ((continuous_snd.const_smul z).sub continuous_fst))
  refine IsResolventAt.mem_resolventSet (R := ContinuousLinearMap.ofIsClosedGraph hclosed)
    (isResolventAt_iff_surjective_and_apply_smul_sub.mpr ⟨hbij.surjective, fun x => ?_⟩)
  rw [ContinuousLinearMap.coeFn_ofIsClosedGraph, hleft]

/-- **Resolvent characterization on a Banach space.** A scalar `z` lies in the resolvent set of
a partial linear map `A` exactly when `A` is closed and the shift `z • I - A : D(A) → X` is
bijective. -/
theorem mem_resolventSet_iff_isClosed_and_bijective :
    z ∈ resolventSet A ↔
      A.IsClosed ∧ Function.Bijective fun x : A.domain => z • (x : X) - A x :=
  ⟨fun h => ⟨isClosed_of_mem_resolventSet h, smul_sub_bijective h⟩,
    fun ⟨hA, hbij⟩ => hA.mem_resolventSet_iff_bijective.mpr hbij⟩

end LinearPMap

end
