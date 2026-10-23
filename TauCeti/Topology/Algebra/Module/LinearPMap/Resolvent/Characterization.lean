/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.LinearPMap
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Basic

/-!
# Characterizations of resolvent points of partial linear maps

For a partial linear map `A : X →ₗ.[𝕜] X`, a scalar `lambda` lies in `LinearPMap.resolventSet A`
when the shift `lambda • I - A : D(A) → X` has a continuous linear two-sided inverse. This file
characterizes this condition through the shift alone.

* `LinearPMap.isResolventAt_iff_surjective_and_apply_smul_sub`: a continuous linear map inverts
  the shift exactly when the shift is surjective and the map is a left inverse of it. The
  right-inverse identity and the domain condition are then automatic.
* `LinearPMap.mem_resolventSet_iff_isClosed_denseRange_apply_smul_sub`: `lambda` is a resolvent
  point exactly when the shift has closed dense range and its inverse on that range extends to a
  continuous linear operator on all of `X`. A left inverse forces the shift to be injective, so
  the extension condition is exactly the statement that the inverse on the range extends.
* `LinearPMap.IsResolventAt.isClosed`: an operator with a resolvent point is closed, its graph
  being the zero set of the continuous map `(x, w) ↦ R (lambda • x - w) - x`.

The normed forms, with a lower bound in place of the extension and the closed graph theorem for
closed operators, are in `TauCeti.Analysis.Normed.Operator.Resolvent.Characterization`.

## References

T. Kato, *Perturbation Theory for Linear Operators*, Section III.5.2;
Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section IV.1.
-/

public section

namespace LinearPMap

section Ring

variable {𝕜 X : Type*} [Ring 𝕜] [AddCommGroup X] [TopologicalSpace X] [Module 𝕜 X]
variable {A : X →ₗ.[𝕜] X} {lambda : 𝕜} {R : X →L[𝕜] X}

/-- A continuous linear map inverts `lambda • I - A` exactly when the shift maps `D(A)` onto `X`
and the map is a left inverse of the shift on `D(A)`. -/
theorem isResolventAt_iff_surjective_and_apply_smul_sub :
    IsResolventAt A lambda R ↔
      Function.Surjective (fun x : A.domain => lambda • (x : X) - A x) ∧
        ∀ x : A.domain, R (lambda • (x : X) - A x) = x := by
  refine ⟨fun h => ⟨h.smul_sub_surjective, h.apply_smul_sub⟩, fun ⟨hsurj, hR⟩ => ?_⟩
  have hmem (y : X) : R y ∈ A.domain := by
    obtain ⟨x, rfl⟩ := hsurj y
    rw [hR x]
    exact x.property
  refine ⟨hmem, fun y => ?_, hR⟩
  obtain ⟨x, rfl⟩ := hsurj y
  rw [congrArg A (Subtype.ext (hR x) : (⟨_, hmem _⟩ : A.domain) = x), hR x]

/-- **Resolvent characterization.** A scalar `lambda` lies in the resolvent set of `A` exactly
when the shift `lambda • I - A : D(A) → X` has closed dense range and some continuous linear
operator `R` on `X` satisfies `R (lambda • x - A x) = x` on `D(A)`.

The last condition makes the shift injective, so it says precisely that the inverse of the
shift on its range extends to the continuous linear operator `R` on the whole space. -/
theorem mem_resolventSet_iff_isClosed_denseRange_apply_smul_sub :
    lambda ∈ resolventSet A ↔
      _root_.IsClosed (Set.range fun x : A.domain => lambda • (x : X) - A x) ∧
        DenseRange (fun x : A.domain => lambda • (x : X) - A x) ∧
        ∃ R : X →L[𝕜] X, ∀ x : A.domain, R (lambda • (x : X) - A x) = x := by
  simp only [mem_resolventSet_iff, isResolventAt_iff_surjective_and_apply_smul_sub,
    exists_and_left, ← and_assoc]
  refine and_congr_left' ⟨fun h => ?_, fun ⟨hcl, hd⟩ => ?_⟩
  · rw [h.range_eq]
    exact ⟨isClosed_univ, h.denseRange⟩
  · exact Set.range_eq_univ.mp (hcl.closure_eq ▸ hd.closure_range)

end Ring

section CommRing

variable {𝕜 X : Type*} [CommRing 𝕜] [AddCommGroup X] [TopologicalSpace X] [Module 𝕜 X]
  [IsTopologicalAddGroup X] [ContinuousConstSMul 𝕜 X] [T2Space X]
variable {A : X →ₗ.[𝕜] X} {lambda : 𝕜} {R : X →L[𝕜] X}

/-- **An operator with a resolvent point is closed.** If `R` inverts `lambda • I - A`, the graph
of `A` is the set of pairs `(x, w)` with `R (lambda • x - w) = x`, which is closed because `R` is
continuous. -/
theorem IsResolventAt.isClosed (h : IsResolventAt A lambda R) : A.IsClosed := by
  have hgraph : (A.graph : Set (X × X)) = {p | R (lambda • p.1 - p.2) = p.1} := by
    ext p
    simp only [SetLike.mem_coe, Set.mem_ofPred_eq]
    refine ⟨(isResolventAt_iff_forall_mem_graph.mp h).2 p, fun hp => ?_⟩
    have hmem := (isResolventAt_iff_forall_mem_graph.mp h).1 (lambda • p.1 - p.2)
    rwa [hp, sub_sub_cancel] at hmem
  rw [LinearPMap.IsClosed, hgraph]
  exact isClosed_eq (R.continuous.comp ((continuous_fst.const_smul lambda).sub continuous_snd))
    continuous_fst

/-- An operator whose resolvent set contains a point is closed. -/
theorem isClosed_of_mem_resolventSet (h : lambda ∈ resolventSet A) : A.IsClosed :=
  (isResolventAt_resolvent h).isClosed

end CommRing

end LinearPMap

end
