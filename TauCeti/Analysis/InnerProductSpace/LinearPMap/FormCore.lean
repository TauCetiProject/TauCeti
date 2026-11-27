/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Friedrichs.Basic
import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore

/-!
# Form cores

Let `S` be a symmetric partial operator on `E` with lower bound `γ`. Its form `⟪S x, y⟫_𝕜` has the
form completion `LinearPMap.FriedrichsSpace S γ hS`, the form domain of the Friedrichs extension of
`S`. A subspace `D` of the domain of `S` is a **form core** (`LinearPMap.IsFormCore`) when its image
is dense in the form completion, that is dense for the form norm
`(re ⟪S x, x⟫_𝕜 + (1 - γ) * ‖x‖ ^ 2) ^ (1 / 2)`.

The domain of `S` is a form core (`LinearPMap.isFormCore_domain`): this is the statement that the
domain of `S` is a form core of the Friedrichs extension. A subspace is a form core exactly when it
approximates every vector of the domain of `S` in the form norm (`LinearPMap.isFormCore_iff`). A
graph core of `S`, in the sense of Mathlib's `LinearPMap.HasCore`, is a form core
(`LinearPMap.HasCore.isFormCore`), since the form norm is bounded by the graph norm:
`‖x‖_S ^ 2 ≤ ‖S x‖ * ‖x‖ + |1 - γ| * ‖x‖ ^ 2` (`LinearPMap.norm_toFriedrichsSpace_sq_le`). For a
self-adjoint `S` bounded below, whose Friedrichs extension is `S` itself, this says that every graph
core of `S` is a form core of its closed form.

## Main declarations

* `LinearPMap.IsFormCore`: a form core of the form of `S`.
* `LinearPMap.isFormCore_iff`: form cores are the subspaces that approximate in the form norm.
* `LinearPMap.isFormCore_domain`: the domain of `S` is a form core.
* `LinearPMap.HasCore.isFormCore`: a graph core is a form core.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), Chapter VI, §1.4.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Graduate Texts in
  Mathematics 265, Springer (2012), §10.1.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {S : E →ₗ.[𝕜] E} {γ : ℝ}

/-- A subspace `D` of the domain of a symmetric operator `S` with lower bound `γ` is a **form core**
of its form when the image of `D` is dense in the form completion `FriedrichsSpace S γ hS`. -/
structure IsFormCore (hS : S.IsSymmetricBoundedBelow γ) (D : Submodule 𝕜 E) : Prop where
  /-- A form core lies in the domain of `S`. -/
  le_domain : D ≤ S.domain
  /-- A form core is dense in the form completion. -/
  dense : Dense (toFriedrichsSpace hS '' {x : S.domain | (x : E) ∈ D})

variable (hS : S.IsSymmetricBoundedBelow γ)

/-- A subspace `D` of the domain of `S` is a form core exactly when every vector of the domain of
`S` is approximated in the form norm by vectors of `D`. -/
theorem isFormCore_iff {D : Submodule 𝕜 E} :
    IsFormCore hS D ↔ D ≤ S.domain ∧ ∀ x : S.domain, ∀ ε > 0,
      ∃ d : S.domain, (d : E) ∈ D ∧ ‖toFriedrichsSpace hS (x - d)‖ < ε := by
  refine ⟨fun h => ⟨h.le_domain, fun x ε hε => ?_⟩, fun ⟨hD, h⟩ => ⟨hD, ?_⟩⟩
  · obtain ⟨_, ⟨d, hd, rfl⟩, hdist⟩ := h.dense.exists_dist_lt (toFriedrichsSpace hS x) hε
    exact ⟨d, hd, by rwa [dist_eq_norm, ← (toFriedrichsSpace hS).map_sub] at hdist⟩
  · refine ((denseRange_toFriedrichsSpace hS).mono ?_).of_closure
    rintro _ ⟨x, rfl⟩
    refine Metric.mem_closure_iff.mpr fun ε hε => ?_
    obtain ⟨d, hd, hlt⟩ := h x ε hε
    exact ⟨_, ⟨d, hd, rfl⟩, by rwa [dist_eq_norm, ← (toFriedrichsSpace hS).map_sub]⟩

variable {hS} in
/-- A subspace of the domain of `S` containing a form core is a form core. -/
theorem IsFormCore.mono {D D' : Submodule 𝕜 E} (h : IsFormCore hS D) (hDD' : D ≤ D')
    (hD' : D' ≤ S.domain) : IsFormCore hS D' :=
  ⟨hD', h.dense.mono (Set.image_mono fun _ hx => hDD' hx)⟩

/-- The form norm is bounded by the graph norm: `‖x‖_S ^ 2 ≤ ‖S x‖ * ‖x‖ + |1 - γ| * ‖x‖ ^ 2`. -/
theorem norm_toFriedrichsSpace_sq_le (x : S.domain) :
    ‖toFriedrichsSpace hS x‖ ^ 2 ≤ ‖S x‖ * ‖(x : E)‖ + |1 - γ| * ‖(x : E)‖ ^ 2 := by
  rw [norm_toFriedrichsSpace_sq]
  gcongr
  · exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  · exact le_abs_self _

/-- The form norm is bounded by the maximum of `‖x‖` and `‖S x‖`:
`‖x‖_S ^ 2 ≤ (1 + |1 - γ|) * max ‖x‖ ‖S x‖ ^ 2`. -/
theorem norm_toFriedrichsSpace_sq_le_mul_max_sq (x : S.domain) :
    ‖toFriedrichsSpace hS x‖ ^ 2 ≤ (1 + |1 - γ|) * max ‖(x : E)‖ ‖S x‖ ^ 2 := by
  calc ‖toFriedrichsSpace hS x‖ ^ 2 ≤ ‖S x‖ * ‖(x : E)‖ + |1 - γ| * ‖(x : E)‖ ^ 2 :=
        norm_toFriedrichsSpace_sq_le hS x
    _ ≤ max ‖(x : E)‖ ‖S x‖ * max ‖(x : E)‖ ‖S x‖ + |1 - γ| * max ‖(x : E)‖ ‖S x‖ ^ 2 := by
        gcongr
        exacts [le_max_right _ _, le_max_left _ _, le_max_left _ _]
    _ = (1 + |1 - γ|) * max ‖(x : E)‖ ‖S x‖ ^ 2 := by ring

/-- The domain of `S` is a form core: it is dense in the form completion, the form domain of the
Friedrichs extension of `S`. -/
theorem isFormCore_domain : IsFormCore hS S.domain where
  le_domain := le_rfl
  dense := by
    rw [Set.eq_univ_of_forall (s := {x : S.domain | (x : E) ∈ S.domain}) fun x => x.property,
      Set.image_univ]
    exact denseRange_toFriedrichsSpace hS

/-- **A graph core is a form core.** If `D` is a graph core of `S`, then `D` is dense in the form
completion, because the form norm is bounded by the graph norm. -/
theorem HasCore.isFormCore {D : Submodule 𝕜 E} (hD : S.HasCore D) : IsFormCore hS D := by
  refine (isFormCore_iff hS).mpr ⟨hD.le_domain, fun x ε hε => ?_⟩
  have hx : ((x : E), S x) ∈ _root_.closure ((S.domRestrict D).graph : Set (E × E)) :=
    hD.graph_subset_of_isClosed isClosed_closure subset_closure (S.mem_graph x)
  set C := 1 + |1 - γ|
  have hC1 : 1 ≤ C := le_add_of_nonneg_right (abs_nonneg _)
  obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp hx (ε / C) (by positivity)
  obtain ⟨y, hy₁, hy₂⟩ := (mem_graph_iff _).mp hp
  let d : S.domain := ⟨y, y.property.right⟩
  have hSd : S d = p.2 := by rw [← hy₂]; exact (domRestrict_apply rfl).symm
  refine ⟨d, y.property.left, lt_of_pow_lt_pow_left₀ 2 hε.le
    ((norm_toFriedrichsSpace_sq_le_mul_max_sq hS _).trans_lt ?_)⟩
  rw [Prod.dist_eq, max_lt_iff] at hdist
  have hmax : max ‖((x - d : S.domain) : E)‖ ‖S (x - d)‖ < ε / C := by
    refine max_lt_iff.mpr ⟨?_, ?_⟩
    · simpa [d, hy₁, dist_eq_norm] using hdist.1
    · simpa [map_sub, hSd, dist_eq_norm] using hdist.2
  calc C * max ‖((x - d : S.domain) : E)‖ ‖S (x - d)‖ ^ 2 < C * (ε / C) ^ 2 := by gcongr
    _ = ε ^ 2 / C := by field_simp
    _ ≤ ε ^ 2 := div_le_self (by positivity) hC1

end LinearPMap
