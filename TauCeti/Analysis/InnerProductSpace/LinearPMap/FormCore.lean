/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Friedrichs
import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore

/-!
# Form cores

Let `S` be a symmetric partial operator on `E` with lower bound `γ`. Its form `⟪S x, y⟫_𝕜` has the
form completion `LinearPMap.FriedrichsSpace S γ hS`, the form domain of the Friedrichs extension of
`S`. A subspace `D` of the domain of `S` is a **form core** (`LinearPMap.IsFormCore`) when its image
is dense in the form completion, that is dense for the form norm
`(re ⟪S x, x⟫_𝕜 + (1 - γ) * ‖x‖ ^ 2) ^ (1 / 2)`.

The domain of `S` is a form core (`LinearPMap.isFormCore_domain`): this is the statement that the
domain of `S` is a form core of the Friedrichs extension. A graph core of `S`, in the sense of
Mathlib's `LinearPMap.HasCore`, is a form core (`LinearPMap.HasCore.isFormCore`), since the form
norm is bounded by the graph norm: `‖x‖_S ^ 2 ≤ ‖S x‖ * ‖x‖ + |1 - γ| * ‖x‖ ^ 2`
(`LinearPMap.norm_toFriedrichsSpace_sq_le`). For a self-adjoint `S` bounded below, whose
Friedrichs extension is `S` itself, this says that every graph core of `S` is a form core of its
closed form. The converse fails: form cores and graph cores are distinct density conditions.

## Main declarations

* `LinearPMap.IsFormCore`: a form core of the form of `S`.
* `LinearPMap.isFormCore_domain`: the domain of `S` is a form core.
* `LinearPMap.HasCore.isFormCore`: a graph core is a form core.

## References

* TauCetiRoadmap, `OperatorTheory/UnboundedOperators/README.md`, §4.7 (UO-D06).
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

/-- The form norm is bounded by the graph norm: `‖x‖_S ^ 2 ≤ ‖S x‖ * ‖x‖ + |1 - γ| * ‖x‖ ^ 2`. -/
theorem norm_toFriedrichsSpace_sq_le (x : S.domain) :
    ‖toFriedrichsSpace hS x‖ ^ 2 ≤ ‖S x‖ * ‖(x : E)‖ + |1 - γ| * ‖(x : E)‖ ^ 2 := by
  rw [norm_toFriedrichsSpace_sq]
  gcongr
  · exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  · exact le_abs_self _

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
  refine ⟨hD.le_domain, ((denseRange_toFriedrichsSpace hS).mono ?_).of_closure⟩
  rintro _ ⟨x, rfl⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hx : ((x : E), S x) ∈ _root_.closure ((S.domRestrict D).graph : Set (E × E)) :=
    hD.graph_subset_of_isClosed isClosed_closure subset_closure (S.mem_graph x)
  set C := 1 + |1 - γ|
  have hC1 : 1 ≤ C := le_add_of_nonneg_right (abs_nonneg _)
  obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp hx (ε / C) (by positivity)
  obtain ⟨y, hy₁, hy₂⟩ := (mem_graph_iff _).mp hp
  let d : S.domain := ⟨y, y.property.right⟩
  have hSd : S d = p.2 := by rw [← hy₂]; exact (domRestrict_apply rfl).symm
  refine ⟨toFriedrichsSpace hS d, ⟨d, y.property.left, rfl⟩, ?_⟩
  rw [Prod.dist_eq, max_lt_iff] at hdist
  have h₁ : ‖((x - d : S.domain) : E)‖ < ε / C := by
    simpa [d, hy₁, dist_eq_norm] using hdist.1
  have h₂ : ‖S (x - d)‖ < ε / C := by
    simpa [map_sub, hSd, dist_eq_norm] using hdist.2
  rw [dist_eq_norm, ← (toFriedrichsSpace hS).map_sub]
  refine lt_of_pow_lt_pow_left₀ 2 hε.le ((norm_toFriedrichsSpace_sq_le hS _).trans_lt ?_)
  have ht : ε / C ≤ ε := div_le_self hε.le hC1
  have hCt : C * (ε / C) = ε := mul_div_cancel₀ ε (by positivity)
  have ha := norm_nonneg ((x - d : S.domain) : E)
  have hk := abs_nonneg (1 - γ)
  nlinarith [mul_le_mul_of_nonneg_right h₂.le ha, mul_le_mul_of_nonneg_left h₁.le hk,
    mul_lt_mul_of_pos_left h₁ hε]

end LinearPMap
