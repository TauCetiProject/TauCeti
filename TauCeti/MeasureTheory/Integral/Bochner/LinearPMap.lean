/-
Copyright (c) 2026 Emiel Lorist and The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emiel Lorist, The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import TauCeti.Analysis.Normed.Operator.LinearPMap.GraphSpace
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Hille's theorem and integration in the graph norm

A closed partial linear map commutes with Bochner integration: if `f` and `g` are integrable
and `(f s, g s)` lies in the graph almost everywhere, then their integrals lie in the graph.
There is no dense-domain assumption and the measure is arbitrary.

The existing `LinearPMap.graphSpace` realizes the domain with its graph norm. A function into
this space is integrable exactly when both coordinates are integrable. In particular, for a
function `u` taking values in the operator's domain, integrability in the graph norm is
integrability of both `u` and its image. For a closed operator between Banach spaces, its
integral in the graph space identifies the integral in the original domain and its image.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*, Volume I,
  Theorem 1.2.4 (Hille's theorem).
* The quotient-map proof of `LinearPMap.integral_mem_graph` is adapted from
  Emiel Lorist's formal proof of Hille's theorem.
-/

public section

open MeasureTheory

namespace LinearPMap

variable {S 𝕜 E F : Type*} [MeasurableSpace S] {μ : Measure S}
  [NormedAddCommGroup E] [NormedAddCommGroup F]

section Integrability

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- A graph-space-valued function is integrable exactly when its two coordinates are
integrable. Neither closedness of the operator nor completeness of the spaces is needed. -/
theorem integrable_graphSpace_iff (T : E →ₗ.[𝕜] F) (u : S → T.graphSpace) :
    Integrable u μ ↔
      Integrable (fun s ↦ T.graphFst (u s)) μ ∧ Integrable (fun s ↦ T.graphSnd (u s)) μ := by
  have hsub := (isometry_subtypeVal :
    Isometry (Subtype.val : T.graphSpace → WithLp 2 (E × F)))
  rw [← hsub.lipschitzWith.integrable_comp_iff_of_antilipschitz
    (f := u) hsub.antilipschitzWith (by rfl),
    ← (WithLp.prodContinuousLinearEquiv 2 𝕜 E F).integrable_comp_iff]
  simp only [Function.comp_def, WithLp.prodContinuousLinearEquiv_apply,
    graphFst_apply, graphSnd_apply]
  exact ⟨fun h ↦ ⟨(ContinuousLinearMap.fst 𝕜 E F).integrable_comp h,
    (ContinuousLinearMap.snd 𝕜 E F).integrable_comp h⟩, fun h ↦ h.1.prodMk h.2⟩

/-- Integrability in the graph norm is equivalent to integrability of the function and its
image under the partial linear map. The domain here carries its original subspace norm;
`toGraphSpace` equips it with the graph norm. -/
theorem integrable_toGraphSpace_iff (T : E →ₗ.[𝕜] F) (u : S → T.domain) :
    Integrable (fun s ↦ T.toGraphSpace (u s)) μ ↔
      Integrable (fun s ↦ (u s : E)) μ ∧ Integrable (fun s ↦ T (u s)) μ := by
  simpa only [graphFst_toGraphSpace, graphSnd_toGraphSpace] using
    T.integrable_graphSpace_iff (fun s ↦ T.toGraphSpace (u s))

end Integrability

variable [NormedSpace ℝ E] [NormedSpace ℝ F]
  [RCLike 𝕜] [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E]
  [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F]

/-- **Hille's theorem.** The integral of an integrable pair lying almost everywhere in the
graph of a closed partial linear map also lies in that graph. -/
theorem integral_mem_graph [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hT : T.IsClosed) {f : S → E} {g : S → F}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : ∀ᵐ s ∂μ, (f s, g s) ∈ T.graph) :
    (∫ s, f s ∂μ, ∫ s, g s ∂μ) ∈ T.graph := by
  let G := T.graph.restrictScalars ℝ
  have : _root_.IsClosed (G : Set (E × F)) := hT
  have hzero : (fun s ↦ G.mkQL (f s, g s)) =ᵐ[μ] 0 := by
    filter_upwards [hfg] with s hs using (Submodule.Quotient.mk_eq_zero G).2 hs
  have hint : (∫ s, G.mkQL (f s, g s) ∂μ) = 0 := by
    simpa using integral_congr_ae hzero
  apply (Submodule.Quotient.mk_eq_zero G).1
  simpa only [Submodule.mkQL_apply, Submodule.mkQ_apply, integral_pair hf hg] using
    (G.mkQL.integral_comp_comm (hf.prodMk hg)).symm.trans hint

/-- The integral of a domain-valued function belongs to the domain of a closed operator
whenever the function and its image are integrable. -/
theorem integral_mem_domain [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hT : T.IsClosed) {u : S → T.domain}
    (hu : Integrable (fun s ↦ (u s : E)) μ) (hTu : Integrable (fun s ↦ T (u s)) μ) :
    (∫ s, (u s : E) ∂μ) ∈ T.domain :=
  mem_domain_of_mem_graph (T.integral_mem_graph hT hu hTu (ae_of_all _ fun s ↦ T.mem_graph (u s)))

/-- A closed partial linear map commutes with the integral of a domain-valued function,
provided both that function and its image are integrable. -/
theorem apply_integral [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hT : T.IsClosed) {u : S → T.domain}
    (hu : Integrable (fun s ↦ (u s : E)) μ) (hTu : Integrable (fun s ↦ T (u s)) μ) :
    T ⟨∫ s, (u s : E) ∂μ, T.integral_mem_domain hT hu hTu⟩ = ∫ s, T (u s) ∂μ := by
  exact ((image_iff _).2
    (T.integral_mem_graph hT hu hTu (ae_of_all _ fun s ↦ T.mem_graph (u s)))).symm

/-- Integration in the graph space agrees with integration in the original space, lifted
back to the domain. Thus it also integrates the image under the closed operator. -/
theorem integral_toGraphSpace [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hT : T.IsClosed) {u : S → T.domain}
    (hu : Integrable (fun s ↦ (u s : E)) μ) (hTu : Integrable (fun s ↦ T (u s)) μ) :
    ∫ s, T.toGraphSpace (u s) ∂μ =
      T.toGraphSpace ⟨∫ s, (u s : E) ∂μ, T.integral_mem_domain hT hu hTu⟩ := by
  let := hT.completeSpace_graphSpace
  apply T.graphFst_injective
  rw [graphFst_toGraphSpace, ← T.graphFst.integral_comp_comm
    ((T.integrable_toGraphSpace_iff u).2 ⟨hu, hTu⟩)]
  simp only [graphFst_toGraphSpace]

end LinearPMap
