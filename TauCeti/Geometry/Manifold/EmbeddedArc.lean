/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Topology.Homotopy.Extension.Basic
import Mathlib.Analysis.Convex.Contractible
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Configuration
import TauCeti.Topology.Homotopy.Extension.Segment

/-!
# An embedded arc through finitely many points of a manifold

Let `M` be a nonempty preconnected Hausdorff `C^n` manifold, `n ≥ 2`, without boundary, modelled
on a finite-dimensional real normed space of dimension at least two. Every finite set `S` of points
of `M` lies on an embedded arc `γ : [0, 1] → M` whose image has the homotopy extension property
(`TauCeti.exists_isClosedEmbedding_hasHomotopyExtensionProperty_range`). The image is an embedded
tree joining the points of `S`: it is contractible and closed, so collapsing it to a point is a
homotopy equivalence (`TauCeti.HasHomotopyExtensionProperty.collapseHomotopyEquiv`). This is how,
in Morse homology with local or differential graded coefficients, the critical points are joined
to a basepoint, so that after the collapse the paths between critical points become loops at the
basepoint (Barraud–Cornea); the basepoint is then one of the points of `S`.

The arc is a straight segment in a chart, moved into place by a diffeomorphism.

* **The segment.** A short segment in the target of a chart has an image `α` in `M` with the
  homotopy extension property
  (`OpenPartialHomeomorph.hasHomotopyExtensionProperty_symm_image_segment`).
* **Moving the points.** Choose distinct points of `α`, one for each point of `S`. In dimension
  at least two the configuration `S` can be carried onto them by a diffeomorphism `Ψ`
  (`TauCeti.exists_diffeotopy_final_comp_eq_of_isPreconnected`), and the arc is `Ψ⁻¹ ∘ α`. The
  homotopy extension property transports along `Ψ⁻¹`
  (`TauCeti.HasHomotopyExtensionProperty.image`).

The dimension hypothesis is used only to move finitely many points at once; a connected manifold
of dimension one (a line or a circle) also contains such arcs, but they are not produced here.

## Main results

* `TauCeti.exists_isClosedEmbedding_hasHomotopyExtensionProperty_range`: an embedded arc through
  a finite set, with contractible image having the homotopy extension property.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. (2) 166 (2007), 657–722.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §4, Homogeneity Lemma.
-/

public section

open Set unitInterval Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **A straight arc in a chart.** In a manifold modelled on a nontrivial real normed space, the
chart at any point `b` contains a straight segment, whose image is an injective path `α`. -/
private theorem exists_injective_chart_arc [Nontrivial E] (b : M) :
    ∃ α : C(I, M), Function.Injective α ∧
      ∃ x y : E, segment ℝ x y ⊆ (chartAt E b).target ∧
        range α = (chartAt E b).symm '' segment ℝ x y := by
  set φ := chartAt E b
  obtain ⟨r, hr, hrt⟩ := Metric.isOpen_iff.1 φ.open_target (φ b) (mem_chart_target E b)
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  set c := φ b
  set w : E := (r / 2 / ‖v‖) • v
  have hwnorm : ‖w‖ = r / 2 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ (norm_ne_zero_iff.2 hv)]
  have hw : w ≠ 0 := norm_ne_zero_iff.1 (by rw [hwnorm]; positivity)
  have hseg : segment ℝ c (c + w) ⊆ φ.target := by
    refine ((convex_ball c r).segment_subset (Metric.mem_ball_self hr) ?_).trans hrt
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hwnorm]
    linarith
  have hseg' : segment ℝ c (c + w) = (fun s : ℝ => c + s • w) '' Icc 0 1 := by
    rw [segment_eq_image', add_sub_cancel_left]
  have hmem (t : I) : c + (t : ℝ) • w ∈ φ.symm.source :=
    φ.symm_source ▸ hseg (hseg' ▸ mem_image_of_mem _ t.2)
  refine ⟨⟨fun t => φ.symm (c + (t : ℝ) • w), φ.continuousOn_symm.comp_continuous (by fun_prop)
    fun t => φ.symm_source ▸ hmem t⟩, fun s t hst => ?_, c, c + w, hseg, ?_⟩
  · exact Subtype.ext (smul_left_injective ℝ hw (add_left_cancel (φ.symm.injOn (hmem s)
      (hmem t) hst)))
  · rw [hseg', image_image]
    ext z
    exact ⟨fun ⟨t, ht⟩ => ⟨t, t.2, ht⟩, fun ⟨t, ht, hz⟩ => ⟨⟨t, ht⟩, hz⟩⟩

variable {n : ℕ∞ω} [IsManifold 𝓘(ℝ, E) n M]

/-- **An embedded arc through finitely many points.** In a nonempty preconnected Hausdorff `C^n`
manifold, `n ≥ 2`, modelled on a finite-dimensional real normed space of dimension at least two,
every finite set `S` of points lies on an embedded arc `γ`. The image of `γ` is contractible and
has the homotopy extension property: it is an embedded tree joining the points of `S`, which can
be collapsed to a point up to homotopy equivalence. -/
theorem exists_isClosedEmbedding_hasHomotopyExtensionProperty_range [Nonempty M]
    [PreconnectedSpace M] (hdim : 1 < Module.rank ℝ E) (hn : 2 ≤ n) {S : Set M} (hS : S.Finite) :
    ∃ γ : C(I, M), IsClosedEmbedding γ ∧ S ⊆ range γ ∧
      HasHomotopyExtensionProperty (range γ) ∧ ContractibleSpace (range γ) := by
  have : Nontrivial E := rank_pos_iff_nontrivial.1 (zero_lt_one.trans hdim)
  obtain ⟨α, hαinj, x, y, hseg, hα⟩ := exists_injective_chart_arc (E := E) (Classical.arbitrary M)
  have hαhep : HasHomotopyExtensionProperty (range α) :=
    hα ▸ (chartAt E _).hasHomotopyExtensionProperty_symm_image_segment hseg
  -- Distinct times `τ x` on the arc for the points `x` of `S`.
  have : Finite S := hS.to_subtype
  have : Infinite I := Icc.infinite zero_lt_one
  obtain ⟨ν, hν⟩ := exists_injective_nat S
  set τ : S → I := Infinite.natEmbedding I ∘ ν
  have hτ : Function.Injective τ := (Infinite.natEmbedding I).injective.comp hν
  -- A diffeomorphism `Ψ` carrying each point `x` of `S` to `α (τ x)`.
  have hmn : ((1 : ℕ∞) : ℕ∞ω) + 1 ≤ n := by
    simpa [one_add_one_eq_two] using hn
  obtain ⟨Φ, -, -, -, -, hΦ⟩ := exists_diffeotopy_final_comp_eq_of_isPreconnected
    (U := univ) (f := Subtype.val) (g := α ∘ τ) hdim le_rfl hmn isOpen_univ
    isPreconnected_univ Subtype.val_injective (hαinj.comp hτ) (fun _ => mem_univ _)
    (fun _ => mem_univ _)
  set Ψ := Φ.final.toHomeomorph
  -- The arc `γ = Ψ⁻¹ ∘ α`.
  let γ : C(I, M) := (Ψ.symm : C(M, M)).comp α
  have hemb : IsClosedEmbedding γ := γ.continuous.isClosedEmbedding (Ψ.symm.injective.comp hαinj)
  refine ⟨γ, hemb, fun z hz => ⟨τ ⟨z, hz⟩, ?_⟩, ?_, ?_⟩
  · simp only [γ, ContinuousMap.comp_apply, ContinuousMap.coe_ofClass]
    rw [← Function.comp_apply (f := α), ← hΦ]
    exact Ψ.symm_apply_apply z
  · rw [show range γ = Ψ.symm '' range α from range_comp (⇑Ψ.symm) (⇑α)]
    exact hαhep.image Ψ.symm
  · have : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
    exact hemb.isEmbedding.toHomeomorph.symm.contractibleSpace

end TauCeti
