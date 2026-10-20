/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.StdSimplex
public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Realization
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.PL.ConvexJoin
public import TauCeti.Topology.PL.FiniteInf
import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite

/-!
# Piecewise-linear simplex models of vertex stars with spherical links

If the link of a vertex `v` is a combinatorial `n`-sphere, then the closed star of `v` is
PL-homeomorphic to the standard `(n + 1)`-simplex, the realization of the full complex on
`Fin (n + 2)`, with `v` going to the barycentre. The identification is pseudo-radial projection
from the barycentre: the link is identified with the boundary of the simplex by its standard PL
model, and each segment from a link point to `v` goes to the segment from its image to the
barycentre. In coordinates, the apex coordinate at `v` is `n + 2` times the least barycentric
coordinate of the image, so the open star of `v` goes onto the open simplex.

Both the homeomorphism and its inverse have piecewise-linear ambient coordinate formulas. These
are the local models at interior vertices for piecewise-linear charts on combinatorial manifolds.

The ambient complex and its vertex type may be infinite: the spherical link has finitely many
faces, which makes the closed star compact.

## Main results

* `PreAbstractSimplicialComplex.IsCombinatorialSphere.exists_homeomorph_closedStarRealization_top`:
  a closed vertex star with a combinatorial-sphere link is PL-homeomorphic to a standard simplex,
  with its vertex at the barycentre.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2, “Pseudo-Radial Projection”, pp. 20–21, and Chapter 3 (vertex stars of combinatorial
  manifolds).
-/

public section

noncomputable section

open AbstractSimplicialComplex Set TauCeti

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K : AbstractSimplicialComplex ι} {v : ι} {n : ℕ}

/-- The standard PL model of a combinatorial-sphere link, read on the geometric link: a
PL formula `f` identifying the link with the boundary of the standard simplex, with a PL inverse
`g` on that boundary. -/
private theorem IsCombinatorialSphere.exists_isPLOn_geometricLink
    (h : IsCombinatorialSphere (link K.toPreAbstractSimplicialComplex {v}) n) :
    ∃ f : (ι → ℝ) → (Fin (n + 2) → ℝ), ∃ g : (Fin (n + 2) → ℝ) → (ι → ℝ),
      IsPLOn f (range fun y : geometricLink K v => (y.1.1 : ι → ℝ)) ∧
      IsPLOn g (range fun y : geometricLink K v => f (y.1.1 : ι → ℝ)) ∧
      (∀ y : geometricLink K v, g (f (y.1.1 : ι → ℝ)) = y.1.1) ∧
      (range fun y : geometricLink K v => f (y.1.1 : ι → ℝ)) =
        {z ∈ range fun t : Convexity.StdSimplex ℝ (Fin (n + 2)) => ⇑t.weights | ∃ i, z i = 0} := by
  obtain ⟨e, f, g, hf, hg, hfe, hge⟩ :=
    h.exists_homeomorph_standardSimplexBoundary (A := K) link_le
  -- The geometric link is the weak polyhedron of the combinatorial link.
  let toLink (y : geometricLink K v) :
      {x : Realization K // x.1.support ∈ link K.toPreAbstractSimplicialComplex {v}} :=
    ⟨y.1, (mem_geometricLink_iff K v y.1).mp y.2⟩
  let ofLink (x : {x : Realization K // x.1.support ∈ link K.toPreAbstractSimplicialComplex {v}}) :
      geometricLink K v :=
    ⟨x.1, (mem_geometricLink_iff K v x.1).mpr x.2⟩
  have hL : (range fun y : geometricLink K v => (y.1.1 : ι → ℝ)) =
      range fun x : {x : Realization K //
        x.1.support ∈ link K.toPreAbstractSimplicialComplex {v}} => (x.1.1 : ι → ℝ) :=
    Subset.antisymm (range_subset_iff.mpr fun y => ⟨toLink y, rfl⟩)
      (range_subset_iff.mpr fun x => ⟨ofLink x, rfl⟩)
  have hT : (range fun y : geometricLink K v => f (y.1.1 : ι → ℝ)) =
      range fun y : Realization (standardSuccSimplexBoundary n) => (y.1 : Fin (n + 2) → ℝ) :=
    Subset.antisymm (range_subset_iff.mpr fun y => ⟨e (toLink y), (hfe (toLink y)).symm⟩)
      (range_subset_iff.mpr fun w => ⟨ofLink (e.symm w),
        (hfe (e.symm w)).trans (by rw [e.apply_symm_apply])⟩)
  refine ⟨f, g, hL ▸ hf, hT ▸ hg, fun y => ?_,
    hT.trans (range_realization_coe_standardSuccSimplexBoundary n)⟩
  rw [hfe (toLink y), hge, e.symm_apply_apply]

/-- **Simplex model of a closed vertex star with a spherical link.** If the link of `v` is a
combinatorial `n`-sphere, the closed star of `v` is homeomorphic to the standard `(n + 1)`-simplex,
the realization of the full complex on `Fin (n + 2)`, with piecewise-linear ambient coordinate
formulas in both directions. The vertex goes to the barycentre, and its coordinate at a point of
the closed star is `n + 2` times the least coordinate of the image, so the open star goes onto the
open simplex. -/
theorem IsCombinatorialSphere.exists_homeomorph_closedStarRealization_top
    (h : IsCombinatorialSphere (link K.toPreAbstractSimplicialComplex {v}) n) :
    ∃ φ : closedStarRealization K {v} ≃ₜ
        Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2))),
      ((φ (starApex K v)).1 : Fin (n + 2) → ℝ) = (fun _ => ((n : ℝ) + 2)⁻¹) ∧
      (∀ x, ((n : ℝ) + 2) * Finset.univ.inf' Finset.univ_nonempty
        ((φ x).1 : Fin (n + 2) → ℝ) = x.1.1 v) ∧
      ∃ F : (ι → ℝ) → (Fin (n + 2) → ℝ), ∃ G : (Fin (n + 2) → ℝ) → (ι → ℝ),
        IsPLOn F (range fun x : closedStarRealization K {v} => (x.1.1 : ι → ℝ)) ∧
        IsPLOn G (range fun y : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2))) =>
          (y.1 : Fin (n + 2) → ℝ)) ∧
        (∀ x, F (x.1.1 : ι → ℝ) = (φ x).1) ∧ ∀ x, G (φ x).1 = (x.1.1 : ι → ℝ) := by
  obtain ⟨f, g, hf, hg, hgf, hT⟩ := h.exists_isPLOn_geometricLink
  have hK := K.isCompact_closedStarRealization (finite_faces_closedStar_iff.mpr h.finite_faces)
  have hne : (geometricLink K v).Nonempty := by
    obtain ⟨_, y, -⟩ : (range fun y : geometricLink K v => f (y.1.1 : ι → ℝ)).Nonempty := by
      rw [hT]
      exact ⟨_, mem_range_self (Convexity.StdSimplex.single 0), 1, by simp⟩
    exact ⟨y.1, y.2⟩
  -- Pseudo-radial projection from the barycentre, with height `c` times the least coordinate.
  let c : ℝ := Fintype.card (Fin (n + 2))
  let hgt : (Fin (n + 2) → ℝ) → ℝ := fun z => c * Finset.univ.inf' Finset.univ_nonempty z
  have hh : IsPLOn hgt univ := by
    let A : ℝ →ᴬ[ℝ] ℝ := (c • ContinuousLinearMap.id ℝ ℝ).toContinuousAffineMap
    refine ((isPLOn_continuousAffineMap A univ).comp
      (Finset.isPLOn_infAffine Finset.univ Finset.univ_nonempty
        fun i => (ContinuousLinearMap.proj i).toContinuousAffineMap)
      (fun _ _ => mem_univ _)).congr fun z _ => ?_
    simp [A, hgt]
  let b := ⇑(Convexity.StdSimplex.barycenter : Convexity.StdSimplex ℝ (Fin (n + 2))).weights
  have hhF (y : geometricLink K v) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      hgt ((1 - t) • f (y.1.1 : ι → ℝ) + t • b) = t := by
    obtain ⟨⟨s, hs⟩, i, hi⟩ : f (y.1.1 : ι → ℝ) ∈
        {z ∈ range fun t : Convexity.StdSimplex ℝ (Fin (n + 2)) => ⇑t.weights | ∃ i, z i = 0} :=
      hT ▸ mem_range_self y
    exact card_mul_inf'_smul_add_smul_barycenter (fun j => hs ▸ s.weights_nonneg j) hi ht.2
  have hS : convexJoin ℝ (range fun y : geometricLink K v => f (y.1.1 : ι → ℝ)) {b} =
      range fun y : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2))) =>
        (y.1 : Fin (n + 2) → ℝ) := by
    rw [hT, convexJoin_boundary_stdSimplex_barycenter, range_realization_coe_top]
  obtain ⟨φ, hapex, hheight, -, F, G, hF, hG, hFφ, hGφ⟩ :=
    exists_homeomorph_closedStarRealization_convexJoin hK hne hf hg hgf
      (hh.mono (subset_univ _)) hhF
  -- Identify the join with the realization of the full complex through its coordinates.
  let r := ((⊤ : AbstractSimplicialComplex (Fin (n + 2))).isClosedEmbedding_realization_coe
    (Set.toFinite _)).isEmbedding.toHomeomorph
  let ψ := φ.trans ((Homeomorph.setCongr hS).trans r.symm)
  have hr (w : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2)))) :
      ((r w : Fin (n + 2) → ℝ)) = (w.1 : Fin (n + 2) → ℝ) :=
    Topology.IsEmbedding.toHomeomorph_apply_coe _ w
  have hψ (x : closedStarRealization K {v}) : ((ψ x).1 : Fin (n + 2) → ℝ) = φ x :=
    (hr _).symm.trans
      (congrArg Subtype.val (r.apply_symm_apply (Homeomorph.setCongr hS (φ x))))
  have hc : c = (n : ℝ) + 2 := by simp [c]
  refine ⟨ψ, ?_, fun x => ?_, F, G, hF, by rw [← hS]; exact hG,
    fun x => by rw [hψ]; exact hFφ x, fun x => by rw [hψ]; exact hGφ x⟩
  · rw [hψ, hapex, ← hc]
    exact funext Convexity.StdSimplex.weights_barycenter_apply
  · rw [hψ, ← hc]
    exact hheight x

end PreAbstractSimplicialComplex
