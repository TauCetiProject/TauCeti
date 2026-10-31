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
import TauCeti.Geometry.Convex.ConvexSpace.Defs

/-!
# Piecewise-linear simplex models of vertex stars with spherical or ball links

If the link of a vertex `v` is a combinatorial `n`-sphere, then the closed star of `v` is
PL-homeomorphic to the standard `(n + 1)`-simplex, the realization of the full complex on
`Fin (n + 2)`, with `v` going to the barycentre. The identification is pseudo-radial projection
from the barycentre: the link is identified with the boundary of the simplex by its standard PL
model, and each segment from a link point to `v` goes to the segment from its image to the
barycentre. In coordinates, the apex coordinate at `v` is `n + 2` times the least barycentric
coordinate of the image, so the open star of `v` goes onto the open simplex.

If instead the link of `v` is a combinatorial `n`-ball, then the closed star of `v` is
PL-homeomorphic to the same simplex with `v` going to its last vertex: the link is identified with
the opposite facet by its standard PL model, and each segment from a link point to `v` goes to the
segment from its image to that vertex. The apex coordinate at `v` is the last barycentric
coordinate of the image, so the open star of `v` goes onto the complement of the facet.

In both cases the homeomorphism and its inverse have piecewise-linear ambient coordinate formulas.
These are the local models at interior and at boundary vertices for piecewise-linear charts on
combinatorial manifolds.

The ambient complex and its vertex type may be infinite: the link has finitely many faces, which
makes the closed star compact.

## Main results

* `PreAbstractSimplicialComplex.IsCombinatorialSphere.exists_homeomorph_closedStarRealization_top`:
  a closed vertex star with a combinatorial-sphere link is PL-homeomorphic to a standard simplex,
  with its vertex at the barycentre.
* `PreAbstractSimplicialComplex.IsCombinatorialBall.exists_homeomorph_closedStarRealization_top`:
  a closed vertex star with a combinatorial-ball link is PL-homeomorphic to a standard simplex,
  with its vertex at a vertex of the simplex and its link on the opposite facet.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 1, “Joins and Cones”, Chapter 2, “Pseudo-Radial Projection”, pp. 20–21, and Chapter 3
  (vertex stars of combinatorial manifolds).
-/

public section

noncomputable section

open AbstractSimplicialComplex Set TauCeti

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K : AbstractSimplicialComplex ι} {v : ι} {n : ℕ}

/-- A PL model of the link of `v`, given on the weak polyhedron of the combinatorial link, read on
the geometric link: the formulas restrict to the geometric link, the inverse formula still undoes
the forward one there, and the image of the geometric link is the coordinate image of the
model. -/
private theorem isPLOn_geometricLink_of_homeomorph {κ : Type*} {L : AbstractSimplicialComplex κ}
    (e : {x : Realization K // x.1.support ∈ link K.toPreAbstractSimplicialComplex {v}} ≃ₜ
      Realization L)
    {f : (ι → ℝ) → (κ → ℝ)} {g : (κ → ℝ) → (ι → ℝ)}
    (hf : IsPLOn f (range fun x : {x : Realization K //
      x.1.support ∈ link K.toPreAbstractSimplicialComplex {v}} => (x.1.1 : ι → ℝ)))
    (hg : IsPLOn g (range fun y : Realization L => (y.1 : κ → ℝ)))
    (hfe : ∀ x, f (x.1.1 : ι → ℝ) = (e x).1) (hge : ∀ y, g (y.1 : κ → ℝ) = (e.symm y).1.1) :
    IsPLOn f (range fun y : geometricLink K v => (y.1.1 : ι → ℝ)) ∧
      IsPLOn g (range fun y : geometricLink K v => f (y.1.1 : ι → ℝ)) ∧
      (∀ y : geometricLink K v, g (f (y.1.1 : ι → ℝ)) = y.1.1) ∧
      (range fun y : geometricLink K v => f (y.1.1 : ι → ℝ)) =
        range fun y : Realization L => (y.1 : κ → ℝ) := by
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
      range fun y : Realization L => (y.1 : κ → ℝ) :=
    Subset.antisymm (range_subset_iff.mpr fun y => ⟨e (toLink y), (hfe (toLink y)).symm⟩)
      (range_subset_iff.mpr fun w => ⟨ofLink (e.symm w),
        (hfe (e.symm w)).trans (by rw [e.apply_symm_apply])⟩)
  refine ⟨hL ▸ hf, hT ▸ hg, fun y => ?_, hT⟩
  rw [hfe (toLink y), hge, e.symm_apply_apply]

/-- Pseudo-radial projection of the closed star of `v` onto a join of the image of the link with a
point `b`, when that join fills the standard `(n + 1)`-simplex, read as a homeomorphism onto the
realization of the full complex on `Fin (n + 2)`. The vertex goes to `b`, the height formula `h`
recovers the coordinate at `v`, and the piecewise-linear coordinate formulas carry over. -/
private theorem exists_homeomorph_top_of_convexJoin {F : (ι → ℝ) → (Fin (n + 2) → ℝ)}
    {G : (Fin (n + 2) → ℝ) → (ι → ℝ)} {h : (Fin (n + 2) → ℝ) → ℝ} {b : Fin (n + 2) → ℝ}
    (hK : IsCompact (closedStarRealization K {v}))
    (hF : IsPLOn F (range fun y : geometricLink K v => (y.1.1 : ι → ℝ)))
    (hG : IsPLOn G (range fun y : geometricLink K v => F (y.1.1 : ι → ℝ)))
    (hGF : ∀ y : geometricLink K v, G (F (y.1.1 : ι → ℝ)) = y.1.1) (hh : IsPLOn h univ)
    (hhF : ∀ y : geometricLink K v, ∀ t ∈ Icc (0 : ℝ) 1,
      h ((1 - t) • F (y.1.1 : ι → ℝ) + t • b) = t)
    (hS : convexJoin ℝ (range fun y : geometricLink K v => F (y.1.1 : ι → ℝ)) {b} =
      range fun y : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2))) =>
        (y.1 : Fin (n + 2) → ℝ)) :
    ∃ φ : closedStarRealization K {v} ≃ₜ
        Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2))),
      ((φ (starApex K v)).1 : Fin (n + 2) → ℝ) = b ∧ (∀ x, h (φ x).1 = x.1.1 v) ∧
      ∃ F' : (ι → ℝ) → (Fin (n + 2) → ℝ), ∃ G' : (Fin (n + 2) → ℝ) → (ι → ℝ),
        IsPLOn F' (range fun x : closedStarRealization K {v} => (x.1.1 : ι → ℝ)) ∧
        IsPLOn G' (range fun y : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2))) =>
          (y.1 : Fin (n + 2) → ℝ)) ∧
        (∀ x, F' (x.1.1 : ι → ℝ) = (φ x).1) ∧ ∀ x, G' (φ x).1 = (x.1.1 : ι → ℝ) := by
  -- The join is the nonempty simplex, so the link is nonempty.
  have hb : ⇑(Convexity.StdSimplex.single (0 : Fin (n + 2)) : Convexity.StdSimplex ℝ _).weights ∈
      convexJoin ℝ (range fun y : geometricLink K v => F (y.1.1 : ι → ℝ)) {b} := by
    rw [hS, range_realization_coe_top]
    exact mem_range_self _
  obtain ⟨-, ⟨y, -⟩, -⟩ := mem_convexJoin.mp hb
  obtain ⟨φ, hapex, hheight, -, F', G', hF', hG', hFφ, hGφ⟩ :=
    exists_homeomorph_closedStarRealization_convexJoin hK ⟨y.1, y.2⟩ hF hG hGF
      (hh.mono (subset_univ _)) hhF
  -- Identify the join with the realization of the full complex through its coordinates.
  let ψ := φ.trans ((Homeomorph.setCongr hS).trans
    ((⊤ : AbstractSimplicialComplex (Fin (n + 2))).realizationHomeomorphRange (toFinite _)).symm)
  have hψ (x : closedStarRealization K {v}) : ((ψ x).1 : Fin (n + 2) → ℝ) = φ x :=
    coe_realizationHomeomorphRange_symm_apply _ _ _
  refine ⟨ψ, by rw [hψ, hapex], fun x => by rw [hψ]; exact hheight x, F', G', hF',
    by rw [← hS]; exact hG', fun x => by rw [hψ]; exact hFφ x, fun x => by rw [hψ]; exact hGφ x⟩

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
  -- The link is the boundary of the standard simplex, by its standard PL model.
  obtain ⟨e, f, g, hf, hg, hfe, hge⟩ :=
    h.exists_homeomorph_standardSimplexBoundary (A := K) link_le
  obtain ⟨hf, hg, hgf, hT⟩ := isPLOn_geometricLink_of_homeomorph e hf hg hfe hge
  rw [range_realization_coe_standardSuccSimplexBoundary] at hT
  have hK := K.isCompact_closedStarRealization (finite_faces_closedStar_iff.mpr h.finite_faces)
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
  obtain ⟨φ, hapex, hheight, hPL⟩ :=
    exists_homeomorph_top_of_convexJoin hK hf hg hgf hh hhF hS
  have hc : c = (n : ℝ) + 2 := by simp [c]
  refine ⟨φ, ?_, fun x => ?_, hPL⟩
  · rw [hapex, ← hc]
    exact funext Convexity.StdSimplex.weights_barycenter_apply
  · rw [← hc]
    exact hheight x

/-- **Simplex model of a closed vertex star with a ball link.** If the link of `v` is a
combinatorial `n`-ball, the closed star of `v` is homeomorphic to the standard `(n + 1)`-simplex,
the realization of the full complex on `Fin (n + 2)`, with piecewise-linear ambient coordinate
formulas in both directions. The vertex goes to the last vertex of the simplex, the link onto the
opposite facet, and the coordinate of a point of the closed star at `v` is the last coordinate of
its image, so the open star goes onto the complement of that facet. -/
theorem IsCombinatorialBall.exists_homeomorph_closedStarRealization_top
    (h : IsCombinatorialBall (link K.toPreAbstractSimplicialComplex {v}) n) :
    ∃ φ : closedStarRealization K {v} ≃ₜ
        Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2))),
      ((φ (starApex K v)).1 : Fin (n + 2) → ℝ) = Pi.single (Fin.last (n + 1)) 1 ∧
      (∀ x, ((φ x).1 : Fin (n + 2) → ℝ) (Fin.last (n + 1)) = x.1.1 v) ∧
      ∃ F : (ι → ℝ) → (Fin (n + 2) → ℝ), ∃ G : (Fin (n + 2) → ℝ) → (ι → ℝ),
        IsPLOn F (range fun x : closedStarRealization K {v} => (x.1.1 : ι → ℝ)) ∧
        IsPLOn G (range fun y : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2))) =>
          (y.1 : Fin (n + 2) → ℝ)) ∧
        (∀ x, F (x.1.1 : ι → ℝ) = (φ x).1) ∧ ∀ x, G (φ x).1 = (x.1.1 : ι → ℝ) := by
  -- The link is the standard `n`-simplex, by its standard PL model.
  obtain ⟨e, f, g, hf, hg, hfe, hge⟩ := h.exists_homeomorph_standardSimplex (A := K) link_le
  obtain ⟨hf, hg, hgf, hT⟩ := isPLOn_geometricLink_of_homeomorph e hf hg hfe hge
  rw [range_realization_coe_top] at hT
  have hK := K.isCompact_closedStarRealization (finite_faces_closedStar_iff.mpr h.finite_faces)
  -- Place the link model on the facet opposite the last vertex, by appending a zero coordinate,
  -- an affine map with affine left inverse `Fin.init`.
  let E : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 2) → ℝ) :=
    ContinuousLinearMap.pi (Fin.lastCases 0 ContinuousLinearMap.proj)
  let P : (Fin (n + 2) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Fin.castSucc j)
  have hE (z : Fin (n + 1) → ℝ) : E z = Fin.snoc z 0 :=
    funext fun i => Fin.lastCases (by simp [E]) (fun j => by simp [E]) i
  have hP (z : Fin (n + 2) → ℝ) : P z = Fin.init z :=
    funext fun j => by simp [P, Fin.init]
  have hF : IsPLOn (fun x => (Fin.snoc (f x) 0 : Fin (n + 2) → ℝ))
      (range fun y : geometricLink K v => (y.1.1 : ι → ℝ)) :=
    ((isPLOn_continuousAffineMap E.toContinuousAffineMap univ).comp hf
      fun _ _ => mem_univ _).congr fun x _ => (hE (f x)).symm
  have hG : IsPLOn (fun z => g (Fin.init z))
      (range fun y : geometricLink K v => (Fin.snoc (f (y.1.1 : ι → ℝ)) 0 : Fin (n + 2) → ℝ)) :=
    (hg.comp (isPLOn_continuousAffineMap P.toContinuousAffineMap _) <| by
      rintro _ ⟨y, rfl⟩
      exact ⟨y, by simp [hP]⟩).congr fun z _ => congrArg g (hP z)
  have hT' : (range fun y : geometricLink K v =>
      (Fin.snoc (f (y.1.1 : ι → ℝ)) 0 : Fin (n + 2) → ℝ)) =
      {z ∈ range fun t : Convexity.StdSimplex ℝ (Fin (n + 2)) => ⇑t.weights |
        z (Fin.last (n + 1)) = 0} := by
    rw [range_comp' (fun w : Fin (n + 1) → ℝ => (Fin.snoc w 0 : Fin (n + 2) → ℝ)), hT,
      ← range_comp', Convexity.StdSimplex.range_snoc_weights_zero]
  -- Coning from the last vertex, with height the last coordinate.
  let b : Fin (n + 2) → ℝ := Pi.single (Fin.last (n + 1)) 1
  have hh : IsPLOn (fun z : Fin (n + 2) → ℝ => z (Fin.last (n + 1))) univ :=
    (isPLOn_continuousAffineMap (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin (n + 2) => ℝ) (Fin.last (n + 1))).toContinuousAffineMap univ).congr
      fun z _ => by simp
  have hS : convexJoin ℝ (range fun y : geometricLink K v =>
      (Fin.snoc (f (y.1.1 : ι → ℝ)) 0 : Fin (n + 2) → ℝ)) {b} =
      range fun y : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2))) =>
        (y.1 : Fin (n + 2) → ℝ) := by
    rw [hT', convexJoin_facet_stdSimplex_single, range_realization_coe_top]
  exact exists_homeomorph_top_of_convexJoin (b := b) hK hF hG
    (fun y => by simp only [Fin.init_snoc, hgf]) hh (fun y t _ => by simp [b]) hS

end PreAbstractSimplicialComplex
