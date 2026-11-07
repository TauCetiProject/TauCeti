/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Triangulable.Vertices
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Complement
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Configuration
import TauCeti.Geometry.Manifold.Connected

/-!
# Finite punctures of compact triangulated manifolds

In a connected smooth manifold of real dimension greater than one, a finite configuration
can be moved onto distinct vertices of a sufficiently subdivided triangulation. Thus a compact
triangulable smooth manifold remains of finite CW type after deleting any finite set, not just
a set already represented by vertices. This supplies finite CW models for punctured surfaces
used in Euler-characteristic calculations for branched covers.

We use finite-configuration homogeneity from `Diffeotopy.Configuration` and the derived
subdivision complement model from `Realization.Complement`. The resulting triangulation is
only topological; no smooth or PL compatibility is asserted.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, §4 (homogeneity).
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 3
  (complements of subpolyhedra).
-/

public noncomputable section

open Set AbstractSimplicialComplex TauCeti.SetLike TauCeti
open scoped Manifold ContDiff

namespace Set.Finite

universe u v w

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [T2Space M] [ConnectedSpace M] [CompactSpace M] [IsManifold 𝓘(ℝ, E) 2 M]

/-- Every finite set in a compact connected triangulable `C²` manifold of real dimension
greater than one is the image of a set of vertices in some finite topological triangulation.
The triangulation need not be smooth. -/
theorem exists_triangulation_vertex_image {S : Set M} (hS : S.Finite)
    (hdim : 1 < Module.rank ℝ E) (htri : IsTriangulable.{w} M) :
    ∃ (ι : Type w) (K : AbstractSimplicialComplex ι) (e : Realization K ≃ₜ M) (s : Set ι),
      Finite ι ∧ e '' (K.vertex '' s) = S := by
  classical
  have : Nontrivial E := (rank_pos_iff_nontrivial (R := ℝ)).mp (lt_trans zero_lt_one hdim)
  have : Infinite M := infinite_of_nontrivial_model (E := E)
  have := hS.to_subtype
  obtain ⟨ι, K, hι, ⟨e⟩, hcard⟩ :=
    htri.exists_finite_triangulation_card_ge (Nat.card S)
  let := Fintype.ofFinite S
  let := Fintype.ofFinite ι
  obtain ⟨j⟩ : Nonempty (S ↪ ι) := Function.Embedding.nonempty_of_card_le (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨Φ, _, _, _, _, hΦ⟩ :=
    exists_diffeotopy_final_comp_eq_of_isPreconnected (E := E) (M := M) (n := 2) (m := 1)
      hdim le_rfl (by norm_num) isOpen_univ isPreconnected_univ
      (f := fun x : S => (x : M)) (g := fun x : S => e (K.vertex (j x)))
      Subtype.val_injective (e.injective.comp (K.vertex_injective.comp j.injective))
      (fun _ => mem_univ _) (fun _ => mem_univ _)
  let e' := e.trans Φ.final.toHomeomorph.symm
  refine ⟨ι, K, e', range j, hι, ?_⟩
  have hmarked (x : S) : e' (K.vertex (j x)) = x := by
    have hx := congrFun hΦ x
    exact Φ.final.injective (by simpa [e', Function.comp_def] using hx.symm)
  ext x
  constructor
  · rintro ⟨_, ⟨_, ⟨y, rfl⟩, rfl⟩, rfl⟩
    exact hmarked y ▸ y.2
  · intro hx
    exact ⟨K.vertex (j ⟨x, hx⟩), ⟨j ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩,
      hmarked ⟨x, hx⟩⟩

/-- Deleting finitely many points from a compact connected triangulable `C²` manifold of real
dimension greater than one leaves a space of finite CW type. The removed points need not be
vertices of the supplied triangulation. -/
theorem finiteCWType_compl_of_isTriangulable {S : Set M} (hS : S.Finite)
    (hdim : 1 < Module.rank ℝ E) (htri : IsTriangulable.{w} M) : FiniteCWType ↥Sᶜ := by
  classical
  have htri' : IsTriangulable.{u} M := htri.lift_of_compactSpace
  obtain ⟨ι, K, e, s, hι, hS⟩ := hS.exists_triangulation_vertex_image hdim htri'
  let := Fintype.ofFinite ι
  have heq : e ⁻¹' Sᶜ = (K.vertex '' s)ᶜ := by
    rw [← hS, preimage_compl, e.injective.preimage_image]
  have := K.instFiniteCWTypeComplVertexImage s
  exact ((e.sets heq.symm).symm).finiteCWType

end Set.Finite
