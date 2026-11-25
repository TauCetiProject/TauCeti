/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.HarmonicCochain
public import TauCeti.LinearAlgebra.Projection

/-!
# Weighted harmonic and exact cochains of multigraphs

For positive rational edge lengths the harmonic and exact subspaces of a multigraph with finitely
many actual edges are complementary over every characteristic-zero field
(`Graph.isCompl_harmonic_exact`, in `TauCeti.Combinatorics.Graph.HarmonicCochain`). The harmonic
projection selects the unique harmonic representative modulo exact cochains. It commutes with
coefficient extension and with sign changes on reversed edges.

## Main results

- `Graph.harmonicProjectionOnto` is the linear projection onto the harmonic subspace.

This is the rational-length version of Besser, *p-adic heights and Vologodsky integration*,
arXiv:1711.06957, Definitions 4.1–4.3 and Theorem 4.4.
-/

public section

namespace Graph

universe u v w

variable {V : Type u} {E : Type v} {G : Graph V E}

open TauCeti (piSignChange)

/-- The harmonic component of a cochain, as a linear map to the harmonic subspace. -/
noncomputable def harmonicProjectionOnto (K : Type w) [Field K] [CharZero K]
    [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) :
    (G.edgeSet → K) →ₗ[K] harmonicCochains K tail head length :=
  (harmonicCochains K tail head length).projectionOnto (exactCochains K tail head)
    (isCompl_harmonic_exact K tail head length hpos)

/-- Harmonic projection is the complementary projection along the exact subspace. -/
theorem harmonicProjectionOnto_def (K : Type w) [Field K] [CharZero K]
    [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) :
    harmonicProjectionOnto K tail head length hpos =
      (harmonicCochains K tail head length).projectionOnto (exactCochains K tail head)
        (isCompl_harmonic_exact K tail head length hpos) := by
  rw [harmonicProjectionOnto]

/-- The projection is the identity on harmonic cochains. -/
@[simp]
theorem harmonicProjectionOnto_apply_harmonic (K : Type w) [Field K] [CharZero K]
    [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) (c : harmonicCochains K tail head length) :
    harmonicProjectionOnto K tail head length hpos c = c := by
  rw [harmonicProjectionOnto_def, Submodule.projectionOnto_apply_left]

/-- The kernel of harmonic projection is exactly the space of differentials. -/
@[simp]
theorem ker_harmonicProjectionOnto (K : Type w) [Field K] [CharZero K]
    [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) :
    LinearMap.ker (harmonicProjectionOnto K tail head length hpos) =
      exactCochains K tail head := by
  rw [harmonicProjectionOnto_def, Submodule.ker_projectionOnto]

/-- A cochain has zero harmonic component if and only if it is exact. -/
@[simp]
theorem harmonicProjectionOnto_eq_zero_iff (K : Type w) [Field K] [CharZero K]
    [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) (c : G.edgeSet → K) :
    harmonicProjectionOnto K tail head length hpos c = 0 ↔
      c ∈ exactCochains K tail head := by
  rw [← ker_harmonicProjectionOnto K tail head length hpos, LinearMap.mem_ker]

/-- A differential has zero harmonic component. -/
@[simp]
theorem harmonicProjectionOnto_differential (K : Type w) [Field K] [CharZero K]
    [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) (f : G.vertexSet → K) :
    harmonicProjectionOnto K tail head length hpos (edgeDifferential tail head f) = 0 := by
  exact (harmonicProjectionOnto_eq_zero_iff K tail head length hpos _).2
    ((mem_exactCochains_iff K tail head _).2 ⟨f, rfl⟩)

/-- Subtracting the harmonic component leaves an exact cochain. -/
theorem sub_harmonicProjectionOnto_mem_exact (K : Type w) [Field K] [CharZero K]
    [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) (c : G.edgeSet → K) :
    c - (harmonicProjectionOnto K tail head length hpos c : G.edgeSet → K) ∈
      exactCochains K tail head := by
  simpa only [Submodule.projection_apply, harmonicProjectionOnto_def] using
    Submodule.sub_projection_mem (isCompl_harmonic_exact K tail head length hpos) c

/-- A harmonic cochain is the projection of a cochain exactly when the difference is exact. -/
theorem harmonicProjectionOnto_eq_iff_sub_mem_exact (K : Type w) [Field K] [CharZero K]
    [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) (c : G.edgeSet → K) (h : harmonicCochains K tail head length) :
    harmonicProjectionOnto K tail head length hpos c = h ↔
      c - (h : G.edgeSet → K) ∈ exactCochains K tail head := by
  rw [← harmonicProjectionOnto_eq_zero_iff K tail head length hpos, map_sub,
    harmonicProjectionOnto_apply_harmonic, sub_eq_zero]

/-- Extending coefficients sends the harmonic component to the harmonic component of the
extended cochain. -/
theorem harmonicProjectionOnto_map {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L]
    [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ) (hpos : ∀ e, 0 < length e)
    (φ : K →+* L) (c : G.edgeSet → K) :
    (harmonicProjectionOnto L tail head length hpos (φ ∘ c) : G.edgeSet → L) =
      φ ∘ (harmonicProjectionOnto K tail head length hpos c : G.edgeSet → K) := by
  have hφ (f : G.edgeSet → K) : (φ.toAddMonoidHom.compLeft G.edgeSet) f = φ ∘ f := by
    funext e
    simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.compLeft_apply,
      AddMonoidHom.coe_ofClass, Function.comp_apply]
  simp only [harmonicProjectionOnto_def, Submodule.coe_projectionOnto_apply, ← hφ]
  refine Submodule.projection_map_apply_of_mem (isCompl_harmonic_exact K tail head length hpos)
    (isCompl_harmonic_exact L tail head length hpos)
    (φ.toAddMonoidHom.compLeft G.edgeSet) ?_ ?_ c
  · intro h hh
    rw [hφ]
    rw [mem_harmonicCochains_iff] at hh ⊢
    simp [edgeDivergence_map, hh]
  · intro r hr
    rw [hφ]
    rw [mem_exactCochains_iff] at hr ⊢
    obtain ⟨f, rfl⟩ := hr
    exact ⟨φ ∘ f, edgeDifferential_map tail head φ.toAddMonoidHom f⟩

/-- Swapping the selected endpoints and negating the same input coordinates negates exactly
those coordinates of the harmonic projection. -/
theorem harmonicProjectionOnto_swap (K : Type w) [Field K] [CharZero K]
    [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ) (hpos : ∀ e, 0 < length e)
    (s : G.edgeSet → Prop) [DecidablePred s] (c : G.edgeSet → K) :
    (harmonicProjectionOnto K (edgeSwapTail tail head s) (edgeSwapHead tail head s) length hpos
        (piSignChange K s c) : G.edgeSet → K) =
      piSignChange K s (harmonicProjectionOnto K tail head length hpos c : G.edgeSet → K) := by
  have hs (f : G.edgeSet → K) : (piSignChange K s).toLinearMap.toAddMonoidHom f =
      piSignChange K s f := by
    simp only [LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe]
  simp only [harmonicProjectionOnto_def, Submodule.coe_projectionOnto_apply, ← hs]
  refine Submodule.projection_map_apply_of_mem (isCompl_harmonic_exact K tail head length hpos)
    (isCompl_harmonic_exact K _ _ length hpos)
    (piSignChange K s).toLinearMap.toAddMonoidHom ?_ ?_ c
  · intro h hh
    rw [hs, mem_harmonicCochains_iff, edgeDivergence_swap]
    exact (mem_harmonicCochains_iff K tail head length h).1 hh
  · intro r hr
    rw [hs]
    rw [mem_exactCochains_iff] at hr ⊢
    obtain ⟨f, rfl⟩ := hr
    refine ⟨f, ?_⟩
    simpa only [edgeDifferentialLinear_apply, LinearMap.comp_apply, LinearEquiv.coe_coe] using
      LinearMap.congr_fun (edgeDifferentialLinear_swap K tail head s) f

/-- Harmonic projection commutes with the change of cochain coordinates induced by reversing
the selected edges of an orientation. -/
theorem Orientation.harmonicProjectionOnto_reverseOn (o : G.Orientation)
    (K : Type w) [Field K] [CharZero K] [Fintype G.edgeSet]
    (length : G.edgeSet → ℚ) (hpos : ∀ e, 0 < length e)
    (s : G.edgeSet → Prop) [DecidablePred s] (c : G.edgeSet → K) :
    (harmonicProjectionOnto K (o.reverseOn s).tail (o.reverseOn s).head length hpos
        (piSignChange K s c) : G.edgeSet → K) =
      piSignChange K s (harmonicProjectionOnto K o.tail o.head length hpos c :
        G.edgeSet → K) := by
  rw [o.reverseOn_tail_eq_edgeSwapTail, o.reverseOn_head_eq_edgeSwapHead]
  exact harmonicProjectionOnto_swap K o.tail o.head length hpos s c

end Graph
