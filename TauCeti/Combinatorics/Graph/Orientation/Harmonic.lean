/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Orientation.Cochains
public import Mathlib.LinearAlgebra.Projection
import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Weighted harmonic and exact cochains of multigraphs

For positive rational edge lengths the harmonic and exact subspaces of a finite multigraph are
complementary over every characteristic-zero field. The harmonic projection commutes with
coefficient extension and with sign changes on reversed edges.

## Main results

- `Graph.harmonic_exact_decomposition` gives the unique harmonic and exact parts of a cochain.
- `Graph.harmonicProjectionOnto` is the linear projection onto the harmonic subspace.

This is the rational-length version of Besser, *p-adic heights and Vologodsky integration*,
arXiv:1711.06957, Definitions 4.1–4.3 and Theorem 4.4. The weighted rank calculation follows
the sum-of-squares argument for `Matrix.rank_transpose_mul_self`, and `Matrix.rank_map`
transports that calculation from the rationals.
-/

public section

namespace Graph

universe u v w

variable {V : Type u} {E : Type v} {G : Graph V E}

/-- Cochains with zero weighted divergence. -/
noncomputable def harmonicCochains (K : Type w) [DivisionRing K] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ) :
    Submodule K (G.edgeSet → K) :=
  LinearMap.ker (edgeDivergence K tail head length)

@[simp]
theorem mem_harmonicCochains_iff (K : Type w) [DivisionRing K] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (c : G.edgeSet → K) :
    c ∈ harmonicCochains K tail head length ↔
      edgeDivergence K tail head length c = 0 := by
  rw [harmonicCochains, LinearMap.mem_ker]

/-- For finite actual vertex and edge sets, positive rational edge lengths, and a
characteristic-zero coefficient field, the harmonic and exact subspaces are complementary.
The endpoint maps may be arbitrary. -/
theorem isCompl_harmonic_exact (K : Type w) [Field K] [CharZero K]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) :
    IsCompl (harmonicCochains K tail head length) (exactCochains K tail head) := by
  classical
  let := Fintype.ofFinite G.vertexSet
  rw [harmonicCochains, exactCochains_eq_range, edgeDivergence_eq_matrix,
    edgeDifferentialLinear_eq_matrix]
  exact Matrix.isCompl_ker_transpose_mul_diagonal_range_of_rat K (endpointMatrix tail head) _
    (fun e ↦ inv_pos.2 (hpos e))

/-- Every cochain of a finite oriented multigraph with positive rational edge lengths and
coefficients in a characteristic-zero field has a unique harmonic/exact pair.
Uniqueness concerns the two cochains. A potential for the exact part need not be unique.
The actual vertex and edge sets are finite, so the ambient types can be infinite. -/
theorem harmonic_exact_decomposition (K : Type w) [Field K] [CharZero K]
    [Finite G.vertexSet] [Fintype G.edgeSet] (o : G.Orientation)
    (length : G.edgeSet → ℚ) (hpos : ∀ e, 0 < length e) (c : G.edgeSet → K) :
    ∃! p : (G.edgeSet → K) × (G.edgeSet → K),
      edgeDivergence K o.tail o.head length p.1 = 0 ∧
      (∃ f, edgeDifferential o.tail o.head f = p.2) ∧ p.1 + p.2 = c := by
  have hc := isCompl_harmonic_exact K o.tail o.head length hpos
  obtain ⟨p, hp, huniq⟩ := Submodule.existsUnique_add_of_isCompl_prod hc c
  have hH := mem_harmonicCochains_iff K o.tail o.head length
  have hE := mem_exactCochains_iff K o.tail o.head (A := K)
  refine ⟨⟨p.1, p.2⟩, ⟨(hH _).1 p.1.property, (hE _).1 p.2.property, hp⟩, ?_⟩
  rintro ⟨h, r⟩ ⟨hh, hr, hsum⟩
  have heq := huniq (⟨⟨h, (hH h).2 hh⟩, ⟨r, (hE r).2 hr⟩⟩) hsum
  exact congrArg (fun q ↦ ((q.1 : G.edgeSet → K), (q.2 : G.edgeSet → K))) heq

/-- The harmonic component of a cochain, as a linear map to the harmonic subspace. -/
noncomputable def harmonicProjectionOnto (K : Type w) [Field K] [CharZero K]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) :
    (G.edgeSet → K) →ₗ[K] harmonicCochains K tail head length :=
  (harmonicCochains K tail head length).projectionOnto (exactCochains K tail head)
    (isCompl_harmonic_exact K tail head length hpos)

/-- The projection is the identity on harmonic cochains. -/
@[simp]
theorem harmonicProjectionOnto_apply_harmonic (K : Type w) [Field K] [CharZero K]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) (c : harmonicCochains K tail head length) :
    harmonicProjectionOnto K tail head length hpos c = c := by
  exact Submodule.projectionOnto_apply_left _ c

/-- The kernel of harmonic projection is exactly the space of differentials. -/
theorem ker_harmonicProjectionOnto (K : Type w) [Field K] [CharZero K]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) :
    LinearMap.ker (harmonicProjectionOnto K tail head length hpos) =
      exactCochains K tail head := by
  exact Submodule.ker_projectionOnto _

/-- Exact cochains have zero harmonic component. -/
@[simp]
theorem harmonicProjectionOnto_differential (K : Type w) [Field K] [CharZero K]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) (f : G.vertexSet → K) :
    harmonicProjectionOnto K tail head length hpos (edgeDifferential tail head f) = 0 := by
  apply (Submodule.projectionOnto_apply_eq_zero_iff _).2
  exact (mem_exactCochains_iff K tail head _).2 ⟨f, rfl⟩

/-- Adding a differential preserves the harmonic component. -/
theorem harmonicProjectionOnto_add_differential (K : Type w) [Field K] [CharZero K]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) (c : G.edgeSet → K) (f : G.vertexSet → K) :
    harmonicProjectionOnto K tail head length hpos (c + edgeDifferential tail head f) =
      harmonicProjectionOnto K tail head length hpos c := by
  rw [map_add, harmonicProjectionOnto_differential, add_zero]

/-- Subtracting the harmonic component leaves an exact cochain. -/
theorem sub_harmonicProjectionOnto_mem_exact (K : Type w) [Field K] [CharZero K]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) (c : G.edgeSet → K) :
    c - (harmonicProjectionOnto K tail head length hpos c : G.edgeSet → K) ∈
      exactCochains K tail head := by
  simpa only [Submodule.projection_apply, harmonicProjectionOnto] using
    Submodule.sub_projection_mem (isCompl_harmonic_exact K tail head length hpos) c

/-- A harmonic cochain is the projection of a cochain exactly when the difference is exact. -/
theorem harmonicProjectionOnto_eq_iff_sub_mem_exact (K : Type w) [Field K] [CharZero K]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) (c : G.edgeSet → K) (h : harmonicCochains K tail head length) :
    harmonicProjectionOnto K tail head length hpos c = h ↔
      c - (h : G.edgeSet → K) ∈ exactCochains K tail head := by
  rw [← ker_harmonicProjectionOnto K tail head length hpos, LinearMap.mem_ker, map_sub,
    harmonicProjectionOnto_apply_harmonic, sub_eq_zero]

/-- Extending coefficients sends the harmonic component to the harmonic component of the
extended cochain. -/
theorem harmonicProjectionOnto_map {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ) (hpos : ∀ e, 0 < length e)
    (φ : K →+* L) (c : G.edgeSet → K) :
    (harmonicProjectionOnto L tail head length hpos (φ ∘ c) : G.edgeSet → L) =
      φ ∘ (harmonicProjectionOnto K tail head length hpos c : G.edgeSet → K) := by
  let h := harmonicProjectionOnto K tail head length hpos c
  have hh := (mem_harmonicCochains_iff K tail head length _).1 h.property
  let h' : harmonicCochains L tail head length := ⟨φ ∘ (h : G.edgeSet → K),
    (mem_harmonicCochains_iff L tail head length _).2 (by simp [edgeDivergence_map, hh])⟩
  obtain ⟨f, hf⟩ := (mem_exactCochains_iff K tail head _).1
    (sub_harmonicProjectionOnto_mem_exact K tail head length hpos c)
  have heq : harmonicProjectionOnto L tail head length hpos (φ ∘ c) = h' := by
    apply (harmonicProjectionOnto_eq_iff_sub_mem_exact L tail head length hpos _ _).2
    refine (mem_exactCochains_iff L tail head _).2 ⟨φ ∘ f, ?_⟩
    have hmap : edgeDifferential tail head (φ ∘ f) = φ ∘ edgeDifferential tail head f :=
      edgeDifferential_map tail head φ.toAddMonoidHom f
    rw [hmap, hf]
    funext e
    exact map_sub φ (c e) (h.val e)
  exact congrArg Subtype.val heq

/-- Reversing the selected edges changes the sign of their harmonic components. -/
theorem harmonicProjectionOnto_swap (K : Type w) [Field K] [CharZero K]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ) (hpos : ∀ e, 0 < length e)
    (s : G.edgeSet → Prop) [DecidablePred s] (c : G.edgeSet → K) :
    (harmonicProjectionOnto K (edgeSwapTail tail head s) (edgeSwapHead tail head s) length hpos
        (edgeSignChange s c) : G.edgeSet → K) =
      edgeSignChange s (harmonicProjectionOnto K tail head length hpos c : G.edgeSet → K) := by
  let h := harmonicProjectionOnto K tail head length hpos c
  have hh := (mem_harmonicCochains_iff K tail head length _).1 h.property
  let h' : harmonicCochains K (edgeSwapTail tail head s) (edgeSwapHead tail head s) length :=
    ⟨edgeSignChange s (h : G.edgeSet → K),
      (mem_harmonicCochains_iff K _ _ length _).2 (by rw [edgeDivergence_swap, hh])⟩
  obtain ⟨f, hf⟩ := (mem_exactCochains_iff K tail head _).1
    (sub_harmonicProjectionOnto_mem_exact K tail head length hpos c)
  have heq : harmonicProjectionOnto K _ _ length hpos (edgeSignChange s c) = h' := by
    apply (harmonicProjectionOnto_eq_iff_sub_mem_exact K _ _ length hpos _ _).2
    refine (mem_exactCochains_iff K _ _ _).2 ⟨f, ?_⟩
    rw [edgeDifferential_swap, hf]
    funext e
    by_cases he : s e <;> simp [h', h, he, sub_eq_add_neg, add_comm]
  exact congrArg Subtype.val heq

end Graph
