/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Orientation.Cochains
import Mathlib.LinearAlgebra.Projection
import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Weighted harmonic and exact cochains of multigraphs

For positive rational edge lengths the harmonic and exact subspaces of a finite multigraph are
complementary over every characteristic-zero field. The harmonic projection selects the unique
harmonic representative modulo exact cochains. It commutes with coefficient extension and with
sign changes on reversed edges.

## Main results

- `Graph.harmonic_exact_decomposition` gives the unique harmonic and exact parts of a cochain.
- `Graph.harmonicProjectionOnto` is the linear projection onto the harmonic subspace.

This is the rational-length version of Besser, *p-adic heights and Vologodsky integration*,
arXiv:1711.06957, Definitions 4.1–4.3 and Theorem 4.4.
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

/-- The space of harmonic cochains is the kernel of weighted divergence. -/
theorem harmonicCochains_eq_ker (K : Type w) [DivisionRing K] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ) :
    harmonicCochains K tail head length = LinearMap.ker (edgeDivergence K tail head length) := by
  rfl

@[simp]
theorem mem_harmonicCochains_iff (K : Type w) [DivisionRing K] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (c : G.edgeSet → K) :
    c ∈ harmonicCochains K tail head length ↔
      edgeDivergence K tail head length c = 0 := by
  rw [harmonicCochains_eq_ker, LinearMap.mem_ker]

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
  rw [harmonicCochains_eq_ker, exactCochains_eq_range, edgeDivergence_eq_vecMulLinear,
    Matrix.vecMulLinear_transpose, edgeDifferentialLinear_eq_mulVecLin]
  simpa only [signedIncMatrix_map] using
    Matrix.isCompl_ker_mulVecLin_transpose_mul_diagonal_range_map
      (signedIncMatrix ℚ tail head) (Rat.castHom K) _ (fun e ↦ inv_pos.2 (hpos e))

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
@[simp]
theorem ker_harmonicProjectionOnto (K : Type w) [Field K] [CharZero K]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) :
    LinearMap.ker (harmonicProjectionOnto K tail head length hpos) =
      exactCochains K tail head := by
  exact Submodule.ker_projectionOnto _

/-- A cochain has zero harmonic component if and only if it is exact. -/
@[simp]
theorem harmonicProjectionOnto_eq_zero_iff (K : Type w) [Field K] [CharZero K]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) (c : G.edgeSet → K) :
    harmonicProjectionOnto K tail head length hpos c = 0 ↔
      c ∈ exactCochains K tail head := by
  rw [← ker_harmonicProjectionOnto K tail head length hpos, LinearMap.mem_ker]

/-- A differential has zero harmonic component. -/
@[simp]
theorem harmonicProjectionOnto_differential (K : Type w) [Field K] [CharZero K]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) (f : G.vertexSet → K) :
    harmonicProjectionOnto K tail head length hpos (edgeDifferential tail head f) = 0 := by
  exact (harmonicProjectionOnto_eq_zero_iff K tail head length hpos _).2
    ((mem_exactCochains_iff K tail head _).2 ⟨f, rfl⟩)

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
  rw [← harmonicProjectionOnto_eq_zero_iff K tail head length hpos, map_sub,
    harmonicProjectionOnto_apply_harmonic, sub_eq_zero]

private theorem map_projection_of_mem {R S M N : Type*} [Ring R] [Ring S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    {p q : Submodule R M} {p' q' : Submodule S N}
    (hpq : IsCompl p q) (hpq' : IsCompl p' q') (φ : M →+ N)
    (hp : ∀ x ∈ p, φ x ∈ p') (hq : ∀ x ∈ q, φ x ∈ q') (x : M) :
    p'.projection q' hpq' (φ x) = φ (p.projection q hpq x) := by
  have h := congrArg φ (Submodule.projection_add_projection_eq_self hpq x)
  rw [map_add] at h
  have hp' := hp _ (Submodule.projection_apply_mem hpq x)
  have hq' := hq _ (Submodule.projection_apply_mem hpq.symm x)
  calc
    _ = p'.projection q' hpq' (φ (p.projection q hpq x) + φ (q.projection p hpq.symm x)) :=
      congrArg (p'.projection q' hpq') h.symm
    _ = _ := by
      rw [map_add, Submodule.projection_apply_of_mem_left hpq' hp',
        Submodule.projection_apply_of_mem_right hpq' hq', add_zero]

/-- Extending coefficients sends the harmonic component to the harmonic component of the
extended cochain. -/
theorem harmonicProjectionOnto_map {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ) (hpos : ∀ e, 0 < length e)
    (φ : K →+* L) (c : G.edgeSet → K) :
    (harmonicProjectionOnto L tail head length hpos (φ ∘ c) : G.edgeSet → L) =
      φ ∘ (harmonicProjectionOnto K tail head length hpos c : G.edgeSet → K) := by
  refine map_projection_of_mem (isCompl_harmonic_exact K tail head length hpos)
    (isCompl_harmonic_exact L tail head length hpos)
    (φ.toAddMonoidHom.compLeft G.edgeSet) ?_ ?_ c
  · intro h hh
    change φ ∘ h ∈ harmonicCochains L tail head length
    rw [mem_harmonicCochains_iff] at hh ⊢
    simp [edgeDivergence_map, hh]
  · intro r hr
    change φ ∘ r ∈ exactCochains L tail head
    rw [mem_exactCochains_iff] at hr ⊢
    obtain ⟨f, rfl⟩ := hr
    exact ⟨φ ∘ f, edgeDifferential_map tail head φ.toAddMonoidHom f⟩

/-- Swapping the selected endpoints and negating the same input coordinates negates exactly
those coordinates of the harmonic projection. -/
theorem harmonicProjectionOnto_swap (K : Type w) [Field K] [CharZero K]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ) (hpos : ∀ e, 0 < length e)
    (s : G.edgeSet → Prop) [DecidablePred s] (c : G.edgeSet → K) :
    (harmonicProjectionOnto K (edgeSwapTail tail head s) (edgeSwapHead tail head s) length hpos
        (edgeSignChange K s c) : G.edgeSet → K) =
      edgeSignChange K s (harmonicProjectionOnto K tail head length hpos c : G.edgeSet → K) := by
  refine map_projection_of_mem (isCompl_harmonic_exact K tail head length hpos)
    (isCompl_harmonic_exact K _ _ length hpos)
    (edgeSignChange K s).toLinearMap.toAddMonoidHom ?_ ?_ c
  · intro h hh
    change edgeSignChange K s h ∈ harmonicCochains K _ _ length
    rw [mem_harmonicCochains_iff, edgeDivergence_swap]
    exact (mem_harmonicCochains_iff K tail head length h).1 hh
  · intro r hr
    change edgeSignChange K s r ∈ exactCochains K _ _
    rw [mem_exactCochains_iff] at hr ⊢
    obtain ⟨f, rfl⟩ := hr
    exact ⟨f, edgeDifferential_swap K tail head s f⟩

/-- Harmonic projection commutes with the change of cochain coordinates induced by reversing
the selected edges of an orientation. -/
theorem Orientation.harmonicProjectionOnto_reverseOn (o : G.Orientation)
    (K : Type w) [Field K] [CharZero K] [Finite G.vertexSet] [Fintype G.edgeSet]
    (length : G.edgeSet → ℚ) (hpos : ∀ e, 0 < length e)
    (s : G.edgeSet → Prop) [DecidablePred s] (c : G.edgeSet → K) :
    (harmonicProjectionOnto K (o.reverseOn s).tail (o.reverseOn s).head length hpos
        (edgeSignChange K s c) : G.edgeSet → K) =
      edgeSignChange K s (harmonicProjectionOnto K o.tail o.head length hpos c :
        G.edgeSet → K) := by
  have ht : (o.reverseOn s).tail = edgeSwapTail o.tail o.head s := by
    funext e
    simp
  have hh : (o.reverseOn s).head = edgeSwapHead o.tail o.head s := by
    funext e
    simp
  rw [ht, hh]
  exact harmonicProjectionOnto_swap K o.tail o.head length hpos s c

end Graph
