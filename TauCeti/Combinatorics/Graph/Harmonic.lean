/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Basic
public import TauCeti.Combinatorics.Graph.Orientation.Basic
public import Mathlib.LinearAlgebra.Projection
import TauCeti.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Weighted harmonic and exact cochains of multigraphs

An edge cochain assigns one value to each actual edge in the chosen orientation. The differential
uses tail minus head, and divergence weights each contribution by the reciprocal edge length.
A loop contributes zero to both maps. Distinct parallel edges have separate coordinates.

For positive rational lengths the harmonic and exact subspaces are complementary over any
characteristic-zero field. The resulting linear harmonic projection commutes with field
homomorphisms, and potentials with zero differential are constant on each connected component.

This is the rational-length version of Besser, *p-adic heights and Vologodsky integration*,
arXiv:1711.06957, Definitions 4.1–4.3 and Theorem 4.4. The weighted rank calculation follows
the sum-of-squares argument for `Matrix.rank_transpose_mul_self`, and `Matrix.rank_map`
transports that calculation from the rationals.
-/

public section

open Matrix Module

namespace Graph

universe u v w

variable {V : Type u} {E : Type v} {G : Graph V E}

/-- The oriented edge differential, with the tail-minus-head convention. The two endpoint maps
may be arbitrary; an orientation supplies the maps compatible with graph incidence. -/
def edgeDifferential {A : Type w} [AddCommGroup A]
    (tail head : G.edgeSet → G.vertexSet) (f : G.vertexSet → A) : G.edgeSet → A :=
  fun e ↦ f (tail e) - f (head e)

@[simp]
theorem edgeDifferential_apply {A : Type w} [AddCommGroup A]
    (tail head : G.edgeSet → G.vertexSet) (f : G.vertexSet → A) (e : G.edgeSet) :
    edgeDifferential tail head f e = f (tail e) - f (head e) := by
  rfl

/-- The differential as a linear map. -/
def edgeDifferentialLinear (K : Type w) [Ring K]
    (tail head : G.edgeSet → G.vertexSet) :
    (G.vertexSet → K) →ₗ[K] (G.edgeSet → K) :=
  LinearMap.pi fun e ↦
    LinearMap.proj (R := K) (φ := fun _ ↦ K) (tail e) -
      LinearMap.proj (R := K) (φ := fun _ ↦ K) (head e)

@[simp]
theorem edgeDifferentialLinear_apply (K : Type w) [Ring K]
    (tail head : G.edgeSet → G.vertexSet) (f : G.vertexSet → K) :
    edgeDifferentialLinear K tail head f = edgeDifferential tail head f := by
  rfl

/-- A vertex potential has zero differential exactly when its values agree on each connected
component. In particular this condition depends only on the incidence of the graph. -/
theorem edgeDifferential_eq_zero_iff {A : Type w} [AddCommGroup A] (o : G.Orientation)
    (f : G.vertexSet → A) :
    edgeDifferential o.tail o.head f = 0 ↔
      ∀ x y : G.vertexSet, G.Reachable x y → f x = f y := by
  constructor
  · intro h
    have hedge (e : G.edgeSet) : f (o.tail e) = f (o.head e) := by
      simpa only [edgeDifferential_apply, Pi.zero_apply, sub_eq_zero] using congrFun h e
    have hlink {e x y} (hxy : G.IsLink e x y) :
        f ⟨x, hxy.left_mem⟩ = f ⟨y, hxy.right_mem⟩ := by
      let a : G.edgeSet := ⟨e, hxy.edge_mem⟩
      rcases (o.isLink a).eq_and_eq_or_eq_and_eq hxy with ⟨ht, hh⟩ | ⟨ht, hh⟩
      · exact (congrArg f (Subtype.ext ht)).symm.trans
          ((hedge a).trans (congrArg f (Subtype.ext hh)))
      · exact (congrArg f (Subtype.ext hh)).symm.trans
          ((hedge a).symm.trans (congrArg f (Subtype.ext ht)))
    intro x y hxy
    apply hxy.elim
    have hwalk {a b : V} (p : G.Walk a b) (ha : a ∈ G.vertexSet) (hb : b ∈ G.vertexSet) :
        f ⟨a, ha⟩ = f ⟨b, hb⟩ := by
      induction p with
      | nil => rfl
      | cons _ hstep _ ih => exact (hlink hstep).trans (ih hstep.right_mem hb)
    exact fun p ↦ hwalk p x.property y.property
  · intro h
    funext e
    simpa only [edgeDifferential_apply, Pi.zero_apply, sub_eq_zero] using
      h _ _ (o.isLink e).reachable

/-- Weighted divergence on actual edge coordinates. Its two endpoint contributions cancel on
loops. Only the actual edge set, rather than the ambient edge type, needs to be finite. -/
noncomputable def edgeDivergence (K : Type w) [Field K]
    [Fintype G.edgeSet] (tail head : G.edgeSet → G.vertexSet)
    (length : G.edgeSet → ℚ) : (G.edgeSet → K) →ₗ[K] (G.vertexSet → K) := by
  classical
  exact
    { toFun := fun c v ↦ ∑ e, ((if tail e = v then c e / (length e : K) else 0) -
        (if head e = v then c e / (length e : K) else 0))
      map_add' := by
        intro c d
        ext v
        simp only [Pi.add_apply, add_div]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro e _
        split_ifs <;> ring
      map_smul' := by
        intro a c
        ext v
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        split_ifs <;> ring }

/-- Divergence sums the tail contributions and subtracts the head contributions. -/
theorem edgeDivergence_apply (K : Type w) [Field K] [Fintype G.edgeSet]
    [DecidableEq G.vertexSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (c : G.edgeSet → K) (v : G.vertexSet) :
    edgeDivergence K tail head length c v =
      ∑ e, ((if tail e = v then c e / (length e : K) else 0) -
        (if head e = v then c e / (length e : K) else 0)) := by
  unfold edgeDivergence
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> rfl

/-- Applying a field homomorphism to the coefficients of a cochain commutes with divergence. -/
theorem edgeDivergence_map {K L : Type*} [Field K] [Field L] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (φ : K →+* L) (c : G.edgeSet → K) :
    edgeDivergence L tail head length (φ ∘ c) = φ ∘ edgeDivergence K tail head length c := by
  classical
  funext v
  simp only [Function.comp_apply, edgeDivergence_apply, map_sum, map_sub, apply_ite, map_div₀,
    map_ratCast, map_zero]

/-- Cochains that are differentials of vertex potentials. -/
def exactCochains (K : Type w) [Ring K] (tail head : G.edgeSet → G.vertexSet) :
    Submodule K (G.edgeSet → K) :=
  LinearMap.range (edgeDifferentialLinear K tail head)

/-- Cochains with zero weighted divergence. -/
noncomputable def harmonicCochains (K : Type w) [Field K] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ) :
    Submodule K (G.edgeSet → K) :=
  LinearMap.ker (edgeDivergence K tail head length)

@[simp]
theorem mem_exactCochains_iff (K : Type w) [Ring K]
    (tail head : G.edgeSet → G.vertexSet) (c : G.edgeSet → K) :
    c ∈ exactCochains K tail head ↔ ∃ f, edgeDifferential tail head f = c := Iff.rfl

@[simp]
theorem mem_harmonicCochains_iff (K : Type w) [Field K] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (c : G.edgeSet → K) :
    c ∈ harmonicCochains K tail head length ↔
      edgeDivergence K tail head length c = 0 := Iff.rfl

private noncomputable def endpointMatrix [DecidableEq G.vertexSet]
    (tail head : G.edgeSet → G.vertexSet) : Matrix G.edgeSet G.vertexSet ℚ :=
  fun e v ↦ (if tail e = v then 1 else 0) - (if head e = v then 1 else 0)

private theorem ker_weightedEndpointMatrix [Fintype G.edgeSet] [Fintype G.vertexSet]
    [DecidableEq G.edgeSet] [DecidableEq G.vertexSet]
    (tail head : G.edgeSet → G.vertexSet) (w : G.edgeSet → ℚ) (hw : ∀ i, 0 < w i) :
    LinearMap.ker ((endpointMatrix tail head)ᵀ * diagonal w * endpointMatrix tail head).mulVecLin =
      LinearMap.ker (endpointMatrix tail head).mulVecLin := by
  let A := endpointMatrix tail head
  -- Name the matrix whose image occurs twice in the weighted sum of squares.
  change LinearMap.ker (Aᵀ * diagonal w * A).mulVecLin = LinearMap.ker A.mulVecLin
  ext x
  simp only [LinearMap.mem_ker, mulVecLin_apply]
  constructor
  · intro h
    have hs : ∑ i, w i * (A *ᵥ x) i ^ 2 = 0 := by
      have h' := congrArg (dotProduct x) h
      have h'' : dotProduct x (Aᵀ *ᵥ (diagonal w *ᵥ (A *ᵥ x))) = 0 := by
        simpa only [← mulVec_mulVec, dotProduct_zero] using h'
      rw [dotProduct_mulVec, vecMul_transpose] at h''
      simpa only [mulVec_diagonal, dotProduct, pow_two, mul_left_comm] using h''
    have hz (i : G.edgeSet) : w i * (A *ᵥ x) i ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦
        mul_nonneg (hw j).le (sq_nonneg _))).1 hs i (Finset.mem_univ i)
    ext i
    exact (sq_eq_zero_iff).1 ((mul_eq_zero.1 (hz i)).resolve_left (hw i).ne')
  · intro h
    rw [← mulVec_mulVec, h, mulVec_zero]

private theorem rank_weightedEndpointMatrix [Fintype G.edgeSet] [Finite G.vertexSet]
    [DecidableEq G.edgeSet] [DecidableEq G.vertexSet]
    (tail head : G.edgeSet → G.vertexSet) (w : G.edgeSet → ℚ) (hw : ∀ i, 0 < w i) :
    ((endpointMatrix tail head)ᵀ * diagonal w * endpointMatrix tail head).rank =
      (endpointMatrix tail head).rank := by
  let := Fintype.ofFinite G.vertexSet
  have h := ((endpointMatrix tail head)ᵀ * diagonal w *
    endpointMatrix tail head).mulVecLin.finrank_range_add_finrank_ker
  rw [ker_weightedEndpointMatrix tail head w hw] at h
  have h' := (endpointMatrix tail head).mulVecLin.finrank_range_add_finrank_ker
  rw [finrank_range_mulVecLin] at h h'
  omega

private theorem isCompl_weightedEndpointMatrix [Fintype G.edgeSet] [Fintype G.vertexSet]
    [DecidableEq G.edgeSet] [DecidableEq G.vertexSet] (K : Type w) [Field K] [CharZero K]
    (tail head : G.edgeSet → G.vertexSet) (w : G.edgeSet → ℚ) (hw : ∀ i, 0 < w i) :
    IsCompl (LinearMap.ker (((endpointMatrix tail head)ᵀ * diagonal w).map
      (Rat.castHom K)).mulVecLin)
      (LinearMap.range ((endpointMatrix tail head).map (Rat.castHom K)).mulVecLin) := by
  let D := (endpointMatrix tail head).map (Rat.castHom K)
  let B := ((endpointMatrix tail head)ᵀ * diagonal w).map (Rat.castHom K)
  -- Use the two matrices over the target field for both the rank and disjointness calculations.
  change IsCompl (LinearMap.ker B.mulVecLin) (LinearMap.range D.mulVecLin)
  have hrank : (B * D).rank = D.rank := by
    dsimp only [B, D]
    rw [← Matrix.map_mul, Matrix.rank_map, Matrix.rank_map]
    exact rank_weightedEndpointMatrix tail head w hw
  have hrankB : B.rank ≤ D.rank := by
    dsimp only [B, D]
    rw [Matrix.rank_map, Matrix.rank_map]
    exact (Matrix.rank_mul_le_left _ _).trans_eq (endpointMatrix tail head).rank_transpose
  apply (Submodule.isCompl_iff_disjoint _ _ ?_).2
  · apply Disjoint.symm
    apply Submodule.disjoint_ker_of_finrank_le B.mulVecLin
    rw [← LinearMap.range_comp, ← mulVecLin_mul, finrank_range_mulVecLin,
      finrank_range_mulVecLin, hrank]
  · have h := B.mulVecLin.finrank_range_add_finrank_ker
    rw [finrank_range_mulVecLin] at h ⊢
    omega

private theorem edgeDifferentialLinear_eq_matrix (K : Type w) [Field K] [CharZero K]
    [Fintype G.vertexSet] [DecidableEq G.vertexSet]
    (tail head : G.edgeSet → G.vertexSet) :
    edgeDifferentialLinear K tail head =
      ((endpointMatrix tail head).map (Rat.castHom K)).mulVecLin := by
  apply LinearMap.ext
  intro f
  ext e
  simp only [edgeDifferentialLinear_apply, edgeDifferential_apply, mulVecLin_apply,
    Matrix.mulVec, dotProduct, Matrix.map_apply]
  have hterm (v : G.vertexSet) :
      (Rat.castHom K) (endpointMatrix tail head e v) * f v =
        (if tail e = v then f v else 0) - (if head e = v then f v else 0) := by
    unfold endpointMatrix
    split_ifs <;> simp
  simp_rw [hterm, Finset.sum_sub_distrib]
  simp [eq_comm]

private theorem edgeDivergence_eq_matrix (K : Type w) [Field K] [CharZero K]
    [Fintype G.edgeSet] [DecidableEq G.edgeSet] [DecidableEq G.vertexSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ) :
    edgeDivergence K tail head length =
      (((endpointMatrix tail head)ᵀ * diagonal (fun e ↦ (length e)⁻¹)).map
        (Rat.castHom K)).mulVecLin := by
  apply LinearMap.ext
  intro c
  ext v
  rw [edgeDivergence_apply, mulVecLin_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.mul_diagonal,
    Matrix.transpose_apply, endpointMatrix]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp [div_eq_mul_inv, mul_comm]

/-- Weighted harmonic cochains and exact cochains are complementary. This algebraic fact holds
for arbitrary endpoint maps, independently of their incidence in a graph. Positivity is needed
only over the rational numbers; rank invariance supplies all characteristic-zero fields. -/
theorem isCompl_harmonic_exact (K : Type w) [Field K] [CharZero K]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) :
    IsCompl (harmonicCochains K tail head length) (exactCochains K tail head) := by
  classical
  let := Fintype.ofFinite G.vertexSet
  rw [harmonicCochains, exactCochains, edgeDivergence_eq_matrix,
    edgeDifferentialLinear_eq_matrix]
  exact isCompl_weightedEndpointMatrix K tail head _
    (fun e ↦ inv_pos.2 (hpos e))

/-- Every cochain of a finite oriented multigraph has a unique harmonic/exact pair.
Uniqueness concerns the two cochains; the potential of the exact part need not be unique.
The actual vertex and edge sets are finite, so the ambient types can be infinite. -/
theorem harmonic_exact_decomposition (K : Type w) [Field K] [CharZero K]
    [Finite G.vertexSet] [Fintype G.edgeSet] (o : G.Orientation)
    (length : G.edgeSet → ℚ) (hpos : ∀ e, 0 < length e) (c : G.edgeSet → K) :
    ∃! p : (G.edgeSet → K) × (G.edgeSet → K),
      edgeDivergence K o.tail o.head length p.1 = 0 ∧
      (∃ f, edgeDifferential o.tail o.head f = p.2) ∧ p.1 + p.2 = c := by
  have hc := isCompl_harmonic_exact K o.tail o.head length hpos
  obtain ⟨p, hp, huniq⟩ := Submodule.existsUnique_add_of_isCompl_prod hc c
  refine ⟨⟨p.1, p.2⟩, ⟨p.1.property, p.2.property, hp⟩, ?_⟩
  rintro ⟨h, r⟩ ⟨hh, hr, hsum⟩
  have heq := huniq (⟨⟨h, hh⟩, ⟨r, hr⟩⟩) hsum
  exact congrArg (fun q ↦ ((q.1 : G.edgeSet → K), (q.2 : G.edgeSet → K))) heq

/-- The harmonic component of a cochain, as a linear map to the harmonic subspace. -/
noncomputable def harmonicProjection (K : Type w) [Field K] [CharZero K]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) :
    (G.edgeSet → K) →ₗ[K] harmonicCochains K tail head length :=
  (harmonicCochains K tail head length).projectionOnto (exactCochains K tail head)
    (isCompl_harmonic_exact K tail head length hpos)

/-- The projection is the identity on harmonic cochains. -/
@[simp]
theorem harmonicProjection_apply_harmonic (K : Type w) [Field K] [CharZero K]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) (c : harmonicCochains K tail head length) :
    harmonicProjection K tail head length hpos c = c := by
  exact Submodule.projectionOnto_apply_left _ c

/-- The kernel of harmonic projection is exactly the space of differentials. -/
theorem ker_harmonicProjection (K : Type w) [Field K] [CharZero K]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) :
    LinearMap.ker (harmonicProjection K tail head length hpos) =
      exactCochains K tail head := by
  exact Submodule.ker_projectionOnto _

/-- Exact cochains have zero harmonic component. -/
@[simp]
theorem harmonicProjection_differential (K : Type w) [Field K] [CharZero K]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) (f : G.vertexSet → K) :
    harmonicProjection K tail head length hpos (edgeDifferential tail head f) = 0 := by
  apply (Submodule.projectionOnto_apply_eq_zero_iff _).2
  exact ⟨f, rfl⟩

/-- Adding a differential preserves the harmonic component. -/
theorem harmonicProjection_add_differential (K : Type w) [Field K] [CharZero K]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) (c : G.edgeSet → K) (f : G.vertexSet → K) :
    harmonicProjection K tail head length hpos (c + edgeDifferential tail head f) =
      harmonicProjection K tail head length hpos c := by
  rw [map_add, harmonicProjection_differential, add_zero]

/-- Subtracting the harmonic component leaves an exact cochain. -/
theorem sub_harmonicProjection_mem_exact (K : Type w) [Field K] [CharZero K]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) (c : G.edgeSet → K) :
    c - (harmonicProjection K tail head length hpos c : G.edgeSet → K) ∈
      exactCochains K tail head := by
  exact Submodule.sub_projection_mem _ c

/-- Extending coefficients sends a cochain's harmonic component to the harmonic component of
the extended cochain. -/
theorem harmonicProjection_map {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L]
    [Finite G.vertexSet] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ) (hpos : ∀ e, 0 < length e)
    (φ : K →+* L) (c : G.edgeSet → K) :
    (harmonicProjection L tail head length hpos (φ ∘ c) : G.edgeSet → L) =
      φ ∘ (harmonicProjection K tail head length hpos c : G.edgeSet → K) := by
  let p := harmonicProjection K tail head length hpos c
  have hp : edgeDivergence K tail head length (p : G.edgeSet → K) = 0 :=
    (mem_harmonicCochains_iff K tail head length _).1 p.property
  let q : harmonicCochains L tail head length := ⟨φ ∘ (p : G.edgeSet → K),
    (mem_harmonicCochains_iff L tail head length _).2 (by simp [edgeDivergence_map, hp])⟩
  obtain ⟨f, hf⟩ := (mem_exactCochains_iff K tail head _).1
    (sub_harmonicProjection_mem_exact K tail head length hpos c)
  have hsum : φ ∘ c = (q : G.edgeSet → L) + edgeDifferential tail head (φ ∘ f) := by
    funext e
    have heq : c e = p.val e + edgeDifferential tail head f e := by
      rw [congrFun hf e, Pi.sub_apply]
      abel
    simpa only [q, Function.comp_apply, Pi.add_apply, edgeDifferential_apply, map_add, map_sub]
      using congrArg φ heq
  rw [hsum, harmonicProjection_add_differential, harmonicProjection_apply_harmonic]

end Graph
