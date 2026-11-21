/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Basic
public import TauCeti.Combinatorics.Graph.Orientation.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Exact cochains and weighted divergence of multigraphs

An edge cochain assigns a value to each actual edge, retaining separate coordinates for parallel
edges. The differential uses tail minus head, and weighted divergence divides each contribution
by its rational edge length. The two contributions cancel when tail and head agree, as they
do for an oriented loop even when its cochain value is nonzero.

The basic differential works in any additive commutative group, its linear version works over
any semiring, and weighted divergence works over a division ring. Changing selected edge
directions changes the signs of their cochain coordinates.

## Main declarations

- `Graph.edgeDifferentialLinear` sends vertex potentials to their edge differences.
- `Graph.edgeDivergence` sends edge cochains to weighted vertex currents.
- `Graph.endpointMatrix` gives the rational signed incidence matrix for these operators.
-/

public section

open Matrix

namespace Graph

universe u v w

variable {V : Type u} {E : Type v} {G : Graph V E}

/-- The oriented edge differential, with the tail-minus-head convention. The endpoint maps
may be arbitrary. A graph orientation supplies maps compatible with incidence. -/
def edgeDifferential {A : Type w} [AddCommGroup A]
    (tail head : G.edgeSet → G.vertexSet) (f : G.vertexSet → A) : G.edgeSet → A :=
  fun e ↦ f (tail e) - f (head e)

@[simp]
theorem edgeDifferential_apply {A : Type w} [AddCommGroup A]
    (tail head : G.edgeSet → G.vertexSet) (f : G.vertexSet → A) (e : G.edgeSet) :
    edgeDifferential tail head f e = f (tail e) - f (head e) := by
  rfl

/-- Taking edge differentials commutes with additive homomorphisms. -/
theorem edgeDifferential_map {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (tail head : G.edgeSet → G.vertexSet) (φ : A →+ B) (f : G.vertexSet → A) :
    edgeDifferential tail head (φ ∘ f) = φ ∘ edgeDifferential tail head f := by
  funext e
  exact (map_sub φ _ _).symm

/-- The differential as a linear map, with arbitrary module coefficients. -/
def edgeDifferentialLinear (R : Type*) [Semiring R] {A : Type w} [AddCommGroup A]
    [Module R A] (tail head : G.edgeSet → G.vertexSet) :
    (G.vertexSet → A) →ₗ[R] (G.edgeSet → A) :=
  LinearMap.funLeft R A tail - LinearMap.funLeft R A head

@[simp]
theorem edgeDifferentialLinear_apply (R : Type*) [Semiring R] {A : Type w}
    [AddCommGroup A] [Module R A] (tail head : G.edgeSet → G.vertexSet)
    (f : G.vertexSet → A) :
    edgeDifferentialLinear R tail head f = edgeDifferential tail head f := by
  rfl

/-- Cochains that are differentials of vertex potentials. -/
def exactCochains (R : Type*) [Semiring R] {A : Type w} [AddCommGroup A] [Module R A]
    (tail head : G.edgeSet → G.vertexSet) : Submodule R (G.edgeSet → A) :=
  LinearMap.range (edgeDifferentialLinear R tail head)

/-- The space of exact cochains is the range of the linear differential. -/
theorem exactCochains_eq_range (R : Type*) [Semiring R] {A : Type w}
    [AddCommGroup A] [Module R A] (tail head : G.edgeSet → G.vertexSet) :
    exactCochains R tail head = LinearMap.range (edgeDifferentialLinear R (A := A) tail head) := by
  rfl

@[simp]
theorem mem_exactCochains_iff (R : Type*) [Semiring R] {A : Type w} [AddCommGroup A]
    [Module R A] (tail head : G.edgeSet → G.vertexSet) (c : G.edgeSet → A) :
    c ∈ exactCochains R tail head ↔ ∃ f, edgeDifferential tail head f = c := by
  simp only [exactCochains_eq_range, LinearMap.mem_range, edgeDifferentialLinear_apply]

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

/-- Weighted divergence on actual edge coordinates. The two contributions of an edge cancel
when its tail equals its head, as for a loop in a graph orientation. Only the actual edge
set needs to be finite.
The reciprocal length multiplies on the right, preserving left linearity over a division ring. -/
noncomputable def edgeDivergence (K : Type w) [DivisionRing K]
    [Fintype G.edgeSet] (tail head : G.edgeSet → G.vertexSet)
    (length : G.edgeSet → ℚ) : (G.edgeSet → K) →ₗ[K] (G.vertexSet → K) := by
  classical
  exact Matrix.vecMulLinear (Matrix.of fun e v ↦
    (if tail e = v then (length e : K)⁻¹ else 0) -
      (if head e = v then (length e : K)⁻¹ else 0))

/-- Divergence sums the tail contributions and subtracts the head contributions. -/
theorem edgeDivergence_apply (K : Type w) [DivisionRing K] [Fintype G.edgeSet]
    [DecidableEq G.vertexSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (c : G.edgeSet → K) (v : G.vertexSet) :
    edgeDivergence K tail head length c v =
      ∑ e, ((if tail e = v then c e / (length e : K) else 0) -
        (if head e = v then c e / (length e : K) else 0)) := by
  unfold edgeDivergence
  simp only [Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp [div_eq_mul_inv]

/-- Applying a ring homomorphism to cochain coefficients commutes with divergence. -/
theorem edgeDivergence_map {K L : Type*} [DivisionRing K] [DivisionRing L]
    [Fintype G.edgeSet] (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (φ : K →+* L) (c : G.edgeSet → K) :
    edgeDivergence L tail head length (φ ∘ c) = φ ∘ edgeDivergence K tail head length c := by
  classical
  funext v
  simp only [Function.comp_apply, edgeDivergence_apply, map_sum, map_sub, apply_ite, map_div₀,
    map_ratCast, map_zero]

/-- The tail-minus-head incidence matrix on actual edge and vertex coordinates. A row is zero
when the two endpoints agree. -/
noncomputable def endpointMatrix [DecidableEq G.vertexSet]
    (tail head : G.edgeSet → G.vertexSet) : Matrix G.edgeSet G.vertexSet ℚ :=
  fun e v ↦ (if tail e = v then 1 else 0) - (if head e = v then 1 else 0)

/-- The entry of the rational incidence matrix at an edge and a vertex. -/
theorem endpointMatrix_apply [DecidableEq G.vertexSet]
    (tail head : G.edgeSet → G.vertexSet) (e : G.edgeSet) (v : G.vertexSet) :
    endpointMatrix tail head e v =
      (if tail e = v then 1 else 0) - (if head e = v then 1 else 0) := by
  rfl

/-- The scalar differential is the rational incidence matrix after extending coefficients. -/
theorem edgeDifferentialLinear_eq_matrix (K : Type w) [Field K] [CharZero K]
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

/-- Weighted divergence is the weighted transpose incidence matrix after extending
coefficients. -/
theorem edgeDivergence_eq_matrix (K : Type w) [Field K] [CharZero K]
    [Fintype G.edgeSet] [DecidableEq G.edgeSet] [DecidableEq G.vertexSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ) :
    edgeDivergence K tail head length =
      (((endpointMatrix tail head)ᵀ * diagonal (fun e ↦ (length e)⁻¹)).map
        (Rat.castHom K)).mulVecLin := by
  unfold edgeDivergence
  rw [← Matrix.vecMulLinear_transpose]
  congr 1
  ext e v
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.mul_diagonal,
    endpointMatrix_apply, Matrix.of_apply]
  split_ifs <;> simp

/-- The tail after swapping endpoints on the selected actual edges. -/
def edgeSwapTail (tail head : G.edgeSet → G.vertexSet) (p : G.edgeSet → Prop)
    [DecidablePred p] : G.edgeSet → G.vertexSet :=
  fun e ↦ if p e then head e else tail e

/-- The head after swapping endpoints on the selected actual edges. -/
def edgeSwapHead (tail head : G.edgeSet → G.vertexSet) (p : G.edgeSet → Prop)
    [DecidablePred p] : G.edgeSet → G.vertexSet :=
  edgeSwapTail head tail p

/-- The swapped tail gives the old head on selected edges and the old tail elsewhere. -/
@[simp]
theorem edgeSwapTail_apply (tail head : G.edgeSet → G.vertexSet)
    (p : G.edgeSet → Prop) [DecidablePred p] (e : G.edgeSet) :
    edgeSwapTail tail head p e = if p e then head e else tail e := by
  rfl

/-- The swapped head gives the old tail on selected edges and the old head elsewhere. -/
@[simp]
theorem edgeSwapHead_apply (tail head : G.edgeSet → G.vertexSet)
    (p : G.edgeSet → Prop) [DecidablePred p] (e : G.edgeSet) :
    edgeSwapHead tail head p e = if p e then tail e else head e := by
  rfl

/-- Change the cochain sign on the selected actual edges. A loop coordinate may change sign,
although its contributions to the differential and divergence remain zero. -/
def edgeSignChange {A : Type w} [AddCommGroup A] (p : G.edgeSet → Prop) [DecidablePred p]
    (c : G.edgeSet → A) : G.edgeSet → A :=
  fun e ↦ if p e then -c e else c e

@[simp]
theorem edgeSignChange_apply {A : Type w} [AddCommGroup A]
    (p : G.edgeSet → Prop) [DecidablePred p] (c : G.edgeSet → A) (e : G.edgeSet) :
    edgeSignChange p c e = if p e then -c e else c e := by
  rfl

/-- Swapping the selected endpoint pairs changes exactly the corresponding differential signs. -/
theorem edgeDifferential_swap {A : Type w} [AddCommGroup A]
    (tail head : G.edgeSet → G.vertexSet) (p : G.edgeSet → Prop) [DecidablePred p]
    (f : G.vertexSet → A) :
    edgeDifferential (edgeSwapTail tail head p) (edgeSwapHead tail head p) f =
      edgeSignChange p (edgeDifferential tail head f) := by
  funext e
  by_cases h : p e <;> simp [h]

/-- Changing the selected endpoint pairs and cochain signs preserves divergence. -/
theorem edgeDivergence_swap (K : Type w) [DivisionRing K] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (p : G.edgeSet → Prop) [DecidablePred p] (c : G.edgeSet → K) :
    edgeDivergence K (edgeSwapTail tail head p) (edgeSwapHead tail head p) length
        (edgeSignChange p c) =
      edgeDivergence K tail head length c := by
  classical
  funext v
  simp only [edgeDivergence_apply]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : p e
  · simp only [edgeSwapTail, edgeSwapHead, h, ↓reduceIte, edgeSignChange_apply, neg_div]
    split_ifs <;> abel
  · simp [edgeSwapTail, edgeSwapHead, h]

end Graph
