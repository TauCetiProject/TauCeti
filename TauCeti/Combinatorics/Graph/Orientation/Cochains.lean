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
- `Graph.signedIncMatrix` gives the signed incidence matrix for these operators.
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
  ext e
  simp only [edgeDifferentialLinear, LinearMap.sub_apply, LinearMap.funLeft_apply,
    Pi.sub_apply, edgeDifferential_apply]

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

/-- The tail-minus-head signed incidence matrix on actual edge and vertex coordinates.
A row is zero when the two endpoints agree. -/
def signedIncMatrix (R : Type*) [AddGroupWithOne R] [DecidableEq G.vertexSet]
    (tail head : G.edgeSet → G.vertexSet) : Matrix G.edgeSet G.vertexSet R :=
  fun e ↦ Pi.single (tail e) 1 - Pi.single (head e) 1

/-- The entry of the signed incidence matrix at an edge and a vertex. -/
theorem signedIncMatrix_apply (R : Type*) [AddGroupWithOne R] [DecidableEq G.vertexSet]
    (tail head : G.edgeSet → G.vertexSet) (e : G.edgeSet) (v : G.vertexSet) :
    signedIncMatrix R tail head e v =
      (if tail e = v then 1 else 0) - (if head e = v then 1 else 0) := by
  simp only [signedIncMatrix, Pi.sub_apply, Pi.single_apply, eq_comm]

/-- Changing the coefficient ring preserves the signed incidence matrix. -/
theorem signedIncMatrix_map {R S : Type*} [NonAssocRing R] [NonAssocRing S]
    [DecidableEq G.vertexSet] (φ : R →+* S) (tail head : G.edgeSet → G.vertexSet) :
    (signedIncMatrix R tail head).map φ = signedIncMatrix S tail head := by
  ext e v
  simp only [Matrix.map_apply, signedIncMatrix_apply]
  split_ifs <;> simp

/-- The scalar differential is multiplication by the signed incidence matrix. -/
theorem edgeDifferentialLinear_eq_mulVecLin (R : Type w) [CommRing R]
    [Fintype G.vertexSet] [DecidableEq G.vertexSet]
    (tail head : G.edgeSet → G.vertexSet) :
    edgeDifferentialLinear R tail head = (signedIncMatrix R tail head).mulVecLin := by
  apply LinearMap.ext
  intro f
  ext e
  simp only [edgeDifferentialLinear_apply, edgeDifferential_apply, mulVecLin_apply,
    Matrix.mulVec, signedIncMatrix, sub_dotProduct, single_dotProduct, one_mul]

/-- Weighted divergence on actual edge coordinates. The two contributions of an edge cancel
when its tail equals its head, as for a loop in a graph orientation. Only the actual edge
set needs to be finite.
The reciprocal length multiplies on the right, preserving left linearity over a division ring. -/
noncomputable def edgeDivergence (K : Type w) [DivisionRing K]
    [Fintype G.edgeSet] (tail head : G.edgeSet → G.vertexSet)
    (length : G.edgeSet → ℚ) : (G.edgeSet → K) →ₗ[K] (G.vertexSet → K) := by
  classical
  exact Matrix.vecMulLinear
    (((signedIncMatrix K tail head)ᵀ * diagonal (fun e ↦ (length e : K)⁻¹))ᵀ)

/-- Divergence sums the tail contributions and subtracts the head contributions. -/
theorem edgeDivergence_apply (K : Type w) [DivisionRing K] [Fintype G.edgeSet]
    [DecidableEq G.vertexSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (c : G.edgeSet → K) (v : G.vertexSet) :
    edgeDivergence K tail head length c v =
      ∑ e, ((if tail e = v then c e / (length e : K) else 0) -
        (if head e = v then c e / (length e : K) else 0)) := by
  classical
  unfold edgeDivergence
  simp only [Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct, Matrix.transpose_apply,
    Matrix.mul_diagonal, signedIncMatrix_apply]
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

/-- Weighted divergence is right multiplication by the transpose of the rational weighted
incidence matrix after extending coefficients. -/
theorem edgeDivergence_eq_vecMulLinear (K : Type w) [DivisionRing K] [CharZero K]
    [Fintype G.edgeSet] [DecidableEq G.edgeSet] [DecidableEq G.vertexSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ) :
    edgeDivergence K tail head length =
      Matrix.vecMulLinear
        ((((signedIncMatrix ℚ tail head)ᵀ * diagonal (fun e ↦ (length e)⁻¹)).map
          (Rat.castHom K))ᵀ) := by
  unfold edgeDivergence
  rw [Matrix.map_mul, Matrix.transpose_map, signedIncMatrix_map,
    Matrix.diagonal_map (map_zero (Rat.castHom K))]
  simp only [map_inv₀, Rat.coe_castHom]
  congr 1
  ext e v
  simp only [Matrix.transpose_apply, Matrix.mul_diagonal, signedIncMatrix_apply]
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

namespace Orientation

/-- Reverse the selected actual edges, preserving their identities and incidences. -/
def reverseOn (o : G.Orientation) (p : G.edgeSet → Prop) [DecidablePred p] :
    G.Orientation where
  tail := edgeSwapTail o.tail o.head p
  head := edgeSwapHead o.tail o.head p
  isLink e := by
    by_cases h : p e
    · simpa only [edgeSwapTail_apply, edgeSwapHead_apply, h, ↓reduceIte] using (o.isLink e).symm
    · simpa only [edgeSwapTail_apply, edgeSwapHead_apply, h, ↓reduceIte] using o.isLink e

/-- Selected-edge reversal exchanges the tail and head exactly on the selected edges. -/
@[simp]
theorem reverseOn_tail (o : G.Orientation) (p : G.edgeSet → Prop) [DecidablePred p]
    (e : G.edgeSet) : (o.reverseOn p).tail e = if p e then o.head e else o.tail e := by
  exact edgeSwapTail_apply o.tail o.head p e

/-- Selected-edge reversal exchanges the head and tail exactly on the selected edges. -/
@[simp]
theorem reverseOn_head (o : G.Orientation) (p : G.edgeSet → Prop) [DecidablePred p]
    (e : G.edgeSet) : (o.reverseOn p).head e = if p e then o.tail e else o.head e := by
  exact edgeSwapHead_apply o.tail o.head p e

/-- Reversing the same selected edges twice restores the orientation. -/
@[simp]
theorem reverseOn_reverseOn (o : G.Orientation) (p : G.edgeSet → Prop) [DecidablePred p] :
    (o.reverseOn p).reverseOn p = o := by
  ext e
  by_cases h : p e <;> simp [h]

end Orientation

/-- Negate the selected edge coordinates as an involutive linear equivalence. When the endpoint
maps agree, as on a loop of a graph orientation, that coordinate contributes zero to the
differential and divergence even when sign change changes the coordinate. -/
def edgeSignChange (R : Type*) [Semiring R] {A : Type w} [AddCommGroup A] [Module R A]
    (p : G.edgeSet → Prop) [DecidablePred p] : (G.edgeSet → A) ≃ₗ[R] (G.edgeSet → A) :=
  LinearEquiv.piCongrRight fun e ↦ if p e then LinearEquiv.neg R else LinearEquiv.refl R A

/-- Sign change negates exactly the selected edge coordinates. -/
@[simp]
theorem edgeSignChange_apply (R : Type*) [Semiring R] {A : Type w}
    [AddCommGroup A] [Module R A] (p : G.edgeSet → Prop) [DecidablePred p]
    (c : G.edgeSet → A) (e : G.edgeSet) :
    edgeSignChange R p c e = if p e then -c e else c e := by
  simp only [edgeSignChange, LinearEquiv.piCongrRight_apply]
  split_ifs <;> simp only [LinearEquiv.neg_apply, LinearEquiv.refl_apply]

/-- Sign change is its own inverse linear equivalence. -/
@[simp]
theorem edgeSignChange_symm (R : Type*) [Semiring R] {A : Type w}
    [AddCommGroup A] [Module R A] (p : G.edgeSet → Prop) [DecidablePred p] :
    (edgeSignChange R (A := A) p).symm = edgeSignChange R p := by
  simp only [edgeSignChange, LinearEquiv.piCongrRight_symm]
  congr 1
  funext e
  split_ifs <;> simp

/-- Applying the same selected sign change twice restores the cochain. -/
@[simp]
theorem edgeSignChange_edgeSignChange (R : Type*) [Semiring R] {A : Type w}
    [AddCommGroup A] [Module R A] (p : G.edgeSet → Prop) [DecidablePred p]
    (c : G.edgeSet → A) : edgeSignChange R p (edgeSignChange R p c) = c := by
  simpa only [edgeSignChange_symm] using (edgeSignChange R p).symm_apply_apply c

/-- Swapping the selected endpoint pairs changes exactly the corresponding differential signs. -/
theorem edgeDifferential_swap (R : Type*) [Semiring R] {A : Type w} [AddCommGroup A]
    [Module R A] (tail head : G.edgeSet → G.vertexSet) (p : G.edgeSet → Prop)
    [DecidablePred p] (f : G.vertexSet → A) :
    edgeDifferential (edgeSwapTail tail head p) (edgeSwapHead tail head p) f =
      edgeSignChange R p (edgeDifferential tail head f) := by
  funext e
  by_cases h : p e <;> simp [h]

/-- Changing the selected endpoint pairs and cochain signs preserves divergence. -/
theorem edgeDivergence_swap (K : Type w) [DivisionRing K] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (p : G.edgeSet → Prop) [DecidablePred p] (c : G.edgeSet → K) :
    edgeDivergence K (edgeSwapTail tail head p) (edgeSwapHead tail head p) length
        (edgeSignChange K p c) =
      edgeDivergence K tail head length c := by
  classical
  funext v
  simp only [edgeDivergence_apply]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : p e
  · simp only [edgeSwapTail_apply, edgeSwapHead_apply, h, ↓reduceIte,
      edgeSignChange_apply, neg_div]
    split_ifs <;> abel
  · simp [h]

/-- Reversing selected edges changes their differential coordinates by the sign equivalence. -/
theorem edgeDifferential_reverseOn (R : Type*) [Semiring R] {A : Type w}
    [AddCommGroup A] [Module R A] (o : G.Orientation) (p : G.edgeSet → Prop)
    [DecidablePred p] (f : G.vertexSet → A) :
    edgeDifferential (o.reverseOn p).tail (o.reverseOn p).head f =
      edgeSignChange R p (edgeDifferential o.tail o.head f) :=
  edgeDifferential_swap R o.tail o.head p f

/-- Reversing selected edges and negating the same input coordinates preserves divergence. -/
theorem edgeDivergence_reverseOn (K : Type w) [DivisionRing K] [Fintype G.edgeSet]
    (o : G.Orientation) (length : G.edgeSet → ℚ) (p : G.edgeSet → Prop) [DecidablePred p]
    (c : G.edgeSet → K) :
    edgeDivergence K (o.reverseOn p).tail (o.reverseOn p).head length (edgeSignChange K p c) =
      edgeDivergence K o.tail o.head length c :=
  edgeDivergence_swap K o.tail o.head length p c

end Graph
