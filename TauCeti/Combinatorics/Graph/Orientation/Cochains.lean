/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Basic
public import TauCeti.Combinatorics.Graph.Orientation.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.LinearAlgebra.Pi.SignChange

/-!
# Exact cochains and weighted divergence of multigraphs

An edge cochain assigns a value to each actual edge, retaining separate coordinates for parallel
edges. The differential uses tail minus head, and weighted divergence divides each contribution
by its rational edge length. The two contributions cancel when tail and head agree, as they
do for an oriented loop even when its cochain value is nonzero.

Lengths are cast to the coefficient division ring before inversion. A zero cast gives zero
weight, including when a positive rational length casts to zero in positive characteristic.

The basic differential works in any additive commutative group. A semiring action on that
group makes the differential linear, and weighted divergence works over a division ring.
Changing selected edge directions changes the signs of their cochain coordinates.

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

/-- The zero potential has zero differential. -/
@[simp]
theorem edgeDifferential_zero {A : Type w} [AddCommGroup A]
    (tail head : G.edgeSet → G.vertexSet) :
    edgeDifferential tail head (0 : G.vertexSet → A) = 0 := by
  funext e
  simp

/-- Taking edge differentials preserves addition of potentials. -/
@[simp]
theorem edgeDifferential_add {A : Type w} [AddCommGroup A]
    (tail head : G.edgeSet → G.vertexSet) (f g : G.vertexSet → A) :
    edgeDifferential tail head (f + g) =
      edgeDifferential tail head f + edgeDifferential tail head g := by
  funext e
  simp only [edgeDifferential_apply, Pi.add_apply]
  abel

/-- Taking edge differentials commutes with additive homomorphisms. -/
theorem edgeDifferential_map {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (tail head : G.edgeSet → G.vertexSet) (φ : A →+ B) (f : G.vertexSet → A) :
    edgeDifferential tail head (φ ∘ f) = φ ∘ edgeDifferential tail head f := by
  funext e
  exact (map_sub φ _ _).symm

/-- The differential as a linear map for a module whose coefficients form an additive
commutative group. -/
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

/-- The linear differential has as its kernel the potentials constant on connected components. -/
theorem mem_ker_edgeDifferentialLinear_iff (R : Type*) [Semiring R] {A : Type w}
    [AddCommGroup A] [Module R A] (o : G.Orientation) (f : G.vertexSet → A) :
    f ∈ LinearMap.ker (edgeDifferentialLinear R o.tail o.head) ↔
      ∀ x y : G.vertexSet, G.Reachable x y → f x = f y := by
  rw [LinearMap.mem_ker, edgeDifferentialLinear_apply, edgeDifferential_eq_zero_iff]

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

/-- Over any ring, the scalar differential is right multiplication by the transposed signed
incidence matrix. -/
theorem edgeDifferentialLinear_eq_vecMulLinear (R : Type w) [Ring R]
    [Fintype G.vertexSet] [DecidableEq G.vertexSet]
    (tail head : G.edgeSet → G.vertexSet) :
    edgeDifferentialLinear R tail head = (signedIncMatrix R tail head)ᵀ.vecMulLinear := by
  apply LinearMap.ext
  intro f
  ext e
  simp only [edgeDifferentialLinear_apply, edgeDifferential_apply, Matrix.vecMulLinear_apply,
    Matrix.vecMul, Matrix.transpose_apply, signedIncMatrix, dotProduct_sub,
    dotProduct_single, mul_one]

/-- The scalar differential is multiplication by the signed incidence matrix. -/
theorem edgeDifferentialLinear_eq_mulVecLin (R : Type w) [CommRing R]
    [Fintype G.vertexSet] [DecidableEq G.vertexSet]
    (tail head : G.edgeSet → G.vertexSet) :
    edgeDifferentialLinear R tail head = (signedIncMatrix R tail head).mulVecLin := by
  rw [edgeDifferentialLinear_eq_vecMulLinear, Matrix.vecMulLinear_transpose]

/-- Weighted divergence on actual edge coordinates. The two contributions of an edge cancel
when its tail equals its head, as for a loop in a graph orientation. Only the actual edge
set needs to be finite.
Lengths are cast to `K` before inversion, and a zero cast gives zero weight, even for a
positive rational length. The reciprocal length multiplies on the right, preserving left
linearity over a division ring. -/
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

/-- Weighted divergence is right multiplication by the coefficient extension of `(Aᵀ * D)ᵀ`,
where `A` is the edge-by-vertex signed incidence matrix and `D` is the diagonal matrix of
reciprocal rational lengths. -/
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

/-- Swapping the selected endpoint pairs negates exactly the selected differential values. -/
theorem edgeDifferential_swap {A : Type w} [AddCommGroup A]
    (tail head : G.edgeSet → G.vertexSet) (p : G.edgeSet → Prop)
    [DecidablePred p] (f : G.vertexSet → A) (e : G.edgeSet) :
    edgeDifferential (edgeSwapTail tail head p) (edgeSwapHead tail head p) f e =
      if p e then -edgeDifferential tail head f e else edgeDifferential tail head f e := by
  by_cases h : p e <;> simp [h]

/-- The linear differential commutes with the selected coordinate sign equivalence. -/
theorem edgeDifferentialLinear_swap (R : Type*) [Semiring R] {A : Type w}
    [AddCommGroup A] [Module R A] (tail head : G.edgeSet → G.vertexSet)
    (p : G.edgeSet → Prop) [DecidablePred p] :
    edgeDifferentialLinear R (A := A) (edgeSwapTail tail head p) (edgeSwapHead tail head p) =
      (TauCeti.piSignChange R p).toLinearMap.comp (edgeDifferentialLinear R tail head) := by
  ext f e
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, edgeDifferentialLinear_apply,
    TauCeti.piSignChange_apply, edgeDifferential_swap]

/-- Changing the selected endpoint pairs and cochain signs preserves divergence. -/
theorem edgeDivergence_swap (K : Type w) [DivisionRing K] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (p : G.edgeSet → Prop) [DecidablePred p] (c : G.edgeSet → K) :
    edgeDivergence K (edgeSwapTail tail head p) (edgeSwapHead tail head p) length
        (TauCeti.piSignChange K p c) =
      edgeDivergence K tail head length c := by
  classical
  funext v
  simp only [edgeDivergence_apply]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : p e
  · simp only [edgeSwapTail_apply, edgeSwapHead_apply, h, ↓reduceIte,
      TauCeti.piSignChange_apply, neg_div]
    split_ifs <;> abel
  · simp [h]

/-- Reversing selected edges negates exactly their differential values. -/
theorem edgeDifferential_reverseOn {A : Type w} [AddCommGroup A]
    (o : G.Orientation) (p : G.edgeSet → Prop) [DecidablePred p]
    (f : G.vertexSet → A) (e : G.edgeSet) :
    edgeDifferential (o.reverseOn p).tail (o.reverseOn p).head f e =
      if p e then -edgeDifferential o.tail o.head f e else
        edgeDifferential o.tail o.head f e := by
  rw [o.reverseOn_tail_eq_edgeSwapTail, o.reverseOn_head_eq_edgeSwapHead]
  exact edgeDifferential_swap o.tail o.head p f e

/-- Selected-edge reversal intertwines the linear differential and coordinate sign change. -/
theorem edgeDifferentialLinear_reverseOn (R : Type*) [Semiring R] {A : Type w}
    [AddCommGroup A] [Module R A] (o : G.Orientation) (p : G.edgeSet → Prop)
    [DecidablePred p] :
    edgeDifferentialLinear R (A := A) (o.reverseOn p).tail (o.reverseOn p).head =
      (TauCeti.piSignChange R p).toLinearMap.comp (edgeDifferentialLinear R o.tail o.head) := by
  rw [o.reverseOn_tail_eq_edgeSwapTail, o.reverseOn_head_eq_edgeSwapHead]
  exact edgeDifferentialLinear_swap R o.tail o.head p

/-- Reversing selected edges and negating the same input coordinates preserves divergence. -/
theorem edgeDivergence_reverseOn (K : Type w) [DivisionRing K] [Fintype G.edgeSet]
    (o : G.Orientation) (length : G.edgeSet → ℚ) (p : G.edgeSet → Prop) [DecidablePred p]
    (c : G.edgeSet → K) :
    edgeDivergence K (o.reverseOn p).tail (o.reverseOn p).head length (TauCeti.piSignChange K p c) =
      edgeDivergence K o.tail o.head length c := by
  rw [o.reverseOn_tail_eq_edgeSwapTail, o.reverseOn_head_eq_edgeSwapHead]
  exact edgeDivergence_swap K o.tail o.head length p c

/-- The divergence reversal square as an equality of compositions of linear maps. -/
theorem edgeDivergence_reverseOn_comp (K : Type w) [DivisionRing K] [Fintype G.edgeSet]
    (o : G.Orientation) (length : G.edgeSet → ℚ) (p : G.edgeSet → Prop) [DecidablePred p] :
    (edgeDivergence K (o.reverseOn p).tail (o.reverseOn p).head length).comp
        (TauCeti.piSignChange K p).toLinearMap = edgeDivergence K o.tail o.head length := by
  ext c v
  exact congrFun (edgeDivergence_reverseOn K o length p c) v

end Graph
