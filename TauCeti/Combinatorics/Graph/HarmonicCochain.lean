/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Module.Rat
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.Combinatorics.Graph.Orientation.Cochains

/-!
# Harmonic and exact cochains on a metric multigraph

Fix a multigraph `G` and choose, for every actual edge, a tail and a head among the actual
vertices. The edge differential `Graph.edgeDifferential` and the weighted divergence
`Graph.edgeDivergence` for rational edge lengths `ℓ` are defined in
`TauCeti.Combinatorics.Graph.Orientation.Cochains`. A cochain is *harmonic* when its divergence
vanishes and *exact* when it is an edge differential.

The edge pairing `(c, d)_ℓ = ∑ₑ c e * d e / ℓ e` makes the differential and the divergence
adjoint, so the harmonic cochains are exactly the cochains orthogonal to the exact ones. The main
result is that, for positive lengths and coefficients in a field of characteristic zero, every
cochain is uniquely the sum of a harmonic and an exact cochain: the exact and harmonic cochains
are complementary subspaces. Over the rationals this follows from positivity of the pairing on a
nonzero exact cochain; over an arbitrary field of characteristic zero it is reduced to the
rational case by applying the `ℚ`-linear functionals of the field, which commute with both edge
maps because the lengths are rational. Consequently every class of cochains modulo exact cochains
has a unique harmonic representative, and the pairing restricted to harmonic cochains is
nondegenerate. The projection onto the harmonic part is `Graph.harmonicProjectionOnto`, in
`TauCeti.Combinatorics.Graph.Orientation.Harmonic`.

Loops, parallel edges, disconnected graphs and infinite vertex sets are allowed: only the actual
edge set is required to be finite. The two endpoint maps are arbitrary; for an orientation of `G`
(`Graph.Orientation`) one takes its `tail` and `head`, but the incidence relation of `G` is never
used, so no such hypothesis is imposed. Characteristic zero is essential: in characteristic `3`
the constant cyclic cochain on a triangle is both exact and harmonic, and positivity of the
lengths is essential, since lengths `1` and `-1` on two parallel edges make their nonzero exact
cochain `(1, 1)` harmonic.

## Main definitions

* `Graph.edgePairing`: the length-weighted pairing of two cochains.
* `Graph.harmonicCochains`: the harmonic cochains.

## Main results

* `Graph.sum_mul_edgeDivergence`: the differential and the divergence are adjoint.
* `Graph.orthogonal_exactCochains`: harmonic cochains are the orthogonal of the exact ones.
* `Graph.edgeDifferential_eq_zero_of_edgeDivergence_eq_zero`: a harmonic exact cochain is zero.
* `Graph.isCompl_harmonic_exact`: harmonic and exact cochains are complementary.
* `Graph.harmonic_exact_decomposition`: every cochain is uniquely harmonic plus exact.
* `Graph.nondegenerate_restrict_harmonicCochains`: the pairing is nondegenerate on harmonic
  cochains.

## References

* A. Besser, *p-adic heights and Vologodsky integration*, arXiv:1711.06957,
  Definitions 4.1–4.3 and Theorem 4.4.
* A. Besser and S. L. Zerbes, *Vologodsky integration on curves with semi-stable reduction*,
  arXiv:1711.06950, Corollary 1.2.
-/

public section

namespace Graph

variable {V E : Type*} {G : Graph V E}

/-! ### The edge differential -/

section Differential

variable (tail head : G.edgeSet → G.vertexSet) {M : Type*} [AddCommGroup M]

@[simp]
theorem edgeDifferential_neg (f : G.vertexSet → M) :
    edgeDifferential tail head (-f) = -edgeDifferential tail head f := by
  ext e
  simp [neg_add_eq_sub]

@[simp]
theorem edgeDifferential_sub (f g : G.vertexSet → M) :
    edgeDifferential tail head (f - g) =
      edgeDifferential tail head f - edgeDifferential tail head g := by
  ext e
  simp only [edgeDifferential_apply, Pi.sub_apply]
  abel

@[simp]
theorem edgeDifferential_smul {R : Type*} [Monoid R] [DistribMulAction R M] (r : R)
    (f : G.vertexSet → M) :
    edgeDifferential tail head (r • f) = r • edgeDifferential tail head f := by
  ext e
  simp [smul_sub]

/-- Reversing every chosen orientation negates the edge differential. -/
theorem edgeDifferential_head_tail (f : G.vertexSet → M) :
    edgeDifferential head tail f = -edgeDifferential tail head f := by
  ext e
  simp

end Differential

/-! ### Exact cochains -/

section Exact

variable (tail head : G.edgeSet → G.vertexSet) {k : Type*} [Ring k]

theorem edgeDifferential_mem_exactCochains (f : G.vertexSet → k) :
    edgeDifferential tail head f ∈ exactCochains k tail head :=
  (mem_exactCochains_iff k tail head _).2 ⟨f, rfl⟩

/-- Reversing every chosen orientation does not change the exact cochains. -/
theorem exactCochains_head_tail :
    exactCochains k (A := k) head tail = exactCochains k tail head := by
  ext c
  rw [mem_exactCochains_iff, mem_exactCochains_iff]
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨-f, by ext; simp [neg_add_eq_sub]⟩
  · rintro ⟨f, rfl⟩
    exact ⟨-f, by ext; simp [neg_add_eq_sub]⟩

/-- Exact cochains are carried to exact cochains by additive coefficient maps. -/
theorem comp_mem_exactCochains {k' F : Type*} [Ring k'] [FunLike F k k']
    [AddMonoidHomClass F k k'] (φ : F) {c : G.edgeSet → k} (hc : c ∈ exactCochains k tail head) :
    φ ∘ c ∈ exactCochains k' tail head := by
  obtain ⟨f, rfl⟩ := (mem_exactCochains_iff k tail head c).1 hc
  exact (mem_exactCochains_iff k' tail head _).2 ⟨φ ∘ f, edgeDifferential_map tail head φ f⟩

end Exact

/-! ### Harmonic cochains -/

/-- Cochains with zero weighted divergence. -/
noncomputable def harmonicCochains (K : Type*) [DivisionRing K] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ) :
    Submodule K (G.edgeSet → K) :=
  LinearMap.ker (edgeDivergence K tail head length)

/-- The space of harmonic cochains is the kernel of weighted divergence. -/
theorem harmonicCochains_eq_ker (K : Type*) [DivisionRing K] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ) :
    harmonicCochains K tail head length = LinearMap.ker (edgeDivergence K tail head length) := by
  rfl

@[simp]
theorem mem_harmonicCochains_iff (K : Type*) [DivisionRing K] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (c : G.edgeSet → K) :
    c ∈ harmonicCochains K tail head length ↔
      edgeDivergence K tail head length c = 0 := by
  rw [harmonicCochains_eq_ker, LinearMap.mem_ker]

/-! ### Weighted divergence and the edge pairing -/

section Divergence

variable (tail head : G.edgeSet → G.vertexSet) {k : Type*} [Field k] [Fintype G.edgeSet]
  (length : G.edgeSet → ℚ)

/-- Reversing every chosen orientation negates the weighted divergence. -/
theorem edgeDivergence_head_tail (c : G.edgeSet → k) :
    edgeDivergence k head tail length c = -edgeDivergence k tail head length c := by
  classical
  ext v
  simp [edgeDivergence_apply]

/-- The weighted divergence commutes with additive maps between coefficient fields of
characteristic zero, such as field embeddings and `ℚ`-linear functionals. -/
theorem edgeDivergence_comp [CharZero k] {k' F : Type*} [Field k'] [CharZero k'] [FunLike F k k']
    [AddMonoidHomClass F k k'] (φ : F) (c : G.edgeSet → k) :
    edgeDivergence k' tail head length (φ ∘ c) = φ ∘ edgeDivergence k tail head length c := by
  classical
  have hdiv (x : k) (q : ℚ) : φ (x / q) = φ x / q := by
    have h := map_ratCast_smul φ k k' q⁻¹ x
    rw [Rat.cast_inv, Rat.cast_inv, smul_eq_mul, smul_eq_mul] at h
    rwa [div_eq_inv_mul, div_eq_inv_mul]
  ext v
  simp [edgeDivergence_apply, map_sum, apply_ite φ, hdiv]

/-- The edge pairing `(c, d)_ℓ = ∑ₑ c e * d e / ℓ e` of two cochains, a symmetric bilinear form
given by the diagonal matrix of inverse lengths. -/
noncomputable def edgePairing : LinearMap.BilinForm k (G.edgeSet → k) := by
  classical
  exact Matrix.toBilin' (Matrix.diagonal fun e ↦ (length e : k)⁻¹)

theorem edgePairing_apply (c d : G.edgeSet → k) :
    edgePairing length c d = ∑ e, c e * d e / (length e : k) := by
  classical
  rw [edgePairing, Matrix.toBilin'_apply']
  simp only [dotProduct, Matrix.mulVec_diagonal]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  ring

/-- The edge pairing is symmetric. -/
theorem edgePairing_comm (c d : G.edgeSet → k) :
    edgePairing length c d = edgePairing length d c := by
  simp only [edgePairing_apply, mul_comm (c _)]

/-- The edge pairing is reflexive: orthogonality is a symmetric relation. -/
theorem edgePairing_isRefl : (edgePairing (k := k) length).IsRefl := fun c d h ↦ by
  rwa [edgePairing_comm]

/-- The edge pairing is nondegenerate when no length vanishes: its matrix is diagonal with
nonzero entries. -/
theorem edgePairing_nondegenerate [CharZero k] (hlen : ∀ e, length e ≠ 0) :
    (edgePairing (k := k) length).Nondegenerate := by
  classical
  rw [edgePairing, LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun e _ ↦ inv_ne_zero (Rat.cast_ne_zero.2 (hlen e))

/-- The adjunction between the edge differential and the weighted divergence, summing over any
finite set of vertices containing all endpoints: `∑ᵥ f v * div c v = (d f, c)_ℓ`. -/
theorem sum_mul_edgeDivergence_of_forall_mem (s : Finset G.vertexSet) (htail : ∀ e, tail e ∈ s)
    (hhead : ∀ e, head e ∈ s) (f : G.vertexSet → k) (c : G.edgeSet → k) :
    ∑ v ∈ s, f v * edgeDivergence k tail head length c v =
      edgePairing length (edgeDifferential tail head f) c := by
  classical
  simp only [edgeDivergence_apply, edgePairing_apply, edgeDifferential_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  simp only [mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq, htail,
    hhead, ite_true]
  ring

/-- The edge differential and the weighted divergence are adjoint for the edge pairing:
`∑ᵥ f v * div c v = (d f, c)_ℓ`. -/
theorem sum_mul_edgeDivergence [Fintype G.vertexSet] (f : G.vertexSet → k) (c : G.edgeSet → k) :
    ∑ v, f v * edgeDivergence k tail head length c v =
      edgePairing length (edgeDifferential tail head f) c :=
  sum_mul_edgeDivergence_of_forall_mem tail head length _ (fun _ ↦ Finset.mem_univ _)
    (fun _ ↦ Finset.mem_univ _) f c

/-- Pairing a cochain with the differential of the indicator of a vertex gives its divergence
there. -/
theorem edgePairing_edgeDifferential_single [DecidableEq G.vertexSet] (v : G.vertexSet)
    (c : G.edgeSet → k) :
    edgePairing length (edgeDifferential tail head (Pi.single v 1)) c =
      edgeDivergence k tail head length c v := by
  classical
  let s : Finset G.vertexSet := insert v (Finset.univ.image tail ∪ Finset.univ.image head)
  rw [← sum_mul_edgeDivergence_of_forall_mem tail head length s (by simp [s]) (by simp [s])]
  simp [Pi.single_apply, s]

/-- Reversing every chosen orientation does not change the harmonic cochains. -/
theorem harmonicCochains_head_tail :
    harmonicCochains k head tail length = harmonicCochains k tail head length := by
  ext c
  rw [mem_harmonicCochains_iff, mem_harmonicCochains_iff, edgeDivergence_head_tail, neg_eq_zero]

/-- Harmonic cochains are carried to harmonic cochains by additive maps between coefficient
fields of characteristic zero. -/
theorem comp_mem_harmonicCochains [CharZero k] {k' F : Type*} [Field k'] [CharZero k']
    [FunLike F k k'] [AddMonoidHomClass F k k'] (φ : F) {c : G.edgeSet → k}
    (hc : c ∈ harmonicCochains k tail head length) :
    φ ∘ c ∈ harmonicCochains k' tail head length := by
  rw [mem_harmonicCochains_iff] at hc ⊢
  rw [edgeDivergence_comp, hc]
  ext v
  simp

/-- The harmonic cochains are exactly the cochains orthogonal to all exact cochains for the edge
pairing. -/
theorem orthogonal_exactCochains :
    (edgePairing (k := k) length).orthogonal (exactCochains k tail head) =
      harmonicCochains k tail head length := by
  classical
  ext c
  simp only [LinearMap.BilinForm.mem_orthogonal_iff, mem_exactCochains_iff,
    mem_harmonicCochains_iff, forall_exists_index, forall_apply_eq_imp_iff]
  refine ⟨fun h ↦ funext fun v ↦ ?_, fun h f ↦ ?_⟩
  · rw [Pi.zero_apply, ← edgePairing_edgeDifferential_single]
    exact h _
  · rw [← sum_mul_edgeDivergence_of_forall_mem tail head length
      (Finset.univ.image tail ∪ Finset.univ.image head) (by simp) (by simp)]
    simp [h]

end Divergence

/-! ### The harmonic/exact decomposition -/

section Harmonic

variable (tail head : G.edgeSet → G.vertexSet) {k : Type*} [Field k] [CharZero k]
  [Fintype G.edgeSet] (length : G.edgeSet → ℚ)

/-- Over the rationals, a harmonic exact cochain vanishes, by positivity of the edge pairing. -/
private theorem edgeDifferential_eq_zero_of_edgeDivergence_eq_zero_rat
    (hpos : ∀ e, 0 < length e) (f : G.vertexSet → ℚ)
    (h : edgeDifferential tail head f ∈ harmonicCochains ℚ tail head length) :
    edgeDifferential tail head f = 0 := by
  rw [← orthogonal_exactCochains] at h
  have hzero := h _ (edgeDifferential_mem_exactCochains tail head f)
  rw [edgePairing_apply] at hzero
  simp only [Rat.cast_id] at hzero
  have hnonneg (e : G.edgeSet) (_ : e ∈ Finset.univ) :
      0 ≤ edgeDifferential tail head f e * edgeDifferential tail head f e / length e :=
    div_nonneg (mul_self_nonneg _) (hpos e).le
  ext e
  have he := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hzero e (Finset.mem_univ e)
  rw [div_eq_zero_iff, mul_self_eq_zero] at he
  exact he.resolve_right (hpos e).ne'

/-- A harmonic exact cochain vanishes: if the weighted divergence of `d f` is zero, then
`d f = 0`. -/
theorem edgeDifferential_eq_zero_of_edgeDivergence_eq_zero (hpos : ∀ e, 0 < length e)
    (f : G.vertexSet → k)
    (h : edgeDivergence k tail head length (edgeDifferential tail head f) = 0) :
    edgeDifferential tail head f = 0 := by
  ext e
  refine (Module.forall_dual_apply_eq_zero_iff ℚ _).1 fun φ ↦ ?_
  have hφ := edgeDifferential_eq_zero_of_edgeDivergence_eq_zero_rat tail head length hpos (φ ∘ f)
    (by
      rw [edgeDifferential_map]
      exact comp_mem_harmonicCochains tail head length φ
        ((mem_harmonicCochains_iff k tail head length _).2 h))
  simpa using congrFun hφ e

/-- The only cochain that is both harmonic and exact is zero. -/
theorem disjoint_harmonicCochains_exactCochains (hpos : ∀ e, 0 < length e) :
    Disjoint (harmonicCochains k tail head length) (exactCochains k tail head) := by
  rw [Submodule.disjoint_def]
  intro c hc hex
  obtain ⟨f, rfl⟩ := (mem_exactCochains_iff k tail head c).1 hex
  exact edgeDifferential_eq_zero_of_edgeDivergence_eq_zero tail head length hpos f
    ((mem_harmonicCochains_iff k tail head length _).1 hc)

end Harmonic

/-- For finitely many actual edges, positive rational edge lengths, and a characteristic-zero
coefficient field, the harmonic and exact subspaces are complementary. The endpoint maps may be
arbitrary, and the vertex set may be infinite. -/
theorem isCompl_harmonic_exact (K : Type*) [Field K] [CharZero K] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) :
    IsCompl (harmonicCochains K tail head length) (exactCochains K tail head) := by
  have h := (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint
    (W := exactCochains K tail head) (edgePairing_isRefl (k := K) length)).2
  rw [orthogonal_exactCochains] at h
  exact (h (disjoint_harmonicCochains_exactCochains tail head length hpos).symm).symm

/-- Every cochain on a multigraph with finitely many actual edges and positive rational lengths,
with coefficients in a field of characteristic zero, is uniquely the sum of a harmonic cochain
and an exact cochain. Loops, parallel edges, disconnected graphs and infinite vertex sets are
allowed, and the endpoint maps need not be compatible with the incidence of `G`. Uniqueness is
of the two cochains, not of a potential for the exact part. -/
theorem harmonic_exact_decomposition (K : Type*) [Field K] [CharZero K] [Fintype G.edgeSet]
    (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ) (hpos : ∀ e, 0 < length e)
    (c : G.edgeSet → K) :
    ∃! p : (G.edgeSet → K) × (G.edgeSet → K),
      edgeDivergence K tail head length p.1 = 0 ∧
      (∃ f, edgeDifferential tail head f = p.2) ∧ p.1 + p.2 = c := by
  have hc := isCompl_harmonic_exact K tail head length hpos
  obtain ⟨p, hp, huniq⟩ := Submodule.existsUnique_add_of_isCompl_prod hc c
  have hH := mem_harmonicCochains_iff K tail head length
  have hE := mem_exactCochains_iff K tail head (A := K)
  refine ⟨⟨p.1, p.2⟩, ⟨(hH _).1 p.1.property, (hE _).1 p.2.property, hp⟩, ?_⟩
  rintro ⟨h, r⟩ ⟨hh, hr, hsum⟩
  have heq := huniq (⟨⟨h, (hH h).2 hh⟩, ⟨r, (hE r).2 hr⟩⟩) hsum
  exact congrArg (fun q ↦ ((q.1 : G.edgeSet → K), (q.2 : G.edgeSet → K))) heq

/-- The edge pairing restricted to harmonic cochains is nondegenerate. -/
theorem nondegenerate_restrict_harmonicCochains {k : Type*} [Field k] [CharZero k]
    [Fintype G.edgeSet] (tail head : G.edgeSet → G.vertexSet) (length : G.edgeSet → ℚ)
    (hpos : ∀ e, 0 < length e) :
    ((edgePairing length).restrict (harmonicCochains k tail head length)).Nondegenerate := by
  rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal
    (edgePairing_isRefl length), ← orthogonal_exactCochains,
    LinearMap.BilinForm.orthogonal_orthogonal
      (edgePairing_nondegenerate length fun e ↦ (hpos e).ne') (edgePairing_isRefl length),
    orthogonal_exactCochains]
  exact isCompl_harmonic_exact k tail head length hpos

end Graph
