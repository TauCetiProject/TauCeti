/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Harmonic and exact cochains on a metric multigraph

Fix a multigraph `G` and choose, for every actual edge, a tail and a head among the actual
vertices. A one-cochain is a function on the actual edges; its value on the reverse flag of an
edge is understood to be the negative value. The *edge differential* of a vertex
function `f` is the cochain `e ↦ f (tail e) - f (head e)`. Given positive rational edge lengths
`ℓ`, the *weighted divergence* of a cochain `c` with coefficients in a field of characteristic
zero is the vertex function whose value at `v` is the sum of `c e / ℓ e` over the edges with
tail `v` minus the same sum over the edges with head `v`. An edge whose chosen tail and head
coincide contributes both terms, which cancel; this is the case for loops when the endpoint maps
come from a `Graph.Orientation`. A cochain is *harmonic* when its divergence vanishes and *exact*
when it is an edge differential.

The edge pairing `(c, d)_ℓ = ∑ₑ c e * d e / ℓ e` makes the differential and the divergence
adjoint, so the harmonic cochains are exactly the cochains orthogonal to the exact ones. The main
result is that every cochain is uniquely the sum of a harmonic and an exact cochain: the exact
and harmonic cochains are complementary subspaces. Over the rationals this follows from
positivity of the pairing on a nonzero exact cochain; over an arbitrary field of characteristic
zero it is reduced to the rational case by applying the `ℚ`-linear functionals of the field,
which commute with both edge maps because the lengths are rational. Consequently every class of
cochains modulo exact cochains has a unique harmonic representative, and the pairing restricted
to harmonic cochains is nondegenerate. The projection onto the harmonic part is
`Submodule.projectionOnto` of `Graph.isCompl_harmonicCochains_exactCochains`.

Loops, parallel edges, disconnected graphs and infinite vertex sets are allowed: only the actual
edge set is required to be finite. The two endpoint maps are arbitrary; for an orientation of `G`
(`Graph.Orientation`) one takes its `tail` and `head`, but the incidence relation of `G` is never
used, so no such hypothesis is imposed. Characteristic zero is essential: in characteristic `3`
the constant cyclic cochain on a triangle is both exact and harmonic, and positivity of the
lengths is essential, since lengths `1` and `-1` on two parallel edges make their nonzero exact
cochain `(1, 1)` harmonic.

## Main definitions

* `Graph.edgeDifferential`: the cochain `e ↦ f (tail e) - f (head e)` of a vertex function.
* `Graph.edgeDivergence`: the weighted divergence of a cochain.
* `Graph.edgePairing`: the length-weighted pairing of two cochains.
* `Graph.exactCochains`, `Graph.harmonicCochains`: the exact and harmonic cochains.

## Main results

* `Graph.sum_mul_edgeDivergence`: the differential and the divergence are adjoint.
* `Graph.orthogonal_exactCochains`: harmonic cochains are the orthogonal of the exact ones.
* `Graph.edgeDifferential_eq_zero_of_edgeDivergence_eq_zero`: a harmonic exact cochain is zero.
* `Graph.isCompl_harmonicCochains_exactCochains`: harmonic and exact cochains are complementary.
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

variable {V E : Type*} (G : Graph V E) (tail head : G.edgeSet → G.vertexSet)

/-! ### The edge differential -/

section Differential

variable {M : Type*} [AddCommGroup M]

/-- The edge differential of a vertex function `f`: its value on an actual edge is the value of
`f` at the chosen tail minus its value at the chosen head. The reverse flag of the edge carries
the negative value; on an edge whose chosen tail and head coincide the differential vanishes. -/
def edgeDifferential (f : G.vertexSet → M) : G.edgeSet → M :=
  fun e ↦ f (tail e) - f (head e)

@[simp]
theorem edgeDifferential_apply (f : G.vertexSet → M) (e : G.edgeSet) :
    G.edgeDifferential tail head f e = f (tail e) - f (head e) :=
  (rfl)

@[simp]
theorem edgeDifferential_zero : G.edgeDifferential tail head (0 : G.vertexSet → M) = 0 := by
  ext e
  simp

@[simp]
theorem edgeDifferential_add (f g : G.vertexSet → M) :
    G.edgeDifferential tail head (f + g) =
      G.edgeDifferential tail head f + G.edgeDifferential tail head g := by
  ext e
  simp only [edgeDifferential_apply, Pi.add_apply]
  abel

@[simp]
theorem edgeDifferential_neg (f : G.vertexSet → M) :
    G.edgeDifferential tail head (-f) = -G.edgeDifferential tail head f := by
  ext e
  simp [neg_add_eq_sub]

@[simp]
theorem edgeDifferential_sub (f g : G.vertexSet → M) :
    G.edgeDifferential tail head (f - g) =
      G.edgeDifferential tail head f - G.edgeDifferential tail head g := by
  ext e
  simp only [edgeDifferential_apply, Pi.sub_apply]
  abel

@[simp]
theorem edgeDifferential_smul {R : Type*} [Monoid R] [DistribMulAction R M] (r : R)
    (f : G.vertexSet → M) :
    G.edgeDifferential tail head (r • f) = r • G.edgeDifferential tail head f := by
  ext e
  simp [smul_sub]

/-- Reversing every chosen orientation negates the edge differential. -/
theorem edgeDifferential_swap (f : G.vertexSet → M) :
    G.edgeDifferential head tail f = -G.edgeDifferential tail head f := by
  ext e
  simp

/-- The edge differential commutes with additive coefficient maps. -/
theorem edgeDifferential_comp {N F : Type*} [AddCommGroup N] [FunLike F M N]
    [AddMonoidHomClass F M N] (φ : F) (f : G.vertexSet → M) :
    G.edgeDifferential tail head (φ ∘ f) = φ ∘ G.edgeDifferential tail head f := by
  ext e
  simp

/-- The edge differential as a linear map, over any ring of scalars acting on the
coefficients. -/
def edgeDifferentialLinearMap (R : Type*) [Semiring R] [Module R M] :
    (G.vertexSet → M) →ₗ[R] G.edgeSet → M where
  toFun := G.edgeDifferential tail head
  map_add' := G.edgeDifferential_add tail head
  map_smul' := G.edgeDifferential_smul tail head

@[simp]
theorem coe_edgeDifferentialLinearMap (R : Type*) [Semiring R] [Module R M] :
    ⇑(G.edgeDifferentialLinearMap (M := M) tail head R) = G.edgeDifferential tail head :=
  (rfl)

end Differential

/-! ### Exact cochains -/

section Exact

variable {k : Type*} [Ring k]

/-- The exact cochains: the edge differentials of vertex functions. -/
def exactCochains : Submodule k (G.edgeSet → k) :=
  LinearMap.range (G.edgeDifferentialLinearMap tail head k)

@[simp]
theorem mem_exactCochains_iff {c : G.edgeSet → k} :
    c ∈ G.exactCochains tail head ↔ ∃ f, G.edgeDifferential tail head f = c :=
  Iff.rfl

theorem edgeDifferential_mem_exactCochains (f : G.vertexSet → k) :
    G.edgeDifferential tail head f ∈ G.exactCochains tail head :=
  ⟨f, rfl⟩

/-- Reversing every chosen orientation does not change the exact cochains. -/
theorem exactCochains_swap : G.exactCochains (k := k) head tail = G.exactCochains tail head := by
  ext c
  rw [mem_exactCochains_iff, mem_exactCochains_iff]
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨-f, by ext; simp [neg_add_eq_sub]⟩
  · rintro ⟨f, rfl⟩
    exact ⟨-f, by ext; simp [neg_add_eq_sub]⟩

/-- Exact cochains are carried to exact cochains by additive coefficient maps. -/
theorem comp_mem_exactCochains {k' F : Type*} [Ring k'] [FunLike F k k']
    [AddMonoidHomClass F k k'] (φ : F) {c : G.edgeSet → k} (hc : c ∈ G.exactCochains tail head) :
    φ ∘ c ∈ G.exactCochains tail head := by
  obtain ⟨f, rfl⟩ := hc
  exact ⟨φ ∘ f, G.edgeDifferential_comp tail head φ f⟩

end Exact

/-! ### Weighted divergence and the edge pairing -/

section Divergence

variable {k : Type*} [Field k] [Fintype G.edgeSet]
  (length : G.edgeSet → {q : ℚ // 0 < q})

/-- The weighted divergence of a cochain `c` at a vertex `v`: the sum of `c e / ℓ e` over the
actual edges with tail `v`, minus the same sum over the actual edges with head `v`. An edge whose
chosen tail and head are both `v` contributes both terms, which cancel. -/
noncomputable def edgeDivergence (c : G.edgeSet → k) (v : G.vertexSet) : k := by
  classical
  exact ∑ e : G.edgeSet,
    ((if tail e = v then c e / (length e : ℚ) else 0) -
      (if head e = v then c e / (length e : ℚ) else 0))

theorem edgeDivergence_apply [DecidableEq G.vertexSet] (c : G.edgeSet → k) (v : G.vertexSet) :
    G.edgeDivergence tail head length c v = ∑ e : G.edgeSet,
      ((if tail e = v then c e / (length e : ℚ) else 0) -
        (if head e = v then c e / (length e : ℚ) else 0)) := by
  rw [edgeDivergence]
  congr!

/-- Reversing every chosen orientation negates the weighted divergence. -/
theorem edgeDivergence_swap (c : G.edgeSet → k) :
    G.edgeDivergence head tail length c = -G.edgeDivergence tail head length c := by
  classical
  ext v
  simp [edgeDivergence_apply]

/-- The weighted divergence commutes with additive maps between coefficient fields of
characteristic zero, such as field embeddings and `ℚ`-linear functionals. -/
theorem edgeDivergence_comp [CharZero k] {k' F : Type*} [Field k'] [CharZero k'] [FunLike F k k']
    [AddMonoidHomClass F k k'] (φ : F) (c : G.edgeSet → k) :
    G.edgeDivergence tail head length (φ ∘ c) = φ ∘ G.edgeDivergence tail head length c := by
  classical
  have hdiv (x : k) (q : ℚ) : φ (x / q) = φ x / q := by
    have h := map_ratCast_smul φ k k' q⁻¹ x
    rw [Rat.cast_inv, Rat.cast_inv, smul_eq_mul, smul_eq_mul] at h
    rwa [div_eq_inv_mul, div_eq_inv_mul]
  ext v
  simp [edgeDivergence_apply, map_sum, apply_ite φ, hdiv]

/-- The weighted divergence as a linear map. -/
noncomputable def edgeDivergenceLinearMap : (G.edgeSet → k) →ₗ[k] G.vertexSet → k where
  toFun := G.edgeDivergence tail head length
  map_add' c d := by
    classical
    ext v
    simp only [edgeDivergence_apply, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    split_ifs <;> ring
  map_smul' a c := by
    classical
    ext v
    simp only [edgeDivergence_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    split_ifs <;> ring

@[simp]
theorem coe_edgeDivergenceLinearMap :
    ⇑(G.edgeDivergenceLinearMap tail head length) = G.edgeDivergence (k := k) tail head length :=
  (rfl)

@[simp]
theorem edgeDivergence_zero : G.edgeDivergence tail head length (0 : G.edgeSet → k) = 0 :=
  map_zero (G.edgeDivergenceLinearMap tail head length)

@[simp]
theorem edgeDivergence_add (c d : G.edgeSet → k) :
    G.edgeDivergence tail head length (c + d) =
      G.edgeDivergence tail head length c + G.edgeDivergence tail head length d :=
  map_add (G.edgeDivergenceLinearMap tail head length) c d

@[simp]
theorem edgeDivergence_neg (c : G.edgeSet → k) :
    G.edgeDivergence tail head length (-c) = -G.edgeDivergence tail head length c :=
  map_neg (G.edgeDivergenceLinearMap tail head length) c

@[simp]
theorem edgeDivergence_sub (c d : G.edgeSet → k) :
    G.edgeDivergence tail head length (c - d) =
      G.edgeDivergence tail head length c - G.edgeDivergence tail head length d :=
  map_sub (G.edgeDivergenceLinearMap tail head length) c d

@[simp]
theorem edgeDivergence_smul (a : k) (c : G.edgeSet → k) :
    G.edgeDivergence tail head length (a • c) = a • G.edgeDivergence tail head length c :=
  map_smul (G.edgeDivergenceLinearMap tail head length) a c

/-- The edge pairing `(c, d)_ℓ = ∑ₑ c e * d e / ℓ e` of two cochains, a symmetric bilinear form
given by the diagonal matrix of inverse lengths. -/
noncomputable def edgePairing : LinearMap.BilinForm k (G.edgeSet → k) := by
  classical
  exact Matrix.toBilin' (Matrix.diagonal fun e ↦ ((length e : ℚ) : k)⁻¹)

theorem edgePairing_apply (c d : G.edgeSet → k) :
    G.edgePairing length c d = ∑ e, c e * d e / (length e : ℚ) := by
  classical
  rw [edgePairing, Matrix.toBilin'_apply']
  simp only [dotProduct, Matrix.mulVec_diagonal]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  ring

/-- The edge pairing is symmetric. -/
theorem edgePairing_comm (c d : G.edgeSet → k) :
    G.edgePairing length c d = G.edgePairing length d c := by
  simp only [edgePairing_apply, mul_comm (c _)]

/-- The edge pairing is reflexive: orthogonality is a symmetric relation. -/
theorem edgePairing_isRefl : (G.edgePairing (k := k) length).IsRefl := fun c d h ↦ by
  rwa [edgePairing_comm]

/-- The edge pairing is nondegenerate: its matrix is diagonal with nonzero entries. -/
theorem edgePairing_nondegenerate [CharZero k] :
    (G.edgePairing (k := k) length).Nondegenerate := by
  classical
  rw [edgePairing, LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun e _ ↦ inv_ne_zero (Rat.cast_ne_zero.2 (length e).property.ne')

/-- The adjunction between the edge differential and the weighted divergence, summing over any
finite set of vertices containing all endpoints: `∑ᵥ f v * div c v = (d f, c)_ℓ`. -/
theorem sum_mul_edgeDivergence_of_forall_mem (s : Finset G.vertexSet) (htail : ∀ e, tail e ∈ s)
    (hhead : ∀ e, head e ∈ s) (f : G.vertexSet → k) (c : G.edgeSet → k) :
    ∑ v ∈ s, f v * G.edgeDivergence tail head length c v =
      G.edgePairing length (G.edgeDifferential tail head f) c := by
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
    ∑ v, f v * G.edgeDivergence tail head length c v =
      G.edgePairing length (G.edgeDifferential tail head f) c :=
  G.sum_mul_edgeDivergence_of_forall_mem tail head length _ (fun _ ↦ Finset.mem_univ _)
    (fun _ ↦ Finset.mem_univ _) f c

/-- Pairing a cochain with the differential of the indicator of a vertex gives its divergence
there. -/
theorem edgePairing_edgeDifferential_single [DecidableEq G.vertexSet] (v : G.vertexSet)
    (c : G.edgeSet → k) :
    G.edgePairing length (G.edgeDifferential tail head (Pi.single v 1)) c =
      G.edgeDivergence tail head length c v := by
  classical
  let s : Finset G.vertexSet := insert v (Finset.univ.image tail ∪ Finset.univ.image head)
  rw [← G.sum_mul_edgeDivergence_of_forall_mem tail head length s (by simp [s])
    (by simp [s])]
  simp [Pi.single_apply, s]

/-! ### Harmonic cochains -/

/-- The harmonic cochains: the cochains of vanishing weighted divergence. -/
noncomputable def harmonicCochains : Submodule k (G.edgeSet → k) :=
  LinearMap.ker (G.edgeDivergenceLinearMap tail head length)

@[simp]
theorem mem_harmonicCochains_iff {c : G.edgeSet → k} :
    c ∈ G.harmonicCochains tail head length ↔ ∀ v, G.edgeDivergence tail head length c v = 0 := by
  simp [harmonicCochains, funext_iff]

/-- Reversing every chosen orientation does not change the harmonic cochains. -/
theorem harmonicCochains_swap :
    G.harmonicCochains (k := k) head tail length = G.harmonicCochains tail head length := by
  ext c
  rw [mem_harmonicCochains_iff, mem_harmonicCochains_iff, edgeDivergence_swap]
  simp

/-- Harmonic cochains are carried to harmonic cochains by additive maps between coefficient
fields of characteristic zero. -/
theorem comp_mem_harmonicCochains [CharZero k] {k' F : Type*} [Field k'] [CharZero k']
    [FunLike F k k'] [AddMonoidHomClass F k k'] (φ : F) {c : G.edgeSet → k}
    (hc : c ∈ G.harmonicCochains tail head length) :
    φ ∘ c ∈ G.harmonicCochains tail head length := by
  rw [G.mem_harmonicCochains_iff tail head length] at hc ⊢
  intro v
  rw [edgeDivergence_comp, Function.comp_apply, hc, map_zero]

/-- The harmonic cochains are exactly the cochains orthogonal to all exact cochains for the edge
pairing. -/
theorem orthogonal_exactCochains :
    (G.edgePairing (k := k) length).orthogonal (G.exactCochains tail head) =
      G.harmonicCochains tail head length := by
  classical
  ext c
  simp only [LinearMap.BilinForm.mem_orthogonal_iff, mem_exactCochains_iff,
    mem_harmonicCochains_iff, forall_exists_index, forall_apply_eq_imp_iff]
  refine ⟨fun h v ↦ ?_, fun h f ↦ ?_⟩
  · rw [← edgePairing_edgeDifferential_single]
    exact h _
  · rw [← G.sum_mul_edgeDivergence_of_forall_mem tail head length
      (Finset.univ.image tail ∪ Finset.univ.image head) (by simp) (by simp)]
    simp [h]

end Divergence

/-! ### The harmonic/exact decomposition -/

section Harmonic

variable {k : Type*} [Field k] [CharZero k] [Fintype G.edgeSet]
  (length : G.edgeSet → {q : ℚ // 0 < q})

/-- Over the rationals, a harmonic exact cochain vanishes, by positivity of the edge pairing. -/
private theorem edgeDifferential_eq_zero_of_edgeDivergence_eq_zero_rat (f : G.vertexSet → ℚ)
    (h : G.edgeDifferential tail head f ∈ G.harmonicCochains tail head length) :
    G.edgeDifferential tail head f = 0 := by
  rw [← orthogonal_exactCochains] at h
  have hzero := h _ (G.edgeDifferential_mem_exactCochains tail head f)
  rw [edgePairing_apply] at hzero
  have hnonneg (e : G.edgeSet) (_ : e ∈ Finset.univ) :
      0 ≤ G.edgeDifferential tail head f e * G.edgeDifferential tail head f e /
        ((length e : ℚ) : ℚ) :=
    div_nonneg (mul_self_nonneg _) (by simpa using (length e).property.le)
  ext e
  have he := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hzero e (Finset.mem_univ e)
  rw [div_eq_zero_iff, mul_self_eq_zero] at he
  exact he.resolve_right (by simpa using (length e).property.ne')

/-- A harmonic exact cochain vanishes: if the weighted divergence of `d f` is zero, then
`d f = 0`. -/
theorem edgeDifferential_eq_zero_of_edgeDivergence_eq_zero (f : G.vertexSet → k)
    (h : ∀ v, G.edgeDivergence tail head length (G.edgeDifferential tail head f) v = 0) :
    G.edgeDifferential tail head f = 0 := by
  ext e
  refine (Module.forall_dual_apply_eq_zero_iff ℚ _).1 fun φ ↦ ?_
  have hφ := G.edgeDifferential_eq_zero_of_edgeDivergence_eq_zero_rat tail head length (φ ∘ f)
    (by
      rw [edgeDifferential_comp]
      exact G.comp_mem_harmonicCochains tail head length φ
        ((G.mem_harmonicCochains_iff tail head length).2 h))
  simpa [edgeDifferential_comp] using congrFun hφ e

/-- The only cochain that is both harmonic and exact is zero. -/
theorem disjoint_harmonicCochains_exactCochains :
    Disjoint (G.harmonicCochains (k := k) tail head length) (G.exactCochains tail head) := by
  rw [Submodule.disjoint_def]
  rintro c hc ⟨f, rfl⟩
  exact G.edgeDifferential_eq_zero_of_edgeDivergence_eq_zero tail head length f
    ((G.mem_harmonicCochains_iff tail head length).1 hc)

/-- The harmonic and the exact cochains are complementary subspaces. -/
theorem isCompl_harmonicCochains_exactCochains :
    IsCompl (G.harmonicCochains (k := k) tail head length) (G.exactCochains tail head) := by
  have h := (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint
    (W := G.exactCochains tail head) (G.edgePairing_isRefl (k := k) length)).2
  rw [orthogonal_exactCochains] at h
  exact (h (G.disjoint_harmonicCochains_exactCochains tail head length).symm).symm

/-- Every cochain on a multigraph with finitely many actual edges and positive rational lengths,
with coefficients in a field of characteristic zero, is uniquely the sum of a harmonic cochain
and an exact cochain. Loops, parallel edges, disconnected graphs and infinite vertex sets are
allowed, and the endpoint maps need not be compatible with the incidence of `G`. Uniqueness is
of the two cochains, not of a potential for the exact part. -/
theorem harmonic_exact_decomposition (c : G.edgeSet → k) :
    ∃! hr : (G.edgeSet → k) × (G.edgeSet → k),
      (∀ v, G.edgeDivergence tail head length hr.1 v = 0) ∧
      (∃ f : G.vertexSet → k, hr.2 = G.edgeDifferential tail head f) ∧
      c = hr.1 + hr.2 := by
  obtain ⟨h, r, hsum, huniq⟩ := Submodule.existsUnique_add_of_isCompl
    (G.isCompl_harmonicCochains_exactCochains (k := k) tail head length) c
  obtain ⟨f, hf⟩ := r.property
  refine ⟨(h, r), ⟨(G.mem_harmonicCochains_iff tail head length).1 h.property, ⟨f, hf.symm⟩,
    hsum.symm⟩, ?_⟩
  rintro ⟨h', r'⟩ ⟨hh', ⟨f', rfl⟩, hc⟩
  obtain ⟨rfl, rfl⟩ := huniq ⟨h', (G.mem_harmonicCochains_iff tail head length).2 hh'⟩
    ⟨_, G.edgeDifferential_mem_exactCochains tail head f'⟩ hc.symm
  rfl

/-- The edge pairing restricted to harmonic cochains is nondegenerate. -/
theorem nondegenerate_restrict_harmonicCochains :
    ((G.edgePairing length).restrict
      (G.harmonicCochains (k := k) tail head length)).Nondegenerate := by
  rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal
    (G.edgePairing_isRefl length), ← orthogonal_exactCochains,
    LinearMap.BilinForm.orthogonal_orthogonal (G.edgePairing_nondegenerate length)
      (G.edgePairing_isRefl length), orthogonal_exactCochains]
  exact (G.isCompl_harmonicCochains_exactCochains tail head length)

end Harmonic

end Graph
