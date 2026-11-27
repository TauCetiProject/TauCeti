/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Star
public import TauCeti.Algebra.TemperleyLieb.Trace.Basic
public import TauCeti.Combinatorics.SimpleGraph.WalkFrom
public import TauCeti.RingTheory.TraceFunctional.Radical
public import TauCeti.LinearAlgebra.Matrix.ExtendLast
public import TauCeti.LinearAlgebra.Matrix.Trace.Positive
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Field
import TauCeti.Data.Fintype.BigOperators

/-!
# Path models of the Temperley–Lieb algebras

Let `G` be a finite simple graph with a base vertex `v₀`, and let `r` be a weighting of its
vertices by nonzero scalars whose squares satisfy the adjacency eigenvector equation with
eigenvalue `δ`: the squared weights of the neighbours of `v` add up to `δ * r v ^ 2`. When this
holds at every vertex, this file builds a representation of the Temperley–Lieb tower with loop
value `δ` on walks in `G` starting at `v₀`, together with a Markov trace, and proves that the trace
is positive when the weights are self-adjoint. More generally, on `n` strands the generator
relations and Markov trace axioms up to `n` strands only inspect the eigenvector equation at
endpoints of walks from `v₀` of fewer than `n` steps
(`TauCeti.TemperleyLieb.IsPathEigenvectorUpTo`). Combined with bounded uniqueness
(`TauCeti.TemperleyLieb.IsMarkovTraceUpTo.unique`), this proves positivity on `n` strands of every
global Markov trace whenever a finite graph carries positive weights satisfying the recurrence up to
depth `n`—even at loop parameters where no finite graph carries a global positive eigenvector; see
`TauCeti.Algebra.TemperleyLieb.Positivity`.

The algebra on `n` strands acts on functions of vertex sequences `s : Fin (n + 1) → V`, among
which the walks from `v₀` (`SimpleGraph.IsWalkFrom`) are the states of the model. The
generator `e i` acts on the vertex at position `b = i + 1`, between the positions `a = i` and
`c = i + 2`: on a walk `s` with `s a = s c` it is the rank-one matrix
`(r (s a) ^ 2)⁻¹ • w wᵀ` on the vertex at `b`, where `w` is the vector of weights `r x` of the
neighbours `x` of `s a`, and it vanishes on the other rows
(`TauCeti.TemperleyLieb.pathGenerator`). Since `a < n`, `s a` is the endpoint of a prefix walk of
fewer than `n` steps, so the quadratic relation is the bounded eigenvector equation
`wᵀ w = δ * r (s a) ^ 2`; the zigzag relations hold because the walk returns to the vertex it
left; and generators at distant positions move independent vertices. Every generator preserves
the walks and their endpoints, and on rows of walks adding a straight strand acts as
`Matrix.extendLast`.

The trace (`TauCeti.TemperleyLieb.pathTrace`) is the matrix trace weighted by
`(r v / r v₀) ^ 2` on the walks ending at `v`. Extending walks of fewer than `n` steps by one step
multiplies the total weight by `δ`, which gives the normalization and the strand inclusion
compatibility up to `n` strands; capping the last step with the previous one forces the walk to
return to its penultimate vertex, which gives the Markov property. For self-adjoint weights the
generator matrices are self-adjoint, so the representation carries the analytic adjoint to the
conjugate transpose, and the trace of `x⋆ * x` is a sum of absolute squares with nonnegative
weights.

The functions supported on the walks form an invariant subspace, and the restriction of the
representation to it (`TauCeti.TemperleyLieb.walkRep`) carries the trace as a weighted matrix trace
whose weights `(r v / r v₀) ^ 2` are nonzero. For self-adjoint weights the image of this
restriction is closed under the conjugate transpose, and over an ordered star field the weighted
trace is faithful on squares: the trace of `x * y`, for `y` acting by the conjugate transpose of
`walkRep x`, vanishes only when `walkRep x` does. So the kernel of the representation on walks is
exactly the trace radical; by `Ideal.kerLiftAlg`, the quotient of the Temperley–Lieb algebra by the
trace radical of the Markov trace is then isomorphic to the image of the path representation on
walks.

## Main definitions

* `TauCeti.TemperleyLieb.IsPathEigenvectorUpTo`: the squared weights satisfy the adjacency
  eigenvector equation with eigenvalue `δ` at endpoints of walks from `v₀` of fewer than `n` steps.
* `TauCeti.TemperleyLieb.pathGenerator`: the matrix of a generator in the path model.
* `TauCeti.TemperleyLieb.pathRep`: the path representation of the Temperley–Lieb algebra.
* `TauCeti.TemperleyLieb.pathWeight`: the weight of a vertex sequence in the trace.
* `TauCeti.TemperleyLieb.pathTrace`: the trace of the path model.
* `TauCeti.TemperleyLieb.walkRep`: the path representation restricted to the walks from `v₀`.

## Main results

* `TauCeti.TemperleyLieb.pathRep_apply_eq_zero`: the path representation preserves walks and
  their endpoints.
* `TauCeti.TemperleyLieb.pathRep_strandIncl_apply`: on rows of walks, adding a straight strand
  acts by `Matrix.extendLast`.
* `TauCeti.TemperleyLieb.isMarkovTraceUpTo_pathTrace`,
  `TauCeti.TemperleyLieb.isMarkovTrace_pathTrace`: the trace of the path model is a Markov trace up
  to `n` strands (and on the full tower under a global eigenvector).
* `TauCeti.TemperleyLieb.pathRep_star`: for self-adjoint weights, the path representation carries
  the analytic adjoint to the conjugate transpose.
* `TauCeti.TemperleyLieb.pathTrace_star_mul_self_nonneg`: for self-adjoint weights, the trace of
  `x⋆ * x` is nonnegative.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_of_isPathEigenvectorUpTo`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_of_graph`: positivity of every
  Markov trace on `n` strands from a bounded-depth or global path model.
* `TauCeti.TemperleyLieb.walkRep_strandIncl_apply`,
  `TauCeti.TemperleyLieb.walkRep_e_last_apply_snoc_snoc`: on walks, adding a strand extends walks
  by one step, and the last generator mixes the penultimate vertex of walks turning back.
* `TauCeti.TemperleyLieb.conjTranspose_mem_range_walkRep`: for self-adjoint weights, the image of
  the path representation on walks is closed under the conjugate transpose.
* `TauCeti.TemperleyLieb.ker_walkRep`, `TauCeti.TemperleyLieb.IsMarkovTrace.ker_walkRep`: for
  nonzero self-adjoint weights over an ordered star field, the kernel of the path representation
  on walks is the trace radical, of the path-model trace and hence of every Markov trace.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989 (path algebras of graphs and their Temperley–Lieb
  representations).
* H. Wenzl, *Hecke algebras of type `A_n` and subfactors*, Invent. Math. 92 (1988), 349–383.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, §§4.4–4.5 (the tree basis
  and the paths on `A_(m-1)`).
-/

public section

open Function Matrix
open SimpleGraph (isWalkFrom_iff_init isWalkFrom_snoc isWalkFrom_zero)

namespace TauCeti.TemperleyLieb

section EigenvectorUpTo

variable {K : Type*} [Semiring K] {V : Type*} [Fintype V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (v₀ : V) (r : V → K)

/-- The squares of `r` satisfy the adjacency eigenvector equation with eigenvalue `δ` at the
endpoints of all walks in `G` from `v₀` with fewer than `n` steps. -/
def IsPathEigenvectorUpTo (δ : K) (n : ℕ) : Prop :=
  ∀ ⦃m : ℕ⦄, m < n → ∀ ⦃s : Fin (m + 1) → V⦄, G.IsWalkFrom v₀ s →
    ∑ u ∈ G.neighborFinset (s (Fin.last m)), r u ^ 2 = δ * r (s (Fin.last m)) ^ 2

variable {G v₀ r}

/-- Unfolded characterization of `IsPathEigenvectorUpTo`. -/
theorem isPathEigenvectorUpTo_iff {δ : K} {n : ℕ} :
    IsPathEigenvectorUpTo G v₀ r δ n ↔
      ∀ ⦃m : ℕ⦄, m < n → ∀ ⦃s : Fin (m + 1) → V⦄, G.IsWalkFrom v₀ s →
        ∑ u ∈ G.neighborFinset (s (Fin.last m)), r u ^ 2 = δ * r (s (Fin.last m)) ^ 2 :=
  (Iff.rfl)

/-- On zero strands there are no walks of fewer than `0` steps, so `IsPathEigenvectorUpTo` holds
vacuously. -/
@[simp]
theorem isPathEigenvectorUpTo_zero (δ : K) : IsPathEigenvectorUpTo G v₀ r δ 0 :=
  fun _ hm ↦ absurd hm (Nat.not_lt_zero _)

/-- Monotonicity of `IsPathEigenvectorUpTo` in the step bound. -/
theorem IsPathEigenvectorUpTo.mono {δ : K} {m n : ℕ} (hδ : IsPathEigenvectorUpTo G v₀ r δ n)
    (hmn : m ≤ n) : IsPathEigenvectorUpTo G v₀ r δ m :=
  fun _ hk _ hs ↦ hδ (hk.trans_le hmn) hs

/-- A global adjacency eigenvector satisfies `IsPathEigenvectorUpTo` at every depth `n`. -/
theorem IsPathEigenvectorUpTo.of_forall {δ : K}
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) (n : ℕ) :
    IsPathEigenvectorUpTo G v₀ r δ n :=
  fun _ _ _ _ ↦ hδ _

/-- Applying a ring homomorphism preserves `IsPathEigenvectorUpTo`. -/
theorem IsPathEigenvectorUpTo.map {L : Type*} [Semiring L] (f : K →+* L) {δ : K} {n : ℕ}
    (hδ : IsPathEigenvectorUpTo G v₀ r δ n) :
    IsPathEigenvectorUpTo G v₀ (f ∘ r) (f δ) n := by
  intro m hm s hs
  simpa [Function.comp_def, map_sum, map_pow, map_mul] using congrArg f (hδ hm hs)

/-- At any position `a` strictly before the end of an `m`-step walk from `v₀`, the bounded
eigenvector hypothesis up to `m` gives the neighbour-square sum at `s a`. -/
theorem IsPathEigenvectorUpTo.apply_of_lt {δ : K} {m : ℕ}
    (hδ : IsPathEigenvectorUpTo G v₀ r δ m) {s : Fin (m + 1) → V} (hs : G.IsWalkFrom v₀ s)
    {a : Fin (m + 1)} (ha : a.val < m) :
    ∑ u ∈ G.neighborFinset (s a), r u ^ 2 = δ * r (s a) ^ 2 := by
  have h := hδ ha (hs.take ha.le)
  have hidx : Fin.castLE (Nat.add_le_add_right ha.le 1) (Fin.last a.val) = a := Fin.ext (by simp)
  rwa [Fin.take_apply, hidx] at h

end EigenvectorUpTo

section WalkGenerator

variable {K : Type*} [Field K] {V : Type*} [DecidableEq V] (G : SimpleGraph V)
  [DecidableRel G.Adj] [G.LocallyFinite] (r : V → K)

omit [G.LocallyFinite] in
/-- Generic Temperley–Lieb generator matrix on a walk-indexed type `W` equipped with an
embedding `toFun : W → Fin (m + 1) → V` and a validity predicate `valid : W → Prop`. -/
def walkGenerator {m : ℕ} {W : Type*} (toFun : W → Fin (m + 1) → V) (valid : W → Prop)
    [DecidablePred valid] (a b c : Fin (m + 1)) : Matrix W W K :=
  Matrix.of fun s t ↦
    if valid s ∧ toFun s a = toFun s c ∧
        toFun t = update (toFun s) b (toFun t b) ∧ G.Adj (toFun s a) (toFun t b) then
      r (toFun s b) * r (toFun t b) / r (toFun s a) ^ 2
    else 0

omit [G.LocallyFinite] in
/-- Entrywise evaluation of `walkGenerator`. -/
theorem walkGenerator_apply {m : ℕ} {W : Type*} (toFun : W → Fin (m + 1) → V)
    (valid : W → Prop) [DecidablePred valid] (a b c : Fin (m + 1)) (s t : W) :
    walkGenerator G r toFun valid a b c s t =
      if valid s ∧ toFun s a = toFun s c ∧
          toFun t = update (toFun s) b (toFun t b) ∧ G.Adj (toFun s a) (toFun t b) then
        r (toFun s b) * r (toFun t b) / r (toFun s a) ^ 2
      else 0 := (rfl)

variable {G r}

/-- Left multiplication by `walkGenerator` sums over neighbours `x` of `toFun s a` via `upd`
when `valid s` and `toFun s a = toFun s c`, and vanishes otherwise. -/
theorem walkGenerator_mul_apply {m : ℕ} {W : Type*} [Fintype W]
    (toFun : W → Fin (m + 1) → V) (hinj : Function.Injective toFun)
    (valid : W → Prop) [DecidablePred valid] {a b c : Fin (m + 1)}
    (upd : ∀ (s : W), valid s → toFun s a = toFun s c → ∀ (x : V), G.Adj (toFun s a) x → W)
    (hupd : ∀ {s : W} (hs : valid s) (hac : toFun s a = toFun s c) {x : V}
      (hx : G.Adj (toFun s a) x), toFun (upd s hs hac x hx) = update (toFun s) b x)
    (X : Matrix W W K) (s u : W) :
    (walkGenerator G r toFun valid a b c * X) s u =
      if h : valid s ∧ toFun s a = toFun s c then
        ∑ x ∈ (G.neighborFinset (toFun s a)).attach,
          r (toFun s b) * r x.val / r (toFun s a) ^ 2 *
            X (upd s h.1 h.2 x.val ((G.mem_neighborFinset _ _).1 x.property)) u
      else 0 := by
  classical
  rw [Matrix.mul_apply]; split_ifs with hs
  · let f (x : {x // x ∈ G.neighborFinset (toFun s a)}) :=
      upd s hs.1 hs.2 x.val ((G.mem_neighborFinset _ _).1 x.property)
    rw [← Finset.sum_subset (Finset.subset_univ ((G.neighborFinset (toFun s a)).attach.image f)),
      Finset.sum_image fun x _ y _ h ↦ Subtype.ext <| by
        have h' := congrFun (congrArg toFun h) b
        simpa [f, hupd] using h']
    · exact Finset.sum_congr rfl fun x _ ↦ by
        have hx : G.Adj (toFun s c) x.val := hs.2 ▸ (G.mem_neighborFinset _ _).1 x.property
        simp [walkGenerator_apply, f, hs.1, hs.2, hupd, hx]
    · intro t _ ht
      rw [walkGenerator_apply, ite_eq_right fun ⟨_, _, hst, hadj⟩ ↦ ht <| Finset.mem_image.2
        ⟨⟨toFun t b, (G.mem_neighborFinset _ _).2 hadj⟩, Finset.mem_attach _ _,
          hinj <| by rw [hupd]; exact hst.symm⟩, zero_mul]
  · exact Finset.sum_eq_zero fun _ _ ↦ by
      rw [walkGenerator_apply, ite_eq_right fun ⟨h1, h2, _⟩ ↦ hs ⟨h1, h2⟩, zero_mul]

/-- When every neighbour `x ≠ x₀` of `toFun s a` makes `X (upd ... x) u = 0`, the matrix product
`(walkGenerator ... * X) s u` collapses to the single term at `x₀`. -/
private theorem walkGenerator_mul_apply_eq_single {m : ℕ} {W : Type*} [Fintype W]
    (toFun : W → Fin (m + 1) → V) (hinj : Function.Injective toFun)
    (valid : W → Prop) [DecidablePred valid] {a b c : Fin (m + 1)}
    (upd : ∀ (s : W), valid s → toFun s a = toFun s c → ∀ (x : V), G.Adj (toFun s a) x → W)
    (hupd : ∀ {s : W} (hs : valid s) (hac : toFun s a = toFun s c) {x : V}
      (hx : G.Adj (toFun s a) x), toFun (upd s hs hac x hx) = update (toFun s) b x)
    (X : Matrix W W K) {s u : W} (hs : valid s ∧ toFun s a = toFun s c)
    (x₀ : V) (hx₀ : G.Adj (toFun s a) x₀)
    (hzero : ∀ {x : V} (hx : G.Adj (toFun s a) x), x ≠ x₀ →
      X (upd s hs.1 hs.2 x hx) u = 0) :
    (walkGenerator G r toFun valid a b c * X) s u =
      r (toFun s b) * r x₀ / r (toFun s a) ^ 2 * X (upd s hs.1 hs.2 x₀ hx₀) u := by
  classical
  rw [walkGenerator_mul_apply toFun hinj valid upd hupd, dite_eq_left hs]
  exact Finset.sum_eq_single_of_mem
    (f := fun x : ↥(G.neighborFinset (toFun s a)) ↦
      r (toFun s b) * r x.val / r (toFun s a) ^ 2 *
        X (upd s hs.1 hs.2 x.val ((G.mem_neighborFinset _ _).1 x.property)) u)
    ⟨x₀, (G.mem_neighborFinset _ _).2 hx₀⟩ (Finset.mem_attach _ _) fun x _ hne ↦ by
      rw [hzero ((G.mem_neighborFinset _ _).1 x.property) (fun h ↦ hne (Subtype.ext h)), mul_zero]

omit [G.LocallyFinite] in
/-- Evaluating `walkGenerator` at a walk `s'` whose position `b` has been updated to `x`. -/
theorem walkGenerator_update_apply {m : ℕ} {W : Type*} (toFun : W → Fin (m + 1) → V)
    (valid : W → Prop) [DecidablePred valid] {a b c : Fin (m + 1)}
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    {s s' : W} (hs' : valid s') (hac : toFun s a = toFun s c)
    {x : V} (hs'_coe : toFun s' = update (toFun s) b x) (u : W) :
    walkGenerator G r toFun valid a b c s' u =
      if toFun u = update (toFun s) b (toFun u b) ∧ G.Adj (toFun s a) (toFun u b) then
        r x * r (toFun u b) / r (toFun s a) ^ 2 else 0 := by
  rw [walkGenerator_apply, hs'_coe]
  simp [update_of_ne (Fin.ne_of_val_ne (by omega) : a ≠ b),
    update_of_ne (Fin.ne_of_val_ne (by omega) : c ≠ b), hac, hs']

omit [G.LocallyFinite] in
/-- For self-adjoint weights `r`, `walkGenerator` is Hermitian when `valid` is preserved by
interior updates. -/
theorem conjTranspose_walkGenerator [StarRing K] (hrs : ∀ v, IsSelfAdjoint (r v))
    {m : ℕ} {W : Type*} {v₀ : V} (toFun : W → Fin (m + 1) → V) (valid : W → Prop)
    [DecidablePred valid] {a b c : Fin (m + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) (hwalk : ∀ {s : W}, valid s → G.IsWalkFrom v₀ (toFun s))
    (hvalid_upd : ∀ {s t : W}, valid s → toFun s a = toFun s c →
      toFun t = update (toFun s) b (toFun t b) → G.Adj (toFun s a) (toFun t b) → valid t) :
    (walkGenerator G r toFun valid a b c)ᴴ = walkGenerator G r toFun valid a b c := by
  have ha : a ≠ b := Fin.ne_of_val_ne (by omega)
  have hc : c ≠ b := Fin.ne_of_val_ne (by omega)
  have hsymm {s t : W} (h : valid s ∧ toFun s a = toFun s c ∧
      toFun t = update (toFun s) b (toFun t b) ∧ G.Adj (toFun s a) (toFun t b)) :
      (valid t ∧ toFun t a = toFun t c ∧
        toFun s = update (toFun t) b (toFun s b) ∧ G.Adj (toFun t a) (toFun s b)) ∧
        toFun t a = toFun s a := by
    have hta : toFun t a = toFun s a := by rw [congrFun h.2.2.1 a, update_of_ne ha]
    exact ⟨⟨hvalid_upd h.1 h.2.1 h.2.2.1 h.2.2.2,
      by rw [hta, congrFun h.2.2.1 c, update_of_ne hc, h.2.1],
      by rw [h.2.2.1, update_idem, update_eq_self], hta ▸ (hwalk h.1).adj hab⟩, hta⟩
  ext s t
  rw [conjTranspose_apply, walkGenerator_apply, walkGenerator_apply]
  split_ifs with h₁ h₂ h₃
  · rw [(hsymm h₂).2]
    simp only [star_div₀, star_mul, star_pow, (hrs _).star_eq, mul_comm (r (toFun s b))]
  all_goals first | exact star_zero K | exact (h₂ (hsymm h₁).1).elim | exact (h₁ (hsymm h₃).1).elim

/-- Idempotent relation `e ^ 2 = δ • e` for `walkGenerator`. -/
theorem walkGenerator_mul_self (hr : ∀ v, r v ≠ 0) {δ : K}
    {m : ℕ} {W : Type*} [Fintype W]
    (toFun : W → Fin (m + 1) → V) (hinj : Function.Injective toFun)
    (valid : W → Prop) [DecidablePred valid] {a b c : Fin (m + 1)}
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (hδ : ∀ {s : W}, valid s →
      ∑ x ∈ G.neighborFinset (toFun s a), r x ^ 2 = δ * r (toFun s a) ^ 2)
    (upd : ∀ (s : W), valid s → toFun s a = toFun s c → ∀ (x : V), G.Adj (toFun s a) x → W)
    (hupd : ∀ {s : W} (hs : valid s) (hac : toFun s a = toFun s c) {x : V}
      (hx : G.Adj (toFun s a) x), toFun (upd s hs hac x hx) = update (toFun s) b x)
    (hvalid_upd : ∀ {s : W} (hs : valid s) (hac : toFun s a = toFun s c) {x : V}
      (hx : G.Adj (toFun s a) x), valid (upd s hs hac x hx)) :
    walkGenerator G r toFun valid a b c * walkGenerator G r toFun valid a b c =
      δ • walkGenerator G r toFun valid a b c := by
  classical
  ext s u
  rw [walkGenerator_mul_apply toFun hinj valid upd hupd, Matrix.smul_apply, walkGenerator_apply,
    smul_eq_mul]
  by_cases hs : valid s ∧ toFun s a = toFun s c
  · rw [dite_eq_left hs]
    by_cases hu : toFun u = update (toFun s) b (toFun u b) ∧ G.Adj (toFun s a) (toFun u b)
    · rw [ite_eq_left ⟨hs.1, hs.2, hu⟩]
      simp_rw [walkGenerator_update_apply toFun valid hab hbc (hvalid_upd hs.1 hs.2 _) hs.2
          (hupd hs.1 hs.2 _),
        ite_eq_left hu]
      rw [(G.neighborFinset (toFun s a)).sum_attach fun x ↦
          r (toFun s b) * r x / r (toFun s a) ^ 2 * (r x * r (toFun u b) / r (toFun s a) ^ 2),
        Finset.sum_congr rfl fun x _ ↦ (by ring :
          r (toFun s b) * r x / r (toFun s a) ^ 2 * (r x * r (toFun u b) / r (toFun s a) ^ 2) =
            r (toFun s b) * r (toFun u b) / r (toFun s a) ^ 4 * r x ^ 2),
        ← Finset.mul_sum, hδ hs.1]
      have := hr (toFun s a); field_simp
    · rw [ite_eq_right fun h ↦ hu h.2.2, mul_zero]
      refine Finset.sum_eq_zero fun x _ ↦ ?_
      rw [walkGenerator_update_apply toFun valid hab hbc (hvalid_upd hs.1 hs.2 _) hs.2
          (hupd hs.1 hs.2 _),
        ite_eq_right hu, mul_zero]
  · rw [dite_eq_right hs, ite_eq_right fun h ↦ hs ⟨h.1, h.2.1⟩, mul_zero]

/-- Zigzag relation `e₁ * e₂ * e₁ = e₁` for adjacent `walkGenerator`s. -/
theorem walkGenerator_zigzag (hr : ∀ v, r v ≠ 0)
    {m : ℕ} {W : Type*} [Fintype W] {v₀ : V}
    (toFun : W → Fin (m + 1) → V) (hinj : Function.Injective toFun)
    (valid : W → Prop) [DecidablePred valid]
    (hwalk : ∀ {s : W}, valid s → G.IsWalkFrom v₀ (toFun s))
    {a₁ b₁ c₁ a₂ b₂ c₂ q : Fin (m + 1)}
    (hab₁ : a₁.val + 1 = b₁.val) (hbc₁ : b₁.val + 1 = c₁.val)
    (hab₂ : a₂.val + 1 = b₂.val) (hbc₂ : b₂.val + 1 = c₂.val)
    (hc : (a₂ = b₁ ∧ b₂ = c₁ ∧ c₂ = q) ∨ (c₂ = b₁ ∧ b₂ = a₁ ∧ a₂ = q))
    (upd : ∀ {a b c : Fin (m + 1)}, a.val + 1 = b.val → b.val + 1 = c.val →
      ∀ (s : W), valid s → toFun s a = toFun s c → ∀ (x : V), G.Adj (toFun s a) x → W)
    (hupd : ∀ {a b c : Fin (m + 1)} (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
      {s : W} (hs : valid s) (hac : toFun s a = toFun s c) {x : V} (hx : G.Adj (toFun s a) x),
      toFun (upd hab hbc s hs hac x hx) = update (toFun s) b x)
    (hvalid_upd : ∀ {a b c : Fin (m + 1)} (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
      {s : W} (hs : valid s) (hac : toFun s a = toFun s c) {x : V} (hx : G.Adj (toFun s a) x),
      valid (upd hab hbc s hs hac x hx)) :
    walkGenerator G r toFun valid a₁ b₁ c₁ * walkGenerator G r toFun valid a₂ b₂ c₂ *
        walkGenerator G r toFun valid a₁ b₁ c₁ =
      walkGenerator G r toFun valid a₁ b₁ c₁ := by
  classical
  have hb₁q : b₁ ≠ q := hc.elim (fun ⟨_, rfl, rfl⟩ ↦ Fin.ne_of_val_ne (by omega))
    fun ⟨_, rfl, rfl⟩ ↦ Fin.ne_of_val_ne (by omega)
  have ⟨hab₁', hcb₁, hac₁'⟩ : a₁ ≠ b₁ ∧ c₁ ≠ b₁ ∧ a₁ ≠ c₁ :=
    ⟨Fin.ne_of_val_ne (by omega), Fin.ne_of_val_ne (by omega), Fin.ne_of_val_ne (by omega)⟩
  ext s u
  rw [mul_assoc, walkGenerator_apply]
  by_cases hs : valid s ∧ toFun s a₁ = toFun s c₁
  · have hqadj : G.Adj (toFun s a₁) (toFun s q) :=
      hc.elim (fun ⟨_, rfl, rfl⟩ ↦ hs.2 ▸ (hwalk hs.1).adj hbc₂)
        fun ⟨_, rfl, rfl⟩ ↦ ((hwalk hs.1).adj hab₂).symm
    -- Stage 1: in `e₁ * (e₂ * e₁)`, only the update of `b₁` to `toFun s q` survives, since `e₂`
    -- requires the two endpoints `{a₂, c₂} = {b₁, q}` of the intermediate walk to agree.
    have hstage1 : ∀ {x : V} (hx : G.Adj (toFun s a₁) x), x ≠ toFun s q →
        (walkGenerator G r toFun valid a₂ b₂ c₂ * walkGenerator G r toFun valid a₁ b₁ c₁)
          (upd hab₁ hbc₁ s hs.1 hs.2 x hx) u = 0 := fun hx hxq ↦ by
      rw [walkGenerator_mul_apply toFun hinj valid (upd hab₂ hbc₂) (hupd hab₂ hbc₂),
        dite_eq_right fun hEq ↦ hxq <| by
          have hxcoe := hupd hab₁ hbc₁ hs.1 hs.2 hx
          rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · simpa [hxcoe, update_of_ne hb₁q.symm] using hEq.2
          · simpa [hxcoe, update_of_ne hb₁q.symm] using hEq.2.symm]
    rw [walkGenerator_mul_apply_eq_single toFun hinj valid (upd hab₁ hbc₁) (hupd hab₁ hbc₁) _ hs
      (toFun s q) hqadj hstage1]
    let s₁ := upd hab₁ hbc₁ s hs.1 hs.2 (toFun s q) hqadj
    have hs₁_valid : valid s₁ := hvalid_upd hab₁ hbc₁ hs.1 hs.2 hqadj
    have hs₁_coe : toFun s₁ = update (toFun s) b₁ (toFun s q) := hupd hab₁ hbc₁ hs.1 hs.2 hqadj
    have ⟨hs₁a₂, hs₁c₂, hs₁b₂⟩ :
        toFun s₁ a₂ = toFun s q ∧ toFun s₁ c₂ = toFun s q ∧ toFun s₁ b₂ = toFun s a₁ := by
      rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
        simp [hs₁_coe, update_of_ne hb₁q.symm, update_of_ne hab₁', update_of_ne hcb₁, hs.2]
    have hs₁ : toFun s₁ a₂ = toFun s₁ c₂ := hs₁a₂.trans hs₁c₂.symm
    have haadj : G.Adj (toFun s₁ a₂) (toFun s a₁) := hs₁a₂ ▸ hqadj.symm
    -- Stage 2: from `s₁`, only the update of `b₂ ∈ {a₁, c₁}` back to `toFun s a₁` survives,
    -- since the final `e₁` requires endpoints `a₁` and `c₁` to agree; that step restores `s₁`.
    have hstage2 : ∀ {y : V} (hy : G.Adj (toFun s₁ a₂) y), y ≠ toFun s a₁ →
        walkGenerator G r toFun valid a₁ b₁ c₁ (upd hab₂ hbc₂ s₁ hs₁_valid hs₁ y hy) u = 0 :=
      fun hy hya ↦ by
        rw [walkGenerator_apply, ite_eq_right fun ⟨_, hEq, _, _⟩ ↦ hya <| by
          rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · simp only [hupd hab₂ hbc₂, hs₁_coe] at hEq
            simpa [update_of_ne hac₁', update_of_ne hab₁'] using hEq.symm
          · simp only [hupd hab₂ hbc₂, hs₁_coe] at hEq
            simpa [update_of_ne hac₁'.symm, update_of_ne hcb₁, ← hs.2] using hEq]
    rw [walkGenerator_mul_apply_eq_single toFun hinj valid (upd hab₂ hbc₂) (hupd hab₂ hbc₂) _
        ⟨hs₁_valid, hs₁⟩ (toFun s a₁) haadj hstage2,
      hinj ((hupd hab₂ hbc₂ hs₁_valid hs₁ haadj).trans (by rw [← hs₁b₂, update_eq_self])),
      walkGenerator_update_apply toFun valid hab₁ hbc₁ hs₁_valid hs.2 hs₁_coe]
    simp only [hs, true_and]; split_ifs
    · rw [hs₁b₂, hs₁a₂, hs.2]; have := hr (toFun s c₁); have := hr (toFun s q); field_simp
    · simp
  · rw [walkGenerator_mul_apply toFun hinj valid (upd hab₁ hbc₁) (hupd hab₁ hbc₁),
      dite_eq_right hs, ite_eq_right fun h ↦ hs ⟨h.1, h.2.1⟩]

/-- Product of two `walkGenerator`s whose updated positions are disjoint. -/
theorem walkGenerator_mul_walkGenerator_apply {m : ℕ} {W : Type*} [Fintype W]
    (toFun : W → Fin (m + 1) → V) (hinj : Function.Injective toFun)
    (valid : W → Prop) [DecidablePred valid] {a b c a' b' c' : Fin (m + 1)}
    (h₁ : b ≠ a') (h₂ : b ≠ b') (h₃ : b ≠ c')
    (upd : ∀ (s : W), valid s → toFun s a = toFun s c → ∀ (x : V), G.Adj (toFun s a) x → W)
    (hupd : ∀ {s : W} (hs : valid s) (hac : toFun s a = toFun s c) {x : V}
      (hx : G.Adj (toFun s a) x), toFun (upd s hs hac x hx) = update (toFun s) b x)
    (hvalid_upd : ∀ {s : W} (hs : valid s) (hac : toFun s a = toFun s c) {x : V}
      (hx : G.Adj (toFun s a) x), valid (upd s hs hac x hx))
    (s u : W) :
    (walkGenerator G r toFun valid a b c * walkGenerator G r toFun valid a' b' c') s u =
      if valid s ∧ toFun s a = toFun s c ∧ toFun s a' = toFun s c' ∧
          toFun u = update (update (toFun s) b (toFun u b)) b' (toFun u b') ∧
          G.Adj (toFun s a) (toFun u b) ∧ G.Adj (toFun s a') (toFun u b') then
        r (toFun s b) * r (toFun u b) / r (toFun s a) ^ 2 *
          (r (toFun s b') * r (toFun u b') / r (toFun s a') ^ 2)
      else 0 := by
  classical
  by_cases hs : valid s ∧ toFun s a = toFun s c
  · by_cases hub : G.Adj (toFun s a) (toFun u b)
    · -- Only `x = toFun u b` survives since the second generator leaves position `b ≠ b'` fixed.
      have hzero : ∀ {x : V} (hx : G.Adj (toFun s a) x), x ≠ toFun u b →
          walkGenerator G r toFun valid a' b' c' (upd s hs.1 hs.2 x hx) u = 0 := fun hx hxu ↦ by
        rw [walkGenerator_apply, ite_eq_right fun ⟨_, _, hEq, _⟩ ↦ hxu <| by
          have hxcoe := hupd hs.1 hs.2 hx
          simpa [hxcoe, update_of_ne h₂] using (congrFun hEq b).symm]
      rw [walkGenerator_mul_apply_eq_single toFun hinj valid upd hupd _ hs (toFun u b) hub hzero,
        walkGenerator_apply]
      have hucoe := hupd hs.1 hs.2 hub
      have huval := hvalid_upd hs.1 hs.2 hub
      simp only [hucoe, update_of_ne h₁.symm, update_of_ne h₂.symm, update_of_ne h₃.symm,
        hs.1, hs.2, huval, hs.2 ▸ hub, true_and]
      split_ifs <;> simp
    · rw [walkGenerator_mul_apply toFun hinj valid upd hupd, dite_eq_left hs,
        ite_eq_right fun h ↦ hub h.2.2.2.2.1]
      refine Finset.sum_eq_zero fun x _ ↦ ?_
      rw [walkGenerator_apply, ite_eq_right fun ⟨_, _, hEq, _⟩ ↦ hub <| by
        have hxcoe := hupd hs.1 hs.2 ((G.mem_neighborFinset _ _).1 x.property)
        exact (by simpa [hxcoe, update_of_ne h₂] using congrFun hEq b : toFun u b = x.val) ▸
          (G.mem_neighborFinset _ _).1 x.property, mul_zero]
  · rw [walkGenerator_mul_apply toFun hinj valid upd hupd, dite_eq_right hs,
      ite_eq_right fun h ↦ hs ⟨h.1, h.2.1⟩]

/-- Far-commutation relation for disjoint `walkGenerator`s. -/
theorem walkGenerator_mul_walkGenerator_comm {m : ℕ} {W : Type*} [Fintype W]
    (toFun : W → Fin (m + 1) → V) (hinj : Function.Injective toFun)
    (valid : W → Prop) [DecidablePred valid] {a b c a' b' c' : Fin (m + 1)}
    (h₁ : b ≠ a') (h₂ : b ≠ b') (h₃ : b ≠ c') (h₄ : b' ≠ a) (h₅ : b' ≠ c)
    (upd₁ : ∀ (s : W), valid s → toFun s a = toFun s c → ∀ (x : V), G.Adj (toFun s a) x → W)
    (hupd₁ : ∀ {s : W} (hs : valid s) (hac : toFun s a = toFun s c) {x : V}
      (hx : G.Adj (toFun s a) x), toFun (upd₁ s hs hac x hx) = update (toFun s) b x)
    (hvalid_upd₁ : ∀ {s : W} (hs : valid s) (hac : toFun s a = toFun s c) {x : V}
      (hx : G.Adj (toFun s a) x), valid (upd₁ s hs hac x hx))
    (upd₂ : ∀ (s : W), valid s → toFun s a' = toFun s c' → ∀ (x : V), G.Adj (toFun s a') x → W)
    (hupd₂ : ∀ {s : W} (hs : valid s) (hac : toFun s a' = toFun s c') {x : V}
      (hx : G.Adj (toFun s a') x), toFun (upd₂ s hs hac x hx) = update (toFun s) b' x)
    (hvalid_upd₂ : ∀ {s : W} (hs : valid s) (hac : toFun s a' = toFun s c') {x : V}
      (hx : G.Adj (toFun s a') x), valid (upd₂ s hs hac x hx)) :
    walkGenerator G r toFun valid a b c * walkGenerator G r toFun valid a' b' c' =
      walkGenerator G r toFun valid a' b' c' * walkGenerator G r toFun valid a b c := by
  classical
  ext s u
  rw [walkGenerator_mul_walkGenerator_apply toFun hinj valid h₁ h₂ h₃ upd₁ hupd₁
      hvalid_upd₁,
    walkGenerator_mul_walkGenerator_apply toFun hinj valid h₄ h₂.symm h₅ upd₂ hupd₂
      hvalid_upd₂,
    update_comm h₂]
  split_ifs <;> first | ring1 | (exfalso; tauto)

end WalkGenerator

variable {K : Type*} [Field K] {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (v₀ : V) (r : V → K)

section Generator

variable {m : ℕ}

/-- The matrix of a Temperley–Lieb generator in the path model on walks with `m` steps, acting on
the vertex at position `b`, whose neighbouring positions are `a` and `c`. Its entry at `s` and `t`
is `r (s b) * r (t b) / r (s a) ^ 2` when `s` is a walk from `v₀` with `s a = s c`, the
configuration `t` differs from `s` at most at position `b`, and `t b` is a neighbour of `s a`; it
is `0` otherwise. -/
def pathGenerator (a b c : Fin (m + 1)) : Matrix (Fin (m + 1) → V) (Fin (m + 1) → V) K :=
  walkGenerator G r id (G.IsWalkFrom v₀) a b c

omit [Fintype V] in
theorem pathGenerator_apply (a b c : Fin (m + 1)) (s t : Fin (m + 1) → V) :
    pathGenerator G v₀ r a b c s t =
      if G.IsWalkFrom v₀ s ∧ s a = s c ∧ t = update s b (t b) ∧ G.Adj (s a) (t b) then
        r (s b) * r (t b) / r (s a) ^ 2
      else 0 := (rfl)

variable {G v₀ r}

/-- Left multiplication by a generator matrix: the row `s` of the product is a weighted sum of
the rows of `X` at the walks obtained from `s` by moving the vertex at position `b` to a neighbour
of `s a`. -/
theorem pathGenerator_mul_apply (a b c : Fin (m + 1))
    (X : Matrix (Fin (m + 1) → V) (Fin (m + 1) → V) K) (s u : Fin (m + 1) → V) :
    (pathGenerator G v₀ r a b c * X) s u =
      if G.IsWalkFrom v₀ s ∧ s a = s c then
        ∑ x ∈ G.neighborFinset (s a), r (s b) * r x / r (s a) ^ 2 * X (update s b x) u
      else 0 := by
  rw [pathGenerator, walkGenerator_mul_apply id Function.injective_id (G.IsWalkFrom v₀)
    (fun s _ _ x _ ↦ update s b x) (fun _ _ _ _ ↦ rfl)]
  simp only [id_eq]
  by_cases hs : G.IsWalkFrom v₀ s ∧ s a = s c
  · rw [dite_eq_left hs, ite_eq_left hs,
      Finset.sum_attach (G.neighborFinset (s a))
        fun x ↦ r (s b) * r x / r (s a) ^ 2 * X (update s b x) u]
  · rw [dite_eq_right hs, ite_eq_right hs]

omit [Fintype V] in
/-- A generator matrix evaluated at a walk whose vertex at position `b` has been moved. -/
theorem pathGenerator_update_apply {a b c : Fin (m + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) {s : Fin (m + 1) → V} (hs : G.IsWalkFrom v₀ s) (hac : s a = s c)
    {x : V} (hx : G.Adj (s a) x) (u : Fin (m + 1) → V) :
    pathGenerator G v₀ r a b c (update s b x) u =
      if u = update s b (u b) ∧ G.Adj (s a) (u b) then r x * r (u b) / r (s a) ^ 2 else 0 :=
  walkGenerator_update_apply id (G.IsWalkFrom v₀) hab hbc (hs.update hab hbc hac hx) hac rfl u

variable (hr : ∀ v, r v ≠ 0) {δ : K}

include hr in
/-- Closing a loop multiplies a generator matrix by the loop value `δ`. -/
theorem pathGenerator_mul_self (hδ : IsPathEigenvectorUpTo G v₀ r δ m)
    {a b c : Fin (m + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) :
    pathGenerator G v₀ r a b c * pathGenerator G v₀ r a b c =
      δ • pathGenerator G v₀ r a b c :=
  walkGenerator_mul_self hr id Function.injective_id (G.IsWalkFrom v₀) hab hbc
    (fun hs ↦ hδ.apply_of_lt hs (by omega)) (fun s _ _ x _ ↦ update s b x)
    (fun _ _ _ _ ↦ rfl) (fun hs hac _ hx ↦ hs.update hab hbc hac hx)

include hr in
/-- The zigzag relation for the generator matrices at the consecutive positions `b` and `c`, with
the one at `b` outside. -/
theorem pathGenerator_zigzag_left {a b c d : Fin (m + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) (hcd : c.val + 1 = d.val) :
    pathGenerator G v₀ r a b c * pathGenerator G v₀ r b c d * pathGenerator G v₀ r a b c =
      pathGenerator G v₀ r a b c :=
  walkGenerator_zigzag hr id Function.injective_id (G.IsWalkFrom v₀) id hab hbc hbc hcd
    (Or.inl ⟨rfl, rfl, rfl⟩) (fun {_ b _} _ _ s _ _ x _ ↦ update s b x)
    (fun {_ _ _} _ _ {_} _ _ {_} _ ↦ rfl)
    (fun {_ _ _} hab' hbc' {_} hs hac {_} hx ↦ hs.update hab' hbc' hac hx)

include hr in
/-- The zigzag relation for the generator matrices at the consecutive positions `b` and `c`, with
the one at `c` outside. -/
theorem pathGenerator_zigzag_right {a b c d : Fin (m + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) (hcd : c.val + 1 = d.val) :
    pathGenerator G v₀ r b c d * pathGenerator G v₀ r a b c * pathGenerator G v₀ r b c d =
      pathGenerator G v₀ r b c d :=
  walkGenerator_zigzag hr id Function.injective_id (G.IsWalkFrom v₀) id hbc hcd hab hbc
    (Or.inr ⟨rfl, rfl, rfl⟩) (fun {_ b _} _ _ s _ _ x _ ↦ update s b x)
    (fun {_ _ _} _ _ {_} _ _ {_} _ ↦ rfl)
    (fun {_ _ _} hab' hbc' {_} hs hac {_} hx ↦ hs.update hab' hbc' hac hx)

/-- The product of the generator matrices at two positions `b` and `b'` that neither neighbours
nor equals the other, as an explicit matrix: it moves both vertices independently. -/
theorem pathGenerator_mul_pathGenerator_apply {a b c a' b' c' : Fin (m + 1)}
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) (h₁ : b ≠ a') (h₂ : b ≠ b')
    (h₃ : b ≠ c') (s v : Fin (m + 1) → V) :
    (pathGenerator G v₀ r a b c * pathGenerator G v₀ r a' b' c') s v =
      if G.IsWalkFrom v₀ s ∧ s a = s c ∧ s a' = s c' ∧
          v = update (update s b (v b)) b' (v b') ∧ G.Adj (s a) (v b) ∧ G.Adj (s a') (v b') then
        r (s b) * r (v b) / r (s a) ^ 2 * (r (s b') * r (v b') / r (s a') ^ 2)
      else 0 :=
  walkGenerator_mul_walkGenerator_apply id Function.injective_id (G.IsWalkFrom v₀)
    h₁ h₂ h₃ (fun s _ _ x _ ↦ update s b x) (fun _ _ _ _ ↦ rfl)
    (fun hs hac _ hx ↦ hs.update hab hbc hac hx) s v

/-- Generator matrices at positions `b` and `b'` that neither neighbour nor equal one another
commute. -/
theorem pathGenerator_mul_pathGenerator_comm {a b c a' b' c' : Fin (m + 1)}
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) (hab' : a'.val + 1 = b'.val)
    (hbc' : b'.val + 1 = c'.val) (h₁ : b ≠ a') (h₂ : b ≠ b') (h₃ : b ≠ c') (h₄ : b' ≠ a)
    (h₅ : b' ≠ c) :
    pathGenerator G v₀ r a b c * pathGenerator G v₀ r a' b' c' =
      pathGenerator G v₀ r a' b' c' * pathGenerator G v₀ r a b c :=
  walkGenerator_mul_walkGenerator_comm id Function.injective_id (G.IsWalkFrom v₀)
    h₁ h₂ h₃ h₄ h₅ (fun s _ _ x _ ↦ update s b x) (fun _ _ _ _ ↦ rfl)
    (fun hs hac _ hx ↦ hs.update hab hbc hac hx) (fun s _ _ x _ ↦ update s b' x)
    (fun _ _ _ _ ↦ rfl) (fun hs hac _ hx ↦ hs.update hab' hbc' hac hx)

/-- On walks, the generator matrix at positions away from the last one is extended from the
walks with one step fewer. -/
theorem pathGenerator_castSucc_apply {a b c : Fin (m + 1)} {s : Fin (m + 2) → V}
    (hs : G.IsWalkFrom v₀ s) (t : Fin (m + 2) → V) :
    pathGenerator G v₀ r a.castSucc b.castSucc c.castSucc s t =
      extendLast (α := fun _ ↦ V) (pathGenerator G v₀ r a b c) s t := by
  obtain ⟨s, y, rfl⟩ : ∃ s' y, s = Fin.snoc s' y := ⟨_, _, (Fin.snoc_init_self s).symm⟩
  obtain ⟨t, z, rfl⟩ : ∃ t' z, t = Fin.snoc t' z := ⟨_, _, (Fin.snoc_init_self t).symm⟩
  rw [isWalkFrom_snoc] at hs
  rw [pathGenerator_apply, extendLast_apply, pathGenerator_apply]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.init_snoc, ← Fin.snoc_update, Fin.snoc_inj,
    isWalkFrom_snoc, hs, true_and, eq_comm (a := z)]
  split_ifs <;> first | rfl | (exfalso; tauto)

end Generator

variable {G v₀ r}

section Rep

variable (hr : ∀ v, r v ≠ 0) {δ : K} {n : ℕ}

variable (G v₀) in
/-- The **path representation** of the Temperley–Lieb algebra on `n` strands with loop value `δ`,
on functions of the vertex sequences of length `n + 1`: the generator `e i` acts by the generator
matrix at position `i + 1`. The generator matrices are supported on the walks in `G` starting at
`v₀`, so on the functions supported on the other vertex sequences the representation acts through
the character sending every generator to `0`. -/
def pathRep (hδ : IsPathEigenvectorUpTo G v₀ r δ n) :
    TemperleyLieb K δ n →ₐ[K] Matrix (Fin (n + 1) → V) (Fin (n + 1) → V) K :=
  lift (fun i ↦ pathGenerator G v₀ r ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩)
    (fun _ ↦ pathGenerator_mul_self hr hδ rfl rfl)
    (fun {i j} h ↦ by
      obtain ⟨i, hi⟩ := i
      obtain ⟨j, hj⟩ := j
      simp only at h
      rcases h with rfl | rfl
      · exact pathGenerator_zigzag_left hr rfl rfl rfl
      · exact pathGenerator_zigzag_right hr rfl rfl rfl)
    (fun {i j} h ↦ pathGenerator_mul_pathGenerator_comm rfl rfl rfl rfl
      (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)
      (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)
      (by simp [Fin.ext_iff]; omega))

/-- The path representation sends the generator `e i` to the generator matrix at position
`i + 1`. -/
@[simp]
theorem pathRep_e (hδ : IsPathEigenvectorUpTo G v₀ r δ n) (i : Fin (n - 1)) :
    pathRep G v₀ hr hδ (e δ i) =
      pathGenerator G v₀ r ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩ :=
  lift_e _ _ _ _ i

/-- The path representation preserves walks and their endpoints: its matrix entry at `s` and `t`
vanishes unless `s` and `t` are both walks from `v₀` or both not, and end at the same vertex. -/
theorem pathRep_apply_eq_zero (hδ : IsPathEigenvectorUpTo G v₀ r δ n)
    (x : TemperleyLieb K δ n) {s t : Fin (n + 1) → V}
    (h : ¬((G.IsWalkFrom v₀ s ↔ G.IsWalkFrom v₀ t) ∧ s (Fin.last n) = t (Fin.last n))) :
    pathRep G v₀ hr hδ x s t = 0 := by
  induction x using TemperleyLieb.induction generalizing s t with
  | e i =>
    rw [pathRep_e, pathGenerator_apply, ite_eq_right_iff]
    rintro ⟨hs, hac, hst, hadj⟩
    refine (h ⟨⟨fun _ ↦ ?_, fun _ ↦ hs⟩, ?_⟩).elim
    · rw [hst]
      exact hs.update rfl rfl hac hadj
    · rw [hst, update_of_ne (by simp [Fin.ext_iff]; omega)]
  | algebraMap k =>
    rw [AlgHom.commutes, Matrix.algebraMap_matrix_apply, ite_eq_right_iff]
    rintro rfl
    exact (h ⟨Iff.rfl, rfl⟩).elim
  | add x y hx hy => rw [map_add, Matrix.add_apply, hx h, hy h, add_zero]
  | mul x y hx hy =>
    rw [map_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun u _ ↦ ?_
    by_cases hsu : (G.IsWalkFrom v₀ s ↔ G.IsWalkFrom v₀ u) ∧ s (Fin.last n) = u (Fin.last n)
    · rw [hy fun hut ↦ h ⟨hsu.1.trans hut.1, hsu.2.trans hut.2⟩, mul_zero]
    · rw [hx hsu, zero_mul]

/-- On the rows of walks, adding a straight strand acts on the path representation by extending
walks by one step: the matrix of `strandIncl x` agrees with `extendLast` of the matrix of `x`. -/
theorem pathRep_strandIncl_apply (hδ : IsPathEigenvectorUpTo G v₀ r δ (n + 2))
    (x : TemperleyLieb K δ (n + 1)) {s : Fin (n + 3) → V}
    (hs : G.IsWalkFrom v₀ s) (t : Fin (n + 3) → V) :
    pathRep G v₀ hr hδ (strandIncl x) s t =
      extendLast (α := fun _ ↦ V) (pathRep G v₀ hr (hδ.mono (Nat.le_succ (n + 1))) x) s t := by
  induction x using TemperleyLieb.induction generalizing s t with
  | e i =>
    rw [strandIncl_e, pathRep_e, pathRep_e, ← pathGenerator_castSucc_apply hs]
    simp only [Fin.castSucc_mk, Fin.val_castSucc]
  | algebraMap k => simp only [AlgHom.commutes]
  | add x y hx hy => simp only [map_add, Matrix.add_apply, hx hs, hy hs]
  | mul x y hx hy =>
    rw [map_mul, map_mul, map_mul, map_mul, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [hx hs]
    by_cases hu : G.IsWalkFrom v₀ u
    · rw [hy hu]
    -- A row of a walk has no entry in the column of a non-walk.
    rw [extendLast_apply, ite_eq_right_iff.2 fun hlast ↦
      pathRep_apply_eq_zero hr (hδ.mono (Nat.le_succ (n + 1))) x
        fun h ↦ hu ((isWalkFrom_iff_init u).2 ⟨h.1.1 ((isWalkFrom_iff_init s).1 hs).1, by
          rw [← h.2, ← hlast]; exact ((isWalkFrom_iff_init s).1 hs).2⟩), zero_mul, zero_mul]

end Rep

section Weight

variable (G v₀ r) in
/-- The weight of a vertex sequence in the trace of the path model: `(r v / r v₀) ^ 2` for a walk
from `v₀` ending at the vertex `v`, and `0` for every other sequence. -/
def pathWeight {m : ℕ} (s : Fin (m + 1) → V) : K :=
  if G.IsWalkFrom v₀ s then (r (s (Fin.last m)) / r v₀) ^ 2 else 0

omit [Fintype V] in
theorem pathWeight_def {m : ℕ} (s : Fin (m + 1) → V) :
    pathWeight G v₀ r s = if G.IsWalkFrom v₀ s then (r (s (Fin.last m)) / r v₀) ^ 2 else 0 :=
  (rfl)

/-- Extending walks by one step multiplies the total weight by `δ`: the weights of the neighbours
of the endpoint of an `m`-step walk add up to `δ` times the weight of that endpoint. -/
theorem sum_pathWeight_snoc {δ : K} {m : ℕ} (hδ : IsPathEigenvectorUpTo G v₀ r δ (m + 1))
    (t : Fin (m + 1) → V) :
    ∑ y, pathWeight G v₀ r (Fin.snoc t y : Fin (m + 2) → V) = δ * pathWeight G v₀ r t := by
  simp only [pathWeight_def, isWalkFrom_snoc, Fin.snoc_last, ite_and]
  split_ifs with ht
  · rw [← Finset.sum_filter, ← SimpleGraph.neighborFinset_eq_filter]
    simp_rw [div_pow]
    rw [← Finset.sum_div, hδ (Nat.lt_succ_self m) ht, mul_div_assoc]
  · simp

end Weight

section Trace

variable (hr : ∀ v, r v ≠ 0) {δ : K} {n : ℕ}

variable (G v₀) in
/-- The **trace of the path model** on `n` strands: the trace of the path representation weighted
by `TauCeti.TemperleyLieb.pathWeight`. Given `IsPathEigenvectorUpTo G v₀ r δ n`, its restrictions
form a Markov trace up to `n` strands (`TauCeti.TemperleyLieb.isMarkovTraceUpTo_pathTrace`). -/
def pathTrace (hδ : IsPathEigenvectorUpTo G v₀ r δ n) : TemperleyLieb K δ n →ₗ[K] K :=
  traceLinearMap (Fin (n + 1) → V) K K ∘ₗ LinearMap.mulLeft K (diagonal (pathWeight G v₀ r)) ∘ₗ
    (pathRep G v₀ hr hδ).toLinearMap

/-- The trace of the path model is the weighted trace of the path representation. -/
theorem pathTrace_apply (hδ : IsPathEigenvectorUpTo G v₀ r δ n) (x : TemperleyLieb K δ n) :
    pathTrace G v₀ hr hδ x = trace (diagonal (pathWeight G v₀ r) * pathRep G v₀ hr hδ x) :=
  (rfl)

/-- The trace of the path model of the identity on `n` strands is `δ ^ n`. -/
@[simp]
theorem pathTrace_one (hδ : IsPathEigenvectorUpTo G v₀ r δ n) :
    pathTrace G v₀ hr hδ (1 : TemperleyLieb K δ n) = δ ^ n := by
  rw [pathTrace_apply, map_one, mul_one, trace_diagonal]
  induction n with
  | zero =>
    rw [Fintype.sum_eq_single (fun _ ↦ v₀) fun s hs ↦ ?_, pow_zero, pathWeight_def,
      ite_eq_left ((isWalkFrom_zero (v₀ := v₀) _).2 rfl), div_self (hr v₀), one_pow]
    rw [pathWeight_def, ite_eq_right fun h ↦ hs (funext fun i ↦ by
      rw [Fin.fin_one_eq_zero i]; exact h.apply_zero)]
  | succ n ih =>
    rw [Fintype.sum_fin_snoc, Finset.sum_congr rfl fun t _ ↦ sum_pathWeight_snoc hδ t,
      ← Finset.mul_sum, ih (hδ.mono (Nat.le_succ n)), pow_succ, mul_comm]

/-- The weight matrix of the path model commutes with the path representation, since the latter
preserves walks and their endpoints. -/
theorem commute_diagonal_pathWeight_pathRep (hδ : IsPathEigenvectorUpTo G v₀ r δ n)
    (x : TemperleyLieb K δ n) :
    Commute (diagonal (pathWeight G v₀ r)) (pathRep G v₀ hr hδ x) := by
  ext s t
  rw [diagonal_mul, mul_diagonal]
  by_cases h : (G.IsWalkFrom v₀ s ↔ G.IsWalkFrom v₀ t) ∧ s (Fin.last n) = t (Fin.last n)
  · rw [pathWeight_def, pathWeight_def, if_congr h.1 (by rw [h.2]) rfl, mul_comm]
  · rw [pathRep_apply_eq_zero hr hδ x h, mul_zero, zero_mul]

/-- **The trace property** of the trace of the path model. -/
theorem pathTrace_mul_comm (hδ : IsPathEigenvectorUpTo G v₀ r δ n)
    (x y : TemperleyLieb K δ n) :
    pathTrace G v₀ hr hδ (x * y) = pathTrace G v₀ hr hδ (y * x) := by
  rw [pathTrace_apply, pathTrace_apply, map_mul, map_mul, ← mul_assoc,
    (commute_diagonal_pathWeight_pathRep hr hδ x).eq, mul_assoc, trace_mul_comm, mul_assoc]

/-- On the diagonal weighted by walks, the path representation of `strandIncl x` agrees with
`extendLast` of the path representation of `x`. -/
private theorem pathWeight_mul_pathRep_strandIncl (hδ : IsPathEigenvectorUpTo G v₀ r δ (n + 2))
    (x : TemperleyLieb K δ (n + 1)) (s t : Fin (n + 3) → V) :
    pathWeight G v₀ r s * pathRep G v₀ hr hδ (strandIncl x) s t =
      pathWeight G v₀ r s *
        extendLast (α := fun _ ↦ V) (pathRep G v₀ hr (hδ.mono (Nat.le_succ (n + 1))) x) s t := by
  by_cases hs : G.IsWalkFrom v₀ s
  · rw [pathRep_strandIncl_apply hr hδ x hs]
  · rw [pathWeight_def, ite_eq_right hs, zero_mul, zero_mul]

/-- Adding a straight strand multiplies the trace of the path model by `δ`. -/
@[simp]
theorem pathTrace_strandIncl (hδ : IsPathEigenvectorUpTo G v₀ r δ (n + 2))
    (x : TemperleyLieb K δ (n + 1)) :
    pathTrace G v₀ hr hδ (strandIncl x) =
      δ * pathTrace G v₀ hr (hδ.mono (Nat.le_succ (n + 1))) x := by
  simp only [pathTrace_apply, trace, Matrix.diag_apply, diagonal_mul]
  rw [Finset.sum_congr rfl fun s _ ↦ pathWeight_mul_pathRep_strandIncl hr hδ x s s,
    Fintype.sum_fin_snoc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  simp only [extendLast_apply, Fin.init_snoc, ite_true]
  rw [← Finset.sum_mul, sum_pathWeight_snoc hδ, mul_assoc]

/-- The weighted partial trace over the last step of walks, against the generator matrix capping
the last step with the previous one, recovers the weighted trace one level down. -/
private theorem trace_pathGenerator_mul_pathRep_strandIncl
    (hδ : IsPathEigenvectorUpTo G v₀ r δ (n + 2)) (x : TemperleyLieb K δ (n + 1))
    {a b c : Fin (n + 3)} (ha : a.val = n) (hb : b.val = n + 1) (hc : c.val = n + 2) :
    trace (pathGenerator G v₀ r a b c *
        (diagonal (pathWeight G v₀ r) * pathRep G v₀ hr hδ (strandIncl x))) =
      trace (diagonal (pathWeight G v₀ r) *
        pathRep G v₀ hr (hδ.mono (Nat.le_succ (n + 1))) x) := by
  obtain ⟨a', rfl, ha'⟩ : ∃ a' : Fin (n + 2), a = a'.castSucc ∧ a'.val = n :=
    ⟨⟨n, by omega⟩, Fin.ext ha, rfl⟩
  obtain rfl : b = (Fin.last (n + 1)).castSucc := Fin.ext hb
  obtain rfl : c = Fin.last (n + 2) := Fin.ext hc
  simp only [trace, Matrix.diag_apply, pathGenerator_mul_apply, diagonal_mul]
  rw [Fintype.sum_fin_snoc]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  simp only [Fin.snoc_castSucc, Fin.snoc_last, isWalkFrom_snoc]
  have ha'l : a'.val + 1 = (Fin.last (n + 1)).val := by simp [ha']
  by_cases ht : G.IsWalkFrom v₀ t
  swap
  · -- Neither side sees a sequence that is not a walk.
    rw [Finset.sum_eq_zero fun y _ ↦ by rw [ite_eq_right fun h ↦ ht h.1.1], pathWeight_def,
      ite_eq_right ht, zero_mul]
  have hadj := ht.adj ha'l
  rw [Fintype.sum_eq_single (t a') fun y hy ↦ ite_eq_right fun h ↦ hy h.2.symm,
    ite_eq_left ⟨⟨ht, hadj.symm⟩, rfl⟩]
  -- Only the move of the vertex at the penultimate position back to `t (Fin.last _)` survives.
  rw [Fin.snoc_castSucc]
  rw [Finset.sum_eq_single_of_mem (t (Fin.last (n + 1))) ((G.mem_neighborFinset _ _).2 hadj)
    fun z _ hz ↦ by
      rw [← Fin.snoc_update, pathWeight_mul_pathRep_strandIncl hr hδ x, extendLast_apply,
        Fin.init_snoc, Fin.init_snoc, Fin.snoc_last, Fin.snoc_last, ite_eq_left rfl,
        pathRep_apply_eq_zero hr (hδ.mono (Nat.le_succ (n + 1))) x fun h ↦ hz (by simpa using h.2),
        mul_zero, mul_zero]]
  rw [update_eq_self_iff.2 (Fin.snoc_castSucc ..).symm, pathWeight_mul_pathRep_strandIncl hr hδ x,
    extendLast_apply, ite_eq_left rfl, Fin.init_snoc, pathWeight_def, pathWeight_def,
    ite_eq_left ((isWalkFrom_snoc t _).2 ⟨ht, hadj.symm⟩), ite_eq_left ht, Fin.snoc_last]
  have := hr (t a')
  field_simp

/-- **The Markov property** of the trace of the path model: capping the added last strand with the
previous one does not change the trace. -/
@[simp]
theorem pathTrace_strandIncl_mul_e_last (hδ : IsPathEigenvectorUpTo G v₀ r δ (n + 2))
    (x : TemperleyLieb K δ (n + 1)) :
    pathTrace G v₀ hr hδ (strandIncl x * e δ (Fin.last n)) =
      pathTrace G v₀ hr (hδ.mono (Nat.le_succ (n + 1))) x := by
  rw [pathTrace_apply, pathTrace_apply, map_mul, pathRep_e, ← mul_assoc, trace_mul_comm]
  exact trace_pathGenerator_mul_pathRep_strandIncl hr hδ x rfl rfl rfl

variable (G v₀) in
/-- Given the eigenvector equation up to `n` steps, the trace of the path model is an unnormalized
Markov trace up to `n` strands. -/
theorem isMarkovTraceUpTo_pathTrace (hδ : IsPathEigenvectorUpTo G v₀ r δ n) :
    IsMarkovTraceUpTo K δ n (fun _ hm ↦ pathTrace G v₀ hr (hδ.mono hm)) :=
  ⟨fun _ hm ↦ pathTrace_one hr (hδ.mono hm),
    fun _ hm x y ↦ pathTrace_mul_comm hr (hδ.mono hm) x y,
    fun _ hm x ↦ pathTrace_strandIncl hr (hδ.mono hm) x,
    fun _ hm x ↦ pathTrace_strandIncl_mul_e_last hr (hδ.mono hm) x⟩

variable (G v₀) in
/-- Given the eigenvector equation up to `n` steps, every Markov trace on the full tower agrees on
`m ≤ n` strands with the trace of the path model. -/
theorem IsMarkovTrace.eq_pathTrace_of_isPathEigenvectorUpTo
    {tr : ∀ k : ℕ, TemperleyLieb K δ k →ₗ[K] K} (htr : IsMarkovTrace K δ tr)
    (hδ : IsPathEigenvectorUpTo G v₀ r δ n) {m : ℕ} (hm : m ≤ n) :
    tr m = pathTrace G v₀ hr (hδ.mono hm) :=
  htr.eq_of_isMarkovTraceUpTo (isMarkovTraceUpTo_pathTrace G v₀ hr hδ) hm

variable (G v₀) in
/-- Under a global adjacency eigenvector, the trace of the path model is an unnormalized Markov
trace on the full tower. -/
theorem isMarkovTrace_pathTrace (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) :
    IsMarkovTrace K δ (fun m ↦ pathTrace G v₀ hr (.of_forall hδ m)) :=
  ⟨fun m ↦ pathTrace_one hr (.of_forall hδ m),
    fun m x y ↦ pathTrace_mul_comm hr (.of_forall hδ m) x y,
    fun m x ↦ pathTrace_strandIncl hr (.of_forall hδ (m + 2)) x,
    fun m x ↦ pathTrace_strandIncl_mul_e_last hr (.of_forall hδ (m + 2)) x⟩

variable (G v₀) in
/-- Under a global adjacency eigenvector, every Markov trace at the loop value `δ` is the trace of
the path model, by uniqueness of Markov traces. -/
theorem IsMarkovTrace.eq_pathTrace {tr : ∀ n : ℕ, TemperleyLieb K δ n →ₗ[K] K}
    (htr : IsMarkovTrace K δ tr)
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) :
    tr = fun m ↦ pathTrace G v₀ hr (.of_forall hδ m) :=
  htr.unique (isMarkovTrace_pathTrace G v₀ hr hδ)

end Trace

section Star

variable [StarRing K]

omit [Fintype V] in
/-- For self-adjoint weights `r`, the generator matrices of the path model are self-adjoint. -/
theorem conjTranspose_pathGenerator (hrs : ∀ v, IsSelfAdjoint (r v)) {m : ℕ}
    {a b c : Fin (m + 1)} (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) :
    (pathGenerator G v₀ r a b c)ᴴ = pathGenerator G v₀ r a b c :=
  conjTranspose_walkGenerator hrs id (G.IsWalkFrom v₀) hab hbc id
    fun {s t} hs hac hst hadj ↦ by
      have hst' : t = update s b (t b) := hst
      rw [hst']; exact hs.update hab hbc hac hadj

variable (hr : ∀ v, r v ≠ 0) (hrs : ∀ v, IsSelfAdjoint (r v)) {δ : K} [Fact (IsSelfAdjoint δ)]
  {n : ℕ}

include hrs in
/-- For self-adjoint weights `r`, the path representation carries the analytic adjoint of the
Temperley–Lieb algebra to the conjugate transpose of matrices. -/
@[simp]
theorem pathRep_star (hδ : IsPathEigenvectorUpTo G v₀ r δ n) (x : TemperleyLieb K δ n) :
    pathRep G v₀ hr hδ (star x) = (pathRep G v₀ hr hδ x)ᴴ := by
  refine (map_star_iff.mpr fun i ↦ ?_) x
  rw [pathRep_e, IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_pathGenerator hrs rfl rfl]

variable [PartialOrder K] [StarOrderedRing K]

omit [Fintype V] in
include hrs in
/-- For self-adjoint weights `r`, every vertex sequence has nonnegative weight. -/
theorem pathWeight_nonneg {m : ℕ} (s : Fin (m + 1) → V) : 0 ≤ pathWeight G v₀ r s := by
  rw [pathWeight_def]
  split_ifs
  · exact ((hrs _).div (hrs _)).sq_nonneg
  · exact le_rfl

omit [Fintype V] in
include hr hrs in
/-- For nonzero self-adjoint weights `r`, every walk from `v₀` has positive weight. -/
theorem pathWeight_pos {m : ℕ} {s : Fin (m + 1) → V} (hs : G.IsWalkFrom v₀ s) :
    0 < pathWeight G v₀ r s := by
  rw [pathWeight_def, ite_eq_left hs]
  have h := mul_star_self_pos_iff.2 (div_ne_zero (hr (s (Fin.last m))) (hr v₀))
  rwa [((hrs _).div (hrs _)).star_eq, ← sq] at h

include hrs in
/-- **Positivity of the trace of the path model.** For self-adjoint weights `r`, the trace of the
path model is nonnegative on every element of the form `x⋆ * x`. -/
theorem pathTrace_star_mul_self_nonneg (hδ : IsPathEigenvectorUpTo G v₀ r δ n)
    (x : TemperleyLieb K δ n) :
    0 ≤ pathTrace G v₀ hr hδ (star x * x) := by
  -- The trace of `D * Aᴴ * A` is the trace of `A * D * Aᴴ`, with `D` a nonnegative diagonal.
  rw [pathTrace_apply, map_mul, pathRep_star hr hrs, ← mul_assoc, trace_mul_comm, ← mul_assoc]
  exact ((posSemidef_diagonal_iff.2 fun s ↦ pathWeight_nonneg hrs s).mul_mul_conjTranspose_same
    _).trace_nonneg

omit [DecidableEq V] in
include hr hrs in
/-- **Bounded-depth positivity of a Markov trace from a path model.** Let `G` be a finite graph
with a base vertex `v₀` and a vertex weighting `r` by nonzero self-adjoint scalars whose squares
satisfy the adjacency eigenvector equation with eigenvalue `δ` at the endpoints of all walks from
`v₀` with fewer than `n` steps. Then on `n` strands every Markov trace at the loop value `δ` is
nonnegative on every element of the form `x⋆ * x`. -/
theorem IsMarkovTrace.map_star_mul_self_nonneg_of_isPathEigenvectorUpTo
    (hδ : IsPathEigenvectorUpTo G v₀ r δ n)
    {tr : ∀ k : ℕ, TemperleyLieb K δ k →ₗ[K] K} (htr : IsMarkovTrace K δ tr)
    (x : TemperleyLieb K δ n) : 0 ≤ tr n (star x * x) := by
  classical
  rw [htr.eq_pathTrace_of_isPathEigenvectorUpTo G v₀ hr hδ le_rfl]
  exact pathTrace_star_mul_self_nonneg hr hrs hδ x

omit [DecidableEq V] in
include hr hrs in
/-- **Positivity of a Markov trace from a path model.** Let `G` be a nonempty finite graph with a
vertex weighting `r` by nonzero self-adjoint scalars whose squares form an eigenvector of the
adjacency matrix with eigenvalue `δ`. Then every Markov trace at the loop value `δ` is nonnegative
on every element of the form `x⋆ * x`. -/
theorem IsMarkovTrace.map_star_mul_self_nonneg_of_graph [Nonempty V]
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2)
    {tr : ∀ k : ℕ, TemperleyLieb K δ k →ₗ[K] K} (htr : IsMarkovTrace K δ tr)
    (x : TemperleyLieb K δ n) : 0 ≤ tr n (star x * x) :=
  htr.map_star_mul_self_nonneg_of_isPathEigenvectorUpTo hr hrs
    (.of_forall (v₀ := Classical.arbitrary V) hδ n) x

end Star

section Walk

variable (hr : ∀ v, r v ≠ 0) {δ : K} {n : ℕ}

variable (G v₀) in
/-- The **path representation on walks**: the path representation of the Temperley–Lieb algebra
on `n` strands, restricted to the functions supported on the walks in `G` from `v₀` with `n`
steps. This subspace is invariant, since a row of a walk has no entries in the columns of other
vertex sequences (`TauCeti.TemperleyLieb.pathRep_apply_eq_zero`), so the restriction is again an
algebra map. -/
def walkRep (hδ : IsPathEigenvectorUpTo G v₀ r δ n) :
    TemperleyLieb K δ n →ₐ[K]
      Matrix {s : Fin (n + 1) → V // G.IsWalkFrom v₀ s} {s : Fin (n + 1) → V // G.IsWalkFrom v₀ s}
        K where
  toFun x := (pathRep G v₀ hr hδ x).submatrix Subtype.val Subtype.val
  map_one' := by rw [map_one, submatrix_one _ Subtype.val_injective]
  map_mul' x y := by
    ext s t
    rw [map_mul, submatrix_apply, Matrix.mul_apply, Matrix.mul_apply,
      ← Fintype.sum_subtype_add_sum_subtype (G.IsWalkFrom v₀)]
    -- The columns of other vertex sequences do not contribute to a row of a walk.
    have h0 : ∑ u : {u // ¬G.IsWalkFrom v₀ u},
        pathRep G v₀ hr hδ x s.val u.val * pathRep G v₀ hr hδ y u.val t.val = 0 :=
      Finset.sum_eq_zero fun u _ ↦ by
        rw [pathRep_apply_eq_zero hr hδ x fun h ↦ u.property (h.1.1 s.property), zero_mul]
    rw [h0, add_zero]
    simp only [submatrix_apply]
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
  commutes' k := by
    ext s t
    simp [algebraMap_matrix_apply, Subtype.ext_iff]

/-- The entries of the path representation on walks are those of the path representation. -/
@[simp]
theorem walkRep_apply (hδ : IsPathEigenvectorUpTo G v₀ r δ n) (x : TemperleyLieb K δ n)
    (s t : {s : Fin (n + 1) → V // G.IsWalkFrom v₀ s}) :
    walkRep G v₀ hr hδ x s t = pathRep G v₀ hr hδ x s t :=
  (rfl)

/-- The path representation on walks preserves endpoints: its entry at the walks `s` and `t`
vanishes unless they end at the same vertex. -/
theorem walkRep_apply_eq_zero (hδ : IsPathEigenvectorUpTo G v₀ r δ n) (x : TemperleyLieb K δ n)
    {s t : {s : Fin (n + 1) → V // G.IsWalkFrom v₀ s}}
    (h : s.val (Fin.last n) ≠ t.val (Fin.last n)) : walkRep G v₀ hr hδ x s t = 0 :=
  pathRep_apply_eq_zero hr hδ x fun h' ↦ h h'.2

/-- On walks, adding a straight strand extends walks by one step: the entry of the path
representation on walks of `strandIncl x` at two walks is the entry of `x` at their initial
segments when they end at the same vertex, and `0` otherwise. -/
theorem walkRep_strandIncl_apply (hδ : IsPathEigenvectorUpTo G v₀ r δ (n + 2))
    (x : TemperleyLieb K δ (n + 1)) (s t : {s : Fin (n + 3) → V // G.IsWalkFrom v₀ s}) :
    walkRep G v₀ hr hδ (strandIncl x) s t =
      if s.val (Fin.last (n + 2)) = t.val (Fin.last (n + 2)) then
        walkRep G v₀ hr (hδ.mono (Nat.le_succ (n + 1))) x ⟨Fin.init s.val, s.property.init⟩
          ⟨Fin.init t.val, t.property.init⟩
      else 0 := by
  rw [walkRep_apply, pathRep_strandIncl_apply hr hδ x s.property, extendLast_apply, walkRep_apply]

/-- The last generator on walks with two final steps: its entry at the walks `p a b` and
`p' a' b'` is `r a * r a' / r b ^ 2` when the walks agree up to their penultimate vertex and return
in their last step to the vertex `p (Fin.last n) = b` they left, and `0` otherwise. -/
theorem walkRep_e_last_apply_snoc_snoc (hδ : IsPathEigenvectorUpTo G v₀ r δ (n + 2))
    {p p' : Fin (n + 1) → V} {a a' b b' : V}
    (hs : G.IsWalkFrom v₀ (Fin.snoc (Fin.snoc p a : Fin (n + 2) → V) b : Fin (n + 3) → V))
    (ht : G.IsWalkFrom v₀ (Fin.snoc (Fin.snoc p' a' : Fin (n + 2) → V) b' : Fin (n + 3) → V)) :
    walkRep G v₀ hr hδ (e δ (Fin.last n)) ⟨_, hs⟩ ⟨_, ht⟩ =
      if p = p' ∧ p (Fin.last n) = b ∧ b' = b then r a * r a' / r b ^ 2 else 0 := by
  have h₀ : (⟨(Fin.last n : ℕ), by omega⟩ : Fin (n + 3)) = (Fin.last n).castSucc.castSucc :=
    Fin.ext (by simp)
  have h₁ : (⟨(Fin.last n : ℕ) + 1, by omega⟩ : Fin (n + 3)) = (Fin.last (n + 1)).castSucc :=
    Fin.ext (by simp)
  have h₂ : (⟨(Fin.last n : ℕ) + 2, by omega⟩ : Fin (n + 3)) = Fin.last (n + 2) :=
    Fin.ext (by simp)
  rw [walkRep_apply, pathRep_e, pathGenerator_apply, h₀, h₁, h₂]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, ← Fin.snoc_update, Fin.update_snoc_last,
    Fin.snoc_inj, hs, true_and]
  have hadj : G.Adj (p' (Fin.last n)) a' := by
    simpa using ht.adj (a := (Fin.last n).castSucc.castSucc) (b := (Fin.last (n + 1)).castSucc)
      (by simp)
  by_cases h : p = p' ∧ p (Fin.last n) = b ∧ b' = b
  · obtain ⟨rfl, rfl, rfl⟩ := h
    simp [hadj]
  · split_ifs <;> simp_all

/-- The trace of the path model is the trace of the path representation on walks, weighted by
`TauCeti.TemperleyLieb.pathWeight`: the walks ending at `v` have weight `(r v / r v₀) ^ 2`. -/
theorem pathTrace_eq_trace_walkRep (hδ : IsPathEigenvectorUpTo G v₀ r δ n)
    (x : TemperleyLieb K δ n) :
    pathTrace G v₀ hr hδ x =
      trace (diagonal (fun s : {s : Fin (n + 1) → V // G.IsWalkFrom v₀ s} ↦
        pathWeight G v₀ r s.val) * walkRep G v₀ hr hδ x) := by
  rw [pathTrace_apply, trace, trace, ← Fintype.sum_subtype_add_sum_subtype (G.IsWalkFrom v₀)]
  -- Every vertex sequence other than a walk has weight `0`.
  have h0 : ∑ s : {s // ¬G.IsWalkFrom v₀ s},
      (diagonal (pathWeight G v₀ r) * pathRep G v₀ hr hδ x).diag s.val = 0 :=
    Finset.sum_eq_zero fun s _ ↦ by
      rw [Matrix.diag_apply, diagonal_mul, pathWeight_def, ite_eq_right s.property, zero_mul]
  rw [h0, add_zero]
  simp only [Matrix.diag_apply, diagonal_mul, walkRep_apply]

section Star

variable [StarRing K] (hrs : ∀ v, IsSelfAdjoint (r v))

include hrs in
/-- For self-adjoint weights `r`, the path representation on walks carries the analytic adjoint
of the Temperley–Lieb algebra to the conjugate transpose of matrices. -/
@[simp]
theorem walkRep_star [Fact (IsSelfAdjoint δ)] (hδ : IsPathEigenvectorUpTo G v₀ r δ n)
    (x : TemperleyLieb K δ n) :
    walkRep G v₀ hr hδ (star x) = (walkRep G v₀ hr hδ x)ᴴ := by
  ext s t
  rw [walkRep_apply, pathRep_star hr hrs, conjTranspose_apply, conjTranspose_apply, walkRep_apply]

include hrs in
/-- For self-adjoint weights `r`, the image of the path representation on walks is closed under
the conjugate transpose, since it is generated by self-adjoint matrices. Unlike
`TauCeti.TemperleyLieb.walkRep_star`, this needs no analytic adjoint on the Temperley–Lieb
algebra. -/
theorem conjTranspose_mem_range_walkRep (hδ : IsPathEigenvectorUpTo G v₀ r δ n)
    (x : TemperleyLieb K δ n) : (walkRep G v₀ hr hδ x)ᴴ ∈ (walkRep G v₀ hr hδ).range := by
  rw [AlgHom.mem_range]
  induction x using TemperleyLieb.induction with
  | e i =>
    refine ⟨e δ i, ?_⟩
    ext s t
    rw [conjTranspose_apply, walkRep_apply, walkRep_apply, pathRep_e, ← conjTranspose_apply,
      conjTranspose_pathGenerator hrs rfl rfl]
  | algebraMap k =>
    refine ⟨algebraMap K _ (star k), ?_⟩
    ext s t
    simp [algebraMap_matrix_apply, Subtype.ext_iff, apply_ite star, eq_comm]
  | add x y hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by rw [map_add, map_add, hx', hy', conjTranspose_add]⟩
  | mul x y hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨y' * x', by rw [map_mul, map_mul, hx', hy', conjTranspose_mul]⟩

variable [PartialOrder K] [StarOrderedRing K]

include hrs in
/-- **The kernel of the path representation on walks is the trace radical.** For nonzero
self-adjoint weights `r`, an element of the Temperley–Lieb algebra on `n` strands acts by zero on
the walks from `v₀` exactly when it lies in the trace radical of the trace of the path model. -/
theorem ker_walkRep (hδ : IsPathEigenvectorUpTo G v₀ r δ n) :
    RingHom.ker (walkRep G v₀ hr hδ) =
      (pathTrace G v₀ hr hδ).traceRadical (pathTrace_mul_comm hr hδ) := by
  ext x
  rw [RingHom.mem_ker, LinearMap.mem_traceRadical]
  refine ⟨fun hx y ↦ by rw [pathTrace_eq_trace_walkRep, map_mul, hx, zero_mul, mul_zero,
    trace_zero], fun hx ↦ ?_⟩
  -- For `y` acting by the conjugate transpose of `x`, the trace of `x * y` is the weighted
  -- squared Hilbert–Schmidt norm of `(walkRep x)ᴴ`.
  obtain ⟨y, hy⟩ := (AlgHom.mem_range _).1 (conjTranspose_mem_range_walkRep hr hrs hδ x)
  rw [← conjTranspose_eq_zero, ← trace_diagonal_mul_conjTranspose_mul_self_eq_zero_iff
    fun s ↦ pathWeight_pos hr hrs s.property,
    conjTranspose_conjTranspose, ← hy, ← map_mul, ← pathTrace_eq_trace_walkRep]
  exact hx y

include hrs in
/-- **The kernel of the path representation on walks is the trace radical of every Markov
trace.** For nonzero self-adjoint weights `r` satisfying the eigenvector equation up to depth `n`,
an element of the Temperley–Lieb algebra on `n` strands acts by zero on the walks from `v₀` exactly
when it lies in the trace radical of a Markov trace at the loop value `δ`. Hence the trace-radical
quotient on `n` strands is isomorphic to the image of the path representation on walks
(`Ideal.kerLiftAlg`). -/
theorem IsMarkovTrace.ker_walkRep {tr : ∀ k : ℕ, TemperleyLieb K δ k →ₗ[K] K}
    (htr : IsMarkovTrace K δ tr) (hδ : IsPathEigenvectorUpTo G v₀ r δ n) :
    RingHom.ker (walkRep G v₀ hr hδ) = (tr n).traceRadical (htr.map_mul_comm n) := by
  rw [TemperleyLieb.ker_walkRep hr hrs]
  ext x
  simp only [LinearMap.mem_traceRadical,
    htr.eq_pathTrace_of_isPathEigenvectorUpTo G v₀ hr hδ le_rfl]

end Star

end Walk

end TauCeti.TemperleyLieb
