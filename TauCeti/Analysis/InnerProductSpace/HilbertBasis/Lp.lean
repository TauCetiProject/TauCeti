/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Basic.Denumerable
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic

/-!
# Hilbert bases of Hilbert direct sums

Given a Hilbert basis `b i` of each summand `E i` of an `ℓ²` Hilbert direct sum `lp E 2`, the
coordinate embeddings `⟨i, k⟩ ↦ lp.single 2 i (b i k)` form a Hilbert basis `lp.hilbertBasis b`
indexed by `Σ i, κ i`. Its coordinate representation reads the `b i`-coordinates in the `i`-th
summand (`lp.hilbertBasis_repr_apply`). Completeness of each summand is inferred from its Hilbert
basis.

For a countably infinite family of nontrivial separable Hilbert spaces `E i` (in particular, the
countable Hilbert sum `lp (fun _ : ℕ => H) 2` of a nontrivial separable Hilbert space, whether `H`
is finite- or infinite-dimensional), the assembled basis index type is countably infinite, yielding
a Hilbert basis indexed by `ℕ` (`lp.exists_hilbertBasis_nat`) and hence a linear isometric
equivalence with `ℓ²(ℕ, 𝕜)`.

## Main declarations

* `lp.hilbertBasis`: Hilbert basis of `lp E 2` assembled from Hilbert bases of the summands.
* `lp.hilbertBasis_apply`, `lp.hilbertBasis_repr_apply`: basis vectors and coordinate formula.
* `lp.exists_hilbertBasis_nat`: a countably infinite Hilbert sum of nontrivial separable Hilbert
  spaces admits a Hilbert basis indexed by `ℕ`.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer GTM 96, 1990, §I.4 and §II.1.
-/

public section

noncomputable section

open scoped ENNReal InnerProductSpace

namespace lp

section DirectSum

variable {ι 𝕜 : Type*} {E : ι → Type*} {κ : ι → Type*} [RCLike 𝕜]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]

private theorem orthonormal_single_hilbertBasis [DecidableEq ι]
    (b : ∀ i, HilbertBasis (κ i) 𝕜 (E i)) :
    Orthonormal 𝕜 (fun p : Σ i, κ i => lp.single (E := E) 2 p.1 (b p.1 p.2)) := by
  classical
  refine orthonormal_iff_ite.2 fun p q => ?_
  rw [lp.inner_single_left]
  rcases p with ⟨i, k⟩
  rcases q with ⟨j, l⟩
  by_cases hij : i = j
  · subst hij
    simpa [Sigma.mk.inj_iff] using (orthonormal_iff_ite.1 (b i).orthonormal k l)
  · simp [hij]

private theorem orthogonal_span_range_single_hilbertBasis [DecidableEq ι]
    (b : ∀ i, HilbertBasis (κ i) 𝕜 (E i)) :
    (Submodule.span 𝕜 (Set.range fun p : Σ i, κ i =>
      lp.single (E := E) 2 p.1 (b p.1 p.2)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  ext i
  refine (b i).repr.injective ?_
  ext k
  have hmem : lp.single (E := E) 2 i (b i k) ∈
      Submodule.span 𝕜 (Set.range fun p : Σ i, κ i => lp.single (E := E) 2 p.1 (b p.1 p.2)) :=
    Submodule.subset_span ⟨⟨i, k⟩, rfl⟩
  have h0 := (Submodule.mem_orthogonal _ _).1 hx _ hmem
  simpa only [lp.inner_single_left, HilbertBasis.repr_apply_apply, map_zero, lp.coeFn_zero,
    Pi.zero_apply] using h0

/-- The Hilbert basis of the Hilbert direct sum `lp E 2` assembled from a Hilbert basis `b i` of
each summand `E i`. -/
def hilbertBasis (b : ∀ i, HilbertBasis (κ i) 𝕜 (E i)) :
    HilbertBasis (Σ i, κ i) 𝕜 (lp E 2) := by
  classical
  haveI : ∀ i, CompleteSpace (E i) := fun i => (b i).completeSpace
  exact HilbertBasis.mkOfOrthogonalEqBot (orthonormal_single_hilbertBasis b)
    (orthogonal_span_range_single_hilbertBasis b)

/-- The `⟨i, k⟩`-th vector of `lp.hilbertBasis b` is `lp.single 2 i (b i k)`. -/
@[simp]
theorem hilbertBasis_apply [DecidableEq ι] (b : ∀ i, HilbertBasis (κ i) 𝕜 (E i)) (p : Σ i, κ i) :
    lp.hilbertBasis b p = lp.single 2 p.1 (b p.1 p.2) := by
  have : ∀ i, CompleteSpace (E i) := fun i => (b i).completeSpace
  rw [hilbertBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]
  ext j
  by_cases hj : j = p.1
  · subst hj; simp
  · simp [hj]

/-- The `⟨i, k⟩`-th coordinate of `x : lp E 2` in `lp.hilbertBasis b` is the `k`-th coordinate of
`x i` in `b i`. -/
@[simp]
theorem hilbertBasis_repr_apply (b : ∀ i, HilbertBasis (κ i) 𝕜 (E i)) (x : lp E 2)
    (p : Σ i, κ i) :
    (lp.hilbertBasis b).repr x p = (b p.1).repr (x p.1) p.2 := by
  classical
  rw [HilbertBasis.repr_apply_apply, hilbertBasis_apply, lp.inner_single_left,
    HilbertBasis.repr_apply_apply]

end DirectSum

section CountableInfinite

variable {ι 𝕜 : Type*} {E : ι → Type*} [RCLike 𝕜]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]

/-- A countably infinite Hilbert direct sum of nontrivial separable complete Hilbert spaces admits
a Hilbert basis indexed by `ℕ`, and hence is unitarily equivalent to `ℓ²(ℕ, 𝕜)` via its coordinate
representation. -/
theorem exists_hilbertBasis_nat [Countable ι] [Infinite ι]
    [∀ i, CompleteSpace (E i)] [∀ i, TopologicalSpace.SeparableSpace (E i)]
    [∀ i, Nontrivial (E i)] :
    Nonempty (HilbertBasis ℕ 𝕜 (lp E 2)) := by
  classical
  choose w b _ using fun i : ι => exists_hilbertBasis 𝕜 (E i)
  have hw_nonempty : ∀ i, Nonempty (w i) := fun i => by
    by_contra h
    rw [not_nonempty_iff] at h
    have : Subsingleton (E i) := (b i).repr.injective.subsingleton
    exact false_of_nontrivial_of_subsingleton (E i)
  have : ∀ i, Countable (w i) := fun i => by
    refine Pairwise.countable_of_isOpen_disjoint
      (s := fun k : w i => Metric.ball (b i k) (1 / 2)) ?_ (fun _ => Metric.isOpen_ball)
      (fun k => Metric.nonempty_ball.2 (by norm_num))
    intro k l hkl
    rw [Function.onFun, Set.disjoint_left]
    intro x hxk hxl
    have hsq : ‖b i k - b i l‖ ^ 2 = 2 := by
      rw [norm_sub_sq (𝕜 := 𝕜), (b i).orthonormal.1 k, (b i).orthonormal.1 l,
        (b i).orthonormal.2 hkl]
      norm_num
    have hdist : dist (b i k) (b i l) < 1 := by
      have htri := dist_triangle_left (b i k) (b i l) x
      rw [Metric.mem_ball] at hxk hxl
      linarith
    rw [dist_eq_norm] at hdist
    nlinarith [norm_nonneg (b i k - b i l)]
  have : Infinite (Σ i, w i) :=
    Infinite.of_injective (fun i => ⟨i, (hw_nonempty i).some⟩) fun _ _ h =>
      congrArg Sigma.fst h
  obtain ⟨e⟩ := nonempty_equiv_of_countable (α := ℕ) (β := Σ i, w i)
  let B := lp.hilbertBasis b
  refine ⟨HilbertBasis.mk (B.orthonormal.comp e e.injective) ?_⟩
  rw [Set.range_comp, e.surjective.range_eq, Set.image_univ]
  exact B.dense_span.ge

end CountableInfinite

end lp
