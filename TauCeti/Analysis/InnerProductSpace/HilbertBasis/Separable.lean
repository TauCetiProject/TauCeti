/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Basic.Denumerable
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic
import TauCeti.Analysis.Normed.Lp.Basic

/-!
# Separable Hilbert spaces and `ℕ`-indexed Hilbert bases

Distinct vectors in an orthonormal family lie at pairwise distance `√2`
(`Orthonormal.dist_eq_sqrt_two`), so the open balls of radius `√2 / 2` around them are pairwise
disjoint. In a separable inner product space every orthonormal family is therefore countable
(`Orthonormal.countable`).

For a Hilbert basis `b : HilbertBasis ι 𝕜 E`, this identifies topological and algebraic properties
of `E` with set-theoretic properties of the index type `ι`:

* `HilbertBasis.separableSpace_iff`: `E` is separable iff `ι` is countable.
* `HilbertBasis.finite_iff` and `HilbertBasis.infinite_iff`: `E` is finite-dimensional iff `ι` is
  finite, and infinite-dimensional iff `ι` is infinite.
* `HilbertBasis.reindex`: reindexing `b` along an equivalence `ι ≃ ι'`.

Combining Zorn's-lemma existence of a Hilbert basis (`exists_hilbertBasis`) with Cantor's
bijection between countably infinite types (`nonempty_equiv_of_countable`) yields a `ℕ`-indexed
Hilbert basis on every complete separable infinite-dimensional Hilbert space
(`TauCeti.nonempty_hilbertBasis_nat`), and hence a linear isometric equivalence `E ≃ₗᵢ[𝕜] ℓ²(ℕ, 𝕜)`
(`TauCeti.nonempty_linearIsometryEquiv_lp_nat`).

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer GTM 96, 1990, §I.4.
-/

public section

open TopologicalSpace
open scoped InnerProductSpace lp

section Orthonormal

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Distinct vectors in an orthonormal family lie at distance `√2`. -/
theorem Orthonormal.dist_eq_sqrt_two {v : ι → E} (hv : Orthonormal 𝕜 v) {i j : ι} (hij : i ≠ j) :
    dist (v i) (v j) = Real.sqrt 2 := by
  have hsq : ‖v i - v j‖ ^ 2 = 2 := by
    rw [@norm_sub_sq 𝕜, hv.norm_eq_one i, hv.norm_eq_one j, hv.inner_eq_zero hij, map_zero]
    norm_num
  rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _), hsq]

/-- In a separable inner product space, every orthonormal family is countable: the open balls of
radius `√2 / 2` around its vectors are pairwise disjoint. -/
theorem Orthonormal.countable [SeparableSpace E] {v : ι → E} (hv : Orthonormal 𝕜 v) :
    Countable ι := by
  have hr : 0 < Real.sqrt 2 / 2 := by positivity
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i ↦ Metric.ball (v i) (Real.sqrt 2 / 2))
    (fun i j hij ↦ Set.disjoint_left.2 fun x hxi hxj ↦ ?_) (fun _ ↦ Metric.isOpen_ball)
    (fun i ↦ ⟨v i, Metric.mem_ball_self hr⟩)
  have hlt : dist (v i) (v j) < Real.sqrt 2 := by
    calc dist (v i) (v j) ≤ dist x (v i) + dist x (v j) := dist_triangle_left _ _ _
      _ < Real.sqrt 2 / 2 + Real.sqrt 2 / 2 := add_lt_add hxi hxj
      _ = Real.sqrt 2 := add_halves _
  exact hlt.ne (hv.dist_eq_sqrt_two hij)

/-- An inner product space admitting an infinite orthonormal family is infinite-dimensional. -/
theorem Orthonormal.not_finiteDimensional [Infinite ι] {v : ι → E} (hv : Orthonormal 𝕜 v) :
    ¬ FiniteDimensional 𝕜 E := fun _ ↦ by
  have := hv.linearIndependent.finite
  exact not_finite ι

end Orthonormal

section Lp

variable {ι 𝕜 : Type*} [RCLike 𝕜] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]

/-- Single-coordinate vectors built from unit vectors in each summand form an orthonormal family in
`lp E 2`. -/
theorem lp.orthonormal_single [DecidableEq ι] {v : ∀ i, E i} (hv : ∀ i, ‖v i‖ = 1) :
    Orthonormal 𝕜 fun i ↦ lp.single 2 i (v i) := by
  refine ⟨fun i ↦ by rw [lp.norm_single zero_lt_two, hv i], fun {i j} hij ↦ ?_⟩
  dsimp only
  rw [lp.inner_single_left, lp.coeFn_single, Pi.single_eq_of_ne hij, inner_zero_right]

/-- The Hilbert direct sum `lp E 2` of an infinite family of nontrivial inner product spaces is
infinite-dimensional. -/
theorem lp.not_finiteDimensional_two [Infinite ι] [∀ i, Nontrivial (E i)] :
    ¬ FiniteDimensional 𝕜 (lp E 2) := by
  classical
  have hunit : ∀ i, ∃ u : E i, ‖u‖ = 1 := fun i ↦ by
    obtain ⟨x, hx⟩ := exists_ne (0 : E i)
    exact ⟨(‖x‖ : 𝕜)⁻¹ • x, by simp [norm_smul, norm_inv, hx]⟩
  choose v hv using hunit
  exact (lp.orthonormal_single hv).not_finiteDimensional

end Lp

namespace HilbertBasis

variable {ι ι' ι'' 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A Hilbert basis of a separable space has a countable index type. -/
theorem countable [SeparableSpace E] (b : HilbertBasis ι 𝕜 E) : Countable ι :=
  b.orthonormal.countable

/-- A space admitting a countable Hilbert basis is separable, being isometric to `ℓ²(ι, 𝕜)`. -/
theorem separableSpace [Countable ι] (b : HilbertBasis ι 𝕜 E) : SeparableSpace E := by
  have : SeparableSpace (lp (fun _ : ι ↦ 𝕜) 2) := lp.separableSpace (by simp)
  exact b.repr.symm.surjective.denseRange.separableSpace b.repr.symm.continuous

/-- For a space with a Hilbert basis `b : HilbertBasis ι 𝕜 E`, separability of `E` is equivalent
to countability of `ι`. -/
theorem separableSpace_iff (b : HilbertBasis ι 𝕜 E) : SeparableSpace E ↔ Countable ι :=
  ⟨fun _ ↦ b.countable, fun _ ↦ b.separableSpace⟩

/-- A space with a finite Hilbert basis is finite-dimensional: the finite-dimensional span of the
basis is closed and dense, so it is the whole space. -/
theorem finiteDimensional [Finite ι] (b : HilbertBasis ι 𝕜 E) : FiniteDimensional 𝕜 E := by
  have : FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range b)) :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range b)
  have hclosed : IsClosed (Submodule.span 𝕜 (Set.range b) : Set E) :=
    Submodule.isClosed_of_finiteDimensional _
  have htop : Submodule.span 𝕜 (Set.range b) = ⊤ := by
    rw [← hclosed.submodule_topologicalClosure_eq]
    exact b.dense_span
  exact Module.Finite.equiv (LinearEquiv.ofTop _ htop)

/-- For a Hilbert basis `b : HilbertBasis ι 𝕜 E`, the index type `ι` is finite iff `E` is
finite-dimensional. -/
theorem finite_iff (b : HilbertBasis ι 𝕜 E) : Finite ι ↔ FiniteDimensional 𝕜 E :=
  ⟨fun _ ↦ b.finiteDimensional, fun _ ↦ b.orthonormal.linearIndependent.finite⟩

/-- For a Hilbert basis `b : HilbertBasis ι 𝕜 E`, the index type `ι` is infinite iff `E` is
infinite-dimensional. -/
theorem infinite_iff (b : HilbertBasis ι 𝕜 E) : Infinite ι ↔ ¬ FiniteDimensional 𝕜 E := by
  rw [← not_finite_iff_infinite, b.finite_iff]

private theorem dense_span_comp_symm (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') :
    ⊤ ≤ (Submodule.span 𝕜 (Set.range (b ∘ e.symm))).topologicalClosure := by
  rw [Set.range_comp, e.symm.surjective.range_eq, Set.image_univ]
  exact b.dense_span.ge

/-- Reindex a Hilbert basis along an equivalence of index types. -/
protected noncomputable def reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') :
    HilbertBasis ι' 𝕜 E :=
  letI := b.completeSpace
  HilbertBasis.mk (b.orthonormal.comp _ e.symm.injective) (b.dense_span_comp_symm e)

@[simp]
theorem coe_reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') :
    ⇑(b.reindex e) = b ∘ e.symm := by
  let := b.completeSpace
  exact HilbertBasis.coe_mk _ _

@[simp]
theorem reindex_apply (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') (i' : ι') :
    b.reindex e i' = b (e.symm i') :=
  congr_fun (b.coe_reindex e) i'

@[simp]
theorem repr_reindex_apply (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') (x : E) (i' : ι') :
    (b.reindex e).repr x i' = b.repr x (e.symm i') := by
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, reindex_apply]

@[simp]
theorem reindex_refl (b : HilbertBasis ι 𝕜 E) :
    b.reindex (Equiv.refl ι) = b :=
  DFunLike.ext _ _ fun _ ↦ by simp

@[simp]
theorem reindex_trans (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') (f : ι' ≃ ι'') :
    (b.reindex e).reindex f = b.reindex (e.trans f) :=
  DFunLike.ext _ _ fun _ ↦ by simp

theorem reindex_symm (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') :
    (b.reindex e).reindex e.symm = b := by
  simp

end HilbertBasis

namespace TauCeti

variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Every complete separable infinite-dimensional Hilbert space admits a Hilbert basis indexed by
`ℕ`. -/
theorem nonempty_hilbertBasis_nat [CompleteSpace E] [SeparableSpace E]
    (hE : ¬ FiniteDimensional 𝕜 E) : Nonempty (HilbertBasis ℕ 𝕜 E) := by
  obtain ⟨s, b, -⟩ := exists_hilbertBasis 𝕜 E
  have : Countable s := b.countable
  have : Infinite s := b.infinite_iff.2 hE
  obtain ⟨e⟩ := nonempty_equiv_of_countable (α := s) (β := ℕ)
  exact ⟨b.reindex e⟩

/-- An inner product space over `ℝ` or `ℂ` admits a `ℕ`-indexed Hilbert basis if and only if it is
complete, separable, and infinite-dimensional. -/
theorem nonempty_hilbertBasis_nat_iff :
    Nonempty (HilbertBasis ℕ 𝕜 E) ↔
      CompleteSpace E ∧ SeparableSpace E ∧ ¬ FiniteDimensional 𝕜 E := by
  refine ⟨fun ⟨b⟩ ↦ ⟨b.completeSpace, b.separableSpace, b.infinite_iff.1 inferInstance⟩, ?_⟩
  rintro ⟨_, _, hE⟩
  exact nonempty_hilbertBasis_nat 𝕜 E hE

/-- Every complete separable infinite-dimensional Hilbert space is linearly isometrically
equivalent to `ℓ²(ℕ, 𝕜)`. -/
theorem nonempty_linearIsometryEquiv_lp_nat [CompleteSpace E] [SeparableSpace E]
    (hE : ¬ FiniteDimensional 𝕜 E) : Nonempty (E ≃ₗᵢ[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2) :=
  let ⟨b⟩ := nonempty_hilbertBasis_nat 𝕜 E hE
  ⟨b.repr⟩

/-- The Hilbert direct sum `lp F 2` of a countably infinite family of nontrivial separable Hilbert
spaces is linearly isometrically equivalent to `ℓ²(ℕ, 𝕜)`. -/
theorem nonempty_linearIsometryEquiv_lp_of_infinite {ι : Type*} [Countable ι] [Infinite ι]
    (F : ι → Type*) [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace 𝕜 (F i)]
    [∀ i, CompleteSpace (F i)] [∀ i, SeparableSpace (F i)] [∀ i, Nontrivial (F i)] :
    Nonempty (lp F 2 ≃ₗᵢ[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2) := by
  have : SeparableSpace (lp F 2) := lp.separableSpace (by simp)
  exact nonempty_linearIsometryEquiv_lp_nat 𝕜 (lp F 2) lp.not_finiteDimensional_two

end TauCeti
