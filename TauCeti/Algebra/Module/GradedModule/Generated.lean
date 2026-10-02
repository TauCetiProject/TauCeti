/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import TauCeti.Algebra.Module.GradedModule.DirectSum
public import TauCeti.Algebra.Module.GradedModule.Shift

/-!
# Graded modules generated in one degree

An internally graded module is generated in degree `d` when its degree-`d` homogeneous piece
generates the underlying module.  This is the module-theoretic condition imposed on the `i`th
projective in a linear resolution: after choosing the degree of the resolved module, its `i`th
projective is generated in the correspondingly shifted degree.

The definition is phrased using `Submodule.span`, so it does not depend on a choice of homogeneous
generators.  The results below give the API needed to use it without unfolding: generation is
invariant under transport by a linear equivalence, its degree changes predictably when the grading
is shifted, and linear maps out of the module are determined by the indicated homogeneous piece.

## Main definitions

* `TauCeti.InternalGrading.IsGeneratedInDegree`: the degree-`d` piece spans the whole module.

## Main results

* `TauCeti.InternalGrading.isGeneratedInDegree_map_iff`: generation in a degree is invariant
  under transport of the grading along a linear equivalence.
* `TauCeti.InternalGrading.isGeneratedInDegree_shift_iff`: shifting an internal grading reindexes
  the generating degree.
* `TauCeti.InternalGrading.isGeneratedInDegree_directSum_iff`: a direct sum is generated in one
  degree exactly when every summand is generated in that degree.
* `TauCeti.InternalGrading.linearMap_ext_of_isGeneratedInDegree`: two linear maps out of a module
  generated in degree `d` agree when they agree on its degree-`d` piece.
* `TauCeti.InternalGrading.IsGeneratedInDegree.piece_add_eq_smul`: over a graded algebra `𝒜`, a
  graded module generated in degree `d` has degree-`m + d` piece `𝒜 m • M_d`.
* `TauCeti.InternalGrading.IsGeneratedInDegree.piece_eq_bot_of_lt`: over a nonnegatively graded
  algebra, a graded module generated in degree `d` vanishes in every degree below `d`.
* `TauCeti.InternalGrading.IsGeneratedInDegree.piece_le_smul_top`: a graded module generated in
  degree `d` has all of its pieces of degree above `d` inside `A₊ M`, where `A₊` is the sum of the
  pieces of positive degree.
* `TauCeti.InternalGrading.apply_mem_smul_top_of_isGeneratedInDegree`: over a nonnegatively graded
  algebra, a degree-zero map from a module generated in degree `d'` to a module generated in a
  lower degree lands in `A₊ M`.

## References

* S. Priddy, "Koszul resolutions", *Transactions of the American Mathematical Society* **152**
  (1970), 39--60, for linear resolutions of graded modules.
* Z. Dancso and A. Licata, "Koszul algebras and flow lattices", *Journal of Combinatorial
  Theory, Series A* **185** (2022), Section 2.2, for the graded-module conventions used by the
  downstream Grothendieck-group constructions.
-/

public section

namespace TauCeti

universe u u' v w

namespace InternalGrading

variable {R : Type u} {A : Type u'} {M : Type v}
variable [Semiring R] [Semiring A]
variable [AddCommMonoid M] [Module R M] [Module A M]

/-- An internally graded module is generated in degree `d` if the `A`-span of its degree-`d`
homogeneous piece is the whole module.  The grading pieces are `R`-submodules, while `A` is the
scalar semiring whose span measures generation (typically the graded algebra acting on the
module). -/
def IsGeneratedInDegree (G : InternalGrading R M) (A : Type u') [Semiring A] [Module A M]
    (d : ℤ) : Prop :=
  Submodule.span A (G.piece d : Set M) = ⊤

/-- Generation in degree `d`, restated as membership of every element in the span of the
degree-`d` piece. -/
theorem isGeneratedInDegree_iff (G : InternalGrading R M) (d : ℤ) :
    G.IsGeneratedInDegree A d ↔ ∀ x : M, x ∈ Submodule.span A (G.piece d : Set M) := by
  constructor
  · intro h x
    rw [h]
    exact Submodule.mem_top
  · intro h
    exact top_unique fun x _ ↦ h x

/-- If the degree-`d` piece is the whole module, then the module is generated in degree `d`. -/
theorem isGeneratedInDegree_of_piece_eq_top (G : InternalGrading R M) (d : ℤ)
    (h : G.piece d = ⊤) : G.IsGeneratedInDegree A d := by
  simp [IsGeneratedInDegree, h]

/-- Enlarging the proposed homogeneous generating piece preserves generation. -/
theorem IsGeneratedInDegree.mono {G H : InternalGrading R M} {d e : ℤ}
    (hG : G.IsGeneratedInDegree A d) (h : G.piece d ≤ H.piece e) :
    H.IsGeneratedInDegree A e := by
  rw [IsGeneratedInDegree] at hG ⊢
  apply top_unique
  rw [← hG]
  exact Submodule.span_mono h

variable {N : Type w} [AddCommMonoid N] [Module A N]

section Map

variable {k : Type u} [CommSemiring k] [Algebra k A]
variable [Module k M] [IsScalarTower k A M] [Module k N] [IsScalarTower k A N]

/-- Transporting an internal grading along a linear equivalence preserves generation in every
degree. -/
@[simp]
theorem isGeneratedInDegree_map_iff (G : InternalGrading k M) (e : M ≃ₗ[A] N) (d : ℤ) :
    (G.map (e.restrictScalars k)).IsGeneratedInDegree A d ↔ G.IsGeneratedInDegree A d := by
  rw [IsGeneratedInDegree, IsGeneratedInDegree, map_piece]
  -- Expose the carrier of the mapped `k`-submodule as an image so the `A`-span map lemma applies.
  change Submodule.span A (e '' (G.piece d : Set M)) = ⊤ ↔ _
  rw [Submodule.span_image_linearEquiv, Submodule.map_eq_top_iff]

end Map

/-- A shift by `c` reindexes generation in degree `d` as generation in degree `d + c` for the
original grading. -/
@[simp]
theorem isGeneratedInDegree_shift_iff (G : InternalGrading R M) (c d : ℤ) :
    (G.shift c).IsGeneratedInDegree A d ↔ G.IsGeneratedInDegree A (d + c) := by
  rw [IsGeneratedInDegree, IsGeneratedInDegree, shift_piece]

/-- Two linear maps out of a module generated in degree `d` are equal exactly when they agree on
homogeneous elements of degree `d`. -/
theorem linearMap_eq_iff_of_isGeneratedInDegree (G : InternalGrading R M) {d : ℤ}
    (hG : G.IsGeneratedInDegree A d) (f g : M →ₗ[A] N) :
    f = g ↔ ∀ x : G.piece d, f x = g x :=
  Submodule.linearMap_eq_iff_of_span_eq_top f g hG

/-- Two linear maps out of a module generated in degree `d` agree everywhere if they agree on
homogeneous elements of degree `d`. -/
theorem linearMap_ext_of_isGeneratedInDegree (G : InternalGrading R M) {d : ℤ}
    (hG : G.IsGeneratedInDegree A d) {f g : M →ₗ[A] N}
    (h : ∀ x : G.piece d, f x = g x) : f = g :=
  (G.linearMap_eq_iff_of_isGeneratedInDegree hG f g).2 h

/-- A linear map out of a module generated in degree `d` vanishes exactly when it vanishes on
homogeneous elements of degree `d`. -/
theorem linearMap_eq_zero_iff_of_isGeneratedInDegree (G : InternalGrading R M) {d : ℤ}
    (hG : G.IsGeneratedInDegree A d) (f : M →ₗ[A] N) :
    f = 0 ↔ ∀ x : G.piece d, f x = 0 :=
  Submodule.linearMap_eq_zero_iff_of_span_eq_top f hG

section DirectSum

variable {ι : Type*} {M : ι → Type v}
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, Module A (M i)]

/-- An external direct sum is generated in degree `d` if every summand is generated in degree
`d`. -/
theorem isGeneratedInDegree_directSum (G : ∀ i, InternalGrading R (M i)) (d : ℤ)
    (hG : ∀ i, (G i).IsGeneratedInDegree A d) :
    (directSum G).IsGeneratedInDegree A d := by
  classical
  rw [isGeneratedInDegree_iff]
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact Submodule.zero_mem _
  | of i x =>
      rw [← DirectSum.lof_eq_of A ι M]
      have hx := ((G i).isGeneratedInDegree_iff d).1 (hG i) x
      induction hx using Submodule.span_induction with
      | mem y hy =>
          rw [directSum_piece]
          exact Submodule.subset_span (lof_mem_directSumPiece G d i ⟨y, hy⟩)
      | zero =>
          rw [map_zero]
          exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
          rw [map_add]
          exact Submodule.add_mem _ hx hy
      | smul a x _ hx =>
          rw [map_smul]
          exact Submodule.smul_mem _ a hx
  | add x y hx hy => exact Submodule.add_mem _ hx hy

/-- If an external direct sum is generated in degree `d`, then every summand is generated in
degree `d`. -/
theorem IsGeneratedInDegree.of_directSum (G : ∀ i, InternalGrading R (M i)) (d : ℤ)
    (hG : (directSum G).IsGeneratedInDegree A d) (i : ι) :
    (G i).IsGeneratedInDegree A d := by
  classical
  rw [(G i).isGeneratedInDegree_iff]
  intro x
  have hx := ((directSum G).isGeneratedInDegree_iff d).1 hG
    (DirectSum.lof A ι M i x)
  have map_span : ∀ y : DirectSum ι M,
      y ∈ Submodule.span A ((directSum G).piece d : Set (DirectSum ι M)) →
        DirectSum.component A ι M i y ∈
          Submodule.span A ((G i).piece d : Set (M i)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        apply Submodule.subset_span
        apply (mem_directSumPiece_iff G d y).1
        rw [← directSum_piece]
        exact hy
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx
  simpa using map_span _ hx

/-- An external direct sum is generated in degree `d` exactly when every summand is generated in
degree `d`. -/
@[simp]
theorem isGeneratedInDegree_directSum_iff (G : ∀ i, InternalGrading R (M i)) (d : ℤ) :
    (directSum G).IsGeneratedInDegree A d ↔ ∀ i, (G i).IsGeneratedInDegree A d :=
  ⟨fun h i ↦ h.of_directSum G d i, isGeneratedInDegree_directSum G d⟩

end DirectSum

end InternalGrading

/-! ### Generation over a graded algebra -/

namespace InternalGrading

variable {k : Type u} {A : Type u'} {M : Type v}
variable [CommSemiring k] [Semiring A] [Algebra k A]
variable [AddCommMonoid M] [Module k M] [Module A M] [IsScalarTower k A M]
variable (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]
variable {G : InternalGrading k M} [SetLike.GradedSMul 𝒜 G.piece] {d : ℤ}

/-- Over a graded algebra `𝒜`, a graded module generated in degree `d` has degree-`m + d` piece
`𝒜 m • M_d`: its homogeneous elements of degree `m + d` are exactly the sums of products of
degree-`m` elements of the algebra with degree-`d` elements of the module. -/
theorem IsGeneratedInDegree.piece_add_eq_smul (hG : G.IsGeneratedInDegree A d) (m : ℤ) :
    G.piece (m + d) = 𝒜 m • G.piece d := by
  refine le_antisymm (fun x hx ↦ ?_) (Submodule.smul_le.2 fun a ha y hy ↦
    SetLike.GradedSMul.smul_mem ha hy)
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.1 ((G.isGeneratedInDegree_iff d).1 hG x)
  rw [← DirectSum.decompose_of_mem_same G.piece hx, DirectSum.decompose_sum,
    DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [DirectSum.coe_decompose_smul_add_of_right_mem 𝒜 G.piece (g i).2]
  exact Submodule.smul_mem_smul (DirectSum.decompose 𝒜 (c i) m).2 (g i).2

/-- Over a nonnegatively graded algebra, a graded module generated in degree `d` has no nonzero
homogeneous elements of degree below `d`. -/
theorem IsGeneratedInDegree.piece_eq_bot_of_lt (h𝒜 : ∀ i < 0, 𝒜 i = ⊥)
    (hG : G.IsGeneratedInDegree A d) {p : ℤ} (hp : p < d) : G.piece p = ⊥ := by
  rw [← sub_add_cancel p d, hG.piece_add_eq_smul 𝒜, h𝒜 _ (by omega), Submodule.bot_smul]

/-- A graded module generated in degree `d` has every homogeneous piece of degree above `d`
inside `A₊ M`, the products of elements of positive degree with elements of the module. -/
theorem IsGeneratedInDegree.piece_le_smul_top (hG : G.IsGeneratedInDegree A d) {p : ℤ}
    (hp : d < p) : G.piece p ≤ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • ⊤ := by
  rw [← sub_add_cancel p d, hG.piece_add_eq_smul 𝒜]
  exact Submodule.smul_mono (le_iSup₂_of_le (p - d) (by omega) le_rfl) le_top

/-- Over a nonnegatively graded algebra, a degree-zero homogeneous map from a graded module
generated in degree `d'` to a graded module generated in a lower degree `d` takes values in
`A₊ M`. The source has no homogeneous elements below degree `d'`, and the target has all of its
homogeneous elements of degree at least `d'` in `A₊ M`. -/
theorem apply_mem_smul_top_of_isGeneratedInDegree (h𝒜 : ∀ i < 0, 𝒜 i = ⊥)
    {M' : Type w} [AddCommMonoid M'] [Module k M'] [Module A M'] [IsScalarTower k A M']
    {G' : InternalGrading k M'} [SetLike.GradedSMul 𝒜 G'.piece] {d' : ℤ}
    (hG' : G'.IsGeneratedInDegree A d') (hG : G.IsGeneratedInDegree A d) (hd : d < d')
    {f : M' →ₗ[A] M} (hf : LinearMap.IsHomogeneous f G'.piece G.piece 0) (x : M') :
    f x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  classical
  rw [← DirectSum.sum_support_decompose G'.piece x, map_sum]
  refine Submodule.sum_mem _ fun p _ ↦ ?_
  have hx : (DirectSum.decompose G'.piece x p : M') ∈ G'.piece p := (DirectSum.decompose _ x p).2
  rcases lt_or_ge p d' with hp | hp
  · rw [(Submodule.eq_bot_iff _).1 (hG'.piece_eq_bot_of_lt 𝒜 h𝒜 hp) _ hx, map_zero]
    exact Submodule.zero_mem _
  · exact hG.piece_le_smul_top 𝒜 (p := p) (by omega) (by simpa using hf.map_mem hx)

end InternalGrading

end TauCeti
