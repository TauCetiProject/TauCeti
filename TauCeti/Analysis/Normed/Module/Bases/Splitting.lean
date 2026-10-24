/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Bases.ModelSpace
public import TauCeti.Topology.Algebra.Module.Span
public import Mathlib.Topology.Algebra.Module.Complement
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.Equiv.Prod

/-!
# Continuous splitting for Banach spaces of countable type

Let `K` be a complete nontrivially normed field and `E` an ultrametric Banach space over `K` of
countable type, that is, some sequence `v : ℕ → E` has dense span. Then every closed subspace of
`E` has a closed complement, and short exact sequences out of `E` split continuously:

* `ContinuousLinearMap.exists_rightInverse_of_surjective_of_dense_span`: every continuous linear
  surjection `q : E →L[K] N` onto a Banach space has a continuous linear section.
* `Submodule.closedComplemented_of_isClosed_of_dense_span`: every closed subspace of `E` is
  continuously complemented, in the sense of Mathlib's `Submodule.ClosedComplemented`.
* `TauCeti.exists_continuousLinearEquiv_prod_of_countableType`: for an embedding `i : M →L[K] E`
  and a surjection `q : E →L[K] N` onto a Banach space with `range i = ker q`, there is a continuous
  linear equivalence `d : E ≃L[K] M × N` with `d (i m) = (m, 0)` and `(d x).2 = q x`.

The quotient `E ⧸ ker q` is again an ultrametric Banach space of countable type, hence potentially
orthonormalisable (`TauCeti.isPotentiallyONable_of_dense_span`). By the bounded inverse theorem it
is continuously linearly equivalent to `N`, and the lifting property of modules with property (Pr)
(`TauCeti.HasPr.lifting_property`) turns that equivalence into a section of `q`. Neither a discrete
valuation on `K` nor an ultrametric norm on `N` is needed, and `M` may be any topological
`K`-module.

## References

* C. Perez-Garcia and W. H. Schikhof, *Locally Convex Spaces over Non-Archimedean Valued
  Fields*, Cambridge Studies in Advanced Mathematics 119, Cambridge University Press, 2010,
  Chapter 2.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Springer, 1984, §2.7.
-/

public section

open Set Submodule Topology

variable {K E N : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [NormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E] [CompleteSpace E]
  [NormedAddCommGroup N] [NormedSpace K N] [CompleteSpace N]

/-- **Continuous sections over spaces of countable type**: over a complete nontrivially normed
field, every continuous linear surjection `q : E →L[K] N` from an ultrametric Banach space of
countable type onto a Banach space has a continuous linear right inverse. -/
theorem ContinuousLinearMap.exists_rightInverse_of_surjective_of_dense_span (q : E →L[K] N)
    (hq : Function.Surjective q) {v : ℕ → E} (hv : Dense (span K (range v) : Set E)) :
    ∃ s : N →L[K] E, q.comp s = .id K N := by
  -- Closedness of `ker q` makes `E ⧸ ker q` a normed space.
  have : IsClosed (q.ker : Set E) := q.isClosed_ker
  -- The quotient `E ⧸ ker q` is of countable type, hence has property (Pr).
  have hpr : TauCeti.HasPr K (E ⧸ q.ker) :=
    (TauCeti.isPotentiallyONable_of_dense_span ((mkQ_surjective _).denseRange.dense_span_range_comp
      q.ker.mkQL.continuous hv)).hasPr
  -- By the bounded inverse theorem the induced map `E ⧸ ker q → N` is an isomorphism.
  let φ : (E ⧸ q.ker) ≃L[K] N := .ofBijective (q.ker.liftQL q le_rfl)
    (ker_liftQ_eq_bot _ _ _ le_rfl) (by simpa [range_liftQ] using LinearMap.range_eq_top.2 hq)
  obtain ⟨g, hg⟩ := hpr.lifting_property q φ hq
  refine ⟨g.comp (φ.symm : N →L[K] E ⧸ q.ker), ?_⟩
  rw [← ContinuousLinearMap.comp_assoc, hg, ContinuousLinearEquiv.coe_comp_coe_symm]

/-- **Closed subspaces of spaces of countable type are complemented**: over a complete nontrivially
normed field, every closed subspace `D` of an ultrametric Banach space of countable type has a
closed complement, that is, there is a continuous linear projection of the space onto `D`. -/
theorem Submodule.closedComplemented_of_isClosed_of_dense_span (D : Submodule K E)
    (hD : IsClosed (D : Set E)) {v : ℕ → E} (hv : Dense (span K (range v) : Set E)) :
    D.ClosedComplemented := by
  obtain ⟨s, hs⟩ := D.mkQL.exists_rightInverse_of_surjective_of_dense_span (mkQ_surjective D) hv
  simpa using D.mkQL.closedComplemented_ker_of_rightInverse s fun y ↦ by
    simpa using DFunLike.congr_fun hs y

namespace TauCeti

/-- **Strict short exact sequences out of a space of countable type split**: over a complete
nontrivially normed field, let `E` be an ultrametric Banach space of countable type, let
`i : M →L[K] E` be an embedding and `q : E →L[K] N` a surjection onto a Banach space with
`range i = ker q`. Then there is a continuous linear equivalence `d : E ≃L[K] M × N` with
`d (i m) = (m, 0)` and `(d x).2 = q x`. -/
theorem exists_continuousLinearEquiv_prod_of_countableType {M : Type*} [AddCommGroup M]
    [Module K M] [TopologicalSpace M] {v : ℕ → E} (hv : Dense (span K (range v) : Set E))
    (i : M →L[K] E) (q : E →L[K] N) (hi : IsEmbedding i) (hq : Function.Surjective q)
    (hiq : i.range = q.ker) :
    ∃ d : E ≃L[K] M × N, (∀ m, d (i m) = (m, 0)) ∧ ∀ x, (d x).2 = q x := by
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective_of_dense_span hq hv
  have hs' : Function.RightInverse s q := fun y ↦ by simpa using DFunLike.congr_fun hs y
  -- `i` identifies `M` with `ker q`, and a section of `q` splits `E` as `N × ker q`.
  let e : M ≃ₗ[K] q.ker :=
    (LinearEquiv.ofInjective i.toLinearMap hi.injective).trans (LinearEquiv.ofEq _ _ hiq)
  let e' : M ≃L[K] q.ker := .ofIsHomeomorph e <| isHomeomorph_iff_isEmbedding_surjective.2
    ⟨IsEmbedding.subtypeVal.of_comp_iff.1 hi, e.surjective⟩
  refine ⟨(ContinuousLinearEquiv.equivOfRightInverse q s hs').trans
    (((ContinuousLinearEquiv.refl K N).prodCongr e'.symm).trans (.prodComm K N M)),
    fun m ↦ ?_, fun x ↦ by simp⟩
  have hm : q (i m) = 0 := LinearMap.mem_ker.1 (hiq ▸ LinearMap.mem_range_self (i : M →ₗ[K] E) m)
  ext
  · simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodComm_apply,
      ContinuousLinearEquiv.prodCongr_apply, Prod.fst_swap, e'.symm_apply_eq]
    exact Subtype.ext (by simp [hm, e', e])
  · simp [hm]

end TauCeti
