/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.DegreeFiltration
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# A homogeneous basis of a symmetric algebra over a field

Over a field `K`, choosing a basis of each homogeneous component of `SymmetricAlgebra K V` and
collecting them gives a basis `TauCeti.SymmetricAlgebra.homogeneousBasis K V` of the symmetric
algebra, indexed by pairs `⟨d, a⟩` with `d` the degree. It is adapted to the degree filtration: the
`k`-th step of the degree filtration (the word filtration of the generators) is spanned by the basis
vectors of degree at most `k` (`TauCeti.SymmetricAlgebra.wordFiltration_eq_span_homogeneousBasis`).
This is the form consumed by the coordinate criterion for total tensor filtrations,
`TauCeti.mem_tensorFiltration_iff_of_basis`.

## Main results

* `TauCeti.SymmetricAlgebra.homogeneousBasis`: the collected basis of the homogeneous components.
* `TauCeti.SymmetricAlgebra.wordFiltration_eq_span_homogeneousBasis`: degree `k` is spanned by the
  basis vectors of degree at most `k`.
-/

public section

namespace TauCeti.SymmetricAlgebra

open TauCeti.Algebra Submodule

universe u v

variable (K : Type u) (V : Type v) [Field K] [AddCommGroup V] [Module K V]

/-- A basis of `SymmetricAlgebra K V` made of homogeneous elements: the union of chosen bases of
the homogeneous components. The index `⟨d, a⟩` has degree `d`. -/
noncomputable def homogeneousBasis :
    Module.Basis (Σ d : ℕ, Module.Basis.ofVectorSpaceIndex K (homogeneousSubmodule K V d)) K
      (_root_.SymmetricAlgebra K V) :=
  (DirectSum.Decomposition.isInternal (homogeneousSubmodule K V)).collectedBasis
    fun _ ↦ Module.Basis.ofVectorSpace K _

variable {K V}

/-- The basis vector of index `⟨d, a⟩` is homogeneous of degree `d`. -/
theorem homogeneousBasis_mem
    (i : Σ d : ℕ, Module.Basis.ofVectorSpaceIndex K (homogeneousSubmodule K V d)) :
    homogeneousBasis K V i ∈ homogeneousSubmodule K V i.1 :=
  DirectSum.IsInternal.collectedBasis_mem _ _ i

/-- **The homogeneous basis is adapted to the degree filtration**: degree `k` of the symmetric
algebra is spanned by the basis vectors of degree at most `k`. -/
theorem wordFiltration_eq_span_homogeneousBasis (k : ℕ) :
    wordFiltration (_root_.SymmetricAlgebra.ι K V) k =
      span K (homogeneousBasis K V '' {i | i.1 ≤ k}) := by
  classical
  refine le_antisymm (fun x hx ↦ ?_) (span_le.mpr ?_)
  · rw [Module.Basis.mem_span_image]
    rintro ⟨d, a⟩ hi
    by_contra hdk
    refine Finsupp.mem_support_iff.mp hi ?_
    have hrepr : ∀ e, (homogeneousBasis K V).repr
        (DirectSum.decompose (homogeneousSubmodule K V) x e : _root_.SymmetricAlgebra K V)
          ⟨d, a⟩ = 0 := fun e ↦ by
      by_cases he : e = d
      · subst he
        rw [coe_decompose_eq_zero_of_mem_wordFiltration (not_le.mp hdk) hx, map_zero,
          Finsupp.zero_apply]
      · exact DirectSum.IsInternal.collectedBasis_repr_of_mem_ne _ _ he (SetLike.coe_mem _)
    rw [← DirectSum.sum_support_decompose (homogeneousSubmodule K V) x, map_sum,
      Finsupp.finsetSum_apply]
    exact Finset.sum_eq_zero fun e _ ↦ hrepr e
  · rintro _ ⟨i, hi, rfl⟩
    exact wordFiltration_mono _ hi (range_pow_le_wordFiltration _ i.1 (homogeneousBasis_mem i))

end TauCeti.SymmetricAlgebra
