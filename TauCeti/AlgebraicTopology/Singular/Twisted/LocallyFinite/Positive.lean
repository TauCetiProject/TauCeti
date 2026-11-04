/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Reindex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Positive-degree Borel–Moore homology of totally disconnected spaces

The zeroth simplicial degeneracies give a support-preserving contraction in positive degrees
on a totally disconnected space. Extending them to locally finite twisted chains shows that
every positive-degree cycle is a boundary. In particular the positive-degree Borel–Moore
groups of a discrete space vanish, with arbitrary module-valued local coefficients and without
any compactness or countability assumption. Degree zero is deliberately not contracted: on an
infinite discrete space it records an unrestricted product, not a direct sum.

## References

* A. Hatcher, *Algebraic Topology*, Sections 2.1 and 3.H.
* G. E. Bredon, *Sheaf Theory*, 2nd ed., Chapter V.
-/

public section

open CategoryTheory Limits SimplexCategory

open scoped Simplicial

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}} [TotallyDisconnectedSpace X]
  (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- Zeroth degeneracies contract locally finite chains in positive degrees on a totally
disconnected space. Both parts of the contraction preserve local finiteness. -/
theorem locallyFiniteReindex_comp_boundary_add_boundary_comp_locallyFiniteReindex (k : ℕ) :
    locallyFiniteReindex L (σ (0 : Fin (k + 1))) ∘ₗ locallyFiniteBoundary L k +
      locallyFiniteBoundary L (k + 1) ∘ₗ locallyFiniteReindex L (σ (0 : Fin (k + 2))) =
        LinearMap.id := by
  have h := extendLocallyFinite_eq_add (isProperlySupported_id (L := L) (a := k + 1))
    ((isProperlySupported_d k).comp
      (isProperlySupported_twistedChainReindex L (σ (0 : Fin (k + 1)))))
    ((isProperlySupported_twistedChainReindex L (σ (0 : Fin (k + 2)))).comp
      (isProperlySupported_d (k + 1)))
    (d_comp_twistedChainReindex_add_twistedChainReindex_comp_d L k).symm
  rw [extendLocallyFinite_id] at h
  simpa only [locallyFiniteBoundary_def, locallyFiniteReindex_def, extendLocallyFinite_comp]
    using h.symm

/-- A locally finite positive-degree cycle is filled by its zeroth degeneracy. This specifies
an actual locally finite filling, rather than only the vanishing of its homology class. -/
theorem locallyFiniteBoundary_reindex_of_boundary_eq_zero (k : ℕ)
    (z : locallyFiniteChains L (k + 1)) (hz : locallyFiniteBoundary L k z = 0) :
    locallyFiniteBoundary L (k + 1)
      (locallyFiniteReindex L (σ (0 : Fin (k + 2))) z) = z := by
  have h := LinearMap.congr_fun
    (locallyFiniteReindex_comp_boundary_add_boundary_comp_locallyFiniteReindex L k) z
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, hz, map_zero, zero_add,
    LinearMap.id_apply] using h

/-- Locally finite twisted chains on a totally disconnected space are exact in every
positive degree. -/
theorem exactAt_locallyFiniteChainComplex_succ_of_totallyDisconnectedSpace (k : ℕ) :
    (locallyFiniteChainComplex L).ExactAt (k + 1) := by
  let S := ShortComplex.moduleCatMk (locallyFiniteBoundary L (k + 1))
    (locallyFiniteBoundary L k) locallyFiniteBoundary_comp_locallyFiniteBoundary
  have hS : S.Exact := ShortComplex.moduleCat_exact_iff S |>.2 fun z hz ↦
    ⟨locallyFiniteReindex L (σ (0 : Fin (k + 2))) z,
      locallyFiniteBoundary_reindex_of_boundary_eq_zero L k z hz⟩
  -- Compare the native chain terms with their named locally finite modules using the
  -- existing term and differential identifications, rather than unfolding the complex.
  have hcomm (j : ℕ) :
      eqToHom (locallyFiniteChainComplex_X L (j + 1)) ≫
          ModuleCat.ofHom (locallyFiniteBoundary L j) =
        (locallyFiniteChainComplex L).d (j + 1) j ≫
          eqToHom (locallyFiniteChainComplex_X L j) := by
    rw [locallyFiniteChainComplex_d]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  let e : (locallyFiniteChainComplex L).sc' (k + 2) (k + 1) k ≅ S :=
    ShortComplex.isoMk (eqToIso (locallyFiniteChainComplex_X L (k + 2)))
      (eqToIso (locallyFiniteChainComplex_X L (k + 1)))
      (eqToIso (locallyFiniteChainComplex_X L k))
      (hcomm (k + 1)) (hcomm k)
  rw [HomologicalComplex.exactAt_iff' _ (k + 2) (k + 1) k (by simp) (by simp),
    ShortComplex.exact_iff_of_iso e]
  exact hS

/-- Positive-degree Borel–Moore homology with local coefficients vanishes on a totally
disconnected space, in particular on any discrete space. -/
theorem isZero_borelMooreHomology_of_totallyDisconnectedSpace {k : ℕ} (hk : k ≠ 0) :
    IsZero (borelMooreHomology L k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  exact (exactAt_locallyFiniteChainComplex_succ_of_totallyDisconnectedSpace L j).isZero_homology

end TauCeti.LocalCoefficientSystem
