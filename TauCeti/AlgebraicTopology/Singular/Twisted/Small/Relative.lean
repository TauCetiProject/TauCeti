/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Relative
public import TauCeti.AlgebraicTopology.Singular.Twisted.Small.Chains

/-!
# Support of relative twisted chains

Two facts about the relative twisted chains of an arbitrary topological pair `P` with coefficients
in a local coefficient system `L` on its ambient space. An ambient chain vanishes in relative
chains exactly when it is supported in the subspace
(`TopPair.twistedChainComplexπ_f_apply_eq_zero_iff`), and on a relative cycle, iterated
barycentric subdivision changes the relative class of a representative by the boundary of the
class of its subdivision prism (`TopPair.twistedChainComplexπ_f_sub_iterate_twistedSubdivision`).
They are the inputs from small chains to excision with local coefficients.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Proposition 2.21.
-/

public section

noncomputable section

open CategoryTheory Topology Simplicial

universe u v w

namespace TopPair

open TauCeti TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R]

section Support

variable (P : TopPair.{v}) (L : LocalCoefficientSystem.{u, v, max v w} R P.fst)

/-- An ambient twisted chain vanishes in relative chains exactly when it is supported in the
subspace. -/
lemma twistedChainComplexπ_f_apply_eq_zero_iff {k : ℕ} (z : L.twistedChainComplex.X k) :
    ((P.twistedChainComplexπ L).f k).hom z = 0 ↔
      z ∈ smallTwistedChains L (fun _ : Unit ↦ Set.range P.map) k := by
  have hsmall (σ : (TopCat.toSSet.obj P.fst) _⦋k⦌) :
      σ ∈ (P.fst.smallSingularSubcomplex fun _ : Unit ↦ Set.range P.map).obj _ ↔
        Set.range (TopCat.simplexMap σ) ⊆ Set.range P.map := by
    rw [TopCat.mem_smallSingularSubcomplex_iff, exists_const,
      ← P.isEmbedding_map.isInducing.mem_range_toSSet_map_app_iff,
      P.mem_range_toSSet_map_app_iff_range_simplexMap_subset]
  rw [mem_smallTwistedChains_iff]
  constructor
  · intro hz σ hσ
    rw [← P.twistedChainComplexCoeff_twistedChainComplexπ_f_apply L σ (mt (hsmall σ).2 hσ), hz,
      map_zero]
  · intro hz
    refine P.twistedChainComplex_ext_coeff L fun σ hσ ↦ ?_
    rw [P.twistedChainComplexCoeff_twistedChainComplexπ_f_apply, map_zero]
    exact hz σ (mt (hsmall σ).1 hσ)

/-- On a relative cycle, iterated barycentric subdivision of a representing ambient chain changes
its relative class by the boundary of the relative class of the subdivision prism. -/
lemma twistedChainComplexπ_f_sub_iterate_twistedSubdivision {n : ℕ}
    (c : L.twistedChainComplex.X n)
    (hc : (P.twistedChainComplex L).d n (n - 1) ((P.twistedChainComplexπ L).f n c) = 0)
    (N : ℕ) :
    (P.twistedChainComplexπ L).f n c -
        (P.twistedChainComplexπ L).f n ((End.of (twistedSubdivisionChainMap L) ^ N).asHom.f n c) =
      (P.twistedChainComplex L).d (n + 1) n ((P.twistedChainComplexπ L).f (n + 1)
        (((twistedSubdivisionHomotopy L).idPow N).hom n (n + 1) c)) := by
  rw [HomologicalComplex.Hom.comm_apply, ← map_sub]
  cases n with
  | zero =>
    have h := ((twistedSubdivisionHomotopy L).idPow N).comm_zero_apply c
    rw [HomologicalComplex.id_f, ModuleCat.id_apply] at h
    rw [sub_eq_of_eq_add h]
  | succ k =>
    have h := ((twistedSubdivisionHomotopy L).idPow N).comm_succ_apply k c
    rw [HomologicalComplex.id_f, ModuleCat.id_apply] at h
    -- The boundary of `c` lies in the subspace, hence so does its prism.
    have hd : (P.twistedChainComplexπ L).f k (L.twistedChainComplex.d (k + 1) k c) = 0 := by
      rw [← HomologicalComplex.Hom.comm_apply]
      exact hc
    rw [twistedChainComplexπ_f_apply_eq_zero_iff] at hd
    have hD := (P.twistedChainComplexπ_f_apply_eq_zero_iff L _).2
      (idPow_twistedSubdivisionHomotopy_hom_mem_smallTwistedChains L _ hd N)
    rw [sub_eq_of_eq_add h, map_add, hD, zero_add]

end Support

end TopPair
