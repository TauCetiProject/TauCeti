/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.TotalDegree
public import TauCeti.Algebra.Lie.UniversalEnveloping.Grading
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Symmetrization.Map

/-!
# Symmetrization preserves total Lie degree

PBW symmetrization respects the grading induced by any additive-commutative-monoid
grading of the Lie algebra. Every permuted word has the same total degree, so averaging
preserves that degree as well. Consequently symmetrization commutes with homogeneous
projections, independently of freeness or finite-dimensionality.

See Dixmier, *Enveloping Algebras*, §2.4, and Petracci, *Universal representations of
Lie algebras by coderivations*, §8 (arXiv:math/0303020v1).
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

variable {Γ : Type*} [AddCommMonoid Γ] (R : Type) (L : Type*)
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L)

/-- Symmetrization carries every total-degree piece of the symmetric algebra into the
corresponding piece of the enveloping algebra. This containment does not require the
pieces of the original module to form a decomposition. -/
theorem pbwSymmetrizationMap_totalDegreeSubmodule_le (n : Γ) :
    TauCeti.SymmetricAlgebra.totalDegreeSubmodule ℒ n ≤
      (homogeneousSubmodule ℒ n).comap (pbwSymmetrizationMap R L) := by
  rw [TauCeti.SymmetricAlgebra.totalDegreeSubmodule_le_iff]
  intro l hl
  rw [Submodule.mem_comap]
  have hprod : (l.map (fun x => SymmetricAlgebra.ι R L (x.2 : L))).prod =
      ∏ i : Fin l.length, SymmetricAlgebra.ι R L ((l.get i).2 : L) := by
    exact (Fin.prod_univ_fun_getElem l
      (fun x => SymmetricAlgebra.ι R L (x.2 : L))).symm
  rw [hprod, pbwSymmetrizationMap_prod_ι]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro σ _
  have hdeg : ((List.ofFn fun i => l.get (σ i)).map Sigma.fst).sum = n := by
    have hperm : (List.ofFn fun i => l.get (σ i)).Perm l := by
      simpa only [Function.comp_def, List.ofFn_get] using σ.ofFn_comp_perm l.get
    exact (hperm.map Sigma.fst).sum_eq.trans hl
  have hmem := prod_mem_homogeneousSubmodule ℒ (List.ofFn fun i => l.get (σ i))
  rw [hdeg] at hmem
  simpa only [List.map_ofFn, Function.comp_def] using hmem

variable [DecidableEq Γ] [GradedLieAlgebra ℒ]

/-- Symmetrization commutes with each homogeneous projection for the total Lie-degree
gradings of the symmetric and enveloping algebras. -/
@[simp]
theorem pbwSymmetrizationMap_decompose (p : SymmetricAlgebra R L) (n : Γ) :
    pbwSymmetrizationMap R L
      (DirectSum.decompose (TauCeti.SymmetricAlgebra.totalDegreeSubmodule ℒ) p n) =
      (DirectSum.decompose (homogeneousSubmodule ℒ) (pbwSymmetrizationMap R L p) n :
        UniversalEnvelopingAlgebra R L) := by
  exact DirectSum.map_decompose_shift
    (TauCeti.SymmetricAlgebra.totalDegreeSubmodule ℒ) (homogeneousSubmodule ℒ)
    (pbwSymmetrizationMap R L).toAddMonoidHom id Function.injective_id
    (fun n _ hx => pbwSymmetrizationMap_totalDegreeSubmodule_le R L ℒ n hx) n p

end TauCeti.UniversalEnvelopingAlgebra
