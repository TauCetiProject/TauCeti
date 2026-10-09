/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Free
public import TauCeti.Algebra.Homology.EulerCharacteristic.GradedDimension

/-!
# Finite Laurent support of graded Hom spaces

Let `P` be a finitely generated graded module and `M` a finite-dimensional graded module over a
graded algebra over a field. Only finitely many shifts `M{j}` receive a nonzero graded map from
`P`, and each Hom space is finite-dimensional, so the Hom spaces `Hom(P, M{j})` have finite
Laurent support. A surjection from a finite graded free module `⨁ᵢ A{dᵢ}` embeds
`Hom(P, M{j})` into `∏ᵢ M_{dᵢ-j}`. No projectivity of `P` and no finite-dimensionality of the
algebra are needed.

## Main results

* `TauCeti.GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj`: graded maps from a finitely
  generated graded module into the shifts of a finite-dimensional one have finite Laurent support.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded free
  modules and degree shifts.
-/

public section

open CategoryTheory

namespace TauCeti.GradedModuleCat

universe uk uA

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- **Graded maps into the shifts of a finite-dimensional graded module have finite Laurent
support** when the source is finitely generated. A surjection from a finite graded free module
`⨁ᵢ A{dᵢ}` embeds `Hom(P, M{j})` into `∏ᵢ M_{dᵢ-j}`, and `M` has only finitely many nonzero
pieces. -/
theorem hasFiniteLaurentSupport_hom_shiftObj (P M : GradedModuleCat.{uA} 𝒜)
    [Module.Finite A P] [Module.Finite k M] :
    HasFiniteLaurentSupport k fun j : ℤ ↦ P ⟶ M.shiftObj j := by
  classical
  obtain ⟨I, hI, d, π, hπ⟩ := exists_finite_free_surjection P
  have : Epi π := (epi_iff_surjective π).2 hπ
  let _ : Fintype I := Fintype.ofFinite I
  have hM := M.grading.finite_piece_ne_bot
  -- Maps out of the free module are tuples in the pieces `M_{dᵢ-j}`.
  have hfree : HasFiniteLaurentSupport k fun j : ℤ ↦ ∀ i, (M.shiftObj j).grading.piece (d i) := by
    refine HasFiniteLaurentSupport.of_finset (fun j ↦ inferInstance)
      (Finset.univ.biUnion fun i ↦ hM.toFinset.image fun p ↦ d i - p) fun j hj ↦ ?_
    have (i : I) : Subsingleton ((M.shiftObj j).grading.piece (d i)) := by
      rw [Submodule.subsingleton_iff_eq_bot]
      by_contra hne
      refine hj (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, Finset.mem_image.2
        ⟨d i + -j, hM.mem_toFinset.2 ?_, by omega⟩⟩)
      simpa using hne
    infer_instance
  exact (hfree.of_equiv fun j ↦ (freeHomEquiv (M.shiftObj j)).symm).of_injective
    (fun j ↦ Linear.leftComp k _ π) fun j _ _ h ↦ (cancel_epi π).1 h

end TauCeti.GradedModuleCat
