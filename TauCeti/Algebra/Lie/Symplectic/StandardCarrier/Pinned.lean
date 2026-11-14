/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.LieGeneration
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation
import TauCeti.Algebra.Lie.Symplectic.Coordinates
import TauCeti.Algebra.Lie.Weights.Dimension
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.System

/-!
# The pinned type-C algebra on the standard symplectic module

`TauCeti.SpStd.pinnedLieEquiv` identifies the independently constructed rational Lie algebra
of type C with the native symplectic matrix Lie algebra. It matches the Cartan generators and
both signs of the simple-root generators in Bourbaki order, including the terminal long root.
Thus the standard symplectic representation can be read as a faithful representation of the
pinned algebra, with the same operators on its integral lattice.

The construction uses `SpStd.isSerreSystem_rootGenerator`, `DynkinType.serreLiftEquiv`, and
`SpStd.lieSpan_range_rootGenerator_eq_top`. The native matrix-entry coordinates and the
root-space dimension count show that the resulting surjection is an isomorphism. This is a
Lie-algebra comparison, not an identification of group schemes or of their points.

## References

* J.-P. Serre, *Complex Semisimple Lie Algebras*, Chapter VI, appendix.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4–6, Plate III.
-/

public section

namespace TauCeti.SpStd

open _root_.LieAlgebra.Symplectic

noncomputable section

variable (n : ℕ) (ht : (DynkinType.C (n + 1)).Valid)

private theorem isSerreSystem_pinned :
    IsSerreSystem ℚ (DynkinType.C (n + 1)).cartanMatrix.transpose
      (cartanGenerator n) (fun i => rootGenerator n (.inl i))
      (fun i => rootGenerator n (.inr i)) := by
  simpa only [DynkinType.cartanMatrix_C, DynkinType.rank_C] using
    isSerreSystem_rootGenerator n

private def pinnedLieHom :
    (DynkinType.C (n + 1)).lieAlgebra ht →ₗ⁅ℚ⁆ sp (Fin (n + 1)) ℚ :=
  (serreLift (isSerreSystem_pinned n)).comp
    (DynkinType.serreLiftEquiv _ ht).symm.toLieHom

private theorem pinnedLieHom_surjective : Function.Surjective (pinnedLieHom n ht) := by
  have hspan : LieSubalgebra.lieSpan ℚ (sp (Fin (n + 1)) ℚ)
      (Set.range (fun i => rootGenerator n (.inl i)) ∪
        Set.range (fun i => rootGenerator n (.inr i))) = ⊤ := by
    simpa only [Sum.range_eq, Function.comp_def] using
      lieSpan_range_rootGenerator_eq_top n
  exact (serreLift_surjective (isSerreSystem_pinned n) hspan).comp
    (DynkinType.serreLiftEquiv _ ht).symm.surjective

private theorem pinnedLieHom_bijective : Function.Bijective (pinnedLieHom n ht) := by
  have hcard : ((DynkinType.C (n + 1)).cartanSubalgebra ht).root.card =
      (DynkinType.C (n + 1)).numRoots := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using
      (Fintype.card_congr ((DynkinType.C (n + 1)).rootEquiv ht)).symm
  have hdim : Module.finrank ℚ ((DynkinType.C (n + 1)).lieAlgebra ht) =
      Module.finrank ℚ (sp (Fin (n + 1)) ℚ) := by
    rw [finrank_eq_finrank_cartan_add_card_root
        ((DynkinType.C (n + 1)).cartanSubalgebra ht),
      DynkinType.finrank_cartanSubalgebra, hcard,
      TauCeti.LieAlgebra.Symplectic.finrank_sp, Fintype.card_fin,
      DynkinType.rank_C, DynkinType.numRoots_C]
    ring
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr
    (pinnedLieHom_surjective n ht), pinnedLieHom_surjective n ht⟩

/-- The pinned rational type-C Lie algebra is the native symplectic Lie algebra, with the
numbered Cartan and positive and negative simple-root generators matched. -/
def pinnedLieEquiv :
    (DynkinType.C (n + 1)).lieAlgebra ht ≃ₗ⁅ℚ⁆ sp (Fin (n + 1)) ℚ :=
  LieEquiv.ofBijective (pinnedLieHom n ht) (pinnedLieHom_bijective n ht)

-- `LieEquiv.ofBijective` retains the underlying homomorphism; `LieHom.comp` evaluates
-- as function composition, so this is the defining composite of `pinnedLieHom`.
private theorem pinnedLieEquiv_apply (x : (DynkinType.C (n + 1)).lieAlgebra ht) :
    pinnedLieEquiv n ht x = serreLift (isSerreSystem_pinned n)
      ((DynkinType.serreLiftEquiv _ ht).symm x) := rfl

/-- The comparison sends each pinned Cartan generator to the standard simple coroot. -/
@[simp]
theorem pinnedLieEquiv_lieBasis_h (i : Fin (n + 1)) :
    pinnedLieEquiv n ht (((DynkinType.C (n + 1)).lieBasis ht).h i) =
      cartanGenerator n i := by
  rw [pinnedLieEquiv_apply]
  exact (congrArg (serreLift (isSerreSystem_pinned n))
    (DynkinType.serreLiftEquiv_symm_lieBasis_h _ ht i)).trans (serreLift_serreH _ i)

/-- The comparison sends each pinned raising generator to the standard positive simple root. -/
@[simp]
theorem pinnedLieEquiv_lieBasis_e (i : Fin (n + 1)) :
    pinnedLieEquiv n ht (((DynkinType.C (n + 1)).lieBasis ht).e i) =
      rootGenerator n (.inl i) := by
  rw [pinnedLieEquiv_apply]
  exact (congrArg (serreLift (isSerreSystem_pinned n))
    (DynkinType.serreLiftEquiv_symm_lieBasis_e _ ht i)).trans (serreLift_serreE _ i)

/-- The comparison sends each pinned lowering generator to the standard negative simple root. -/
@[simp]
theorem pinnedLieEquiv_lieBasis_f (i : Fin (n + 1)) :
    pinnedLieEquiv n ht (((DynkinType.C (n + 1)).lieBasis ht).f i) =
      rootGenerator n (.inr i) := by
  rw [pinnedLieEquiv_apply]
  exact (congrArg (serreLift (isSerreSystem_pinned n))
    (DynkinType.serreLiftEquiv_symm_lieBasis_f _ ht i)).trans (serreLift_serreF _ i)

/-- The inverse comparison recovers each numbered pinned Cartan generator. -/
@[simp]
theorem pinnedLieEquiv_symm_cartanGenerator (i : Fin (n + 1)) :
    (pinnedLieEquiv n ht).symm (cartanGenerator n i) =
      ((DynkinType.C (n + 1)).lieBasis ht).h i := by
  rw [LieEquiv.symm_apply_eq, pinnedLieEquiv_lieBasis_h]

/-- The inverse comparison recovers each numbered pinned raising generator. -/
@[simp]
theorem pinnedLieEquiv_symm_rootGenerator_inl (i : Fin (n + 1)) :
    (pinnedLieEquiv n ht).symm (rootGenerator n (.inl i)) =
      ((DynkinType.C (n + 1)).lieBasis ht).e i := by
  rw [LieEquiv.symm_apply_eq, pinnedLieEquiv_lieBasis_e]

/-- The inverse comparison recovers each numbered pinned lowering generator. -/
@[simp]
theorem pinnedLieEquiv_symm_rootGenerator_inr (i : Fin (n + 1)) :
    (pinnedLieEquiv n ht).symm (rootGenerator n (.inr i)) =
      ((DynkinType.C (n + 1)).lieBasis ht).f i := by
  rw [LieEquiv.symm_apply_eq, pinnedLieEquiv_lieBasis_f]

end

end TauCeti.SpStd
