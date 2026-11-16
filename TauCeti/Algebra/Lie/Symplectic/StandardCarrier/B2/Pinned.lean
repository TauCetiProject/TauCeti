/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Basic
public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Chevalley
import TauCeti.Algebra.Lie.Symplectic.Coordinates
import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.LieGeneration
import TauCeti.Algebra.Lie.Weights.Dimension
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.System
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation

/-!
# The pinned type-B₂ algebra as four-by-four symplectic matrices

The rank-two symplectic Lie algebra `sp₄` cannot be instantiated at `TauCeti.SpStd.pinnedLieEquiv`
because `TauCeti.DynkinType.C 2` is excluded by `TauCeti.DynkinType.Valid` in favor of
`TauCeti.DynkinType.B 2`. In Bourbaki numbering, node `0` of `B₂` is long and node `1` is short,
whereas `TauCeti.SpStd` at `n = 1` numbers node `0` as short and node `1` as long.

`TauCeti.SpStd.b2NodeEquiv` packages that Bourbaki node correspondence between
`Fin (DynkinType.B 2).rank` and `Fin 2`, and `TauCeti.SpStd.b2PinnedLieEquiv` identifies the
independently constructed rational Lie algebra of type `B 2` with `sp (Fin 2) ℚ`, matching the
Cartan, raising, and lowering generators across `b2NodeEquiv`. Thus the four-dimensional symplectic
module and its standard integral coordinate lattice become a representation of the pinned `B₂`
algebra.

The construction applies `IsSerreSystem.submatrix` along `b2NodeEquiv` to
`TauCeti.SpStd.isSerreSystem_rootGenerator 1`, rewrites the reindexed Cartan matrix via
`TauCeti.DynkinType.cartanMatrix_C_two_apply_eq_cartanMatrix_B_two`, and lifts through
`TauCeti.DynkinType.serreLiftEquiv`. Surjectivity follows from
`TauCeti.SpStd.lieSpan_range_rootGenerator_eq_top 1`, and injectivity from the root-space
dimension count `2 + 8 = 10`. This is a rational Lie-algebra comparison; it does not assert an
identification of group schemes or of their points.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plates II and III.
* J.-P. Serre, *Complex Semisimple Lie Algebras*, Chapter VI, appendix.

The Serre-lift isomorphism construction, dimension-count bijectivity proof, and generator equations
adapt `TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Pinned`.
-/

public section

namespace TauCeti.SpStd

open _root_.LieAlgebra.Symplectic

/-- **The rank-two symplectic carrier node corresponding to a Bourbaki-numbered node of `B₂`.** It
exchanges the two nodes via `Equiv.swap 0 1`, sending the long node `0` of `B₂` to the final node
`1` of `SpStd 1` and the short node `1` of `B₂` to node `0` of `SpStd 1`. -/
def b2NodeEquiv : Fin (DynkinType.B 2).rank ≃ Fin 2 :=
  (Equiv.swap 0 1 : Equiv.Perm (Fin 2))

/-- The node correspondence is `Equiv.swap 0 1`. -/
theorem b2NodeEquiv_def : b2NodeEquiv = (Equiv.swap 0 1 : Equiv.Perm (Fin 2)) :=
  (rfl)

/-- Evaluating `b2NodeEquiv` swaps the two nodes `0` and `1`. This is not a `simp` lemma so that
`Equiv.apply_symm_apply` and `Equiv.symm_apply_apply` remain applicable to `b2NodeEquiv`. -/
theorem b2NodeEquiv_apply (i : Fin (DynkinType.B 2).rank) :
    b2NodeEquiv i = (Equiv.swap 0 1 : Equiv.Perm (Fin 2)) i :=
  (rfl)

/-- Evaluating `b2NodeEquiv.symm` swaps the two nodes `0` and `1`. -/
theorem b2NodeEquiv_symm_apply (i : Fin 2) :
    b2NodeEquiv.symm i = (Equiv.swap 0 1 : Equiv.Perm (Fin 2)) i :=
  (rfl)

/-- The node swap `b2NodeEquiv` agrees with `TauCeti.lengthPermRankTwo`. -/
theorem b2NodeEquiv_apply_eq_lengthPermRankTwo (i : Fin (DynkinType.B 2).rank) :
    b2NodeEquiv i = lengthPermRankTwo i := by
  obtain ⟨j, rfl⟩ := b2NodeEquiv.symm.surjective i
  rw [Equiv.apply_symm_apply, b2NodeEquiv_symm_apply]
  fin_cases j <;> simp

/-- **The final carrier node `1` corresponds to the long simple root of `B₂`.** -/
theorem b2NodeEquiv_eq_one_iff (i : Fin (DynkinType.B 2).rank) :
    b2NodeEquiv i = 1 ↔ (DynkinType.B 2).IsLongSimpleRoot i := by
  obtain ⟨j, rfl⟩ := b2NodeEquiv.symm.surjective i
  rw [Equiv.apply_symm_apply, DynkinType.isLongSimpleRoot_B, b2NodeEquiv_symm_apply]
  fin_cases j <;> simp

/-- **The initial carrier node `0` corresponds to the short simple root of `B₂`.** -/
theorem b2NodeEquiv_eq_zero_iff (i : Fin (DynkinType.B 2).rank) :
    b2NodeEquiv i = 0 ↔ ¬ (DynkinType.B 2).IsLongSimpleRoot i := by
  rw [← b2NodeEquiv_eq_one_iff]
  generalize b2NodeEquiv i = c
  fin_cases c <;> decide

noncomputable section

private abbrev validB2 : (DynkinType.B 2).Valid := DynkinType.valid_B.mpr le_rfl

private theorem isSerreSystem_b2 :
    IsSerreSystem ℚ (DynkinType.B 2).cartanMatrix.transpose
      (fun i => cartanGenerator 1 (b2NodeEquiv i))
      (fun i => rootGenerator 1 (.inl (b2NodeEquiv i)))
      (fun i => rootGenerator 1 (.inr (b2NodeEquiv i))) := by
  have h := (isSerreSystem_rootGenerator 1).submatrix (f := b2NodeEquiv) b2NodeEquiv.injective
  have hCM : (CartanMatrix.C 2).transpose.submatrix b2NodeEquiv b2NodeEquiv =
      (DynkinType.B 2).cartanMatrix.transpose := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.transpose_apply]
    have hC := DynkinType.cartanMatrix_C_two_apply_eq_cartanMatrix_B_two
      (b2NodeEquiv j) (b2NodeEquiv i)
    rw [DynkinType.cartanMatrix_C] at hC
    exact hC.trans (by
      rw [← b2NodeEquiv_symm_apply, ← b2NodeEquiv_symm_apply,
        Equiv.symm_apply_apply, Equiv.symm_apply_apply])
  simpa only [hCM, Function.comp_def] using h

private def b2PinnedLieHom :
    (DynkinType.B 2).lieAlgebra validB2 →ₗ⁅ℚ⁆ sp (Fin 2) ℚ :=
  (serreLift isSerreSystem_b2).comp ((DynkinType.B 2).serreLiftEquiv validB2).symm.toLieHom

private theorem b2PinnedLieHom_surjective : Function.Surjective b2PinnedLieHom := by
  have hpos : Set.range (fun i : Fin (DynkinType.B 2).rank =>
      rootGenerator 1 (.inl (b2NodeEquiv i))) =
        Set.range (fun i : Fin 2 => rootGenerator 1 (.inl i)) :=
    b2NodeEquiv.surjective.range_comp (fun i => rootGenerator 1 (.inl i))
  have hneg : Set.range (fun i : Fin (DynkinType.B 2).rank =>
      rootGenerator 1 (.inr (b2NodeEquiv i))) =
        Set.range (fun i : Fin 2 => rootGenerator 1 (.inr i)) :=
    b2NodeEquiv.surjective.range_comp (fun i => rootGenerator 1 (.inr i))
  have hspan : LieSubalgebra.lieSpan ℚ (sp (Fin 2) ℚ)
      (Set.range (fun i : Fin (DynkinType.B 2).rank =>
          rootGenerator 1 (.inl (b2NodeEquiv i))) ∪
        Set.range (fun i : Fin (DynkinType.B 2).rank =>
          rootGenerator 1 (.inr (b2NodeEquiv i)))) = ⊤ := by
    rw [hpos, hneg]
    simpa only [Sum.range_eq, Function.comp_def] using lieSpan_range_rootGenerator_eq_top 1
  exact (serreLift_surjective isSerreSystem_b2 hspan).comp
    ((DynkinType.B 2).serreLiftEquiv validB2).symm.surjective

private theorem b2PinnedLieHom_bijective : Function.Bijective b2PinnedLieHom := by
  have hcard : ((DynkinType.B 2).cartanSubalgebra validB2).root.card =
      (DynkinType.B 2).numRoots := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using
      (Fintype.card_congr ((DynkinType.B 2).rootEquiv validB2)).symm
  have hdim : Module.finrank ℚ ((DynkinType.B 2).lieAlgebra validB2) =
      Module.finrank ℚ (sp (Fin 2) ℚ) := by
    rw [finrank_eq_finrank_cartan_add_card_root ((DynkinType.B 2).cartanSubalgebra validB2),
      DynkinType.finrank_cartanSubalgebra, hcard,
      TauCeti.LieAlgebra.Symplectic.finrank_sp, Fintype.card_fin,
      DynkinType.rank_B, DynkinType.numRoots_B]
    norm_num
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr
    b2PinnedLieHom_surjective, b2PinnedLieHom_surjective⟩

/-- **The pinned rational type-`B₂` Lie algebra is the four-by-four symplectic Lie algebra**, with
the Cartan and positive and negative simple-root generators matched across
`TauCeti.SpStd.b2NodeEquiv`. -/
def b2PinnedLieEquiv :
    (DynkinType.B 2).lieAlgebra (DynkinType.valid_B.mpr le_rfl) ≃ₗ⁅ℚ⁆ sp (Fin 2) ℚ :=
  LieEquiv.ofBijective b2PinnedLieHom b2PinnedLieHom_bijective

private theorem b2PinnedLieEquiv_apply
    (x : (DynkinType.B 2).lieAlgebra (DynkinType.valid_B.mpr le_rfl)) :
    b2PinnedLieEquiv x = serreLift isSerreSystem_b2
      (((DynkinType.B 2).serreLiftEquiv validB2).symm x) := by
  rw [b2PinnedLieEquiv, LieEquiv.ofBijective_toFun, b2PinnedLieHom, LieHom.comp_apply,
    LieEquiv.coe_toLieHom]

/-- The comparison sends each pinned `B₂` Cartan generator to the standard simple coroot at the
swapped symplectic node. -/
@[simp]
theorem b2PinnedLieEquiv_lieBasis_h {ht : (DynkinType.B 2).Valid}
    (i : Fin (DynkinType.B 2).rank) :
    b2PinnedLieEquiv (((DynkinType.B 2).lieBasis ht).h i) =
      cartanGenerator 1 (b2NodeEquiv i) := by
  rw [b2PinnedLieEquiv_apply]
  exact (congrArg (serreLift isSerreSystem_b2)
    ((DynkinType.B 2).serreLiftEquiv_symm_lieBasis_h validB2 i)).trans
    (serreLift_serreH isSerreSystem_b2 i)

/-- The comparison sends each pinned `B₂` raising generator to the standard positive simple root at
the swapped symplectic node. -/
@[simp]
theorem b2PinnedLieEquiv_lieBasis_e {ht : (DynkinType.B 2).Valid}
    (i : Fin (DynkinType.B 2).rank) :
    b2PinnedLieEquiv (((DynkinType.B 2).lieBasis ht).e i) =
      rootGenerator 1 (.inl (b2NodeEquiv i)) := by
  rw [b2PinnedLieEquiv_apply]
  exact (congrArg (serreLift isSerreSystem_b2)
    ((DynkinType.B 2).serreLiftEquiv_symm_lieBasis_e validB2 i)).trans
    (serreLift_serreE isSerreSystem_b2 i)

/-- The comparison sends each pinned `B₂` lowering generator to the standard negative simple root
at the swapped symplectic node. -/
@[simp]
theorem b2PinnedLieEquiv_lieBasis_f {ht : (DynkinType.B 2).Valid}
    (i : Fin (DynkinType.B 2).rank) :
    b2PinnedLieEquiv (((DynkinType.B 2).lieBasis ht).f i) =
      rootGenerator 1 (.inr (b2NodeEquiv i)) := by
  rw [b2PinnedLieEquiv_apply]
  exact (congrArg (serreLift isSerreSystem_b2)
    ((DynkinType.B 2).serreLiftEquiv_symm_lieBasis_f validB2 i)).trans
    (serreLift_serreF isSerreSystem_b2 i)

/-- On the signed simple-root family, the comparison acts by `TauCeti.SpStd.b2NodeEquiv` on both
signs. -/
@[simp↓]
theorem b2PinnedLieEquiv_lieBasis_rootGenerator {ht : (DynkinType.B 2).Valid}
    (k : Fin (DynkinType.B 2).rank ⊕ Fin (DynkinType.B 2).rank) :
    b2PinnedLieEquiv (((DynkinType.B 2).lieBasis ht).rootGenerator k) =
      rootGenerator 1 (Sum.map b2NodeEquiv b2NodeEquiv k) := by
  cases k with
  | inl i =>
      rw [LieAlgebra.Basis.rootGenerator_inl, Sum.map_inl, b2PinnedLieEquiv_lieBasis_e]
  | inr i =>
      rw [LieAlgebra.Basis.rootGenerator_inr, Sum.map_inr, b2PinnedLieEquiv_lieBasis_f]

/-- The inverse comparison sends each standard symplectic simple coroot to the pinned `B₂` Cartan
generator at the swapped node. -/
@[simp]
theorem b2PinnedLieEquiv_symm_cartanGenerator (i : Fin 2) :
    b2PinnedLieEquiv.symm (cartanGenerator 1 i) =
      ((DynkinType.B 2).lieBasis (DynkinType.valid_B.mpr le_rfl)).h (b2NodeEquiv.symm i) := by
  rw [LieEquiv.symm_apply_eq, b2PinnedLieEquiv_lieBasis_h, Equiv.apply_symm_apply]

/-- The inverse comparison sends each standard positive simple root to the pinned `B₂` raising
generator at the swapped node. -/
@[simp]
theorem b2PinnedLieEquiv_symm_rootGenerator_inl (i : Fin 2) :
    b2PinnedLieEquiv.symm (rootGenerator 1 (.inl i)) =
      ((DynkinType.B 2).lieBasis (DynkinType.valid_B.mpr le_rfl)).e (b2NodeEquiv.symm i) := by
  rw [LieEquiv.symm_apply_eq, b2PinnedLieEquiv_lieBasis_e, Equiv.apply_symm_apply]

/-- The inverse comparison sends each standard negative simple root to the pinned `B₂` lowering
generator at the swapped node. -/
@[simp]
theorem b2PinnedLieEquiv_symm_rootGenerator_inr (i : Fin 2) :
    b2PinnedLieEquiv.symm (rootGenerator 1 (.inr i)) =
      ((DynkinType.B 2).lieBasis (DynkinType.valid_B.mpr le_rfl)).f (b2NodeEquiv.symm i) := by
  rw [LieEquiv.symm_apply_eq, b2PinnedLieEquiv_lieBasis_f, Equiv.apply_symm_apply]

/-- The inverse comparison sends the signed simple-root family of `sp₄` to the pinned `B₂` signed
simple-root family reindexed by `b2NodeEquiv.symm`. -/
theorem b2PinnedLieEquiv_symm_rootGenerator (k : Fin 2 ⊕ Fin 2) :
    b2PinnedLieEquiv.symm (rootGenerator 1 k) =
      ((DynkinType.B 2).lieBasis (DynkinType.valid_B.mpr le_rfl)).rootGenerator
        (Sum.map b2NodeEquiv.symm b2NodeEquiv.symm k) := by
  cases k with
  | inl i =>
      rw [Sum.map_inl, LieAlgebra.Basis.rootGenerator_inl, b2PinnedLieEquiv_symm_rootGenerator_inl]
  | inr i =>
      rw [Sum.map_inr, LieAlgebra.Basis.rootGenerator_inr, b2PinnedLieEquiv_symm_rootGenerator_inr]

end

end TauCeti.SpStd
