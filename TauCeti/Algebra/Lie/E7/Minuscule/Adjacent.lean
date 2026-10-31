/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Carrier
public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Adjacent

/-!
# Adjacent-root Heisenberg subgroups of the native E7 carrier

For either common sign and every commutative base ring, two adjacent simple-root
subgroups generate an embedded copy of the existing Heisenberg group. Its central
parameter is the ordered edge commutator. The three coordinates are unique even
in characteristics two and three.
-/

public section

open scoped commutatorElement
open Multiplicative TauCeti.DynkinType

namespace TauCeti.E7Minuscule

variable (positive : Bool) (i j : Fin 7) (R : Type*) [CommRing R]

/-- The signed simple-root index: `true` means positive and `false` means negative. -/
def signedRootIndex (positive : Bool) (i : Fin 7) : Fin 7 ⊕ Fin 7 :=
  if positive then .inl i else .inr i

/-- The positive sign selects the existing positive simple-root index. -/
@[simp] theorem signedRootIndex_true (i : Fin 7) : signedRootIndex true i = .inl i := by rfl

/-- The negative sign selects the existing negative simple-root index. -/
@[simp] theorem signedRootIndex_false (i : Fin 7) : signedRootIndex false i = .inr i := by rfl

/-- The integral matrix of a signed simple root in the minuscule weight basis. -/
def signedRootMatrix (positive : Bool) (i : Fin 7) : Matrix (Fin 56) (Fin 56) ℤ :=
  if positive then raisingMatrix i else loweringMatrix i

/-- Positive simple roots use the existing raising matrices. -/
@[simp] theorem signedRootMatrix_true (i : Fin 7) :
    signedRootMatrix true i = raisingMatrix i := by rfl

/-- Negative simple roots use the existing lowering matrices. -/
@[simp] theorem signedRootMatrix_false (i : Fin 7) :
    signedRootMatrix false i = loweringMatrix i := by rfl

private def signedWeightTable (positive : Bool) : MinusculeWeightTable (Fin 7) (Fin 56) :=
  if positive then weightTable else weightTable.negWeights

private theorem signedWeightTable_cartanMatrix :
    (signedWeightTable positive).cartanMatrix = CartanMatrix.E 7 := by
  cases positive <;> simp [signedWeightTable]

private theorem signedWeightTable_raisingMatrix :
    (signedWeightTable positive).raisingMatrix i = signedRootMatrix positive i := by
  cases positive
  · simp only [signedWeightTable, Bool.false_eq_true, ite_false, signedRootMatrix,
      MinusculeWeightTable.negWeights_raisingMatrix]
    ext a b
    simp only [MinusculeWeightTable.loweringMatrix_apply, loweringMatrix_apply,
      weightTable_weight, weightTable_reflection]
  · simp [signedWeightTable, signedRootMatrix]

private theorem signedWeightTable_exists_neg_one :
    ∃ a, (signedWeightTable positive).weight a i = -1 := by
  cases positive
  · obtain ⟨a, ha⟩ := exists_e7MinusculeWeight_apply_eq_one i
    exact ⟨a, by simpa [signedWeightTable] using congrArg Neg.neg ha⟩
  · simpa [signedWeightTable] using exists_e7MinusculeWeight_apply_eq_neg_one i

/-- The signed simple-root matrix formula on native carrier points. -/
theorem coe_rootSubgroupPoints_signed (t : R) :
    ((rootSubgroupPoints (signedRootIndex positive i) R (ofAdd t) :
      Matrix.GeneralLinearGroup (Fin 56) R) : Matrix (Fin 56) (Fin 56) R) =
        1 + t • (signedRootMatrix positive i).map Int.cast := by
  cases positive <;> simp only [signedRootIndex, Bool.false_eq_true, ite_false,
    ite_true, signedRootMatrix, coe_rootSubgroupPoints_inl, coe_rootSubgroupPoints_inr, toAdd_ofAdd]

private theorem adjacent_symm (hij : CartanMatrix.E 7 i j = -1) :
    CartanMatrix.E 7 j i = -1 := by
  rw [(CartanMatrix.E_isSymm 7).apply i j]
  exact hij

/-- The ordered adjacent-edge commutator parameter, defined inside the native carrier. -/
noncomputable def adjacentRootCommutator (t : R) : points R :=
  ⁅rootSubgroupPoints (signedRootIndex positive i) R (ofAdd t),
    rootSubgroupPoints (signedRootIndex positive j) R (ofAdd 1)⁆

private theorem coe_commutator_rootSubgroupPoints (hij : CartanMatrix.E 7 i j = -1) (s t : R) :
    (((⁅rootSubgroupPoints (signedRootIndex positive i) R (ofAdd s),
      rootSubgroupPoints (signedRootIndex positive j) R (ofAdd t)⁆ : points R) :
        Matrix.GeneralLinearGroup (Fin 56) R) : Matrix (Fin 56) (Fin 56) R) =
      1 + (s * t) • (signedWeightTable positive).raisingCommutatorMatrix i j := by
  have h := (signedWeightTable positive).raising_unipotent_commutator i j
    (by simpa only [signedWeightTable_cartanMatrix] using hij)
    (by simpa only [signedWeightTable_cartanMatrix] using adjacent_symm i j hij) s t
  simpa only [commutatorElement_def, ← map_inv, ← ofAdd_neg, Subgroup.coe_mul, Units.val_mul,
    coe_rootSubgroupPoints_signed, signedWeightTable_raisingMatrix] using h

/-- The matrix of the adjacent edge parameter is `1 + t(AB-BA)`. -/
theorem coe_adjacentRootCommutator (hij : CartanMatrix.E 7 i j = -1) (t : R) :
    ((adjacentRootCommutator positive i j R t : Matrix.GeneralLinearGroup (Fin 56) R) :
      Matrix (Fin 56) (Fin 56) R) =
        1 + t • ((signedRootMatrix positive i).map (Int.cast : ℤ → R) *
            (signedRootMatrix positive j).map Int.cast -
          (signedRootMatrix positive j).map Int.cast *
              (signedRootMatrix positive i).map Int.cast) := by
  simpa only [adjacentRootCommutator, mul_one,
    MinusculeWeightTable.raisingCommutatorMatrix_eq,
    signedWeightTable_raisingMatrix] using
    coe_commutator_rootSubgroupPoints positive i j R hij t 1

/-- The two-parameter adjacent Chevalley commutator formula in the designated carrier. -/
theorem commutator_rootSubgroupPoints_adjacent (hij : CartanMatrix.E 7 i j = -1) (s t : R) :
    ⁅rootSubgroupPoints (signedRootIndex positive i) R (ofAdd s),
      rootSubgroupPoints (signedRootIndex positive j) R (ofAdd t)⁆ =
        adjacentRootCommutator positive i j R (s * t) := by
  apply Subtype.ext
  apply Units.ext
  simp only [adjacentRootCommutator, coe_commutator_rootSubgroupPoints positive i j R hij,
    mul_one]

private theorem coe_adjacentHeisenberg_product (hij : CartanMatrix.E 7 i j = -1)
    (g : HeisenbergGroup R) :
    (((rootSubgroupPoints (signedRootIndex positive j) R (ofAdd g.y) *
        rootSubgroupPoints (signedRootIndex positive i) R (ofAdd g.x) *
        adjacentRootCommutator positive i j R g.z : points R) :
          Matrix.GeneralLinearGroup (Fin 56) R) :
          Matrix (Fin 56) (Fin 56) R) =
      (signedWeightTable positive).raisingHeisenbergMatrix i j g := by
  rw [(signedWeightTable positive).raisingHeisenbergMatrix_eq_mul i j
    (by simpa only [signedWeightTable_cartanMatrix] using hij)
    (by simpa only [signedWeightTable_cartanMatrix] using adjacent_symm i j hij)]
  simp only [Subgroup.coe_mul, Units.val_mul, coe_rootSubgroupPoints_signed,
    coe_adjacentRootCommutator positive i j R hij,
    MinusculeWeightTable.raisingCommutatorMatrix_eq, signedWeightTable_raisingMatrix]

/-- The faithful ordered Heisenberg parametrization of an adjacent pair of signed roots. -/
noncomputable def adjacentHeisenbergHom (hij : CartanMatrix.E 7 i j = -1) :
    HeisenbergGroup R →* points R where
  toFun g := rootSubgroupPoints (signedRootIndex positive j) R (ofAdd g.y) *
    rootSubgroupPoints (signedRootIndex positive i) R (ofAdd g.x) *
      adjacentRootCommutator positive i j R g.z
  map_one' := by simp [adjacentRootCommutator, commutatorElement_def]
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    have hmul := (signedWeightTable positive).raisingHeisenbergMatrix_mul i j
      (by simpa only [signedWeightTable_cartanMatrix] using hij)
      (by simpa only [signedWeightTable_cartanMatrix] using adjacent_symm i j hij) g h
    simpa only [← coe_adjacentHeisenberg_product positive i j R hij,
      Subgroup.coe_mul, Units.val_mul] using hmul

/-- The ordered root-factor formula for the native Heisenberg homomorphism. -/
theorem adjacentHeisenbergHom_apply (hij : CartanMatrix.E 7 i j = -1) (g : HeisenbergGroup R) :
    adjacentHeisenbergHom positive i j R hij g =
      rootSubgroupPoints (signedRootIndex positive j) R (ofAdd g.y) *
        rootSubgroupPoints (signedRootIndex positive i) R (ofAdd g.x) *
          adjacentRootCommutator positive i j R g.z := by rfl

/-- The native Heisenberg parametrization is injective over every commutative ring. -/
theorem adjacentHeisenbergHom_injective (hij : CartanMatrix.E 7 i j = -1) :
    Function.Injective (adjacentHeisenbergHom positive i j R hij) := by
  intro g h he
  apply (signedWeightTable positive).raisingHeisenbergMatrix_injective i j
    (by simpa only [signedWeightTable_cartanMatrix] using hij)
    (by simpa only [signedWeightTable_cartanMatrix] using adjacent_symm i j hij)
    (signedWeightTable_exists_neg_one positive i)
  have he' := congrArg (fun g : points R ↦
    ((g : Matrix.GeneralLinearGroup (Fin 56) R) : Matrix (Fin 56) (Fin 56) R)) he
  simpa only [adjacentHeisenbergHom_apply,
    coe_adjacentHeisenberg_product positive i j R hij] using he'

/-- The first coordinate is the signed simple-root subgroup at `i`. -/
@[simp] theorem adjacentHeisenbergHom_x (hij : CartanMatrix.E 7 i j = -1) (x : R) :
    adjacentHeisenbergHom positive i j R hij ⟨x, 0, 0⟩ =
      rootSubgroupPoints (signedRootIndex positive i) R (ofAdd x) := by
  simp [adjacentHeisenbergHom_apply, adjacentRootCommutator, commutatorElement_def]

/-- The second coordinate is the signed simple-root subgroup at `j`. -/
@[simp] theorem adjacentHeisenbergHom_y (hij : CartanMatrix.E 7 i j = -1) (y : R) :
    adjacentHeisenbergHom positive i j R hij ⟨0, y, 0⟩ =
      rootSubgroupPoints (signedRootIndex positive j) R (ofAdd y) := by
  simp [adjacentHeisenbergHom_apply, adjacentRootCommutator, commutatorElement_def]

/-- The central coordinate is the ordered adjacent-edge commutator. -/
@[simp] theorem adjacentHeisenbergHom_z (hij : CartanMatrix.E 7 i j = -1) (z : R) :
    adjacentHeisenbergHom positive i j R hij ⟨0, 0, z⟩ =
      adjacentRootCommutator positive i j R z := by
  simp [adjacentHeisenbergHom_apply]

/-- The edge commutator is an additive one-parameter subgroup of the native carrier. -/
noncomputable def adjacentRootCommutatorHom (hij : CartanMatrix.E 7 i j = -1) :
    Multiplicative R →* points R where
  toFun t := adjacentRootCommutator positive i j R (toAdd t)
  map_one' := by simp [adjacentRootCommutator, commutatorElement_def]
  map_mul' s t := by
    have h := (adjacentHeisenbergHom positive i j R hij).map_mul
      ⟨0, 0, toAdd s⟩ ⟨0, 0, toAdd t⟩
    have he : (⟨0, 0, toAdd s⟩ : HeisenbergGroup R) * ⟨0, 0, toAdd t⟩ =
        ⟨0, 0, toAdd s + toAdd t⟩ := by ext <;> simp
    rw [he, adjacentHeisenbergHom_z, adjacentHeisenbergHom_z,
      adjacentHeisenbergHom_z] at h
    exact h

/-- Evaluation of the additive edge subgroup. -/
@[simp] theorem adjacentRootCommutatorHom_apply (hij : CartanMatrix.E 7 i j = -1) (t : R) :
    adjacentRootCommutatorHom positive i j R hij (ofAdd t) =
      adjacentRootCommutator positive i j R t := by rfl

/-- The edge parameter is faithful, without inverting two or three. -/
theorem adjacentRootCommutator_injective (hij : CartanMatrix.E 7 i j = -1) :
    Function.Injective (adjacentRootCommutator positive i j R) := by
  intro s t h
  have he : adjacentHeisenbergHom positive i j R hij ⟨0, 0, s⟩ =
      adjacentHeisenbergHom positive i j R hij ⟨0, 0, t⟩ := by simpa using h
  exact congrArg HeisenbergGroup.z
    (adjacentHeisenbergHom_injective positive i j R hij he)

/-- The edge subgroup commutes with the first simple-root subgroup. -/
theorem adjacentRootCommutator_commute_left (hij : CartanMatrix.E 7 i j = -1) (s t : R) :
    Commute (adjacentRootCommutator positive i j R s)
      (rootSubgroupPoints (signedRootIndex positive i) R (ofAdd t)) := by
  have h : Commute (⟨0, 0, s⟩ : HeisenbergGroup R) ⟨t, 0, 0⟩ := by
    apply HeisenbergGroup.ext <;> simp
  simpa using h.map (adjacentHeisenbergHom positive i j R hij)

/-- The edge subgroup commutes with the second simple-root subgroup. -/
theorem adjacentRootCommutator_commute_right (hij : CartanMatrix.E 7 i j = -1) (s t : R) :
    Commute (adjacentRootCommutator positive i j R s)
      (rootSubgroupPoints (signedRootIndex positive j) R (ofAdd t)) := by
  have h : Commute (⟨0, 0, s⟩ : HeisenbergGroup R) ⟨0, t, 0⟩ := by
    apply HeisenbergGroup.ext <;> simp
  simpa using h.map (adjacentHeisenbergHom positive i j R hij)

/-- Reversing the ordered adjacent edge negates its central parameter. -/
theorem adjacentRootCommutator_swap (hij : CartanMatrix.E 7 i j = -1) (t : R) :
    adjacentRootCommutator positive j i R t = adjacentRootCommutator positive i j R (-t) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_adjacentRootCommutator positive j i R (adjacent_symm i j hij),
    coe_adjacentRootCommutator positive i j R hij]
  module

/-- The subgroup generated by the two full signed simple-root subgroups. -/
noncomputable def adjacentRootSubgroup : Subgroup (points R) :=
  Subgroup.closure (Set.range (rootSubgroupPoints (signedRootIndex positive i) R) ∪
    Set.range (rootSubgroupPoints (signedRootIndex positive j) R))

/-- The Heisenberg map has exactly the subgroup generated by the adjacent roots as range. -/
theorem adjacentHeisenbergHom_range (hij : CartanMatrix.E 7 i j = -1) :
    (adjacentHeisenbergHom positive i j R hij).range =
      adjacentRootSubgroup positive i j R := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    have hi (t : Multiplicative R) :
        rootSubgroupPoints (signedRootIndex positive i) R t ∈
          adjacentRootSubgroup positive i j R :=
      Subgroup.subset_closure (Or.inl ⟨t, rfl⟩)
    have hj (t : Multiplicative R) :
        rootSubgroupPoints (signedRootIndex positive j) R t ∈
          adjacentRootSubgroup positive i j R :=
      Subgroup.subset_closure (Or.inr ⟨t, rfl⟩)
    rw [adjacentHeisenbergHom_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hj _) (hi _))
      (by simpa only [adjacentRootCommutator, commutatorElement_def] using
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hi _) (hj _))
          (Subgroup.inv_mem _ (hi _))) (Subgroup.inv_mem _ (hj _)))
  · apply (Subgroup.closure_le _).2
    rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact ⟨⟨toAdd t, 0, 0⟩, by simp⟩
    · exact ⟨⟨0, toAdd t, 0⟩, by simp⟩

/-- Every element of the adjacent-root subgroup has unique Heisenberg coordinates. -/
theorem existsUnique_adjacentHeisenberg_coordinates (hij : CartanMatrix.E 7 i j = -1)
    (g : points R) (hg : g ∈ adjacentRootSubgroup positive i j R) :
    ∃! c : HeisenbergGroup R, adjacentHeisenbergHom positive i j R hij c = g := by
  rw [← adjacentHeisenbergHom_range positive i j R hij] at hg
  obtain ⟨c, hc⟩ := hg
  exact ⟨c, hc, fun d hd ↦ adjacentHeisenbergHom_injective positive i j R hij (hd.trans hc.symm)⟩

/-- The adjacent-root subgroup is the existing Heisenberg group over the base ring. -/
noncomputable def adjacentHeisenbergEquiv (hij : CartanMatrix.E 7 i j = -1) :
    HeisenbergGroup R ≃* adjacentRootSubgroup positive i j R :=
  MulEquiv.ofBijective
    ((adjacentHeisenbergHom positive i j R hij).codRestrict
      (adjacentRootSubgroup positive i j R) (fun c ↦ by
        rw [← adjacentHeisenbergHom_range positive i j R hij]
        exact ⟨c, rfl⟩))
    ⟨fun _ _ h ↦ adjacentHeisenbergHom_injective positive i j R hij (congrArg Subtype.val h),
      fun g ↦ by
        obtain ⟨c, hc, _⟩ := existsUnique_adjacentHeisenberg_coordinates
          positive i j R hij g g.property
        exact ⟨c, Subtype.ext hc⟩⟩

/-- The equivalence retains the ordered native root-factor coordinates. -/
@[simp] theorem coe_adjacentHeisenbergEquiv (hij : CartanMatrix.E 7 i j = -1)
    (g : HeisenbergGroup R) :
    (adjacentHeisenbergEquiv positive i j R hij g : points R) =
      adjacentHeisenbergHom positive i j R hij g := by rfl

/-- Torus conjugation rescales the edge parameter by the product of its signed root characters. -/
theorem weightTorusPoints_conj_adjacentRootCommutator (hij : CartanMatrix.E 7 i j = -1)
    (s : Fin 7 → Rˣ) (t : R) :
    weightTorusPoints R s * adjacentRootCommutator positive i j R t *
        (weightTorusPoints R s)⁻¹ =
      adjacentRootCommutator positive i j R
        ((torusCharacter s (DynkinType.E7.rootGeneratorWeight valid_E7
          (signedRootIndex positive i)) : R) *
          (torusCharacter s (DynkinType.E7.rootGeneratorWeight valid_E7
            (signedRootIndex positive j)) : R) * t) := by
  -- View conjugation as an automorphism to transport the commutator.
  change MulAut.conj (weightTorusPoints R s)
    (adjacentRootCommutator positive i j R t) = _
  rw [adjacentRootCommutator, map_commutatorElement]
  -- Evaluate that automorphism to use the existing torus conjugation equations.
  change ⁅weightTorusPoints R s * _ * (weightTorusPoints R s)⁻¹,
    weightTorusPoints R s * _ * (weightTorusPoints R s)⁻¹⁆ = _
  rw [weightTorusPoints_conj_rootSubgroupPoints, weightTorusPoints_conj_rootSubgroupPoints]
  simp only [toAdd_ofAdd, mul_one, commutator_rootSubgroupPoints_adjacent positive i j R hij]
  congr 1
  ring

end TauCeti.E7Minuscule
