/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.TableRow.Symmetry
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.Triality

/-!
# The coupled triality symmetry of the table row `A₅⁴ D₄`

In the rootful rank-24 table, `TauCeti.RootfulNiemeierType.a5FourthD4` is the unique row whose
parenthesized pattern symmetry is not a pure coordinate glue symmetry: its glue columns are
`[2(024)0]`, `[33001]`, `[30302]`, and `[30033]`, and rotating the three marked `A₅` positions
`1, 2, 3` while leaving the `D₄` label in position `4` unchanged sends `[33001]` outside the glue
subgroup (`not_mem_glueSymmetries_a5FourthD4BlockRot`).

Because the three literal generators cycle the nonzero `D₄` labels `1 ↦ 2 ↦ 3 ↦ 1` (`s ↦ v ↦ c ↦ s`)
in lockstep with the three marked `A₅` positions, coupling the block rotation with `D₄` triality
(`TauCeti.DynkinType.typeD4Triality`) on the `D₄` component preserves `a5FourthD4.glueSubgroup` and
lifts to an order-three self-isometry `TauCeti.RootfulNiemeierType.a5FourthD4TrialityRotation` of
`TauCeti.niemeierA5FourthD4`.  This yields a faithful action
`TauCeti.RootfulNiemeierType.a5FourthD4CyclicSymmetryHom` of the cyclic pattern's symmetry group,
and hence a faithful lattice action `TauCeti.RootfulNiemeierType.coupledPatternIsometryHom` for
every pattern of every row of the rootful rank-24 table without exception.

## Main declarations

* `TauCeti.RootfulNiemeierType.a5FourthD4BlockRot`: the cyclic rotation of positions `1, 2, 3`
  generating `(GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries`.
* `TauCeti.RootfulNiemeierType.not_mem_glueSymmetries_a5FourthD4BlockRot`: the uncoupled block
  rotation is not a glue symmetry of `a5FourthD4`.
* `TauCeti.RootfulNiemeierType.a5FourthD4TrialityRotation`: the order-three self-isometry of
  `niemeierA5FourthD4` rotating the three marked `A₅` components and applying `typeD4Triality` on
  the `D₄` component.
* `TauCeti.RootfulNiemeierType.a5FourthD4CyclicSymmetryHom`: faithful action of
  `(GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries` on `niemeierA5FourthD4`.
* `TauCeti.RootfulNiemeierType.coupledPatternIsometryHom`,
  `TauCeti.RootfulNiemeierType.coupledPatternIsometryHom_injective`: faithful action of every
  pattern symmetry group across all 23 rootful Niemeier rows.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4
  §§3 and 7, and Chapter 16 §1, Table 16.1.
-/

public section

namespace TauCeti

namespace RootfulNiemeierType

open DynkinType IntegralLattice

/-! ### The marked-block rotation of `[2(024)0]` and its uncoupled obstruction -/

/-- **The marked-block rotation of `A₅⁴ D₄`**: the 3-cycle `1 ↦ 2 ↦ 3 ↦ 1` fixing positions `0` and
`4`, which generates `(GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries`. -/
def a5FourthD4BlockRot : Equiv.Perm (Fin 5) :=
  Equiv.Perm.finSumPerm (Equiv.Perm.finSumPerm (1 : Equiv.Perm (Fin 1)) (finRotate 3))
    (1 : Equiv.Perm (Fin 1))

/-- `a5FourthD4BlockRot` is the 3-cycle `swap 1 2 * swap 2 3` on `Fin 5`. -/
theorem a5FourthD4BlockRot_eq_swap_mul_swap :
    a5FourthD4BlockRot = Equiv.swap 1 2 * Equiv.swap 2 3 := by
  apply Equiv.ext
  intro i
  -- Write each element of `Fin 5` in `Fin (1 + 3 + 1)` block form so `finSumPerm_apply_*` applies.
  fin_cases i
  · change a5FourthD4BlockRot (Fin.castAdd 1 (Fin.castAdd 3 (0 : Fin 1))) = _
    rw [a5FourthD4BlockRot, Equiv.Perm.finSumPerm_apply_castAdd,
      Equiv.Perm.finSumPerm_apply_castAdd]
    decide
  · change a5FourthD4BlockRot (Fin.castAdd 1 (Fin.natAdd 1 (0 : Fin 3))) = _
    rw [a5FourthD4BlockRot, Equiv.Perm.finSumPerm_apply_castAdd,
      Equiv.Perm.finSumPerm_apply_natAdd]
    decide
  · change a5FourthD4BlockRot (Fin.castAdd 1 (Fin.natAdd 1 (1 : Fin 3))) = _
    rw [a5FourthD4BlockRot, Equiv.Perm.finSumPerm_apply_castAdd,
      Equiv.Perm.finSumPerm_apply_natAdd]
    decide
  · change a5FourthD4BlockRot (Fin.castAdd 1 (Fin.natAdd 1 (2 : Fin 3))) = _
    rw [a5FourthD4BlockRot, Equiv.Perm.finSumPerm_apply_castAdd,
      Equiv.Perm.finSumPerm_apply_natAdd]
    decide
  · change a5FourthD4BlockRot (Fin.natAdd 4 (0 : Fin 1)) = _
    rw [a5FourthD4BlockRot, Equiv.Perm.finSumPerm_apply_natAdd]
    decide

@[simp]
theorem a5FourthD4BlockRot_zero : a5FourthD4BlockRot 0 = 0 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

@[simp]
theorem a5FourthD4BlockRot_one : a5FourthD4BlockRot 1 = 2 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

@[simp]
theorem a5FourthD4BlockRot_two : a5FourthD4BlockRot 2 = 3 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

@[simp]
theorem a5FourthD4BlockRot_three : a5FourthD4BlockRot 3 = 1 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

@[simp]
theorem a5FourthD4BlockRot_four : a5FourthD4BlockRot 4 = 4 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

@[simp]
theorem a5FourthD4BlockRot_inv_zero : a5FourthD4BlockRot⁻¹ 0 = 0 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

@[simp]
theorem a5FourthD4BlockRot_inv_one : a5FourthD4BlockRot⁻¹ 1 = 3 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

@[simp]
theorem a5FourthD4BlockRot_inv_two : a5FourthD4BlockRot⁻¹ 2 = 1 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

@[simp]
theorem a5FourthD4BlockRot_inv_three : a5FourthD4BlockRot⁻¹ 3 = 2 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

@[simp]
theorem a5FourthD4BlockRot_inv_four : a5FourthD4BlockRot⁻¹ 4 = 4 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

/-- `a5FourthD4BlockRot` has order three. -/
@[simp]
theorem a5FourthD4BlockRot_pow_three : a5FourthD4BlockRot ^ 3 = 1 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

/-- `a5FourthD4BlockRot` belongs to the symmetry group of the cyclic pattern `[2(024)0]`. -/
theorem a5FourthD4BlockRot_mem_symmetries :
    a5FourthD4BlockRot ∈ (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries := by
  rw [GluePattern.symmetries_cyclic]
  exact Subgroup.mem_zpowers _

private theorem glueLabelWord_mem_a5FourthD4_glueSubgroup
    (d : ∀ i : Fin a5FourthD4.components.length, Fin (a5FourthD4.componentType i).glueLabelCount)
    (hd : (List.ofFn fun i ↦ (d i).val) ∈ a5FourthD4.glueWords) :
    (fun i ↦ (a5FourthD4.componentType i).glueLabelEquiv
      (a5FourthD4.isSimplyLaced_componentType i) (d i)) ∈ a5FourthD4.glueSubgroup := by
  rw [glueSubgroup_def]
  refine AddSubgroup.subset_closure (mem_glueGenerators_iff.mpr ?_)
  rwa [encodeGlueWord_glueLabelEquiv]

/-- **The uncoupled block rotation of `[2(024)0]` is not a glue symmetry of `A₅⁴ D₄`**: reindexing
`[33001]` along `a5FourthD4BlockRot` gives `[30031]`, whose sum with `[30033]` is the nonzero glue
word `[00002]` of shortest norm `1 < 4`. -/
theorem not_mem_glueSymmetries_a5FourthD4BlockRot :
    (a5FourthD4BlockRot : Equiv.Perm (Fin a5FourthD4.components.length)) ∉
      a5FourthD4.glueSymmetries := by
  intro hrot
  let d₁ : ∀ i : Fin 5, Fin (a5FourthD4.componentType i).glueLabelCount :=
    fun i ↦ ⟨![3, 3, 0, 0, 1] i, by fin_cases i <;> decide⟩
  let d₃ : ∀ i : Fin 5, Fin (a5FourthD4.componentType i).glueLabelCount :=
    fun i ↦ ⟨![3, 0, 0, 3, 3] i, by fin_cases i <;> decide⟩
  let w₁ : a5FourthD4.glueModule := fun i ↦
    (a5FourthD4.componentType i).glueLabelEquiv (a5FourthD4.isSimplyLaced_componentType i) (d₁ i)
  let w₃ : a5FourthD4.glueModule := fun i ↦
    (a5FourthD4.componentType i).glueLabelEquiv (a5FourthD4.isSimplyLaced_componentType i) (d₃ i)
  let v := piGlueAlphabetCongr a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType
    a5FourthD4BlockRot (a5FourthD4.componentType_apply_of_mem_glueSymmetries hrot)
    (hs := a5FourthD4.isSimplyLaced_componentType) w₁
  have hv : v ∈ a5FourthD4.glueSubgroup :=
    (a5FourthD4.piGlueAlphabetCongr_mem_glueSubgroup_iff hrot w₁).mpr
      (glueLabelWord_mem_a5FourthD4_glueSubgroup d₁ (by decide))
  have hw₃ : w₃ ∈ a5FourthD4.glueSubgroup :=
    glueLabelWord_mem_a5FourthD4_glueSubgroup d₃ (by decide)
  have hv_enc : encodeGlueWord a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType v =
      [3, 0, 0, 3, 1] := by
    refine (encodeGlueWord_piGlueAlphabetCongr_eq_ofFn _ _ _ _ _ w₁).trans ?_
    refine (congrArg List.ofFn (funext fun k : Fin 5 ↦
      congrArg Fin.val (Equiv.symm_apply_apply _ (d₁ (a5FourthD4BlockRot k))))).trans ?_
    dsimp only [d₁]
    rw [a5FourthD4BlockRot_eq_swap_mul_swap]
    decide
  have hw₃_enc :
      encodeGlueWord a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType w₃ =
        [3, 0, 0, 3, 3] := by
    rw [encodeGlueWord_glueLabelEquiv]
    decide
  have henc : encodeGlueWord a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType
      (v + w₃) = [0, 0, 0, 0, 2] := by
    refine (encodeGlueWord_add _ _ v w₃).trans ?_
    rw [hv_enc, hw₃_enc]
    decide +kernel
  have hne : v + w₃ ≠ 0 := fun h0 ↦ absurd
    (henc.symm.trans ((congrArg (encodeGlueWord a5FourthD4.componentType
      a5FourthD4.isSimplyLaced_componentType) h0).trans (encodeGlueWord_zero _ _))) (by decide)
  have hmin := four_le_sum_glueMinimum_of_mem_glueSubgroup a5FourthD4 (add_mem hv hw₃) hne
  rw [← glueWordMinimum_encodeGlueWord, henc] at hmin
  exact absurd hmin (by decide +kernel)

/-! ### Lifting `[2(024)0]` to `niemeierA5FourthD4` via `D₄` triality -/

private theorem componentType_a5FourthD4BlockRot_inv (k : Fin a5FourthD4.components.length) :
    a5FourthD4.componentType ((a5FourthD4BlockRot⁻¹ : Equiv.Perm (Fin 5)) k) =
      a5FourthD4.componentType k := by
  have h : ∀ j : Fin 5,
      a5FourthD4.componentType (a5FourthD4BlockRot⁻¹ j) = a5FourthD4.componentType j
    | 0 => by rw [a5FourthD4BlockRot_inv_zero]
    | 1 => by rw [a5FourthD4BlockRot_inv_one]; rfl
    | 2 => by rw [a5FourthD4BlockRot_inv_two]; rfl
    | 3 => by rw [a5FourthD4BlockRot_inv_three]; rfl
    | 4 => by rw [a5FourthD4BlockRot_inv_four]
  exact h k

private noncomputable def a5FourthD4ComponentIsometry :
    ∀ k : Fin a5FourthD4.components.length, Isometry
      ((a5FourthD4.componentType k).rootLattice (a5FourthD4.isSimplyLaced_componentType k))
      ((a5FourthD4.componentType k).rootLattice (a5FourthD4.isSimplyLaced_componentType k))
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => Isometry.refl _
  | ⟨4, h⟩ => typeD4Triality (a5FourthD4.isSimplyLaced_componentType ⟨4, h⟩)
  | ⟨_ + 5, h⟩ => False.elim (Nat.not_lt_of_ge (Nat.le_add_left 5 _) h)

private noncomputable def a5FourthD4ComponentGlueEquiv :
    ∀ k : Fin a5FourthD4.components.length,
      (a5FourthD4.componentType k).glueAlphabet (a5FourthD4.isSimplyLaced_componentType k) ≃+
        (a5FourthD4.componentType k).glueAlphabet (a5FourthD4.isSimplyLaced_componentType k)
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => AddEquiv.refl _
  | ⟨4, h⟩ =>
    (typeD4TrialityGlueAlphabetIsometry
      (a5FourthD4.isSimplyLaced_componentType ⟨4, h⟩)).toLinearEquiv.toAddEquiv
  | ⟨_ + 5, h⟩ => False.elim (Nat.not_lt_of_ge (Nat.le_add_left 5 _) h)

private def a5FourthD4DigitPerm : Fin a5FourthD4.components.length → ℕ → ℕ
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => id
  | ⟨4, _⟩ => (Equiv.swap 1 2 * Equiv.swap 2 3 : Equiv.Perm ℕ)
  | ⟨_ + 5, h⟩ => False.elim (Nat.not_lt_of_ge (Nat.le_add_left 5 _) h)

private theorem a5FourthD4ComponentIsometry_glueAlphabetIsometry
    (k : Fin a5FourthD4.components.length)
    (x : (a5FourthD4.componentType k).glueAlphabet (a5FourthD4.isSimplyLaced_componentType k)) :
    (a5FourthD4.componentType k).glueAlphabetIsometry (a5FourthD4.valid_componentType k)
        (a5FourthD4.isSimplyLaced_componentType k) (a5FourthD4ComponentGlueEquiv k x) =
      (a5FourthD4ComponentIsometry k).discriminantQuadraticIsometry
        ((a5FourthD4.componentType k).isEven_rootLattice (a5FourthD4.isSimplyLaced_componentType k))
        ((a5FourthD4.componentType k).glueAlphabetIsometry (a5FourthD4.valid_componentType k)
          (a5FourthD4.isSimplyLaced_componentType k) x) := by
  have hrefl : ∀ {t : DynkinType} (hv : t.Valid) (ht : t.IsSimplyLaced) (y : t.glueAlphabet ht),
      t.glueAlphabetIsometry hv ht y =
        (Isometry.refl (t.rootLattice ht)).discriminantQuadraticIsometry
          (t.isEven_rootLattice ht) (t.glueAlphabetIsometry hv ht y) := fun hv ht y ↦ by
    refine Eq.trans ?_ (Isometry.discriminantQuadraticIsometry_apply _ _ _).symm
    rw [Isometry.discriminantGroupEquiv_refl]
    rfl
  fin_cases k <;> first
    | exact hrefl _ _ x
    | exact glueAlphabetIsometry_typeD4TrialityGlueAlphabetIsometry _ _ x

private theorem a5FourthD4ComponentGlueEquiv_mem_glueSubgroup_iff (w : a5FourthD4.glueModule) :
    (fun k ↦ a5FourthD4ComponentGlueEquiv k
      (piGlueAlphabetCongr a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType
        (a5FourthD4BlockRot⁻¹ : Equiv.Perm (Fin 5)) componentType_a5FourthD4BlockRot_inv w k)) ∈
      a5FourthD4.glueSubgroup ↔ w ∈ a5FourthD4.glueSubgroup := by
  refine a5FourthD4.coupled_mem_glueSubgroup_iff_of_glueWords
    (g := (a5FourthD4BlockRot⁻¹ : Equiv.Perm (Fin 5))) componentType_a5FourthD4BlockRot_inv
    a5FourthD4ComponentGlueEquiv a5FourthD4DigitPerm (fun k j ↦ ?_) ?_ w
  · fin_cases k <;> first
      | exact (congrArg Fin.val (Equiv.symm_apply_apply _ j)).trans rfl
      | refine (congrArg (fun y ↦ (((D 4).glueLabelEquiv
          (a5FourthD4.isSimplyLaced_componentType (4 : Fin 5))).symm y).val)
            (typeD4TrialityGlueAlphabetIsometry_glueLabelEquiv _ j)).trans ?_
        refine (congrArg Fin.val (Equiv.symm_apply_apply _ _)).trans ?_
        have hj : ∀ m : Fin 4, (typeD4TrialityLabelPerm m).val =
            (Equiv.swap 1 2 * Equiv.swap 2 3 : Equiv.Perm ℕ) m.val
          | 0 => by rw [typeD4TrialityLabelPerm_zero]; decide
          | 1 => by rw [typeD4TrialityLabelPerm_one]; decide
          | 2 => by rw [typeD4TrialityLabelPerm_two]; decide
          | 3 => by rw [typeD4TrialityLabelPerm_three]; decide
        exact hj j
  · -- Specialize `a5FourthD4.components.length` to `5` so `decide` reduces `List.ofFn`.
    change ∀ l ∈ a5FourthD4.glueWords,
      (List.ofFn fun k : Fin 5 ↦
        a5FourthD4DigitPerm k (l.getD (a5FourthD4BlockRot⁻¹ k) 0)) ∈ a5FourthD4.glueWords
    rw [a5FourthD4BlockRot_eq_swap_mul_swap]
    decide

/-- **The coupled triality rotation of `niemeierA5FourthD4`**: the self-isometry moving the three
marked `A₅` components by `1 ↦ 2 ↦ 3 ↦ 1`, fixing the leading `A₅` component `0`, and applying
`TauCeti.DynkinType.typeD4Triality` on the `D₄` component `4`. -/
noncomputable def a5FourthD4TrialityRotation :
    Isometry niemeierA5FourthD4 niemeierA5FourthD4 :=
  a5FourthD4.coupledLatticeIsometry (g := (a5FourthD4BlockRot⁻¹ : Equiv.Perm (Fin 5)))
    componentType_a5FourthD4BlockRot_inv a5FourthD4ComponentIsometry
    (fun k x ↦ a5FourthD4ComponentGlueEquiv k x)
    a5FourthD4ComponentIsometry_glueAlphabetIsometry
    a5FourthD4ComponentGlueEquiv_mem_glueSubgroup_iff

private theorem rootLatticeIsometryOfEq_blockRot_inv_eq
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) (a b : Fin 5)
    (hab : (a5FourthD4BlockRot⁻¹ : Equiv.Perm (Fin 5)) a = b)
    (ht : a5FourthD4.componentType b = a5FourthD4.componentType a) :
    (a5FourthD4.componentType
        ((a5FourthD4BlockRot⁻¹ : Equiv.Perm (Fin 5)) a)).rootLatticeIsometryOfEq
        (a5FourthD4.isSimplyLaced_componentType _) (componentType_a5FourthD4BlockRot_inv a)
        (a5FourthD4.isSimplyLaced_componentType a)
        (x ((a5FourthD4BlockRot⁻¹ : Equiv.Perm (Fin 5)) a)) =
      (a5FourthD4.componentType b).rootLatticeIsometryOfEq
        (a5FourthD4.isSimplyLaced_componentType b) ht
        (a5FourthD4.isSimplyLaced_componentType a) (x b) := by
  subst hab
  rfl

@[simp]
theorem a5FourthD4TrialityRotation_apply_zero
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityRotation x (0 : Fin 5) = x (0 : Fin 5) :=
  (a5FourthD4.coupledLatticeIsometry_apply _ _ _ _ _ x (0 : Fin 5)).trans <|
    (Isometry.refl_apply (V := Fin (A 5).rank → ℚ) _ _).trans <|
      (rootLatticeIsometryOfEq_blockRot_inv_eq x 0 0 a5FourthD4BlockRot_inv_zero rfl).trans <|
        (DFunLike.congr_fun (rootLatticeIsometryOfEq_rfl
          (a5FourthD4.componentType (0 : Fin 5))
          (a5FourthD4.isSimplyLaced_componentType (0 : Fin 5))) (x (0 : Fin 5))).trans <|
          Isometry.refl_apply _ _

@[simp]
theorem a5FourthD4TrialityRotation_apply_one
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityRotation x (1 : Fin 5) = x (3 : Fin 5) :=
  (a5FourthD4.coupledLatticeIsometry_apply _ _ _ _ _ x (1 : Fin 5)).trans <|
    (Isometry.refl_apply (V := Fin (A 5).rank → ℚ) _ _).trans <|
      (rootLatticeIsometryOfEq_blockRot_inv_eq x 1 3 a5FourthD4BlockRot_inv_one rfl).trans <|
        (DFunLike.congr_fun (rootLatticeIsometryOfEq_rfl
          (a5FourthD4.componentType (3 : Fin 5))
          (a5FourthD4.isSimplyLaced_componentType (3 : Fin 5))) (x (3 : Fin 5))).trans <|
          Isometry.refl_apply _ _

@[simp]
theorem a5FourthD4TrialityRotation_apply_two
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityRotation x (2 : Fin 5) = x (1 : Fin 5) :=
  (a5FourthD4.coupledLatticeIsometry_apply _ _ _ _ _ x (2 : Fin 5)).trans <|
    (Isometry.refl_apply (V := Fin (A 5).rank → ℚ) _ _).trans <|
      (rootLatticeIsometryOfEq_blockRot_inv_eq x 2 1 a5FourthD4BlockRot_inv_two rfl).trans <|
        (DFunLike.congr_fun (rootLatticeIsometryOfEq_rfl
          (a5FourthD4.componentType (1 : Fin 5))
          (a5FourthD4.isSimplyLaced_componentType (1 : Fin 5))) (x (1 : Fin 5))).trans <|
          Isometry.refl_apply _ _

@[simp]
theorem a5FourthD4TrialityRotation_apply_three
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityRotation x (3 : Fin 5) = x (2 : Fin 5) :=
  (a5FourthD4.coupledLatticeIsometry_apply _ _ _ _ _ x (3 : Fin 5)).trans <|
    (Isometry.refl_apply (V := Fin (A 5).rank → ℚ) _ _).trans <|
      (rootLatticeIsometryOfEq_blockRot_inv_eq x 3 2 a5FourthD4BlockRot_inv_three rfl).trans <|
        (DFunLike.congr_fun (rootLatticeIsometryOfEq_rfl
          (a5FourthD4.componentType (2 : Fin 5))
          (a5FourthD4.isSimplyLaced_componentType (2 : Fin 5))) (x (2 : Fin 5))).trans <|
          Isometry.refl_apply _ _

@[simp]
theorem a5FourthD4TrialityRotation_apply_four
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityRotation x (4 : Fin 5) =
      typeD4Triality (isSimplyLaced_D 4) (x (4 : Fin 5)) :=
  (a5FourthD4.coupledLatticeIsometry_apply _ _ _ _ _ x (4 : Fin 5)).trans <|
    congrArg (typeD4Triality (isSimplyLaced_D 4)) <|
      (rootLatticeIsometryOfEq_blockRot_inv_eq x 4 4 a5FourthD4BlockRot_inv_four rfl).trans <|
        (DFunLike.congr_fun (rootLatticeIsometryOfEq_rfl
          (a5FourthD4.componentType (4 : Fin 5))
          (a5FourthD4.isSimplyLaced_componentType (4 : Fin 5))) (x (4 : Fin 5))).trans <|
          Isometry.refl_apply _ _

/-- **The coupled triality rotation has order three.** -/
@[simp]
theorem a5FourthD4TrialityRotation_pow_three : a5FourthD4TrialityRotation ^ 3 = 1 := by
  let τ := typeD4Triality (isSimplyLaced_D 4)
  have h4 : ∀ y : Fin (D 4).rank → ℚ, τ (τ (τ y)) = y := fun y ↦ by
    rw [← Isometry.mul_apply, ← Isometry.mul_apply, ← pow_two, ← pow_succ,
      typeD4Triality_pow_three, Isometry.one_apply]
  apply Isometry.ext
  intro x
  rw [pow_succ, pow_two, Isometry.mul_apply, Isometry.mul_apply, Isometry.one_apply]
  funext k
  generalize (k : Fin 5) = j
  fin_cases j
  · exact (a5FourthD4TrialityRotation_apply_zero _).trans <|
      (a5FourthD4TrialityRotation_apply_zero _).trans (a5FourthD4TrialityRotation_apply_zero _)
  · exact (a5FourthD4TrialityRotation_apply_one _).trans <|
      (a5FourthD4TrialityRotation_apply_three _).trans (a5FourthD4TrialityRotation_apply_two _)
  · exact (a5FourthD4TrialityRotation_apply_two _).trans <|
      (a5FourthD4TrialityRotation_apply_one _).trans (a5FourthD4TrialityRotation_apply_three _)
  · exact (a5FourthD4TrialityRotation_apply_three _).trans <|
      (a5FourthD4TrialityRotation_apply_two _).trans (a5FourthD4TrialityRotation_apply_one _)
  · exact (a5FourthD4TrialityRotation_apply_four _).trans <|
      (congrArg τ (a5FourthD4TrialityRotation_apply_four _)).trans <|
        (congrArg (fun v ↦ τ (τ v)) (a5FourthD4TrialityRotation_apply_four _)).trans
          (h4 (x (4 : Fin 5)))

/-- `a5FourthD4TrialityRotation` is nontrivial. -/
theorem a5FourthD4TrialityRotation_ne_one : a5FourthD4TrialityRotation ≠ 1 := by
  intro h
  let x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ :=
    fun i _ ↦ if i.val = 1 then 1 else 0
  have hx := congrFun (congrFun (DFunLike.congr_fun h x) (2 : Fin 5)) ⟨0, by decide⟩
  have hlhs : a5FourthD4TrialityRotation x (2 : Fin 5) ⟨0, by decide⟩ = 1 := by
    rw [congrFun (a5FourthD4TrialityRotation_apply_two x) ⟨0, by decide⟩]
    rfl
  have hrhs : (1 : Isometry niemeierA5FourthD4 niemeierA5FourthD4) x (2 : Fin 5) ⟨0, by decide⟩ =
      0 := by
    rw [Isometry.one_apply]
    rfl
  exact one_ne_zero (hlhs.symm.trans (hx.trans hrhs))

/-! ### Faithful action of all pattern symmetry groups across all 23 rows -/

private theorem mem_symmetries_a5FourthD4_cyclic_iff (g : Equiv.Perm (Fin 5)) :
    g ∈ (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries ↔
      g = 1 ∨ g = a5FourthD4BlockRot ∨ g = a5FourthD4BlockRot ^ 2 := by
  rw [GluePattern.symmetries_cyclic]
  -- `[2]`, `[0, 2, 4]`, `[0]` have lengths `1, 3, 1`, matching `a5FourthD4BlockRot`.
  change g ∈ Subgroup.zpowers a5FourthD4BlockRot ↔ _
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    clear hg
    have hinv : a5FourthD4BlockRot⁻¹ = a5FourthD4BlockRot ^ 2 := by
      rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide
    have h22 : (2 + 2 : ℕ) = 3 + 1 := rfl
    induction k using Int.induction_on with
    | zero => exact Or.inl (zpow_zero _)
    | succ i ih =>
      rw [zpow_add_one]
      rcases ih with h | h | h <;> rw [h]
      · exact Or.inr (Or.inl (one_mul _))
      · exact Or.inr (Or.inr (sq _).symm)
      · exact Or.inl (by rw [← pow_succ, a5FourthD4BlockRot_pow_three])
    | pred i ih =>
      rw [zpow_sub_one, hinv]
      rcases ih with h | h | h <;> rw [h]
      · exact Or.inr (Or.inr (one_mul _))
      · exact Or.inl (by rw [← pow_succ', a5FourthD4BlockRot_pow_three])
      · exact Or.inr (Or.inl (by
          rw [← pow_add, h22, pow_add, a5FourthD4BlockRot_pow_three, one_mul, pow_one]))
  · rintro (rfl | rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _
    · exact pow_mem (Subgroup.mem_zpowers _) 2

/-- **The indicated symmetry group of `[2(024)0]` acts on `niemeierA5FourthD4`** by powers of
`a5FourthD4TrialityRotation`. -/
noncomputable def a5FourthD4CyclicSymmetryHom :
    (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries →*
      Isometry niemeierA5FourthD4 niemeierA5FourthD4 where
  toFun g := a5FourthD4TrialityRotation ^ ((g.val ⟨1, by decide⟩).val - 1)
  map_one' := pow_zero _
  map_mul' a b := by
    have ha := (mem_symmetries_a5FourthD4_cyclic_iff a.val).mp a.property
    have hb := (mem_symmetries_a5FourthD4_cyclic_iff b.val).mp b.property
    have hpow : ∀ m : ℕ, a5FourthD4TrialityRotation ^ m =
        a5FourthD4TrialityRotation ^ (m % 3) := fun m ↦ by
      conv_lhs => rw [← Nat.div_add_mod m 3]
      rw [pow_add, pow_mul, a5FourthD4TrialityRotation_pow_three, one_pow, one_mul]
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
      simp only [Subgroup.coe_mul, ha, hb, a5FourthD4BlockRot_eq_swap_mul_swap, ← pow_add] <;>
      rw [hpow ((_ : ℕ) + (_ : ℕ))] <;>
      exact congrArg (a5FourthD4TrialityRotation ^ ·) (by decide)

/-- The generator `a5FourthD4BlockRot` of `[2(024)0].symmetries` acts as
`a5FourthD4TrialityRotation`. -/
@[simp]
theorem a5FourthD4CyclicSymmetryHom_blockRot :
    a5FourthD4CyclicSymmetryHom ⟨a5FourthD4BlockRot, a5FourthD4BlockRot_mem_symmetries⟩ =
      a5FourthD4TrialityRotation := by
  have hexp : (a5FourthD4BlockRot (1 : Fin 5)).val - 1 = 1 := by
    rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide
  exact (congrArg (a5FourthD4TrialityRotation ^ ·) hexp).trans (pow_one _)

/-- **The cyclic pattern `[2(024)0]` acts faithfully on `niemeierA5FourthD4`.** -/
theorem a5FourthD4CyclicSymmetryHom_injective :
    Function.Injective a5FourthD4CyclicSymmetryHom := by
  rw [injective_iff_map_eq_one]
  intro g hg
  let gen : (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries :=
    ⟨a5FourthD4BlockRot, a5FourthD4BlockRot_mem_symmetries⟩
  rcases (mem_symmetries_a5FourthD4_cyclic_iff g.val).mp g.property with h | h | h
  · exact Subtype.ext h
  · have hg_eq : g = gen := Subtype.ext h
    rw [hg_eq, a5FourthD4CyclicSymmetryHom_blockRot] at hg
    exact absurd hg a5FourthD4TrialityRotation_ne_one
  · have hg_eq : g = gen ^ 2 := Subtype.ext h
    rw [hg_eq, map_pow, a5FourthD4CyclicSymmetryHom_blockRot] at hg
    have h22 : (2 + 2 : ℕ) = 3 + 1 := rfl
    have h1 : a5FourthD4TrialityRotation = 1 := by
      calc a5FourthD4TrialityRotation
          = a5FourthD4TrialityRotation ^ 2 * a5FourthD4TrialityRotation ^ 2 := by
            rw [← pow_add, h22, pow_add, a5FourthD4TrialityRotation_pow_three, one_mul, pow_one]
        _ = 1 := by rw [hg, mul_one]
    exact absurd h1 a5FourthD4TrialityRotation_ne_one

/-- **Every table pattern of every rootful Niemeier row acts on the lattice of its row**: by pure
component permutation (`patternIsometryHom`) on the 22 rows other than `A₅⁴ D₄`, and by the
coupled triality action (`a5FourthD4CyclicSymmetryHom`) on `A₅⁴ D₄`. -/
noncomputable def coupledPatternIsometryHom {r : RootfulNiemeierType} {p : GluePattern}
    (hp : p ∈ r.gluePatterns) :
    p.symmetries →* Isometry r.lattice r.lattice :=
  if hr : r = a5FourthD4 then
    match p, hp with
    | .literal _, _ => 1
    | .evenPermutations _, hp => by simp [hr, gluePatterns] at hp
    | .cyclic pre block post, hp => by
      have hp' : pre = [2] ∧ block = [0, 2, 4] ∧ post = [0] := by
        simpa [hr, gluePatterns] using hp
      rcases hp' with ⟨rfl, rfl, rfl⟩
      subst hr
      exact a5FourthD4CyclicSymmetryHom
  else
    patternIsometryHom hr hp

/-- On every row other than `A₅⁴ D₄`, `coupledPatternIsometryHom` agrees with
`patternIsometryHom`. -/
@[simp]
theorem coupledPatternIsometryHom_eq_patternIsometryHom {r : RootfulNiemeierType}
    (hr : r ≠ a5FourthD4) {p : GluePattern} (hp : p ∈ r.gluePatterns) :
    coupledPatternIsometryHom hp = patternIsometryHom hr hp := by
  simp [coupledPatternIsometryHom, hr]

/-- On the cyclic pattern `[2(024)0]` of `A₅⁴ D₄`, `coupledPatternIsometryHom` is
`a5FourthD4CyclicSymmetryHom`. -/
@[simp]
theorem coupledPatternIsometryHom_a5FourthD4_cyclic
    (hp : GluePattern.cyclic [2] [0, 2, 4] [0] ∈ a5FourthD4.gluePatterns) :
    coupledPatternIsometryHom hp = a5FourthD4CyclicSymmetryHom := by
  simp [coupledPatternIsometryHom]

/-- On any literal pattern of any row, `coupledPatternIsometryHom` is trivial. -/
@[simp]
theorem coupledPatternIsometryHom_literal {r : RootfulNiemeierType} (word : List ℕ)
    (hp : GluePattern.literal word ∈ r.gluePatterns) :
    coupledPatternIsometryHom hp = 1 := by
  ext g
  have hg : g = 1 := Subtype.ext <| Subgroup.mem_bot.mp <| by
    simpa [GluePattern.symmetries_literal] using g.property
  rw [hg, map_one, MonoidHom.one_apply]

/-- **Every pattern symmetry group across all 23 rootful Niemeier rows embeds faithfully into the
isometry group of its row's lattice.** -/
theorem coupledPatternIsometryHom_injective {r : RootfulNiemeierType} {p : GluePattern}
    (hp : p ∈ r.gluePatterns) :
    Function.Injective (coupledPatternIsometryHom hp) := by
  by_cases hr : r = a5FourthD4
  · subst hr
    rcases p with word | ⟨pre, block, post⟩ | @⟨n, word⟩
    · intro a b _
      have ha : a.val = 1 := Subgroup.mem_bot.mp
        (by simpa [GluePattern.symmetries_literal] using a.property)
      have hb : b.val = 1 := Subgroup.mem_bot.mp
        (by simpa [GluePattern.symmetries_literal] using b.property)
      exact Subtype.ext (ha.trans hb.symm)
    · have hp' : pre = [2] ∧ block = [0, 2, 4] ∧ post = [0] := by
        simpa [gluePatterns] using hp
      rcases hp' with ⟨rfl, rfl, rfl⟩
      exact a5FourthD4CyclicSymmetryHom_injective
    · simp [gluePatterns] at hp
  · rw [coupledPatternIsometryHom_eq_patternIsometryHom hr]
    exact patternIsometryHom_injective hr hp

end RootfulNiemeierType

end TauCeti
